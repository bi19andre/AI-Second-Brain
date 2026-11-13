#!/usr/bin/env python3
"""AI Second Brain — painel de um vault do Obsidian usado como memória de agente: specs, ADRs, anotações e grafo.

Uso:
    python3 vault_status.py                  # gera <projeto>/_status.html no vault (retrato, com a aba Grafo)
    python3 vault_status.py --no-graph       # retrato sem o grafo (modo rápido, sem networkx)
    python3 vault_status.py --html PATH      # destino alternativo do HTML
    python3 vault_status.py --json PATH      # exporta também o modelo de dados (verificadores)
    python3 vault_status.py --no-history     # pula o histórico git (modo rápido)
    python3 vault_status.py serve [--port 8765]   # painel AO VIVO em http://localhost:8765 (só 127.0.0.1)
    --vault PATH                             # outro vault (qualquer modo); o histórico git segue o do real

Lançador do modo ao vivo: ./vault-panel.sh start|stop|status|restart|open|ensure

Só biblioteca padrão (git via subprocess); o grafo usa o vault_graph.py (networkx), importado só no
caminho do grafo — sem networkx a aba Grafo mostra um aviso. Nada no vault é alterado além do HTML gerado.

Modo ao vivo (serve): servidor stdlib em 127.0.0.1 com "/" (página única: grafo + specs; "/foco" é alias),
"/completo" (painel completo), "/data.json", "/graph.json",
"/events" (Server-Sent Events) e "/healthz". Um observador faz POLLING (o Obsidian grava pelo Windows em
/mnt/c e o WSL não recebe inotify dali): conjunto quente a cada 2 s (specs, _INDEX, inbox, anotações, a
listagem de 02_Memory e os ADRs "quentes": os 20 de número mais alto + os que nasceram/mudaram há < 10 min),
varredura completa a cada 60 s (edição num ADR antigo aparece em até 60 s). Status reconstruído 1,5 s após a
última mudança, com cache (texto por mtime+tamanho, git por HEAD); grafo em thread própria após 10 s de vault
quieto. O retrato _status.html é regravado no máximo a cada 30 s — na subida espera o 1º grafo (até 90 s) e no
desligamento grava o que estava pendente.

Fontes (raw/ do vault NUNCA é lida):
    01_Specs/*.md (1º nível)  status (frontmatter > "**Status:**" do corpo > tag do _INDEX),
                              checkboxes no arquivo e nas seções "Crit…"/"Fase…", frontmatter
                              de arquivamento, título (H1)
    00_Context/_INDEX.md      tag "[…]" da linha da spec (seção "## Specs" e "### Arquivadas")
                              e o "~NN%" dela — estimativa atual de andamento
    git do repo               docs/vault/<projeto>/01_Specs/ (cópia sincronizada do vault, opcional):
                              uma versão por commit → série de status/checkboxes por spec
    git do vault              <projeto>/01_Specs/ — só para antecipar a data de criação
    02_Memory/ADR-*.md        número, título, data, status, 1º módulo afetado
    02_Memory/_inbox/*.md     notas de sessão (vivas + as que já existiram no git do repo)
    04_Anotações/*.md         anotações livres

Ligação spec ↔ ADR/nota: o texto do ADR/nota cita o slug da spec, OU a spec cita "ADR-NNNN".
"""
from __future__ import annotations

import argparse
import codecs
import glob
import hashlib
import json
import os
import re
import secrets
import signal
import subprocess
import sys
import threading
import time
import traceback
import unicodedata
from collections import Counter, defaultdict
from datetime import date, datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlsplit

try:
    from zoneinfo import ZoneInfo

    TZ = ZoneInfo("America/Sao_Paulo")
except Exception:  # sem tzdata: Brasília não tem horário de verão desde 2019
    TZ = timezone(timedelta(hours=-3))

# Projeto principal = pasta do vault cujas specs/ADRs o painel acompanha (VAULT_PANEL_VAULT; o vault-panel.sh lê o local.env)
VAULT = os.path.abspath(os.path.expanduser(os.environ.get("VAULT_PANEL_VAULT") or "."))
VAULT_ROOT = os.path.dirname(VAULT)       # o vault do Obsidian inteiro (todos os projetos)
HERE = os.path.dirname(os.path.abspath(__file__))  # pasta da ferramenta (vault_graph.py, assets/)
# repo git com a cópia sincronizada do vault (histórico das specs); padrão = a própria pasta
REPO = os.environ.get("VAULT_PANEL_REPO") or HERE
REPO_VAULT = os.environ.get("VAULT_PANEL_REPO_VAULT") or "docs/vault/" + os.path.basename(VAULT)   # cópia do vault no repo
SPECS_DIR = os.path.join(VAULT, "01_Specs")
INDEX_MD = os.path.join(VAULT, "00_Context", "_INDEX.md")
MEMORY_DIR = os.path.join(VAULT, "02_Memory")
INBOX_DIR = os.path.join(MEMORY_DIR, "_inbox")
ANOT_DIR = os.path.join(VAULT, "04_Anotações")
SPEC_EXCLUDE = {"_template.md"}


def vault_projects(root):
    """Projetos do vault que o painel sabe ler: pasta de 1º nível com 01_Specs/*.md ou 02_Memory/ADR-*.md."""
    def tem(d, pred):
        try:
            with os.scandir(d) as it:
                return any(pred(e.name) for e in it)
        except OSError:
            return False
    out = []
    try:
        names = sorted(os.listdir(root), key=str.lower)
    except OSError:
        return out
    for n in names:
        p = os.path.join(root, n)
        if n.startswith(".") or n in ("raw", "assets") or not os.path.isdir(p):
            continue
        if tem(os.path.join(p, "01_Specs"), lambda f: f.endswith(".md")) or \
                tem(os.path.join(p, "02_Memory"), lambda f: f.startswith("ADR-")):
            out.append(n)
    return out


def set_vault(path):
    """--vault: aponta as fontes para outro vault. O histórico git continua vindo do repo (REPO_VAULT) e do
    git do vault real (VAULT_ROOT) — com uma cópia, a série de status segue a do real."""
    global VAULT, SPECS_DIR, INDEX_MD, MEMORY_DIR, INBOX_DIR, ANOT_DIR
    VAULT = os.path.abspath(path)
    SPECS_DIR = os.path.join(VAULT, "01_Specs")
    INDEX_MD = os.path.join(VAULT, "00_Context", "_INDEX.md")
    MEMORY_DIR = os.path.join(VAULT, "02_Memory")
    INBOX_DIR = os.path.join(MEMORY_DIR, "_inbox")
    ANOT_DIR = os.path.join(VAULT, "04_Anotações")


def windows_path(path):
    """/mnt/c/Users/x → C:\\Users\\x (para o link obsidian://open?path=…); None fora de /mnt/<letra>."""
    m = re.match(r"/mnt/([a-zA-Z])(?=/|$)(.*)$", path or "")
    if not m:
        return None
    return m.group(1).upper() + ":" + (m.group(2) or "/").replace("/", "\\")

RE_H1 = re.compile(r"(?m)^#[ \t]+(.+?)(?:[ \t]+#+)?[ \t]*$")
RE_HEADING = re.compile(r"^(#{1,6})[ \t]+(.*)$")
RE_CHECK = re.compile(r"^[ \t>]*- \[([ xX])\]")
RE_STATUS_LINE = re.compile(r"(?:\*\*Status:?\*\*:?|(?m:^>[ \t]*Status:))[ \t]*([^\n]*)")
RE_ADR_DATE = re.compile(r"(?:\*\*Data:?\*\*:?|(?m:^>[ \t]*Data:))[ \t]*(\d{4})-(\d{2})(?:-(\d{2}))?")
RE_ADR_MODULE = re.compile(r"\*\*M[óo]dulos?(?: afetados?)?:?\*\*:?[ \t]*([^\n]*)")
RE_ADR_CITE = re.compile(r"\bADR-0*(\d{1,4})((?:/0*\d{1,4})*)(?:[ \t]*(?:\.\.\.?|…)[ \t]*(?:ADR-)?0*(\d{1,4}))?")
# título de seção de critérios: começa (após numeração/emoji) por Critério(s) / Fase(s) / Faseamento
RE_CRIT_TITLE = re.compile(r"(?:criterios?|fases?|faseamento)\b")
RE_PCT = re.compile(r"~\s*(\d{1,3})\s*%")
RE_YM = re.compile(r"(\d{4})-(\d{2})(?:-(\d{2}))?")
RE_NAME_DATE = re.compile(r"(\d{4})-(\d{2})(?:-(\d{2}))?$")
RE_DAY_PREFIX = re.compile(r"^(\d{4})-(\d{2})-(\d{2})")

SPEC_STATUSES = ("rascunho", "aprovada", "em-desenvolvimento", "implementada", "arquivada",
                 "estudo", "guia", "desconhecido")
# só estes status "andam": estudo, guia e implementada não contam como parados
STATUS_QUE_PARAM = ("rascunho", "aprovada", "em-desenvolvimento", "desconhecido")
PARADA_DIAS = 30
LIGACAO_AMPLA = 5      # nota/ADR que cita ≥ 5 specs é referência ampla (auditoria, índice): liga, mas não é atividade
LINHA_EM_MASSA = 5     # linha idêntica mexida em ≥ 5 specs no mesmo commit = edição mecânica em lote
FAIXA_ADR_MAX = 50     # "ADR-0010..0015" expande até 50 números

def _load_modules():
    """Sinônimos de módulo (o gráfico de ADRs por módulo junta rótulos que são o mesmo módulo): arquivo local opcional,
    fora do git — VAULT_PANEL_MODULES ou ./local.modules.json = {"aliases": {"chave": "Nome"}, "keep_slash": ["chave"]}.
    Chave = o rótulo só com letras e dígitos, minúsculo e sem acento (ex.: "Login Social" → "loginsocial")."""
    p = os.environ.get("VAULT_PANEL_MODULES") or os.path.join(HERE, "local.modules.json")
    try:
        with open(p, encoding="utf-8") as fh:
            d = json.load(fh)
    except (OSError, ValueError):
        return {}, set()
    return dict(d.get("aliases") or {}), set(d.get("keep_slash") or [])


MODULE_ALIASES, MODULE_KEEP_SLASH = _load_modules()
GIT_ERRORS = []
ADR_STATUSES = ("aceito", "substituído", "revertido", "proposto", "outro", "arquivado")


# ───────────────────────── utilidades ─────────────────────────

class _LiveCache:
    """Só no modo `serve` — o que não mudou entre reconstruções não é relido nem reparseado:
    texto de cada arquivo por (mtime, tamanho) — a assinatura vem do observador, sem stat extra —,
    parse de spec por texto (versões do git são imutáveis), `git log` por (repo, pathspec) enquanto o
    HEAD do repo não muda, e blobs `sha:caminho` para sempre."""

    def __init__(self):
        self.sigs = {}        # caminho absoluto -> (mtime_ns, tamanho): dicionário do observador
        self.texts = {}       # caminho -> (assinatura, texto)
        self.parse = {}       # texto -> parse_spec_text(texto)
        self.parse_used = set()
        self.logs = {}        # (repo, pathspec, renames) -> (HEAD, commits)
        self.blobs = {}       # (repo, "sha:caminho") -> texto|None
        self.heads = {}       # repo -> assinatura do HEAD nesta reconstrução

    def prune(self):
        """Poda o que ficou para trás (arquivo apagado, versão antiga de uma spec viva)."""
        if self.sigs:
            self.texts = {p: v for p, v in self.texts.items() if p in self.sigs}
        self.parse = {t: v for t, v in self.parse.items() if t in self.parse_used}
        self.parse_used = set()


_CACHE = None   # _LiveCache no modo serve; None no retrato (comportamento original, sem cache)


def _sig_of(path):
    c = _CACHE
    if c is not None:
        s = c.sigs.get(path)
        if s is not None:
            return s
    try:
        st = os.stat(path)
    except OSError:
        return None
    return (st.st_mtime_ns, st.st_size)


def _read_disk(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            return f.read()
    except OSError:
        return ""


def _read(path):
    c = _CACHE
    if c is None:
        return _read_disk(path)
    sig = _sig_of(path)
    hit = c.texts.get(path)
    if hit is not None and sig is not None and hit[0] == sig:
        return hit[1]
    text = _read_disk(path)
    if sig is not None:
        c.texts[path] = (sig, text)
    return text


def _isfile(path):
    c = _CACHE
    if c is not None and path in c.sigs:
        return True
    return os.path.isfile(path)


def _fold(s):
    """minúsculo e sem acento — para comparar rótulos escritos de jeitos diferentes."""
    s = unicodedata.normalize("NFKD", s or "")
    return "".join(c for c in s if not unicodedata.combining(c)).lower()


def _iso(d):
    return d.isoformat() if d else None


def _mtime_date(path):
    if _CACHE is not None:
        s = _sig_of(path)
        return datetime.fromtimestamp(s[0] / 1e9, TZ).date() if s else None
    try:
        return datetime.fromtimestamp(os.path.getmtime(path), TZ).date()
    except OSError:
        return None


def _mk_date(y, m, d=None):
    try:
        return date(int(y), int(m), int(d) if d else 1)
    except (TypeError, ValueError):
        return None


def split_frontmatter(text):
    if text.startswith("\ufeff"):
        text = text[1:]
    if not text.startswith("---"):
        return {}, text
    m = re.match(r"---[ \t]*\r?\n(.*?)\r?\n---[ \t]*(?:\r?\n|$)", text, re.S)
    if not m:
        return {}, text
    fm, key, mode, cont = {}, None, None, []

    def flush():
        if key is None or mode is None:
            return
        if mode == "lista":
            fm[key] = ", ".join(c.lstrip("- ").strip().strip('"').strip("'") for c in cont if c.strip())
        else:  # escalar em bloco: ">" dobra as linhas com espaço, "|" mantém as quebras
            fm[key] = ("\n" if mode.startswith("|") else " ").join(c.strip() for c in cont if c.strip())

    for ln in m.group(1).splitlines():
        mm = re.match(r"([A-Za-z_][\w-]*)[ \t]*:[ \t]*(.*?)[ \t]*$", ln)
        if mm and not ln[:1].isspace():
            flush()
            key, cont = mm.group(1).lower(), []
            val = (mm.group(2) or "").strip()
            if val in (">", ">-", ">+", "|", "|-", "|+"):
                mode, fm[key] = val, ""
            elif val == "":
                mode, fm[key] = "lista", ""
            else:
                mode, fm[key] = None, val.strip('"').strip("'").strip()
        elif key is not None and mode is not None and (ln[:1].isspace() or ln.lstrip().startswith("- ")):
            cont.append(ln)
    flush()
    if not fm:  # "---" era régua horizontal, não frontmatter: nada foi engolido
        return {}, text
    return fm, text[m.end():]


def first_h1(body):
    in_fence = False
    for ln in body.splitlines():
        if ln.lstrip().startswith(("```", "~~~")):
            in_fence = not in_fence
            continue
        if not in_fence:
            m = RE_H1.match(ln)
            if m:
                return m.group(1).strip()
    return None


def status_token(rest):
    """Primeiro token entre crases quando a linha começa por crase; senão a 1ª expressão."""
    rest = (rest or "").strip()
    if rest.startswith("`"):
        m = re.match(r"`([^`]+)`", rest)
        if m:
            return m.group(1).strip()
    tok = re.split(r"\s+[·—|(–-]\s|\s*\*\*|<br|\s*\(|\s+·", rest, maxsplit=1)[0]
    return tok.strip(" `*>.;,")


def norm_spec_status(raw):
    s = re.sub(r"^[\W_]+", "", _fold(raw)).strip(" `*>[]")   # tira emoji/marcadores do começo
    if not s:
        return "desconhecido"
    if s.startswith(("arquivad", "cancelad", "descontinuad")):
        return "arquivada"
    if s.startswith(("em-desenvolvimento", "em desenvolvimento", "em-andamento", "em andamento",
                     "implementacao", "em-implementacao", "em implementacao", "working", "em construcao",
                     "parcial")):
        return "em-desenvolvimento"
    if s.startswith(("implementad", "concluid", "entregue", "done", "finalizad")):
        return "implementada"
    if s.startswith(("aprovad", "approved")):
        return "aprovada"
    if s.startswith(("rascunho", "draft", "em-review", "em review", "em-revisao", "em revisao", "revisao",
                     "proposto", "proposta", "proposed", "em-discussao", "em discussao")):
        return "rascunho"
    if s.startswith("estudo"):
        return "estudo"
    if s.startswith(("viva", "vivo", "ativo", "ativa", "guia", "referencia")):
        return "guia"
    return "desconhecido"


def norm_adr_status(raw):
    s = _fold(raw).strip(" `*>[]")
    if s.startswith("arquivad"):
        return "arquivado"
    if s.startswith(("substitu", "superseded", "obsolet")):
        return "substituído"
    if s.startswith(("revertid", "reverted", "revogad", "desfeit", "rollback", "revoked")):
        return "revertido"
    if s.startswith(("aceit", "approved", "accepted", "implemented", "implementad", "aprovad", "vigente",
                     "em vigor", "ativo", "concluid", "entregue", "aplicad", "adotad", "corrigid", "resolvid")):
        return "aceito"
    if s.startswith(("propost", "proposed", "rascunho", "draft", "em discussao", "em-discussao")):
        return "proposto"
    return "outro"


def bracket_tag(cell):
    """Conteúdo do primeiro "[…]" (colchetes balanceados) no começo da célula."""
    cell = cell.lstrip()
    if not cell.startswith("["):
        return None
    depth = 0
    for i, ch in enumerate(cell):
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                return cell[1:i].strip()
    return None


def _clean_heading(raw):
    t = re.sub(r"<[^>]*>", "", raw)
    t = re.sub(r"\[\[([^\]|]+)\|([^\]]+)\]\]", r"\2", t)
    t = re.sub(r"\[\[([^\]]+)\]\]", r"\1", t)
    return re.sub(r"[`*]", "", t).strip()


def is_crit_heading(raw):
    """Seção de critérios = título que COMEÇA (após numeração, emoji ou marcação) por
    Critério(s) / Fase(s) / Faseamento. "Críticos", "Execução da fase 1", "escrita", "ênfase",
    "Rollout faseado" e títulos que só citam "critério" no meio ficam de fora."""
    t = re.sub(r"^[\W\d_]+", "", _fold(_clean_heading(raw)))
    return RE_CRIT_TITLE.match(t) is not None


def count_checks(text):
    """(feitos, total, feitos_crit, total_crit, seções) — crit = caixas sob seções de critérios
    (ver is_crit_heading; H1 nunca conta). Caixas dentro de bloco de código não contam."""
    done = total = cdone = ctotal = 0
    sec_level = None
    secs = []
    in_fence = False
    for ln in text.splitlines():
        if ln.lstrip().startswith(("```", "~~~")):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        h = RE_HEADING.match(ln)
        if h:
            lvl = len(h.group(1))
            if sec_level is not None and lvl <= sec_level:
                sec_level = None
            if sec_level is None and lvl >= 2 and is_crit_heading(h.group(2)):
                sec_level = lvl
                secs.append([_clean_heading(h.group(2))[:90], 0, 0])
            continue
        m = RE_CHECK.match(ln)
        if m:
            ok = m.group(1) in "xX"
            total += 1
            done += ok
            if sec_level is not None:
                ctotal += 1
                cdone += ok
                secs[-1][1] += ok
                secs[-1][2] += 1
    return done, total, cdone, ctotal, [{"titulo": t, "feitos": f, "total": n} for t, f, n in secs if n]


def parse_spec_cached(text):
    """parse_spec_text com memo por texto no modo ao vivo (o resultado é só lido, nunca alterado)."""
    c = _CACHE
    if c is None:
        return parse_spec_text(text)
    p = c.parse.get(text)
    if p is None:
        p = c.parse[text] = parse_spec_text(text)
    c.parse_used.add(text)
    return p


def cited_adr_numbers(text):
    """ADR-0042/0057 → {42, 57}; ADR-0010..0015 → 10 a 15 (faixa de até FAIXA_ADR_MAX)."""
    nums = set()
    for m in RE_ADR_CITE.finditer(text):
        last = int(m.group(1))
        nums.add(last)
        for extra in re.findall(r"\d{1,4}", m.group(2) or ""):
            last = int(extra)
            nums.add(last)
        if m.group(3):
            end = int(m.group(3))
            if last < end <= last + FAIXA_ADR_MAX:
                nums.update(range(last, end + 1))
    return nums


def slug_regex(slug):
    return re.compile(r"(?<![A-Za-z0-9_-])" + re.escape(slug) + r"(?![A-Za-z0-9_])")


def cites_slug(text, slug, rx):
    return slug in text and rx.search(text) is not None


# ───────────────────────── git ─────────────────────────

def git(repo, args, stdin=None):
    """stdout do git; falha (erro, timeout, "dubious ownership"…) vira aviso no stderr e em GIT_ERRORS."""
    cmd = " ".join(args[:2])
    try:
        r = subprocess.run(["git", "-C", repo, "-c", "core.quotepath=off", *args],
                           input=stdin, capture_output=True, timeout=120)
    except (OSError, subprocess.TimeoutExpired) as e:
        GIT_ERRORS.append(f"{repo}: git {cmd}: {type(e).__name__}")
        print(f"aviso: git {cmd} em {repo} falhou ({type(e).__name__})", file=sys.stderr)
        return b""
    if r.returncode != 0:
        msg = r.stderr.decode("utf-8", "replace").strip().splitlines()
        GIT_ERRORS.append(f"{repo}: git {cmd}: {msg[0] if msg else 'código ' + str(r.returncode)}")
        print(f"aviso: git {cmd} em {repo} falhou: {' '.join(msg)[:300]}", file=sys.stderr)
        return b""
    return r.stdout


def _unquote_git_path(p):
    """Caminho entre aspas do git (C-style): escapes viram bytes; UTF-8 cru passa intacto."""
    if len(p) >= 2 and p[0] == '"' and p[-1] == '"':
        try:
            return codecs.escape_decode(p[1:-1].encode("utf-8"))[0].decode("utf-8", "replace")
        except Exception:
            return p[1:-1]
    return p


def head_sig(repo):
    """Assinatura barata do HEAD de um repo (lê .git/HEAD e a ref, sem subprocesso); None se não der."""
    def rd(p):
        with open(p, encoding="utf-8", errors="replace") as f:
            return f.read().strip()
    gd = os.path.join(repo, ".git")
    try:
        if os.path.isfile(gd):                      # worktree/submódulo: ".git" é um arquivo "gitdir: …"
            line = rd(gd)
            if not line.startswith("gitdir:"):
                return None
            gd = os.path.normpath(os.path.join(repo, line[7:].strip()))
        head = rd(os.path.join(gd, "HEAD"))
        if not head.startswith("ref:"):
            return head
        ref = head[4:].strip()
        common = gd
        if os.path.isfile(os.path.join(gd, "commondir")):
            common = os.path.normpath(os.path.join(gd, rd(os.path.join(gd, "commondir"))))
        for base in (gd, common):
            if os.path.isfile(os.path.join(base, ref)):
                return ref + "@" + rd(os.path.join(base, ref))
        for ln in rd(os.path.join(common, "packed-refs")).splitlines():
            if ln.endswith(" " + ref):
                return ref + "@" + ln.split()[0]
    except OSError:
        return None
    return None


def git_log_files(repo, pathspec, renames=False):
    """[(sha, data_local, [(status, caminho, caminho_antigo|None)])] do mais novo para o mais velho.
    renames=True liga a detecção de renomeação do git (similaridade padrão, 50%).
    No modo ao vivo o resultado fica em cache enquanto o HEAD do repo não muda (falha nunca é cacheada)."""
    c, key = _CACHE, (repo, pathspec, renames)
    head = c.heads.get(repo) if c is not None else None
    if head:
        hit = c.logs.get(key)
        if hit and hit[0] == head:
            return hit[1]
    nerr = len(GIT_ERRORS)
    commits = _git_log_files(repo, pathspec, renames)
    if head and len(GIT_ERRORS) == nerr:
        c.logs[key] = (head, commits)
    return commits


def _git_log_files(repo, pathspec, renames):
    out = git(repo, ["log", "-M" if renames else "--no-renames", "--format=%x1e%H%x1f%aI", "--name-status",
                     "--", pathspec])
    commits = []
    for block in out.decode("utf-8", "replace").split("\x1e")[1:]:
        lines = block.strip("\n").split("\n")
        if not lines or "\x1f" not in lines[0]:
            continue
        sha, iso = lines[0].split("\x1f", 1)
        try:
            d = datetime.fromisoformat(iso.strip()).astimezone(TZ).date()
        except ValueError:
            continue
        files = []
        for ln in lines[1:]:
            if not ln.strip():
                continue
            parts = ln.split("\t")
            if len(parts) < 2:
                continue
            old = _unquote_git_path(parts[1]) if len(parts) >= 3 else None
            files.append((parts[0][:1], _unquote_git_path(parts[-1]), old))
        commits.append((sha, d, files))
    return commits


def git_cat_blobs(repo, specs):
    """{"sha:caminho": texto|None} — uma chamada só a `git cat-file --batch`. No modo ao vivo só busca o
    que ainda não está no cache (blob de um commit não muda)."""
    specs = list(dict.fromkeys(specs))
    c = _CACHE
    if c is None:
        return _git_cat_blobs(repo, specs)
    missing = [sp for sp in specs if (repo, sp) not in c.blobs]
    if missing:
        nerr = len(GIT_ERRORS)
        got = _git_cat_blobs(repo, missing)
        if len(GIT_ERRORS) == nerr:
            c.blobs.update(((repo, sp), v) for sp, v in got.items())
        else:
            return {sp: c.blobs.get((repo, sp), got.get(sp)) for sp in specs}
    return {sp: c.blobs[(repo, sp)] for sp in specs}


def _git_cat_blobs(repo, specs):
    if not specs:
        return {}
    out = git(repo, ["cat-file", "--batch"], ("\n".join(specs) + "\n").encode("utf-8"))
    res, pos = {}, 0
    for spec in specs:
        nl = out.find(b"\n", pos)
        if nl < 0:
            res[spec] = None
            continue
        header = out[pos:nl].decode("utf-8", "replace")
        pos = nl + 1
        parts = header.rsplit(" ", 2)
        if len(parts) != 3 or parts[1] != "blob" or not parts[2].isdigit():
            res[spec] = None
            continue
        size = int(parts[2])
        res[spec] = out[pos:pos + size].decode("utf-8", "replace")
        pos += size + 1
    return res


def first_appearance(commits, prefix, name_filter):
    """{nome: data mais antiga} para arquivos diretamente sob prefix."""
    first = {}
    for _sha, d, files in commits:
        for _st, p, _old in files:
            if not p.startswith(prefix):
                continue
            rest = p[len(prefix):]
            if "/" in rest or not name_filter(rest):
                continue
            if rest not in first or d < first[rest]:
                first[rest] = d
    return first


# ───────────────────────── specs ─────────────────────────

def parse_spec_text(text):
    fm, body = split_frontmatter(text)
    head = "\n".join(body.splitlines()[:60])
    line = RE_STATUS_LINE.search(head)
    status_texto = line.group(1).strip() if line else ""
    body_tok = status_token(status_texto) if line else ""
    fm_status = fm.get("status", "")
    if fm_status:
        bruto, fonte = fm_status, "frontmatter"
        st = norm_spec_status(fm_status)
        if st == "desconhecido" and body_tok and norm_spec_status(body_tok) != "desconhecido":
            bruto, fonte, st = body_tok, "corpo", norm_spec_status(body_tok)
    elif body_tok:
        bruto, fonte, st = body_tok, "corpo", norm_spec_status(body_tok)
    else:
        bruto, fonte, st = "", None, "desconhecido"
    feitos, total, cf, ct, secs = count_checks(text)
    dm = RE_ADR_DATE.search(head)
    data_corpo = (_mk_date(*dm.groups()), dm.group(3) is None) if dm else (None, False)
    return {"fm": fm, "titulo": first_h1(body), "status": st, "status_bruto": bruto, "status_fonte": fonte,
            "status_texto": status_texto[:600], "feitos": feitos, "total": total, "crit_feitos": cf,
            "crit_total": ct, "crit_secoes": secs, "data_corpo": data_corpo}


def parse_index():
    """{slug: {tag, status, pct, secao, aliases}} — linhas da seção "## Specs" do _INDEX.
    aliases = nomes antigos citados na linha como "(era `x`, antes `y`)"."""
    out = {}
    in_specs, sub = False, "specs"
    for ln in _read(INDEX_MD).splitlines():
        if ln.startswith("## "):
            in_specs = ln[3:].strip().lower().startswith("specs")
            sub = "specs"
            continue
        if not in_specs:
            continue
        if ln.startswith("### "):
            sub = "arquivadas" if "arquivad" in _fold(ln) else _fold(ln[4:].strip())
            continue
        if not ln.lstrip().startswith("|"):
            continue
        parts = ln.split("|", 2)
        if len(parts) < 3:
            continue
        m = re.search(r"01_Specs/([^/)\]`|\s]+)\.md", parts[1])
        if not m:
            continue
        slug = m.group(1)
        tag = bracket_tag(parts[2])
        if tag is None:
            continue
        pm = RE_PCT.search(tag)
        first = re.split(r"[\s·;,]+", tag.strip(), maxsplit=1)[0]
        aliases = []
        for par in re.findall(r"\(((?:era|antes|ex)\b[^)]*)\)", parts[2]):
            aliases += [a for a in re.findall(r"`([a-z0-9][a-z0-9-]{5,})`", par) if a != slug]
        entry = {"tag": tag, "status": norm_spec_status(first), "pct": int(pm.group(1)) if pm else None,
                 "secao": sub, "nao_iniciada": "nao iniciad" in _fold(tag), "aliases": aliases}
        # a linha em "Arquivadas" é a mais recente quando a spec aparece nas duas
        if slug not in out or sub == "arquivadas":
            out[slug] = entry
    return out


def _line_delta(old, new):
    """(linhas acrescentadas, linhas removidas) — sem espaços nas pontas e sem linhas em branco."""
    a = Counter(ln.strip() for ln in (old or "").splitlines() if ln.strip())
    b = Counter(ln.strip() for ln in (new or "").splitlines() if ln.strip())
    return set((b - a).keys()), set((a - b).keys())


def _real_changes(changes):
    """changes = {slug: (texto_anterior|None, parsed_anterior|None, texto, parsed)} de UM commit (ou do
    vault vivo contra o último commit). Devolve {slug: True/False}: False = a spec só recebeu linhas que
    o mesmo lote pôs/tirou em ≥ LINHA_EM_MASSA specs (aviso colado em 40 specs de uma vez), ou só espaço.
    Mudança de status ou de contagem de caixas sempre conta."""
    deltas = {slug: _line_delta(c[0], c[2]) for slug, c in changes.items() if c[0] is not None}
    freq = Counter()
    for add_, rem in deltas.values():
        freq.update(("+", ln) for ln in add_)
        freq.update(("-", ln) for ln in rem)
    em_massa = {k for k, n in freq.items() if n >= LINHA_EM_MASSA}
    out = {}
    for slug, (old_t, old_p, _t, new_p) in changes.items():
        if old_t is None:
            out[slug] = True  # 1ª versão conhecida
            continue
        if old_p and (old_p["status"], old_p["feitos"], old_p["total"]) != (new_p["status"], new_p["feitos"],
                                                                            new_p["total"]):
            out[slug] = True
            continue
        add_, rem = deltas[slug]
        keys = {("+", ln) for ln in add_} | {("-", ln) for ln in rem}
        out[slug] = bool(keys) and not keys <= em_massa
    return out


def collect_specs(no_history, stats):
    files = sorted(f for f in os.listdir(SPECS_DIR)
                   if f.endswith(".md") and f not in SPEC_EXCLUDE
                   and _isfile(os.path.join(SPECS_DIR, f)))
    index = parse_index()
    specs = {}
    for f in files:
        slug = f[:-3]
        path = os.path.join(SPECS_DIR, f)
        text = _read(path)
        p = parse_spec_cached(text)
        specs[slug] = {"slug": slug, "path": path, "text": text, "parsed": p, "historico_raw": [],
                       "git_first": None, "git_first_is_history_start": False, "git_last": None,
                       "git_last_text": None, "live_changed": True, "vault_first": None,
                       "mtime": _mtime_date(path), "aliases": [], "link_names": [slug]}
    for slug, idx in index.items():   # nome antigo citado no _INDEX também liga ADR/nota à spec
        if slug in specs:
            specs[slug]["link_names"] += [a for a in idx["aliases"] if len(a) >= 12]
    stats["historico_inicio"] = None
    stats["mudancas_mecanicas_ignoradas"] = 0
    if no_history:
        return specs, index

    prefix = REPO_VAULT + "/01_Specs/"

    def top(p):  # nome (sem .md) de um arquivo de 1º nível de 01_Specs; senão None
        if not p or not p.startswith(prefix):
            return None
        rest = p[len(prefix):]
        return rest[:-3] if "/" not in rest and rest.endswith(".md") else None

    commits = git_log_files(REPO, prefix, renames=True)
    stats["commits_specs_repo"] = len(commits)
    history_start = min((d for _s, d, _f in commits), default=None)
    stats["historico_inicio"] = _iso(history_start)

    # spec renomeada: o histórico do nome antigo passa para o nome atual. Fontes: "(era `x`, antes `y`)"
    # na linha do _INDEX (reescrita pesada o git não reconhece) e as renomeações que o git detecta.
    historic, renames = set(), {}
    for _sha, _d, fls in commits:
        for st, p, old in fls:
            n, o = top(p), top(old)
            historic.update(x for x in (n, o) if x)
            if st == "R" and n and o and o != n:
                renames.setdefault(o, n)
    alias = {}
    for slug, idx in index.items():
        if slug not in specs:
            continue
        for a in idx["aliases"]:
            rx = re.compile(re.escape(a) + r"(?:-\d{4}-\d{2}(?:-\d{2})?)?")
            for n in historic:
                if n not in specs and rx.fullmatch(n):
                    alias[n] = slug
    for o, n in renames.items():
        if o in specs or o in alias:
            continue
        seen = {o}
        while n not in specs and n in renames and n not in seen:
            seen.add(n)
            n = renames[n]
        n = alias.get(n, n)
        if n in specs:
            alias[o] = n
    for o, n in sorted(alias.items()):
        specs[n]["aliases"].append(o)
        specs[n]["link_names"].append(o)

    wanted = []
    for sha, d, fls in commits:
        for st, p, _old in fls:
            n = top(p)
            slug = n if n in specs else alias.get(n)
            if not slug:
                continue
            s = specs[slug]
            if s["git_first"] is None or d < s["git_first"]:
                s["git_first"] = d
            if st in "AMRC":
                wanted.append((sha, d, slug, f"{sha}:{p}"))
    blobs = git_cat_blobs(REPO, [w[3] for w in wanted])
    stats["versoes_specs_lidas"] = sum(1 for v in blobs.values() if v is not None)

    # do commit mais velho para o mais novo: cada versão contra a anterior da mesma spec
    por_commit = {}
    for sha, d, slug, key in reversed(wanted):
        por_commit.setdefault(sha, (d, []))[1].append((slug, key))
    prev = {}
    for sha, (d, items) in por_commit.items():
        changes = {}
        for slug, key in items:
            txt = blobs.get(key)
            if txt is None:
                continue
            pv = parse_spec_cached(txt)
            specs[slug]["historico_raw"].append((d, sha, pv))
            old_t, old_p = prev.get(slug, (None, None))
            changes[slug] = (old_t, old_p, txt, pv)
            prev[slug] = (txt, pv)
        for slug, real in _real_changes(changes).items():
            s = specs[slug]
            if real:
                s["git_last"] = d if s["git_last"] is None or d > s["git_last"] else s["git_last"]
            else:
                stats["mudancas_mecanicas_ignoradas"] += 1
    # vault vivo contra a última versão sincronizada (o lote mecânico pode estar só no vault)
    live = {slug: (prev[slug][0], prev[slug][1], s["text"], s["parsed"])
            for slug, s in specs.items() if slug in prev}
    for slug, real in _real_changes(live).items():
        specs[slug]["live_changed"] = real
    for slug, s in specs.items():
        if slug in prev:
            s["git_last_text"] = prev[slug][0]
            if s["git_last"] is None:
                s["git_last"] = s["git_first"]
        s["git_first_is_history_start"] = bool(s["git_first"] and history_start and s["git_first"] == history_start)
    vcommits = git_log_files(VAULT_ROOT, os.path.basename(VAULT) + "/01_Specs/")
    stats["commits_specs_vault"] = len(vcommits)
    vfirst = first_appearance(vcommits, os.path.basename(VAULT) + "/01_Specs/", lambda n: n.endswith(".md"))
    for name, d in vfirst.items():
        slug = name[:-3] if name[:-3] in specs else alias.get(name[:-3])
        if slug and (specs[slug]["vault_first"] is None or d < specs[slug]["vault_first"]):
            specs[slug]["vault_first"] = d
    return specs, index


def build_spec_models(specs, index, today):
    models = []
    for slug, s in specs.items():
        p = s["parsed"]
        idx = index.get(slug)
        st, fonte, bruto = p["status"], p["status_fonte"], p["status_bruto"]
        if st == "desconhecido" and idx and idx["status"] != "desconhecido":
            st, fonte = idx["status"], "_INDEX"
            bruto = bruto or idx["tag"]
        fm = p["fm"]
        arquivada = st == "arquivada"

        # histórico: um ponto por dia (a última versão do dia), do mais velho p/ o mais novo
        per_day = {}
        for d, _sha, pv in s["historico_raw"]:  # já vem do mais velho → mais novo; o último do dia vence
            per_day[d] = pv
        points = []
        for d in sorted(per_day):
            pv = per_day[d]
            hst = pv["status"]
            if hst == "desconhecido" and fonte == "_INDEX":
                hst = st  # o arquivo nunca declarou status: vale o do _INDEX ao longo do tempo
            points.append({"data": d.isoformat(), "status": hst, "feitos": pv["feitos"], "total": pv["total"],
                           "crit_feitos": pv["crit_feitos"], "crit_total": pv["crit_total"]})
        points.append({"data": today.isoformat(), "status": st, "feitos": p["feitos"], "total": p["total"],
                       "crit_feitos": p["crit_feitos"], "crit_total": p["crit_total"], "hoje": True})
        compact = []
        for pt in points:
            key = (pt["status"], pt["feitos"], pt["total"], pt["crit_feitos"], pt["crit_total"])
            if compact and compact[-1]["data"] == pt["data"]:
                compact[-1] = pt
            elif compact and not pt.get("hoje") and key == (compact[-1]["status"], compact[-1]["feitos"],
                                                             compact[-1]["total"], compact[-1]["crit_feitos"],
                                                             compact[-1]["crit_total"]):
                continue
            else:
                compact.append(pt)

        # criação: 1ª aparição no git (repo ou vault, a mais antiga). O git do repo começa em 23/06/2026:
        # quem já estava no 1º commit tem ali só o corte do histórico, não a criação — vale então a linha
        # "Data:" da própria spec, senão o dia 01 do mês do nome, senão o corte (marcado aproximado).
        m = RE_NAME_DATE.search(slug)
        name_date = _mk_date(m.group(1), m.group(2), m.group(3)) if m else None
        body_date, body_aprox = p["data_corpo"]
        firsts = [(d, src) for d, src in ((s["git_first"], "git"), (s["vault_first"], "git-vault")) if d]
        git_first = min(firsts)[0] if firsts else None
        if firsts:
            criada, criada_fonte = min(firsts)
            aprox = False
            if s["git_first_is_history_start"] and criada == s["git_first"]:
                if body_date and body_date <= criada:
                    criada, criada_fonte, aprox = body_date, "linha Data da spec (anterior ao histórico)", body_aprox
                elif name_date and name_date <= criada:
                    criada, criada_fonte, aprox = name_date, "mês no nome (anterior ao histórico)", not m.group(3)
                else:
                    criada_fonte, aprox = "início do histórico (criada nesta data ou antes)", True
        elif body_date:
            criada, criada_fonte, aprox = body_date, "linha Data da spec", body_aprox
        elif name_date:
            criada, criada_fonte, aprox = name_date, "nome", not m.group(3)
        else:
            criada, criada_fonte, aprox = s["mtime"], "mtime", True

        # última mudança do próprio arquivo (commits só com edição mecânica em lote não contam)
        ultima = s["git_last"]
        if ultima is None or s["live_changed"]:
            cands = [d for d in (ultima, s["mtime"]) if d]
            ultima = max(cands) if cands else None

        arq_em = None
        if fm.get("arquivado_em"):
            mm = RE_YM.search(fm["arquivado_em"])
            arq_em = _mk_date(*mm.groups()) if mm else None
        if arquivada and not arq_em and idx:
            mm = RE_YM.search(idx["tag"])
            arq_em = _mk_date(*mm.groups()) if mm else None
        if arquivada and not arq_em:
            for pt in compact:
                if pt["status"] == "arquivada":
                    arq_em = date.fromisoformat(pt["data"])
                    break

        if p["crit_total"] > 0:
            crit = {"feitos": p["crit_feitos"], "total": p["crit_total"], "base": "secoes",
                    "secoes": p["crit_secoes"]}
        else:
            crit = {"feitos": p["feitos"], "total": p["total"], "base": "arquivo", "secoes": []}
        # "no ar"/"viva"/entregue sem nenhuma caixa marcada: as caixas nunca foram mantidas — 0% enganaria
        tag_f = _fold(idx["tag"]) if idx else ""
        no_ar = bool(re.search(r"\bno ar\b|\bviva\b|\bentregue\b|\bimplementad", tag_f)) or st in ("implementada", "guia")
        if arquivada:
            pct, pct_fonte = None, "arquivada"
        elif idx and idx["pct"] is not None:
            pct, pct_fonte = idx["pct"], "_INDEX"
        elif idx and idx["nao_iniciada"]:
            pct, pct_fonte = 0, "_INDEX (não iniciada)"
        elif crit["total"] > 0 and crit["feitos"] == 0 and no_ar:
            pct, pct_fonte = None, "no ar, caixas nunca marcadas"
        elif crit["total"] > 0:
            pct, pct_fonte = round(100 * crit["feitos"] / crit["total"]), "critérios"
        else:
            pct, pct_fonte = None, None

        models.append({
            "slug": slug, "arquivo": f"01_Specs/{slug}.md", "titulo": p["titulo"] or slug,
            "status": st, "status_bruto": bruto, "status_fonte": fonte, "status_texto": p["status_texto"],
            "arquivada": arquivada, "conta_parada": (not arquivada) and st in STATUS_QUE_PARAM,
            "index": ({k: idx[k] for k in ("tag", "status", "pct", "secao")} if idx else None),
            "status_divergente": bool(idx and idx["status"] not in ("desconhecido", st)
                                      and not (st == "guia" and idx["status"] == "guia")),
            "andamento_pct": pct, "andamento_fonte": pct_fonte,
            "checkboxes": {"feitos": p["feitos"], "total": p["total"],
                           "crit_feitos": p["crit_feitos"], "crit_total": p["crit_total"]},
            "criterios": crit,
            "criada_em": _iso(criada), "criada_aproximada": aprox, "criada_fonte": criada_fonte,
            "primeira_aparicao_git": _iso(git_first), "renomeada_de": s["aliases"],
            "arquivado_em": _iso(arq_em), "motivo": fm.get("motivo") or None,
            "substituido_por": fm.get("substituido_por") or None,
            "ultima_mudanca": _iso(ultima),
            "historico": compact,
            "_text": s["text"], "_link_names": s["link_names"],
        })
    return models


# ───────────────────────── ADRs ─────────────────────────

def collect_adrs():
    adrs = []
    for path in sorted(glob.glob(os.path.join(MEMORY_DIR, "ADR-*.md"))):
        name = os.path.basename(path)
        text = _read(path)
        fm, body = split_frontmatter(text)
        m = re.match(r"ADR-0*(\d+)", name)
        num = int(m.group(1)) if m else None
        head = "\n".join(body.splitlines()[:40])

        data, aprox = None, False
        dm = RE_ADR_DATE.search(head)
        if dm:
            data, aprox = _mk_date(*dm.groups()), dm.group(3) is None
        title = first_h1(body) or name[:-3]
        if data is None:
            dm = re.search(r"(\d{4})-(\d{2})-(\d{2})", title)
            if dm:
                data = _mk_date(*dm.groups())
        if data is None and fm.get("date"):
            dm = RE_YM.search(fm["date"])
            if dm:
                data, aprox = _mk_date(*dm.groups()), dm.group(3) is None
        if data is None:
            dm = re.search(r"(\d{4})-(\d{2})\.md$", name)
            if dm:
                data, aprox = _mk_date(dm.group(1), dm.group(2)), True

        # status: a linha "Status" vale; "substituído" vence o frontmatter "arquivado" (quase todo ADR
        # arquivado foi substituído, e a série "Substituído" ficaria vazia). Arquivamento vira campo à parte.
        sm = RE_STATUS_LINE.search(head)
        linha = sm.group(1).strip() if sm else ""
        fm_st = fm.get("status", "")
        bruto = status_token(linha) if sm else fm_st
        st = norm_adr_status(bruto)
        if st == "outro" and fm_st and norm_adr_status(fm_st) != "outro":
            st = norm_adr_status(fm_st)
        if st == "substituído" and re.match(r"\W*substitu\w*\s+parcial", _fold(linha)):
            st = "aceito"  # substituído só em parte: a decisão segue valendo
        arquivado = _fold(fm_st).startswith("arquivad")
        if arquivado and st != "substituído":
            st = "arquivado"

        mm = RE_ADR_MODULE.search(head)
        mod = clean_module(mm.group(1)) if mm else ""
        adrs.append({"id": f"ADR-{num}" if num is not None else name[:-3], "num": num, "arquivo": name,
                     "titulo": title, "data": _iso(data), "data_aproximada": aprox, "status": st,
                     "arquivado": arquivado, "status_bruto": (bruto or "")[:160],
                     "modulo_bruto": mod, "_mod": mod, "_text": text})
    # mesmo módulo escrito de jeitos diferentes ("Login Social" × "LoginSocial", e os sinônimos do local.modules.json)
    # vira um rótulo só
    by_key = defaultdict(Counter)
    for a in adrs:
        k = module_key(a["_mod"])
        canon = MODULE_ALIASES.get(k)
        if canon:
            a["_mod"], k = canon, module_key(canon)
        a["_mkey"] = k
        if k:
            by_key[k][a["_mod"]] += 1
    for a in adrs:
        k = a["_mkey"]
        a["modulo"] = by_key[k].most_common(1)[0][0] if k else "(sem módulo)"
        a.pop("_mod", None)
    return adrs


def module_key(label):
    return re.sub(r"[^a-z0-9]", "", _fold(label))


def clean_module(raw):
    """1º módulo da linha "Módulos afetados": sem link/marcação, cortado no 1º separador
    (vírgula, parêntese, ponto e vírgula, " / ", "▸", " — ", "→", "·"; "/" colado só quando não é
    parte do nome, como "IA/LLM"), sem sufixo "_Module"."""
    mod = re.sub(r"\[\[([^\]|]+)\|([^\]]+)\]\]", r"\2", raw)
    mod = re.sub(r"\[\[([^\]]+)\]\]", r"\1", mod)
    mod = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", mod)
    mod = mod.replace("`", "").replace("*", "").strip()
    mod = re.split(r"[,(;]", mod, maxsplit=1)[0]
    mod = re.split(r"\s+[/—–→▸·|]\s+|[▸→·]", mod, maxsplit=1)[0].strip()
    if "/" in mod and module_key(mod) not in MODULE_KEEP_SLASH:
        mod = mod.split("/", 1)[0]
    mod = re.sub(r"_(module|modulo)$", "", mod.strip(), flags=re.I).replace("_", " ")
    return mod.strip(" .:-—–")


# ───────────────────────── anotações ─────────────────────────

def collect_notes(no_history, stats):
    notes = {}
    live_inbox = set()
    if os.path.isdir(INBOX_DIR):
        live_inbox = {n for n in os.listdir(INBOX_DIR)
                      if n.endswith(".md") and not n.startswith("_") and _isfile(os.path.join(INBOX_DIR, n))}
    hist = {}
    if not no_history:
        prefix = REPO_VAULT + "/02_Memory/_inbox/"
        commits = git_log_files(REPO, prefix)
        stats["commits_inbox_repo"] = len(commits)
        for sha, d, files in commits:  # mais novo → mais velho
            for st, p, _old in files:
                if not p.startswith(prefix):
                    continue
                name = p[len(prefix):]
                if "/" in name or not name.endswith(".md") or name.startswith("_"):
                    continue
                h = hist.setdefault(name, {"first": d, "last_key": None})
                h["first"] = min(h["first"], d)
                if h["last_key"] is None and st in "AM":
                    h["last_key"] = f"{sha}:{p}"
    need = [h["last_key"] for n, h in hist.items() if n not in live_inbox and h["last_key"]]
    blobs = git_cat_blobs(REPO, need)
    for name in sorted(live_inbox | set(hist)):
        live = name in live_inbox
        text = _read(os.path.join(INBOX_DIR, name)) if live else (blobs.get(hist[name]["last_key"]) or "")
        dm = RE_DAY_PREFIX.match(name)
        if dm:
            d = _mk_date(*dm.groups())
        elif name in hist:
            d = hist[name]["first"]
        else:
            d = _mtime_date(os.path.join(INBOX_DIR, name))
        _fm, body = split_frontmatter(text)
        notes["inbox/" + name] = {"id": "inbox/" + name, "arquivo": "02_Memory/_inbox/" + name,
                                  "titulo": first_h1(body) or name[:-3], "data": _iso(d), "tipo": "sessao",
                                  "consolidada": not live, "pendencias": "PENDENCIAS" in name.upper(),
                                  "_text": text}
    # 04_Anotações — data = 1ª aparição no git (repo ou vault), senão mtime
    firsts = {}
    if not no_history:
        pre = REPO_VAULT + "/04_Anotações/"
        firsts = first_appearance(git_log_files(REPO, pre), pre, lambda n: n.endswith(".md"))
        vpre = os.path.basename(VAULT) + "/04_Anotações/"
        for n, d in first_appearance(git_log_files(VAULT_ROOT, vpre), vpre, lambda n: n.endswith(".md")).items():
            firsts[n] = min(d, firsts.get(n, d))
    if os.path.isdir(ANOT_DIR):
        for name in sorted(os.listdir(ANOT_DIR)):
            path = os.path.join(ANOT_DIR, name)
            if not name.endswith(".md") or not _isfile(path):
                continue
            text = _read(path)
            _fm, body = split_frontmatter(text)
            d = firsts.get(name) or _mtime_date(path)
            notes["anotacao/" + name] = {"id": "anotacao/" + name, "arquivo": "04_Anotações/" + name,
                                         "titulo": first_h1(body) or name[:-3], "data": _iso(d),
                                         "tipo": "anotacao", "consolidada": False, "pendencias": False,
                                         "_text": text}
    return list(notes.values())


# ───────────────────────── modelo ─────────────────────────

def build_model(no_history):
    t0 = time.time()
    now = datetime.now(TZ)
    today = now.date()
    stats = {}
    GIT_ERRORS.clear()
    specs_raw, index = collect_specs(no_history, stats)
    specs = build_spec_models(specs_raw, index, today)
    adrs = collect_adrs()
    notes = collect_notes(no_history, stats)

    adr_by_num = {a["num"]: a for a in adrs if a["num"] is not None}
    adr_by_id = {a["id"]: a for a in adrs}
    for a in adrs:
        a["specs"] = []
    for n in notes:
        n["specs"] = []
    via_by_spec, notes_by_spec = {}, {}
    for sp in specs:
        slug = sp["slug"]
        names = [(nm, slug_regex(nm)) for nm in dict.fromkeys(sp["_link_names"])]

        def cites(text):
            return any(cites_slug(text, nm, rx) for nm, rx in names)

        via = {}
        for num in cited_adr_numbers(sp["_text"]):
            if num in adr_by_num:
                via[adr_by_num[num]["id"]] = "spec"
        for a in adrs:
            if cites(a["_text"]):
                via[a["id"]] = "ambos" if via.get(a["id"]) == "spec" else "adr"
        linked_notes = [n for n in notes if cites(n["_text"])]
        for aid in via:
            adr_by_id[aid]["specs"].append(slug)
        for n in linked_notes:
            n["specs"].append(slug)
        via_by_spec[slug], notes_by_spec[slug] = via, linked_notes
        sp["adrs"] = [{"id": aid, "via": v} for aid, v in
                      sorted(via.items(), key=lambda kv: (adr_by_id[kv[0]]["data"] or "", kv[0]), reverse=True)]
        sp["notas"] = [n["id"] for n in sorted(linked_notes, key=lambda n: n["data"] or "", reverse=True)]

    # última atividade: referência ampla (nota/ADR que cita ≥ LIGACAO_AMPLA specs, como a auditoria do
    # vault que lista as paradas) continua ligada no detalhe, mas não conta como atividade da spec
    for n in notes:
        n["ampla"] = len(n["specs"]) >= LIGACAO_AMPLA
    for a in adrs:
        a["ampla"] = len(a["specs"]) >= LIGACAO_AMPLA
    for sp in specs:
        via, linked_notes = via_by_spec[sp["slug"]], notes_by_spec[sp["slug"]]
        cands = []
        if sp["ultima_mudanca"]:
            cands.append((sp["ultima_mudanca"], "spec"))
        adr_dates = [(adr_by_id[aid]["data"], aid) for aid, v in via.items()
                     if adr_by_id[aid]["data"] and (v != "adr" or not adr_by_id[aid]["ampla"])]
        if adr_dates:
            cands.append(max(adr_dates))
        note_dates = [(n["data"], n["id"]) for n in linked_notes
                      if n["data"] and not n["pendencias"] and not n["ampla"]]
        if note_dates:
            cands.append((max(note_dates)[0], "nota"))
        if cands:
            d, src = max(cands, key=lambda c: (c[0], c[1] == "spec"))
            sp["ultima_atividade"], sp["ultima_atividade_fonte"] = d, src
            sp["dias_parada"] = (today - date.fromisoformat(d)).days
        else:
            sp["ultima_atividade"] = sp["ultima_atividade_fonte"] = sp["dias_parada"] = None
        sp["parada"] = bool(sp["conta_parada"] and (sp["dias_parada"] or 0) > PARADA_DIAS)

    for coll in (specs, adrs, notes):
        for item in coll:
            for k in ("_text", "_mkey", "_link_names"):
                item.pop(k, None)
    specs.sort(key=lambda s: s["slug"])
    adrs.sort(key=lambda a: (a["data"] or "", a["num"] or 0), reverse=True)
    notes.sort(key=lambda n: (n["data"] or "", n["id"]), reverse=True)

    abertas = [s for s in specs if not s["arquivada"]]
    notas_graf = [n for n in notes if not n["pendencias"]]   # os marcadores *PENDENCIAS* ficam à parte
    stats["git_erros"] = list(GIT_ERRORS)
    resumo = {
        "specs_total": len(specs), "specs_abertas": len(abertas),
        "specs_arquivadas": len(specs) - len(abertas),
        "specs_por_status": dict(Counter(s["status"] for s in specs)),
        "specs_paradas_30d": sum(1 for s in specs if s["parada"]),
        "specs_com_pct_index": sum(1 for s in specs if s["index"] and s["index"]["pct"] is not None),
        "adrs_total": len(adrs), "adrs_por_status": dict(Counter(a["status"] for a in adrs)),
        "adrs_arquivados": sum(1 for a in adrs if a["arquivado"]),
        "adrs_data_aproximada": sum(1 for a in adrs if a["data_aproximada"]),
        "adrs_sem_data": sum(1 for a in adrs if not a["data"]),
        "notas_total": len(notas_graf), "notas_por_tipo": dict(Counter(n["tipo"] for n in notas_graf)),
        "notas_consolidadas": sum(1 for n in notas_graf if n["consolidada"]),
        "notas_pendencias": sum(1 for n in notes if n["pendencias"]),
        "ligacoes_spec_adr": sum(len(s["adrs"]) for s in specs),
        "ligacoes_spec_nota": sum(len(s["notas"]) for s in specs),
        **stats,
    }
    return {
        "gerado_em": now.isoformat(timespec="seconds"), "hoje": today.isoformat(), "fuso": "America/Sao_Paulo",
        "com_historico": not no_history, "tempo_s": round(time.time() - t0, 2),
        "regras": {"parada_dias": PARADA_DIAS, "status_que_param": list(STATUS_QUE_PARAM),
                   "ligacao_ampla": LIGACAO_AMPLA, "linha_em_massa": LINHA_EM_MASSA},
        "projeto": os.path.basename(VAULT), "projetos": vault_projects(os.path.dirname(VAULT)),
        "fontes": {"vault": VAULT, "index": INDEX_MD, "repo": REPO, "obsidian_base": windows_path(VAULT),
                   "historico_specs": f"{REPO}:{REPO_VAULT}/01_Specs/",
                   "historico_vault": f"{VAULT_ROOT}:{os.path.basename(VAULT)}/01_Specs/",
                   "inbox_git": f"{REPO}:{REPO_VAULT}/02_Memory/_inbox/"},
        "resumo": resumo, "specs": specs, "adrs": adrs, "notas": notes,
    }


# ── outros projetos (título = seletor): mesmo modelo, montado sob demanda, sem histórico git (a cópia do vault no repo
#    é só a do projeto principal). build_model lê os caminhos globais (VAULT…): uma montagem por vez, com a trava ──
MODEL_LOCK = threading.RLock()
_BASE = [None]          # vault principal do `serve` (o do histórico git)
_PROJ = {}              # projeto -> (assinatura dos arquivos, corpo JSON)


def _project_sig(path):
    """Assinatura barata do que o modelo lê: specs (1º nível), ADRs, inbox, anotações e o _INDEX."""
    sig = []
    for sub in ("01_Specs", "02_Memory", os.path.join("02_Memory", "_inbox"), "04_Anotações"):
        try:
            with os.scandir(os.path.join(path, sub)) as it:
                for e in it:
                    if e.name.endswith(".md"):
                        st = e.stat()
                        sig.append((sub, e.name, st.st_mtime_ns, st.st_size))
        except OSError:
            pass
    try:
        st = os.stat(os.path.join(path, "00_Context", "_INDEX.md"))
        sig.append(("_INDEX", st.st_mtime_ns, st.st_size))
    except OSError:
        pass
    return hash(tuple(sorted(sig, key=repr)))


def project_json(name):
    """Corpo de /data.json?projeto=NOME (None se o nome não é um projeto do vault — nada de caminho livre)."""
    global VAULT, SPECS_DIR, INDEX_MD, MEMORY_DIR, INBOX_DIR, ANOT_DIR
    root = os.path.dirname(_BASE[0] or VAULT)
    if name not in vault_projects(root):
        return None
    pdir = os.path.join(root, name)
    sig = _project_sig(pdir)
    hit = _PROJ.get(name)
    if hit and hit[0] == sig:
        return hit[1]
    with MODEL_LOCK:
        saved = (VAULT, SPECS_DIR, INDEX_MD, MEMORY_DIR, INBOX_DIR, ANOT_DIR)
        try:
            set_vault(pdir)
            model = build_model(True)
        finally:
            VAULT, SPECS_DIR, INDEX_MD, MEMORY_DIR, INBOX_DIR, ANOT_DIR = saved
    body = json.dumps(model, ensure_ascii=False, separators=(",", ":")).encode("utf-8", "replace")
    _PROJ[name] = (sig, body)
    return body


def _u8(s):
    """UTF-8 que nunca levanta: nome de arquivo com byte inválido (surrogate do os.listdir) vira "?" em vez
    de derrubar a publicação (UnicodeEncodeError travava o status e o grafo)."""
    return s.encode("utf-8", "replace")


def embed_json(model):
    return escape_embed(json.dumps(model, ensure_ascii=False, separators=(",", ":")))


def escape_embed(s):
    """JSON pronto para dentro de <script type="application/json">: sem "<", ">", "&" nem U+2028/2029 crus."""
    return s.replace("&", "\\u0026").replace("<", "\\u003c").replace(">", "\\u003e") \
        .replace("\u2028", "\\u2028").replace("\u2029", "\\u2029")


def boot_json(status_embed, graph_embed, meta):
    """Carga embutida na página: {modo, grafo_estado, …, "status": modelo, "grafo": modelo|null}.
    status_embed/graph_embed já passaram por embed_json (ou são "null")."""
    head = embed_json(meta)
    return head[:-1] + ',"status":' + status_embed + ',"grafo":' + graph_embed + "}"


def _font_b64():
    """Google Sans (variável, eixo ótico, subconjunto latin; OFL — assets/google-sans-OFL.txt) embutida na página:
    vale no ao vivo e no retrato aberto como arquivo, sem pedir nada a servidor de fonte."""
    import base64
    try:
        with open(os.path.join(HERE, "assets", "google-sans-latin-opsz-normal.woff2"), "rb") as f:
            return base64.b64encode(f.read()).decode("ascii")
    except OSError:
        return ""   # sem o arquivo: a pilha de fontes cai para Segoe UI / system-ui


def render_page(status_embed, graph_embed, meta):
    return HTML_TEMPLATE.replace("__DATA__", boot_json(status_embed, graph_embed, meta))


def write_file_atomic(path, text):
    """Grava num temporário (dotfile, que o Obsidian ignora) e troca; se a troca for negada (arquivo aberto
    no Windows), grava direto."""
    tmp = os.path.join(os.path.dirname(os.path.abspath(path)), "." + os.path.basename(path) + ".tmp")
    try:
        with open(tmp, "w", encoding="utf-8", errors="replace") as f:
            f.write(text)
        os.replace(tmp, path)
    except OSError:
        with open(path, "w", encoding="utf-8", errors="replace") as f:
            f.write(text)
        try:
            os.remove(tmp)
        except OSError:
            pass
    return os.path.getsize(path)


def write_html(model, path, graph=None, grafo_estado=None, grafo_msg=None):
    """Retrato estático (abre por file://, sem servidor): status e grafo embutidos."""
    meta = {"modo": "retrato", "grafo_estado": grafo_estado or ("pronto" if graph else "ausente"),
            "grafo_msg": grafo_msg}
    return write_file_atomic(path, render_page(embed_json(model), embed_json(graph) if graph else "null", meta))


# ───────────────────────── grafo (vault_graph.py + networkx) ─────────────────────────

def build_graph_model(vault=None):
    """(modelo|None, estado, mensagem). networkx só é importado aqui: sem ele a aba Grafo mostra um aviso."""
    t0 = time.time()
    try:
        if HERE not in sys.path:
            sys.path.insert(0, HERE)
        import vault_graph
    except ImportError as e:
        return None, "indisponivel", (f"networkx não está disponível no python3 ({e}). "
                                      "Instale com: pip install networkx")
    G, broken, _adr = vault_graph.build(vault=vault or VAULT)
    m = vault_graph.graph_model(G, broken)
    m.update({"gerado_em": datetime.now(TZ).isoformat(timespec="seconds"), "tempo_s": round(time.time() - t0, 2),
              "vault": vault or VAULT, "memoria_dir": vault_graph.MEMORY_DIR})
    m["universo"] = build_universe_model(vault_graph, vault)
    return m, "pronto", None


def build_universe_model(vault_graph, vault=None):
    """Universo (página única /foco): o vault do Obsidian inteiro — todos os projetos —, com os grupos de cor do
    grafo nativo e a área por caminho. Com --vault numa cópia, a raiz é a pasta-mãe da cópia. Falha não derruba
    o grafo do projeto principal: a aba cai para ele."""
    try:
        t0 = time.time()
        raiz = os.path.dirname(vault or VAULT)
        G, broken, _adr = vault_graph.build(vault=raiz, universe=True, attachments=True, main=os.path.basename(vault or VAULT))
        grupos = vault_graph.obsidian_groups(os.path.join(raiz, ".obsidian", "graph.json"))
        um = vault_graph.graph_model(G, broken, universe=True, groups=grupos)
        um.update({"universo": True, "grupos": grupos, "raiz": raiz, "obsidian_raiz": windows_path(raiz),
                   "projetos": sorted({n["projeto"] for n in um["nos"]}), "memoria_dir": vault_graph.MEMORY_DIR,
                   "tempo_s": round(time.time() - t0, 2)})
        return um
    except Exception:  # noqa: BLE001
        traceback.print_exc()
        return None


def build_graph_safe(vault=None):
    try:
        return build_graph_model(vault)
    except Exception as e:  # noqa: BLE001 — o painel segue sem o grafo
        traceback.print_exc()
        return None, "erro", f"{type(e).__name__}: {e}"


HTML_TEMPLATE = r"""<!DOCTYPE html>
<html lang="pt-BR">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>AI Second Brain</title>
<script src="https://cdnjs.cloudflare.com/ajax/libs/d3/7.8.5/d3.min.js"></script>
<style>
@font-face{font-family:'Google Sans Variable';font-style:normal;font-display:swap;font-weight:400 700;
  src:url(data:font/woff2;base64,__FONT_WOFF2__) format('woff2-variations');
  unicode-range:U+0000-00FF,U+0131,U+0152-0153,U+02BB-02BC,U+02C6,U+02DA,U+02DC,U+0304,U+0308,U+0329,U+2000-206F,U+20AC,U+2122,U+2191,U+2193,U+2212,U+2215,U+FEFF,U+FFFD}
/* Design system do bi19 (app, tema Clássico, paleta "Dynamic Urban") com a moldura clara.
   Valores: dev19/app/src/bi19/theme.css, DESIGN.md e themes/glass.css (moldura). Só escuro.
   Toda medida de margem/padding/gap sai da escala de 4 px; raio só --radius-md/-pill/-full; cor só por token. */
:root{
  color-scheme:dark;
  font-size:106.25%;   /* letra base 17 px, como o app do bi19 (a Google Sans pública não tem hinting) */
  /* marca */
  --bi19-noir:#17212B; --bi19-mint:#ECF0F1; --bi19-saffron:#F39C12; --bi19-saffron-soft:#FAD7B8; --bi19-orange:#E67E22;
  --bi19-accent:var(--bi19-orange);
  --bi19-panel:var(--bi19-noir); --bi19-surface:#2C3E50; --bi19-surface-2:#34495E;
  --bi19-text:#ECF0F1;        /* 14,2:1 no painel, 9,5:1 no cartão */
  --bi19-text-soft:#CBD3D8;   /* 10,8:1 no painel, 7,2:1 no cartão */
  --bi19-line:color-mix(in srgb,var(--bi19-mint) 16%,transparent);
  --bi19-line-strong:color-mix(in srgb,var(--bi19-mint) 34%,transparent);
  --bi19-ok:#A6EBCB; --bi19-bad:#FFC6BC; --bi19-page:#FFFFFF;
  /* moldura clara: o fundo da tela fica atrás do menu e do painel; o menu não tem cor própria */
  --bi19-frame-bg:#ECF0F1; --bi19-frame-gap:var(--spacing-sm); --bi19-frame-radius:0.625rem; --bi19-rail-w:5.25rem;
  --bi19-rail-text:#172B36; --bi19-rail-hover:rgba(23,43,54,0.08); --bi19-rail-active:rgba(23,43,54,0.14);
  --bi19-rail-active-ink:color-mix(in srgb,var(--bi19-saffron) 50%,var(--bi19-noir));
  /* espaço: escala fixa de 4 px · raio: só três · tipo */
  --spacing-2xs:0.125rem; --spacing-xs:0.25rem; --spacing-sm:0.5rem; --spacing-md:0.75rem;
  --spacing-lg:1rem; --spacing-xl:1.5rem; --spacing-2xl:2rem;
  --radius-md:0.35rem; --radius-pill:999px; --radius-full:50%;
  --font:'Google Sans Variable','Google Sans','Segoe UI',system-ui,sans-serif;
  --mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;
  --fs-h1:1.5rem; --fs-h3:1.3rem; --fs-h2:1.05rem; --fs-p:0.875rem; --fs-caption:0.75rem; --fs-micro:0.6875rem;
  --fs-kpi:1.75rem; --fs-rail:0.68rem; --fs-rail-sm:0.6rem;
  /* papéis do painel (o CSS e o canvas leem estes nomes) */
  --page:var(--bi19-panel); --surface:var(--bi19-surface); --surface-2:var(--bi19-surface-2); --hover:var(--bi19-surface-2);
  --ink:var(--bi19-text); --ink-2:var(--bi19-text-soft); --muted:var(--bi19-text-soft);
  --grid:var(--bi19-line); --axis:var(--bi19-line-strong); --border:var(--bi19-line); --border-strong:var(--bi19-line-strong);
  --accent:var(--bi19-accent);
  --accent-track:color-mix(in srgb,var(--bi19-mint) 14%,transparent);
  --accent-wash:color-mix(in srgb,var(--bi19-accent) 16%,transparent);
  --focus:var(--bi19-saffron);
  --warn:var(--bi19-saffron); --warn-ink:var(--bi19-saffron-soft); --good:var(--bi19-ok);
  /* status das specs: uma cor distinta por etapa, na ordem da legenda (validada: faixa de luminosidade, croma, separação
     para daltonismo e visão normal entre vizinhos; o magenta fica abaixo de 3:1 no cartão e vem sempre com rótulo).
     Editáveis na legenda da linha do tempo; arquivada e sem status = neutros */
  --st-rascunho:#d55181; --st-aprovada:#3987e5; --st-dev:#c98500; --st-impl:#199e70;
  --st-estudo:#9085e9; --st-guia:#e66767; --st-arquivada:#7f8c8d; --st-desconhecido:#a3b1b2;
  /* mapa de calor (ADRs por dia): rampa sequencial de um azul, clara = mais (validada no cartão) */
  --heat-1:#256abf; --heat-2:#3987e5; --heat-3:#6da7ec; --heat-4:#9ec5f4; --heat-5:#cde2fb;
  /* séries categóricas: ordem fixa validada para daltonismo (passos do escuro); abaixo de 3:1 no cartão o gráfico
     tem tabela e legenda (alívio exigido) */
  --c1:#3987e5; --c2:#d95926; --c3:#199e70; --c4:#c98500; --c5:#d55181; --c6:#008300; --c7:#9085e9; --c8:#e66767;
  --c-outros:#7f8c8d;
  --shadow:0 10px 30px rgba(0,0,0,0.45); --scrim:rgba(10,15,22,0.6);
}
*{box-sizing:border-box}
[hidden]{display:none !important}
html{-webkit-text-size-adjust:100%;height:100%}
/* gaveta aberta: trava a rolagem do painel (quem rola é ele, não a página) */
html.noscroll #panel{overflow:hidden}
body{margin:0;height:100%;overflow:hidden;background:var(--bi19-frame-bg);color:var(--ink);font:var(--fs-p)/1.45 var(--font)}
:where(button,input,select,textarea){font-family:inherit}
.ico{width:1em;height:1em;flex:none;vertical-align:-0.125em;stroke-width:1.75}
/* ── moldura: menu fixo à esquerda + painel arredondado ── */
.shell{height:100%;padding:var(--bi19-frame-gap) var(--bi19-frame-gap) var(--bi19-frame-gap) var(--bi19-rail-w)}
#panel{position:relative;height:100%;overflow:auto;background:var(--page);border-radius:var(--bi19-frame-radius);color:var(--ink);display:flex;flex-direction:column}
.rail{position:fixed;z-index:30;top:0;left:0;width:var(--bi19-rail-w);height:100%;padding:var(--spacing-lg) var(--spacing-sm) var(--bi19-frame-gap);display:flex;flex-direction:column;align-items:center;gap:var(--spacing-xs);color:var(--bi19-rail-text)}
.rail .brand{display:block;margin-bottom:var(--spacing-lg)}
.rail .brand svg{display:block;width:2.5rem;height:auto}
nav.tabs{display:flex;flex-direction:column;gap:var(--spacing-xs);width:100%}
nav.tabs button{appearance:none;border:0;background:none;width:100%;padding:var(--spacing-sm) 0;border-radius:var(--radius-md);display:flex;flex-direction:column;align-items:center;gap:var(--spacing-xs);color:var(--bi19-rail-text);font:inherit;font-size:var(--fs-rail);letter-spacing:0.01em;cursor:pointer}
nav.tabs button .ico{font-size:1.25rem}
nav.tabs button>span{max-width:100%;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
nav.tabs button:hover{background:var(--bi19-rail-hover)}
nav.tabs button[aria-selected="true"]{color:var(--bi19-rail-active-ink);font-weight:600;background:var(--bi19-rail-active)}
/* foco no fundo claro: o amarelo da marca não chega a 3:1 ali; vai o laranja escurecido do item ativo */
nav.tabs button:focus-visible{outline:2px solid var(--bi19-rail-active-ink);outline-offset:-2px}
/* ── página dentro do painel ── */
header.top{position:sticky;top:0;z-index:20;background:var(--page);border-bottom:1px solid var(--grid);padding:var(--spacing-xl) var(--spacing-2xl) var(--spacing-lg)}
.hrow{display:flex;align-items:center;justify-content:space-between;gap:var(--spacing-sm) var(--spacing-lg);flex-wrap:wrap}
h1{font-size:var(--fs-h1);line-height:1.25;margin:0;font-weight:650;letter-spacing:-0.01em}
/* título = seletor de projeto: lê como título, vira campo no hover/foco */
.ptitle{display:flex;align-items:baseline;flex-wrap:wrap;gap:var(--spacing-xs) var(--spacing-sm)}
.ptitle select{font:inherit;color:var(--ink);background:transparent;border:1px solid transparent;border-radius:var(--radius-md);padding:0 var(--spacing-xs);min-height:0;max-width:100%;cursor:pointer;field-sizing:content}
.ptitle select:hover{border-color:var(--border-strong);background:var(--surface)}
.ptitle select:disabled{cursor:default;appearance:none;-webkit-appearance:none}
.ptitle select:disabled:hover{border-color:transparent;background:transparent}
.ptitle select option{background:var(--surface);color:var(--ink);font-size:var(--fs-p);font-weight:400}
.lead{color:var(--ink-2);font-size:var(--fs-p);margin:var(--spacing-xs) 0 0}
main.wrap{width:100%;max-width:none;padding:var(--spacing-xl) var(--spacing-2xl) var(--spacing-2xl);flex:1 0 auto}
/* aba Grafo: o universo ocupa o painel inteiro (sem cabeçalho nem rodapé; o indicador ao vivo vai para a coluna) */
#panel.is-uni{overflow:hidden}
#panel.is-uni>header.top,#panel.is-uni>footer{display:none}
#panel.is-uni>main.wrap{max-width:none;padding:0;flex:1 1 auto;min-height:0;display:flex;flex-direction:column}
#panel.is-uni #p-grafo{flex:1 1 auto;min-height:0}
.card{background:var(--surface);border:1px solid var(--border);border-radius:var(--radius-md);padding:var(--spacing-xl);margin-bottom:var(--spacing-lg);min-width:0}
/* saltos por scrollIntoView param abaixo do cabeçalho sticky (--hdr-h medido no JS; 0 quando ele é estático) */
.card,.gwrap,[role="tabpanel"]{scroll-margin-top:calc(var(--hdr-h, 0px) + var(--spacing-md))}
.card h2{font-size:var(--fs-h2);margin:0;font-weight:650}
.caption{color:var(--muted);font-size:var(--fs-caption);margin:var(--spacing-sm) 0 0}
details.method{font-size:var(--fs-caption);color:var(--ink-2);margin:var(--spacing-sm) 0 0}
details.method summary{cursor:pointer;color:var(--ink-2)}
details.method ul{margin:var(--spacing-xs) 0 0;padding-left:var(--spacing-lg)}
details.method li{margin:var(--spacing-xs) 0}
.empty{color:var(--muted);font-size:var(--fs-p);margin:var(--spacing-md) 0}
:focus-visible{outline:2px solid var(--focus);outline-offset:2px}
/* KPIs */
.kpis{display:grid;grid-template-columns:repeat(auto-fit,minmax(8rem,1fr));gap:var(--spacing-sm);margin-bottom:var(--spacing-sm)}
.kpi{appearance:none;font:inherit;text-align:left;color:var(--ink);padding:var(--spacing-md) var(--spacing-lg);border:1px solid var(--border);border-radius:var(--radius-md);background:var(--surface);cursor:pointer;min-width:0;display:flex;flex-direction:column;justify-content:space-between;gap:var(--spacing-xs)}
.kpi:hover{background:var(--hover)}
.kpi[aria-pressed="true"]{border-color:var(--accent);box-shadow:inset 0 0 0 1px var(--accent)}
.kpi .lbl{display:flex;align-items:center;gap:var(--spacing-xs);color:var(--ink-2);font-size:var(--fs-caption)}
.kpi .val{display:block;font-size:var(--fs-kpi);font-weight:650;line-height:1.15}
.sw{display:inline-block;width:0.625rem;height:0.625rem;border-radius:var(--radius-md);flex:none}
.hatch{background:repeating-linear-gradient(135deg,var(--axis) 0 2px,var(--surface-2) 2px 5px)}
.outline{background:var(--surface);border:1.5px dashed var(--st-desconhecido)}
/* filtros e controles */
.filters{display:flex;flex-wrap:wrap;gap:var(--spacing-sm) var(--spacing-md);align-items:center;margin:var(--spacing-md) 0}
.fgroup{display:inline-flex;align-items:center;gap:var(--spacing-xs)}
.flabel{color:var(--muted);font-size:var(--fs-caption)}
input[type="search"],input[type="text"],select{font:inherit;font-size:var(--fs-p);color:var(--ink);background:var(--surface-2);border:1px solid var(--border-strong);border-radius:var(--radius-md);padding:var(--spacing-xs) var(--spacing-sm);min-height:2.25rem;max-width:100%}
input[type="search"]::placeholder,input[type="text"]::placeholder{color:var(--ink-2);opacity:0.85}
input[type="search"]{flex:1 1 13rem;min-width:0;max-width:20rem}
input:focus-visible,select:focus-visible{outline:2px solid var(--focus);outline-offset:1px}
/* alternância (2 a 4 opções) = .bi19-segmented: grupo em surface-2, ativo em pêssego com texto noir */
.seg{display:inline-flex;padding:var(--spacing-2xs);border-radius:var(--radius-md);background:var(--surface-2);border:1px solid var(--border)}
.seg button{appearance:none;border:0;background:none;color:var(--ink-2);font:inherit;font-size:var(--fs-p);padding:var(--spacing-xs) var(--spacing-lg);border-radius:var(--radius-md);cursor:pointer}
.seg button:hover{color:var(--ink)}
.seg button{display:inline-flex;align-items:center;gap:var(--spacing-xs)}
.seg button .ico{font-size:1rem}
/* barra de visualização (Kanban | Tabela, Barras | Calor | Linha) acima dos filtros */
.vbar{display:flex;align-items:center;gap:var(--spacing-md);margin-bottom:var(--spacing-xs)}
/* legenda de status editável: a bolinha é o seletor de cor */
.lgst{display:inline-flex;align-items:center;gap:var(--spacing-xs);cursor:pointer}
.seg button[aria-pressed="true"]{background:var(--bi19-saffron-soft);color:var(--bi19-noir);font-weight:600}
label.chk{display:inline-flex;gap:var(--spacing-xs);align-items:center;color:var(--ink-2);cursor:pointer;font-size:var(--fs-p)}
label.chk input{accent-color:var(--bi19-saffron)}
.count{color:var(--muted);font-size:var(--fs-caption);margin-left:auto}
/* botão secundário do bi19 (.bi19-btn--quiet, tamanho --sm): contorno, hover só de fundo */
.btn{appearance:none;display:inline-flex;align-items:center;justify-content:center;gap:var(--spacing-xs);min-height:1.85rem;padding:0 var(--spacing-sm);border:1px solid var(--border-strong);border-radius:var(--radius-md);background:transparent;color:var(--ink);font:600 var(--fs-caption)/1 var(--font);cursor:pointer;white-space:nowrap}
.btn:hover{background:var(--surface-2)}
.btn .ico{font-size:1rem}
.btn:disabled{opacity:.45;cursor:not-allowed}
.btn:disabled:hover{background:transparent}
/* primário do bi19 (.bi19-btn): amarelo cheio, texto noir 7,4:1; uma ação principal por área */
.btn.primary{background:var(--bi19-saffron);border-color:transparent;color:var(--bi19-noir)}
.btn.primary:hover{background:color-mix(in srgb,var(--bi19-saffron) 86%,var(--bi19-page))}
input[type="color"]{width:2.25rem;height:2.25rem;padding:var(--spacing-2xs);border:1px solid var(--border-strong);border-radius:var(--radius-md);background:var(--surface-2);cursor:pointer}
input[type="color"]::-webkit-color-swatch-wrapper{padding:0}
input[type="color"]::-webkit-color-swatch{border:0;border-radius:var(--radius-md)}
input[type="color"]::-moz-color-swatch{border:0;border-radius:var(--radius-md)}
/* lista de specs */
table.list{width:100%;border-collapse:collapse;font-size:var(--fs-p)}
table.list th{font-size:var(--fs-caption);font-weight:600;color:var(--ink-2);text-align:left;padding:var(--spacing-sm);border-bottom:1px solid var(--grid);white-space:nowrap}
table.list td{padding:var(--spacing-sm);border-bottom:1px solid var(--grid);vertical-align:middle}
table.list tr.grp th{background:var(--surface-2);color:var(--ink);font-size:var(--fs-p);padding:var(--spacing-sm)}
table.list tr.grp th .gc{color:var(--ink-2);font-weight:500}
table.list tr.row:hover td{background:var(--hover)}
.lst-wrap{overflow-x:auto}
.num{text-align:right;font-variant-numeric:tabular-nums;white-space:nowrap}
button.link{appearance:none;background:none;border:0;padding:0;color:var(--ink);font:inherit;font-weight:600;text-align:left;cursor:pointer;line-height:1.35}
button.link:hover{text-decoration:underline;text-decoration-color:var(--accent);text-underline-offset:3px}
.slug{color:var(--muted);font-size:var(--fs-caption);overflow-wrap:anywhere}
.note{font-size:var(--fs-caption);color:var(--ink-2);margin-top:var(--spacing-xs)}
/* pílula do bi19: raio pílula, peso 600, texto cheio sobre fundo neutro (contorno leve: some no hover da linha sem ele) */
.badge{display:inline-flex;align-items:center;gap:var(--spacing-xs);border:1px solid var(--border);border-radius:var(--radius-pill);padding:var(--spacing-2xs) var(--spacing-sm);font-size:var(--fs-caption);font-weight:600;color:var(--ink);white-space:nowrap;background:var(--surface-2)}
.dot{width:0.5rem;height:0.5rem;border-radius:var(--radius-full);flex:none;display:inline-block}
.meter{display:flex;align-items:center;gap:var(--spacing-sm);min-width:7rem}
.meter .track{flex:1;height:0.375rem;border-radius:var(--radius-pill);background:var(--accent-track);overflow:hidden;min-width:3.5rem}
.meter .fill{height:100%;background:var(--accent);border-radius:var(--radius-pill)}
.meter .pct{font-variant-numeric:tabular-nums;font-weight:600;min-width:2.5rem;text-align:right}
.src{display:block;color:var(--muted);font-size:var(--fs-micro);line-height:1.3}
.cellv{display:inline-block}
.stale{display:inline-flex;align-items:center;gap:var(--spacing-xs);font-weight:650;color:var(--ink)}
.warnicon{color:var(--warn)}
.spark{display:block}
.dim{color:var(--muted)}
/* gráficos */
.chart{width:100%;position:relative;min-height:2.5rem}
.chart svg{display:block}
.tick{fill:var(--ink-2);font-size:var(--fs-micro);font-variant-numeric:tabular-nums}
.vlabel{fill:var(--ink-2);font-size:var(--fs-micro);font-weight:600;font-variant-numeric:tabular-nums}
.endlabel{fill:var(--ink-2);font-size:var(--fs-micro)}
.endlabel tspan.v{fill:var(--ink);font-weight:650}
.chart-head{display:flex;justify-content:space-between;align-items:flex-start;gap:var(--spacing-sm) var(--spacing-md);flex-wrap:wrap;margin-bottom:var(--spacing-sm)}
.chart-head .sub{color:var(--ink-2);font-size:var(--fs-caption);margin-top:var(--spacing-2xs)}
.legend{display:flex;flex-wrap:wrap;gap:var(--spacing-xs) var(--spacing-md);margin:var(--spacing-xs) 0 var(--spacing-sm);font-size:var(--fs-caption);color:var(--ink-2)}
.legend span{display:inline-flex;align-items:center;gap:var(--spacing-xs)}
.legend b{color:var(--ink);font-weight:600;font-variant-numeric:tabular-nums}
.lkey{display:inline-block;width:0.875rem;height:2px;border-radius:1px}
table.data{width:100%;border-collapse:collapse;font-size:var(--fs-caption);margin-top:var(--spacing-sm)}
table.data th,table.data td{padding:var(--spacing-xs) var(--spacing-sm);border-bottom:1px solid var(--grid);text-align:left}
table.data th{color:var(--ink-2);font-weight:600;font-size:var(--fs-caption)}
table.data td.num,table.data th.num{text-align:right}
.scroll-x{overflow-x:auto}
/* linha do tempo (a altura da linha é medida do desenho: fica em px) */
.tl{position:relative}
.tl-axis{display:grid;align-items:end;background:var(--surface);position:sticky;z-index:5;border-bottom:1px solid var(--grid)}
.tl-row{display:grid;align-items:center;height:24px}
.tl-row .lbl{min-width:0;padding-right:var(--spacing-sm)}
.tl-row .lbl button{display:block;max-width:100%;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-weight:500;font-size:var(--fs-caption)}
.tl-row:hover{background:var(--hover)}
.tl-over{position:absolute;top:0;bottom:0;width:1px;pointer-events:none}
.tl-over.grid{background:var(--grid)}
.tl-over.today{background:var(--ink-2)}
.tl-rows{position:relative}
.tl-row.narrow{display:block;height:auto;padding:var(--spacing-xs) 0;border-bottom:1px solid var(--grid)}
.tl-row.narrow .lbl{padding:0}
.tl-row.narrow svg{display:block;margin-top:var(--spacing-2xs)}
/* gaveta de detalhe */
.scrim{position:fixed;inset:0;background:var(--scrim);z-index:40}
.drawer{position:fixed;top:0;right:0;bottom:0;width:min(41rem,100vw);background:var(--surface);border-left:1px solid var(--border);box-shadow:var(--shadow);z-index:41;overflow-y:auto;overflow-x:hidden;padding:var(--spacing-lg) var(--spacing-xl) var(--spacing-2xl);color:var(--ink)}
.drawer h2{font-size:var(--fs-h3);line-height:1.3;margin:0 0 var(--spacing-xs);font-weight:650}
/* topo fixo da gaveta: indicador ao vivo (atualização/reconexão visíveis enquanto se lê) + Fechar */
.drhead{position:sticky;top:calc(-1 * var(--spacing-lg));z-index:3;display:flex;align-items:center;gap:var(--spacing-sm);margin:calc(-1 * var(--spacing-lg)) calc(-1 * var(--spacing-xl)) var(--spacing-sm);padding:var(--spacing-md) var(--spacing-xl) var(--spacing-sm);background:var(--surface);border-bottom:1px solid var(--grid)}
.drhead .close{margin-left:auto;flex:none}
.drhead .live{font-size:var(--fs-caption);padding:var(--spacing-2xs) var(--spacing-sm)}
.drawer h3{font-size:var(--fs-h2);margin:var(--spacing-xl) 0 var(--spacing-sm);font-weight:650}
.stline{display:flex;flex-wrap:wrap;gap:var(--spacing-sm);align-items:center;margin:var(--spacing-md) 0 var(--spacing-xs)}
.stx{color:var(--ink-2);font-size:var(--fs-p)}
.tagline{font-size:var(--fs-caption);color:var(--ink-2);margin-top:var(--spacing-xs);overflow-wrap:anywhere}
.facts{display:grid;grid-template-columns:repeat(auto-fill,minmax(10rem,1fr));gap:var(--spacing-sm) var(--spacing-lg);margin:var(--spacing-md) 0 var(--spacing-xs)}
.facts div{font-size:var(--fs-p);min-width:0;overflow-wrap:anywhere}
.facts span{display:block;color:var(--muted);font-size:var(--fs-caption)}
.arch{background:var(--surface-2);border-radius:var(--radius-md);padding:var(--spacing-sm) var(--spacing-md);font-size:var(--fs-p);margin-top:var(--spacing-md);overflow-wrap:anywhere}
.arch b{font-weight:600}
.seq{font-size:var(--fs-caption);color:var(--ink-2);margin-top:var(--spacing-xs);overflow-wrap:anywhere}
.mini{list-style:none;margin:0;padding:0}
.mini li{display:grid;grid-template-columns:5.25rem 1fr;gap:var(--spacing-sm);padding:var(--spacing-xs) 0;border-bottom:1px solid var(--grid);font-size:var(--fs-p)}
.mini li .d{color:var(--muted);font-variant-numeric:tabular-nums}
.mini li .via{display:block;color:var(--muted);font-size:var(--fs-micro)}
/* tooltip */
#tip{position:fixed;z-index:60;pointer-events:none;background:var(--surface);color:var(--ink);border:1px solid var(--border-strong);border-radius:var(--radius-md);box-shadow:var(--shadow);padding:var(--spacing-sm) var(--spacing-md);font-size:var(--fs-caption);max-width:20rem}
#tip .t{color:var(--ink-2);margin-bottom:var(--spacing-xs);font-size:var(--fs-caption)}
#tip .r{display:flex;align-items:center;gap:var(--spacing-sm);line-height:1.55}
#tip .r b{font-variant-numeric:tabular-nums;min-width:1.5rem;text-align:right}
#tip .r .k{width:0.75rem;height:2px;border-radius:1px;flex:none}
#tip .tot{border-top:1px solid var(--grid);margin-top:var(--spacing-xs);padding-top:var(--spacing-xs);color:var(--ink-2)}
/* tabela de ADRs / notas */
table.rows{width:100%;border-collapse:collapse;font-size:var(--fs-p)}
table.rows th{font-size:var(--fs-caption);font-weight:600;color:var(--ink-2);text-align:left;padding:var(--spacing-sm);border-bottom:1px solid var(--grid);white-space:nowrap}
table.rows td{padding:var(--spacing-sm);border-bottom:1px solid var(--grid);vertical-align:top}
table.rows td.t{overflow-wrap:anywhere}
table.rows td.m{overflow-wrap:break-word;min-width:5.5rem}
table.rows th.num,table.rows td.num{text-align:right}
.chips{display:flex;flex-wrap:wrap;gap:var(--spacing-xs)}
.chip{appearance:none;font:inherit;font-size:var(--fs-micro);font-weight:600;color:var(--ink);background:var(--surface-2);border:1px solid var(--border);border-radius:var(--radius-pill);padding:var(--spacing-2xs) var(--spacing-sm);cursor:pointer;max-width:100%;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.chip:hover{border-color:var(--border-strong)}
/* ao vivo × retrato */
.live{display:inline-flex;align-items:center;gap:var(--spacing-sm);font-size:var(--fs-caption);font-weight:600;color:var(--ink);border:1px solid var(--border);border-radius:var(--radius-pill);padding:var(--spacing-xs) var(--spacing-md) var(--spacing-xs) var(--spacing-sm);background:var(--surface-2);transition:background-color .6s ease,border-color .6s ease;max-width:100%;min-width:0}
.live > span:last-child{overflow:hidden;text-overflow:ellipsis;white-space:nowrap;min-width:0}
.live .ld{width:0.5rem;height:0.5rem;border-radius:var(--radius-full);flex:none;background:var(--muted)}
.live.on .ld{background:var(--good)}
.live.wait .ld{background:var(--warn)}
.live.off .ld{background:transparent;border:1.5px solid var(--muted)}
.live code{font-family:var(--mono);font-size:var(--fs-caption);color:var(--ink)}
.live.flash{background:var(--accent-wash);border-color:var(--accent)}
/* abrir no Obsidian */
a.obs{display:inline-flex;align-items:center;gap:var(--spacing-xs);color:var(--ink-2);font-size:var(--fs-caption);font-weight:500;text-decoration:none;border-radius:var(--radius-md);padding:var(--spacing-2xs) var(--spacing-xs);vertical-align:middle;white-space:nowrap}
a.obs:hover{color:var(--ink);background:var(--surface-2)}
a.obs .ico{font-size:0.875rem}
a.obs.txt{border:1px solid var(--border-strong);min-height:1.85rem;padding:0 var(--spacing-sm);font-weight:600;color:var(--ink)}
.acts{display:flex;flex-wrap:wrap;gap:var(--spacing-xs);align-items:center;margin:var(--spacing-sm) 0 var(--spacing-2xs)}
/* grafo */
.kpi .sub{display:block;font-size:var(--fs-micro);color:var(--muted);overflow:hidden;text-overflow:ellipsis;white-space:nowrap;margin-top:calc(-1 * var(--spacing-xs))}
.sw.ringk{background:var(--surface);border:2px solid var(--warn)}
.sw.hollowk{background:var(--surface);border:1.5px solid var(--ink-2);border-radius:var(--radius-full)}
.sw.round{border-radius:var(--radius-full)}
.glayout{display:grid;grid-template-columns:minmax(0,1fr) 19rem;gap:var(--spacing-md);align-items:start}
.gwrap{position:relative;height:clamp(420px,70vh,780px);border:1px solid var(--grid);border-radius:var(--radius-md);background:var(--surface);overflow:hidden}
.gwrap canvas{display:block;width:100%;height:100%;cursor:grab;touch-action:none}
/* toque: um dedo rola a PÁGINA (o mapa não prende a rolagem); dois dedos movem e dão zoom no mapa */
@media (hover:none) and (pointer:coarse){.gwrap canvas{touch-action:pan-x pan-y}}
.gwrap canvas.hit{cursor:pointer}
.gwrap canvas.drag{cursor:grabbing}
.gtools{position:absolute;top:var(--spacing-sm);right:var(--spacing-sm);display:flex;gap:var(--spacing-xs);z-index:2}
.gtools .btn{background:var(--surface);min-width:1.85rem}
.gforce{position:absolute;right:var(--spacing-sm);bottom:var(--spacing-sm);z-index:2;display:grid;grid-template-columns:auto 8.5rem auto;align-items:center;gap:var(--spacing-xs) var(--spacing-sm);background:var(--surface);border:1px solid var(--border-strong);border-radius:var(--radius-md);padding:var(--spacing-sm) var(--spacing-md);font-size:var(--fs-caption);color:var(--ink-2);cursor:default}
.gfrow{display:contents}
.gfreset{grid-column:1/-1;justify-self:end;margin-top:var(--spacing-xs)}
.gforce input[type="range"]{width:100%;margin:0;accent-color:var(--bi19-saffron);cursor:pointer}
.gforce output{min-width:4ch;text-align:right;font-variant-numeric:tabular-nums;font-weight:600;color:var(--ink)}
@media (max-width:980px){.gforce{grid-template-columns:auto 5.5rem auto}}
.gmsg{position:absolute;left:var(--spacing-sm);top:var(--spacing-sm);z-index:2;display:flex;align-items:center;gap:var(--spacing-sm);max-width:calc(100% - 16rem);background:var(--surface);border:1px solid var(--border-strong);border-radius:var(--radius-md);padding:var(--spacing-xs) var(--spacing-sm);font-size:var(--fs-caption);color:var(--ink-2)}
.gmsg .ld{width:0.5rem;height:0.5rem;border-radius:var(--radius-full);flex:none;background:var(--warn)}
.ghint{position:absolute;left:50%;bottom:var(--spacing-sm);transform:translateX(-50%);z-index:2;pointer-events:none;background:var(--surface);border:1px solid var(--border-strong);border-radius:var(--radius-md);padding:var(--spacing-xs) var(--spacing-sm);font-size:var(--fs-caption);color:var(--ink-2);opacity:0;transition:opacity .25s ease;white-space:nowrap}
.ghint.show{opacity:1}
.gpanel{border:1px solid var(--grid);border-radius:var(--radius-md);padding:var(--spacing-md) var(--spacing-lg);max-height:clamp(420px,70vh,780px);overflow-y:auto;background:var(--surface);min-width:0}
.gpanel h3{font-size:var(--fs-h2);line-height:1.3;margin:0;overflow-wrap:anywhere;font-weight:650}
.gp-head{display:flex;align-items:flex-start;justify-content:space-between;gap:var(--spacing-sm)}
/* título de seção = .bi19-eyebrow */
.gp-sec{font-size:var(--fs-caption);font-weight:600;text-transform:uppercase;letter-spacing:0.12em;color:var(--ink-2);margin:var(--spacing-md) 0 var(--spacing-xs)}
.gp-out{background:var(--surface-2);border-radius:var(--radius-md);padding:var(--spacing-sm);font-size:var(--fs-caption);margin-top:var(--spacing-sm)}
.nlist{list-style:none;margin:0;padding:0}
.nlist li{display:flex;align-items:center;gap:var(--spacing-sm);padding:var(--spacing-xs) 0;border-bottom:1px solid var(--grid);font-size:var(--fs-caption);min-width:0}
.nlist li button.link{font-weight:500;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;min-width:0;flex:1 1 auto}
.nlist .m{color:var(--muted);font-variant-numeric:tabular-nums;font-size:var(--fs-micro);flex:none}
.hints{margin:var(--spacing-sm) 0 0;padding-left:var(--spacing-lg);color:var(--ink-2);font-size:var(--fs-caption)}
.hints li{margin:var(--spacing-xs) 0}
code.alvo{font-family:var(--mono);font-size:var(--fs-caption);color:var(--ink-2);overflow-wrap:anywhere}
.isl{font-size:var(--fs-caption);color:var(--ink-2);margin:var(--spacing-md) 0 var(--spacing-xs);font-weight:600}
@media (prefers-reduced-motion:reduce){.live,.ghint{transition:none}}
/* ── aba Grafo: universo em tela cheia no painel + coluna das specs abertas ── */
#foco{display:grid;grid-template-columns:21rem minmax(0,1fr);height:100%;background:var(--page)}
.fcol{display:flex;flex-direction:column;gap:var(--spacing-sm);min-height:0;overflow-y:auto;padding:var(--spacing-lg);border-right:1px solid var(--grid);background:var(--page)}
.fhead{display:flex;align-items:center;justify-content:space-between;gap:var(--spacing-sm);flex-wrap:wrap}
.fhead h1{font-size:var(--fs-h3);margin:0}
.fsub{margin:0;font-size:var(--fs-caption);color:var(--ink-2)}
.fcol>*{flex:0 0 auto}
.fcol input[type="search"]{flex:0 0 auto;width:100%;max-width:none}
.fgrp h2{display:flex;align-items:center;gap:var(--spacing-sm);font-size:var(--fs-caption);font-weight:600;text-transform:uppercase;letter-spacing:0.12em;color:var(--ink-2);margin:var(--spacing-sm) 0}
/* contador = .bi19-count */
.fgrp h2 .n{margin-left:auto;display:inline-block;min-width:1.4rem;padding:0 var(--spacing-xs);border-radius:var(--radius-pill);background:var(--surface-2);color:var(--ink);font-weight:600;text-align:center;letter-spacing:0}
.fitem{display:flex;align-items:stretch;gap:var(--spacing-xs);border:1px solid var(--border);border-radius:var(--radius-md);margin-bottom:var(--spacing-sm);background:var(--surface)}
.fitem.sel{border-color:var(--accent);box-shadow:inset 0 0 0 1px var(--accent)}
.fpick{flex:1;min-width:0;display:flex;flex-direction:column;gap:var(--spacing-xs);text-align:left;border:0;background:none;color:var(--ink);padding:var(--spacing-sm) var(--spacing-md);border-radius:var(--radius-md);cursor:pointer;font:inherit}
.fpick:hover:not(:disabled){background:var(--hover)}
.fpick:disabled{cursor:default;opacity:.7}
.fpick:focus-visible,.fmore:focus-visible{outline:2px solid var(--focus);outline-offset:1px}
.ft{font-size:var(--fs-p);font-weight:600;line-height:1.3;overflow-wrap:anywhere}
.fmeta{display:flex;align-items:center;gap:var(--spacing-sm);font-size:var(--fs-caption);color:var(--ink-2)}
.fbar{flex:1;height:0.375rem;border-radius:var(--radius-pill);background:var(--accent-track);overflow:hidden}
.fbar>span{display:block;height:100%;background:var(--accent);border-radius:var(--radius-pill)}
.fp{font-variant-numeric:tabular-nums;font-weight:600;color:var(--ink)}
.fd{margin-left:auto;font-variant-numeric:tabular-nums;white-space:nowrap}
/* parada: o amarelo cheio não chega a 7:1 como texto no cartão; vai o pêssego */
.fd.warn{color:var(--warn-ink);font-weight:600}
.fmore{align-self:center;margin-right:var(--spacing-xs)}
.fnote{margin:auto 0 0;font-size:var(--fs-caption);color:var(--muted)}
.fmap{position:relative;min-width:0;min-height:0}
/* o céu (cosSky) e as estrelas leem estes tokens; os controles sobre o mapa viram vidro escuro do noir */
#foco .fmap{
  --space-0:#010205;--space-1:#070b17;
  --star-ctx:#ffe3b3;--star-spec:#ffa23d;--star-adr:#ff6446;--star-mem:#cddcff;--star-core:#fff6ea;--filament:#ff9466;
  --c1:var(--star-ctx);--c2:var(--star-spec);--c3:var(--star-adr);--c-outros:var(--star-mem);
  --surface:color-mix(in srgb,var(--bi19-noir) 80%,transparent);--surface-2:color-mix(in srgb,var(--bi19-surface) 88%,transparent);
  --hover:rgba(236,240,241,0.07);
  color:var(--ink)}
#foco .gwrap{height:100%;border:0;border-radius:0;background:var(--space-0)}
#foco .gpanel,#foco .gtools .btn,#foco .gmsg,#foco .gforce{backdrop-filter:blur(8px);-webkit-backdrop-filter:blur(8px)}
#foco .gtools{top:var(--spacing-md);right:var(--spacing-md)}
#foco .gforce{right:var(--spacing-md);bottom:var(--spacing-md)}
#foco .gpanel{position:absolute;top:3.25rem;right:var(--spacing-md);width:20rem;max-height:calc(100% - 4rem);z-index:3;box-shadow:var(--shadow)}
#foco .gmsg{top:auto;bottom:var(--spacing-md);left:var(--spacing-md);max-width:calc(100% - var(--spacing-xl))}
/* contador = .bi19-count */
.cnt{display:inline-block;min-width:1.4rem;padding:0 var(--spacing-xs);border-radius:var(--radius-pill);background:var(--surface-2);color:var(--ink);font-size:var(--fs-caption);font-weight:600;text-align:center;letter-spacing:0;text-transform:none}
/* legenda do universo no painel lateral: cada item mostra/oculta as estrelas dele (olho) */
.lg{display:flex;flex-direction:column;gap:var(--spacing-md)}
.lgsec{display:flex;flex-direction:column;gap:var(--spacing-2xs)}
.lgsec+.lgsec{padding-top:var(--spacing-md);border-top:1px solid var(--grid)}
.lghead{display:flex;align-items:center;justify-content:space-between;gap:var(--spacing-sm);min-height:1.85rem;margin-bottom:var(--spacing-xs)}
.lghead h2{display:inline-flex;align-items:center;gap:var(--spacing-sm);margin:0;font-size:var(--fs-caption);font-weight:600;text-transform:uppercase;letter-spacing:0.12em;color:var(--ink-2)}
.lghead .lgacts{display:flex;gap:var(--spacing-xs)}
.lgrow{display:flex;align-items:center;gap:var(--spacing-sm);min-height:2rem;padding:var(--spacing-2xs) var(--spacing-sm) var(--spacing-2xs) var(--spacing-2xs);border-radius:var(--radius-md);color:var(--ink);font-size:var(--fs-p);cursor:pointer}
.lgrow:hover{background:var(--hover)}
.lgeye{appearance:none;display:inline-flex;align-items:center;justify-content:center;width:1.75rem;height:1.75rem;flex:none;border:0;border-radius:var(--radius-md);background:none;color:var(--ink-2);cursor:pointer}
.lgeye:hover{color:var(--ink)}
.lgeye .ico{font-size:1rem}
/* a bolinha É o seletor de cor do projeto */
input[type="color"].lgcor{width:1.125rem;height:1.125rem;flex:none;padding:0;border:0;border-radius:var(--radius-full);background:none;cursor:pointer}
input[type="color"].lgcor::-webkit-color-swatch{border-radius:var(--radius-full)}
input[type="color"].lgcor::-moz-color-swatch{border-radius:var(--radius-full)}
input[type="color"].lgcor:hover{box-shadow:0 0 0 2px var(--border-strong)}
.lgrow .lgn{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.lgrow b{font-weight:600;font-variant-numeric:tabular-nums;color:var(--ink-2)}
/* oculto: texto riscado (segue ≥ 7:1) e bolinha apagada — o estado não depende só da cor */
.lgrow.off{color:var(--ink-2)}
.lgrow.off .lgn{text-decoration:line-through}
.lgrow.off .lgcor{opacity:.35}
.lgkey{display:flex;flex-wrap:wrap;gap:var(--spacing-xs) var(--spacing-md);font-size:var(--fs-caption);color:var(--ink-2);padding:var(--spacing-xs) var(--spacing-sm) 0}
.lgkey span{display:inline-flex;align-items:center;gap:var(--spacing-xs)}
/* página Specs: as abertas num quadro por etapa */
.saboard{display:grid;grid-template-columns:repeat(auto-fit,minmax(17rem,1fr));gap:var(--spacing-lg);align-items:start}
.sacol h2{display:flex;align-items:center;gap:var(--spacing-sm);font-size:var(--fs-h2);font-weight:650;margin:0 0 var(--spacing-md)}
footer{border-top:1px solid var(--border);color:var(--ink-2);font-size:var(--fs-caption);padding:var(--spacing-lg) var(--spacing-2xl) var(--spacing-xl);overflow-wrap:anywhere}
footer p{margin:0 0 var(--spacing-xs)}
footer code{font-family:var(--mono);color:var(--ink)}
@media (max-width:980px){.glayout{grid-template-columns:1fr}.gpanel{max-height:none}.gmsg{max-width:calc(100% - var(--spacing-lg));top:auto;bottom:var(--spacing-sm)}}
@media (min-width:861px) and (max-width:1180px){
  table.list .c-opt{display:none}
  table.list td.c-st .badge{padding:var(--spacing-xs);gap:0}
  table.list td.c-st .badge .bl{position:absolute;width:1px;height:1px;overflow:hidden;clip:rect(0 0 0 0);white-space:nowrap}
  table.list td,table.list th{padding-left:var(--spacing-sm);padding-right:var(--spacing-sm)}
  .meter{min-width:6rem}
}
@media (max-width:860px){
  :root{--bi19-rail-w:3.75rem}
  .rail{padding-inline:var(--spacing-2xs)}
  nav.tabs button{font-size:var(--fs-rail-sm);letter-spacing:0}   /* "Andamento" cabe nos 3,75rem do menu estreito */
  header.top{padding:var(--spacing-lg) var(--spacing-lg) var(--spacing-md)}
  main.wrap{padding:var(--spacing-lg)}
  footer{padding:var(--spacing-lg)}
  table.list thead{display:none}
  table.list,table.list tbody,table.list tr,table.list td,table.list th{display:block;width:100%}
  table.list tr.row{border-bottom:1px solid var(--grid);padding:var(--spacing-sm) 0}
  table.list td{border:0;padding:var(--spacing-xs) var(--spacing-2xs);display:flex;justify-content:space-between;align-items:center;gap:var(--spacing-md);text-align:right}
  table.list td::before{content:attr(data-label);color:var(--muted);font-size:var(--fs-caption);text-align:left;flex:none}
  table.list td.main{display:block;text-align:left}
  table.list td .cellv{text-align:right}
  table.list td.main::before{content:none}
  table.list .meter{min-width:0;width:60%}
  table.rows thead{display:none}
  table.rows,table.rows tbody,table.rows tr,table.rows td{display:block;width:100%}
  table.rows tr{border-bottom:1px solid var(--grid);padding:var(--spacing-xs) 0}
  table.rows td{border:0;padding:var(--spacing-2xs)}
}
@media (max-width:760px){
  #panel.is-uni{overflow:auto}
  #foco{grid-template-columns:1fr;grid-template-rows:62vh auto;height:auto}
  .fcol{order:2;border-right:0;border-top:1px solid var(--grid);overflow:visible}
  .fmap{order:1;height:62vh}
  #foco .gpanel{left:var(--spacing-sm);right:var(--spacing-sm);width:auto;top:auto;bottom:var(--spacing-sm);max-height:55%}
}
@media (max-width:640px){
  header.top{position:static}
  .gwrap{height:62vh}
  .drawer{padding:var(--spacing-lg) var(--spacing-lg) var(--spacing-2xl)}
  .drhead{margin:calc(-1 * var(--spacing-lg)) calc(-1 * var(--spacing-lg)) var(--spacing-sm);padding:var(--spacing-sm) var(--spacing-lg)}
  .live{border-radius:var(--radius-md);align-items:flex-start}
  .live .ld{margin-top:var(--spacing-xs)}
  .live > span:last-child{white-space:normal;overflow:visible}
  .kpi .val{font-size:var(--fs-h1)}
}
</style>
</head>
<body>
<svg width="0" height="0" style="position:absolute" aria-hidden="true" focusable="false"><defs>
<pattern id="hatch" width="5" height="5" patternUnits="userSpaceOnUse" patternTransform="rotate(45)"><rect width="5" height="5" style="fill:var(--surface-2)"></rect><line x1="0" y1="0" x2="0" y2="5" style="stroke:var(--axis);stroke-width:2"></line></pattern>
</defs></svg>
<aside class="rail" aria-label="Navegação">
<div class="brand"><svg viewBox="0 0 1781 1104" role="img" aria-label="bi19" focusable="false"><path fill="#E67E22" fill-rule="evenodd" d="M781.25,662.28 C781.38,406.36 781.09,239.51 780.48,223.22 L779.50,196.95 770.50,202.09 C765.55,204.92 757.75,209.67 753.17,212.65 C748.60,215.62 745.13,217.60 745.47,217.04 C747.78,213.31 777.02,193.06 794.50,183.08 L803.50,177.95 804.30,195.72 C805.44,221.25 806.10,727.68 805.23,915.50 L804.50,1074.50 792.76,1074.78 L781.03,1075.06 781.25,662.28 Z M1178.00,1008.50 L1178.00,942.00 1110.00,942.00 L1042.00,942.00 1042.00,932.50 L1042.00,923.00 1121.92,923.00 L1201.85,923.00 1202.17,960.55 C1202.35,981.20 1202.35,1015.40 1202.18,1036.55 L1201.85,1075.00 1189.93,1075.00 L1178.00,1075.00 1178.00,1008.50 Z M1685.00,1032.44 C1704.81,1011.85 1716.97,995.13 1728.26,972.97 C1734.88,959.99 1742.43,942.10 1741.63,941.30 C1741.38,941.04 1692.19,940.63 1632.33,940.37 C1572.48,940.12 1517.64,939.52 1510.47,939.05 C1498.99,938.29 1496.39,937.76 1488.63,934.63 C1478.31,930.48 1472.95,927.47 1466.90,922.43 C1455.56,913.00 1447.20,899.42 1442.82,883.28 C1441.07,876.83 1440.67,872.27 1440.50,856.50 C1440.39,846.05 1440.23,835.81 1440.15,833.75 L1440.00,830.00 1369.61,830.00 C1306.34,830.00 1299.15,829.84 1298.61,828.42 C1298.27,827.55 1298.00,823.27 1298.00,818.92 L1298.00,811.00 1381.00,811.00 L1464.00,811.00 1464.15,814.25 C1464.23,816.04 1464.41,826.27 1464.53,837.00 C1464.80,859.27 1466.20,866.47 1472.99,880.50 C1480.62,896.27 1492.95,907.61 1510.11,914.65 C1524.36,920.49 1516.73,920.14 1645.78,920.97 C1711.39,921.39 1765.31,921.98 1765.61,922.27 C1767.47,924.14 1749.30,961.31 1738.92,976.88 C1724.92,997.87 1701.21,1023.29 1681.96,1037.95 L1673.50,1044.39 1685.00,1032.44 Z M450.51,1018.95 C472.15,996.14 492.03,962.86 504.38,928.80 C512.81,905.51 519.22,877.10 522.37,849.00 C525.96,816.92 525.07,758.89 520.54,730.56 C514.65,693.67 501.64,652.56 487.77,627.00 C473.07,599.91 447.99,571.45 425.30,556.11 C421.56,553.58 412.71,548.53 405.63,544.89 L392.77,538.26 402.13,532.99 C407.28,530.09 413.38,526.44 415.68,524.86 C417.98,523.29 420.38,522.00 421.02,522.00 C422.95,522.00 441.06,531.63 448.70,536.73 C467.59,549.34 487.62,570.37 503.74,594.54 C521.86,621.71 537.21,665.71 544.55,711.56 C550.16,746.61 550.18,809.31 544.58,844.25 C538.20,884.07 529.68,911.69 514.55,941.50 C497.10,975.92 477.09,1000.89 450.91,1020.95 L442.50,1027.39 450.51,1018.95 Z M25.00,926.50 L25.00,917.00 132.75,916.95 C246.55,916.89 274.45,916.27 287.50,913.53 C297.42,911.44 308.62,907.67 316.50,903.76 L322.50,900.78 319.00,904.47 C307.28,916.83 285.08,928.04 263.50,932.50 C249.51,935.39 227.88,935.93 125.25,935.97 L25.00,936.00 25.00,926.50 Z M1178.00,681.99 L1178.00,485.98 1170.09,470.18 C1150.96,431.97 1138.25,414.10 1110.57,386.45 C1094.01,369.91 1077.51,356.44 1057.88,343.45 C1050.07,338.29 1043.29,333.93 1042.81,333.77 C1042.34,333.61 1042.07,326.17 1042.22,317.23 L1042.50,300.98 1057.00,309.27 C1094.91,330.92 1124.62,354.60 1149.63,383.08 C1167.10,402.99 1176.00,416.25 1190.83,444.50 L1201.85,465.50 1202.05,576.00 C1202.16,636.77 1202.19,729.59 1202.12,782.25 L1202.00,878.00 1190.00,878.00 L1178.00,878.00 1178.00,681.99 Z M1754.50,555.75 L1754.50,234.50 1751.74,220.84 C1742.17,173.54 1724.36,135.58 1696.62,103.36 C1679.70,83.71 1663.93,69.59 1644.50,56.68 C1616.76,38.26 1584.22,26.19 1549.34,21.39 C1531.46,18.93 1497.71,18.89 1482.00,21.32 C1465.95,23.80 1449.32,27.61 1437.14,31.60 C1425.80,35.31 1404.95,45.03 1392.70,52.32 C1388.42,54.87 1385.21,56.48 1385.57,55.89 C1386.95,53.65 1410.06,37.12 1418.77,32.13 C1448.53,15.10 1474.08,6.66 1510.50,1.82 C1535.92,-1.56 1570.04,0.35 1596.40,6.63 C1629.10,14.41 1662.78,30.93 1687.00,51.05 C1712.88,72.56 1735.94,100.56 1750.37,128.00 C1762.33,150.76 1768.96,169.72 1775.18,199.00 L1778.26,213.50 1779.11,328.00 C1779.97,444.67 1779.45,814.36 1778.37,854.75 L1777.78,877.00 1766.14,877.00 L1754.50,877.00 1754.50,555.75 Z M160.00,819.70 C160.00,790.35 159.70,733.18 159.34,692.67 L158.67,619.00 170.72,619.00 L182.76,619.00 183.44,662.25 C183.82,686.04 183.98,743.08 183.81,789.00 L183.50,872.50 171.75,872.78 L160.00,873.06 160.00,819.70 Z M1497.64,560.46 C1486.65,557.71 1479.43,553.44 1470.07,544.14 C1457.22,531.38 1450.59,520.80 1443.98,502.50 L1440.72,493.50 1440.80,382.50 L1440.88,271.50 1451.69,262.03 C1457.64,256.82 1462.56,252.21 1462.62,251.78 C1462.69,251.35 1462.81,250.66 1462.89,250.25 C1462.97,249.84 1463.47,250.18 1464.00,251.00 C1464.61,251.95 1464.98,293.52 1464.98,363.38 L1465.00,474.26 1468.12,483.38 C1474.25,501.27 1481.04,512.20 1494.07,525.14 C1503.73,534.74 1510.80,538.81 1522.60,541.57 C1528.01,542.84 1533.05,543.09 1546.00,542.73 C1560.47,542.32 1563.39,541.95 1569.75,539.69 C1573.74,538.28 1577.00,537.51 1577.00,537.98 C1577.00,539.42 1566.50,548.29 1560.49,551.92 C1557.38,553.81 1551.16,556.70 1546.67,558.35 C1538.91,561.21 1537.61,561.37 1521.00,561.64 C1508.14,561.85 1501.95,561.54 1497.64,560.46 Z M442.50,502.95 C443.60,501.61 447.14,497.59 450.37,494.01 C463.61,479.32 481.39,448.25 489.00,426.50 C493.23,414.43 498.31,394.37 501.16,378.50 C503.38,366.17 503.50,363.26 503.48,322.00 C503.46,274.66 503.25,272.14 496.88,240.63 C488.97,201.47 471.30,160.95 449.38,131.68 C440.10,119.29 421.76,100.52 410.50,91.88 C399.03,83.08 383.54,73.57 367.57,65.50 C341.10,52.14 319.22,44.46 292.01,38.97 C261.99,32.91 261.18,32.88 137.75,32.68 L25.00,32.50 25.00,22.75 L25.00,13.00 111.25,13.09 C158.69,13.14 217.75,13.54 242.50,13.98 C292.30,14.86 299.52,15.59 327.70,22.53 C359.34,30.33 392.01,44.44 418.50,61.74 C433.01,71.22 439.07,76.10 452.37,88.99 C475.88,111.77 493.66,139.68 507.56,175.62 C515.17,195.28 520.38,215.53 525.17,244.02 C527.30,256.65 527.44,260.36 527.45,303.00 L527.45,348.50 524.69,362.50 C518.92,391.80 513.32,409.39 503.03,430.50 C488.58,460.15 467.28,486.47 445.01,502.19 C441.15,504.91 440.79,505.02 442.50,502.95 Z M159.00,355.10 C159.00,294.00 158.64,244.00 158.21,244.00 C157.07,244.00 141.49,253.03 131.44,259.51 C126.71,262.56 123.17,264.54 123.56,263.91 C126.44,259.24 178.28,225.00 182.46,225.00 C182.76,225.00 183.00,274.94 183.00,335.98 L183.00,446.95 227.75,446.56 C263.00,446.25 274.50,445.83 281.92,444.55 C292.40,442.75 303.46,439.30 311.31,435.38 L316.50,432.79 312.50,436.99 C304.18,445.72 289.34,454.55 274.70,459.46 C259.51,464.56 251.94,465.23 203.75,465.74 L159.00,466.20 159.00,355.10 Z M1190.07,362.86 L1178.64,350.78 1178.25,192.15 C1178.04,104.91 1177.68,33.35 1177.46,33.13 C1177.25,32.91 1155.45,32.50 1129.03,32.22 C1102.62,31.94 1081.00,31.53 1081.00,31.30 C1081.00,31.08 1083.12,26.94 1085.72,22.10 L1090.44,13.30 1110.55,12.68 C1127.61,12.15 1200.80,13.46 1201.65,14.31 C1202.39,15.05 1202.99,325.77 1202.29,348.72 L1201.50,374.94 1190.07,362.86 Z M1299.00,357.44 C1299.00,352.01 1299.16,351.69 1306.25,343.19 C1331.70,312.68 1369.22,275.23 1399.60,250.01 C1416.62,235.89 1419.93,233.35 1412.03,240.49 C1388.74,261.52 1363.09,287.10 1342.83,309.50 C1335.05,318.10 1322.12,333.94 1310.78,348.75 C1304.78,356.59 1299.67,363.00 1299.43,363.00 C1299.20,363.00 1299.00,360.50 1299.00,357.44 Z M505.66,323.75 C505.38,323.06 505.16,323.62 505.16,325.00 C505.16,326.38 505.38,326.94 505.66,326.25 C505.94,325.56 505.94,324.44 505.66,323.75 Z M529.27,306.00 C529.27,303.52 529.47,302.51 529.71,303.75 C529.94,304.99 529.94,307.01 529.71,308.25 C529.47,309.49 529.27,308.48 529.27,306.00 Z M25.00,296.67 L25.00,291.18 40.75,275.34 C55.10,260.90 64.67,252.31 78.50,241.45 C81.25,239.29 77.40,243.59 69.94,251.01 C55.08,265.80 47.96,273.71 34.14,290.83 L25.00,302.15 25.00,296.67 Z M646.00,249.92 L646.00,244.84 663.75,227.16 C673.51,217.43 687.35,204.80 694.50,199.08 L707.50,188.68 694.92,200.76 C681.32,213.82 666.86,229.79 654.63,245.25 C650.38,250.61 646.71,255.00 646.46,255.00 C646.21,255.00 646.00,252.71 646.00,249.92 Z M904.00,153.64 L904.01,146.50 918.75,143.68 C946.67,138.35 976.89,126.39 1000.83,111.19 C1007.02,107.27 1011.82,104.48 1011.50,105.00 C1010.31,106.93 987.16,123.76 976.50,130.45 C970.45,134.25 959.65,140.17 952.50,143.60 C940.23,149.49 917.62,157.79 908.25,159.85 L904.00,160.79 904.00,153.64 Z M781.00,86.16 L781.00,33.30 756.11,32.58 C742.42,32.19 712.15,31.96 688.86,32.08 L646.50,32.29 646.50,22.89 L646.50,13.50 725.50,13.50 L804.50,13.50 804.76,70.24 L805.02,126.98 793.01,133.00 L781.00,139.02 781.00,86.16 Z"/><path fill="#2C3E50" fill-rule="evenodd" d="M1491.50,1102.87 C1441.06,1098.08 1397.39,1079.58 1361.04,1047.61 C1346.37,1034.70 1331.08,1017.61 1319.35,1001.00 C1297.39,969.92 1283.11,933.18 1277.55,893.50 C1276.23,884.03 1274.03,847.25 1274.01,834.25 L1274.00,830.00 1357.00,830.00 L1440.00,830.00 1440.15,833.75 C1440.23,835.81 1440.39,846.05 1440.50,856.50 C1440.67,872.27 1441.07,876.83 1442.82,883.28 C1447.20,899.42 1455.56,913.00 1466.90,922.43 C1472.95,927.47 1478.31,930.48 1488.63,934.63 C1496.39,937.76 1498.99,938.29 1510.47,939.05 C1517.64,939.52 1572.48,940.12 1632.33,940.37 C1692.19,940.63 1741.38,941.04 1741.63,941.30 C1742.43,942.09 1734.88,959.98 1728.26,973.00 C1709.62,1009.63 1677.28,1045.33 1641.92,1068.32 C1624.77,1079.48 1601.21,1089.94 1581.00,1095.38 C1554.34,1102.55 1519.12,1105.50 1491.50,1102.87 Z M0.65,1066.59 C-0.18,1032.31 -0.18,997.60 0.66,963.16 L1.32,936.00 113.41,935.97 C175.06,935.95 232.25,935.53 240.50,935.04 C248.75,934.56 259.10,933.41 263.50,932.50 C278.35,929.43 293.14,923.44 305.81,915.34 C312.25,911.23 327.66,896.56 333.49,889.00 C343.83,875.59 355.11,852.03 359.94,833.78 C363.85,819.01 365.00,806.63 365.00,779.43 C365.00,737.31 358.92,706.60 345.23,679.63 C330.99,651.59 308.73,633.63 276.80,624.44 C262.61,620.36 261.15,620.26 200.23,619.52 L158.96,619.02 159.23,755.26 L159.50,891.50 80.37,891.76 L1.24,892.01 0.48,785.26 C0.07,726.54 0.04,622.25 0.43,553.50 L1.15,428.50 6.71,414.00 C13.22,397.02 24.37,374.29 33.58,359.26 C58.64,318.33 94.67,282.32 136.66,256.26 C148.67,248.80 157.21,244.00 158.46,244.00 C158.76,244.00 159.00,294.00 159.00,355.10 L159.00,466.20 203.75,465.74 C239.46,465.36 250.40,464.93 257.92,463.60 C281.50,459.43 300.71,449.53 315.38,433.98 C330.44,418.02 341.17,396.17 346.54,370.50 C348.93,359.08 349.32,354.59 349.76,333.50 C350.30,306.79 349.36,294.61 345.60,279.78 C334.54,236.18 307.55,208.01 266.24,196.95 C259.15,195.05 254.28,194.80 208.50,194.00 L158.50,193.11 141.50,201.91 C87.07,230.08 50.08,260.42 10.72,309.14 L1.32,320.78 0.66,272.14 C-0.18,210.17 -0.18,144.69 0.66,81.63 L1.33,31.94 126.41,32.43 C262.91,32.96 262.06,32.93 292.03,38.97 C319.22,44.46 341.11,52.15 367.57,65.50 C383.54,73.57 399.03,83.08 410.50,91.88 C421.76,100.52 440.10,119.29 449.38,131.68 C471.30,160.95 488.97,201.47 496.88,240.63 C503.25,272.14 503.46,274.66 503.48,322.00 C503.50,363.26 503.38,366.17 501.16,378.50 C498.31,394.37 493.23,414.43 489.00,426.50 C484.18,440.27 473.09,462.17 464.19,475.50 C447.54,500.43 428.41,518.20 402.63,532.70 L392.75,538.25 405.63,544.88 C412.71,548.53 421.56,553.58 425.30,556.11 C447.99,571.45 473.07,599.91 487.77,627.00 C501.64,652.56 514.65,693.67 520.54,730.56 C525.07,758.89 525.96,816.92 522.37,849.00 C517.76,890.10 507.99,924.98 491.97,957.50 C470.82,1000.42 446.91,1027.85 408.50,1053.26 C395.45,1061.89 364.26,1077.09 349.84,1081.84 C323.96,1090.38 320.22,1091.04 291.50,1092.02 C277.20,1092.52 206.06,1093.05 133.40,1093.21 L1.31,1093.50 0.65,1066.59 Z M622.67,1093.34 C622.30,1092.97 622.00,932.98 622.00,737.82 L622.00,382.96 628.16,367.23 C639.84,337.41 657.97,304.99 674.74,283.92 C689.41,265.50 715.01,240.33 733.00,226.64 C743.52,218.63 756.82,209.93 770.50,202.10 L779.50,196.95 780.18,217.72 C781.43,255.66 782.07,635.17 781.28,866.00 L780.50,1093.50 701.92,1093.76 C658.71,1093.90 623.04,1093.71 622.67,1093.34 Z M1018.00,1018.00 L1018.00,942.00 1098.00,942.00 L1178.00,942.00 1178.00,1018.00 L1178.00,1094.00 1098.00,1094.00 L1018.00,1094.00 1018.00,1018.00 Z M1034.75,897.25 L1018.00,896.95 1018.00,608.44 L1018.00,319.93 1020.25,321.10 C1029.02,325.67 1047.54,336.68 1058.22,343.68 C1076.52,355.68 1094.44,370.31 1110.57,386.43 C1138.28,414.14 1150.97,431.99 1170.09,470.18 L1178.00,485.98 1178.00,691.33 L1178.00,896.68 1153.25,897.34 C1129.90,897.96 1071.85,897.92 1034.75,897.25 Z M1594.01,894.75 C1594.02,894.06 1594.71,891.25 1595.54,888.50 C1596.38,885.75 1597.77,879.23 1598.62,874.00 C1599.97,865.72 1600.13,850.20 1599.84,753.48 L1599.50,642.45 1586.00,652.61 C1563.32,669.67 1545.95,678.61 1522.10,685.47 C1504.61,690.50 1496.29,691.32 1468.56,690.72 C1447.84,690.27 1442.83,689.84 1432.50,687.64 C1379.20,676.28 1345.26,653.72 1316.45,610.50 C1303.31,590.79 1292.51,565.33 1285.96,538.62 C1281.88,521.99 1277.75,496.90 1277.62,488.00 C1277.52,480.70 1277.71,480.10 1284.66,465.29 C1312.01,407.00 1343.73,362.12 1390.94,314.95 C1401.15,304.75 1416.02,290.82 1424.00,283.99 C1431.97,277.16 1438.56,271.22 1438.62,270.79 C1438.69,270.35 1438.81,269.66 1438.89,269.25 C1438.97,268.84 1439.47,269.18 1440.00,270.00 C1440.62,270.95 1440.93,312.09 1440.85,382.50 L1440.72,493.50 1443.98,502.50 C1450.59,520.80 1457.22,531.38 1470.07,544.14 C1479.74,553.75 1486.81,557.82 1498.60,560.57 C1503.95,561.82 1509.20,562.08 1522.00,561.76 C1537.30,561.38 1539.09,561.13 1546.67,558.35 C1557.93,554.21 1565.25,549.65 1573.10,541.89 C1581.58,533.51 1588.10,522.41 1592.44,509.00 C1597.79,492.45 1599.15,484.19 1599.93,463.50 C1600.77,441.18 1600.44,279.54 1599.51,263.50 C1598.80,251.12 1596.23,240.16 1591.39,228.78 C1583.53,210.32 1572.45,197.85 1556.91,189.98 C1544.33,183.61 1539.57,182.81 1516.56,183.18 L1496.46,183.50 1486.91,188.12 C1481.65,190.66 1469.53,198.01 1459.98,204.46 C1409.78,238.30 1364.16,278.39 1318.83,328.50 C1311.00,337.16 1298.09,352.97 1286.59,367.99 L1275.50,382.49 1274.88,358.99 C1273.98,324.92 1275.64,243.91 1277.48,231.69 C1286.67,170.99 1313.54,119.04 1355.83,80.19 C1374.17,63.34 1391.40,51.85 1415.48,40.40 C1434.50,31.36 1454.91,25.51 1482.00,21.32 C1497.71,18.89 1531.46,18.93 1549.34,21.39 C1584.22,26.19 1616.76,38.26 1644.50,56.68 C1663.93,69.59 1679.70,83.71 1696.62,103.36 C1724.18,135.38 1741.67,172.47 1751.72,220.28 L1754.50,233.50 1754.82,533.50 C1754.99,698.50 1754.83,847.56 1754.45,864.75 L1753.77,896.00 1673.88,896.00 C1610.64,896.00 1594.00,895.74 1594.01,894.75 Z M1153.50,369.44 C1114.77,330.61 1090.02,312.48 1041.42,287.37 L1021.33,277.00 951.32,277.00 L881.31,277.00 880.66,259.75 C880.30,250.26 880.01,225.18 880.01,204.00 L880.02,165.50 894.76,162.66 C922.73,157.26 952.44,145.56 976.50,130.45 C1003.38,113.58 1027.19,92.43 1042.77,71.56 C1047.26,65.55 1054.43,54.22 1058.72,46.38 L1066.50,32.14 1073.50,31.82 C1082.28,31.42 1176.96,32.62 1177.48,33.14 C1178.07,33.74 1178.56,348.98 1178.00,372.50 L1177.50,393.50 1153.50,369.44 Z M505.16,325.00 C505.16,323.62 505.38,323.06 505.66,323.75 C505.94,324.44 505.94,325.56 505.66,326.25 C505.38,326.94 505.16,326.38 505.16,325.00 Z M622.25,153.25 L622.50,32.50 672.50,32.18 C700.00,32.01 735.66,32.17 751.75,32.55 L781.00,33.23 781.00,89.61 L781.00,145.98 768.75,152.12 C738.46,167.29 716.47,181.19 694.56,199.00 C671.86,217.46 650.00,239.77 630.63,264.25 C626.38,269.61 622.70,274.00 622.45,274.00 C622.20,274.00 622.11,219.66 622.25,153.25 Z"/></svg></div>
<nav class="tabs" role="tablist" aria-label="Seções" aria-orientation="vertical" id="tabs"></nav>
</aside>
<div class="shell"><div id="panel">
<header class="top">
<div class="hrow"><h1 class="ptitle"><span>Andamento do</span> <select id="proj" aria-label="Projeto"></select></h1><span id="live" class="live off" aria-live="off"></span></div>
<p class="lead" id="lead"></p>
</header>
<main class="wrap">
<section id="p-grafo" role="tabpanel" aria-labelledby="tab-grafo" hidden></section>
<section id="p-specs" role="tabpanel" aria-labelledby="tab-specs" hidden></section>
<section id="p-linha" role="tabpanel" aria-labelledby="tab-linha" hidden></section>
<section id="p-adrs" role="tabpanel" aria-labelledby="tab-adrs" hidden></section>
<section id="p-notas" role="tabpanel" aria-labelledby="tab-notas" hidden></section>
</main>
<footer id="foot"></footer>
</div></div>
<div id="tip" role="tooltip" hidden></div>
<script type="application/json" id="dados">__DATA__</script>
<script>
(function(){
'use strict';
/* carga embutida: {modo:'retrato'|'ao-vivo', grafo_estado, status:{…}, grafo:{…}|null}; no modo ao vivo
   D e GR são trocados quando o servidor avisa (SSE) — por isso "let" e índices recalculáveis */
const BOOT = JSON.parse(document.getElementById('dados').textContent);
/* a aba Grafo é o universo (o vault inteiro do Obsidian, em 3D) + a coluna das specs abertas — o que era a página
   única "/" antes de o painel completo virar a página só ("/", "/foco" e "/completo" servem a mesma). FOCO segue
   como constante porque o motor do grafo pergunta por ela */
const FOCO = true;
const PANEL = document.getElementById('panel');     // quem rola é o painel (moldura do bi19), não a janela
let D = BOOT.status;
let HOJE = D.hoje;
const HAS_D3 = typeof window.d3 !== 'undefined';
const NS = 'http://www.w3.org/2000/svg';

/* ── DOM: todo texto entra por textContent/createTextNode (nunca innerHTML) ── */
function h(tag, attrs){
  const el = document.createElement(tag);
  if (attrs) for (const k in attrs){
    const v = attrs[k];
    if (v == null || v === false) continue;
    if (k === 'class') el.className = v;
    else if (k === 'text') el.textContent = v;
    else if (k.slice(0,2) === 'on') el.addEventListener(k.slice(2), v);
    else el.setAttribute(k, v === true ? '' : v);
  }
  for (let i = 2; i < arguments.length; i++) add(el, arguments[i]);
  return el;
}
function add(el, c){
  if (c == null || c === false) return;
  if (Array.isArray(c)) { c.forEach(x => add(el, x)); return; }
  el.appendChild(typeof c === 'object' ? c : document.createTextNode(String(c)));
}
function sv(tag, attrs){
  const el = document.createElementNS(NS, tag);
  if (attrs) for (const k in attrs) if (attrs[k] != null) el.setAttribute(k, attrs[k]);
  return el;
}
/* ── ícones: Lucide (os mesmos do react-icons/lu do app do bi19; ISC), traço 1,75, tamanho 1em ── */
const LU = {"list-checks":[["path",{"d":"m3 17 2 2 4-4"}],["path",{"d":"m3 7 2 2 4-4"}],["path",{"d":"M13 6h8"}],["path",{"d":"M13 12h8"}],["path",{"d":"M13 18h8"}]],"chart-gantt":[["path",{"d":"M10 6h8"}],["path",{"d":"M12 16h6"}],["path",{"d":"M3 3v16a2 2 0 0 0 2 2h16"}],["path",{"d":"M8 11h7"}]],"scroll-text":[["path",{"d":"M15 12h-5"}],["path",{"d":"M15 8h-5"}],["path",{"d":"M19 17V5a2 2 0 0 0-2-2H4"}],["path",{"d":"M8 21h12a2 2 0 0 0 2-2v-1a1 1 0 0 0-1-1H11a1 1 0 0 0-1 1v1a2 2 0 1 1-4 0V5a2 2 0 1 0-4 0v2a1 1 0 0 0 1 1h3"}]],"notebook-pen":[["path",{"d":"M13.4 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2v-7.4"}],["path",{"d":"M2 6h4"}],["path",{"d":"M2 10h4"}],["path",{"d":"M2 14h4"}],["path",{"d":"M2 18h4"}],["path",{"d":"M21.378 5.626a1 1 0 1 0-3.004-3.004l-5.01 5.012a2 2 0 0 0-.506.854l-.837 2.87a.5.5 0 0 0 .62.62l2.87-.837a2 2 0 0 0 .854-.506z"}]],"orbit":[["circle",{"cx":"12","cy":"12","r":"3"}],["circle",{"cx":"19","cy":"5","r":"2"}],["circle",{"cx":"5","cy":"19","r":"2"}],["path",{"d":"M10.4 21.9a10 10 0 0 0 9.941-15.416"}],["path",{"d":"M13.5 2.1a10 10 0 0 0-9.841 15.416"}]],"x":[["path",{"d":"M18 6 6 18"}],["path",{"d":"m6 6 12 12"}]],"arrow-up-right":[["path",{"d":"M7 7h10v10"}],["path",{"d":"M7 17 17 7"}]],"plus":[["path",{"d":"M5 12h14"}],["path",{"d":"M12 5v14"}]],"minus":[["path",{"d":"M5 12h14"}]],"scan":[["path",{"d":"M3 7V5a2 2 0 0 1 2-2h2"}],["path",{"d":"M17 3h2a2 2 0 0 1 2 2v2"}],["path",{"d":"M21 17v2a2 2 0 0 1-2 2h-2"}],["path",{"d":"M7 21H5a2 2 0 0 1-2-2v-2"}]],"shuffle":[["path",{"d":"m18 14 4 4-4 4"}],["path",{"d":"m18 2 4 4-4 4"}],["path",{"d":"M2 18h1.973a4 4 0 0 0 3.3-1.7l5.454-8.6a4 4 0 0 1 3.3-1.7H22"}],["path",{"d":"M2 6h1.972a4 4 0 0 1 3.6 2.2"}],["path",{"d":"M22 18h-6.041a4 4 0 0 1-3.3-1.8l-.359-.45"}]],"triangle-alert":[["path",{"d":"m21.73 18-8-14a2 2 0 0 0-3.48 0l-8 14A2 2 0 0 0 4 21h16a2 2 0 0 0 1.73-3"}],["path",{"d":"M12 9v4"}],["path",{"d":"M12 17h.01"}]],"external-link":[["path",{"d":"M15 3h6v6"}],["path",{"d":"M10 14 21 3"}],["path",{"d":"M18 13v6a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2V8a2 2 0 0 1 2-2h6"}]],"search":[["circle",{"cx":"11","cy":"11","r":"8"}],["path",{"d":"m21 21-4.3-4.3"}]],"palette":[["circle",{"cx":"13.5","cy":"6.5","r":".5","fill":"currentColor"}],["circle",{"cx":"17.5","cy":"10.5","r":".5","fill":"currentColor"}],["circle",{"cx":"8.5","cy":"7.5","r":".5","fill":"currentColor"}],["circle",{"cx":"6.5","cy":"12.5","r":".5","fill":"currentColor"}],["path",{"d":"M12 2C6.5 2 2 6.5 2 12s4.5 10 10 10c.926 0 1.648-.746 1.648-1.688 0-.437-.18-.835-.437-1.125-.29-.289-.438-.652-.438-1.125a1.64 1.64 0 0 1 1.668-1.668h1.996c3.051 0 5.555-2.503 5.555-5.554C21.965 6.012 17.461 2 12 2z"}]],"arrow-up":[["path",{"d":"m5 12 7-7 7 7"}],["path",{"d":"M12 19V5"}]],"arrow-down":[["path",{"d":"M12 5v14"}],["path",{"d":"m19 12-7 7-7-7"}]],"trash2":[["path",{"d":"M3 6h18"}],["path",{"d":"M19 6v14c0 1-1 2-2 2H7c-1 0-2-1-2-2V6"}],["path",{"d":"M8 6V4c0-1 1-2 2-2h4c1 0 2 1 2 2v2"}],["line",{"x1":"10","x2":"10","y1":"11","y2":"17"}],["line",{"x1":"14","x2":"14","y1":"11","y2":"17"}]],"rotate-ccw":[["path",{"d":"M3 12a9 9 0 1 0 9-9 9.75 9.75 0 0 0-6.74 2.74L3 8"}],["path",{"d":"M3 3v5h5"}]],"eye":[["path",{"d":"M2.062 12.348a1 1 0 0 1 0-.696 10.75 10.75 0 0 1 19.876 0 1 1 0 0 1 0 .696 10.75 10.75 0 0 1-19.876 0"}],["circle",{"cx":"12","cy":"12","r":"3"}]],"eye-off":[["path",{"d":"M10.733 5.076a10.744 10.744 0 0 1 11.205 6.575 1 1 0 0 1 0 .696 10.747 10.747 0 0 1-1.444 2.49"}],["path",{"d":"M14.084 14.158a3 3 0 0 1-4.242-4.242"}],["path",{"d":"M17.479 17.499a10.75 10.75 0 0 1-15.417-5.151 1 1 0 0 1 0-.696 10.75 10.75 0 0 1 4.446-5.143"}],["path",{"d":"m2 2 20 20"}]],"square-kanban":[["rect",{"width":"18","height":"18","x":"3","y":"3","rx":"2"}],["path",{"d":"M8 7v7"}],["path",{"d":"M12 7v4"}],["path",{"d":"M16 7v9"}]],"table":[["path",{"d":"M12 3v18"}],["rect",{"width":"18","height":"18","x":"3","y":"3","rx":"2"}],["path",{"d":"M3 9h18"}],["path",{"d":"M3 15h18"}]],"chart-column":[["path",{"d":"M3 3v16a2 2 0 0 0 2 2h16"}],["path",{"d":"M18 17V9"}],["path",{"d":"M13 17V5"}],["path",{"d":"M8 17v-3"}]],"chart-line":[["path",{"d":"M3 3v16a2 2 0 0 0 2 2h16"}],["path",{"d":"m19 9-5 5-4-4-3 3"}]],"calendar-days":[["path",{"d":"M8 2v4"}],["path",{"d":"M16 2v4"}],["rect",{"width":"18","height":"18","x":"3","y":"4","rx":"2"}],["path",{"d":"M3 10h18"}],["path",{"d":"M8 14h.01"}],["path",{"d":"M12 14h.01"}],["path",{"d":"M16 14h.01"}],["path",{"d":"M8 18h.01"}],["path",{"d":"M12 18h.01"}],["path",{"d":"M16 18h.01"}]]};
function ico(name, label){
  const s = sv('svg', {viewBox:'0 0 24 24', fill:'none', stroke:'currentColor', 'stroke-width':'1.75',
    'stroke-linecap':'round', 'stroke-linejoin':'round', class:'ico'});
  if (label){ s.setAttribute('role', 'img'); s.setAttribute('aria-label', label); } else s.setAttribute('aria-hidden', 'true');
  (LU[name] || []).forEach(c => s.appendChild(sv(c[0], c[1])));
  return s;
}
function fold(s){ return String(s || '').normalize('NFD').replace(/[̀-ͯ]/g, '').toLowerCase(); }
function debounce(fn, ms){ let t; return function(){ clearTimeout(t); const a = arguments; t = setTimeout(() => fn.apply(null, a), ms); }; }

/* ── datas (tudo em UTC sobre datas-calendário já locais de São Paulo) ── */
function pd(s){ const a = s.split('-'); return new Date(Date.UTC(+a[0], +a[1]-1, +a[2])); }
function ds(d){ return d.toISOString().slice(0,10); }
function addD(d, n){ return new Date(d.getTime() + n*86400000); }
function segunda(s){ const d = pd(s); return ds(addD(d, -((d.getUTCDay()+6)%7))); }
function br(s){ return s ? s.slice(8,10)+'/'+s.slice(5,7)+'/'+s.slice(0,4) : '—'; }
function brc(s){ return s ? s.slice(8,10)+'/'+s.slice(5,7) : '—'; }
function dias(a, b){ return Math.round((pd(b) - pd(a)) / 86400000); }
const MESES = ['jan','fev','mar','abr','mai','jun','jul','ago','set','out','nov','dez'];
const NF = new Intl.NumberFormat('pt-BR');
function nfmt(v){ return NF.format(v); }

/* ── status das specs: ciclo de vida = rampa ordinal de uma cor (claro → escuro) ── */
const ST = {
  'rascunho':          {l:'Rascunho',           c:'var(--st-rascunho)'},
  'aprovada':          {l:'Aprovada',           c:'var(--st-aprovada)'},
  'em-desenvolvimento':{l:'Em desenvolvimento', c:'var(--st-dev)'},
  'implementada':      {l:'Implementada',       c:'var(--st-impl)'},
  'estudo':            {l:'Estudo',             c:'var(--st-estudo)'},
  'guia':              {l:'Guia / doc viva',    c:'var(--st-guia)'},
  'desconhecido':      {l:'Sem status',         c:'var(--st-desconhecido)'},
  'arquivada':         {l:'Arquivada',          c:'var(--st-arquivada)'},
  'sem-historico':     {l:'Antes do histórico', c:'url(#hatch)'}
};
const ST_LEGEND = ['rascunho','aprovada','em-desenvolvimento','implementada','estudo','guia','desconhecido','arquivada','sem-historico'];
const GROUPS = [
  {k:'em-desenvolvimento', l:'Em desenvolvimento', st:['em-desenvolvimento']},
  {k:'aprovada',           l:'Aprovadas',          st:['aprovada']},
  {k:'rascunho',           l:'Rascunhos',          st:['rascunho']},
  {k:'implementada',       l:'Implementadas',      st:['implementada']},
  {k:'estudo-guia',        l:'Estudos e guias',    st:['estudo','guia']},
  {k:'desconhecido',       l:'Sem status declarado', st:['desconhecido']},
  {k:'arquivada',          l:'Arquivadas',         st:['arquivada']}
];
function stm(k){ return ST[k] || ST.desconhecido; }
function swatch(k, cls){
  if (k === 'sem-historico') return h('span', {class:(cls||'dot')+' hatch'});
  if (k === 'desconhecido') return h('span', {class:(cls||'dot')+' outline'});   // contorno tracejado
  return h('span', {class:cls||'dot', style:'background:'+stm(k).c});
}
function badge(k){ return h('span', {class:'badge', title:stm(k).l}, swatch(k), h('span', {class:'bl'}, stm(k).l)); }
function plural(n, um, varios){ return nfmt(n) + ' ' + (n === 1 ? um : varios); }
function warnIcon(){ const s = ico('triangle-alert'); s.classList.add('warnicon'); return s; }
function cleanMd(t){
  return String(t || '').replace(/\[\[([^\]|]+)\|([^\]]+)\]\]/g, '$2').replace(/\[\[([^\]]+)\]\]/g, '$1')
    .replace(/<br\s*\/?>/gi, ' ').replace(/[`*]/g, '').trim();
}
function shortTitle(t){
  return cleanMd(t).replace(/^\s*spec\s*[:—–-]\s*/i, '').replace(/\s*[—–-]\s*spec\s*$/i, '').trim();
}
/* ── "Abrir no Obsidian": obsidian://open?path=<caminho Windows absoluto> (só para vault em /mnt/<letra>) ── */
function obsHref(rel){
  if (!rel || rel.slice(0, 8) === 'memoria/') return null;
  const uni = GR && GR.universo && GR.obsidian_raiz &&
    (rel.indexOf('/') < 0 || (GR.projetos || []).indexOf(rel.split('/')[0]) >= 0);
  const b = uni ? GR.obsidian_raiz : (D.fontes && D.fontes.obsidian_base);
  if (!b) return null;
  return 'obsidian://open?path=' + encodeURIComponent(b + '\\' + rel.split('/').join('\\'));
}
function obsIcon(){ return ico('external-link'); }
function obsLink(rel, what, withText){
  const href = obsHref(rel);
  if (!href) return null;
  return h('a', {class:'obs' + (withText ? ' txt' : ''), href, title:'Abrir no Obsidian',
    'aria-label': withText ? null : 'Abrir ' + (what || rel) + ' no Obsidian'}, obsIcon(), withText ? 'Abrir no Obsidian' : null);
}
/* nota de sessão já consolidada saiu do inbox: o arquivo não existe mais no vault */
function notaRel(n){ return n.tipo === 'sessao' && n.consolidada ? null : n.arquivo; }

let ADR, NOTA, SPEC;             /* índices de D — recalculados em indexData() a cada versão nova */

/* ── tooltip único (valor primeiro, rótulo depois; chave de linha, não caixa) ── */
const tip = document.getElementById('tip');
let tipOwner = null, tipOff = null;
function showTip(ev, title, rows, total, off){
  if (tipOff && tipOff !== off) tipOff();
  tipOwner = ev.currentTarget || ev.target; tipOff = off || null;
  tip.replaceChildren();
  if (title) tip.appendChild(h('div', {class:'t'}, title));
  for (const r of rows){
    tip.appendChild(h('div', {class:'r'},
      r.c ? h('span', {class:'k', style:'background:'+r.c}) : null,
      r.v != null ? h('b', null, typeof r.v === 'number' ? nfmt(r.v) : r.v) : null,
      h('span', null, r.l)));
  }
  if (total != null) tip.appendChild(h('div', {class:'tot'}, 'Total: ' + nfmt(total)));
  tip.hidden = false;
  moveTip(ev);
}
function moveTip(ev){
  const pad = 14, r = tip.getBoundingClientRect();
  let x = ev.clientX + pad, y = ev.clientY + pad;
  if (ev.pointerType === 'touch'){          // acima do dedo, centrado
    x = ev.clientX - r.width / 2; y = ev.clientY - r.height - 24;
    if (y < 8) y = ev.clientY + 28;
  }
  if (x + r.width > innerWidth - 8) x = ev.pointerType === 'touch' ? innerWidth - 8 - r.width : ev.clientX - r.width - pad;
  if (y + r.height > innerHeight - 8) y = ev.clientY - r.height - pad;
  tip.style.left = Math.max(8, x) + 'px'; tip.style.top = Math.max(8, y) + 'px';
}
function hideTip(){
  tip.hidden = true; tipOwner = null;
  if (tipOff){ const f = tipOff; tipOff = null; f(); }
}
/* no toque o pointerleave vem logo após o pointerup: ali o tooltip fica até tocar fora ou rolar */
function leaveTip(ev){ if (!ev || ev.pointerType !== 'touch') hideTip(); }
document.addEventListener('pointerdown', ev => { if (!tip.hidden && ev.target !== tipOwner) hideTip(); }, true);
addEventListener('scroll', () => { if (!tip.hidden) hideTip(); }, {passive:true, capture:true});
function noD3(ctx){
  return h('p', {class:'empty'}, 'Gráfico indisponível: a biblioteca d3 (cdnjs) não carregou. ' +
    (ctx || 'Use "Ver como tabela" e a lista abaixo.'));
}

/* ── controles ── */
function seg(label, opts, cur, onpick){
  const g = h('div', {class:'fgroup'}, h('span', {class:'flabel'}, label));
  const box = h('div', {class:'seg', role:'group', 'aria-label':label});
  opts.forEach(o => {
    const b = h('button', {type:'button', 'aria-pressed': String(o.v === cur)}, o.i ? ico(o.i) : null, o.l);
    b.addEventListener('click', () => {
      box.querySelectorAll('button').forEach(bb => bb.setAttribute('aria-pressed', String(bb === b)));
      onpick(o.v);
    });
    box.appendChild(b);
  });
  g.appendChild(box);
  return g;
}
function selectEl(label, opts, cur, onchange){
  const s = h('select', {'aria-label':label, onchange: e => onchange(e.target.value)});
  for (const o of opts){ const op = h('option', {value:o.v}, o.l); if (o.v === cur) op.selected = true; s.appendChild(op); }
  return s;
}
function searchEl(ph, cur, oninput){
  const i = h('input', {type:'search', placeholder:ph, 'aria-label':ph, value:cur});
  i.addEventListener('input', debounce(() => oninput(i.value), 140));
  return i;
}

/* ════════════════ aba 1 — andamento das specs ════════════════ */
const S = {q:'', st:'', arq:false};
let specListHost, specCount, kpiBox;
function specPassa(s){
  if (!S.arq && s.arquivada) return false;
  if (S.st === 'parada'){ if (!s.parada) return false; }
  else if (S.st){ const g = GROUPS.find(g => g.k === S.st); if (g && !g.st.includes(s.status)) return false; }
  if (S.q){
    const hay = fold([s.slug, s.titulo, s.index ? s.index.tag : '', s.status_texto].join(' '));
    if (!fold(S.q).split(/\s+/).every(w => hay.includes(w))) return false;
  }
  return true;
}
let specsStale = false;   /* dados novos chegaram com a aba montada: redesenha ao mostrar */
/* página Specs: o mesmo recurso em duas visualizações (kanban das etapas | tabela de andamento), escolhida na barra */
const SV = {v: (() => { try { return localStorage.getItem('vault-panel:specs-vista') === 'tabela' ? 'tabela' : 'kanban'; } catch (e) { return 'kanban'; } })()};
let svUI = null;
function renderSpecsPage(){
  const host = document.getElementById('p-specs');
  if (!svUI){
    svUI = {kan: h('div', {id:'v-kanban'}), tab: h('div', {id:'v-tabela'})};
    host.replaceChildren(h('div', {class:'vbar'}, seg('Visualização', [{v:'kanban', l:'Kanban', i:'square-kanban'}, {v:'tabela', l:'Tabela', i:'table'}], SV.v,
      v => { SV.v = v; try { localStorage.setItem('vault-panel:specs-vista', v); } catch (e) {} renderSpecsPage(); })), svUI.kan, svUI.tab);
  }
  svUI.kan.hidden = SV.v !== 'kanban'; svUI.tab.hidden = SV.v !== 'tabela';
  if (SV.v === 'kanban') renderAbertas(); else renderSpecs();
}
function renderSpecs(){
  const host = document.getElementById('v-tabela');
  if (host.dataset.ok){
    if (specsStale){ specsStale = false; fillKpis(); drawSpecList(); }
    return;
  }
  host.dataset.ok = '1'; specsStale = false;
  kpiBox = h('div', {class:'kpis', role:'group', 'aria-label':'Specs abertas por status (clique para filtrar)'});
  fillKpis();
  host.appendChild(kpiBox);
  host.appendChild(h('details', {class:'method'},
    h('summary', null, 'Andamento = "~NN%" do _INDEX ou critérios marcados; parada = sem atividade há mais de ' + D.regras.parada_dias + ' dias. Como é calculado'),
    h('ul', null,
      h('li', null, 'Andamento: estimativa "~NN%" da tag do _INDEX (varredura mais recente) quando existe; "não iniciada" no _INDEX conta 0%; sem isso, critérios marcados ÷ total ',
        '(caixas "- [x]" nas seções cujo título começa por Critérios ou Fase; se a spec não tem essas seções, no arquivo todo). Spec no ar sem nenhuma caixa marcada fica sem medida.'),
      h('li', null, 'Última atividade: a mais recente entre a mudança da spec, o ADR ligado e a nota ligada. Não contam a edição mecânica em lote (a mesma linha em ',
        D.regras.linha_em_massa + ' ou mais specs no mesmo commit) nem a nota ou o ADR que cita ' + D.regras.ligacao_ampla + ' ou mais specs (auditoria, índice).'),
      h('li', null, 'Parada: só para rascunho, aprovada e em desenvolvimento. Estudo, guia e implementada não andam por natureza e aparecem em cinza.'))));
  const filt = h('div', {class:'filters'});
  filt.appendChild(searchEl('Buscar spec, tag ou status…', S.q, v => { S.q = v; drawSpecList(); }));
  const opts = [{v:'', l:'Todos os status'}].concat(GROUPS.map(g => ({v:g.k, l:g.l})), [{v:'parada', l:'Paradas há mais de 30 dias'}]);
  const sel = selectEl('Filtrar por status', opts, S.st, v => { S.st = v; if (v === 'arquivada') { S.arq = true; arqBox.checked = true; } drawSpecList(); });
  sel.id = 'spec-st';
  filt.appendChild(sel);
  const arqBox = h('input', {type:'checkbox', onchange: e => { S.arq = e.target.checked; drawSpecList(); }});
  filt.appendChild(h('label', {class:'chk'}, arqBox, 'Incluir arquivadas'));
  specCount = h('span', {class:'count', 'aria-live':'polite'});
  filt.appendChild(specCount);
  host.appendChild(filt);
  specListHost = h('div', {class:'card lst-wrap', style:'padding:var(--spacing-xs) var(--spacing-sm)'});
  host.appendChild(specListHost);
  drawSpecList();
}
function fillKpis(){
  const foco = kpiBox.contains(document.activeElement) ? document.activeElement.dataset.k : null;
  const abertas = D.specs.filter(s => !s.arquivada);
  kpiBox.replaceChildren();
  for (const g of GROUPS){
    if (g.k === 'arquivada') continue;
    const c = abertas.filter(s => g.st.includes(s.status)).length;
    if (!c && (g.k === 'desconhecido')) continue;
    kpiBox.appendChild(kpiTile(g.k, g.l, c, g.st.map(k => swatch(k, 'sw'))));
  }
  const par = D.specs.filter(s => s.parada).length;
  kpiBox.appendChild(kpiTile('parada', 'Paradas há mais de ' + D.regras.parada_dias + ' dias', par, [warnIcon()]));
  if (foco){ const b = kpiBox.querySelector('[data-k="' + foco + '"]'); if (b) b.focus({preventScroll:true}); }
}
function kpiTile(k, label, val, marks){
  return h('button', {type:'button', class:'kpi', 'data-k':k, 'aria-pressed':String(S.st === k),
      onclick: () => { S.st = S.st === k ? '' : k; const sel = document.getElementById('spec-st'); if (sel) sel.value = S.st; drawSpecList(); }},
    h('span', {class:'lbl'}, marks, label),
    h('span', {class:'val'}, nfmt(val)));
}
function pctOf(s){ return s.andamento_pct == null ? -1 : s.andamento_pct; }
function drawSpecList(){
  kpiBox.querySelectorAll('.kpi').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.k === S.st)));
  const list = D.specs.filter(specPassa);
  specCount.textContent = nfmt(list.length) + (list.length === 1 ? ' spec' : ' specs');
  specListHost.replaceChildren();
  if (!list.length){ specListHost.appendChild(h('p', {class:'empty'}, 'Nenhuma spec com esses filtros.')); return; }
  const t = h('table', {class:'list'});
  const cols = ['Spec','Status','Andamento','Critérios','Criada em','Última atividade','Parada','Caixas no tempo'];
  const ccls = [null, 'c-st', null, 'num', 'c-opt', null, 'num', null];
  t.appendChild(h('thead', null, h('tr', null, cols.map((c, i) => h('th', {class: ccls[i], scope:'col'}, c)))));
  for (const g of GROUPS){
    const rows = list.filter(s => g.st.includes(s.status));
    if (!rows.length) continue;
    rows.sort((a, b) => pctOf(b) - pctOf(a) || fold(a.titulo).localeCompare(fold(b.titulo)));
    const tb = h('tbody');
    tb.appendChild(h('tr', {class:'grp'}, h('th', {colspan:'8', scope:'rowgroup'}, g.l, ' ', h('span', {class:'gc'}, '· ' + rows.length))));
    for (const s of rows) tb.appendChild(specRow(s));
    t.appendChild(tb);
  }
  specListHost.appendChild(t);
}
function specRow(s){
  const nm = h('td', {class:'main', 'data-label':'Spec'},
    h('button', {type:'button', class:'link', onclick: e => openSpec(s.slug, e.currentTarget)}, shortTitle(s.titulo)),
    h('div', {class:'slug'}, s.slug, ' ', obsLink(s.arquivo, s.slug)));
  if (s.status_divergente && s.index)
    nm.appendChild(h('div', {class:'note'}, 'No _INDEX: ', stm(s.index.status).l.toLowerCase(), ' (o arquivo diz ', stm(s.status).l.toLowerCase(), ')'));
  if (s.arquivada && s.arquivado_em) nm.appendChild(h('div', {class:'note'}, 'Arquivada em ' + br(s.arquivado_em)));
  const tr = h('tr', {class:'row'}, nm, h('td', {class:'c-st', 'data-label':'Status'}, badge(s.status)));
  tr.appendChild(h('td', {'data-label':'Andamento'}, meter(s)));
  const c = s.criterios;
  tr.appendChild(h('td', {class:'num', 'data-label':'Critérios'},
    h('span', {class:'cellv'}, c.total ? c.feitos + '/' + c.total : '—',
      c.total && c.base === 'arquivo' ? h('span', {class:'src'}, 'no arquivo') : null)));
  tr.appendChild(h('td', {class:'c-opt', 'data-label':'Criada em', title: 'Fonte: ' + (s.criada_fonte || '—') + (s.criada_aproximada ? ' (dia aproximado)' : '')},
    br(s.criada_em) + (s.criada_aproximada ? ' ≈' : '')));
  const fonte = s.ultima_atividade_fonte === 'spec' ? 'na spec' : s.ultima_atividade_fonte === 'nota' ? 'nota ligada' : (s.ultima_atividade_fonte || '');
  tr.appendChild(h('td', {'data-label':'Última atividade'}, h('span', {class:'cellv'}, br(s.ultima_atividade), fonte ? h('span', {class:'src'}, fonte) : null)));
  const dp = s.dias_parada;
  let pc;
  if (dp == null) pc = '—';
  else if (s.parada) pc = h('span', {class:'stale', title:'Sem atividade há ' + dp + ' dias (acima de ' + D.regras.parada_dias + ')'}, warnIcon(), dp + ' d');
  else pc = h('span', {class: s.conta_parada ? null : 'dim', title: s.conta_parada ? null : 'Estudo, guia, implementada e arquivada não contam como paradas'}, dp + ' d');
  tr.appendChild(h('td', {class:'num', 'data-label':'Parada'}, pc));
  tr.appendChild(h('td', {'data-label':'Caixas no tempo'}, sparkline(s)));
  return tr;
}
function meter(s){
  if (s.andamento_pct == null){
    return h('span', {class:'dim cellv'}, '—', h('span', {class:'src'}, s.arquivada ? 'arquivada' : (s.andamento_fonte || 'sem medida')));
  }
  const p = Math.max(0, Math.min(100, s.andamento_pct));
  const approx = s.andamento_fonte === '_INDEX';
  const src = s.andamento_fonte === '_INDEX' ? '_INDEX' : s.andamento_fonte === 'critérios' ? 'critérios' : '_INDEX: não iniciada';
  return h('div', null,
    h('div', {class:'meter', role:'img', 'aria-label': (approx ? 'cerca de ' : '') + p + '% (' + src + ')'},
      h('div', {class:'track'}, h('div', {class:'fill', style:'width:' + p + '%'})),
      h('span', {class:'pct'}, (approx ? '~' : '') + p + '%')),
    h('span', {class:'src'}, src));
}
let BURN_BASE = 'arquivo';  /* 'arquivo' = todas as caixas (fases/tarefas) · 'secoes' = só critérios de aceite/fases */
function critSeries(s, base){
  const b = (base || 'arquivo') === 'secoes';
  return s.historico.map(p => ({d:p.data, f: b ? p.crit_feitos : p.feitos, t: b ? p.crit_total : p.total}));
}
function sparkline(s){
  const pts = critSeries(s).filter(p => p.t > 0);
  if (!pts.length) return h('span', {class:'dim'}, '—');
  const W = 92, H = 24, pad = 3;
  const a = pd(s.criada_em && s.criada_em < pts[0].d ? s.criada_em : pts[0].d).getTime(), b = pd(HOJE).getTime();
  const X = d => pad + (b > a ? (pd(d).getTime() - a) / (b - a) : 1) * (W - 2*pad);
  const Y = v => H - pad - v * (H - 2*pad);
  let dstr = '';
  pts.forEach((p, i) => {
    const x = X(p.d), y = Y(p.f / p.t);
    if (i === 0) dstr += 'M' + x.toFixed(1) + ',' + y.toFixed(1);
    else dstr += 'H' + x.toFixed(1) + 'V' + y.toFixed(1);
  });
  const last = pts[pts.length - 1];
  dstr += 'H' + (W - pad);
  const first = pts[0];
  const svg = sv('svg', {width:W, height:H, class:'spark', role:'img',
    'aria-label': 'Caixas marcadas no arquivo: de ' + Math.round(100*first.f/first.t) + '% em ' + br(first.d) + ' a ' + Math.round(100*last.f/last.t) + '% hoje'});
  svg.appendChild(sv('line', {x1:pad, x2:W-pad, y1:H-pad+0.5, y2:H-pad+0.5, style:'stroke:var(--grid);stroke-width:1'}));
  svg.appendChild(sv('path', {d:dstr, style:'fill:none;stroke:var(--muted);stroke-width:1.5;stroke-linejoin:round;stroke-linecap:round'}));
  svg.appendChild(sv('circle', {cx:W-pad, cy:Y(last.f/last.t), r:3, style:'fill:var(--accent);stroke:var(--surface);stroke-width:1.5'}));
  const t = sv('title'); t.textContent = svg.getAttribute('aria-label'); svg.appendChild(t);
  return svg;
}

/* ── gaveta de detalhe da spec ── */
let drawerEls = null, drawerOpener = null, drawerSlug = null, drLiveEl = null;
function closeDrawer(silent){
  if (!drawerEls) return;
  hideTip();
  drawerEls.forEach(e => e.remove()); drawerEls = null; drawerSlug = null; drLiveEl = null;
  document.removeEventListener('keydown', drawerKey);
  document.documentElement.classList.remove('noscroll');
  if (!silent && drawerOpener){
    let o = drawerOpener;      // quem abriu foi redesenhado (legenda do universo): acha o equivalente pelo data-k
    if (!document.contains(o) && o.dataset && o.dataset.k) o = document.querySelector('[data-k="' + o.dataset.k + '"]');
    if (o && document.contains(o)) o.focus();
  }
}
/* Esc fecha; Tab e Shift+Tab ficam presos dentro da gaveta (aria-modal) */
function drawerKey(e){
  if (!drawerEls) return;
  if (e.key === 'Escape'){ closeDrawer(); return; }
  if (e.key !== 'Tab') return;
  const dr = drawerEls[1];
  const f = drFocusables(dr);
  if (!f.length){ e.preventDefault(); return; }
  const first = f[0], last = f[f.length - 1], cur = document.activeElement;
  if (e.shiftKey && (cur === first || !dr.contains(cur))){ e.preventDefault(); last.focus(); }
  else if (!e.shiftKey && (cur === last || !dr.contains(cur))){ e.preventDefault(); first.focus(); }
}
function drFocusables(dr){
  return [...dr.querySelectorAll('button, [href], input, select, textarea, [tabindex]:not([tabindex="-1"])')]
    .filter(x => !x.disabled && x.getClientRects().length);
}
/* identidade do elemento focado na gaveta, para devolver o foco a ELE depois de um redesenho */
function drFocusKey(){
  if (!drawerEls || !drawerEls[1].contains(document.activeElement)) return null;
  const el = document.activeElement, f = drFocusables(drawerEls[1]);
  return {i: f.indexOf(el), t: (el.textContent || '').trim(), href: el.getAttribute('href')};
}
function drFocusRestore(dr, k, fallback){
  const f = drFocusables(dr), txt = x => (x.textContent || '').trim();
  let el = k.href ? f.find(x => x.getAttribute('href') === k.href) : null;
  if (!el && k.i >= 0 && f[k.i] && txt(f[k.i]) === k.t) el = f[k.i];
  if (!el && k.t) el = f.find(x => txt(x) === k.t);
  (el || fallback).focus({preventScroll:true});
}
/* keep = {scroll, focus}: redesenho por dados novos (modo ao vivo) — mantém a rolagem e o foco no MESMO
   elemento (link de ADR, botão "Só critérios…"), e não rouba o foco se ele estava fora da gaveta */
function openSpec(slug, opener, keep){
  closeDrawer(!!keep);
  const s = SPEC.get(slug); if (!s) return;
  drawerOpener = opener || null; drawerSlug = slug;
  const scrim = h('div', {class:'scrim', onclick: closeDrawer});
  const dr = h('aside', {class:'drawer', role:'dialog', 'aria-modal':'true', 'aria-labelledby':'dr-title'});
  const closeBtn = h('button', {type:'button', class:'btn close', onclick: closeDrawer}, ico('x'), 'Fechar');
  /* o cabeçalho da página fica sob o scrim e atrás da gaveta: o indicador ao vivo vai junto no topo dela */
  drLiveEl = LIVE ? h('span', {class:'live', 'aria-live':'off'}) : null;
  dr.appendChild(h('div', {class:'drhead'}, drLiveEl, closeBtn));
  dr.appendChild(h('h2', {id:'dr-title'}, shortTitle(s.titulo)));
  dr.appendChild(h('div', {class:'slug'}, s.arquivo));
  const gid = specGid(s.slug);
  const acts = h('div', {class:'acts'}, obsLink(s.arquivo, 'a spec', true),
    G && G.byId.has(gid) ? h('button', {type:'button', class:'btn', onclick: () => { closeDrawer(true); show('grafo'); gSelect(gid, {center:true}); }}, 'Ver no grafo') : null);
  if (acts.childNodes.length) dr.appendChild(acts);
  if (s.renomeada_de && s.renomeada_de.length)
    dr.appendChild(h('div', {class:'slug'}, 'Renomeada — antes: ' + s.renomeada_de.join(', ') + ' (histórico e ligações somados)'));
  // arquivada: a linha "Status" do corpo é a de antes do arquivamento — rotular para não parecer o status atual
  dr.appendChild(h('div', {class:'stline'}, badge(s.status),
    s.status_texto ? h('span', {class:'stx'}, s.arquivada ? 'Status no corpo, antes do arquivamento: ' : null, cleanMd(s.status_texto)) : null));
  if (s.index) dr.appendChild(h('div', {class:'tagline'}, h('b', null, 'Tag no _INDEX: '), '[' + s.index.tag + ']'));
  const c = s.criterios, cb = s.checkboxes;
  const fonteSt = s.status_fonte === 'frontmatter' ? 'frontmatter' : s.status_fonte === 'corpo' ? 'linha "Status" do corpo' : s.status_fonte === '_INDEX' ? 'tag do _INDEX' : '—';
  const facts = [
    ['Andamento', s.andamento_pct == null ? '—' : ((s.andamento_fonte === '_INDEX' ? '~' : '') + s.andamento_pct + '% · ' + s.andamento_fonte)],
    ['Critérios', c.total ? c.feitos + ' de ' + c.total + (c.base === 'secoes' ? ' (seções de critérios/fases)' : ' (arquivo todo)') : '—'],
    ['Caixas no arquivo', cb.total ? cb.feitos + ' de ' + cb.total : 'nenhuma'],
    ['Status declarado em', fonteSt + (s.status_bruto ? ' · "' + cleanMd(s.status_bruto) + '"' : '')],
    ['Criada em', br(s.criada_em) + (s.criada_aproximada ? ' (aprox.)' : '') + ' · ' + (s.criada_fonte || '—')],
    ['Última mudança da spec', br(s.ultima_mudanca)],
    ['Última atividade', br(s.ultima_atividade) + (s.ultima_atividade_fonte ? ' · ' + (s.ultima_atividade_fonte === 'spec' ? 'na spec' : s.ultima_atividade_fonte) : '')],
    ['Dias parada', s.dias_parada == null ? '—' : s.dias_parada + (s.parada ? ' — acima de ' + D.regras.parada_dias :
      (!s.conta_parada && !s.arquivada ? ' (' + stm(s.status).l.toLowerCase() + ': não conta como parada)' : ''))]
  ];
  dr.appendChild(h('div', {class:'facts'}, facts.map(f => h('div', null, h('span', null, f[0]), f[1]))));
  if (c.base === 'secoes' && c.secoes && c.secoes.length)
    dr.appendChild(h('div', {class:'seq'}, 'Seções contadas como critérios: ' +
      c.secoes.map(x => '"' + cleanMd(x.titulo) + '" (' + x.feitos + '/' + x.total + ')').join(' · ')));
  if (s.arquivada){
    dr.appendChild(h('div', {class:'arch'},
      h('div', null, h('b', null, 'Arquivada em: '), br(s.arquivado_em)),
      s.motivo ? h('div', null, h('b', null, 'Motivo: '), cleanMd(s.motivo)) : h('div', {class:'dim'}, 'Sem motivo registrado no frontmatter.'),
      s.substituido_por ? h('div', null, h('b', null, 'Substituída por: '), cleanMd(s.substituido_por)) : null));
  }
  dr.appendChild(h('h3', null, 'Linha do tempo de status'));
  const laneHost = h('div', {class:'chart', id:'dr-lane'});
  dr.appendChild(laneHost);
  const seqTxt = laneSegs(s).segs.map(g => brc(g.a) + ' ' + stm(g.st).l.toLowerCase()).join(' → ');
  dr.appendChild(h('div', {class:'seq'}, seqTxt + (s.arquivada ? ' · arquivada em ' + br(s.arquivado_em) : ' · hoje')));
  dr.appendChild(h('h3', null, 'Andamento no tempo: caixas marcadas × total'));
  if (s.criterios.base === 'secoes'){
    dr.appendChild(seg('Contar', [{v:'arquivo', l:'Todas as caixas'}, {v:'secoes', l:'Só critérios de aceite/fases'}], BURN_BASE, v => {
      BURN_BASE = v; const bh = document.getElementById('dr-burn'); if (bh) burnup(bh, s);
    }));
  }
  const buHost = h('div', {class:'chart', id:'dr-burn'});
  dr.appendChild(buHost);
  dr.appendChild(h('h3', null, 'ADRs ligados (' + s.adrs.length + ')'));
  if (!s.adrs.length) dr.appendChild(h('p', {class:'empty'}, 'Nenhum ADR cita esta spec, e ela não cita ADRs.'));
  else {
    const ul = h('ul', {class:'mini'});
    for (const l of s.adrs){
      const a = ADR.get(l.id); if (!a) continue;
      const via = l.via === 'spec' ? 'citado pela spec' : l.via === 'adr' ? 'cita a spec' : 'cita a spec e é citado por ela';
      const amplo = l.via === 'adr' && a.ampla ? ' · cita ' + a.specs.length + ' specs: não conta como atividade' : '';
      ul.appendChild(h('li', null, h('span', {class:'d'}, br(a.data) + (a.data_aproximada ? ' ≈' : '')),
        h('span', null, a.titulo, ' ', obsLink('02_Memory/' + a.arquivo, a.id), h('span', {class:'via'}, via + ' · ' + a.status + (a.arquivado && a.status !== 'arquivado' ? ' (arquivado)' : '') + (a.modulo ? ' · ' + a.modulo : '') + amplo))));
    }
    dr.appendChild(ul);
  }
  dr.appendChild(h('h3', null, 'Notas ligadas (' + s.notas.length + ')'));
  if (!s.notas.length) dr.appendChild(h('p', {class:'empty'}, 'Nenhuma nota de sessão ou anotação cita esta spec.'));
  else {
    const ul = h('ul', {class:'mini'});
    for (const id of s.notas){
      const n = NOTA.get(id); if (!n) continue;
      ul.appendChild(h('li', null, h('span', {class:'d'}, br(n.data)),
        h('span', null, n.titulo, ' ', obsLink(notaRel(n), n.titulo), h('span', {class:'via'}, (n.tipo === 'sessao' ? 'nota de sessão' : 'anotação') + (n.consolidada ? ' · consolidada' : n.tipo === 'sessao' ? ' · no inbox' : '') +
          (n.pendencias ? ' · marcador de pendências, não conta como atividade' : '') +
          (n.ampla ? ' · cita ' + n.specs.length + ' specs: referência ampla, não conta como atividade' : '')))));
    }
    dr.appendChild(ul);
  }
  document.body.appendChild(scrim); document.body.appendChild(dr);
  drawerEls = [scrim, dr];
  document.documentElement.classList.add('noscroll');
  document.addEventListener('keydown', drawerKey);
  drawDrawerCharts();
  if (drLiveEl) liveRender();
  if (keep){ dr.scrollTop = keep.scroll || 0; if (keep.focus) drFocusRestore(dr, keep.focus, closeBtn); }
  else closeBtn.focus();
}
function drawDrawerCharts(){
  if (!drawerSlug) return;
  const s = SPEC.get(drawerSlug);
  const lane = document.getElementById('dr-lane'), bu = document.getElementById('dr-burn');
  if (lane) laneChart(lane, s);
  if (bu) burnup(bu, s);
}

/* ── segmentos de status de uma spec (criação → hoje ou arquivamento) ── */
function laneSegs(s){
  const fim = s.arquivada && s.arquivado_em ? s.arquivado_em : HOJE;
  const pts = s.historico.filter(p => p.data <= fim);
  let ini = s.criada_em || (pts[0] ? pts[0].data : HOJE);
  if (pts.length && pts[0].data < ini) ini = pts[0].data;
  const endX = ds(addD(pd(fim), 1));
  const segs = [];
  if (!pts.length){ segs.push({a:ini, b:endX, st:s.status}); return {ini, fim, endX, segs}; }
  if (pts[0].data > ini) segs.push({a:ini, b:pts[0].data, st:'sem-historico'});
  for (let i = 0; i < pts.length; i++){
    const a = pts[i].data, b = i + 1 < pts.length ? pts[i+1].data : endX, st = pts[i].status;
    const last = segs[segs.length - 1];
    if (last && last.st === st){ last.b = b; continue; }
    if (b > a) segs.push({a, b, st});
  }
  return {ini, fim, endX, segs};
}
function segTip(ev, s, g){
  const n = dias(g.a, g.b);
  showTip(ev, shortTitle(s.titulo), [
    {c: g.st === 'sem-historico' ? 'var(--axis)' : stm(g.st).c, v: stm(g.st).l, l: ''},
    {l: 'de ' + br(g.a) + ' a ' + br(ds(addD(pd(g.b), -1))) + ' · ' + n + (n === 1 ? ' dia' : ' dias')}
  ]);
}
function drawLaneSegs(svg, s, x, y, hgt, segs){
  segs.forEach((g, i) => {
    const x0 = x(pd(g.a)), x1 = x(pd(g.b));
    const w = Math.max(1.5, x1 - x0 - (i < segs.length - 1 ? 2 : 0));
    // "Sem status" = contorno tracejado: um cinza chapado some no fundo e se confunde com "Arquivada"
    const r = g.st === 'desconhecido'
      ? sv('rect', {x:x0 + 0.75, y:y + 0.75, width:Math.max(0.5, w - 1.5), height:hgt - 1.5, rx:2,
          style:'fill:var(--surface);stroke:var(--st-desconhecido);stroke-width:1.5;stroke-dasharray:3 2'})
      : sv('rect', {x:x0, y:y, width:w, height:hgt, rx:2, style:'fill:' + stm(g.st).c});
    r.addEventListener('pointerenter', ev => segTip(ev, s, g));
    r.addEventListener('pointerdown', ev => segTip(ev, s, g));
    r.addEventListener('pointermove', moveTip);
    r.addEventListener('pointerleave', leaveTip);
    svg.appendChild(r);
  });
}
function laneChart(host, s){
  hideTip();
  host.replaceChildren();
  if (!HAS_D3){ host.appendChild(noD3('A sequência de status logo abaixo continua válida.')); return; }
  const L = laneSegs(s);
  const W = Math.max(260, host.clientWidth), H = 50;
  const x = d3.scaleUtc().domain([pd(L.ini), pd(L.endX)]).range([1, W - 1]);
  const svg = sv('svg', {width:W, height:H, role:'img', 'aria-label':'Linha do tempo de status da spec'});
  drawLaneSegs(svg, s, x, 4, 22, L.segs);
  const nT = Math.max(2, Math.min(6, Math.floor(W / 90)));
  x.ticks(nT).forEach(t => {
    const xx = x(t);
    svg.appendChild(sv('line', {x1:xx, x2:xx, y1:28, y2:32, style:'stroke:var(--axis);stroke-width:1'}));
    const anchor = xx < 18 ? 'start' : xx > W - 18 ? 'end' : 'middle';
    const tx = sv('text', {x:xx, y:45, 'text-anchor':anchor, class:'tick'}); tx.textContent = brc(ds(t)); svg.appendChild(tx);
  });
  host.appendChild(svg);
  const lg = h('div', {class:'legend'});
  const seen = [...new Set(L.segs.map(g => g.st))];
  ST_LEGEND.filter(k => seen.includes(k)).forEach(k => lg.appendChild(h('span', null, swatch(k, 'sw'), stm(k).l)));
  host.appendChild(lg);
}

/* ── burn-up: critérios feitos × total ── */
function burnup(host, s){
  hideTip();
  host.replaceChildren();
  const base = s.criterios.base === 'secoes' ? BURN_BASE : 'arquivo';
  const pts = critSeries(s, base);
  if (!pts.some(p => p.t > 0)){ host.appendChild(h('p', {class:'empty'}, 'Esta spec não tem caixas de critério ("- [ ]" / "- [x]") em nenhuma versão do histórico.')); return; }
  if (!HAS_D3){ host.appendChild(noD3('Os números de critérios acima continuam válidos.')); return; }
  host.appendChild(h('div', {class:'legend'},
    h('span', null, h('span', {class:'lkey', style:'background:var(--accent)'}), 'Feitos'),
    h('span', null, h('span', {class:'lkey', style:'background:var(--muted)'}), 'Total'),
    h('span', {class:'dim'}, base === 'secoes' ? '(só as seções de critérios de aceite/fases)' : '(todas as caixas do arquivo: fases, tarefas e critérios)')));
  const W = Math.max(260, host.clientWidth), H = 200, m = {t:12, r:96, b:26, l:34};
  let ini = s.criada_em && s.criada_em < pts[0].d ? s.criada_em : pts[0].d;
  if (ini >= HOJE) ini = ds(addD(pd(HOJE), -1));
  const x = d3.scaleUtc().domain([pd(ini), pd(HOJE)]).range([m.l, W - m.r]);
  const maxT = d3.max(pts, p => p.t) || 1;
  const y = d3.scaleLinear().domain([0, maxT]).nice().range([H - m.b, m.t]);
  const svg = d3.select(host).append('svg').attr('width', W).attr('height', H).attr('role', 'img')
    .attr('aria-label', 'Critérios feitos e total ao longo do tempo');
  const yt = y.ticks(Math.min(5, y.domain()[1])).filter(Number.isInteger);
  svg.append('g').selectAll('line').data(yt).join('line').attr('x1', m.l).attr('x2', W - m.r)
    .attr('y1', t => Math.round(y(t)) + .5).attr('y2', t => Math.round(y(t)) + .5)
    .style('stroke', t => t === 0 ? 'var(--axis)' : 'var(--grid)').style('stroke-width', 1);
  svg.append('g').selectAll('text').data(yt).join('text').attr('class', 'tick').attr('x', m.l - 7).attr('y', t => y(t))
    .attr('dy', '0.32em').attr('text-anchor', 'end').text(t => nfmt(t));
  const xt = x.ticks(Math.max(2, Math.min(6, Math.floor((W - m.l - m.r) / 80))));
  svg.append('g').selectAll('text').data(xt).join('text').attr('class', 'tick').attr('x', t => x(t)).attr('y', H - m.b + 17)
    .attr('text-anchor', 'middle').text(t => brc(ds(t)));
  const P = pts.map(p => ({d:p.d, x:x(pd(p.d)), f:p.f, t:p.t}));
  const lastP = P[P.length - 1];
  const ext = P.concat([{d:HOJE, x:x(pd(HOJE)), f:lastP.f, t:lastP.t}]);
  const area = d3.area().x(p => p.x).y0(y(0)).y1(p => y(p.f)).curve(d3.curveStepAfter);
  const line = k => d3.line().x(p => p.x).y(p => y(p[k])).curve(d3.curveStepAfter);
  svg.append('path').attr('d', area(ext)).style('fill', 'var(--accent)').style('opacity', 0.10);
  svg.append('path').attr('d', line('t')(ext)).style('fill', 'none').style('stroke', 'var(--muted)').style('stroke-width', 2).style('stroke-linejoin', 'round');
  svg.append('path').attr('d', line('f')(ext)).style('fill', 'none').style('stroke', 'var(--accent)').style('stroke-width', 2).style('stroke-linejoin', 'round');
  const xe = x(pd(HOJE));
  [['t', 'var(--muted)'], ['f', 'var(--accent)']].forEach(([k, c]) => svg.append('circle').attr('cx', xe).attr('cy', y(lastP[k])).attr('r', 4)
    .style('fill', c).style('stroke', 'var(--surface)').style('stroke-width', 2));
  let yT = y(lastP.t), yF = y(lastP.f);
  const lbl = (yy, name, v) => { const t = svg.append('text').attr('class', 'endlabel').attr('x', xe + 9).attr('y', yy).attr('dy', '0.32em');
    t.append('tspan').attr('class', 'v').text(nfmt(v)); t.append('tspan').text(' ' + name); };
  if (lastP.f === lastP.t) lbl(yT, 'de ' + nfmt(lastP.t), lastP.f);
  else {
    if (yF - yT < 14){ const mid = (yF + yT) / 2; yT = mid - 7; yF = mid + 7; }
    lbl(yT, 'total', lastP.t); lbl(yF, 'feitos', lastP.f);
  }
  const cross = svg.append('line').attr('y1', m.t).attr('y2', H - m.b).style('stroke', 'var(--axis)').style('stroke-width', 1).style('opacity', 0);
  const crossOff = () => cross.style('opacity', 0);
  svg.append('rect').attr('x', m.l).attr('y', m.t).attr('width', W - m.l - m.r).attr('height', H - m.t - m.b).style('fill', 'transparent')
    .on('pointerdown pointermove', ev => {
      const [px] = d3.pointer(ev);
      let best = P[0]; for (const p of P) if (Math.abs(p.x - px) < Math.abs(best.x - px)) best = p;
      cross.attr('x1', best.x).attr('x2', best.x).style('opacity', 1);
      showTip(ev, br(best.d) + (best.d === HOJE ? ' (hoje)' : ''), [
        {c:'var(--accent)', v:best.f, l:'feitos'}, {c:'var(--muted)', v:best.t, l:'total'},
        {l: best.t ? Math.round(100 * best.f / best.t) + '% concluído' : ''}], null, crossOff);
    })
    .on('pointerleave', leaveTip);
}

/* ════════════════ aba 2 — linha do tempo ════════════════ */
const L = {q:'', st:'', arq:false};
let tlHost, tlCount, tlTable;
/* cores dos status das specs: editáveis na legenda da linha do tempo (bolinha = seletor), salvas neste navegador; valem no
   painel inteiro (todas as telas pintam por var(--st-*)) */
const STC_KEY = 'vault-panel:cores-status';
const ST_EDIT = ['rascunho', 'aprovada', 'em-desenvolvimento', 'implementada', 'estudo', 'guia', 'arquivada'];
const ST_VAR = k => (/var\((--[\w-]+)\)/.exec(stm(k).c) || [])[1];
const ST_PADRAO = {};
let STC = (() => { try { const o = JSON.parse(localStorage.getItem(STC_KEY) || '{}'); return o && typeof o === 'object' ? o : {}; } catch (e) { return {}; } })();
(function stcInit(){
  const cs = getComputedStyle(document.documentElement);
  ST_EDIT.forEach(k => { ST_PADRAO[k] = cs.getPropertyValue(ST_VAR(k)).trim().toLowerCase(); });
  ST_EDIT.forEach(k => {
    if (/^#[0-9a-f]{6}$/i.test(STC[k] || '')) document.documentElement.style.setProperty(ST_VAR(k), STC[k]);
    else delete STC[k];
  });
})();
function stcSave(){ try { localStorage.setItem(STC_KEY, JSON.stringify(STC)); } catch (e) {} }
function stcSet(k, c){
  if (c.toLowerCase() === ST_PADRAO[k]){ delete STC[k]; document.documentElement.style.removeProperty(ST_VAR(k)); }
  else { STC[k] = c; document.documentElement.style.setProperty(ST_VAR(k), c); }
  stcSave();
}
function stLegend(lg){
  lg.replaceChildren();
  ST_LEGEND.forEach(k => {
    if (ST_EDIT.indexOf(k) < 0){ lg.appendChild(h('span', null, swatch(k, 'sw'), stm(k).l)); return; }
    lg.appendChild(h('label', {class:'lgst', title:'Trocar a cor de ' + stm(k).l},
      h('input', {type:'color', class:'lgcor', value: STC[k] || ST_PADRAO[k] || '#888888', 'aria-label':'Cor de ' + stm(k).l,
        oninput: e => stcSet(k, e.target.value), onchange: () => stLegend(lg)}), stm(k).l));
  });
  if (Object.keys(STC).length) lg.appendChild(h('button', {type:'button', class:'btn', title:'Volta as cores de fábrica dos status',
    onclick: () => { ST_EDIT.forEach(k => { delete STC[k]; document.documentElement.style.removeProperty(ST_VAR(k)); }); stcSave(); stLegend(lg); }},
    ico('rotate-ccw'), 'Cores padrão'));
}
function renderLinha(){
  const host = document.getElementById('p-linha');
  if (!host.dataset.ok){
    host.dataset.ok = '1';
    const filt = h('div', {class:'filters'});
    filt.appendChild(searchEl('Buscar spec…', L.q, v => { L.q = v; drawTimeline(); }));
    const opts = [{v:'', l:'Todos os status atuais'}].concat(GROUPS.map(g => ({v:g.k, l:g.l})));
    filt.appendChild(selectEl('Filtrar por status atual', opts, L.st, v => { L.st = v; if (v === 'arquivada'){ L.arq = true; arq.checked = true; } drawTimeline(); }));
    const arq = h('input', {type:'checkbox', onchange: e => { L.arq = e.target.checked; drawTimeline(); }});
    filt.appendChild(h('label', {class:'chk'}, arq, 'Incluir arquivadas'));
    tlCount = h('span', {class:'count', 'aria-live':'polite'});
    filt.appendChild(tlCount);
    host.appendChild(filt);
    const card = h('div', {class:'card'});
    const tbtn = h('button', {type:'button', class:'btn', 'aria-expanded':'false'}, 'Ver como tabela');
    tlTable = h('div', {hidden:true});
    tbtn.addEventListener('click', () => { const open = tlTable.hidden; tlTable.hidden = !open; tbtn.setAttribute('aria-expanded', String(open)); tbtn.textContent = open ? 'Ocultar tabela' : 'Ver como tabela'; });
    card.appendChild(h('div', {class:'chart-head'}, h('div', null, h('h2', null, 'Status de cada spec ao longo do tempo'),
      h('div', {class:'sub'}, 'Uma raia por spec, da criação até hoje (ou até o arquivamento). Cada trecho tem a cor do status vigente. Ordem: data de criação.')), tbtn));
    const lg = h('div', {class:'legend'});
    stLegend(lg);
    card.appendChild(lg);
    tlHost = h('div', {class:'tl'});
    card.appendChild(tlHost);
    const hi = D.resumo.historico_inicio;
    card.appendChild(h('p', {class:'caption'}, 'O histórico vem dos commits da cópia do vault no repositório' + (hi ? ' (desde ' + br(hi) + ')' : '') +
      '; trecho hachurado = a spec já existia, mas antes da 1ª versão no histórico. Criação de quem já existia no início do histórico: a linha "Data:" da própria spec; sem ela, o dia 01 do mês no nome ("≈").'));
    card.appendChild(tlTable);
    host.appendChild(card);
  }
  drawTimeline();
}
function segSeq(L, s){
  return L.segs.map(g => brc(g.a) + ' ' + stm(g.st).l.toLowerCase()).join(' → ') + (s.arquivada ? ' · arquivada em ' + br(s.arquivado_em) : ' · hoje');
}
function drawTimeline(){
  if (!tlHost) return;
  hideTip();
  tlHost.replaceChildren();
  const list = D.specs.filter(s => {
    if (!L.arq && s.arquivada) return false;
    if (L.st){ const g = GROUPS.find(g => g.k === L.st); if (g && !g.st.includes(s.status)) return false; }
    if (L.q && !fold(s.slug + ' ' + s.titulo).includes(fold(L.q))) return false;
    return true;
  }).map(s => ({s, L: laneSegs(s)}))
    .sort((a, b) => a.L.ini.localeCompare(b.L.ini) || a.s.slug.localeCompare(b.s.slug));
  tlCount.textContent = plural(list.length, 'spec', 'specs');
  // tabela (mesmo recorte): sequência de status por spec
  const tt = h('table', {class:'rows'});
  tt.appendChild(h('thead', null, h('tr', null, ['Spec', 'Criada em', 'Status ao longo do tempo'].map(c => h('th', {scope:'col'}, c)))));
  const ttb = h('tbody');
  list.forEach(r => ttb.appendChild(h('tr', null, h('td', {class:'t'}, shortTitle(r.s.titulo)),
    h('td', {class:'num', style:'text-align:left'}, br(r.s.criada_em) + (r.s.criada_aproximada ? ' ≈' : '')), h('td', {class:'t'}, segSeq(r.L, r.s)))));
  tt.appendChild(ttb);
  tlTable.replaceChildren(h('div', {class:'scroll-x'}, tt));
  if (!list.length){ tlHost.appendChild(h('p', {class:'empty'}, 'Nenhuma spec com esses filtros.')); return; }
  if (!HAS_D3){ tlHost.appendChild(noD3('A tabela ("Ver como tabela") continua válida.')); return; }
  // no celular o título vai acima da raia (raia com a largura toda) em vez de uma coluna estreita
  const W = tlHost.clientWidth, narrow = W < 640;
  const lblW = narrow ? 0 : 260, laneW = narrow ? Math.max(120, W) : Math.max(120, W - lblW - 6);
  const minIni = list.reduce((m, r) => r.L.ini < m ? r.L.ini : m, HOJE);
  const x = d3.scaleUtc().domain([pd(minIni), addD(pd(HOJE), 1)]).range([1, laneW - 1]);
  const grid = narrow ? laneW + 'px' : lblW + 'px ' + laneW + 'px';
  const span = dias(minIni, HOJE);
  const ticks = span > 75 ? x.ticks(d3.utcMonth.every(1)) : x.ticks(d3.utcMonday.every(span > 30 ? 2 : 1));
  const tfmt = (t, i) => span > 75 ? MESES[t.getUTCMonth()] + ((t.getUTCMonth() === 0 || i === 0) && laneW > 420 ? ' ' + t.getUTCFullYear() : '') : brc(ds(t));
  const hdr = document.querySelector('header.top');
  const stickyTop = hdr && getComputedStyle(hdr).position === 'sticky' ? hdr.offsetHeight : 0;
  const ax = h('div', {class:'tl-axis', style:'grid-template-columns:' + grid + ';top:' + stickyTop + 'px'});
  if (!narrow) ax.appendChild(h('div', {class:'flabel', style:'padding:0 0 var(--spacing-xs)'}, 'Spec'));
  const asvg = sv('svg', {width:laneW, height:26, 'aria-hidden':'true'});
  const xHoje = x(pd(HOJE));
  let lastX = -1e9;
  ticks.forEach((t, i) => {
    const xx = x(t), lbl = tfmt(t, i), wlab = lbl.length * 6.2;
    const left = xx < wlab / 2 ? xx : xx - wlab / 2;
    if (left < lastX + 8 || xx + wlab / 2 > xHoje - 30) return;
    const tx = sv('text', {x:xx, y:16, 'text-anchor': xx < wlab / 2 ? 'start' : 'middle', class:'tick'}); tx.textContent = lbl; asvg.appendChild(tx);
    lastX = left + wlab;
  });
  const th = sv('text', {x:xHoje, y:16, 'text-anchor':'end', class:'tick'}); th.textContent = 'hoje'; asvg.appendChild(th);
  ax.appendChild(asvg);
  tlHost.appendChild(ax);
  const rows = h('div', {class:'tl-rows'});
  if (!narrow){
    ticks.forEach(t => rows.appendChild(h('div', {class:'tl-over grid', style:'left:' + (lblW + x(t)) + 'px'})));
    rows.appendChild(h('div', {class:'tl-over today', style:'left:' + (lblW + x(pd(HOJE))) + 'px'}));
  }
  const rh = narrow ? 18 : 24, ry = narrow ? 3 : 6;
  for (const r of list){
    const s = r.s;
    const row = h('div', {class:'tl-row' + (narrow ? ' narrow' : ''), style: narrow ? null : 'grid-template-columns:' + grid});
    row.appendChild(h('div', {class:'lbl'}, h('button', {type:'button', class:'link', title: shortTitle(s.titulo) + ' · ' + s.slug,
      onclick: e => openSpec(s.slug, e.currentTarget)}, shortTitle(s.titulo))));
    const svg = sv('svg', {width:laneW, height:rh, role:'img', 'aria-label': shortTitle(s.titulo) + ': ' + r.L.segs.map(g => stm(g.st).l + ' desde ' + br(g.a)).join(', ')});
    if (narrow){  // grade e "hoje" dentro de cada raia (sem sobrepor o título)
      ticks.forEach(t => svg.appendChild(sv('line', {x1:x(t), x2:x(t), y1:0, y2:rh, style:'stroke:var(--grid);stroke-width:1'})));
      svg.appendChild(sv('line', {x1:xHoje, x2:xHoje, y1:0, y2:rh, style:'stroke:var(--ink-2);stroke-width:1'}));
    }
    drawLaneSegs(svg, s, x, ry, 12, r.L.segs);
    if (s.arquivada){
      const xe = x(pd(r.L.endX));
      svg.appendChild(sv('line', {x1:xe + 2, x2:xe + 2, y1:ry - 3, y2:ry + 15, style:'stroke:var(--st-arquivada);stroke-width:2;stroke-linecap:round'}));
    }
    row.appendChild(svg);
    rows.appendChild(row);
  }
  tlHost.appendChild(rows);
}

/* ════════════════ barras por dia/semana (ADRs e anotações) ════════════════ */
/* recorte do período; por semana ele recua até a segunda-feira, para a 1ª barra ser uma semana inteira */
function rangeOf(items, per, grao){
  const dated = items.filter(i => i.data && i.data <= HOJE);
  let ini = per === 'tudo' ? dated.reduce((m, i) => i.data < m ? i.data : m, HOJE) : ds(addD(pd(HOJE), -(+per - 1)));
  if (grao === 'semana') ini = segunda(ini);
  return {ini, inRange: dated.filter(i => i.data >= ini)};
}
function buildBuckets(R, grao, keyOf){
  const keys = [];
  for (let d = pd(R.ini); d <= pd(HOJE); d = addD(d, grao === 'dia' ? 1 : 7)) keys.push(ds(d));
  const map = new Map(keys.map(k => [k, {key:k, values:{}, total:0, emCurso:false}]));
  for (const it of R.inRange){
    const b = map.get(grao === 'dia' ? it.data : segunda(it.data)); if (!b) continue;
    const k = keyOf(it); b.values[k] = (b.values[k] || 0) + 1; b.total++;
  }
  const buckets = [...map.values()];
  const last = buckets[buckets.length - 1];
  if (last) last.emCurso = grao === 'dia' ? last.key === HOJE : ds(addD(pd(last.key), 6)) > HOJE;
  return {buckets, inRange: R.inRange, ini: R.ini};
}
function bucketTitle(b, grao){
  if (grao === 'dia') return br(b.key) + (b.emCurso ? ' (hoje, em curso)' : '');
  return 'Semana de ' + brc(b.key) + ' a ' + br(ds(addD(pd(b.key), 6))) + (b.emCurso ? ' (em curso)' : '');
}
function barPath(x, y, w, hh, r){
  if (r <= 0) return 'M' + x + ',' + y + 'h' + w + 'v' + hh + 'h' + (-w) + 'Z';
  return 'M' + x + ',' + (y + hh) + 'V' + (y + r) + 'Q' + x + ',' + y + ' ' + (x + r) + ',' + y + 'H' + (x + w - r) +
    'Q' + (x + w) + ',' + y + ' ' + (x + w) + ',' + (y + r) + 'V' + (y + hh) + 'Z';
}
function stackedChart(host, buckets, series, grao, aria){
  hideTip();
  host.replaceChildren();
  if (!HAS_D3){ host.appendChild(noD3()); return; }
  const W = Math.max(280, host.clientWidth), H = 250, m = {t:22, r:8, b:28, l:36};
  const x = d3.scaleBand().domain(buckets.map(b => b.key)).range([m.l, W - m.r]).paddingInner(buckets.length > 60 ? 0.2 : 0.3).paddingOuter(0.1);
  const bw = Math.max(1, Math.min(24, x.bandwidth())), off = (x.bandwidth() - bw) / 2;
  const maxT = d3.max(buckets, b => b.total) || 0;
  const y = d3.scaleLinear().domain([0, Math.max(1, maxT)]).nice().range([H - m.b, m.t]);
  const svg = d3.select(host).append('svg').attr('width', W).attr('height', H).attr('role', 'img').attr('aria-label', aria);
  const yt = y.ticks(Math.min(5, y.domain()[1])).filter(Number.isInteger);
  svg.append('g').selectAll('line').data(yt).join('line').attr('x1', m.l).attr('x2', W - m.r)
    .attr('y1', t => Math.round(y(t)) + .5).attr('y2', t => Math.round(y(t)) + .5)
    .style('stroke', t => t === 0 ? 'var(--axis)' : 'var(--grid)').style('stroke-width', 1);
  svg.append('g').selectAll('text').data(yt).join('text').attr('class', 'tick').attr('x', m.l - 7).attr('y', t => y(t))
    .attr('dy', '0.32em').attr('text-anchor', 'end').text(t => nfmt(t));
  const hov = svg.append('rect').attr('y', m.t - 8).attr('height', H - m.b - m.t + 8).attr('width', x.step()).attr('rx', 3)
    .style('fill', 'var(--hover)').style('opacity', 0);
  const hovOff = () => hov.style('opacity', 0);
  const g = svg.append('g');
  for (const b of buckets){
    const segs = series.filter(s => (b.values[s.k] || 0) > 0);
    let cum = 0;
    segs.forEach((s, i) => {
      const v = b.values[s.k], yb = y(cum), yt2 = y(cum + v); cum += v;
      let top = yt2, bot = yb - (i > 0 ? 2 : 0);
      if (bot - top < 1) bot = top + 1;
      const isTop = i === segs.length - 1;
      g.append('path').attr('d', barPath(x(b.key) + off, top, bw, bot - top, isTop ? Math.min(4, bw / 2, bot - top) : 0)).style('fill', s.c);
    });
  }
  const every = Math.max(1, Math.ceil(44 / x.step()));
  svg.append('g').selectAll('text').data(buckets.filter((b, i) => i % every === 0)).join('text').attr('class', 'tick')
    .attr('x', b => x(b.key) + x.bandwidth() / 2).attr('y', H - m.b + 17).attr('text-anchor', 'middle').text(b => brc(b.key));
  if (maxT > 0){
    const mb = buckets.reduce((a, b) => b.total > a.total ? b : a);
    svg.append('text').attr('class', 'vlabel').attr('x', x(mb.key) + x.bandwidth() / 2).attr('y', y(mb.total) - 6)
      .attr('text-anchor', 'middle').text(nfmt(mb.total));
  }
  const lead = (x.step() - x.bandwidth()) / 2;
  svg.append('g').selectAll('rect').data(buckets).join('rect')
    .attr('x', b => x(b.key) - lead).attr('y', m.t - 8).attr('width', x.step()).attr('height', H - m.b - m.t + 8).style('fill', 'transparent')
    .on('pointerenter pointerdown pointermove', (ev, b) => {
      hov.attr('x', x(b.key) - lead).style('opacity', 1);
      const rows = series.filter(s => b.values[s.k]).map(s => ({c:s.c, v:b.values[s.k], l:s.l})).reverse();
      showTip(ev, bucketTitle(b, grao), rows.length ? rows : [{l:'nenhum'}], rows.length > 1 ? b.total : null, hovOff);
    })
    .on('pointerleave', leaveTip);
}
/* mapa de calor por dia (semanas em colunas, segunda a domingo nas linhas): intensidade = quantos ADRs no dia, rampa de um
   azul em raiz quadrada (o dia de pico não apaga os outros); a dica mostra a divisão pela cor escolhida (status/módulo) */
function heatChart(host, items, series, keyOf, ini){
  hideTip();
  host.replaceChildren();
  const byDay = new Map();
  items.forEach(a => { let c = byDay.get(a.data); if (!c){ c = {t:0, v:{}}; byDay.set(a.data, c); } c.t++; const k = keyOf(a); c.v[k] = (c.v[k] || 0) + 1; });
  let max = 1; byDay.forEach(c => { if (c.t > max) max = c.t; });
  const DAY = 86400000, d0 = pd(segunda(ini)), d1 = pd(HOJE), nW = Math.floor((d1 - d0) / (7 * DAY)) + 1;
  /* célula estica na largura do cartão (poucas semanas = blocos largos); a altura fica entre 12 e 28 px */
  const W = Math.max(280, host.clientWidth), m = {t:18, l:32, r:8}, gap = 3;
  const cw = Math.max(4, (W - m.l - m.r) / nW - gap), cs = Math.max(12, Math.min(28, cw)), gridH = 7 * (cs + gap), H = m.t + gridH + 34;
  const svg = sv('svg', {width:W, height:H, role:'img', 'aria-label':'ADRs por dia: mapa de calor com ' + nW + ' semanas; "Ver como tabela" traz os números'});
  const bin = v => Math.min(5, 1 + Math.floor(Math.sqrt(v / max) * 4.999));
  const txt = (x, y, t, anchor) => { const e = sv('text', {class:'tick', x:x, y:y, dy:'0.32em', 'text-anchor':anchor || 'start'}); e.textContent = t; svg.appendChild(e); };
  ['seg', '', 'qua', '', 'sex', '', ''].forEach((l, r) => { if (l) txt(m.l - 6, m.t + r * (cs + gap) + cs / 2, l, 'end'); });
  let mes = -1;
  for (let d = d0; d <= d1; d = new Date(d.getTime() + DAY)){
    const key = ds(d), col = Math.floor((d - d0) / (7 * DAY)), row = (d.getUTCDay() + 6) % 7;
    const x = m.l + col * (cw + gap), y = m.t + row * (cs + gap);
    if (row === 0 && d.getUTCMonth() !== mes){ mes = d.getUTCMonth(); txt(x, m.t - 9, MESES[mes]); }
    if (key < ini) continue;
    const c = byDay.get(key), v = c ? c.t : 0;
    const r = sv('rect', {x:x, y:y, width:cw, height:cs, rx:2, style:'fill:' + (v ? 'var(--heat-' + bin(v) + ')' : 'var(--surface-2)')});
    r.addEventListener('pointerenter', ev => {
      const rows = c ? series.filter(se => c.v[se.k]).map(se => ({c:se.c, v:c.v[se.k], l:se.l})).reverse() : [];
      showTip(ev, br(key) + (key === HOJE ? ' (hoje)' : ''), rows.length ? rows : [{l:'nenhum ADR'}], rows.length > 1 ? v : null);
    });
    r.addEventListener('pointermove', moveTip);
    r.addEventListener('pointerleave', leaveTip);
    svg.appendChild(r);
  }
  const ly = m.t + gridH + 12;
  let lx = m.l;
  txt(lx, ly + 5, 'menos'); lx += 40;
  for (let i = 0; i <= 5; i++){ svg.appendChild(sv('rect', {x:lx, y:ly, width:10, height:10, rx:2, style:'fill:' + (i ? 'var(--heat-' + i + ')' : 'var(--surface-2)')})); lx += 13; }
  txt(lx + 4, ly + 5, 'mais (pico: ' + plural(max, 'ADR', 'ADRs') + ' num dia)');
  host.appendChild(svg);
}
/* linhas por série (status ou módulo) sobre os mesmos períodos das barras; "Acumulado" soma desde o início do período.
   Dica com mira vertical: os valores daquele período, do maior para o menor */
function lineChart(host, buckets, series, grao, acum){
  hideTip();
  host.replaceChildren();
  if (!HAS_D3){ host.appendChild(noD3()); return; }
  const used = series.filter(se => buckets.some(b => b.values[se.k]));
  const val = {};
  used.forEach(se => { let c = 0; val[se.k] = buckets.map(b => { const v = b.values[se.k] || 0; c += v; return acum ? c : v; }); });
  const W = Math.max(280, host.clientWidth), H = 260, m = {t:16, r:14, b:28, l:40};
  const x = d3.scalePoint().domain(buckets.map(b => b.key)).range([m.l, W - m.r]).padding(0.3);
  const maxV = d3.max(used, se => d3.max(val[se.k])) || 1;
  const y = d3.scaleLinear().domain([0, maxV]).nice().range([H - m.b, m.t]);
  const svg = d3.select(host).append('svg').attr('width', W).attr('height', H).attr('role', 'img')
    .attr('aria-label', 'ADRs por ' + grao + (acum ? ', acumulado' : '') + ' em linhas; "Ver como tabela" traz os números');
  const yt = y.ticks(5).filter(Number.isInteger);
  svg.append('g').selectAll('line').data(yt).join('line').attr('x1', m.l).attr('x2', W - m.r)
    .attr('y1', t => Math.round(y(t)) + .5).attr('y2', t => Math.round(y(t)) + .5)
    .style('stroke', t => t === 0 ? 'var(--axis)' : 'var(--grid)').style('stroke-width', 1);
  svg.append('g').selectAll('text').data(yt).join('text').attr('class', 'tick').attr('x', m.l - 7).attr('y', t => y(t))
    .attr('dy', '0.32em').attr('text-anchor', 'end').text(t => nfmt(t));
  const step = buckets.length > 1 ? x(buckets[1].key) - x(buckets[0].key) : (W - m.l - m.r);
  const every = Math.max(1, Math.ceil(44 / Math.max(1, step)));
  svg.append('g').selectAll('text').data(buckets.filter((b, i) => i % every === 0)).join('text').attr('class', 'tick')
    .attr('x', b => x(b.key)).attr('y', H - m.b + 17).attr('text-anchor', 'middle').text(b => brc(b.key));
  const line = d3.line().x((v, i) => x(buckets[i].key)).y(v => y(v)).curve(d3.curveMonotoneX);
  used.forEach(se => svg.append('path').attr('d', line(val[se.k])).style('fill', 'none').style('stroke', se.c)
    .style('stroke-width', 2).style('stroke-linejoin', 'round').style('stroke-linecap', 'round'));
  const cross = svg.append('line').attr('y1', m.t).attr('y2', H - m.b).style('stroke', 'var(--axis)').style('stroke-width', 1).style('opacity', 0);
  const dots = svg.append('g');
  const off = () => { cross.style('opacity', 0); dots.selectAll('circle').remove(); };
  svg.append('rect').attr('x', m.l - step / 2).attr('y', m.t).attr('width', W - m.l - m.r + step).attr('height', H - m.b - m.t)
    .style('fill', 'transparent')
    .on('pointerenter pointermove pointerdown', ev => {
      let i = Math.round((d3.pointer(ev)[0] - x(buckets[0].key)) / step);
      i = Math.max(0, Math.min(buckets.length - 1, i));
      const b = buckets[i], cx = x(b.key);
      cross.attr('x1', cx).attr('x2', cx).style('opacity', 1);
      dots.selectAll('circle').data(used).join('circle').attr('cx', cx).attr('cy', se => y(val[se.k][i])).attr('r', 4)
        .style('fill', se => se.c).style('stroke', 'var(--surface)').style('stroke-width', 2);
      const rows = used.map(se => ({c:se.c, v:val[se.k][i], l:se.l})).filter(r => r.v).sort((a, c) => c.v - a.v);
      showTip(ev, bucketTitle(b, grao) + (acum ? ' — acumulado' : ''), rows.length ? rows : [{l:'nenhum'}], null, off);
    })
    .on('pointerleave', leaveTip);
}
function legendFor(series, totals){
  const lg = h('div', {class:'legend'});
  series.forEach(s => { if (totals[s.k]) lg.appendChild(h('span', null, h('span', {class:'sw', style:'background:' + s.c}), s.l, ' ', h('b', null, nfmt(totals[s.k])))); });
  return lg;
}
function dataTable(buckets, series, grao){
  const used = series.filter(s => buckets.some(b => b.values[s.k]));
  const t = h('table', {class:'data'});
  t.appendChild(h('thead', null, h('tr', null, h('th', null, grao === 'dia' ? 'Dia' : 'Semana (segunda a domingo)'), used.map(s => h('th', {class:'num'}, s.l)), h('th', {class:'num'}, 'Total'))));
  const tb = h('tbody');
  buckets.filter(b => b.total).slice().reverse().forEach(b => tb.appendChild(h('tr', null, h('td', null, bucketTitle(b, grao)),
    used.map(s => h('td', {class:'num'}, nfmt(b.values[s.k] || 0))), h('td', {class:'num'}, nfmt(b.total)))));
  t.appendChild(tb);
  return h('div', {class:'scroll-x'}, t);
}
function chartCard(parent){
  const card = h('div', {class:'card'});
  const head = h('div', {class:'chart-head'});
  const titleBox = h('div');
  const tbtn = h('button', {type:'button', class:'btn', 'aria-expanded':'false'}, 'Ver como tabela');
  head.appendChild(titleBox); head.appendChild(tbtn);
  const lg = h('div'), ch = h('div', {class:'chart'}), cap = h('p', {class:'caption'}), tbl = h('div', {hidden:true});
  tbtn.addEventListener('click', () => { const open = tbl.hidden; tbl.hidden = !open; tbtn.setAttribute('aria-expanded', String(open)); tbtn.textContent = open ? 'Ocultar tabela' : 'Ver como tabela'; });
  card.appendChild(head); card.appendChild(lg); card.appendChild(ch); card.appendChild(cap); card.appendChild(tbl);
  parent.appendChild(card);
  return {titleBox, lg, ch, cap, tbl};
}

/* ════════════════ aba 3 — ADRs ════════════════ */
const A = {per:'90', grao:'dia', cor:'status', q:'', st:'', mod:'', todos:false,
           vis: (() => { try { const v = localStorage.getItem('vault-panel:adrs-vista'); return v === 'calor' || v === 'linha' ? v : 'barras'; } catch (e) { return 'barras'; } })(),
           acum: false};
const ADR_ST = [
  {k:'aceito', l:'Aceito', c:'var(--c1)'}, {k:'substituído', l:'Substituído', c:'var(--c2)'},
  {k:'revertido', l:'Revertido', c:'var(--c3)'}, {k:'proposto', l:'Proposto', c:'var(--c4)'},
  {k:'outro', l:'Outro / sem status', c:'var(--c5)'}, {k:'arquivado', l:'Arquivado', c:'var(--c-outros)'}
];
let MOD_COUNT, MOD_RANK, TOP_GERAL;
function indexData(){
  HOJE = D.hoje;
  ADR = new Map(D.adrs.map(a => [a.id, a]));
  NOTA = new Map(D.notas.map(x => [x.id, x]));
  SPEC = new Map(D.specs.map(s => [s.slug, s]));
  MOD_COUNT = new Map();
  D.adrs.forEach(a => { if (a.modulo && a.modulo !== '(sem módulo)') MOD_COUNT.set(a.modulo, (MOD_COUNT.get(a.modulo) || 0) + 1); });
  MOD_RANK = [...MOD_COUNT.entries()].sort((a, b) => b[1] - a[1]).map(e => e[0]);
  TOP_GERAL = MOD_RANK.slice(0, 8);
}
/* recarrega as opções de um <select> preservando a escolha (se a opção sumiu, ela fica, marcada) */
function fillSelect(sel, opts, cur){
  if (cur && !opts.some(o => o.v === cur)) opts = opts.concat([{v:cur, l:cur + ' (0)'}]);
  const sig = opts.map(o => o.v + '\u0001' + o.l).join('\u0002');
  if (sel.dataset.sig === sig){ sel.value = cur; return; }
  sel.dataset.sig = sig;
  sel.replaceChildren(...opts.map(o => { const op = h('option', {value:o.v}, o.l); if (o.v === cur) op.selected = true; return op; }));
}
function modOpts(){
  const mods = [...MOD_COUNT.entries()].sort((a, b) => b[1] - a[1]).map(e => ({v:e[0], l:e[0] + ' (' + e[1] + ')'}));
  return [{v:'', l:'Todos os módulos'}].concat(mods, [{v:'(sem módulo)', l:'(sem módulo)'}]);
}
/* top 8 DO RECORTE visível; a cor segue o módulo, não a posição: quem está no top 8 geral tem sempre
   o seu slot de cor, e os demais do recorte ocupam os slots livres */
function modSeries(inRange){
  const c = new Map();
  inRange.forEach(a => { if (a.modulo && a.modulo !== '(sem módulo)') c.set(a.modulo, (c.get(a.modulo) || 0) + 1); });
  const top = [...c.entries()].sort((a, b) => b[1] - a[1] || MOD_RANK.indexOf(a[0]) - MOD_RANK.indexOf(b[0])).slice(0, 8).map(e => e[0]);
  const slot = new Map();
  top.forEach(m => { const g = TOP_GERAL.indexOf(m); if (g >= 0) slot.set(m, g); });
  const used = new Set(slot.values()), free = [0,1,2,3,4,5,6,7].filter(i => !used.has(i));
  top.forEach(m => { if (!slot.has(m)) slot.set(m, free.shift()); });
  const series = top.slice().sort((a, b) => slot.get(a) - slot.get(b)).map(m => ({k:m, l:m, c:'var(--c' + (slot.get(m) + 1) + ')'}));
  series.push({k:'__outros', l:'Outros módulos', c:'var(--c-outros)'});
  const set = new Set(top);
  return {series, keyOf: a => set.has(a.modulo) ? a.modulo : '__outros'};
}
let adrUI = null;
function adrPassa(a){
  if (A.st && a.status !== A.st) return false;
  if (A.mod && a.modulo !== A.mod) return false;
  if (A.q){ const hay = fold((a.num != null ? 'adr-' + a.num + ' ' : '') + a.titulo + ' ' + a.modulo + ' ' + a.arquivo);
    if (!fold(A.q).split(/\s+/).every(w => hay.includes(w))) return false; }
  return true;
}
function renderAdrs(){
  const host = document.getElementById('p-adrs');
  if (!adrUI){
    host.appendChild(h('div', {class:'vbar'}, seg('Visualização', [{v:'barras', l:'Barras', i:'chart-column'},
      {v:'calor', l:'Calor por dia', i:'calendar-days'}, {v:'linha', l:'Linha', i:'chart-line'}], A.vis,
      v => { A.vis = v; try { localStorage.setItem('vault-panel:adrs-vista', v); } catch (e) {} drawAdrs(); })));
    const filt = h('div', {class:'filters'});
    filt.appendChild(seg('Período', [{v:'30', l:'30 d'}, {v:'90', l:'90 d'}, {v:'tudo', l:'Tudo'}], A.per, v => { A.per = v; drawAdrs(); }));
    filt.appendChild(seg('Agrupar por', [{v:'dia', l:'Dia'}, {v:'semana', l:'Semana'}], A.grao, v => { A.grao = v; drawAdrs(); }));
    filt.appendChild(seg('Cor por', [{v:'status', l:'Status'}, {v:'modulo', l:'Módulo'}], A.cor, v => { A.cor = v; drawAdrs(); }));
    filt.appendChild(searchEl('Buscar ADR (número, título, módulo)…', A.q, v => { A.q = v; drawAdrs(); }));
    filt.appendChild(selectEl('Status do ADR', [{v:'', l:'Todos os status'}].concat(ADR_ST.map(s => ({v:s.k, l:s.l}))), A.st, v => { A.st = v; drawAdrs(); }));
    const modSel = selectEl('Módulo', [], A.mod, v => { A.mod = v; drawAdrs(); });
    filt.appendChild(modSel);
    const acum = h('input', {type:'checkbox', onchange: e => { A.acum = e.target.checked; drawAdrs(); }});
    const acumL = h('label', {class:'chk', title:'Linha que soma os ADRs desde o início do período'}, acum, 'Acumulado');
    filt.appendChild(acumL);
    host.appendChild(filt);
    const cc = chartCard(host);
    const tcard = h('div', {class:'card'});
    const thead = h('div', {class:'chart-head'});
    const tcount = h('div');
    thead.appendChild(tcount);
    tcard.appendChild(thead);
    const tbody = h('div');
    tcard.appendChild(tbody);
    host.appendChild(tcard);
    adrUI = {cc, tcount, tbody, modSel, acumL};
  }
  drawAdrs();
}
function periodoTxt(per, grao, ini){
  if (per === 'tudo') return 'desde o primeiro registro';
  return 'nos últimos ' + per + ' dias' + (grao === 'semana' ? ', em semanas inteiras (desde ' + br(ini) + ')' : '');
}
function drawAdrs(){
  if (!adrUI) return;
  fillSelect(adrUI.modSel, modOpts(), A.mod);
  hideTip();   // o gráfico pode sair vazio (sem stackedChart) e o elemento sob o ponteiro some
  const items = D.adrs.filter(adrPassa);
  const R = rangeOf(items, A.per, A.grao);
  let series, keyOf;
  if (A.cor === 'status'){ series = ADR_ST; keyOf = a => a.status; }
  else { const ms = modSeries(R.inRange); series = ms.series; keyOf = ms.keyOf; }
  const B = buildBuckets(R, A.grao, keyOf);
  const {cc} = adrUI;
  adrUI.acumL.hidden = A.vis !== 'linha';
  cc.titleBox.replaceChildren(h('h2', null, A.vis === 'calor' ? 'ADRs por dia — mapa de calor' :
      'ADRs por ' + (A.grao === 'dia' ? 'dia' : 'semana') + ', por ' + (A.cor === 'status' ? 'status' : 'módulo') + (A.vis === 'linha' && A.acum ? ' (acumulado)' : '')),
    h('div', {class:'sub'}, plural(B.inRange.length, 'ADR ', 'ADRs ') + periodoTxt(A.per, A.grao, B.ini) + (A.grao === 'semana' ? ' · semana ISO (segunda a domingo), fuso de São Paulo' : '')));
  const totals = {}; B.inRange.forEach(a => { const k = keyOf(a); totals[k] = (totals[k] || 0) + 1; });
  cc.lg.replaceChildren(A.vis === 'calor' ? h('span') : legendFor(series, totals));   // calor: a escala vem no próprio gráfico
  if (!B.inRange.length) cc.ch.replaceChildren(h('p', {class:'empty'}, 'Nenhum ADR no período com esses filtros.'));
  else if (A.vis === 'calor') heatChart(cc.ch, B.inRange, series, keyOf, B.ini);
  else if (A.vis === 'linha') lineChart(cc.ch, B.buckets, series, A.grao, A.acum);
  else stackedChart(cc.ch, B.buckets, series, A.grao, 'ADRs por ' + A.grao);
  const aprox = B.inRange.filter(a => a.data_aproximada).length, semData = items.filter(a => !a.data).length;
  cc.cap.textContent = (A.cor === 'modulo' ? 'Módulo = primeiro módulo da linha "Módulos afetados", com sinônimos e submódulos juntados (sinônimos em local.modules.json). Cor para os 8 mais frequentes do período (o módulo mantém a cor ao trocar o período); o resto em "Outros módulos". ' : 'Substituído vale mesmo quando o ADR também está arquivado; "Arquivado" = arquivado sem substituição. ') +
    (aprox ? aprox + ' ADR(s) sem dia exato contam no dia 01 do mês. ' : '') + (semData ? semData + ' ADR(s) sem data ficam fora do gráfico (aparecem na tabela em "Tudo").' : '');
  cc.tbl.replaceChildren(dataTable(B.buckets, series, A.grao));
  // tabela de ADRs do mesmo recorte
  const rows = A.per === 'tudo' ? items : B.inRange;
  adrUI.tcount.replaceChildren(h('h2', null, 'ADRs do recorte'), h('div', {class:'sub'}, plural(rows.length, 'ADR', 'ADRs') + ' · mais recentes primeiro'));
  drawAdrTable(rows);
}
function drawAdrTable(rows){
  const host = adrUI.tbody; host.replaceChildren();
  if (!rows.length){ host.appendChild(h('p', {class:'empty'}, 'Nenhum ADR.')); return; }
  const LIM = 300;
  const sorted = rows.slice().sort((a, b) => (b.data || '').localeCompare(a.data || '') || (b.num || 0) - (a.num || 0));
  const t = h('table', {class:'rows'});
  t.appendChild(h('thead', null, h('tr', null, ['Data', 'Nº', 'Título', 'Status', 'Módulo', 'Specs'].map(c => h('th', {scope:'col'}, c)))));
  const tb = h('tbody');
  const put = list => list.forEach(a => {
    const st = ADR_ST.find(s => s.k === a.status) || ADR_ST[4];
    tb.appendChild(h('tr', null,
      h('td', {class:'num', style:'text-align:left'}, br(a.data) + (a.data_aproximada ? ' ≈' : '')),
      h('td', {class:'num', style:'text-align:left'}, a.num != null ? 'ADR-' + a.num : '—'),
      h('td', {class:'t', title:a.arquivo}, cleanMd(a.titulo).replace(/^ADR-0*\d+\s*[—–:-]+\s*/, ''), ' ', obsLink('02_Memory/' + a.arquivo, a.id)),
      h('td', null, h('span', {class:'badge'}, h('span', {class:'dot', style:'background:' + st.c}), st.l),
        a.arquivado && a.status !== 'arquivado' ? h('span', {class:'src'}, 'arquivado') : null),
      h('td', {class:'m'}, a.modulo, a.modulo_bruto && fold(a.modulo_bruto).replace(/[^a-z0-9]/g, '') !== fold(a.modulo).replace(/[^a-z0-9]/g, '') ? h('span', {class:'src'}, a.modulo_bruto) : null),
      h('td', null, specChips(a.specs))));
  });
  put(A.todos ? sorted : sorted.slice(0, LIM));
  t.appendChild(tb);
  host.appendChild(h('div', {class:'scroll-x'}, t));
  if (sorted.length > LIM && !A.todos){
    const more = h('button', {type:'button', class:'btn', style:'margin-top:var(--spacing-sm)', onclick: () => { A.todos = true; put(sorted.slice(LIM)); more.remove(); }}, 'Mostrar todos (' + nfmt(sorted.length) + ')');
    host.appendChild(more);
  }
}
function specChips(slugs){
  if (!slugs || !slugs.length) return h('span', {class:'dim'}, '—');
  return h('div', {class:'chips'}, slugs.map(sl => h('button', {type:'button', class:'chip', title:sl, onclick: e => openSpec(sl, e.currentTarget)}, sl.replace(/-\d{4}-\d{2}(-\d{2})?$/, ''))));
}

/* ════════════════ aba 4 — anotações ════════════════ */
const N = {per:'tudo', grao:'dia', q:'', tipo:''};
const NOTE_SERIES = [{k:'sessao', l:'Nota de sessão', c:'var(--c1)'}, {k:'anotacao', l:'Anotação', c:'var(--c2)'}];
let notaUI = null;
function renderNotas(){
  const host = document.getElementById('p-notas');
  if (!notaUI){
    const filt = h('div', {class:'filters'});
    filt.appendChild(seg('Período', [{v:'30', l:'30 d'}, {v:'90', l:'90 d'}, {v:'tudo', l:'Tudo'}], N.per, v => { N.per = v; drawNotas(); }));
    filt.appendChild(seg('Agrupar por', [{v:'dia', l:'Dia'}, {v:'semana', l:'Semana'}], N.grao, v => { N.grao = v; drawNotas(); }));
    filt.appendChild(searchEl('Buscar nota…', N.q, v => { N.q = v; drawNotas(); }));
    filt.appendChild(selectEl('Tipo', [{v:'', l:'Sessão e anotação'}, {v:'sessao', l:'Só notas de sessão'}, {v:'anotacao', l:'Só anotações'}], N.tipo, v => { N.tipo = v; drawNotas(); }));
    host.appendChild(filt);
    const cc = chartCard(host);
    const tcard = h('div', {class:'card'});
    const tcount = h('div', {class:'chart-head'});
    const tbody = h('div');
    tcard.appendChild(tcount); tcard.appendChild(tbody);
    host.appendChild(tcard);
    const pendCard = h('div', {class:'card', hidden:true});
    host.appendChild(pendCard);
    notaUI = {cc, tcount, tbody, pendCard};
  }
  drawNotas();
}
function drawPend(){
  const pc = notaUI.pendCard;
  const pend = D.notas.filter(n => n.pendencias).sort((a, b) => (b.data || '').localeCompare(a.data || ''));
  pc.hidden = !pend.length;
  pc.replaceChildren();
  if (!pend.length) return;
  pc.appendChild(h('h2', null, 'Marcadores de pendências (fora dos gráficos)'));
  pc.appendChild(h('p', {class:'caption', style:'margin-top:var(--spacing-2xs)'}, 'Arquivos *PENDENCIAS* do inbox: listas de trabalho em aberto, não notas de sessão.'));
  const ul = h('ul', {class:'mini'});
  pend.forEach(n => ul.appendChild(h('li', null, h('span', {class:'d'}, br(n.data)), h('span', null, n.titulo, ' ', obsLink(notaRel(n), n.titulo), h('span', {class:'via'}, n.consolidada ? 'já saiu do inbox' : 'no inbox')))));
  pc.appendChild(ul);
}
function drawNotas(){
  if (!notaUI) return;
  drawPend();
  hideTip();
  const items = D.notas.filter(n => !n.pendencias && (!N.tipo || n.tipo === N.tipo) &&
    (!N.q || fold(n.titulo + ' ' + n.arquivo + ' ' + (n.specs || []).join(' ')).includes(fold(N.q))));
  const B = buildBuckets(rangeOf(items, N.per, N.grao), N.grao, n => n.tipo);
  const {cc} = notaUI;
  cc.titleBox.replaceChildren(h('h2', null, 'Anotações por ' + (N.grao === 'dia' ? 'dia' : 'semana')),
    h('div', {class:'sub'}, plural(B.inRange.length, 'nota ', 'notas ') + periodoTxt(N.per, N.grao, B.ini) + ' · sessão = nota do inbox (viva ou já consolidada) · anotação = 04_Anotações'));
  const totals = {}; B.inRange.forEach(n => { totals[n.tipo] = (totals[n.tipo] || 0) + 1; });
  cc.lg.replaceChildren(legendFor(NOTE_SERIES, totals));
  if (!B.inRange.length) cc.ch.replaceChildren(h('p', {class:'empty'}, 'Nenhuma nota no período com esses filtros.'));
  else stackedChart(cc.ch, B.buckets, NOTE_SERIES, N.grao, 'Anotações por ' + N.grao);
  cc.cap.textContent = 'Data da nota de sessão = prefixo AAAA-MM-DD do nome; da anotação = 1ª aparição no git (ou data do arquivo).';
  cc.tbl.replaceChildren(dataTable(B.buckets, NOTE_SERIES, N.grao));
  const rows = (N.per === 'tudo' ? items : B.inRange).slice().sort((a, b) => (b.data || '').localeCompare(a.data || '') || a.id.localeCompare(b.id));
  notaUI.tcount.replaceChildren(h('div', null, h('h2', null, 'Notas do recorte'), h('div', {class:'sub'}, plural(rows.length, 'nota', 'notas') + ' · mais recentes primeiro')));
  const host = notaUI.tbody; host.replaceChildren();
  if (!rows.length){ host.appendChild(h('p', {class:'empty'}, 'Nenhuma nota.')); return; }
  const t = h('table', {class:'rows'});
  t.appendChild(h('thead', null, h('tr', null, ['Data', 'Título', 'Tipo', 'Situação', 'Specs'].map(c => h('th', {scope:'col'}, c)))));
  const tb = h('tbody');
  rows.forEach(n => {
    const s = NOTE_SERIES.find(x => x.k === n.tipo);
    tb.appendChild(h('tr', null,
      h('td', {class:'num', style:'text-align:left'}, br(n.data)),
      h('td', {class:'t', title:n.arquivo}, n.titulo, ' ', obsLink(notaRel(n), n.titulo)),
      h('td', null, h('span', {class:'badge'}, h('span', {class:'dot', style:'background:' + s.c}), s.l)),
      h('td', null, n.tipo === 'sessao' ? (n.consolidada ? 'consolidada' : 'no inbox') : '—'),
      h('td', null, specChips(n.specs))));
  });
  t.appendChild(tb);
  host.appendChild(h('div', {class:'scroll-x'}, t));
}

/* ════════════════ aba 5 — grafo do vault ════════════════ */
/* Cor = grupo de tipo de doc. Mapa de força = forma "dispersão": qualquer par de nós pode encostar, então só
   3 matizes categóricas (validadas todos-contra-todos, claro e escuro) + cinza "outros"; o tipo fino fica no
   filtro, na dica e no painel. Em construção = anel de status (aviso) com rótulo na legenda; arquivado =
   contorno vazio (forma, não só cor). */
/* a aba Grafo mostra o UNIVERSO (vault inteiro, todos os projetos); sem ele, o grafo do projeto principal */
function grafoDaTela(g){ return g && FOCO && g.universo ? g.universo : (g || null); }
function specGid(slug){ return (GR && GR.universo ? (D.projeto || '') + '/' : '') + '01_Specs/' + slug + '.md'; }
function nodeSpecSlug(n){
  let id = n.id;
  if (GR && GR.universo){ const pre = (D.projeto || '') + '/'; if (id.indexOf(pre) !== 0) return null; id = id.slice(pre.length); }
  return id.indexOf('01_Specs/') === 0 && id.split('/').length === 2 ? id.slice(9, -3) : null;
}
let GR = grafoDaTela(BOOT.grafo);
let GR_EST = BOOT.grafo_estado || (GR ? 'pronto' : 'ausente');
let GR_MSG = BOOT.grafo_msg || '';
function prefGet(key, def, min, max){ try { const v = parseInt(localStorage.getItem(key), 10); return isFinite(v) ? Math.max(min, Math.min(max, v)) : def; } catch (e) { return def; } }
function prefSet(key, v){ try { localStorage.setItem(key, String(v)); } catch (e) {} }
/* universo (página única): luminosidade 20–200 % e movimento 0–200 % (0 = parado) */
let LUZ = prefGet('vault-panel:luz', 100, 20, 200) / 100;
let MOV = prefGet('vault-panel:mov', 100, 0, 200) / 100;
/* física do mapa: padrão = o grafo do Obsidian do vault (graph.json: centro 0,13, distância 30, repulsão 20; força dos
   links 0,24). Escalas do Obsidian: repulsão 0–20 × REP_K = forceManyBody do d3; centro 0–1 × CEN_K = forceX/forceY.
   Centro contra repulsão = disco de densidade uniforme (o "jeito Obsidian"). Chaves novas: o padrão vale de novo */
const FIS_PADRAO = {cent: 0.13, lf: 0.24, ld: 30, rep: 20}, REP_K = 8, CEN_K = 3;   // CEN_K medido: 0,13 aqui ≈ o disco do Obsidian em 0,13
const FIS_K = {cent: 'vault-panel:fisica:centro', lf: 'vault-panel:fisica:link-forca', ld: 'vault-panel:fisica:link-dist',
               rep: 'vault-panel:fisica:repulsao'};
/* força de cada ligação = a regra do d3 (e do Obsidian): 1 ÷ ligações do nó com MENOS ligações, × o slider.
   Hub com centenas de folhas não engole o mapa; as folhas ficam penduradas em cacho em volta dele */
function linkStr(l){ return GF.lf / Math.max(1, Math.min(l.source.vd || 1, l.target.vd || 1)); }
function prefGetF(key, def, min, max){ try { const v = parseFloat(localStorage.getItem(key)); return isFinite(v) ? Math.max(min, Math.min(max, v)) : def; } catch (e) { return def; } }
/* orfaos = ADR que ninguém cita; anexos = imagens/PDFs (só no universo); lf/ld = força e distância das ligações */
const GF = {q:'', tipo:'', area:'', conj:'', viz:true, orfaos:prefGet('vault-panel:adrs-orfaos', 1, 0, 1) === 1, anexos:prefGet('vault-panel:anexos', 1, 0, 1) === 1,
            pr:true, rq:'', todosT:false, todosR:false, todosC:false, cent:prefGetF(FIS_K.cent, FIS_PADRAO.cent, 0, 1),
            lf:prefGetF(FIS_K.lf, FIS_PADRAO.lf, 0, 1), ld:prefGet(FIS_K.ld, FIS_PADRAO.ld, 30, 500), rep:prefGetF(FIS_K.rep, FIS_PADRAO.rep, 0, 20),
            cit:prefGet('vault-panel:citacoes', 0, 0, 1) === 1};
const GKIND = {modulo:'ctx', componente:'ctx', engenharia:'ctx', contexto:'ctx', glossario:'ctx', spec:'spec', adr:'adr', memoria:'mem', outro:'mem', anexo:'mem'};
const GGROUPS = [
  {k:'ctx',  l:'Contexto', c:'var(--c1)', d:'módulos, componentes, engenharia, glossário'},
  {k:'spec', l:'Specs', c:'var(--c2)', d:'as specs de 01_Specs (1º nível) — as mesmas da aba Andamento'},
  {k:'adr',  l:'ADRs', c:'var(--c3)'},
  {k:'mem',  l:'Memória, templates e outros', c:'var(--c-outros)', d:'memória do agente, índices de 02_Memory, templates e subpastas de 01_Specs, docs soltos'}
];
const KIND_L = {modulo:'Módulo', componente:'Componente', engenharia:'Engenharia', contexto:'Contexto', glossario:'Glossário',
                spec:'Spec', spec_aux:'Template ou auxiliar de 01_Specs', adr:'ADR', memoria:'Memória', outro:'Outro', anexo:'Anexo'};
/* o vault_graph chama de "spec" tudo que está em 01_Specs/** (templates de e-mail/form/LP, _template, _arquivadas);
   aqui spec = 1º nível sem o _template.md, o mesmo recorte da aba Andamento — o resto vira "spec_aux" */
function gTk(n){
  if (n.tipo !== 'spec') return n.tipo;
  return /^01_Specs\/[^/]+\.md$/.test(n.id) && n.id !== '01_Specs/_template.md' ? 'spec' : 'spec_aux';
}
function kindL(n){ return KIND_L[n.tk] || n.tk; }
/* tela de toque sem mouse: um dedo rola a página, dois movem/dão zoom no mapa (mesma media query do CSS) */
const GTOUCH = matchMedia('(hover: none) and (pointer: coarse)').matches;
const PRF = new Intl.NumberFormat('pt-BR', {minimumFractionDigits:4, maximumFractionDigits:4});
const RM = matchMedia('(prefers-reduced-motion: reduce)').matches;
let G = null, gUI = null, gSim = null, gZoom = null, gCv = null, gCtx = null, gPal = null;
let gW = 0, gH = 0, gDpr = 1, gTf = null, gHover = null, gSel = null, gAutoFit = true, gRun = 0, gHintT = null;
let gVis = [], gBase = [], gVN = [], gVL = [];
let gSelDim = true;   /* seleção apaga o que não é vizinho — até o recorte mudar (aí vira só o anel) */
let gRec = false;     /* recorte ativo com vizinhos: os vizinhos (fora de gBase) saem esmaecidos */

function gBuild(){
  if (!GR){ G = null; return; }
  const prev = G ? G.byId : null;
  const nodes = GR.nos.map((n, i) => {
    const o = prev ? prev.get(n.id) : null;
    const tk = gTk(n);
    const node = Object.assign({}, n, {i, tk, grp: tk === 'spec_aux' ? 'mem' : (GKIND[n.tipo] || 'mem'), deg: n.grau_in + n.grau_out,
      lab: n.rotulo, _hay: fold(n.rotulo + ' ' + n.id)});
    if (o && o.x != null){ node.x = o.x; node.y = o.y; }
    return node;
  });
  const byId = new Map(nodes.map(n => [n.id, n]));
  const adj = nodes.map(() => new Set()), ins = nodes.map(() => []), outs = nodes.map(() => []), links = [];
  for (const e of GR.arestas){
    const a = nodes[e[0]], b = nodes[e[1]];
    if (!a || !b) continue;
    links.push({source:a, target:b, ex: e[2] !== 0});   // ex = ligação que o Obsidian também desenha
    adj[a.i].add(b.i); adj[b.i].add(a.i); outs[a.i].push(b.i); ins[b.i].push(a.i);
  }
  let prMax = 1e-9; nodes.forEach(n => { if (n.pagerank > prMax) prMax = n.pagerank; });
  const prRank = new Map(nodes.slice().sort((a, b) => b.pagerank - a.pagerank).map((n, k) => [n.id, k + 1]));   // posição no ranking
  const byPr = nodes.slice().sort((a, b) => b.pagerank - a.pagerank);
  /* assinatura da ESTRUTURA (ids + arestas): versão nova que só mudou métricas não reaquece a simulação */
  let hs = 2166136261 >>> 0;
  const mix = v => { hs = Math.imul(hs ^ v, 16777619) >>> 0; };
  for (const n of GR.nos){ for (let c = 0; c < n.id.length; c++) mix(n.id.charCodeAt(c)); mix(10); }
  for (const e of GR.arestas){ mix(e[0]); mix(e[1] + 1e6); }
  G = {nodes, links, adj, ins, outs, byId, prMax, prRank, byPr, sig: GR.nos.length + ':' + GR.arestas.length + ':' + hs};
  gSeed(nodes, adj);
  nodes.forEach(n => { n.r = gRadius(n); });
  if (FOCO){ cosDepth(); pcPadraoCache = null; }   // projetos podem ter mudado: refaz as cores padrão
  gHover = null;
  if (gSel && !byId.has(gSel)) gSel = null;
}
/* posição inicial: nó que já existia mantém a sua; novo nasce perto de um vizinho posicionado, senão no setor
   da sua área (o d3-force só acomoda — sem layout pré-calculado no servidor) */
function gSeed(nodes, adj){
  const areas = [...new Set(nodes.map(n => n.area))].sort();
  const R0 = 14 * Math.sqrt(nodes.length);
  const ctr = new Map(areas.map((a, k) => { const t = 2 * Math.PI * k / areas.length; return [a, [Math.cos(t) * R0, Math.sin(t) * R0]]; }));
  let seed = 7;
  const rnd = () => { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed / 4294967296; };
  for (const n of nodes){
    if (n.x != null) continue;
    let base = null;
    for (const j of adj[n.i]){ const m = nodes[j]; if (m.x != null){ base = [m.x, m.y]; break; } }
    const c = base || ctr.get(n.area), r = (base ? 24 : R0 * 0.35) * Math.sqrt(rnd()), t = 2 * Math.PI * rnd();
    n.x = c[0] + r * Math.cos(t); n.y = c[1] + r * Math.sin(t);
  }
}
function gRadius(n){ return GF.pr ? 2.2 + 24 * Math.sqrt(n.pagerank / G.prMax) : 3 + Math.sqrt(Math.max(1, n.deg)) * 1.35; }
function fmtPr(v){ return PRF.format(v || 0); }
function gIsOrphanAdr(n){ return n.tipo === 'adr' && n.grau_in === 0; }
function gConjIds(k){
  const M = GR.metricas;
  switch (k){
    case 'orfaos': return M.orfaos;
    case 'adrs_nunca_citados': return M.adrs_nunca_citados;
    case 'nao_resolvidas': return [...new Set(M.nao_resolvidas.map(r => r.origem))];
    case 'working': return M.working;
    case 'arquivados': return M.arquivados.ids;
    case 'ilhas': return M.componentes.ilhas.flat().concat(G.nodes.filter(n => n.deg === 0).map(n => n.id));
    case 'hubs': return M.hubs.map(x => x.id);
  }
  return [];
}
function gCompute(){
  const N = G.nodes, conj = GF.conj ? new Set(gConjIds(GF.conj)) : null;
  const words = GF.q ? fold(GF.q).split(/\s+/).filter(Boolean) : [];
  const recorte = !!(GF.tipo || GF.area || conj || words.length);
  const base = N.map(n => (!GF.tipo || n.tk === GF.tipo) && (!GF.area || n.area === GF.area) &&
    (!conj || conj.has(n.id)) && (!words.length || words.every(w => n._hay.includes(w))));
  const vis = base.slice();
  if (recorte && GF.viz) N.forEach((n, i) => { if (base[i]) G.adj[i].forEach(j => { vis[j] = true; }); });
  /* ADR órfão (ninguém cita) só aparece com "Incluir ADRs órfãos" — ou quando é o próprio conjunto escolhido */
  if (!GF.orfaos) N.forEach((n, i) => { if (vis[i] && gIsOrphanAdr(n) && !(conj && conj.has(n.id))) vis[i] = false; });
  if (!GF.anexos) N.forEach((n, i) => { if (n.tipo === 'anexo'){ vis[i] = false; base[i] = false; } });
  /* projetos desligados na legenda do universo: filtro duro (nem como vizinho do recorte) */
  if (PJ_OFF.size) N.forEach((n, i) => { if (PJ_OFF.has(n.projeto)){ vis[i] = false; base[i] = false; } });
  return {vis, base, recorte};
}
/* fit = o recorte mudou (filtro, busca, métrica): enquadra de novo e a seleção deixa de apagar o resto do mapa
   (fica só o anel) — senão o resultado do filtro some sob o foco antigo */
function gApply(alpha, fit){
  if (!G) return;
  const r = gCompute(); gVis = r.vis; gBase = r.base; gRec = r.recorte && GF.viz;
  gVN = G.nodes.filter(n => gVis[n.i]);
  gVL = G.links.filter(l => gVis[l.source.i] && gVis[l.target.i] && (GF.cit || l.ex));   // citação só com o interruptor
  if (FOCO){   /* universo: sem ligação VISÍVEL = órfão → anel em volta do núcleo (como no Obsidian), fora da física */
    const lk = new Uint8Array(G.nodes.length);
    for (const l of gVL){ lk[l.source.i] = 1; lk[l.target.i] = 1; }
    G.nodes.forEach(n => { n.orf = !!gVis[n.i] && !lk[n.i]; });
  }
  for (const n of G.nodes) n.vd = 0;                  // ligações visíveis por nó (força de cada ligação: linkStr)
  for (const l of gVL){ l.source.vd++; l.target.vd++; }
  if (fit) gSelDim = false;
  if (gSim){
    gSim.nodes(FOCO ? gVN.filter(n => !n.orf) : gVN); gSim.force('link').links(gVL);
    if (fit) gAutoFit = true;
    gKick(alpha);
  }
  gCountRender(); gLegendRender(); gTableRender(); gDraw();
}
function gKick(alpha){
  if (!gSim || !(alpha > 0)) return;
  if (active === 'grafo'){ gSim.alpha(Math.max(gSim.alpha(), alpha || 0.1)).restart(); }
  else gRun = Math.max(gRun, alpha || 0.1);
}
function gPause(){ if (gSim){ if (gSim.alpha() > gSim.alphaMin()) gRun = Math.max(gRun, gSim.alpha()); gSim.stop(); } hideGHover(); }
function gResume(){
  if (!gUI) return;
  gSize();
  if (gSim && gRun > 0){ gSim.alpha(Math.max(gSim.alpha(), gRun)).restart(); gRun = 0; }
  gDraw();
}
function hideGHover(){ if (gHover){ gHover = null; } if (tipOwner && tipOwner === gCv) hideTip(); }

/* ── canvas: tokens do tema lidos do CSS (e relidos quando o tema muda) ── */
function gReadPal(){
  const cs = getComputedStyle(document.documentElement), v = k => cs.getPropertyValue(k).trim();
  gPal = {grp:{ctx:v('--c1'), spec:v('--c2'), adr:v('--c3'), mem:v('--c-outros')}, edge:v('--axis'), edgeHi:v('--ink-2'),
          label:v('--ink-2'), surface:v('--surface'), ink:v('--ink'), warn:v('--warn')};
}
function gSize(){
  if (!gUI || !gCv) return;
  const r = gUI.wrap.getBoundingClientRect();
  if (r.width < 10 || r.height < 10) return;      // aba escondida: mantém o tamanho anterior
  gDpr = window.devicePixelRatio || 1;
  gW = r.width; gH = r.height;
  gCv.width = Math.round(gW * gDpr); gCv.height = Math.round(gH * gDpr);
  if (!gTf) gTf = HAS_D3 ? d3.zoomIdentity.translate(gW / 2, gH / 2).scale(0.35) : {x:gW / 2, y:gH / 2, k:0.35};
}
function gDraw(){
  if (FOCO){ cosRequest(); return; }          // página única: o universo desenha no próprio laço
  if (!gUI || !gCtx || !G || !gTf || !gW) return;
  const ctx = gCtx, P = gPal, k = gTf.k;
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.clearRect(0, 0, gCv.width, gCv.height);
  ctx.setTransform(gDpr * k, 0, 0, gDpr * k, gDpr * gTf.x, gDpr * gTf.y);
  const selN = gSel ? G.byId.get(gSel) : null;
  let focus = gHover || (gSelDim ? selN : null);
  if (focus && !gVis[focus.i]) focus = null;
  const nb = focus ? G.adj[focus.i] : null;
  /* trama de ~16 mil arestas SEMPRE abaixo de 1 px de dispositivo: acima disso (DPR ≥ 1,5 — celular, Windows a
     150%) o Skia sai do caminho rápido de linha fina e cada desenho passa de 120 ms (mapa a 5 fps) */
  ctx.lineWidth = Math.min(0.7, 0.9 / gDpr) / k; ctx.strokeStyle = P.edge; ctx.globalAlpha = focus ? 0.10 : 0.45;
  ctx.beginPath();
  for (const l of gVL){
    if (focus && (l.source === focus || l.target === focus)) continue;
    ctx.moveTo(l.source.x, l.source.y); ctx.lineTo(l.target.x, l.target.y);
  }
  ctx.stroke();
  if (focus){
    ctx.lineWidth = 1.2 / k; ctx.strokeStyle = P.edgeHi; ctx.globalAlpha = 0.9;
    ctx.beginPath();
    for (const l of gVL){
      if (l.source !== focus && l.target !== focus) continue;
      ctx.moveTo(l.source.x, l.source.y); ctx.lineTo(l.target.x, l.target.y);
    }
    ctx.stroke();
  }
  for (const n of gVN){
    const dim = focus && n !== focus && !nb.has(n.i);
    ctx.globalAlpha = dim ? 0.14 : (!focus && gRec && !gBase[n.i]) ? 0.3 : 1;   // vizinho do recorte: esmaecido
    const c = P.grp[n.grp] || P.grp.mem;
    ctx.beginPath(); ctx.arc(n.x, n.y, n.r, 0, 6.2832);
    if (n.arquivado){      // contorno vazio: arquivado é histórico, não contexto
      ctx.fillStyle = P.surface; ctx.fill();
      ctx.lineWidth = Math.max(1.5 / k, n.r * 0.35); ctx.strokeStyle = c; ctx.stroke();
    } else {
      ctx.fillStyle = c; ctx.fill();
      ctx.lineWidth = 1 / k; ctx.strokeStyle = P.surface; ctx.stroke();   // anel de superfície entre nós que se tocam
    }
    if (n.working){
      ctx.beginPath(); ctx.arc(n.x, n.y, n.r + 2.5 / k, 0, 6.2832);
      ctx.lineWidth = 2 / k; ctx.strokeStyle = P.warn; ctx.stroke();
    }
  }
  if (selN && gVis[selN.i]){
    ctx.globalAlpha = 1; ctx.beginPath(); ctx.arc(selN.x, selN.y, selN.r + 4.5 / k, 0, 6.2832);
    ctx.lineWidth = 2 / k; ctx.strokeStyle = P.ink; ctx.stroke();
  }
  gLabels(ctx, P, k, focus, nb);
}
/* rótulos em px de tela: aparecem com o zoom (mais centrais antes); com foco, o foco e os vizinhos mais
   centrais. Grade de ocupação: rótulo que encostaria noutro já posto não é desenhado (sem amontoado). */
let gGrid = null, gMeasure = null, gNbCache = {id:null, list:[]};
const LBL_FONT = '500 11px "Google Sans Variable", "Google Sans", system-ui, sans-serif';
function gLabelW(n){
  if (n._w == null){
    if (!gMeasure){ gMeasure = document.createElement('canvas').getContext('2d'); gMeasure.font = LBL_FONT; }
    n._w = gMeasure.measureText(n.lab).width;
  }
  return n._w;
}
function gLabels(ctx, P, k, focus, nb){
  const CW = 6, cols = Math.ceil(gW / CW) + 2, rows = Math.ceil(gH / CW) + 2;
  if (!gGrid || gGrid.length !== cols * rows) gGrid = new Uint8Array(cols * rows); else gGrid.fill(0);
  ctx.setTransform(gDpr, 0, 0, gDpr, 0, 0);
  ctx.font = LBL_FONT; ctx.textAlign = 'center'; ctx.textBaseline = 'top'; ctx.lineJoin = 'round';
  const thr = 1.21;
  const put = (n, alpha, force) => {
    const w = gLabelW(n) + 4, sx = n.x * k + gTf.x, sy = (n.y + n.r) * k + gTf.y + 2;
    const x0 = sx - w / 2, x1 = sx + w / 2, y0 = sy, y1 = sy + 13;
    if (x1 < 0 || x0 > gW || y1 < 0 || y0 > gH) return;
    const c0 = Math.max(0, Math.floor(x0 / CW)), c1 = Math.min(cols - 1, Math.floor(x1 / CW));
    const r0 = Math.max(0, Math.floor(y0 / CW)), r1 = Math.min(rows - 1, Math.floor(y1 / CW));
    if (!force) for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++) if (gGrid[r * cols + c]) return;
    for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++) gGrid[r * cols + c] = 1;
    ctx.globalAlpha = alpha;
    ctx.lineWidth = 3; ctx.strokeStyle = P.surface; ctx.strokeText(n.lab, sx, sy);
    ctx.fillStyle = P.label; ctx.fillText(n.lab, sx, sy);
  };
  if (focus){
    put(focus, 1, true);
    if (gNbCache.id !== focus.id || gNbCache.v !== G){
      gNbCache = {id:focus.id, v:G, list:[...nb].map(j => G.nodes[j]).sort((a, b) => b.pagerank - a.pagerank)};
    }
    for (const m of gNbCache.list) if (gVis[m.i]) put(m, 1, false);
  } else {
    /* opacidade com piso de 0,8 (texto a 0,25–0,5 ficava abaixo de 3:1); com recorte, só os que casaram
       ganham rótulo — os vizinhos esmaecidos aparecem ao passar o mouse */
    for (const n of G.byPr){
      if (!gVis[n.i] || (gRec && !gBase[n.i])) continue;
      const effZ = k + Math.sqrt(Math.max(1, n.deg)) / 9;
      if (effZ < thr) continue;
      put(n, 0.8 + 0.2 * Math.min(1, (effZ - thr) * 2.5), false);
    }
  }
  ctx.globalAlpha = 1;
}
/* nó SOB o ponteiro (o último desenhado, que fica por cima); só se nenhum contém o ponto, o mais próximo num
   raio de 18 px de tela (alvo de toque maior que o nó) */
function gPick(ev){
  if (FOCO) return cosPick(ev);
  if (!gSim || !gTf) return null;
  const src = ev.touches ? (ev.touches[0] || ev.changedTouches[0]) : ev;
  if (!src) return null;
  const p = gTf.invert(d3.pointer(src, gCv)), px = p[0], py = p[1], tol = 2 / gTf.k;
  if (!isFinite(px) || !isFinite(py)) return null;
  for (let j = gVN.length - 1; j >= 0; j--){
    const n = gVN[j], dx = n.x - px, dy = n.y - py, r = n.r + tol;
    if (dx * dx + dy * dy <= r * r) return n;
  }
  return gSim.find(px, py, 18 / gTf.k) || null;
}
function gTipFor(ev, n){
  showTip(ev, n.lab, [
    {v: kindL(n), l: '· área ' + n.area + (n.working ? ' · em construção' : '') + (n.arquivado ? ' · arquivado' : '')},
    {v: n.grau_in, l: 'citado por (in)'},
    {v: n.grau_out, l: 'aponta para (out)'},
    {v: fmtPr(n.pagerank), l: 'PageRank · #' + nfmt(G.prRank.get(n.id)) + ' de ' + nfmt(G.nodes.length)}
  ]);
}
function gCanvasInit(){
  gCv = gUI.canvas; gCtx = gCv.getContext('2d');
  gReadPal();
  gSize();
  if (!HAS_D3) return;
  gSim = d3.forceSimulation([])
    .force('link', d3.forceLink([]).distance(GF.ld).strength(linkStr))
    .force('charge', d3.forceManyBody().strength(-GF.rep * REP_K).theta(0.9))   // sem alcance máximo: o grupo grande abre em disco, como no Obsidian
    .force('x', d3.forceX(0).strength(GF.cent * CEN_K)).force('y', d3.forceY(0).strength(GF.cent * CEN_K))
    .velocityDecay(0.55).alphaDecay(0.028)
    .on('tick', gDraw)
    .on('end', () => { if (gAutoFit){ gAutoFit = false; gFit(); } });
  gSim.stop();
  gZoom = d3.zoom().scaleExtent([0.05, 8])
    /* rolagem sozinha continua rolando a página; Ctrl/⌘ + rolagem ou pinça dão zoom. No toque (GTOUCH), um dedo
       é da página — o gesto do mapa só começa com dois dedos */
    .filter(ev => ev.type === 'wheel' ? (FOCO || ev.ctrlKey || ev.metaKey)
      : ev.type.slice(0, 5) === 'touch' ? (!GTOUCH || ev.touches.length >= 2)
      : (!ev.button && !gPick(ev)))
    .on('zoom', ev => { gTf = ev.transform; if (ev.sourceEvent) gAutoFit = false; gDraw(); });
  const drag = d3.drag().container(gCv)      /* no universo (FOCO) o mapa gira em 3D: arrastar nó não faz sentido */
    .filter(ev => !FOCO && (ev.type.slice(0, 5) === 'touch' ? !GTOUCH : (!ev.ctrlKey && !ev.button)))
    .subject(ev => gPick(ev.sourceEvent || ev))
    .on('start', ev => { gCv.classList.add('drag'); hideTip(); if (!ev.active) gSim.alphaTarget(0.25).restart(); ev.subject.fx = ev.subject.x; ev.subject.fy = ev.subject.y; })
    .on('drag', ev => { const p = gTf.invert(d3.pointer(ev.sourceEvent, gCv)); ev.subject.fx = p[0]; ev.subject.fy = p[1]; })
    .on('end', ev => { gCv.classList.remove('drag'); if (!ev.active) gSim.alphaTarget(0); ev.subject.fx = null; ev.subject.fy = null; });
  d3.select(gCv).call(drag).call(gZoom).on('dblclick.zoom', null);
  /* o d3-drag grava touch-action:none inline; no toque a página precisa receber o gesto de um dedo */
  if (GTOUCH) gCv.style.touchAction = 'pan-x pan-y';
  d3.select(gCv).call(gZoom.transform, gTf);
  gCv.addEventListener('pointermove', ev => {
    if (gCv.classList.contains('drag')) return;
    const n = gPick(ev);
    if (n !== gHover){ gHover = n; gCv.classList.toggle('hit', !!n); gDraw(); }
    if (n) gTipFor(ev, n); else if (tipOwner === gCv) hideTip();
  });
  gCv.addEventListener('pointerleave', ev => { if (gHover){ gHover = null; gCv.classList.remove('hit'); gDraw(); } leaveTip(ev); });
  gCv.addEventListener('click', ev => { const n = gPick(ev); gSelect(n ? n.id : null); });
  gCv.addEventListener('wheel', ev => { if (!FOCO && !(ev.ctrlKey || ev.metaKey)) gHint(); }, {passive:true});
  if (GTOUCH) gCv.addEventListener('touchmove', ev => { if (ev.touches.length === 1) gHint(); }, {passive:true});
  if (typeof ResizeObserver === 'function') new ResizeObserver(() => { if (active === 'grafo'){ gSize(); gDraw(); } }).observe(gUI.wrap);
  matchMedia('(prefers-color-scheme: dark)').addEventListener('change', () => { gReadPal(); gDraw(); });
  new MutationObserver(() => { gReadPal(); gDraw(); }).observe(document.documentElement, {attributes:true, attributeFilter:['data-theme']});
}
function gHint(){
  gUI.hint.classList.add('show'); clearTimeout(gHintT);
  gHintT = setTimeout(() => gUI.hint.classList.remove('show'), 1400);
}
function gZoomBy(f){ if (gZoom) d3.select(gCv).transition().duration(RM ? 0 : 200).call(gZoom.scaleBy, f); }
function gFit(){
  if (FOCO){ cosFit(); return; }
  if (!gZoom || !gVN.length || !gW) return;
  const q = (arr, p) => arr[Math.max(0, Math.min(arr.length - 1, Math.round(p * (arr.length - 1))))];
  const xs = gVN.map(n => n.x).sort((a, b) => a - b), ys = gVN.map(n => n.y).sort((a, b) => a - b);
  const x0 = q(xs, 0.01), x1 = q(xs, 0.99), y0 = q(ys, 0.01), y1 = q(ys, 0.99);   // ignora os poucos nós arremessados longe
  const pad = 40, w = Math.max(40, x1 - x0), hh = Math.max(40, y1 - y0);
  const k = Math.max(0.05, Math.min(2, Math.min((gW - 2 * pad) / w, (gH - 2 * pad) / hh)));
  const t = d3.zoomIdentity.translate(gW / 2 - (x0 + x1) / 2 * k, gH / 2 - (y0 + y1) / 2 * k).scale(k);
  d3.select(gCv).transition().duration(RM ? 0 : 400).call(gZoom.transform, t);
}
function gCenter(n){
  if (FOCO){ cosCenter(n); return; }
  if (!gZoom || n.x == null || !gW) return;
  gAutoFit = false;
  const k = Math.max(gTf.k, 0.9);
  const t = d3.zoomIdentity.translate(gW / 2 - n.x * k, gH / 2 - n.y * k).scale(k);
  d3.select(gCv).transition().duration(RM ? 0 : 450).call(gZoom.transform, t);
}
/* seleção: painel de detalhe + foco no mapa; opt.center = veio de uma lista (centraliza e rola até o mapa) */
function gSelect(id, opt){
  gSel = id && G && G.byId.has(id) ? id : null;
  gSelDim = true;
  gPanelRender();
  if (opt && opt.center && gSel){
    const n = G.byId.get(gSel);
    if (gVis[n.i]) gCenter(n);
    if (opt.scroll && gUI) gUI.card.scrollIntoView({block:'start', behavior: RM ? 'auto' : 'smooth'});
  }
  gDraw();
}
function gShowNode(id){ gSelect(id, {center:true, scroll:true}); }
function gClearFilters(){
  GF.q = ''; GF.tipo = ''; GF.area = ''; GF.conj = '';
  gUI.q.value = ''; gUI.tipo.value = ''; gUI.area.value = '';
  gKpisRender(); gConjRender(); gApply(0.3, true);
}
function nodeBtn(id, extra){
  const n = G.byId.get(id);
  const lab = n ? n.lab : id;
  return h('button', {type:'button', class:'link', title:id, onclick: () => gShowNode(id)}, lab, extra || null);
}
function grpSwatch(n){
  const c = GR && GR.universo ? cosCor(n) : (GGROUPS.find(x => x.k === n.grp) || GGROUPS[3]).c;   // no universo: a cor da estrela
  return h('span', {class:'sw round' + (n.arquivado ? ' hollowk' : ''), style: n.arquivado ? 'border-color:' + c : 'background:' + c});
}

/* ── painel de detalhe do nó ── */
function gPanelRender(){
  if (!gUI) return;
  const host = gUI.panel, keep = host.scrollTop;
  host.replaceChildren();
  const n = gSel && G ? G.byId.get(gSel) : null;
  if (FOCO) host.hidden = !n;
  if (!n){
    host.appendChild(h('h3', null, 'Detalhe'));
    host.appendChild(h('p', {class:'empty'}, 'Clique num nó do mapa, ou num doc das listas, para ver caminho, grau e vizinhos.'));
    host.appendChild(h('ul', {class:'hints'}, GTOUCH ? [
      h('li', null, 'Toque num nó para ver o detalhe e destacar os vizinhos.'),
      h('li', null, 'Um dedo rola a página; dois dedos movem o mapa e a pinça dá zoom.'),
      h('li', null, '"+", "−" e "Enquadrar" também navegam; "Ver como tabela" lista os nós.')
    ] : [
      h('li', null, 'Passe o mouse para destacar os vizinhos.'),
      h('li', null, 'Arraste um nó para movê-lo; arraste o fundo para navegar.'),
      h('li', null, 'Ctrl + rolagem (ou pinça) para zoom; "Enquadrar" mostra tudo.'),
      h('li', null, 'Enter na busca seleciona o doc mais central que casar.')]));
    return;
  }
  host.appendChild(h('div', {class:'gp-head'}, h('h3', null, n.lab),
    h('button', {type:'button', class:'btn', 'aria-label':'Fechar detalhe', onclick: () => gSelect(null)}, ico('x'))));
  host.appendChild(h('div', {class:'slug', style:'margin-top:var(--spacing-2xs)'}, n.id));
  host.appendChild(h('div', {class:'stline'}, h('span', {class:'badge'}, grpSwatch(n), kindL(n)),
    h('span', {class:'badge'}, 'área ' + n.area),
    n.working ? h('span', {class:'badge'}, h('span', {class:'sw round ringk'}), 'em construção') : null,
    n.arquivado ? h('span', {class:'badge'}, 'arquivado') : null));
  host.appendChild(h('div', {class:'facts'},
    h('div', null, h('span', null, 'Citado por (in)'), nfmt(n.grau_in)),
    h('div', null, h('span', null, 'Aponta para (out)'), nfmt(n.grau_out)),
    h('div', null, h('span', null, 'PageRank'), fmtPr(n.pagerank) + ' · #' + nfmt(G.prRank.get(n.id)) + ' de ' + nfmt(G.nodes.length))));
  const slug = nodeSpecSlug(n);
  const acts = h('div', {class:'acts'}, obsLink(n.id, n.lab, true),
    slug && SPEC.has(slug) ? h('button', {type:'button', class:'btn', onclick: e => openSpec(slug, e.currentTarget)}, 'Ver andamento da spec') : null,
    gVis[n.i] ? h('button', {type:'button', class:'btn', onclick: () => gCenter(n)}, 'Centralizar') : null);
  if (acts.childNodes.length) host.appendChild(acts);
  if (n.id.indexOf('memoria/') === 0)
    host.appendChild(h('p', {class:'caption'}, 'Memória do agente (fora do vault): ' + (GR.memoria_dir || '~/.claude/…/memory') + '.'));
  if (!gVis[n.i])
    host.appendChild(h('div', {class:'gp-out'}, 'Fora do recorte atual do mapa. ',
      h('button', {type:'button', class:'btn', onclick: () => { if (n.projeto && PJ_OFF.has(n.projeto)) pjToggle(n.projeto, true); gClearFilters(); if (gIsOrphanAdr(n) && !GF.orfaos){ GF.orfaos = true; gUI.orfBox.checked = true; gApply(0.3); } gSelect(n.id, {center:true}); }}, 'Mostrar no mapa')));
  const lista = (titulo, idxs) => {
    host.appendChild(h('div', {class:'gp-sec'}, titulo + ' (' + nfmt(idxs.length) + ')'));
    if (!idxs.length){ host.appendChild(h('p', {class:'empty', style:'margin:var(--spacing-xs) 0'}, 'nenhum')); return; }
    const ord = idxs.map(j => G.nodes[j]).sort((a, b) => b.pagerank - a.pagerank);
    const ul = h('ul', {class:'nlist'});
    const put = arr => arr.forEach(m => ul.appendChild(h('li', null, grpSwatch(m),
      h('button', {type:'button', class:'link', title:m.id, onclick: () => gSelect(m.id, {center:true})}, m.lab),
      h('span', {class:'m'}, kindL(m)))));
    put(ord.slice(0, 40));
    host.appendChild(ul);
    if (ord.length > 40){
      const more = h('button', {type:'button', class:'btn', style:'margin-top:var(--spacing-sm)', onclick: () => { put(ord.slice(40)); more.remove(); }}, 'Mostrar todos (' + nfmt(ord.length) + ')');
      host.appendChild(more);
    }
  };
  lista('Citado por', G.ins[n.i]);
  lista('Aponta para', G.outs[n.i]);
  host.scrollTop = keep;
}

/* ── cartões de métrica (clicáveis: recortam o mapa e listam) ── */
function gTiles(){
  const M = GR.metricas, C = M.componentes;
  const fora = Math.max(0, G.nodes.length - (C.maior || 0));
  const topHub = M.hubs.length ? G.byId.get(M.hubs[0].id) : null;
  return [
    {k:'orfaos', l:'Contexto órfão', v:M.orfaos.length, t:'Docs de contexto que nenhum outro doc aponta (fora o _INDEX)'},
    {k:'adrs_nunca_citados', l:'ADRs nunca citados', v:M.adrs_nunca_citados.length, t:'Nenhum doc cita o ADR, nem por número'},
    {k:'nao_resolvidas', l:'Referências não resolvidas', v:M.nao_resolvidas.length, t:'Links e caminhos que não viram doc do vault; o mapa mostra as origens'},
    {k:'working', l:'Em construção', v:M.working.length, mark:h('span', {class:'sw round ringk'}), t:'status: working ou "EM CONSTRUÇÃO" no começo do doc'},
    {k:'arquivados', l:'Arquivados', v:M.arquivados.total, mark:h('span', {class:'sw round hollowk'}), t:'status: arquivado — histórico, não contexto'},
    {k:'ilhas', l:'Componentes', v:C.total, sub:nfmt(fora) + ' fora do principal', lt:'Fora do componente principal', t:'Grupos sem caminho entre si; o mapa mostra quem está fora do componente principal'},
    {k:'hubs', l:'Maior hub (ligações)', v:topHub ? topHub.deg : 0, sub: topHub ? topHub.lab : '', lt:'Hubs — os ' + M.hubs.length + ' docs de contexto de maior grau', t:'Os 30 docs de contexto de maior grau (candidatos a quebrar se crescerem)'}
  ];
}
function gKpisRender(){
  const foco = gUI.kpis.contains(document.activeElement) ? document.activeElement.dataset.k : null;
  gUI.kpis.replaceChildren(...gTiles().map(t => h('button', {type:'button', class:'kpi', 'data-k':t.k,
      'aria-pressed':String(GF.conj === t.k), title:t.t, onclick: () => gSetConj(GF.conj === t.k ? '' : t.k)},
    h('span', {class:'lbl'}, t.mark || null, t.l), h('span', {class:'val'}, nfmt(t.v)), t.sub ? h('span', {class:'sub'}, t.sub) : null)));
  if (foco){ const b = gUI.kpis.querySelector('[data-k="' + foco + '"]'); if (b) b.focus({preventScroll:true}); }
}
function gSetConj(k){
  GF.conj = k; GF.todosC = false;
  gUI.kpis.querySelectorAll('.kpi').forEach(b => b.setAttribute('aria-pressed', String(b.dataset.k === k)));
  gConjRender(); gApply(0.3, true);
}
function docCell(id){
  const n = G.byId.get(id);
  return h('td', {class:'t'}, n ? grpSwatch(n) : null, ' ', nodeBtn(id), ' ', obsLink(id, n ? n.lab : id),
    h('div', {class:'slug'}, id));
}
/* lista longa: 300 linhas e "Mostrar todos" (a escolha fica em GF[flag] e sobrevive a dados novos) */
function limited(host, rows, LIM, flag, mkTable){
  const all = GF[flag];
  host.appendChild(mkTable(all ? rows : rows.slice(0, LIM)));
  if (rows.length > LIM && !all)
    host.appendChild(h('button', {type:'button', class:'btn', style:'margin-top:var(--spacing-sm)', onclick: () => { GF[flag] = true; limitedRedraw(flag); }}, 'Mostrar todos (' + nfmt(rows.length) + ')'));
}
function limitedRedraw(flag){ if (flag === 'todosT') gTableRender(); else if (flag === 'todosR') gRefsRender(); else gConjRender(); }
function docTable(ids, cols){
  const t = h('table', {class:'rows'});
  t.appendChild(h('thead', null, h('tr', null, h('th', {scope:'col'}, 'Doc'), cols.map(c => h('th', {scope:'col', class: c.txt ? null : 'num'}, c.l)))));
  const tb = h('tbody');
  ids.forEach(id => { const n = G.byId.get(id); tb.appendChild(h('tr', null, docCell(id), cols.map(c => h('td', {class: c.txt ? null : 'num'}, n ? c.f(n) : '—')))); });
  t.appendChild(tb);
  return h('div', {class:'scroll-x'}, t);
}
const COL_IN = {l:'In', f:n => nfmt(n.grau_in)}, COL_OUT = {l:'Out', f:n => nfmt(n.grau_out)};
const COL_PR = {l:'PageRank', f:n => fmtPr(n.pagerank)}, COL_TIPO = {l:'Tipo', txt:true, f:n => kindL(n)};
const COL_GRAU = {l:'Grau', f:n => nfmt(n.deg)};
function gConjRender(){
  const c = gUI.conjCard;
  c.replaceChildren();
  if (!GF.conj){ c.hidden = true; return; }
  c.hidden = false;
  const t = gTiles().find(x => x.k === GF.conj);
  const ids = gConjIds(GF.conj);
  c.appendChild(h('div', {class:'chart-head'}, h('div', null, h('h2', null, t.lt || t.l), h('div', {class:'sub'}, t.t + ' · ' + plural(ids.length, 'doc', 'docs') + ' no recorte do mapa')),
    h('button', {type:'button', class:'btn', onclick: () => gSetConj('')}, 'Limpar recorte')));
  const body = h('div');
  c.appendChild(body);
  if (!ids.length){ body.appendChild(h('p', {class:'empty'}, 'Nenhum doc nesta métrica.')); return; }
  if (GF.conj === 'nao_resolvidas'){
    body.appendChild(h('p', {class:'caption'}, 'O mapa mostra as ' + plural(ids.length, 'origem', 'origens') + '; a lista origem → alvo está em "Referências não resolvidas", abaixo. ',
      h('button', {type:'button', class:'btn', onclick: () => gUI.refCard.scrollIntoView({block:'start', behavior: RM ? 'auto' : 'smooth'})}, 'Ir para a lista')));
    return;
  }
  if (GF.conj === 'ilhas'){
    const M = GR.metricas;
    M.componentes.ilhas.forEach((isl, i) => { body.appendChild(h('div', {class:'isl'}, 'Ilha ' + (i + 1) + ' · ' + plural(isl.length, 'doc', 'docs'))); body.appendChild(docTable(isl, [COL_TIPO, COL_IN, COL_OUT])); });
    const iso = G.nodes.filter(n => n.deg === 0).map(n => n.id);
    if (iso.length){ body.appendChild(h('div', {class:'isl'}, 'Isolados (nenhum link, nem de ida nem de volta) · ' + nfmt(iso.length))); body.appendChild(docTable(iso, [COL_TIPO])); }
    return;
  }
  const cols = GF.conj === 'hubs' ? [COL_GRAU, COL_IN, COL_OUT, COL_PR] : [COL_TIPO, COL_IN, COL_OUT, COL_PR];
  limited(body, ids, 300, 'todosC', rows => docTable(rows, cols));
}

/* ── referências não resolvidas (origem → alvo), com filtro próprio ── */
function gRefsRender(){
  if (!gUI) return;
  const all = GR.metricas.nao_resolvidas;
  const words = GF.rq ? fold(GF.rq).split(/\s+/).filter(Boolean) : [];
  const rows = words.length ? all.filter(r => { const hay = fold(r.origem + ' ' + r.alvo); return words.every(w => hay.includes(w)); }) : all;
  gUI.refCount.textContent = nfmt(rows.length) + ' de ' + nfmt(all.length);
  const host = gUI.refBody;
  host.replaceChildren();
  if (!rows.length){ host.appendChild(h('p', {class:'empty'}, all.length ? 'Nenhuma referência com esse filtro.' : 'Nenhuma referência não resolvida.')); return; }
  limited(host, rows, 100, 'todosR', list => {
    const t = h('table', {class:'rows'});
    t.appendChild(h('thead', null, h('tr', null, h('th', {scope:'col'}, 'Origem'), h('th', {scope:'col'}, 'Alvo não resolvido'))));
    const tb = h('tbody');
    list.forEach(r => tb.appendChild(h('tr', null, docCell(r.origem), h('td', {class:'t'}, h('code', {class:'alvo'}, r.alvo)))));
    t.appendChild(tb);
    return h('div', {class:'scroll-x'}, t);
  });
}

/* ── tabela do mapa (gêmea acessível do canvas): nós visíveis por PageRank ── */
function gTableRender(){
  if (!gUI || gUI.table.hidden) return;
  const ids = gVN.slice().sort((a, b) => b.pagerank - a.pagerank).map(n => n.id);
  gUI.table.replaceChildren();
  if (!ids.length){ gUI.table.appendChild(h('p', {class:'empty'}, 'Nenhum nó no recorte.')); return; }
  limited(gUI.table, ids, 100, 'todosT', rows => docTable(rows, [COL_TIPO, {l:'Área', txt:true, f:n => n.area}, COL_IN, COL_OUT, COL_PR]));
}
function gCountRender(){
  if (!gUI) return;
  const arestas = plural(gVL.length, 'aresta', 'arestas');
  if (gRec){      // o que casou × vizinhos trazidos por "Incluir vizinhos do recorte"
    const achados = gVN.reduce((c, n) => c + (gBase[n.i] ? 1 : 0), 0);
    gUI.count.textContent = nfmt(achados) + (achados === 1 ? ' encontrado' : ' encontrados') + ' + ' + plural(gVN.length - achados, 'vizinho', 'vizinhos') +
      ' · de ' + plural(G.nodes.length, 'nó', 'nós') + ' · ' + arestas;
  } else gUI.count.textContent = nfmt(gVN.length) + ' de ' + plural(G.nodes.length, 'nó', 'nós') + ' · ' + arestas;
}
/* legenda do universo, no painel lateral: uma linha por projeto — olho (mostra/oculta), bolinha (a cor do projeto,
   clique para trocar), nome e quantas estrelas ele põe no mapa (o ADR que ninguém cita fica fora, como no mapa) */
function cosLegend(){
  if (!fUI || !fUI.leg || !G) return;
  const L = fUI.leg, ae = document.activeElement;
  const fk = L.contains(ae) ? (ae.dataset.f || null) : null;      // foco sobrevive ao redesenho
  L.replaceChildren();
  const cp = new Map();
  G.nodes.forEach(n => { if (n.projeto && (GF.orfaos || !gIsOrphanAdr(n)) && (GF.anexos || n.tipo !== 'anexo')) cp.set(n.projeto, (cp.get(n.projeto) || 0) + 1); });
  fUI.sub.textContent = plural(gVN.length, 'estrela', 'estrelas') + ' no mapa · ' + plural(gVL.length, 'ligação', 'ligações');
  const pj = pjLista(), pOff = pj.filter(x => PJ_OFF.has(x.p)).length;
  const sec = h('section', {class:'lgsec', 'aria-label':'Projetos'});
  sec.appendChild(h('div', {class:'lghead'},
    h('h2', null, 'Projetos', h('span', {class:'cnt'}, nfmt(pj.length - pOff) + ' de ' + nfmt(pj.length))),
    h('span', {class:'lgacts'},
      pOff ? h('button', {type:'button', class:'btn', 'data-f':'p-todos', onclick: pjTodos}, 'Mostrar todos') : null,
      Object.keys(PC).length ? h('button', {type:'button', class:'btn', 'data-f':'c-padrao', title:'Volta às cores padrão de todos os projetos',
        onclick: pcRestaurar}, ico('rotate-ccw'), 'Cores padrão') : null)));
  pj.forEach(x => {
    const on = !PJ_OFF.has(x.p), nome = pjNome(x.p);
    const row = h('div', {class:'lgrow' + (on ? '' : ' off'),
        onclick: e => { if (e.target === row || e.target.closest('.lgn, b')) pjToggle(x.p, !on); }},   // clicar no nome também alterna
      h('button', {type:'button', class:'lgeye', 'data-f':'p:' + x.p, 'aria-pressed':String(on), 'aria-label':'Mostrar ' + nome + ' no mapa',
        title: on ? 'Ocultar do mapa' : 'Mostrar no mapa', onclick: () => pjToggle(x.p, !on)}, ico(on ? 'eye' : 'eye-off')),
      h('input', {type:'color', class:'lgcor', value:pjCor(x.p), 'data-f':'c:' + x.p, title:'Trocar a cor', 'aria-label':'Cor de ' + nome,
        oninput: e => pcTrocar(x.p, e.target.value), onchange: () => gLegendRender()}),
      h('span', {class:'lgn'}, nome), h('b', null, nfmt(cp.get(x.p) || 0)));
    sec.appendChild(row);
  });
  sec.appendChild(h('div', {class:'lgkey'}, h('span', null, h('span', {class:'sw round ringk'}), 'em construção'),
    h('span', null, h('span', {class:'sw round hollowk'}), 'arquivado (estrela apagada)')));
  /* órfãos: o que o Obsidian mostra e o mapa pode esconder — mesmo olho dos projetos */
  let nAnexo = 0, nOrf = 0;
  G.nodes.forEach(n => { if (PJ_OFF.has(n.projeto)) return; if (n.tipo === 'anexo') nAnexo++; else if (gIsOrphanAdr(n)) nOrf++; });
  const tg = (f, on, nome, n, title, set) => {
    const row = h('div', {class:'lgrow' + (on ? '' : ' off'), title:title,
        onclick: e => { if (e.target === row || e.target.closest('.lgn, b')) set(!on); }},
      h('button', {type:'button', class:'lgeye', 'data-f':f, 'aria-pressed':String(on), 'aria-label':'Mostrar ' + nome.toLowerCase() + ' no mapa',
        onclick: () => set(!on)}, ico(on ? 'eye' : 'eye-off')),
      h('span', {class:'lgn'}, nome), h('b', null, nfmt(n)));
    return row;
  };
  const sec2 = h('section', {class:'lgsec', 'aria-label':'Mostrar no mapa'}, h('div', {class:'lghead'}, h('h2', null, 'Mostrar')));
  if (nAnexo || GF.anexos) sec2.appendChild(tg('o:anexos', GF.anexos, 'Anexos (imagens, PDFs)', nAnexo,
    'Imagens, PDFs, áudio e vídeo do vault (fora os "Arquivos excluídos" do Obsidian); o que ninguém cita fica solto',
    on => { GF.anexos = on; prefSet('vault-panel:anexos', on ? 1 : 0); gApply(0.3, true); }));
  sec2.appendChild(tg('o:adrs', GF.orfaos, 'ADRs que ninguém cita', nOrf, 'ADR sem nenhum doc apontando para ele',
    on => { GF.orfaos = on; prefSet('vault-panel:adrs-orfaos', on ? 1 : 0); if (gUI && gUI.orfBox) gUI.orfBox.checked = on; gApply(0.3, true); }));
  let nCit = 0;
  for (const l of G.links) if (!l.ex && !PJ_OFF.has(l.source.projeto) && !PJ_OFF.has(l.target.projeto)) nCit++;
  sec2.appendChild(tg('o:cit', GF.cit, 'Citações (ADR-NNN, caminhos em crase)', nCit,
    'Ligações que o Obsidian não desenha: "ADR-1234" no texto, caminho entre crases e os índices de memória. Desligadas, o mapa fica como o do Obsidian',
    on => { GF.cit = on; prefSet('vault-panel:citacoes', on ? 1 : 0); gApply(0.8, true); }));
  L.append(sec, sec2);
  if (fk){
    const el = [...L.querySelectorAll('[data-f]')].find(x => x.dataset.f === fk) || L.querySelector('.lgeye');
    if (el) el.focus({preventScroll:true});
  }
}
function gLegendRender(){
  if (!gUI || !gUI.legend) return;
  if (FOCO && GR && GR.universo){ cosLegend(); return; }
  const cnt = {}; G.nodes.forEach(n => { cnt[n.grp] = (cnt[n.grp] || 0) + 1; });
  gUI.legend.replaceChildren(...GGROUPS.map(g => h('span', {title: g.d || null}, h('span', {class:'sw round', style:'background:' + g.c}), g.l, ' ', h('b', null, nfmt(cnt[g.k] || 0)))),
    h('span', null, h('span', {class:'sw round ringk'}), 'em construção'),
    h('span', null, h('span', {class:'sw round hollowk'}), FOCO ? 'arquivado (estrela apagada)' : 'arquivado (contorno vazio)'));
  if (gRec) gUI.legend.appendChild(h('span', null, h('span', {class:'sw round', style:'background:var(--c-outros);opacity:.35'}), 'esmaecido = vizinho do recorte'));
}
function gStateRender(){
  if (!gUI){ if (active === 'grafo') renderFoco(); return; }
  const m = gUI.msg, quando = GR ? hhmm(GR.gerado_em) : '';
  m.replaceChildren();
  if (GR_EST === 'pendente' || GR_EST === 'recalculando'){
    m.hidden = false; m.append(h('span', {class:'ld'}), h('span', null, 'recalculando… mantendo o grafo de ' + quando));
  } else if (GR_EST === 'erro' || GR_EST === 'indisponivel'){
    m.hidden = false; m.append(warnIcon(), h('span', null, (GR_MSG || 'falha ao recalcular') + ' — mantendo o grafo de ' + quando));
  } else m.hidden = true;
  gTitleRender();
}
function hhmm(iso){ return iso ? br(iso.slice(0, 10)).slice(0, 5) + ' ' + iso.slice(11, 16) : '—'; }
function gTitleRender(){
  const M = GR.metricas;
  let nSpec = 0, nAux = 0; G.nodes.forEach(n => { if (n.tk === 'spec') nSpec++; else if (n.tk === 'spec_aux') nAux++; });
  gUI.title.replaceChildren(h('h2', null, 'Mapa do vault'),
    h('div', {class:'sub'}, 'Cor = grupo do doc; tamanho = ' + (GF.pr ? 'PageRank' : 'grau') + '. Grafo de ' + hhmm(GR.gerado_em) + ' · ' +
      plural(M.nos, 'nó', 'nós') + ' · ' + plural(M.arestas, 'aresta', 'arestas') + ' · ' + nfmt(M.contexto) + ' de contexto, ' +
      plural(nSpec, 'spec', 'specs') + (nAux ? ' (+' + nfmt(nAux) + ' templates e auxiliares de 01_Specs)' : '') + ', ' + nfmt(M.adrs) + ' ADRs.'));
}
function tipoOpts(){
  const c = {}; G.nodes.forEach(n => { c[n.tk] = (c[n.tk] || 0) + 1; });
  return [{v:'', l:'Todos os tipos'}].concat(Object.keys(c).sort((a, b) => c[b] - c[a]).map(k => ({v:k, l:(KIND_L[k] || k) + ' (' + nfmt(c[k]) + ')'})));
}
function areaOpts(){
  const c = {}; G.nodes.forEach(n => { c[n.area] = (c[n.area] || 0) + 1; });
  return [{v:'', l:'Todas as áreas'}].concat(Object.keys(c).sort().map(k => ({v:k, l:k + ' (' + nfmt(c[k]) + ')'})));
}
/* tudo que depende do modelo do grafo (chamado ao montar e a cada versão nova) */
function gFill(alpha){
  fillSelect(gUI.tipo, tipoOpts(), GF.tipo);
  fillSelect(gUI.area, areaOpts(), GF.area);
  gKpisRender(); gLegendRender(); gStateRender();
  gConjRender(); gRefsRender(); gPanelRender();
  gApply(alpha, false);
}
function gSearchPick(){
  if (!G) return;
  let best = null;
  G.nodes.forEach(n => { if (gBase[n.i] && gVis[n.i] && (!best || n.pagerank > best.pagerank)) best = n; });
  if (best) gSelect(best.id, {center:true});
}
function gEmptyRender(host){
  const msg = GR_EST === 'indisponivel' || GR_EST === 'erro' ? (GR_MSG || 'Grafo indisponível.')
    : GR_EST === 'ausente' ? 'Este retrato foi gerado sem o grafo (--no-graph). Rode "python3 vault_status.py" sem --no-graph, ou abra o painel ao vivo: ./vault-panel.sh open'
    : 'Recalculando o grafo… (a primeira montagem leva alguns segundos)';
  host.replaceChildren(h('div', {class:'card'}, h('h2', null, 'Grafo do vault'), h('p', {class:'empty'}, msg)));
}
/* o motor (renderGrafo) monta num contêiner oculto fora das abas: a aba Grafo adota só o mapa, os controles e o
   painel do nó (renderFoco); métricas, tabela e referências do grafo 2D ficam montadas ali, sem aparecer */
function gLegacyHost(){
  let el = document.getElementById('g-motor');
  if (!el){ el = h('div', {id:'g-motor', hidden:true}); document.body.appendChild(el); }
  return el;
}
function renderGrafo(){
  const host = gLegacyHost();
  if (!GR){ gEmptyRender(host); return; }
  if (!G) gBuild();
  if (!gUI){
    host.replaceChildren();
    gUI = {};
    gUI.kpis = h('div', {class:'kpis', role:'group', 'aria-label':'Métricas do grafo (clique para recortar o mapa e listar)'});
    host.appendChild(gUI.kpis);
    host.appendChild(h('details', {class:'method'},
      h('summary', null, 'O que entra no grafo e como ler'),
      h('ul', null,
        h('li', null, 'Nós: todos os .md do vault, fora raw/, _inbox/, assets/, .obsidian/ e .trash/ (e das subpastas em VAULT_PANEL_EXCLUDE) — ',
          'inclui 04_Anotações/, os .md soltos na raiz (CLAUDE.md, desenhos do Excalidraw) e os templates e subpastas de 01_Specs (em cinza, fora da contagem de specs) — ',
          'mais a memória do agente (~/.claude/…/memory, fora do vault).'),
        h('li', null, 'Arestas: [[wikilink]], [texto](caminho.md), `caminho.md` entre crases, "ADR-NNN" citado no texto e "- NNN" nos índices de memória.'),
        h('li', null, 'PageRank: o quanto o doc é apontado por docs que também são apontados — centralidade. Grau = citações recebidas (in) + links para outros (out).'),
        h('li', null, 'Mesmas regras de "python3 vault_graph.py" (relatório no terminal).'))));
    const filt = h('div', {class:'filters'});
    gUI.q = searchEl('Buscar doc (nome ou caminho)…', GF.q, v => { GF.q = v; gApply(0.3, true); });
    gUI.q.addEventListener('keydown', e => {       // Enter: aplica o texto já (sem esperar o debounce) e seleciona
      if (e.key !== 'Enter') return;
      e.preventDefault();
      if (GF.q !== gUI.q.value){ GF.q = gUI.q.value; gApply(0.3, true); }
      gSearchPick();
    });
    filt.appendChild(gUI.q);
    gUI.tipo = selectEl('Tipo de doc', [], GF.tipo, v => { GF.tipo = v; gApply(0.3, true); });
    gUI.area = selectEl('Área', [], GF.area, v => { GF.area = v; gApply(0.3, true); });
    filt.appendChild(gUI.tipo); filt.appendChild(gUI.area);
    const chk = (label, key, fn) => { const i = h('input', {type:'checkbox', onchange: e => { GF[key] = e.target.checked; fn(); }}); i.checked = GF[key]; return [h('label', {class:'chk'}, i, label), i]; };
    const [l1] = chk('Incluir vizinhos do recorte', 'viz', () => gApply(0.3, true));
    const [l2, i2] = chk('Incluir ADRs órfãos', 'orfaos', () => gApply(0.3, true));
    const [l3] = chk('Tamanho por PageRank', 'pr', () => { G.nodes.forEach(n => { n.r = gRadius(n); }); gTitleRender(); gKick(0.15); gDraw(); });
    gUI.orfBox = i2;
    filt.append(l1, l2, l3);
    gUI.count = h('span', {class:'count', 'aria-live':'polite'});
    filt.appendChild(gUI.count);
    host.appendChild(filt);
    const card = h('div', {class:'card'});
    gUI.card = card;
    gUI.title = h('div');
    gUI.tbtn = h('button', {type:'button', class:'btn', 'aria-expanded':'false'}, 'Ver como tabela');
    card.appendChild(h('div', {class:'chart-head'}, gUI.title, gUI.tbtn));
    gUI.legend = h('div', {class:'legend'});
    card.appendChild(gUI.legend);
    const lay = h('div', {class:'glayout'});
    gUI.wrap = h('div', {class:'gwrap'});
    gUI.canvas = h('canvas', {role:'img', 'aria-label':'Mapa de força do vault: cada nó é um doc e cada aresta um link. "Ver como tabela" e as listas abaixo trazem os mesmos dados.'});
    gUI.msg = h('div', {class:'gmsg', hidden:true, role:'status'});
    gUI.hint = h('div', {class:'ghint', 'aria-hidden':'true'}, GTOUCH ? 'Use dois dedos para mover o mapa' : 'Ctrl + rolagem (ou pinça) para dar zoom');
    const tools = h('div', {class:'gtools'},
      h('button', {type:'button', class:'btn', title:'Aproximar', 'aria-label':'Aproximar', onclick: () => gZoomBy(1.4)}, ico('plus')),
      h('button', {type:'button', class:'btn', title:'Afastar', 'aria-label':'Afastar', onclick: () => gZoomBy(1 / 1.4)}, ico('minus')),
      h('button', {type:'button', class:'btn', onclick: gFit}, ico('scan'), 'Enquadrar'),
      h('button', {type:'button', class:'btn', title:'Solta as forças de novo', onclick: () => gKick(0.6)}, ico('shuffle'), 'Reorganizar'));
    const slRow = (label, title, min, max, val, onchange, step, fmt) => {
      fmt = fmt || (v => v + '%');
      const out = h('output', {class:'gfval'}, fmt(val));
      const inp = h('input', {type:'range', min:String(min), max:String(max), step:String(step || 1), value:String(val), 'aria-label':label,
        'aria-valuetext': fmt(val)});
      inp.addEventListener('input', () => {
        const v = +inp.value; out.textContent = fmt(v); inp.setAttribute('aria-valuetext', fmt(v)); onchange(v);
      });
      const row = h('label', {class:'gfrow', title:title}, h('span', null, label), inp, out);
      row._set = v => { inp.value = String(v); out.textContent = fmt(v); inp.setAttribute('aria-valuetext', fmt(v)); };
      return row;
    };
    const linkKick = debounce(() => {                       // força/distância dos links: reacomoda e reenquadra
      if (!gSim) return;
      gSim.force('link').distance(GF.ld).strength(linkStr);
      gSim.force('charge').strength(-GF.rep * REP_K);
      gSim.force('x').strength(GF.cent * CEN_K); gSim.force('y').strength(GF.cent * CEN_K);
      if (FOCO){ COS.n = 0; cosRequest(); }
      gKick(0.5);           // sem gAutoFit: o reenquadramento devolvia o grafo ao mesmo tamanho e a mudança sumia
    }, 120);
    const fisSave = (k, v) => { try { localStorage.setItem(FIS_K[k], String(v)); } catch (e) {} };
    const num = d => v => v.toFixed(d).replace('.', ',');
    const rCen = slRow('Força central', 'Puxa tudo para o centro: contra a repulsão, forma o disco de densidade uniforme do Obsidian', 0, 1, GF.cent,
      v => { GF.cent = v; fisSave('cent', v); linkKick(); }, 0.01, num(2));
    const rLf = slRow('Força dos links', 'Quanto cada ligação puxa os dois docs um para o outro (0 = solta)', 0, 1, GF.lf,
      v => { GF.lf = v; fisSave('lf', v); linkKick(); }, 0.01, num(2));
    const rLd = slRow('Distância dos links', 'Comprimento de repouso de cada ligação', 30, 500, GF.ld,
      v => { GF.ld = v; fisSave('ld', v); linkKick(); }, 1, num(0));
    const rRep = slRow('Força de repulsão', 'Quanto cada doc empurra os outros: alta espalha o mapa por igual e forma os cachos em volta dos hubs', 0, 20, GF.rep,
      v => { GF.rep = v; fisSave('rep', v); linkKick(); }, 0.5, num(1));
    gUI.force = h('div', {class:'gforce', role:'group', 'aria-label':'Ajustes do mapa'},
      rCen, rLf, rLd, rRep,
      FOCO ? slRow('Luminosidade', 'Brilho das estrelas, dos filamentos e do fundo', 20, 200, Math.round(LUZ * 100),
        v => { LUZ = v / 100; prefSet('vault-panel:luz', v); cosRequest(); }) : null,
      FOCO ? slRow('Movimento', 'Velocidade da rotação, da respiração e da cintilação (0 % = parado)', 0, 200, Math.round(MOV * 100),
        v => { MOV = v / 100; prefSet('vault-panel:mov', v); cosRequest(); }) : null,
      h('button', {type:'button', class:'btn gfreset', title:'Volta as quatro forças aos valores do grafo do Obsidian',
        onclick: () => {
          Object.assign(GF, FIS_PADRAO);
          ['cent', 'lf', 'ld', 'rep'].forEach(k => fisSave(k, FIS_PADRAO[k]));
          rCen._set(GF.cent); rLf._set(GF.lf); rLd._set(GF.ld); rRep._set(GF.rep);
          linkKick();
        }}, ico('rotate-ccw'), 'Padrão'));
    gUI.wrap.append(gUI.canvas, gUI.msg, gUI.hint, tools, gUI.force);
    if (!HAS_D3) gUI.wrap.replaceChildren(noD3('As métricas, a tabela e as listas continuam válidas.'));
    gUI.panel = h('aside', {class:'gpanel', 'aria-label':'Detalhe do nó selecionado'});
    lay.append(gUI.wrap, gUI.panel);
    card.appendChild(lay);
    gUI.table = h('div', {hidden:true, style:'margin-top:var(--spacing-md)'});
    gUI.tbtn.addEventListener('click', () => { const open = gUI.table.hidden; gUI.table.hidden = !open; gUI.tbtn.setAttribute('aria-expanded', String(open)); gUI.tbtn.textContent = open ? 'Ocultar tabela' : 'Ver como tabela'; gTableRender(); });
    card.appendChild(gUI.table);
    host.appendChild(card);
    gUI.conjCard = h('div', {class:'card', hidden:true});
    host.appendChild(gUI.conjCard);
    const rc = h('div', {class:'card'});
    gUI.refCard = rc;
    rc.appendChild(h('div', {class:'chart-head'}, h('div', null, h('h2', null, 'Referências não resolvidas'),
      h('div', {class:'sub'}, 'Links e caminhos que não viram doc do vault: mistura link quebrado real com referência a arquivo do repo ou de outro vault — confira os que deviam ser docs daqui.'))));
    const rf = h('div', {class:'filters', style:'margin:var(--spacing-sm) 0'});
    rf.appendChild(searchEl('Filtrar por origem ou alvo…', GF.rq, v => { GF.rq = v; GF.todosR = false; gRefsRender(); }));
    gUI.refCount = h('span', {class:'count'});
    rf.appendChild(gUI.refCount);
    rc.appendChild(rf);
    gUI.refBody = h('div');
    rc.appendChild(gUI.refBody);
    host.appendChild(rc);
    if (HAS_D3) gCanvasInit(); else { gCv = null; }
    gFill(1);
  } else gPanelRender();     // o botão "Ver andamento da spec" depende do status, que pode ter mudado com a aba oculta
  gResume();
}
function applyGraph(ng){
  const sy = PANEL.scrollTop, prevSig = G ? G.sig : null;
  GR = grafoDaTela(ng);
  gBuild();
  if (gUI) gFill(G.sig === prevSig ? 0 : 0.12);    // só métricas mudaram: redesenha sem mexer nas posições
  else if (active === 'grafo') renderFoco();        // fora da aba: monta quando ela abrir (o tamanho depende dela)
  PANEL.scrollTop = sy;
}

/* ════════════════ universo (página única): estrelas em 3D, rotação lenta, respiração ════════════════ */
/* o layout x,y vem da mesma simulação de força; z nasce de um hash do id suavizado pelos vizinhos (aglomerados
   em profundidade). A câmera gira devagar (1 volta a cada 5 min), inclina, e o todo respira — sem rótulos. */
/* cor das estrelas = cor do PROJETO, escolhida na própria legenda (a bolinha de cada projeto no painel lateral).
   Padrão: os 8 maiores projetos na ordem categórica validada (≥ 3:1 no céu, separação para daltonismo); do 9º em diante,
   cinza neutro até alguém escolher — não há 9ª cor distinguível. A cor segue o projeto, nunca a posição na lista: ocultar
   um não repinta os outros. Cores escolhidas e projetos ocultos ficam salvos neste navegador (localStorage). */
const PC_KEY = 'vault-panel:cores-dos-projetos', PJ_KEY = 'vault-panel:projetos-ocultos';
const PC_PALETA = ['#3987e5', '#d95926', '#199e70', '#c98500', '#d55181', '#008300', '#9085e9', '#e66767'];
const PC_NEUTRO = '#b9ad9f';
let PC = pcLoad(), pcPadraoCache = null, pcSaveT = null;
let PJ_OFF = new Set(pjLoad());
try { ['vault-panel:grupos-de-cor', 'vault-panel:grupos-ocultos', 'vault-panel:cor'].forEach(k => localStorage.removeItem(k)); } catch (e) {}
function pcCor(c){ return /^#[0-9a-f]{6}$/i.test(c || '') ? c.toLowerCase() : null; }
function pcLoad(){
  try {
    const o = JSON.parse(localStorage.getItem(PC_KEY) || '{}'), r = {};
    if (o && typeof o === 'object') for (const k in o){ const c = pcCor(o[k]); if (c) r[String(k)] = c; }
    return r;
  } catch (e) { return {}; }
}
function pcSaveSoon(){ clearTimeout(pcSaveT); pcSaveT = setTimeout(() => { try { localStorage.setItem(PC_KEY, JSON.stringify(PC)); } catch (e) {} }, 300); }
function pjLoad(){ try { const a = JSON.parse(localStorage.getItem(PJ_KEY) || '[]'); return Array.isArray(a) ? a.map(String) : []; } catch (e) { return []; } }
function pjSave(){ try { localStorage.setItem(PJ_KEY, JSON.stringify([...PJ_OFF])); } catch (e) {} }
function pjNome(p){ return p === '(raiz)' ? 'raiz do vault' : p === 'memoria-agente' ? 'memória do agente' : p; }
function pjLista(){
  const c = new Map();
  if (G) G.nodes.forEach(n => { if (n.projeto) c.set(n.projeto, (c.get(n.projeto) || 0) + (n.tipo === 'anexo' ? 1e-6 : 1)); });
  return [...c.entries()].sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0], 'pt-BR')).map(([p, n]) => ({p, n: Math.round(n)}));
}
function pjToggle(p, on){ if (on) PJ_OFF.delete(p); else PJ_OFF.add(p); pjSave(); gApply(0.3, true); }
function pjTodos(){ PJ_OFF.clear(); pjSave(); gApply(0.3, true); }
function pcPadrao(p){
  if (!pcPadraoCache){ pcPadraoCache = new Map(); pjLista().forEach((x, k) => pcPadraoCache.set(x.p, PC_PALETA[k] || PC_NEUTRO)); }
  return pcPadraoCache.get(p) || PC_NEUTRO;
}
function pjCor(p){ return PC[p] || pcPadrao(p); }
/* troca de cor: repinta as estrelas sem redesenhar a legenda (o seletor de cor aberto fecharia) */
function pcMudou(){ if (G) G.nodes.forEach(n => { n._c = null; }); pcSaveSoon(); gPanelRender(); cosRequest(); }
function pcTrocar(p, c){ c = pcCor(c); if (!c) return; if (c === pcPadrao(p)) delete PC[p]; else PC[p] = c; pcMudou(); }
function pcRestaurar(){ PC = {}; pcMudou(); gLegendRender(); }
function cosCor(n){ return cosVis(cosCorBase(n)); }
function cosCorBase(n){
  if (GR && GR.universo) return pjCor(n.projeto);
  const P = cosPalette(); return P.grp[n.grp] || P.grp.mem;
}
/* mistura com branco (t = 0..1) */
function cosTint(hex, t){
  const [r, g, b] = cosRgb(hex), to = x => Math.round(x + (255 - x) * t).toString(16).padStart(2, '0');
  return '#' + to(r) + to(g) + to(b);
}
/* cor legível no espaço: clareia as muito escuras (um azul-marinho escolhido para um projeto, por exemplo) */
const VIS_CACHE = new Map();
function cosVis(hex){
  let v = VIS_CACHE.get(hex);
  if (v) return v;
  const [r, g, b] = cosRgb(hex), L = (0.2126 * r + 0.7152 * g + 0.0722 * b) / 255;
  v = L >= 0.42 ? hex : cosTint(hex, Math.min(0.6, (0.42 - L) / (1 - L) + 0.08));
  VIS_CACHE.set(hex, v);
  return v;
}
function cosSprite(hex){
  let spr = COS.spr.get(hex);
  if (spr) return spr;
  const [r, g, b] = cosRgb(hex), S = 64, cv = document.createElement('canvas');
  cv.width = cv.height = S;
  const c = cv.getContext('2d'), gr = c.createRadialGradient(S / 2, S / 2, 0, S / 2, S / 2, S / 2);
  const [cr, cg, cb] = cosRgb(cosTint(hex, 0.55));
  gr.addColorStop(0, 'rgba(' + cr + ',' + cg + ',' + cb + ',1)');        // centro: a cor clareada (não branco)
  gr.addColorStop(0.14, 'rgba(' + r + ',' + g + ',' + b + ',0.95)');
  gr.addColorStop(0.34, 'rgba(' + r + ',' + g + ',' + b + ',0.4)');
  gr.addColorStop(0.62, 'rgba(' + r + ',' + g + ',' + b + ',0.09)');
  gr.addColorStop(1, 'rgba(' + r + ',' + g + ',' + b + ',0)');
  c.fillStyle = gr; c.fillRect(0, 0, S, S);
  COS.spr.set(hex, cv);
  return cv;
}
const COS = {spr: new Map(), tv: 0, lastNow: 0, t0: performance.now(), last: 0, dirty: true, raf: 0, n: 0, R: 300, cx: 0, cy: 0, ms: 12,
             sky: null, skyKey: '', pal: null, order: [], orderSrc: null, th: 0};
function cosHash(str, salt){
  let h = 2166136261 ^ (salt || 0);
  for (let i = 0; i < str.length; i++){ h ^= str.charCodeAt(i); h = Math.imul(h, 16777619); }
  h ^= h >>> 13; h = Math.imul(h, 0x5bd1e995); h ^= h >>> 15;
  return (h >>> 0) / 4294967296;
}
function cosDepth(){
  const N = G.nodes.length, z = new Float64Array(N), nz = new Float64Array(N);
  G.nodes.forEach(n => { z[n.i] = cosHash(n.id, 7) * 2 - 1; });
  for (let it = 0; it < 6; it++){
    G.nodes.forEach(n => {
      const a = G.adj[n.i]; let sm = 0, c = 0;
      a.forEach(j => { sm += z[j]; c++; });
      nz[n.i] = c ? 0.45 * z[n.i] + 0.55 * sm / c : z[n.i];
    });
    z.set(nz);
  }
  let m = 0, v = 0;
  for (let i = 0; i < N; i++) m += z[i];
  m /= N || 1;
  for (let i = 0; i < N; i++) v += (z[i] - m) * (z[i] - m);
  const sd = Math.sqrt(v / (N || 1)) || 1;
  G.nodes.forEach(n => {
    n.z3 = Math.max(-1.7, Math.min(1.7, (z[n.i] - m) / sd * 0.6));
    const u = cosHash(n.id, 31), w = cosHash(n.id, 57);
    n.cw = {p: u * 6.2832, f1: 0.05 + 0.05 * w, f2: 0.04 + 0.05 * u, f3: 0.6 + 1.2 * w, amp: 2 + 5 * u};
  });
}
function cosRgb(c){
  const m = /^#?([0-9a-f]{6})$/i.exec((c || '').trim());
  if (!m) return [200, 210, 255];
  const x = parseInt(m[1], 16);
  return [x >> 16 & 255, x >> 8 & 255, x & 255];
}
function cosPalette(){
  if (COS.pal) return COS.pal;
  const cs = getComputedStyle(fUI && fUI.map ? fUI.map : document.documentElement), v = k => cs.getPropertyValue(k).trim();
  const P = {grp: {ctx: v('--star-ctx'), spec: v('--star-spec'), adr: v('--star-adr'), mem: v('--star-mem')},
             fil: v('--filament') || '#8fa8ff', warn: v('--warn') || '#ffb65c', core: v('--star-core') || '#ffffff',
             sp0: v('--space-0') || '#010205', sp1: v('--space-1') || '#070b17'};
  P.rgb = {}; for (const k in P.grp) P.rgb[k] = cosRgb(P.grp[k]);
  COS.pal = P;   /* o brilho de cada estrela vem de cosSprite(cor), criado sob demanda */
  return P;
}
function cosSky(){
  const key = gCv.width + 'x' + gCv.height;
  if (COS.sky && COS.skyKey === key) return COS.sky;
  const P = cosPalette(), W = gCv.width, H = gCv.height, cv = document.createElement('canvas');
  cv.width = W; cv.height = H;
  /* céu neutro, sem nuvens de cor: degradê + vinheta pintados numa tela 8× MENOR, desfocados e ampliados com
     suavização (o desfoque apaga o pontilhado que o Chrome põe em cada degradê) */
  const F = 8, w = Math.max(8, Math.ceil(W / F)), hh = Math.max(8, Math.ceil(H / F)), S = Math.min(w, hh);
  const lo = document.createElement('canvas');
  lo.width = w; lo.height = hh;
  const c = lo.getContext('2d');
  const bg = c.createRadialGradient(w * 0.5, hh * 0.45, 0, w * 0.5, hh * 0.5, Math.hypot(w, hh) * 0.65);
  bg.addColorStop(0, P.sp1); bg.addColorStop(1, P.sp0);
  c.fillStyle = bg; c.fillRect(0, 0, w, hh);
  const [dR, dG, dB] = cosRgb(P.sp0);
  const vg = c.createRadialGradient(w / 2, hh / 2, S * 0.35, w / 2, hh / 2, Math.hypot(w, hh) * 0.62);
  vg.addColorStop(0, 'rgba(' + dR + ',' + dG + ',' + dB + ',0)'); vg.addColorStop(1, 'rgba(' + dR + ',' + dG + ',' + dB + ',0.5)');
  c.fillStyle = vg; c.fillRect(0, 0, w, hh);
  const lo2 = document.createElement('canvas');
  lo2.width = w; lo2.height = hh;
  const c2 = lo2.getContext('2d');
  c2.filter = 'blur(3px)';
  c2.drawImage(lo, 0, 0);
  const o = cv.getContext('2d');
  o.imageSmoothingEnabled = true; o.imageSmoothingQuality = 'high';
  o.drawImage(lo2, 0, 0, w, hh, 0, 0, W, H);
  COS.sky = cv; COS.skyKey = key;
  return cv;
}
function cosStats(){
  let sx = 0, sy = 0, c = 0;
  for (const n of gVN){ if (n.x == null || n.orf) continue; sx += n.x; sy += n.y; c++; }
  if (!c) return;
  const cx = sx / c, cy = sy / c;
  let v = 0;
  const d2 = [];
  for (const n of gVN){
    if (n.x == null || n.orf) continue;
    const e = (n.x - cx) * (n.x - cx) + (n.y - cy) * (n.y - cy);
    v += e; d2.push(e);
  }
  d2.sort((a, b) => a - b);
  COS.cx = cx; COS.cy = cy; COS.R = Math.max(60, Math.sqrt(v / c));
  COS.R98 = Math.sqrt(d2[Math.floor((d2.length - 1) * 0.95)] || 0);   // borda do núcleo, 95 % (os satélites distantes não empurram o anel)
}
function cosRequest(){ COS.dirty = true; if (!COS.raf) COS.raf = requestAnimationFrame(cosFrame); }
function cosMoving(){ return !RM && !document.hidden && MOV > 0 && active === 'grafo'; }
function cosFrame(now){
  COS.raf = 0;
  if (!gUI || !gCtx || !G || !gTf || !gW) return;
  const moving = cosMoving(), every = COS.ms > 26 ? 50 : 33;     // ~30 fps; máquina lenta cai para ~20
  if (moving && !COS.dirty && now - COS.last < every){ COS.raf = requestAnimationFrame(cosFrame); return; }
  const dt = COS.lastNow ? Math.min(0.25, (now - COS.lastNow) / 1000) : 0;   // aba volta do fundo: sem salto
  COS.lastNow = now;
  if (moving) COS.tv += dt * MOV;
  COS.last = now; COS.dirty = false;
  const a = performance.now();
  cosRender(COS.tv);
  COS.ms = COS.ms * 0.9 + (performance.now() - a) * 0.1;
  if (moving) COS.raf = requestAnimationFrame(cosFrame);
}
document.addEventListener('visibilitychange', () => { if (active === 'grafo' && !document.hidden) cosRequest(); });
function cosRender(t){
  const ctx = gCtx, P = cosPalette(), k = gTf.k, dpr = gDpr;
  if (!(COS.n++ % 20)) cosStats();
  const R = COS.R, cx = COS.cx, cy = COS.cy, TAU = 6.2832;
  /* movimento: giro NO PLANO DA TELA (galáxia vista de cima, 1 volta a cada 5 min) + BALANÇO 3D LIMITADO — inclina até
     ±26° para os lados e ±17° para cima/baixo, em ciclos lentos e diferentes. A física é 2D (como a do Obsidian): o giro
     completo em torno do eixo vertical punha o disco de lado e as formações viravam retas; o balanço nunca chega lá */
  const th = t * TAU / 300, yaw = 0.45 * Math.sin(t * TAU / 170), pitch = 0.30 * Math.sin(t * TAU / 240 + 1.3);
  COS.th = th;
  const ct = Math.cos(th), st = Math.sin(th), cyw = Math.cos(yaw), syw = Math.sin(yaw), cpt = Math.cos(pitch), spt = Math.sin(pitch);
  const breathe = 1 + 0.024 * Math.sin(t * TAU / 9);
  const depth = R * 0.95, D = R * 3.2;
  /* anel dos órfãos: logo além da borda do núcleo */
  const Rcore = COS.R98 || R * 2.2;
  const Rh = COS.Rh = Rcore * 1.12 + 16;   // anel logo além da borda, como no Obsidian
  for (const n of gVN){
    if (n.x == null) continue;
    const w = n.cw || (n.cw = {p: 0, f1: 0.07, f2: 0.06, f3: 1, amp: 3});
    if (n.orf){
      /* órbita: ângulo e espessura estáveis por doc; 1 volta a cada ~10 min (no Movimento 100 %), velocidades
         um pouco diferentes — o anel "escorre" em vez de girar como peça rígida */
      const o = n.ob || (n.ob = {a: cosHash(n.id, 71) * TAU, r: 1 + (cosHash(n.id, 72) - 0.5) * 0.16, w: 0.85 + 0.3 * cosHash(n.id, 73)});
      const ang = o.a + t * TAU / 600 * o.w, rr = Rh * o.r * breathe;
      n.sx = cx + Math.cos(ang) * rr; n.sy = cy + Math.sin(ang) * rr; n.sf = 1; n.sz = 0;
      n.px = gTf.x + n.sx * k; n.py = gTf.y + n.sy * k;
      n.pr = Math.max(1.1, n.r * k * 0.5);      // anexo/órfão tem PageRank ~0: sem piso o anel some
      n.tw = 0.8 + 0.2 * Math.sin(t * w.f3 + w.p * 2.1);
      continue;
    }
    let ox = n.x - cx, oy = n.y - cy, oz = (n.z3 || 0) * depth;
    const dx = ox * breathe + w.amp * Math.sin(t * w.f1 + w.p);
    const dy = oy * breathe + w.amp * Math.cos(t * w.f2 + w.p * 1.3);
    const dz = oz * breathe;
    const x1 = dx * ct - dy * st, y1 = dx * st + dy * ct;           // giro no plano
    const x2 = x1 * cyw + dz * syw, z2 = -x1 * syw + dz * cyw;      // balanço lateral (limitado)
    const y3 = y1 * cpt - z2 * spt, z3 = y1 * spt + z2 * cpt;       // balanço vertical (limitado)
    const f = Math.max(0.6, Math.min(1.6, D / (D - z3)));
    n.sx = cx + x2 * f; n.sy = cy + y3 * f; n.sf = f; n.sz = z3;
    n.px = gTf.x + n.sx * k; n.py = gTf.y + n.sy * k;
    n.pr = Math.max(0.95, n.r * f * k * 0.62);   // ponto visível no zoom de enquadrar (antes sumia sob as linhas)
    n.tw = 0.8 + 0.2 * Math.sin(t * w.f3 + w.p * 2.1);
  }
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.clearRect(0, 0, gCv.width, gCv.height);
  ctx.globalCompositeOperation = 'source-over';
  /* fundo: estrelas distantes com paralaxe lenta (andam ~1/4 da tela por volta) */
  ctx.globalAlpha = Math.min(1, 0.45 + 0.55 * LUZ);
  ctx.drawImage(cosSky(), 0, 0);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  const selN = gSel ? G.byId.get(gSel) : null;
  let focus = gHover || (gSelDim ? selN : null);
  if (focus && (!gVis[focus.i] || focus.px == null)) focus = null;
  const nb = focus ? G.adj[focus.i] : null;
  /* filamentos: 3 faixas de profundidade (longe = mais tênue); linha abaixo de 1 px de dispositivo (caminho rápido) */
  /* filamentos na cor da estrela de ORIGEM (cada região fica tingida pelo seu projeto/área, como no grafo
     nativo), agrupados por (cor, faixa de profundidade): poucas dezenas de strokes por quadro */
  ctx.lineWidth = Math.min(0.7, 0.9 / dpr);
  /* milhares de ligações somam brilho: a linha fica mais tênue quanto mais ligações na tela (como no Obsidian) */
  const lm = Math.max(0.4, Math.min(1, 9000 / Math.max(1, gVL.length)));
  const BANDA = focus ? [0.025, 0.035, 0.05] : [0.05 * lm, 0.09 * lm, 0.16 * lm];
  const paths = new Map();
  for (const l of gVL){
    const A = l.source, B = l.target;
    if (A.px == null || B.px == null) continue;
    if (focus && (A === focus || B === focus)) continue;
    const fz = (A.sf + B.sf) * 0.5, bb = fz < 0.93 ? 0 : fz < 1.08 ? 1 : 2;
    const key = (A._c || (A._c = cosCor(A))) + bb;
    let pth = paths.get(key);
    if (!pth){ pth = new Path2D(); paths.set(key, pth); }
    pth.moveTo(A.px, A.py); pth.lineTo(B.px, B.py);
  }
  paths.forEach((pth, key) => {
    ctx.globalAlpha = Math.min(1, BANDA[+key.slice(-1)] * LUZ);
    ctx.strokeStyle = key.slice(0, -1);
    ctx.stroke(pth);
  });
  ctx.globalCompositeOperation = 'lighter';
  if (focus){
    const fc = focus._c || (focus._c = cosCor(focus));
    ctx.lineWidth = 1.1; ctx.strokeStyle = fc; ctx.globalAlpha = Math.min(1, 0.55 * LUZ);
    ctx.beginPath();
    for (const l of gVL){
      if (l.source !== focus && l.target !== focus) continue;
      ctx.moveTo(l.source.px, l.source.py); ctx.lineTo(l.target.px, l.target.py);
    }
    ctx.stroke();
    /* pulsos de luz percorrendo as conexões do foco (saem da estrela em foco) */
    ctx.fillStyle = P.core;
    for (const l of gVL){
      if (l.source !== focus && l.target !== focus) continue;
      const o = l.source === focus ? l.target : l.source;
      const u = (t * 0.28 + cosHash(o.id, 3)) % 1;
      const x = focus.px + (o.px - focus.px) * u, y = focus.py + (o.py - focus.py) * u;
      ctx.globalAlpha = Math.min(1, 0.85 * Math.sin(u * Math.PI) * Math.max(0.6, LUZ));
      ctx.beginPath(); ctx.arc(x, y, 1.6, 0, TAU); ctx.fill();
    }
  }
  /* estrelas: de trás para frente */
  if (COS.orderSrc !== gVN){ COS.order = gVN.slice(); COS.orderSrc = gVN; }   // gApply troca o array quando o recorte muda
  const order = COS.order;
  order.sort((p, q) => (p.sz || 0) - (q.sz || 0));
  for (const n of order){
    if (n.px == null || !gVis[n.i]) continue;
    if (n.px < -40 || n.py < -40 || n.px > gW + 40 || n.py > gH + 40) continue;
    const dim = focus && n !== focus && !nb.has(n.i) ? 0.12 : (!focus && gRec && !gBase[n.i]) ? 0.3 : 1;
    const near = Math.max(0.22, Math.min(1, 0.25 + 0.75 * (n.sf - 0.6) / 1.0));
    let a = near * n.tw * dim * (n.arquivado ? 0.35 : 1) * LUZ;
    const spr = cosSprite(n._c || (n._c = cosCor(n))), g = n.pr * 5.2 * (0.8 + 0.2 * LUZ);   // mais luz = halo maior
    ctx.globalAlpha = Math.min(1, a);
    ctx.drawImage(spr, n.px - g / 2, n.py - g / 2, g, g);
    if (n.pr > 2.4 && !n.arquivado){
      ctx.globalAlpha = Math.min(1, a * 0.8);
      ctx.fillStyle = cosTint(n._c, 0.6);
      ctx.beginPath(); ctx.arc(n.px, n.py, n.pr * 0.3, 0, TAU); ctx.fill();
    }
    if (n.working && dim === 1){      // em construção: anel tênue
      ctx.globalAlpha = 0.32 * near;
      ctx.strokeStyle = P.warn; ctx.lineWidth = 0.8;
      ctx.beginPath(); ctx.arc(n.px, n.py, n.pr + 2.5, 0, TAU); ctx.stroke();
    }
  }
  ctx.globalCompositeOperation = 'source-over';
  if (selN && gVis[selN.i] && selN.px != null){
    const pul = 0.5 + 0.5 * Math.sin(t * 2.4);
    ctx.globalAlpha = 0.55 + 0.35 * pul;
    ctx.strokeStyle = P.core; ctx.lineWidth = 1.4;
    ctx.beginPath(); ctx.arc(selN.px, selN.py, selN.pr + 6 + 3 * pul, 0, TAU); ctx.stroke();
  }
  ctx.globalAlpha = 1;
}
function cosPick(ev){
  if (!gCv) return null;
  const src = ev.touches ? (ev.touches[0] || ev.changedTouches[0]) : ev;
  if (!src || typeof d3 === 'undefined') return null;
  const m = d3.pointer(src, gCv), mx = m[0], my = m[1];
  let best = null, bd = Infinity;
  for (const n of gVN){
    if (n.px == null || !gVis[n.i]) continue;
    const dx = n.px - mx, dy = n.py - my, d2 = dx * dx + dy * dy, rr = Math.max(n.pr * 1.6 + 2, 7);
    if (d2 > rr * rr) continue;
    if (!best || d2 < bd - 4 || (Math.abs(d2 - bd) <= 4 && n.sz > best.sz)){ best = n; bd = d2; }
  }
  return best;
}
function cosCenter(n){
  if (!gZoom || !gW || n.sx == null) return;
  gAutoFit = false;
  const k = Math.max(gTf.k, 0.9);
  const t = d3.zoomIdentity.translate(gW / 2 - n.sx * k, gH / 2 - n.sy * k).scale(k);
  d3.select(gCv).transition().duration(RM ? 0 : 600).call(gZoom.transform, t);
}
function cosFit(){
  if (!gZoom || !gVN.length || !gW) return;
  const pts = gVN.filter(n => n.x != null);
  if (!pts.length) return;
  const X = n => n.sx != null ? n.sx : n.x, Y = n => n.sy != null ? n.sy : n.y;
  const q = (arr, p) => arr[Math.max(0, Math.min(arr.length - 1, Math.round(p * (arr.length - 1))))];
  const xs = pts.map(X).sort((a, b) => a - b), ys = pts.map(Y).sort((a, b) => a - b);
  let x0 = q(xs, 0.02), x1 = q(xs, 0.98), y0 = q(ys, 0.02), y1 = q(ys, 0.98);
  if (COS.Rh && pts.some(n => n.orf)){         // o anel dos órfãos entra inteiro no quadro
    const e = COS.Rh * 1.1;
    x0 = Math.min(x0, COS.cx - e); x1 = Math.max(x1, COS.cx + e); y0 = Math.min(y0, COS.cy - e); y1 = Math.max(y1, COS.cy + e);
  }
  const pad = 60, w = Math.max(40, x1 - x0), hh = Math.max(40, y1 - y0);
  const k = Math.max(0.05, Math.min(2, Math.min((gW - 2 * pad) / w, (gH - 2 * pad) / hh)));
  const t = d3.zoomIdentity.translate(gW / 2 - (x0 + x1) / 2 * k, gH / 2 - (y0 + y1) / 2 * k).scale(k);
  d3.select(gCv).transition().duration(RM ? 0 : 500).call(gZoom.transform, t);
}

/* ════════════════ aba Grafo (universo + legenda lateral) e página Specs (abertas por etapa) ════════════════ */
/* a aba Grafo monta o motor no #p-grafo (oculto) e a página única adota só o mapa e o painel do nó:
   um código de grafo só, com as mesmas atualizações ao vivo */
const FC = {q:''};
/* kanban da página Specs, na ordem do fluxo; estudos, guias e "sem status" não são etapa: ficam fora (contados) */
const SA = {arq: (() => { try { return localStorage.getItem('vault-panel:kanban-arquivadas') === '1'; } catch (e) { return false; } })()};
const F_GROUPS = [
  {k:'nao', st:'rascunho', l:'Não iniciadas', um:'não iniciada', varios:'não iniciadas', f:s => !s.arquivada && (s.status === 'rascunho' || s.status === 'aprovada')},
  {k:'dev', st:'em-desenvolvimento', l:'Em desenvolvimento', um:'em desenvolvimento', varios:'em desenvolvimento', f:s => !s.arquivada && s.status === 'em-desenvolvimento'},
  {k:'fim', st:'implementada', l:'Finalizadas', um:'finalizada', varios:'finalizadas', f:s => s.arquivada ? SA.arq : s.status === 'implementada'}];
let fUI = null;
function renderFoco(){
  if (!fUI){
    const col = h('aside', {class:'fcol', 'aria-label':'Legenda do mapa'});
    const head = h('div', {class:'fhead'}, h('h1', null, 'Grafo do vault'));
    fUI = {col:col, head:head, sub:h('p', {class:'fsub'}), leg:h('div', {class:'lg'}), map:h('div', {class:'fmap'})};
    col.append(head, fUI.sub, fUI.leg);
    document.getElementById('p-grafo').replaceChildren(h('div', {id:'foco'}, col, fUI.map));
  }
  placeLive();
  if (!GR){ fUI.sub.textContent = ''; fUI.leg.replaceChildren(h('p', {class:'empty'}, 'A legenda aparece quando o grafo terminar de montar.')); }
  fGraphInit();
}
function fGraphInit(){
  if (!GR){ gEmptyRender(fUI.map); return; }
  if (!gUI){
    /* o motor monta no contêiner oculto (tamanho 0): parte do tamanho da área do mapa para o zoom inicial */
    const r = fUI.map.getBoundingClientRect();
    gW = r.width; gH = r.height; gDpr = window.devicePixelRatio || 1;
    if (!gTf && HAS_D3) gTf = d3.zoomIdentity.translate(gW / 2, gH / 2).scale(0.35);
    renderGrafo();
    if (!gUI) return;
  }
  if (gUI.wrap.parentNode !== fUI.map) fUI.map.replaceChildren(gUI.wrap, gUI.panel);
  gSize(); gPanelRender(); gLegendRender(); gDraw();
}
function fPassa(s){
  if (!FC.q) return true;
  const q = fold(FC.q);
  return fold(s.titulo).indexOf(q) >= 0 || fold(s.slug).indexOf(q) >= 0;
}
let saUI = null;
function renderAbertas(){
  const host = document.getElementById('v-kanban');
  if (!saUI){
    host.replaceChildren();
    const arq = h('input', {type:'checkbox', onchange: e => {
      SA.arq = e.target.checked;
      try { localStorage.setItem('vault-panel:kanban-arquivadas', SA.arq ? '1' : '0'); } catch (err) {}
      saRender();
    }});
    arq.checked = SA.arq;
    saUI = {count: h('span', {class:'count', 'aria-live':'polite'}), board: h('div', {class:'saboard'})};
    host.append(h('div', {class:'filters'}, searchEl('Filtrar specs…', FC.q, v => { FC.q = v; saRender(); }),
        h('label', {class:'chk'}, arq, 'Incluir arquivadas em Finalizadas'), saUI.count),
      saUI.board,
      h('p', {class:'caption'}, 'Clique numa spec para ver o andamento; o botão ', ico('orbit'), ' leva até ela no grafo.'));
  }
  saRender();
}
function saRender(){
  if (!saUI) return;
  const ord = (a, b) => pctOf(b) - pctOf(a) || (a.dias_parada || 0) - (b.dias_parada || 0) || a.titulo.localeCompare(b.titulo, 'pt-BR');
  const recente = (a, b) => String(b.arquivado_em || b.ultima_atividade || '').localeCompare(String(a.arquivado_em || a.ultima_atividade || '')) ||
    a.titulo.localeCompare(b.titulo, 'pt-BR');
  const grupos = F_GROUPS.map(g => ({g:g, todas:D.specs.filter(g.f)}))
    .map(x => ({g:x.g, n:x.todas.length, rows:x.todas.filter(fPassa).sort(x.g.k === 'fim' ? recente : ord)}));
  const fora = D.specs.filter(s => !s.arquivada && !F_GROUPS.some(g => g.f(s)));
  const nEst = fora.filter(s => s.status === 'estudo' || s.status === 'guia').length, nSem = fora.length - nEst;
  const nArq = D.specs.filter(s => s.arquivada).length;
  saUI.count.textContent = grupos.map(x => plural(x.n, x.g.um, x.g.varios)).join(' · ') +
    (!SA.arq && nArq ? ' (+' + nfmt(nArq) + ' arquivadas)' : '') +
    (fora.length ? ' · fora do quadro: ' + [nEst ? plural(nEst, 'estudo ou guia', 'estudos e guias') : null, nSem ? plural(nSem, 'sem status', 'sem status') : null].filter(Boolean).join(', ') : '');
  saUI.board.replaceChildren(...grupos.map(x => {
    const sec = h('section', {class:'sacol', 'aria-label':x.g.l},
      h('h2', null, swatch(x.g.st), x.g.l, h('span', {class:'cnt'}, nfmt(x.rows.length))));
    if (!x.rows.length) sec.appendChild(h('p', {class:'empty'}, FC.q ? 'Nada casa com o filtro.' : 'Nenhuma.'));
    x.rows.forEach(s => sec.appendChild(saItem(s)));
    return sec;
  }));
}
function saItem(s){
  const gid = specGid(s.slug), noGrafo = !(G && G.byId.has(gid)), p = s.andamento_pct, t = shortTitle(s.titulo);
  return h('div', {class:'fitem'},
    h('button', {type:'button', class:'fpick', title:'Andamento da spec', onclick: e => openSpec(s.slug, e.currentTarget)},
      h('span', {class:'ft'}, t),
      h('span', {class:'fmeta'},
        p == null ? h('span', {class:'dim'}, s.arquivada ? 'arquivada' : 'sem estimativa') :
          h('span', {class:'fbar', role:'img', 'aria-label':p + '% de andamento'}, h('span', {style:'width:' + Math.max(2, p) + '%'})),
        p == null ? null : h('span', {class:'fp'}, (s.andamento_fonte === '_INDEX' ? '~' : '') + p + '%'),
        s.arquivada && p != null ? h('span', {class:'dim'}, 'arquivada') : null,
        h('span', {class:'fd' + (s.parada ? ' warn' : ''), title: s.dias_parada == null ? null : 'Sem atividade há ' + s.dias_parada + ' dias'},
          s.dias_parada == null ? '' : (s.dias_parada === 0 ? 'hoje' : s.dias_parada + ' d')))),
    h('button', {type:'button', class:'btn fmore', disabled: noGrafo || null, 'aria-label':'Ver ' + t + ' no grafo',
      title: noGrafo ? 'Esta spec ainda não está no grafo' : 'Ver no grafo',
      onclick: () => { show('grafo'); gSelect(gid, {center:true}); }}, ico('orbit')));
}

/* ════════════════ abas, cabeçalho e rodapé ════════════════ */
const TABS = [{id:'grafo', l:'Grafo do vault', c:'Grafo', i:'orbit', f:renderFoco},
              {id:'specs', l:'Specs', c:'Specs', i:'square-kanban', f:renderSpecsPage},
              {id:'linha', l:'Linha do tempo', c:'Linha', i:'chart-gantt', f:renderLinha},
              {id:'adrs', l:'ADRs', c:'ADRs', i:'scroll-text', f:renderAdrs},
              {id:'notas', l:'Anotações', c:'Notas', i:'notebook-pen', f:renderNotas}];
let active = 'specs';
const nav = document.getElementById('tabs');
TABS.forEach((t, i) => {
  // item do menu: ícone + rótulo curto; o nome acessível (e a dica) é o longo
  const b = h('button', {type:'button', role:'tab', id:'tab-' + t.id, 'aria-controls':'p-' + t.id, 'aria-label':t.l, title:t.l, onclick: () => show(t.id)},
    ico(t.i), h('span', {'aria-hidden':'true'}, t.c));
  b.addEventListener('keydown', e => {
    const nx = e.key === 'ArrowDown' || e.key === 'ArrowRight', pv = e.key === 'ArrowUp' || e.key === 'ArrowLeft';
    if (!nx && !pv) return;
    e.preventDefault();
    const j = (i + (nx ? 1 : TABS.length - 1)) % TABS.length;
    show(TABS[j].id); document.getElementById('tab-' + TABS[j].id).focus();
  });
  nav.appendChild(b);
});
function show(id){
  if (!TABS.some(t => t.id === id)) id = 'grafo';
  if (active === 'grafo' && id !== 'grafo') gPause();
  active = id; hideTip();
  PANEL.classList.toggle('is-uni', id === 'grafo');  // antes de desenhar: o tamanho do mapa depende disso
  TABS.forEach(t => {
    const b = document.getElementById('tab-' + t.id);
    b.setAttribute('aria-selected', String(t.id === id)); b.tabIndex = t.id === id ? 0 : -1;
    document.getElementById('p-' + t.id).hidden = t.id !== id;
  });
  TABS.find(t => t.id === id).f();
  placeLive();
  try { history.replaceState(null, '', '#' + id); } catch (e) {}
}
addEventListener('hashchange', () => { const id = (location.hash || '').slice(1); if (id && id !== active) show(id); });
const foot = document.getElementById('foot');
/* título = seletor de projeto (ao vivo): specs, ADRs e anotações do projeto escolhido; o grafo segue o vault inteiro */
const BASE_PROJ = D.projeto || '';
let PROJ = (() => { try { return localStorage.getItem('vault-panel:projeto') || ''; } catch (e) { return ''; } })();
const projSel = document.getElementById('proj');
function projUrl(){ return 'data.json' + (PROJ && PROJ !== BASE_PROJ ? '?projeto=' + encodeURIComponent(PROJ) : ''); }
function projFill(){
  const lista = D.projetos && D.projetos.length ? D.projetos : [D.projeto || ''], cur = D.projeto || BASE_PROJ;
  projSel.replaceChildren(...lista.map(p => h('option', {value:p, selected: p === cur || null}, p)));
  projSel.value = cur;
  projSel.disabled = !(BOOT.modo === 'ao-vivo' && /^https?:$/.test(location.protocol)) || lista.length < 2;
  document.title = 'Andamento do ' + cur;
}
projSel.addEventListener('change', () => {
  PROJ = projSel.value;
  try { localStorage.setItem('vault-panel:projeto', PROJ); } catch (e) {}
  liveFetch('s', true);
});
function drawChrome(){
  projFill();
  const R = D.resumo, gen = D.gerado_em || '';
  document.getElementById('lead').textContent =
    nfmt(R.specs_abertas) + ' specs abertas · ' + nfmt(R.specs_arquivadas) + ' arquivadas · ' + nfmt(R.adrs_total) + ' ADRs · ' +
    plural(R.notas_total, 'anotação', 'anotações') + (R.notas_pendencias ? ' (+' + plural(R.notas_pendencias, 'marcador', 'marcadores') + ' de pendências)' : '') +
    ' — gerado em ' + br(gen.slice(0, 10)) + ' às ' + gen.slice(11, 16);
  foot.replaceChildren();
  foot.appendChild(h('p', null, 'Gerado em ' + br(gen.slice(0, 10)) + ' às ' + gen.slice(11, 16) + ' (' + D.fuso + ') em ' +
    String(D.tempo_s).replace('.', ',') + ' s' + (D.com_historico ? '' : ' · sem histórico git (modo --no-history)') + '.'));
  if (R.git_erros && R.git_erros.length)
    foot.appendChild(h('p', null, h('b', null, 'Atenção: '), R.git_erros.length + ' chamada(s) ao git falharam e o histórico está incompleto (' +
      R.git_erros.slice(0, 3).join(' · ') + ').'));
  foot.appendChild(h('p', null, 'Fontes: ', h('code', null, D.fontes.vault), ' (01_Specs, 00_Context/_INDEX.md, 02_Memory/ADR-*, 02_Memory/_inbox, 04_Anotações)',
    D.com_historico ? [' · histórico das specs: ', h('code', null, D.fontes.historico_specs), ' e ', h('code', null, D.fontes.historico_vault),
      ' · notas já consolidadas: ', h('code', null, D.fontes.inbox_git)]
      : ' · sem histórico git (só o projeto principal tem a cópia do vault no repo)',
    ' · grafo: ', h('code', null, 'vault_graph.py'), '.'));
  foot.appendChild(h('p', null, 'Ao vivo: ', h('code', null, './vault-panel.sh open'), ' (servidor local em 127.0.0.1, atualiza sozinho). Retrato: ',
    h('code', null, 'python3 vault_status.py'), ' na raiz de ', h('code', null, D.fontes.repo),
    ' (', h('code', null, '--no-history'), ' e ', h('code', null, '--no-graph'), ' = modos rápidos; ', h('code', null, '--json CAMINHO'), ' exporta o modelo de dados).'));
}

/* ════════════════ ao vivo (servidor local, SSE) × retrato (arquivo) ════════════════ */
const LIVE = BOOT.modo === 'ao-vivo' && /^https?:$/.test(location.protocol) && typeof EventSource === 'function';
const liveEl = document.getElementById('live');
const liveHome = liveEl.parentNode;
/* o indicador ao vivo fica no cabeçalho; na aba Grafo (sem cabeçalho), no topo da coluna das specs */
function placeLive(){
  const dest = active === 'grafo' && fUI ? fUI.head : liveHome;
  if (liveEl.parentNode !== dest) dest.appendChild(liveEl);
}
let liveConn = LIVE ? 'conectando' : 'retrato', es = null, lastMsg = 0, lastV = null, flashT = null;
const busy = {s:false, g:false}, again = {s:false, g:false};
function agoTxt(iso){
  const sec = Math.max(0, Math.round((Date.now() - Date.parse(iso)) / 1000));
  if (!isFinite(sec)) return '';
  if (sec < 60) return 'há ' + sec + ' s';
  const m = Math.floor(sec / 60);
  if (m < 60) return 'há ' + m + ' min';
  const hh = Math.floor(m / 60);
  return 'há ' + hh + ' h' + (m % 60 ? ' ' + (m % 60) + ' min' : '');
}
/* estado do indicador (cabeçalho e topo da gaveta): "atualizado há Xs" enquanto a mudança é recente;
   depois "sem mudanças há X" — reconstrução que não mudou nada não gera versão, e o servidor segue conferindo */
function liveState(){
  const gen = D.gerado_em || '';
  const quando = br(gen.slice(0, 10)) + ' ' + gen.slice(11, 19);
  if (!LIVE)
    return {cls:'off', title:'Retrato (arquivo estático): os dados são de ' + br(gen.slice(0, 10)) + ' ' + gen.slice(11, 16) +
      '. Para o painel ao vivo, rode na raiz do repo: ./vault-panel.sh open',
      kids: () => [h('span', null, 'retrato de ' + br(gen.slice(0, 10)) + ' ' + gen.slice(11, 16) + ' — para ao vivo: ', h('code', null, './vault-panel.sh open'))]};
  if (liveConn === 'ao-vivo'){
    const erro = lastV && lastV.status_erro;
    const idade = (Date.now() - Date.parse(gen)) / 1000;
    const contato = lastMsg ? Math.max(0, Math.round((Date.now() - lastMsg) / 1000)) : null;
    const txt = erro ? 'ao vivo · falha ao atualizar' : 'ao vivo · ' + (idade < 60 ? 'atualizado ' : 'sem mudanças ') + agoTxt(gen);
    return {cls: erro ? 'wait' : 'on',
      title: (erro ? 'A última reconstrução falhou (' + erro + ') — o painel mostra os dados anteriores; veja ./vault-panel.sh status. ' : '') +
        'Última mudança nos dados: ' + quando + '. O servidor local confere o vault a cada 2 s (varredura completa a cada 60 s)' +
        (contato != null ? '; último contato há ' + contato + ' s.' : '.'),
      kids: () => [h('span', null, txt)]};
  }
  return {cls:'wait', title:'Sem contato com o servidor local; tentando de novo. Para subir: ./vault-panel.sh start',
    kids: () => [h('span', null, liveConn === 'conectando' ? 'conectando…' : 'reconectando…')]};
}
function liveRender(){
  const st = liveState();
  for (const el of [liveEl, drLiveEl]){
    if (!el) continue;
    el.className = 'live ' + st.cls + (flashT ? ' flash' : '');
    el.title = st.title;
    el.replaceChildren(h('span', {class:'ld', 'aria-hidden':'true'}), ...st.kids());
  }
}
function liveFlash(){
  clearTimeout(flashT);
  flashT = setTimeout(() => { flashT = null; liveEl.classList.remove('flash'); if (drLiveEl) drLiveEl.classList.remove('flash'); }, 1400);
  liveEl.classList.add('flash'); if (drLiveEl) drLiveEl.classList.add('flash');
}
function liveCheck(){
  const v = lastV;
  if (!v) return;
  if (v.instancia !== D.instancia || v.versao_status !== D.versao) liveFetch('s');
  if (v.versao_grafo > 0 && (!GR || v.instancia !== GR.instancia || v.versao_grafo !== GR.versao)) liveFetch('g');
}
async function liveFetch(k, force){
  if (busy[k]){ again[k] = true; return; }
  busy[k] = true;
  try {
    const r = await fetch(k === 's' ? projUrl() : 'graph.json', {cache:'no-store'});
    if (r.ok){
      const data = await r.json();
      /* outro projeto: o servidor devolve o mesmo modelo enquanto nada muda — só redesenha se mudou */
      const novo = k !== 's' || force || data.gerado_em !== D.gerado_em || data.projeto !== D.projeto;
      if (k === 's'){ if (novo) applyStatus(data); } else applyGraph(data);
      if (novo && (k === 's' || active === 'grafo')) liveFlash();
      liveRender();
    }
  } catch (e) { /* servidor caiu no meio: o EventSource reconecta e o próximo aviso tenta de novo */ }
  finally { busy[k] = false; if (again[k]){ again[k] = false; liveCheck(); } }
}
function onVersao(v){
  lastV = v; lastMsg = Date.now();
  liveConn = 'ao-vivo';
  if (v.grafo_estado !== GR_EST || (v.grafo_msg || '') !== (GR_MSG || '')){ GR_EST = v.grafo_estado; GR_MSG = v.grafo_msg || ''; if (GR) gStateRender(); else if (active === 'grafo') renderFoco(); }
  liveCheck();
  liveRender();
}
function liveConnect(){
  if (es){ try { es.close(); } catch (e) {} }
  es = new EventSource('events');
  es.addEventListener('versao', ev => { let v = null; try { v = JSON.parse(ev.data); } catch (e) {} if (v) onVersao(v); });
  es.addEventListener('ping', () => { lastMsg = Date.now(); if (liveConn !== 'ao-vivo'){ liveConn = 'ao-vivo'; liveRender(); }
    if (PROJ && PROJ !== BASE_PROJ) liveFetch('s'); });   // outro projeto: confere a cada ping (o aviso de versão é do principal)
  es.onerror = () => {
    if (liveConn !== 'reconectando'){ liveConn = 'reconectando'; liveRender(); }
    if (es.readyState === 2) setTimeout(liveConnect, 3000);     // CLOSED: o navegador desistiu — recria
  };
}
/* dados novos: troca D e redesenha preservando aba, filtros, busca, ordenação, gaveta aberta e rolagem */
function applyStatus(nd){
  const sy = PANEL.scrollTop;
  const drScroll = drawerEls ? drawerEls[1].scrollTop : 0;
  const drFocus = drFocusKey();
  D = nd; indexData(); drawChrome();
  specsStale = true;
  if (active === 'grafo') gPanelRender();
  else TABS.find(t => t.id === active).f();
  if (drawerSlug){
    if (SPEC.has(drawerSlug)) openSpec(drawerSlug, drawerOpener, {scroll: drScroll, focus: drFocus});
    else closeDrawer(true);
  }
  PANEL.scrollTop = sy;
}
/* altura do cabeçalho sticky → --hdr-h (scroll-margin dos saltos por scrollIntoView); 0 quando ele é estático (celular) */
const hdrEl = document.querySelector('header.top');
function hdrMeasure(){
  const sticky = getComputedStyle(hdrEl).position === 'sticky';
  document.documentElement.style.setProperty('--hdr-h', (sticky ? Math.ceil(hdrEl.getBoundingClientRect().height) : 0) + 'px');
}
if (typeof ResizeObserver === 'function') new ResizeObserver(hdrMeasure).observe(hdrEl);
indexData();
if (GR) gBuild();
drawChrome();
liveRender();
hdrMeasure();
if (LIVE){
  liveConnect();
  setInterval(() => {
    if (lastMsg && Date.now() - lastMsg > 45000){ lastMsg = Date.now(); liveConn = 'reconectando'; liveConnect(); }   // conexão muda (sem ping)
    liveRender();
  }, 1000);
}
addEventListener('resize', debounce(() => {
  hdrMeasure();
  if (active === 'linha') drawTimeline();
  else if (active === 'adrs') drawAdrs();
  else if (active === 'notas') drawNotas();
  else if (active === 'grafo'){ gSize(); gDraw(); }
  drawDrawerCharts();
}, 160));
show((location.hash || '').slice(1) || 'grafo');
if (LIVE && PROJ && PROJ !== BASE_PROJ) liveFetch('s', true);   // abre no projeto que a pessoa escolheu da última vez
})();
</script>
</body>
</html>
"""


HTML_TEMPLATE = HTML_TEMPLATE.replace("__FONT_WOFF2__", _font_b64())


# ───────────────────────── modo ao vivo (serve) ─────────────────────────

HOT_EVERY = 2.0          # conjunto quente: specs, _INDEX, inbox, anotações, listagem de 02_Memory, HEADs
FULL_EVERY = 60.0        # varredura completa (mtime+tamanho de todos os .md)
DEBOUNCE_STATUS = 1.5    # s após a última mudança
DEBOUNCE_GRAPH = 10.0    # s de vault quieto antes de recalcular o grafo
STATIC_EVERY = 30.0      # retrato _status.html: no máximo 1 gravação a cada 30 s
KEEPALIVE = 15.0         # SSE
MEM_WATCH_S = 600.0      # ADR que nasceu/mudou há pouco: stat a cada varredura rápida por 10 min
MEM_TOP = 20             # e sempre os 20 ADRs de número mais alto (onde caem quase todas as criações e edições)
MEM_WATCH_MAX = 60       # teto do conjunto "nasceu/mudou há pouco" (mudança em massa por git não vira 1.500 stats)
GRAPH_WAIT_MAX = 90.0    # retrato: espera o 1º grafo até 90 s após subir antes de gravar sem ele
UNI_EVERY = 60.0         # outros projetos do vault: assinatura a cada 60 s
SKIP_DIRS = {"raw", ".obsidian", ".trash", "assets"}
GENERATED = {"_status.html", "_graph.html", "_status.md"}   # o que o próprio painel grava: nunca observado
COST_LOG_EVERY = 600.0   # registra o custo do observador no log a cada 10 min


def log(msg):
    print(f"[{datetime.now(TZ):%Y-%m-%d %H:%M:%S}] {msg}", file=sys.stderr, flush=True)


def affects_status(rel):
    """Mudança neste caminho (relativo ao vault) mexe no modelo de status?"""
    parts = rel.split("/")
    if len(parts) == 2 and parts[1].endswith(".md"):
        if parts[0] == "01_Specs":
            return parts[1] not in SPEC_EXCLUDE
        if parts[0] == "02_Memory":
            return parts[1].startswith("ADR-")
        if parts[0] == "04_Anotações":
            return True
    if len(parts) == 3 and parts[0] == "02_Memory" and parts[1] == "_inbox":
        return True
    return rel == "00_Context/_INDEX.md"


def _env_set(nome):
    return {x.strip().strip("/") for x in (os.environ.get(nome) or "").split(",") if x.strip()}


_EXCL_SUB, _EXCL_KEEP = _env_set("VAULT_PANEL_EXCLUDE"), _env_set("VAULT_PANEL_EXCLUDE_KEEP")


def affects_graph(rel):
    """Mesmo recorte do vault_graph.collect_files (sem raw/_inbox/assets; das subpastas excluídas, só os mantidos)."""
    if rel.startswith("memoria/"):
        return True
    parts = rel.split("/")
    if any(p in ("raw", "_inbox", "assets", ".obsidian", ".trash") for p in parts[:-1]):
        return False
    for sub in _EXCL_SUB:
        if rel.startswith(sub + "/"):
            return os.path.basename(rel) in _EXCL_KEEP
    return True


class VaultWatcher(threading.Thread):
    """Polling híbrido do vault (o WSL não recebe inotify do que o Windows grava em /mnt/c).

    A cada HOT_EVERY: stat dos .md de 01_Specs, _inbox e 04_Anotações, do _INDEX.md e da memória do
    agente; LISTAGEM de nomes de 02_Memory (ADR novo/removido) e stat dos ADRs "quentes" (os MEM_TOP de
    número mais alto + os que nasceram ou mudaram nos últimos MEM_WATCH_S — o Obsidian cria a nota vazia e
    ela é preenchida depois); HEAD do repo e do git do vault; virada do dia. A cada FULL_EVERY: mtime+tamanho
    de todos os .md (fora de raw/.obsidian/.trash/assets). `sigs` (caminho → (mtime_ns, tamanho)) é também a
    fonte de assinaturas do cache de leitura."""

    def __init__(self, vault, agent_mem, repos, on_change, stop):
        super().__init__(name="observador", daemon=True)
        self.vault, self.agent_mem, self.repos = vault, agent_mem, repos
        self.on_change, self.stop = on_change, stop
        self.sigs = {}
        self.hot_dirs = [os.path.join(vault, "01_Specs"), os.path.join(vault, "02_Memory", "_inbox"),
                         os.path.join(vault, "04_Anotações")] + ([agent_mem] if agent_mem else [])
        self.index_md = os.path.join(vault, "00_Context", "_INDEX.md")
        self.mem_dir = os.path.join(vault, "02_Memory")
        self.members = {d: set() for d in self.hot_dirs}
        self.mem_names = set()
        self.mem_top = set()       # caminhos dos MEM_TOP ADRs de número mais alto
        self.mem_watch = {}        # caminho -> monotonic até quando segue quente (nasceu/mudou há pouco)
        self.heads = {r: head_sig(r) for r in repos}
        self.today = datetime.now(TZ).date()
        self.cost = {"rapidas": 0, "rapidas_parede_s": 0.0, "rapidas_cpu_s": 0.0,
                     "completas": 0, "completas_parede_s": 0.0, "completas_cpu_s": 0.0,
                     "ultima_completa_s": None, "erros": 0}
        self._err_logged = set()

    def rel(self, path):
        if path.startswith(self.vault + os.sep):
            return path[len(self.vault) + 1:].replace(os.sep, "/")
        return "memoria/" + os.path.basename(path)

    def _err(self, where, e):
        self.cost["erros"] += 1
        if where not in self._err_logged:   # uma linha por origem (o Windows pode sumir por um tempo)
            self._err_logged.add(where)
            log(f"observador: falha em {where}: {type(e).__name__}: {e}")

    def _md_in(self, d, old=None):
        """.md diretamente em d. Erro numa entrada (symlink quebrado, arquivo apagado no meio da listagem)
        pula só aquela entrada — ou mantém a assinatura anterior (`old`) se o arquivo ainda existe."""
        out = {}
        with os.scandir(d) as it:
            for e in it:
                if not e.name.endswith(".md") or e.name in GENERATED:
                    continue
                try:
                    if not e.is_file():
                        continue
                    st = e.stat()
                except FileNotFoundError:
                    continue
                except OSError as ex:
                    self._err("entrada " + e.path, ex)
                    if old is not None and e.path in old:
                        out[e.path] = old[e.path]
                    continue
                out[e.path] = (st.st_mtime_ns, st.st_size)
        return out

    @staticmethod
    def _adr_n(name):
        m = re.match(r"ADR-0*(\d+)", name)
        return int(m.group(1)) if m else -1

    def _set_mem_names(self, names):
        self.mem_names = names
        top = sorted((n for n in names if n.startswith("ADR-")), key=self._adr_n, reverse=True)[:MEM_TOP]
        self.mem_top = {os.path.join(self.mem_dir, n) for n in top}

    def scan_full(self):
        """Tudo de novo. Erro numa entrada ou numa subpasta não derruba a passada: a entrada é pulada (ou
        mantém a assinatura anterior se o erro não for "não existe"). Só erro na RAIZ do vault aborta e mantém
        o mapa antigo (Windows fora do ar ≠ vault apagado)."""
        w, c = time.monotonic(), time.thread_time()
        old = self.sigs
        new, stack = {}, [self.vault]
        while stack:
            d = stack.pop()
            try:
                with os.scandir(d) as it:
                    entries = list(it)
            except OSError as e:
                if d == self.vault:
                    self._err("varredura completa", e)
                    return set()
                self._err("pasta " + d, e)
                if not isinstance(e, FileNotFoundError):   # pasta ainda existe mas não abriu: mantém o que havia
                    pre = d + os.sep
                    new.update({p: s for p, s in old.items() if p.startswith(pre)})
                continue
            for e in entries:
                try:
                    if e.is_dir(follow_symlinks=False):
                        if e.name not in SKIP_DIRS and not e.name.startswith("."):
                            stack.append(e.path)
                        continue
                    if not e.name.endswith(".md") or e.name in GENERATED:
                        continue
                    st = e.stat()
                except FileNotFoundError:     # symlink quebrado ou apagado no meio da varredura
                    continue
                except OSError as ex:
                    self._err("entrada " + e.path, ex)
                    if e.path in old:
                        new[e.path] = old[e.path]
                    continue
                new[e.path] = (st.st_mtime_ns, st.st_size)
        if self.agent_mem:
            try:
                if os.path.isdir(self.agent_mem):
                    new.update(self._md_in(self.agent_mem, old))
            except OSError as e:
                self._err(self.agent_mem, e)
                new.update({p: s for p, s in old.items() if os.path.dirname(p) == self.agent_mem})
        changed = {p for p in new.keys() | old.keys() if new.get(p) != old.get(p)}
        self.sigs = new
        for d in self.hot_dirs:
            self.members[d] = {p for p in new if os.path.dirname(p) == d}
        mem = {p: s for p, s in new.items() if os.path.dirname(p) == self.mem_dir}
        self._set_mem_names({os.path.basename(p) for p in mem})
        # ADR mexido há pouco (pela data do arquivo) ou que acabou de mudar: segue no stat rápido por 10 min
        agora, lim = time.monotonic(), time.time() - MEM_WATCH_S
        for p, s in mem.items():
            if s[0] / 1e9 >= lim or (old and p in changed):
                self.mem_watch[p] = max(self.mem_watch.get(p, 0.0), agora + MEM_WATCH_S)
        vivos = [p for p, t in self.mem_watch.items() if p in mem and t > agora]
        if len(vivos) > MEM_WATCH_MAX:   # mudança em massa (git): só os mais recentes pela data do arquivo
            vivos = sorted(vivos, key=lambda p: mem[p][0], reverse=True)[:MEM_WATCH_MAX]
        self.mem_watch = {p: self.mem_watch[p] for p in vivos}
        self.cost["completas"] += 1
        self.cost["completas_parede_s"] += time.monotonic() - w
        self.cost["completas_cpu_s"] += time.thread_time() - c
        self.cost["ultima_completa_s"] = round(time.monotonic() - w, 3)
        return {self.rel(p) for p in changed}

    def scan_hot(self):
        w, c = time.monotonic(), time.thread_time()
        sigs, changed = self.sigs, set()
        for d in self.hot_dirs:
            try:
                new = self._md_in(d, sigs) if os.path.isdir(d) else {}
            except OSError as e:
                self._err(d, e)
                continue
            for p in self.members[d] - new.keys():
                sigs.pop(p, None)
                changed.add(p)
            for p, sg in new.items():
                if sigs.get(p) != sg:
                    sigs[p] = sg
                    changed.add(p)
            self.members[d] = set(new)
        try:
            st = os.stat(self.index_md)
            sg = (st.st_mtime_ns, st.st_size)
        except OSError:
            sg = None
        if sigs.get(self.index_md) != sg:
            if sg is None:
                sigs.pop(self.index_md, None)
            else:
                sigs[self.index_md] = sg
            changed.add(self.index_md)
        # 02_Memory: a LISTAGEM de nomes (ADR novo/removido) + stat só dos ADRs quentes; o conteúdo dos demais
        # entra na varredura completa
        try:
            names = {n for n in os.listdir(self.mem_dir) if n.endswith(".md") and n not in GENERATED}
        except OSError as e:
            self._err(self.mem_dir, e)
            names = self.mem_names
        agora = time.monotonic()
        for n in self.mem_names - names:
            p = os.path.join(self.mem_dir, n)
            sigs.pop(p, None)
            self.mem_watch.pop(p, None)
            changed.add(p)
        novos = names - self.mem_names
        for n in novos:   # nasceu agora: quase sempre vazio (Obsidian) — fica quente por 10 min
            self.mem_watch[os.path.join(self.mem_dir, n)] = agora + MEM_WATCH_S
        if names != self.mem_names:
            self._set_mem_names(names)
        self.mem_watch = {p: t for p, t in self.mem_watch.items() if t > agora}
        for p in self.mem_top | self.mem_watch.keys():
            try:
                st = os.stat(p)
                sg = (st.st_mtime_ns, st.st_size)
            except FileNotFoundError:   # renomeado/apagado entre a listagem e o stat: a próxima listagem decide
                continue
            except OSError as e:
                self._err("ADR " + p, e)
                continue
            if sigs.get(p) != sg:
                sigs[p] = sg
                changed.add(p)
                if p in self.mem_watch or p not in self.mem_top:
                    self.mem_watch[p] = agora + MEM_WATCH_S   # sendo editado: estende a janela
        self.cost["rapidas"] += 1
        self.cost["rapidas_parede_s"] += time.monotonic() - w
        self.cost["rapidas_cpu_s"] += time.thread_time() - c
        return {self.rel(p) for p in changed}

    def scan_meta(self):
        out = set()
        for r in self.repos:
            h = head_sig(r)
            if h != self.heads.get(r):
                self.heads[r] = h
                out.add("<git>")
        today = datetime.now(TZ).date()
        if today != self.today:
            self.today = today
            out.add("<dia>")
        return out

    def run(self):
        next_hot = time.monotonic() + HOT_EVERY
        next_full = time.monotonic() + FULL_EVERY
        while not self.stop.is_set():
            now = time.monotonic()
            changed = set()
            try:
                if now >= next_full:
                    changed |= self.scan_full()
                    next_full, next_hot = now + FULL_EVERY, now + HOT_EVERY
                elif now >= next_hot:
                    changed |= self.scan_hot()
                    next_hot = now + HOT_EVERY
                changed |= self.scan_meta()
                if changed:
                    self.on_change(changed)
            except Exception as e:  # noqa: BLE001 — o observador nunca morre
                self._err("laço", e)
                traceback.print_exc()
            self.stop.wait(max(0.05, min(next_hot, next_full) - time.monotonic()))


class DebouncedJob(threading.Thread):
    """Roda `fn(motivos)` quando passaram `quiet` s desde o último poke(); pokes durante a execução
    geram uma nova rodada ao terminar."""

    def __init__(self, name, quiet, fn, stop):
        super().__init__(name=name, daemon=True)
        self.quiet, self.fn, self.stop = quiet, fn, stop
        self.cv = threading.Condition()
        self.pending, self.last, self.reasons = False, 0.0, set()

    def poke(self, reasons=(), immediate=False):
        with self.cv:
            self.pending = True
            self.last = time.monotonic() - (self.quiet if immediate else 0)
            self.reasons |= set(reasons)
            self.cv.notify_all()

    def run(self):
        while not self.stop.is_set():
            with self.cv:
                while not self.pending and not self.stop.is_set():
                    self.cv.wait(1.0)
                while not self.stop.is_set():
                    remaining = self.last + self.quiet - time.monotonic()
                    if remaining <= 0:
                        break
                    self.cv.wait(remaining)
                if self.stop.is_set():
                    return
                self.pending, reasons, self.reasons = False, self.reasons, set()
            try:
                self.fn(reasons)
            except Exception:  # noqa: BLE001
                log(f"{self.name}: falhou")
                traceback.print_exc()


def _fingerprint(model, volatile):
    """Impressão digital do modelo sem os campos voláteis (hora, tempo, versão): reconstrução que não mudou
    nada não vira versão nova nem evento."""
    saved = {k: model.pop(k) for k in volatile if k in model}
    body = json.dumps(model, ensure_ascii=False, separators=(",", ":"))
    model.update(saved)
    return hashlib.sha1(_u8(body)).hexdigest()


class LiveState:
    """Estado compartilhado entre o observador, os reconstrutores e as conexões HTTP."""

    def __init__(self, html_path, no_history, write_static, graph_expected=True):
        self.lock = threading.Lock()
        self.write_lock = threading.Lock()   # uma gravação do retrato por vez (timer × desligamento)
        self.instancia = secrets.token_hex(4)
        self.iniciado = time.time()
        self.iniciado_mono = time.monotonic()
        self.html_path, self.no_history, self.write_static = html_path, no_history, write_static
        self.graph_expected = graph_expected
        self.ready = threading.Event()
        self.stopping = False
        self.status_model = None
        self.status_json = b""
        self.status_embed = "null"
        self.status_fp = None
        self.vs = 0
        self.status_ultimo_s = None
        self.status_erro, self.status_erro_em = None, None
        self.graph_json = None
        self.graph_embed = "null"
        self.graph_fp = None
        self.vg = 0
        self.graph_gerado_em = None
        self.graph_ultimo_s = None
        self.grafo_estado, self.grafo_msg = "recalculando", None
        self.subs = set()
        self.page_cache = (None, b"")
        self.last_static = 0.0
        self.static_timer = None
        self.static_gen = 0          # timer antigo (substituído/cancelado) que dispara mesmo assim não grava
        self.static_deferral = False  # o timer atual só espera o 1º grafo (a publicação do grafo o substitui)
        self.cpu_samples = [(time.monotonic(), time.process_time())]

    # ── assinantes SSE: um Event por conexão; o laço da conexão sempre envia o estado MAIS RECENTE
    def payload(self):
        with self.lock:
            return {"instancia": self.instancia, "versao_status": self.vs, "versao_grafo": self.vg,
                    "grafo_estado": self.grafo_estado, "grafo_msg": self.grafo_msg,
                    "gerado_em": self.status_model["gerado_em"] if self.status_model else None,
                    "grafo_gerado_em": self.graph_gerado_em,
                    "status_erro": self.status_erro, "status_erro_em": self.status_erro_em}

    def subscribe(self):
        ev = threading.Event()
        with self.lock:
            self.subs.add(ev)
        return ev

    def unsubscribe(self, ev):
        with self.lock:
            self.subs.discard(ev)

    def broadcast(self):
        with self.lock:
            subs = list(self.subs)
        for ev in subs:
            ev.set()

    def set_graph_state(self, estado, msg=None):
        with self.lock:
            if (self.grafo_estado, self.grafo_msg) == (estado, msg):
                return
            self.grafo_estado, self.grafo_msg = estado, msg
            solta = estado in ("erro", "indisponivel") and self.static_deferral
        self.broadcast()
        if solta:   # o 1º grafo falhou: o retrato que esperava por ele grava agora (sem grafo)
            self.schedule_static()

    def set_status_error(self, msg):
        """msg=None limpa. Falha na reconstrução do status aparece no indicador e na /healthz."""
        with self.lock:
            if msg == self.status_erro:
                return
            self.status_erro = msg
            self.status_erro_em = datetime.now(TZ).isoformat(timespec="seconds") if msg else None
        self.broadcast()

    # ── publicação
    def publish_status(self, model, tempo):
        fp = _fingerprint(model, ("gerado_em", "tempo_s", "versao", "instancia"))
        with self.lock:
            self.status_ultimo_s = tempo
            if fp == self.status_fp:
                return False
            vs = self.vs + 1
            model["versao"], model["instancia"] = vs, self.instancia
            raw = json.dumps(model, ensure_ascii=False, separators=(",", ":"))
            body = _u8(raw)
            self.vs = vs
            self.status_model, self.status_fp, self.status_embed = model, fp, escape_embed(raw)
            self.status_json = body
        self.ready.set()
        self.broadcast()
        self.schedule_static()
        return True

    def publish_graph(self, gm, tempo):
        fp = _fingerprint(gm, ("gerado_em", "tempo_s", "versao", "instancia"))
        with self.lock:
            self.graph_ultimo_s = tempo
            changed = fp != self.graph_fp
            if changed:
                vg = self.vg + 1
                gm["versao"], gm["instancia"] = vg, self.instancia
                raw = json.dumps(gm, ensure_ascii=False, separators=(",", ":"))
                body = _u8(raw)
                self.vg = vg
                self.graph_fp, self.graph_embed = fp, escape_embed(raw)
                self.graph_json = body
                self.graph_gerado_em = gm["gerado_em"]
            self.grafo_estado, self.grafo_msg = "pronto", None
            solta = self.static_deferral
        self.broadcast()
        if changed or solta:
            self.schedule_static()
        return changed

    def page(self):
        with self.lock:
            key = (self.vs, self.vg, self.grafo_estado, self.grafo_msg)
            if self.page_cache[0] == key:
                return self.page_cache[1]
            meta = {"modo": "ao-vivo", "instancia": self.instancia, "grafo_estado": self.grafo_estado,
                    "grafo_msg": self.grafo_msg}
            status_embed, graph_embed = self.status_embed, self.graph_embed
        body = _u8(render_page(status_embed, graph_embed, meta))
        with self.lock:
            self.page_cache = (key, body)
        return body

    # ── retrato estático: no máximo 1 gravação a cada STATIC_EVERY
    def _arm(self, delay, deferral):
        """Com self.lock: (re)arma o timer do retrato."""
        if self.static_timer is not None:
            self.static_timer.cancel()
        self.static_gen += 1
        t = threading.Timer(delay, self._write_static, args=(self.static_gen,))
        t.daemon = True
        self.static_timer, self.static_deferral = t, deferral
        return t

    def schedule_static(self):
        if not self.write_static:
            return
        with self.lock:
            if self.stopping or (self.static_timer is not None and not self.static_deferral):
                return
            t = self._arm(max(0.0, self.last_static + STATIC_EVERY - time.monotonic()), False)
        t.start()

    def _waiting_first_graph(self):
        """Com self.lock: o retrato ainda deve esperar o 1º grafo? (quanto falta, em s; 0 = não espera)"""
        if not self.graph_expected or self.graph_json is not None or self.grafo_estado not in ("recalculando", "pendente"):
            return 0.0
        return max(0.0, self.iniciado_mono + GRAPH_WAIT_MAX - time.monotonic())

    def _write_static(self, gen=None, final=False):
        """Grava o retrato. Na subida, espera o 1º grafo (até GRAPH_WAIT_MAX) para não trocar um retrato que
        tem grafo por um sem. final=True: gravação síncrona do desligamento (a pendente, sem janela de 30 s)."""
        with self.write_lock:
            with self.lock:
                if gen is not None:
                    if gen != self.static_gen:        # timer substituído/cancelado
                        return
                    self.static_timer, self.static_deferral = None, False
                if self.status_embed == "null" or (self.stopping and not final):
                    return
                falta = self._waiting_first_graph()
                if falta > 0:
                    if final:
                        log("retrato não regravado no desligamento: o 1º grafo ainda estava em montagem "
                            "(fica o retrato anterior)")
                        return
                    t = self._arm(falta, True)       # a publicação do grafo antecipa (schedule_static)
                    t.start()
                    return
                self.last_static = time.monotonic()
                meta = {"modo": "retrato", "grafo_estado": "pronto" if self.graph_json else self.grafo_estado,
                        "grafo_msg": None if self.graph_json else self.grafo_msg}
                status_embed, graph_embed = self.status_embed, self.graph_embed
            try:
                t0 = time.time()
                size = write_file_atomic(self.html_path, render_page(status_embed, graph_embed, meta))
                log(f"retrato regravado{' (desligamento)' if final else ''}: {self.html_path} "
                    f"({size // 1024} KB, {time.time() - t0:.2f} s)")
            except OSError as e:
                log(f"retrato: falha ao gravar {self.html_path}: {e}")

    def flush_static(self):
        """Desligamento: a gravação agendada (dentro da janela de 30 s) sai agora, em vez de ser perdida."""
        with self.lock:
            pend = self.static_timer is not None
            if pend:
                self.static_timer.cancel()
                self.static_gen += 1
                self.static_timer, self.static_deferral = None, False
        if pend:
            self._write_static(final=True)
        else:   # espera uma gravação que esteja no meio (timer já disparado)
            with self.write_lock:
                pass

    def cpu_pct(self, window=60.0):
        """CPU do processo (todas as threads) na janela mais recente de amostras, em % de 1 núcleo."""
        now, cpu = time.monotonic(), time.process_time()
        with self.lock:
            self.cpu_samples.append((now, cpu))
            self.cpu_samples = [x for x in self.cpu_samples if now - x[0] <= max(window, 600.0)] or [(now, cpu)]
            base = next((x for x in self.cpu_samples if now - x[0] <= window), self.cpu_samples[0])
        dt = now - base[0]
        return round(100.0 * (cpu - base[1]) / dt, 2) if dt > 0.5 else None


def _make_handler(state, watcher, port):
    allowed_hosts = {"localhost", "127.0.0.1", "[::1]"}

    class Handler(BaseHTTPRequestHandler):
        server_version = "vault-panel/1"

        def log_message(self, fmt, *args):   # sem uma linha por requisição no log
            pass

        def _host_ok(self):
            """Só aceita Host local (protege de DNS rebinding: outro site não lê o vault pelo navegador)."""
            host = (self.headers.get("Host") or "").strip().lower()
            name = host.split("]")[0] + "]" if host.startswith("[") else host.rsplit(":", 1)[0]
            return name in allowed_hosts

        def _send(self, code, body, ctype, extra=None):
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("Referrer-Policy", "no-referrer")
            for k, v in (extra or {}).items():
                self.send_header(k, v)
            self.end_headers()
            if self.command != "HEAD":
                self.wfile.write(body)

        def _json(self, code, obj):
            self._send(code, _u8(json.dumps(obj, ensure_ascii=False)), "application/json; charset=utf-8")

        def do_HEAD(self):
            self.do_GET()

        def do_GET(self):
            if not self._host_ok():
                return self._send(403, b"host nao permitido\n", "text/plain; charset=utf-8")
            path = urlsplit(self.path).path
            try:
                if path in ("/", "/index.html", "/foco", "/foco/", "/completo", "/completo/"):
                    fim = time.monotonic() + 90
                    while not state.ready.wait(0.5):
                        with state.lock:
                            erro = state.status_erro
                        if erro or state.stopping or time.monotonic() >= fim:
                            msg = ("o painel não conseguiu montar o primeiro modelo: " + erro +
                                   " — veja o log (./vault-panel.sh status)\n") if erro else \
                                "o painel ainda está montando o primeiro modelo; recarregue em instantes\n"
                            return self._send(503, _u8(msg), "text/plain; charset=utf-8", {"Retry-After": "3"})
                    csp = ("default-src 'self'; script-src 'self' 'unsafe-inline' https://cdnjs.cloudflare.com; "
                           "style-src 'self' 'unsafe-inline'; img-src 'self' data:; connect-src 'self'; "
                           "font-src data:; base-uri 'none'; form-action 'none'; frame-ancestors 'none'")
                    return self._send(200, state.page(), "text/html; charset=utf-8", {"Content-Security-Policy": csp})
                if path == "/data.json":
                    proj = (parse_qs(urlsplit(self.path).query).get("projeto") or [""])[0]
                    if proj and proj != os.path.basename(_BASE[0] or VAULT):
                        try:
                            body = project_json(proj)
                        except Exception as e:  # noqa: BLE001
                            traceback.print_exc()
                            return self._json(500, {"estado": "erro", "mensagem": f"{type(e).__name__}: {e}"})
                        if body is None:
                            return self._json(404, {"estado": "erro", "mensagem": "projeto desconhecido"})
                        return self._send(200, body, "application/json; charset=utf-8")
                    if not state.ready.is_set():
                        with state.lock:
                            erro = state.status_erro
                        return self._json(503, {"estado": "erro" if erro else "iniciando", "mensagem": erro})
                    with state.lock:
                        body = state.status_json
                    return self._send(200, body, "application/json; charset=utf-8")
                if path == "/graph.json":
                    with state.lock:
                        body, est, msg = state.graph_json, state.grafo_estado, state.grafo_msg
                    if body is None:
                        return self._json(503, {"estado": est, "mensagem": msg})
                    return self._send(200, body, "application/json; charset=utf-8", {"X-Grafo-Estado": est})
                if path == "/events":
                    if self.command == "HEAD":
                        return self._send(200, b"", "text/event-stream; charset=utf-8")
                    return self._events()
                if path == "/healthz":
                    return self._json(200, self._health())
                return self._send(404, b"nao encontrado\n", "text/plain; charset=utf-8")
            except (BrokenPipeError, ConnectionResetError):
                pass

        def _health(self):
            p = state.payload()
            c = watcher.cost
            avg = lambda tot, n: round(1000 * tot / n, 1) if n else None   # noqa: E731
            return {"ok": True, "pid": os.getpid(), "porta": port, "vault": VAULT, **p,
                    "pronto": state.ready.is_set(), "uptime_s": round(time.time() - state.iniciado),
                    "status_rebuild_s": state.status_ultimo_s, "grafo_rebuild_s": state.graph_ultimo_s,
                    "cpu_processo_s": round(time.process_time(), 2), "cpu_pct_60s": state.cpu_pct(60.0),
                    "observador": {"arquivos": len(watcher.sigs), "rapidas": c["rapidas"],
                                   "rapida_parede_ms": avg(c["rapidas_parede_s"], c["rapidas"]),
                                   "rapida_cpu_ms": avg(c["rapidas_cpu_s"], c["rapidas"]),
                                   "completas": c["completas"],
                                   "completa_parede_ms": avg(c["completas_parede_s"], c["completas"]),
                                   "completa_cpu_ms": avg(c["completas_cpu_s"], c["completas"]),
                                   "erros": c["erros"]}}

        def _events(self):
            self.send_response(200)
            self.send_header("Content-Type", "text/event-stream; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            self.send_header("X-Accel-Buffering", "no")
            self.end_headers()
            sub = state.subscribe()
            try:
                self.wfile.write(b"retry: 3000\n\n")
                last = None
                while not state.stopping:
                    p = state.payload()
                    if p != last:
                        self.wfile.write(b"event: versao\ndata: " + _u8(json.dumps(p, ensure_ascii=False)) + b"\n\n")
                        self.wfile.flush()
                        last = p
                    if sub.wait(KEEPALIVE):
                        sub.clear()
                        continue
                    if state.stopping:
                        break
                    self.wfile.write(b"event: ping\ndata: {\"t\":" + str(int(time.time())).encode() + b"}\n\n")
                    self.wfile.flush()
            except (BrokenPipeError, ConnectionResetError, OSError):
                pass
            finally:
                state.unsubscribe(sub)

    return Handler


def serve(a):
    no_history = a.no_history
    html_path = a.html or os.path.join(VAULT, "_status.html")
    stop = threading.Event()
    state = LiveState(html_path, no_history, write_static=not a.no_static)
    agent_mem = None
    try:   # a memória do agente entra no grafo (vault_graph.MEMORY_DIR); sem networkx, fica de fora
        if HERE not in sys.path:
            sys.path.insert(0, HERE)
        import vault_graph
        agent_mem = vault_graph.MEMORY_DIR if os.path.isdir(vault_graph.MEMORY_DIR) else None
        graph_ok = True
    except ImportError as e:
        graph_ok = False
        state.grafo_estado = "indisponivel"
        state.grafo_msg = f"networkx não está disponível no python3 ({e}). Instale com: pip install networkx"
    state.graph_expected = graph_ok

    global _CACHE
    _CACHE = _LiveCache()
    watcher = VaultWatcher(VAULT, agent_mem, (REPO, VAULT_ROOT), on_change=lambda ch: on_change(ch), stop=stop)
    try:
        httpd = ThreadingHTTPServer(("127.0.0.1", a.port), _make_handler(state, watcher, a.port))
    except OSError as e:
        print(f"vault_status serve: não consegui abrir 127.0.0.1:{a.port} ({e}). Já está no ar? "
              f"Veja ./vault-panel.sh status", file=sys.stderr)
        return 1
    httpd.daemon_threads = True
    _BASE[0] = VAULT
    log(f"painel ao vivo em http://localhost:{a.port}  · vault {VAULT} · pid {os.getpid()}")

    def rebuild_status(reasons):
        t0 = time.time()
        motivo = ", ".join(sorted(reasons)[:4]) + (f" (+{len(reasons) - 4})" if len(reasons) > 4 else "")
        try:
            _CACHE.sigs = watcher.sigs
            _CACHE.heads = dict(watcher.heads)
            with MODEL_LOCK:
                model = build_model(no_history)
            _CACHE.prune()
            tempo = round(time.time() - t0, 2)
            mudou = state.publish_status(model, tempo)
        except Exception as e:  # noqa: BLE001 — aparece no indicador e na /healthz; a próxima mudança tenta de novo
            traceback.print_exc()
            state.set_status_error(f"{type(e).__name__}: {e}")
            log(f"status: falhou — {type(e).__name__}: {e}" + (f" — {motivo}" if motivo else ""))
            return
        state.set_status_error(None)
        log(f"status {'v' + str(state.vs) if mudou else 'sem mudança'} em {tempo:.2f} s"
            + (f" — {motivo}" if motivo else ""))

    def rebuild_graph(reasons):
        state.set_graph_state("recalculando")
        t0 = time.time()
        try:
            gm, estado, msg = build_graph_safe(VAULT)
            tempo = round(time.time() - t0, 2)
            if gm is None:
                state.set_graph_state(estado, msg)
                log(f"grafo: {estado} — {msg}")
                return
            mudou = state.publish_graph(gm, tempo)
        except Exception as e:  # noqa: BLE001 — nunca fica preso em "recalculando"
            traceback.print_exc()
            state.set_graph_state("erro", f"{type(e).__name__}: {e}")
            log(f"grafo: erro ao publicar — {type(e).__name__}: {e}")
            return
        log(f"grafo {'v' + str(state.vg) if mudou else 'sem mudança'} em {tempo:.2f} s "
            f"({len(gm['nos'])} nós, {len(gm['arestas'])} arestas)")

    status_job = DebouncedJob("status", DEBOUNCE_STATUS, rebuild_status, stop)
    graph_job = DebouncedJob("grafo", DEBOUNCE_GRAPH, rebuild_graph, stop)

    def universe_watch():
        """Outros projetos do vault: assinatura mtime+tamanho a cada UNI_EVERY;
        mudou → reconstrói o grafo (o universo vai junto). O projeto principal fica com o VaultWatcher."""
        raiz, principal = os.path.dirname(VAULT), os.path.basename(VAULT)
        excl = {"raw", "_inbox", "assets", ".obsidian", ".trash", ".git"}

        def assinatura():
            h = 0
            for root, dirs, names in os.walk(raiz):
                if root == raiz:
                    dirs[:] = [d for d in dirs if d != principal and d not in excl]
                else:
                    dirs[:] = [d for d in dirs if d not in excl]
                for n in names:
                    if n.endswith(".md"):
                        try:
                            st = os.stat(os.path.join(root, n))
                        except OSError:
                            continue
                        h = hash((h, root, n, st.st_mtime_ns, st.st_size))
            return h

        ultima = None
        while not stop.wait(0 if ultima is None else UNI_EVERY):
            try:
                a = assinatura()
            except Exception:  # noqa: BLE001
                continue
            if ultima is not None and a != ultima:
                with state.lock:
                    pronto = state.grafo_estado in ("pronto", "erro")
                if pronto:
                    state.set_graph_state("pendente")
                graph_job.poke({"<universo>"})
                log("universo: mudança em outro projeto do vault")
            ultima = a

    if graph_ok:
        threading.Thread(target=universe_watch, name="universo", daemon=True).start()

    def on_change(changed):
        st = any(r in ("<git>", "<dia>") or affects_status(r) for r in changed)
        gr = graph_ok and any(affects_graph(r) for r in changed if not r.startswith("<"))
        if st:
            status_job.poke(changed)
        if gr:
            with state.lock:
                pronto = state.grafo_estado in ("pronto", "erro")
            if pronto:
                state.set_graph_state("pendente")
            graph_job.poke(changed)

    def shutdown(signum, _frame):
        if state.stopping:
            return
        log(f"sinal {signum}: encerrando")
        state.stopping = True
        stop.set()
        state.broadcast()
        threading.Thread(target=httpd.shutdown, daemon=True).start()

    signal.signal(signal.SIGTERM, shutdown)
    signal.signal(signal.SIGINT, shutdown)

    threading.Thread(target=httpd.serve_forever, kwargs={"poll_interval": 0.5}, name="http", daemon=True).start()
    watcher.scan_full()   # mapa inicial (≈0,5 s) antes da 1ª reconstrução: o cache lê as assinaturas dali
    log(f"observador: {len(watcher.sigs)} arquivos .md (varredura completa em {watcher.cost['ultima_completa_s']} s)")
    status_job.start()
    status_job.poke({"<inicio>"}, immediate=True)
    if graph_ok:
        graph_job.start()
        graph_job.poke({"<inicio>"}, immediate=True)
    watcher.start()

    last_cost = time.monotonic()
    while not stop.wait(10.0):
        state.cpu_pct(60.0)   # amostra para a janela de CPU
        if time.monotonic() - last_cost >= COST_LOG_EVERY:
            last_cost = time.monotonic()
            c = watcher.cost
            r, f = max(1, c["rapidas"]), max(1, c["completas"])
            log(f"custo do observador: {c['rapidas']} varreduras rápidas (média {1000 * c['rapidas_parede_s'] / r:.0f} ms"
                f" de parede, {1000 * c['rapidas_cpu_s'] / r:.1f} ms de CPU), {c['completas']} completas (média"
                f" {1000 * c['completas_parede_s'] / f:.0f} ms, {1000 * c['completas_cpu_s'] / f:.0f} ms de CPU);"
                f" CPU do processo na última janela: {state.cpu_pct(600.0)}%")
    state.flush_static()   # a gravação do retrato agendada na janela de 30 s não se perde
    time.sleep(0.2)
    httpd.server_close()   # libera a porta já (um restart logo em seguida não esbarra no socket antigo)
    log("encerrado")
    return 0


def main():
    ap = argparse.ArgumentParser(description="AI Second Brain: painel ao vivo de um vault do Obsidian (specs, ADRs, anotações e grafo).")
    ap.add_argument("modo", nargs="?", choices=("serve",), help="serve = painel ao vivo em http://localhost:PORTA")
    ap.add_argument("--vault", help="pasta do vault (padrão: " + VAULT + ")")
    ap.add_argument("--html", help="destino do HTML (padrão: <vault>/_status.html)")
    ap.add_argument("--json", help="exporta o modelo de dados neste caminho")
    ap.add_argument("--no-history", action="store_true", help="pula o histórico git (modo rápido)")
    ap.add_argument("--no-graph", action="store_true", help="retrato sem a aba Grafo (não usa networkx)")
    ap.add_argument("--port", type=int, default=int(os.environ.get("VAULT_PANEL_PORT", "8765")),
                    help="porta do modo serve (só 127.0.0.1; padrão 8765 ou $VAULT_PANEL_PORT)")
    ap.add_argument("--no-static", action="store_true", help="serve: não regrava o retrato _status.html")
    a = ap.parse_args()
    if a.vault:
        set_vault(a.vault)
    if not (os.path.isdir(os.path.join(VAULT, "01_Specs")) or os.path.isdir(os.path.join(VAULT, "02_Memory"))):
        ap.error(f"{VAULT}: não parece a pasta de um projeto do vault (sem 01_Specs/ nem 02_Memory/). "
                 "Aponte o projeto principal com --vault ou VAULT_PANEL_VAULT (ver local.env.example).")
    if a.modo == "serve":
        sys.exit(serve(a))
    html = a.html or os.path.join(VAULT, "_status.html")
    t0 = time.time()
    graph, gstate, gmsg, tgraph = None, "ausente", None, None
    if a.no_graph:
        model = build_model(a.no_history)
    else:   # o grafo (I/O no /mnt/c + networkx) roda em paralelo com o status
        box = {}

        def _g():
            tg = time.time()
            box["r"] = build_graph_safe(VAULT)
            box["t"] = time.time() - tg
        th = threading.Thread(target=_g, name="grafo")
        th.start()
        model = build_model(a.no_history)
        th.join()
        (graph, gstate, gmsg), tgraph = box["r"], box["t"]
    size = write_html(model, html, graph=graph, grafo_estado=gstate, grafo_msg=gmsg)
    if a.json:
        with open(a.json, "w", encoding="utf-8", errors="replace") as f:
            json.dump(model, f, ensure_ascii=False, indent=1)
    r = model["resumo"]
    por = " · ".join(f"{k} {v}" for k, v in sorted(r["specs_por_status"].items(), key=lambda kv: -kv[1]))
    print(f"vault_status: {r['specs_total']} specs ({r['specs_abertas']} abertas, {r['specs_arquivadas']} arquivadas;"
          f" {r['specs_paradas_30d']} paradas > {PARADA_DIAS} d)  [{por}]")
    print(f"  ADRs {r['adrs_total']} ({r['adrs_data_aproximada']} com data aproximada, {r['adrs_arquivados']}"
          f" arquivados) · notas {r['notas_total']} ({r['notas_por_tipo'].get('sessao', 0)} sessão,"
          f" {r['notas_por_tipo'].get('anotacao', 0)} anotação, {r['notas_consolidadas']} consolidadas)"
          f" + {r['notas_pendencias']} marcador{'es' if r['notas_pendencias'] != 1 else ''} de pendências · ligações spec↔ADR {r['ligacoes_spec_adr']},"
          f" spec↔nota {r['ligacoes_spec_nota']}")
    if model["com_historico"]:
        print(f"  histórico: {r.get('commits_specs_repo', 0)} commits de specs no repo,"
              f" {r.get('versoes_specs_lidas', 0)} versões lidas ({r.get('mudancas_mecanicas_ignoradas', 0)}"
              f" edições mecânicas em lote ignoradas); {r.get('commits_specs_vault', 0)} no git do vault")
    else:
        print("  histórico git: pulado (--no-history)")
    if a.no_graph:
        print("  grafo: pulado (--no-graph)")
    elif graph:
        mm = graph["metricas"]
        print(f"  grafo: {mm['nos']} nós · {mm['arestas']} arestas · {len(mm['nao_resolvidas'])} referências não"
              f" resolvidas · {len(mm['orfaos'])} órfãos ({tgraph:.1f} s, em paralelo)")
    else:
        print(f"  grafo {gstate}: {gmsg}", file=sys.stderr)
    if r.get("git_erros"):
        print(f"  ATENÇÃO: {len(r['git_erros'])} chamada(s) ao git falharam — histórico incompleto", file=sys.stderr)
    print(f"HTML: {html} ({size // 1024} KB)" + (f" · JSON: {a.json}" if a.json else ""))
    print(f"tempo: {time.time() - t0:.1f} s")


if __name__ == "__main__":
    main()
