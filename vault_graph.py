#!/usr/bin/env python3
"""Graph engineering de um vault do Obsidian — métricas + mapa interativo.

Uso:
    python3 vault_graph.py                 # relatório no stdout + _graph.html no vault
    python3 vault_graph.py --all           # inclui ADRs órfãos no HTML (pesado)
    python3 vault_graph.py --gexf out.gexf # export para Gephi
    python3 vault_graph.py --html PATH     # destino alternativo do HTML

O que entra no graph: 00_Context (exceto dados/ — fichas geradas), 01_Specs,
02_Memory (ADRs + hooks), 03_Glossary, CLAUDE.md do vault, e os índices de
memória do agente (MEMORY.md / MEMORY_HISTORICO.md / adrs-*.md). raw/ e
_inbox/ ficam fora por regra do vault.

Arestas reconhecidas:
    [[wikilink]] · [texto](caminho.md) · `caminho/Doc.md` em backtick ·
    ADR-NNN (citação textual) · "- NNN hook" nos índices de memória.

Métricas: links quebrados, docs órfãos, hubs, PageRank, componentes,
docs em status working, ADRs nunca citados.

Como biblioteca (aba Grafo do vault_status.py): build(vault=…) → graph_model(G, broken)
devolve o modelo serializável (nós, arestas, métricas completas), sem layout.
"""
import argparse
import html as html_mod
import json
import os
import re
import sys
from collections import defaultdict
from urllib.parse import unquote

import networkx as nx

# Projeto principal (pasta do vault cujas specs/ADRs o painel acompanha) e memória do agente: por ambiente
# (VAULT_PANEL_VAULT / VAULT_PANEL_MEMORY — o vault-panel.sh lê o local.env)
VAULT = os.path.abspath(os.path.expanduser(os.environ.get("VAULT_PANEL_VAULT") or "."))
VAULT_ROOT = os.path.dirname(VAULT)          # o vault do Obsidian inteiro (todos os projetos)
OBSIDIAN_GRAPH = os.path.join(VAULT_ROOT, ".obsidian", "graph.json")   # grupos de cor do grafo nativo
MEMORY_DIR = os.path.expanduser(os.environ.get("VAULT_PANEL_MEMORY") or "")   # vazio = sem memória do agente
EXCLUDE_DIRS = {"raw", "_inbox", "assets", ".obsidian", ".trash"}
# subpastas do projeto só com fichas geradas (fora do grafo) e os arquivos delas que entram assim mesmo, por ambiente:
# VAULT_PANEL_EXCLUDE="00_Context/gerados" e VAULT_PANEL_EXCLUDE_KEEP="_Indice.md" (vírgula separa vários)
EXCLUDE_SUBPATHS = {x.strip().strip("/") for x in (os.environ.get("VAULT_PANEL_EXCLUDE") or "").split(",") if x.strip()}
EXCLUDE_KEEP = {x.strip() for x in (os.environ.get("VAULT_PANEL_EXCLUDE_KEEP") or "").split(",") if x.strip()}

RE_WIKI = re.compile(r"\[\[([^\]|#]+)")
RE_MD = re.compile(r"\]\(([^)#\s]+\.md)\)")
RE_TICK = re.compile(r"`([\w][\w./ \-]*\.md)`")
RE_ADR = re.compile(r"\bADR[- ](\d{2,4})\b")
RE_MEMHOOK = re.compile(r"(?m)^\s*-\s+\**(\d{3,4})\b")
RE_STATUS_WORKING = re.compile(r"(?im)^status:\s*working|EM CONSTRU")
# Doc arquivado: frontmatter `status: arquivado` — fica no grafo (links não quebram), mas pintado de cinza e contado à parte.
RE_STATUS_ARCHIVED = re.compile(r"(?im)^status:\s*arquivado")
# Anexos (só no universo, como o "Anexos" do grafo do Obsidian): imagens, PDFs, áudio e vídeo que o Obsidian abre.
# Respeitam os "Arquivos excluídos" do próprio Obsidian (.obsidian/app.json → userIgnoreFilters, os de prefixo).
ATTACH_EXT = {".png", ".jpg", ".jpeg", ".gif", ".webp", ".svg", ".bmp", ".avif", ".pdf",
              ".mp4", ".webm", ".mov", ".mkv", ".ogv", ".mp3", ".wav", ".m4a", ".ogg", ".flac"}
ATTACH_SKIP_DIRS = {"raw", ".obsidian", ".trash", ".git", "node_modules"}
RE_EMBED_MD = re.compile(r"\]\(<?([^)>#]+?\.(?:png|jpe?g|gif|webp|svg|bmp|avif|pdf|mp4|webm|mov|mkv|ogv|mp3|wav|m4a|ogg|flac))>?\)", re.I)


def rel(path, vault=None):
    vault = vault or VAULT
    if path.startswith(vault):
        return os.path.relpath(path, vault)
    return "memoria/" + os.path.basename(path)


def collect_files(vault=None, memory_dir=None, excl_sub=None):
    """vault/memory_dir = None → os padrões (VAULT, MEMORY_DIR). O vault_status passa outro vault no --vault.
    excl_sub: subcaminhos (relativos ao vault) dos quais só o índice curado entra — padrão EXCLUDE_SUBPATHS."""
    vault = vault or VAULT
    excl_sub = EXCLUDE_SUBPATHS if excl_sub is None else excl_sub
    memory_dir = MEMORY_DIR if memory_dir is None else memory_dir
    files = []
    for root, dirs, names in os.walk(vault):
        dirs[:] = [d for d in dirs if d not in EXCLUDE_DIRS]
        r = os.path.relpath(root, vault)
        if any(r == s or r.startswith(s + "/") for s in excl_sub):
            # subpasta de fichas geradas: só os arquivos mantidos entram
            for n in names:
                if n in EXCLUDE_KEEP:
                    files.append(os.path.join(root, n))
            dirs[:] = []
            continue
        for n in names:
            if n.endswith(".md"):
                files.append(os.path.join(root, n))
    if memory_dir and os.path.isdir(memory_dir):
        for n in os.listdir(memory_dir):
            if n.endswith(".md"):
                files.append(os.path.join(memory_dir, n))
    return files


def obsidian_ignore(vault):
    """Prefixos de "Arquivos excluídos" do Obsidian (userIgnoreFilters sem os de regex, que começam com "/")."""
    try:
        with open(os.path.join(vault, ".obsidian", "app.json"), encoding="utf-8") as fh:
            d = json.load(fh)
    except (OSError, ValueError):
        return []
    return [f for f in d.get("userIgnoreFilters") or [] if isinstance(f, str) and f and not f.startswith("/")]


def collect_attachments(vault):
    """Anexos do vault (caminhos relativos), fora de raw/, .obsidian/, .trash/ e dos excluídos do Obsidian."""
    ign = obsidian_ignore(vault)
    out = []
    for dirpath, dirs, names in os.walk(vault):
        dirs[:] = [d for d in dirs if d not in ATTACH_SKIP_DIRS]
        r = os.path.relpath(dirpath, vault)
        r = "" if r == "." else r.replace(os.sep, "/") + "/"
        if r and any(r.startswith(f) for f in ign if f.endswith("/")):
            dirs[:] = []
            continue
        for n in names:
            if os.path.splitext(n)[1].lower() in ATTACH_EXT:
                rp = r + n
                if not any(rp == f or rp.startswith(f) for f in ign):
                    out.append(rp)
    return out


def node_kind(relpath):
    if relpath.startswith("memoria/"):
        return "memoria"
    if relpath.startswith("02_Memory/ADR-"):
        return "adr"
    if relpath.startswith("02_Memory/"):
        return "memoria"
    if relpath.startswith("01_Specs/"):
        return "spec"
    if relpath.startswith("00_Context/modulos/"):
        return "modulo"
    if relpath.startswith("00_Context/componentes/"):
        return "componente"
    if relpath.startswith("00_Context/engenharia/"):
        return "engenharia"
    if relpath.startswith("00_Context/"):
        return "contexto"
    if relpath.startswith("03_Glossary/"):
        return "glossario"
    return "outro"


def project_of(rp):
    """Universo: projeto = 1ª pasta do caminho; memória do agente e arquivos da raiz à parte."""
    if rp.startswith("memoria/"):
        return "memoria-agente"
    return rp.split("/", 1)[0] if "/" in rp else "(raiz)"


def local_of(rp):
    """Caminho dentro do projeto (o que node_kind/node_area entendem)."""
    p = project_of(rp)
    return rp if p in ("memoria-agente", "(raiz)") else rp[len(p) + 1:]


_MAIN = [None]   # projeto principal do universo (a memória do agente é dele; rótulo de área com a área interna)


def build(vault=None, memory_dir=None, universe=False, attachments=False, main=None):
    """universe=True: vault = raiz do Obsidian (todos os projetos). Ids viram "Projeto/caminho"; o link
    resolve como no Obsidian (nome único no vault inteiro, desempate pela mesma pasta e depois pelo mesmo
    projeto) e ADR-NNN resolve dentro do PRÓPRIO projeto (cada vault numera os seus).
    attachments=True (só com universe): anexos viram nós (tipo "anexo"), ligados por ![[x.png]], [[x.pdf]] e
    ![](caminho/x.png); anexo que ninguém cita fica solto, como no Obsidian."""
    vault = vault or (VAULT_ROOT if universe else VAULT)
    main = main or os.path.basename(VAULT)
    _MAIN[0] = main
    files = collect_files(vault, memory_dir,
                          excl_sub={main + "/" + x for x in EXCLUDE_SUBPATHS} if universe else None)
    proj = project_of if universe else (lambda _rp: "")
    loc = local_of if universe else (lambda rp: rp)
    by_base = defaultdict(list)   # basename sem .md, lowercase -> [relpath]
    by_relpath = {}
    adr_by_num = {}
    contents = {}
    for f in files:
        rp = rel(f, vault)
        by_relpath[rp.lower()] = rp
        base = os.path.splitext(os.path.basename(f))[0].lower()
        by_base[base].append(rp)
        m = re.match(r"ADR-0*(\d+)", os.path.basename(f))
        if m and loc(rp).startswith("02_Memory/"):
            adr_by_num[(proj(rp), int(m.group(1))) if universe else int(m.group(1))] = rp
        try:
            contents[rp] = open(f, encoding="utf-8", errors="replace").read()
        except OSError:
            contents[rp] = ""

    G = nx.DiGraph()
    for rp in contents:
        G.add_node(rp, kind=node_kind(loc(rp)), working=bool(RE_STATUS_WORKING.search(contents[rp][:400])),
                   archived=bool(RE_STATUS_ARCHIVED.search(contents[rp][:400])))

    att = collect_attachments(vault) if (universe and attachments) else []
    att_by_rel = {a.lower(): a for a in att}
    att_by_name = defaultdict(list)
    for a in att:
        att_by_name[os.path.basename(a).lower()].append(a)
        G.add_node(a, kind="anexo", working=False, archived=False)

    def resolve_att(target, src):
        t = unquote(target.strip()).replace("\\", "/")
        while t.startswith("./"):
            t = t[2:]
        if "/" in t:
            for cand in (t, proj(src) + "/" + t, os.path.normpath(os.path.join(os.path.dirname(src), t)).replace(os.sep, "/")):
                if cand.lower() in att_by_rel:
                    return att_by_rel[cand.lower()]
        hits = att_by_name.get(os.path.basename(t).lower())
        if not hits:
            return None
        if len(hits) == 1:
            return hits[0]
        same = [h for h in hits if os.path.dirname(h) == os.path.dirname(src)] or [h for h in hits if proj(h) == proj(src)]
        return (same or hits)[0]

    broken = []

    PLACEHOLDER = re.compile(r"NNN|YYYY|AAAA|slug|<|\bX\.md|ADR-123\b")
    CODE_PREFIX = ("frontend/", "backend/", "mobile/", "src/", "app/", "lib/")   # caminho de código, não doc

    def is_noise(t):
        return bool(PLACEHOLDER.search(t)) or t.startswith(CODE_PREFIX)

    def resolve(target, src):
        t = target.strip().rstrip("\\").replace("\\", "/")
        if "/" in t:
            # forma caminho (com ou sem .md): relativo à raiz do vault ou ao dir do src
            p = t if t.endswith(".md") else t + ".md"
            cand = p.lstrip("./").lower()
            if cand in by_relpath:
                return by_relpath[cand]
            if universe and proj(src) not in ("memoria-agente", "(raiz)"):
                cand2 = (proj(src) + "/" + cand).lower()          # caminho escrito a partir da raiz do projeto
                if cand2 in by_relpath:
                    return by_relpath[cand2]
            joined = os.path.normpath(os.path.join(os.path.dirname(src), p)).lower()
            if joined in by_relpath:
                return by_relpath[joined]
            t = os.path.splitext(os.path.basename(t))[0]
        elif t.endswith(".md"):
            if t.lower() in by_relpath:
                return by_relpath[t.lower()]
            t = os.path.splitext(t)[0]
        hits = by_base.get(t.lower())
        if not hits:
            return None
        if len(hits) == 1:
            return hits[0]
        same = [h for h in hits if os.path.dirname(h) == os.path.dirname(src)]
        if not same and universe:
            same = [h for h in hits if proj(h) == proj(src)]
        return (same or hits)[0]

    def link(a, b, explicit):
        """ex=True: ligação que o Obsidian também desenha ([[link]], [texto](x.md), ![[anexo]]); ex=False: citação
        (ADR-NNN, `caminho` em crase, "- NNN" dos índices de memória). A mesma dupla pelos dois jeitos = explícita."""
        if G.has_edge(a, b):
            if explicit:
                G[a][b]["ex"] = True
        else:
            G.add_edge(a, b, ex=explicit)

    for src, text in contents.items():
        explicit_t = set(RE_WIKI.findall(text)) | set(RE_MD.findall(text))
        if att:
            explicit_t |= set(RE_EMBED_MD.findall(text))
        targets = explicit_t | set(RE_TICK.findall(text))
        for t in targets:
            if is_noise(t) or t.startswith(("http", "mailto")):
                continue
            ex = t in explicit_t
            if att and os.path.splitext(t.strip())[1].lower() in ATTACH_EXT:
                dst = resolve_att(t, src)
                if dst:
                    link(src, dst, ex)
                else:
                    broken.append((src, t.strip()))
                continue
            dst = resolve(t, src)
            if dst and dst != src:
                link(src, dst, ex)
            elif dst is None:
                broken.append((src, t.strip()))
        nums = {int(n) for n in RE_ADR.findall(text)}
        if src.startswith("memoria/") or "/adrs-" in src or src.endswith(("MEMORY.md", "MEMORY_HISTORICO.md")):
            nums.update(int(n) for n in RE_MEMHOOK.findall(text))
        adr_proj = main if proj(src) == "memoria-agente" else proj(src)   # a memória do agente é do projeto principal
        for n in nums:
            dst = adr_by_num.get((adr_proj, n)) if universe else adr_by_num.get(n)
            if dst and dst != src:
                link(src, dst, False)
    return G, broken, adr_by_num


CTX_KINDS = ("modulo", "componente", "engenharia", "contexto", "glossario")


def _adr_num(n):
    """Número do ADR no nome; -1 quando não há (ex.: ADR-frontend-refactor-…): vai para o fim da lista."""
    m = re.search(r"ADR-0*(\d+)", n)
    return int(m.group(1)) if m else -1


def metrics(G, broken, pr):
    """Métricas do relatório, completas (sem o corte `top`) — base do report() e do graph_model()."""
    ctx = [n for n, d in G.nodes(data=True) if d["kind"] in CTX_KINDS]
    adrs = [n for n, d in G.nodes(data=True) if d["kind"] == "adr"]
    specs = [n for n, d in G.nodes(data=True) if d["kind"] == "spec"]
    comps = sorted(nx.connected_components(G.to_undirected()), key=len, reverse=True)
    archived = [n for n, d in G.nodes(data=True) if d.get("archived")]
    by_kind = {}
    for n in archived:
        by_kind[G.nodes[n]["kind"]] = by_kind.get(G.nodes[n]["kind"], 0) + 1
    return {
        "ctx": ctx, "adrs": adrs, "specs": specs,
        "orphan_ctx": sorted(n for n in ctx if G.in_degree(n) == 0 and not n.endswith("_INDEX.md")),
        "orphan_adr": sorted((n for n in adrs if G.in_degree(n) == 0), key=lambda n: -_adr_num(n)),
        "broken": broken,
        "hubs": sorted(ctx, key=lambda n: -(G.in_degree(n) + G.out_degree(n))),
        "pagerank_ctx": sorted(ctx, key=lambda n: -pr[n]),
        "comps": comps,
        "islands": [c for c in comps[1:] if len(c) > 1],
        "working": sorted(n for n, d in G.nodes(data=True) if d.get("working")),
        "archived": archived, "archived_by_kind": by_kind,
    }


def report(G, broken, adr_by_num, top=12):
    pr = nx.pagerank(G, alpha=0.85)
    m = metrics(G, broken, pr)
    ctx, adrs, specs = m["ctx"], m["adrs"], m["specs"]

    print(f"Vault graph: {G.number_of_nodes()} nós · {G.number_of_edges()} arestas")
    print(f"  contexto {len(ctx)} · ADRs {len(adrs)} · specs {len(specs)}")

    orphan_ctx = m["orphan_ctx"]
    print(f"\n■ Docs de contexto ÓRFÃOS (ninguém aponta): {len(orphan_ctx)}")
    for n in orphan_ctx[:top]:
        print(f"  - {n}")
    if len(orphan_ctx) > top:
        print(f"  … +{len(orphan_ctx)-top}")

    orphan_adr = m["orphan_adr"]
    print(f"\n■ ADRs nunca citados (nem por número): {len(orphan_adr)}  [mais recentes:]")
    for n in orphan_adr[:top]:
        print(f"  - {n}")

    print(f"\n■ Referências NÃO RESOLVIDAS no vault: {len(broken)}")
    print("  (mistura link quebrado real com referência a arquivo do repo/outro vault — conferir as que deviam ser docs daqui)")
    for src, t in broken[:top]:
        print(f"  - {src} → «{t}»")
    if len(broken) > top:
        print(f"  … +{len(broken)-top}")

    print("\n■ Hubs (grau total — candidatos a quebrar se crescerem):")
    for n in m["hubs"][:top]:
        print(f"  {G.in_degree(n)+G.out_degree(n):4d}  {n}  (in {G.in_degree(n)} / out {G.out_degree(n)})")

    print("\n■ PageRank top (o que o graph considera mais central):")
    for n in m["pagerank_ctx"][:top]:
        print(f"  {pr[n]:.4f}  {n}")

    comps, small = m["comps"], m["islands"]
    print(f"\n■ Componentes: {len(comps)} (maior: {len(comps[0])} nós)")
    if small:
        print("  Ilhas desconexas (>1 nó — contexto que agente não alcança por navegação):")
        for c in small[:8]:
            print(f"   - {len(c)} nós: {sorted(c)[:4]}")

    working = m["working"]
    print(f"\n■ Docs em status working/EM CONSTRUÇÃO: {len(working)}")
    for n in working[:top]:
        print(f"  - {n}")

    archived, by_kind = m["archived"], m["archived_by_kind"]
    print(f"\n■ Docs ARQUIVADOS (status: arquivado — não são contexto, só histórico): {len(archived)}"
          + (f"  {by_kind}" if by_kind else ""))
    return pr


def _sig(v):
    """PageRank com 4 algarismos significativos (o JSON não precisa de 17 casas)."""
    return float(f"{v:.4g}")


def node_label(n, kind):
    if kind == "anexo":
        return os.path.basename(n)          # anexo: com a extensão (foto.png ≠ foto.pdf)
    label = os.path.splitext(os.path.basename(n))[0]
    if kind == "adr":
        label = label.split("-2026")[0].split("-2025")[0]
    return label


def obsidian_groups(path=None):
    """Grupos de cor do grafo nativo (.obsidian/graph.json → colorGroups): [{query, cor, rotulo}], na ordem."""
    try:
        with open(path or OBSIDIAN_GRAPH, encoding="utf-8") as fh:
            d = json.load(fh)
    except (OSError, ValueError):
        return []
    out = []
    for g in d.get("colorGroups", []):
        q, rgb = g.get("query", ""), (g.get("color") or {}).get("rgb")
        if rgb is None:
            continue
        m = re.search(r'path:"?([^"\s]+?)/?"?(?:\s|$)', q)
        out.append({"query": q, "cor": "#%06x" % int(rgb), "rotulo": m.group(1) if m else q})
    return out


RE_OBS_TERM = re.compile(r'-?\([^()]*\)|-?\w+:"[^"]*"|-?\w+:\S+')


def obsidian_match(query, path):
    """Subconjunto da busca do Obsidian usado nos grupos: termos path:/file: (substring, sem caixa), '-' nega,
    (a OR b) agrupa; termos lado a lado = E."""
    fname = path.rsplit("/", 1)[-1].lower()
    pl = path.lower()

    def term(t):
        neg = t.startswith("-")
        t = t[1:] if neg else t
        if t.startswith("("):
            ok = any(term(x.strip()) for x in re.split(r"\s+OR\s+", t[1:-1]) if x.strip())
        else:
            k, _, v = t.partition(":")
            v = v.strip('"').lower()
            ok = (v in fname) if k == "file" else (v in pl)
        return ok != neg

    items = RE_OBS_TERM.findall(query)
    return bool(items) and all(term(x) for x in items)


def universe_area(rp):
    """Divisão por caminho no universo: no projeto principal, a área do vault_graph (módulo, specs, ADRs…); nos outros
    projetos, a 1ª pasta dentro do projeto."""
    p, lp = project_of(rp), local_of(rp)
    if p == _MAIN[0]:
        return p + " · " + node_area(lp)
    if p == "memoria-agente":
        return "memória do agente"
    if p == "(raiz)":
        return "raiz do vault"
    return p + " · " + lp.split("/")[0] if "/" in lp else p


def graph_model(G, broken, pr=None, top=30, universe=False, groups=None):
    """Modelo serializável (JSON) do grafo para o painel do vault_status.py (aba Grafo).

    nos:      id (= caminho relativo ao vault; "memoria/…" = memória do agente, fora do vault),
              rotulo, tipo, area, grau_in, grau_out, pagerank, working, arquivado
    arestas:  [índice_origem, índice_destino, explícita 1|0] sobre a lista `nos`, ordenadas (0 = citação:
              ADR-NNN, caminho em crase, índice de memória — o Obsidian não desenha)
    metricas: as do relatório, completas (listas de ids), mais hubs/PageRank com os valores.
    Não calcula layout: quem desenha é o d3-force no navegador.
    Arestas e referências não resolvidas saem ORDENADAS: a ordem de inserção vem de um set de strings
    (varia com o PYTHONHASHSEED), e o painel não pode mudar de ordem a cada processo. O report() do
    CLI segue com a ordem de antes."""
    pr = pr if pr is not None else nx.pagerank(G, alpha=0.85)
    m = metrics(G, broken, pr)
    nodes = list(G.nodes())
    idx = {n: i for i, n in enumerate(nodes)}
    nos = []
    for n in nodes:
        d = G.nodes[n]
        no = {"id": n, "caminho": n, "rotulo": node_label(n, d["kind"]), "tipo": d["kind"],
              "area": universe_area(n) if universe else node_area(n), "grau_in": G.in_degree(n),
              "grau_out": G.out_degree(n), "pagerank": _sig(pr.get(n, 0.0)), "working": bool(d.get("working")),
              "arquivado": bool(d.get("archived"))}
        if universe:
            no["projeto"] = project_of(n)
            no["og"] = next((i for i, g in enumerate(groups or []) if obsidian_match(g["query"], n)), -1) \
                if project_of(n) != "memoria-agente" else -1
        nos.append(no)
    comps = m["comps"]
    return {
        "nos": nos,
        "arestas": sorted([idx[a], idx[b], 1 if d.get("ex", True) else 0] for a, b, d in G.edges(data=True)),
        "metricas": {
            "nos": G.number_of_nodes(), "arestas": G.number_of_edges(),
            "contexto": len(m["ctx"]), "adrs": len(m["adrs"]), "specs": len(m["specs"]),
            "orfaos": m["orphan_ctx"],
            "adrs_nunca_citados": m["orphan_adr"],
            "nao_resolvidas": [{"origem": src, "alvo": t} for src, t in sorted(broken)],
            "hubs": [{"id": n, "grau": G.in_degree(n) + G.out_degree(n), "grau_in": G.in_degree(n),
                      "grau_out": G.out_degree(n)} for n in m["hubs"][:top]],
            "pagerank_top": [{"id": n, "pagerank": _sig(pr[n])} for n in m["pagerank_ctx"][:top]],
            "componentes": {"total": len(comps), "maior": len(comps[0]) if comps else 0,
                            "isolados": sum(1 for c in comps if len(c) == 1),
                            "ilhas": [sorted(c) for c in m["islands"]]},
            "working": m["working"],
            "arquivados": {"total": len(m["archived"]), "por_tipo": m["archived_by_kind"],
                           "ids": sorted(m["archived"])},
        },
    }


COLORS = {"modulo": "#4c9be8", "componente": "#7bc96f", "engenharia": "#e8a33d",
          "contexto": "#c678dd", "spec": "#e06c75", "adr": "#8a8f98",
          "glossario": "#56b6c2", "memoria": "#d19a66", "outro": "#aaaaaa"}


def node_area(rp):
    """Área para o filtro do HTML — grupos da estrutura real do vault."""
    if rp.startswith("00_Context/modulos/"):
        rest = rp[len("00_Context/modulos/"):]
        if "/" in rest:
            return rest.split("/")[0]          # subpasta de módulos = área
        return "modulos-core"                  # módulo solto em 00_Context/modulos/
    for prefix, area in (("00_Context/componentes/", "componentes"),
                         ("00_Context/engenharia/", "engenharia"),
                         ("00_Context/", "contexto-raiz"),
                         ("01_Specs/", "specs"),
                         ("02_Memory/ADR-", "adr"),
                         ("02_Memory/", "memoria"),
                         ("memoria/", "memoria"),
                         ("03_Glossary/", "glossario"),
                         ("03_QA/", "qa")):
        if rp.startswith(prefix):
            return area
    return "outro"


def write_html(G, pr, path, include_orphan_adrs=False):
    keep = []
    for n, d in G.nodes(data=True):
        if d["kind"] == "adr" and not include_orphan_adrs and G.in_degree(n) == 0:
            continue
        keep.append(n)
    idx = {n: i for i, n in enumerate(keep)}
    # layout pré-calculado como warm start — o d3-force do browser só acomoda
    # (alpha baixo), em vez de estabilizar do zero com canvas em branco.
    sub = G.subgraph(keep).to_undirected()
    pos = nx.spring_layout(sub, k=2.2 / max(1, len(keep)) ** 0.5, iterations=80, seed=42)
    SCALE = 1600
    nodes = []
    for n in keep:
        d = G.nodes[n]
        deg = G.in_degree(n) + G.out_degree(n)
        label = os.path.splitext(os.path.basename(n))[0]
        if d["kind"] == "adr":
            label = label.split("-2026")[0].split("-2025")[0]
        nodes.append({"l": label, "c": "#e5c07b" if d.get("working") else ("#555a60" if d.get("archived") else COLORS[d["kind"]]),
                      "v": max(1, deg), "a": node_area(n),
                      "t": f"{n} · in {G.in_degree(n)} out {G.out_degree(n)} · pr {pr.get(n, 0):.4f}",
                      "x": round(pos[n][0] * SCALE), "y": round(pos[n][1] * SCALE)})
    links = [[idx[a], idx[b]] for a, b in G.edges() if a in idx and b in idx]
    legend = "".join(f'<span><i style="background:{c}"></i>{k}</span>' for k, c in COLORS.items())
    page = HTML_TEMPLATE.replace("__LEGEND__", legend + '<span><i style="background:#e5c07b"></i>working</span><span><i style="background:#555a60"></i>arquivado</span>') \
        .replace("__NODES__", json.dumps(nodes, separators=(",", ":"))) \
        .replace("__LINKS__", json.dumps(links, separators=(",", ":")))
    open(path, "w", encoding="utf-8").write(page)
    print(f"\nHTML: {path}  ({len(nodes)} nós, {len(links)} arestas, {os.path.getsize(path)//1024} KB)")


HTML_TEMPLATE = """<!DOCTYPE html><html><head><meta charset="utf-8"><title>Vault graph</title>
<script src="https://cdnjs.cloudflare.com/ajax/libs/d3/7.8.5/d3.min.js"></script>
<style>html,body{margin:0;height:100%;overflow:hidden;background:#16181d;color:#ccc;font:13px sans-serif}
canvas{display:block;cursor:grab}canvas:active{cursor:grabbing}
#legend{position:fixed;bottom:8px;left:8px;background:#22252bd0;padding:7px 11px;border-radius:6px;z-index:9;pointer-events:none}
#legend span{display:inline-block;margin-right:10px}#legend i{display:inline-block;width:10px;height:10px;border-radius:50%;margin-right:4px}
#tip{position:fixed;display:none;background:#22252bee;border:1px solid #444;padding:5px 9px;border-radius:5px;z-index:10;pointer-events:none;max-width:480px}
#panel{position:fixed;top:8px;right:8px;width:238px;background:#1d2026ee;border:1px solid #333;border-radius:8px;z-index:9;user-select:none}
#panel h4{margin:0;padding:8px 12px;cursor:pointer;font-size:13px;color:#dde}
#panel .body{padding:2px 12px 10px;display:none}#panel.open .body{display:block}
#panel h5{margin:10px 0 4px;font-size:11px;text-transform:uppercase;letter-spacing:.5px;color:#8a93a5}
#panel label{display:flex;align-items:center;justify-content:space-between;margin:5px 0;font-size:12px;gap:8px}
#panel input[type=range]{width:120px;accent-color:#4c9be8}
#panel select,#panel input[type=text]{width:100%;background:#14161b;color:#ccc;border:1px solid #3a3f4a;border-radius:4px;padding:4px 6px;margin:3px 0;font-size:12px;box-sizing:border-box}
#count{font-size:11px;color:#8a93a5;margin-top:4px}</style>
</head><body>
<div id="legend">__LEGEND__</div><div id="tip"></div>
<div id="panel" class="open"><h4 onclick="panel.classList.toggle('open')">⚙ Filtros e exibição</h4><div class="body">
 <h5>Filtro</h5>
 <select id="fArea"><option value="">todas as áreas</option></select>
 <input id="fBusca" type="text" placeholder="buscar módulo/feature… (ex.: login)">
 <label><span>incluir vizinhos do recorte</span><input id="fViz" type="checkbox" checked></label>
 <div id="count"></div>
 <h5>Nós e linhas</h5>
 <label><span>tamanho dos nós</span><input id="sNode" type="range" min="0.3" max="3" step="0.1" value="1"></label>
 <label><span>espessura da linha</span><input id="sLw" type="range" min="0.2" max="3" step="0.1" value="0.7"></label>
 <label><span>opacidade da linha</span><input id="sLo" type="range" min="0.05" max="1" step="0.05" value="0.5"></label>
 <label><span>setas</span><input id="sArrow" type="checkbox"></label>
 <h5>Texto</h5>
 <label><span>quantidade</span><input id="sTxt" type="range" min="0" max="1" step="0.05" value="0.45"></label>
 <label><span>tamanho</span><input id="sTs" type="range" min="6" max="20" step="1" value="11"></label>
 <h5>Forças</h5>
 <label><span>repulsão</span><input id="sRep" type="range" min="5" max="200" step="5" value="42"></label>
 <label><span>distância do link</span><input id="sDist" type="range" min="20" max="220" step="5" value="70"></label>
 <label><span>força central</span><input id="sCen" type="range" min="0" max="0.08" step="0.005" value="0.015"></label>
</div></div>
<canvas id="c"></canvas><script>
const N=__NODES__,L=__LINKS__;
const links=L.map(([s,t])=>({source:s,target:t}));
const adj=N.map(()=>new Set());links.forEach((l,j)=>{adj[l.source].add(l.target);adj[l.target].add(l.source)});
const cv=document.getElementById('c'),tip=document.getElementById('tip'),panel=document.getElementById('panel'),dpr=devicePixelRatio||1;
let W,H;function size(){W=innerWidth;H=innerHeight;cv.width=W*dpr;cv.height=H*dpr;cv.style.width=W+'px';cv.style.height=H+'px'}
size();addEventListener('resize',()=>{size();draw()});
const ctx=cv.getContext('2d');
N.forEach((n,i)=>{n.index=i;n.r0=3+Math.sqrt(n.v)*1.35});
const S={node:1,lw:.7,lo:.5,arrow:false,txt:.45,ts:11,rep:42,dist:70,cen:.015};
let tf=d3.zoomIdentity.translate(innerWidth/2,innerHeight/2).scale(.35),hover=null;
let vis=N.map(()=>true),vlinks=links,vnodes=N;
const sim=d3.forceSimulation(N)
 .force('link',d3.forceLink(links).distance(S.dist).strength(.4))
 .force('charge',d3.forceManyBody().strength(-S.rep).theta(.9).distanceMax(700))
 .force('x',d3.forceX(0).strength(S.cen)).force('y',d3.forceY(0).strength(S.cen))
 .velocityDecay(.55).alpha(.25).alphaDecay(.028).on('tick',draw);
function applyFilter(){
 const area=fArea.value,q=fBusca.value.trim().toLowerCase(),viz=fViz.checked;
 if(!area&&!q){vis=N.map(()=>true)}
 else{
  const base=N.map(n=>(!area||n.a===area)&&(!q||n.l.toLowerCase().includes(q)||n.t.toLowerCase().includes(q)));
  vis=base.slice();
  if(viz)N.forEach((n,i)=>{if(base[i])adj[i].forEach(j=>vis[j]=true)});
 }
 vnodes=N.filter((n,i)=>vis[i]);
 vlinks=links.filter(l=>vis[l.source.index]&&vis[l.target.index]);
 sim.nodes(vnodes);sim.force('link').links(vlinks);
 sim.alpha(.35).restart();
 count.textContent=vnodes.length+' nós · '+vlinks.length+' arestas';
}
function applyForces(){
 sim.force('link').distance(S.dist);
 sim.force('charge').strength(-S.rep);
 sim.force('x').strength(S.cen);sim.force('y').strength(S.cen);
 sim.alpha(.3).restart();
}
function draw(){
 ctx.save();ctx.clearRect(0,0,cv.width,cv.height);ctx.scale(dpr,dpr);
 ctx.translate(tf.x,tf.y);ctx.scale(tf.k,tf.k);
 const hl=hover!=null&&vis[hover],nb=hl?adj[hover]:null;
 ctx.lineWidth=S.lw/tf.k;
 ctx.beginPath();
 for(const l of vlinks){if(hl&&l.source.index!==hover&&l.target.index!==hover)continue;
  ctx.moveTo(l.source.x,l.source.y);ctx.lineTo(l.target.x,l.target.y)}
 ctx.strokeStyle=hl?'#8b93a3':'#3a3f4a';ctx.globalAlpha=hl?.9:S.lo;ctx.stroke();
 if(hl){ctx.beginPath();
  for(const l of vlinks){if(l.source.index===hover||l.target.index===hover)continue;
   ctx.moveTo(l.source.x,l.source.y);ctx.lineTo(l.target.x,l.target.y)}
  ctx.strokeStyle='#3a3f4a';ctx.globalAlpha=Math.min(.12,S.lo);ctx.stroke()}
 if(S.arrow){ctx.globalAlpha=hl?.9:S.lo;ctx.fillStyle=hl?'#8b93a3':'#3a3f4a';
  for(const l of vlinks){if(hl&&l.source.index!==hover&&l.target.index!==hover)continue;
   const dx=l.target.x-l.source.x,dy=l.target.y-l.source.y,dd=Math.hypot(dx,dy)||1;
   const tx=l.target.x-dx/dd*(l.target.r0*S.node+3),ty=l.target.y-dy/dd*(l.target.r0*S.node+3);
   const a=Math.atan2(dy,dx),s=4/tf.k+1.5;
   ctx.beginPath();ctx.moveTo(tx,ty);
   ctx.lineTo(tx-s*Math.cos(a-.4),ty-s*Math.sin(a-.4));
   ctx.lineTo(tx-s*Math.cos(a+.4),ty-s*Math.sin(a+.4));ctx.fill()}}
 for(const n of vnodes){const i=n.index,dim=hl&&i!==hover&&!nb.has(i);
  ctx.globalAlpha=dim?.15:1;ctx.beginPath();
  ctx.arc(n.x,n.y,n.r0*S.node,0,6.2832);ctx.fillStyle=n.c;ctx.fill();
  if(i===hover){ctx.lineWidth=2/tf.k;ctx.strokeStyle='#fff';ctx.stroke()}}
 const zk=tf.k,thr=2.2*(1-S.txt);
 ctx.fillStyle='#cfd3da';ctx.textAlign='center';ctx.font=(S.ts/zk)+'px sans-serif';
 for(const n of vnodes){const i=n.index;
  const effZ=zk+Math.sqrt(n.v)/9;
  const rel=hl&&(i===hover||nb.has(i));
  if(!rel&&(hl||effZ<thr))continue;
  ctx.globalAlpha=rel?1:Math.max(0,Math.min(1,(effZ-thr)*2.5));
  ctx.fillText(n.l,n.x,n.y+n.r0*S.node+S.ts/zk+2/zk)}
 ctx.restore()}
function pick(ev){const p=tf.invert(d3.pointer(ev,cv));const n=sim.find(p[0],p[1],18/tf.k);return n&&vis[n.index]?n:null}
d3.select(cv).call(d3.drag().container(cv)
 .subject(ev=>pick(ev.sourceEvent||ev))
 .on('start',ev=>{if(!ev.active)sim.alphaTarget(.28).restart();ev.subject.fx=ev.subject.x;ev.subject.fy=ev.subject.y})
 .on('drag',ev=>{const p=tf.invert(d3.pointer(ev.sourceEvent,cv));ev.subject.fx=p[0];ev.subject.fy=p[1]})
 .on('end',ev=>{if(!ev.active)sim.alphaTarget(0);ev.subject.fx=null;ev.subject.fy=null}))
 .call(d3.zoom().scaleExtent([.05,8]).filter(ev=>ev.type==='wheel'||!pick(ev))
 .on('zoom',ev=>{tf=ev.transform;draw()}));
cv.addEventListener('mousemove',ev=>{const n=pick(ev);const i=n?n.index:null;
 if(i!==hover){hover=i;draw()}
 if(n){tip.style.display='block';tip.style.left=(ev.clientX+14)+'px';tip.style.top=(ev.clientY+10)+'px';tip.textContent=n.t}
 else tip.style.display='none'});
cv.addEventListener('mouseleave',()=>{hover=null;tip.style.display='none';draw()});
[...new Set(N.map(n=>n.a))].sort().forEach(a=>{const o=document.createElement('option');o.value=a;o.textContent=a;fArea.appendChild(o)});
fArea.onchange=applyFilter;fViz.onchange=applyFilter;
let deb;fBusca.oninput=()=>{clearTimeout(deb);deb=setTimeout(applyFilter,220)};
const bind=(el,k,fn)=>{el.oninput=()=>{S[k]=el.type==='checkbox'?el.checked:+el.value;(fn||draw)()}};
bind(sNode,'node');bind(sLw,'lw');bind(sLo,'lo');bind(sArrow,'arrow');bind(sTxt,'txt');bind(sTs,'ts');
bind(sRep,'rep',applyForces);bind(sDist,'dist',applyForces);bind(sCen,'cen',applyForces);
count.textContent=N.length+' nós · '+links.length+' arestas';
draw();
</script></body></html>"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--html", default=os.path.join(VAULT, "_graph.html"))
    ap.add_argument("--all", action="store_true", help="inclui ADRs órfãos no HTML")
    ap.add_argument("--gexf", help="exporta GraphML/GEXF p/ Gephi")
    a = ap.parse_args()
    G, broken, adr_by_num = build()
    pr = report(G, broken, adr_by_num)
    write_html(G, pr, a.html, include_orphan_adrs=a.all)
    if a.gexf:
        nx.write_gexf(G, a.gexf)
        print(f"GEXF: {a.gexf}")


if __name__ == "__main__":
    main()
