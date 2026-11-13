#!/bin/bash
# Painel do vault AO VIVO (python3 vault_status.py serve) em http://localhost:${VAULT_PANEL_PORT:-8765}.
# O servidor escuta só em 127.0.0.1, observa o vault por polling (o Obsidian grava pelo Windows em /mnt/c,
# sem inotify) e empurra as mudanças ao navegador por SSE.
#
#   ./vault-panel.sh start    sobe em segundo plano (nohup; pid em /tmp/vault-panel.pid, log em /tmp/vault-panel.log)
#   ./vault-panel.sh stop     derruba
#   ./vault-panel.sh status   no ar? versões, CPU e custo do observador
#   ./vault-panel.sh restart  stop + start
#   ./vault-panel.sh open     sobe se preciso e abre no navegador do Windows a página única (/: grafo + specs)
#   ./vault-panel.sh open completo   idem, mas o painel completo antigo (/completo)
#   ./vault-panel.sh ensure   para hook: idempotente, silencioso, < 1 s, sempre sai 0
#
# VAULT_PANEL_PORT = porta (padrão 8765) · VAULT_PANEL_VAULT = outro vault (padrão: o do vault_status.py)
# Porta diferente da 8765 = instância própria: pid/log/lock em /tmp/vault-panel-<porta>.* (não mexe na 8765).
set -uo pipefail

ROOT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
# configuração local (caminhos do seu vault; fora do git): ver local.env.example
if [[ -f "$ROOT_DIR/local.env" ]]; then set -a; . "$ROOT_DIR/local.env"; set +a; fi
PORT="${VAULT_PANEL_PORT:-8765}"
if [[ ! "$PORT" =~ ^[0-9]+$ ]]; then
  echo "VAULT_PANEL_PORT inválida: $PORT" >&2
  [[ "${1:-}" == "ensure" ]] && exit 0
  exit 2
fi
if [[ "$PORT" == "8765" ]]; then
  BASE=/tmp/vault-panel
else
  BASE="/tmp/vault-panel-${PORT}"
fi
PIDFILE="${BASE}.pid"
LOGFILE="${BASE}.log"
LOCKFILE="${BASE}.lock"
BUSYFILE="${BASE}.ocupada"     # aviso já registrado: porta tomada por outro processo (o ensure não repete)
URL="http://localhost:${PORT}"
HEALTH="http://127.0.0.1:${PORT}/healthz"

healthy() {   # $1 = timeout em s
  curl -fsS -m "${1:-1}" -o /dev/null "$HEALTH" 2>/dev/null
}

port_open() {   # alguém aceita conexão em 127.0.0.1:$PORT? (instantâneo: recusa ou aceita na hora)
  (exec 3<>"/dev/tcp/127.0.0.1/${PORT}") 2>/dev/null
}

is_panel() {   # $1 = pid, $2 = "estrito" (exige --port $PORT) ou "solto" (--port ausente também vale)
  local pid="$1" cmd port
  [[ "$pid" =~ ^[0-9]+$ ]] || return 1
  [[ -r "/proc/$pid/cmdline" ]] || return 1
  cmd="$(tr '\0' ' ' < "/proc/$pid/cmdline" 2>/dev/null)"
  [[ "$cmd" == *vault_status.py* && " $cmd " == *" serve "* ]] || return 1
  if [[ "$cmd" =~ --port[=\ ]([0-9]+) ]]; then
    port="${BASH_REMATCH[1]}"
    [[ "$port" == "$PORT" ]]
    return
  fi
  [[ "${2:-estrito}" == "solto" ]]
}

live_pid() {   # pid do pidfile, se o processo existe E é o painel desta porta; pidfile velho é apagado
  local pid
  [[ -f "$PIDFILE" ]] || return 1
  pid="$(cat "$PIDFILE" 2>/dev/null)"
  if [[ "$pid" =~ ^[0-9]+$ ]] && kill -0 "$pid" 2>/dev/null && is_panel "$pid" estrito; then
    echo "$pid"
    return 0
  fi
  rm -f "$PIDFILE"   # processo morto, ou o PID foi reaproveitado por outro programa
  return 1
}

pick_python() {   # interpretador com networkx (o grafo precisa): o do sistema não tem, e o atalho do Windows
                  # (wsl.exe sem shell de login) não herda o venv no PATH — find_spec, sem importar: rápido p/ o ensure
  local cand
  for cand in ${VAULT_PANEL_PYTHON:+"$VAULT_PANEL_PYTHON"} "$ROOT_DIR/.venv/bin/python3" python3; do
    "$cand" -c 'import importlib.util as u, sys; sys.exit(u.find_spec("networkx") is None)' >/dev/null 2>&1 \
      && { echo "$cand"; return 0; }
  done
  echo python3   # nenhum tem: sobe assim mesmo (o grafo aparece como indisponível, com a instrução)
}

spawn() {   # sobe o servidor em segundo plano (sem esperar)
  local args=(serve --port "$PORT")
  [[ -n "${VAULT_PANEL_VAULT:-}" ]] && args+=(--vault "$VAULT_PANEL_VAULT")
  [[ -n "${VAULT_PANEL_NO_STATIC:-}" ]] && args+=(--no-static)   # não grava o retrato <projeto>/_status.html
  # log não cresce sem limite: acima de 2 MB recomeça
  [[ -f "$LOGFILE" && $(stat -c %s "$LOGFILE" 2>/dev/null || echo 0) -gt 2097152 ]] && : > "$LOGFILE"
  nohup "$(pick_python)" "$ROOT_DIR/vault_status.py" "${args[@]}" >>"$LOGFILE" 2>&1 </dev/null 9>&- &
  echo $! > "$PIDFILE"
}

busy_msg() {
  echo "a porta $PORT está ocupada por outro processo que não responde como o painel (veja: ss -ltnp 'sport = :$PORT')"
}

start() {
  local pid
  if healthy 1; then
    rm -f "$BUSYFILE"
    echo "já está no ar: $URL"
    return 0
  fi
  if pid="$(live_pid)"; then
    echo "processo $pid existe mas ainda não responde (subindo?); aguardando…"
  elif port_open; then
    busy_msg >&2
    return 1
  else
    rm -f "$BUSYFILE"
    spawn
    pid="$(cat "$PIDFILE")"
    echo "subindo o painel (pid $pid, log $LOGFILE)…"
  fi
  for _ in $(seq 1 60); do
    if healthy 1; then
      echo "no ar: $URL"
      return 0
    fi
    kill -0 "$pid" 2>/dev/null || { echo "o servidor saiu; últimas linhas do log:" >&2; tail -n 15 "$LOGFILE" >&2; rm -f "$PIDFILE"; return 1; }
    sleep 0.5
  done
  echo "não respondeu em 30 s; veja $LOGFILE" >&2
  return 1
}

stop() {
  local pid
  if ! pid="$(live_pid)"; then
    # sem pidfile válido: talvez tenha subido de outro jeito — pergunta o pid ao próprio servidor
    pid="$(curl -fsS -m 1 "$HEALTH" 2>/dev/null | python3 -c 'import json,sys; print(json.load(sys.stdin)["pid"])' 2>/dev/null)"
    if [[ -z "$pid" ]]; then
      echo "não está no ar"
      return 0
    fi
    if ! is_panel "$pid" solto; then
      echo "o pid $pid informado na porta $PORT não é um 'vault_status.py serve' desta porta — não mexo nele" >&2
      return 1
    fi
  fi
  kill -TERM "$pid" 2>/dev/null
  for _ in $(seq 1 20); do
    kill -0 "$pid" 2>/dev/null || break
    sleep 0.25
  done
  if kill -0 "$pid" 2>/dev/null; then
    if is_panel "$pid" solto; then   # nunca SIGKILL num pid que não é (mais) o painel
      kill -KILL "$pid" 2>/dev/null
      echo "derrubado à força (pid $pid)"
    else
      echo "o pid $pid não é mais o painel; nada a derrubar" >&2
    fi
  else
    echo "parado (pid $pid)"
  fi
  rm -f "$PIDFILE"
}

status() {
  local body pid
  if body="$(curl -fsS -m 2 "$HEALTH" 2>/dev/null)"; then
    echo "no ar: $URL"
    printf '%s' "$body" | python3 -c '
import json, sys
h = json.load(sys.stdin)
g, o = h.get, h.get("observador", {})
print("  pid %s · vault %s · no ar há %s s" % (g("pid"), g("vault"), g("uptime_s")))
print("  status v%s (gerado %s, reconstrução %s s)" % (g("versao_status"), g("gerado_em"), g("status_rebuild_s")))
if g("status_erro"):
    print("  ATENÇÃO: a última reconstrução do status falhou em %s: %s" % (g("status_erro_em"), g("status_erro")))
print("  grafo v%s [%s] (gerado %s, reconstrução %s s)%s" % (g("versao_grafo"), g("grafo_estado"), g("grafo_gerado_em"), g("grafo_rebuild_s"),
      (" — " + g("grafo_msg")) if g("grafo_msg") else ""))
print("  CPU do processo: %s%% no último minuto · %s s no total" % (g("cpu_pct_60s"), g("cpu_processo_s")))
print("  observador: %s arquivos · %s varreduras rápidas (%s ms, %s ms de CPU) · %s completas (%s ms, %s ms de CPU) · %s erros" % (
    o.get("arquivos"), o.get("rapidas"), o.get("rapida_parede_ms"), o.get("rapida_cpu_ms"),
    o.get("completas"), o.get("completa_parede_ms"), o.get("completa_cpu_ms"), o.get("erros")))
' 2>/dev/null || printf '  %s\n' "$body"
    return 0
  fi
  if pid="$(live_pid)"; then
    echo "processo $pid existe mas não responde em $HEALTH (subindo, ou travado — veja $LOGFILE)"
    return 1
  fi
  if port_open; then
    busy_msg
    return 1
  fi
  echo "não está no ar (./vault-panel.sh start)"
  return 3
}

open_browser() {
  start || return 1
  if command -v wslview >/dev/null 2>&1; then
    wslview "$URL" >/dev/null 2>&1 && return 0
  fi
  if command -v cmd.exe >/dev/null 2>&1; then
    # cd para /mnt/c: o cmd.exe reclama de diretório atual UNC (\\wsl$…)
    (cd /mnt/c 2>/dev/null; cmd.exe /c start "" "$URL" >/dev/null 2>&1) && return 0
  fi
  if command -v xdg-open >/dev/null 2>&1; then
    xdg-open "$URL" >/dev/null 2>&1 && return 0
  fi
  echo "abra no navegador: $URL"
}

ensure() {
  # para hook: nunca bloqueia nem falha. Porta respondendo = nada a fazer; senão sobe em segundo plano.
  if healthy 0.4; then
    rm -f "$BUSYFILE" 2>/dev/null
    return 0
  fi
  (
    command -v flock >/dev/null 2>&1 && { exec 9>"$LOCKFILE"; flock -n 9 || exit 0; }
    live_pid >/dev/null && exit 0   # já está subindo (ou travado): não sobe outro
    if port_open; then              # porta tomada por outro processo: subir só geraria "Address already in use"
      if [[ ! -f "$BUSYFILE" ]]; then
        echo "[$(date '+%F %T')] ensure: $(busy_msg); o painel não foi iniciado" >>"$LOGFILE"
        : > "$BUSYFILE"
      fi
      exit 0
    fi
    rm -f "$BUSYFILE"
    spawn
  ) >/dev/null 2>&1
  return 0
}

case "${1:-}" in
  start)   start ;;
  stop)    stop ;;
  status)  status ;;
  restart) stop; start ;;
  open)    [ "${2:-}" == "completo" ] && URL="$URL/completo"; open_browser ;;
  ensure)  ensure; exit 0 ;;
  *)
    echo "uso: $0 {start|stop|status|restart|open [completo]|ensure}" >&2
    exit 2 ;;
esac
