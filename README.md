# AI Second Brain

A live dashboard for an **Obsidian vault used as the memory of an AI coding agent**: specs, decision records (ADRs),
session notes and a 3D graph of the whole vault, updated as you write.

Built by [bi19](https://bi19.app). Interface in Portuguese (pt-BR).

## What it shows

- **Graph** — the whole vault as a slowly drifting 3D universe (Obsidian-like 2D physics with a limited 3D sway).
  One color per project (click the dot to change it); show/hide projects, attachments, uncited ADRs and
  number-only citations; orphans orbit in a ring around the core; center, link and repel forces like Obsidian's.
- **Specs** — kanban (*Not started → In progress → Done*) or a progress table with status KPIs, criteria
  checkboxes and stale-spec warnings.
- **Timeline** — one lane per spec, colored by status over time (status colors are editable).
- **ADRs** — per day/week as stacked bars, a calendar heatmap or lines (per period or cumulative), by status or module.
- **Notes** — session notes and free-form notes over time.
- **Project switcher** — any project folder of the vault with `01_Specs/` or `02_Memory/ADR-*.md`.

Everything runs locally: a small Python server (standard library + networkx) on `127.0.0.1`.

## Requirements

- **Python 3.9+**
- **networkx** (installed below) — without it the panel still works, but the Graph tab shows a notice
- **git** — optional, only for the spec history/timeline
- A modern browser (Chrome, Edge, Firefox, Safari). Internet access the first time, to load d3 from cdnjs

## Installation

### 1. Get the code

```bash
git clone https://github.com/bi19andre/AI-Second-Brain.git
cd AI-Second-Brain
```

### 2. Create a virtual environment and install networkx

Linux / macOS / WSL:

```bash
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
```

`vault-panel.sh` picks `./.venv/bin/python3` automatically.

### 3. Configure your vault

```bash
cp local.env.example local.env
```

Edit `local.env` (it is git-ignored):

| Variable | Required | What it is |
|---|---|---|
| `VAULT_PANEL_VAULT` | yes | **Main project**: the vault folder whose specs/ADRs you track (has `01_Specs/` and/or `02_Memory/`). Its **parent** is treated as the whole Obsidian vault — every sibling folder becomes a project in the graph. |
| `VAULT_PANEL_MEMORY` | no | Folder with your AI agent's memory notes (`*.md`). They join the graph as "agent memory". |
| `VAULT_PANEL_REPO` | no | A git repo that keeps a synced copy of the vault under `docs/vault/<project>/`. Enables the spec history (timeline, sparklines). |
| `VAULT_PANEL_REPO_VAULT` | no | Path of that copy inside the repo, if not `docs/vault/<project>`. |
| `VAULT_PANEL_EXCLUDE` / `VAULT_PANEL_EXCLUDE_KEEP` | no | Subfolders of generated files to leave out of the graph (comma-separated), and file names inside them to keep. |
| `VAULT_PANEL_MODULES` | no | Path to a module-synonyms file (default `./local.modules.json`, see `local.modules.example.json`). |
| `VAULT_PANEL_PYTHON` | no | Python to use, if not `./.venv/bin/python3`. |
| `VAULT_PANEL_PORT` | no | Port (default `8765`). |
| `VAULT_PANEL_NO_STATIC` | no | `1` = don't write the static snapshot `<project>/_status.html` into the vault. |

Example vault layout:

```
ObsidianVault/            ← the whole vault (parent folder)
├── MyProject_dev/        ← VAULT_PANEL_VAULT
│   ├── 00_Context/_INDEX.md
│   ├── 01_Specs/*.md
│   ├── 02_Memory/ADR-0001-some-decision.md
│   ├── 02_Memory/_inbox/*.md
│   └── 04_Anotações/*.md
└── OtherProject_dev/     ← shows up in the graph and in the project switcher
```

### 4. Run

```bash
./vault-panel.sh open
```

This starts the live panel in the background and opens `http://localhost:8765` (or your port) in the browser.

| Command | Does |
|---|---|
| `./vault-panel.sh start` | start in the background (pid/log in `/tmp/vault-panel*`) |
| `./vault-panel.sh open` | start if needed and open the browser |
| `./vault-panel.sh status` | is it up? versions, CPU, watcher cost |
| `./vault-panel.sh stop` / `restart` | stop / restart |
| `./vault-panel.sh ensure` | idempotent, silent start — for hooks |

### Windows (Obsidian on Windows, panel in WSL)

Run the panel inside WSL and point `VAULT_PANEL_VAULT` to the vault through `/mnt/c/...`
(for example `/mnt/c/Users/you/Documents/ObsidianVault/MyProject_dev`). WSL does not get file-change events for
files written by Windows, so the server **polls**: hot files every 2 s, a full scan every 60 s. "Open in Obsidian"
links are converted to Windows paths automatically, and `./vault-panel.sh open` opens the Windows browser.

### Start it automatically (optional)

With [Claude Code](https://claude.com/claude-code), add a `SessionStart` hook to `.claude/settings.json`:

```json
{ "hooks": { "SessionStart": [ { "hooks": [
  { "type": "command", "command": "bash /path/to/AI-Second-Brain/vault-panel.sh ensure >/dev/null 2>&1 || true", "timeout": 10 }
] } ] } }
```

### Static snapshot (no server)

```bash
.venv/bin/python3 vault_status.py --vault /path/to/MyProject_dev --html snapshot.html
```

`--no-history` and `--no-graph` make it faster; `--json PATH` exports the data model.

## Vault conventions

| Path | Used for |
|---|---|
| `01_Specs/*.md` | specs: status (frontmatter `status:` or a `**Status:**` line), `- [ ]` criteria |
| `00_Context/_INDEX.md` | optional status tag and `~NN%` estimate per spec |
| `02_Memory/ADR-NNNN-*.md` | decision records: number, title, date, status, affected module |
| `02_Memory/_inbox/*.md` | session notes |
| `04_Anotações/*.md` | free-form notes (the folder keeps its Portuguese name, "Notes") |

Links count as Obsidian does (`[[wikilink]]`, `[text](file.md)`, `![[attachment]]`); "ADR-1234" mentions and
paths in backticks are kept as a separate, optional layer. Attachments respect Obsidian's *Excluded files*.
`raw/` folders are never read.

## Troubleshooting

- **"Not a vault project folder" on startup** (the panel prints it in Portuguese: *não parece a pasta de um projeto do
  vault*) — `VAULT_PANEL_VAULT` must point to a project folder that has `01_Specs/` or `02_Memory/`, not to the vault root.
- **Graph tab says networkx is missing** — install it in the Python the panel uses (`.venv/bin/pip install networkx`)
  or set `VAULT_PANEL_PYTHON`.
- **Port already in use** — set another `VAULT_PANEL_PORT` (each port is a separate instance).
- **Something looks stale** — `./vault-panel.sh status` shows the last rebuild and errors; the log is in `/tmp/vault-panel*.log`.

## Privacy

The server listens on `127.0.0.1` only, checks the `Host` header (DNS-rebinding protection) and sends a strict
Content-Security-Policy. Nothing is uploaded anywhere; the only external request is d3 from cdnjs. Your paths
live in `local.env` and `local.modules.json`, both git-ignored.

## Credits

- [Google Sans](https://fonts.google.com/specimen/Google+Sans) — SIL Open Font License 1.1 (`assets/google-sans-OFL.txt`), embedded.
- [Lucide](https://lucide.dev) icons — ISC License, embedded as SVG paths.
- [d3](https://d3js.org) — ISC License, loaded from cdnjs.
- [networkx](https://networkx.org) — BSD-3-Clause.

## License

MIT — see [LICENSE](LICENSE).
