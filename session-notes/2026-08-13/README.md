# Session notes — 2026-08-13

Working notes from the Claude Code sessions on this repo. Written for the next session to
read, not as a changelog — git already has the changelog.

Read `08-…` first; it is the most recent and supersedes parts of the synthesis.

| File | Session | Covers |
|---|---|---|
| `00-SYNTHESIS.md` | — | Cross-session synthesis of 1–6, written by session 7. Partly superseded. |
| `01-2ff30151` | Aug 4 | Env setup; produced `conjectures-v2/` and all 100 building clean |
| `02-6d584690` | Aug 4 | Killed mid-tool-call; no output |
| `03-8ef14022` | Aug 12 | Provenance audit; two conclusions later corrected |
| `04-ec75be9c` | Aug 12 | Corrected session 3; re-ran the full build |
| `05-01410245` | Aug 12 | Re-ran the build again after session 4's log was reaped |
| `06-9227ed25` | Aug 12 | `lakefile.toml` + `ConjecturesV2` symlink; upstream-drift finding |
| `07-7e577b95` | Aug 13 | Wrote the synthesis and the first durable memories |
| `08-0d3a5042` | Aug 13 | Six merged PRs; pipeline redefined; DeepMind archived |

## Why this directory exists

Sessions 1–7 wrote their notes to `/tmp` scratchpads, which get reaped. Session 5 redid an
entire Lean build purely because session 4's log had vanished, and session 8 had to
reconstruct all seven of session 7's documents from `Write` tool inputs buried in a
transcript. Notes meant to outlive a session belong in the repo or in the memory
directory — not in `/tmp`.
