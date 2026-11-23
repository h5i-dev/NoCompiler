# swe-bin pilot, 2026-11-21-r2

A pilot, not the benchmark. Patch mode, one counted attempt per task (the attempts column counts every session; see below). Solver: Claude Code TUI (`claude --model claude-opus-4-8`, run/solve.sh), with the environment's MCP tools as its only tools. 90 minutes wall per task, at most two at once. The prompt is run/prompt.md plus the issue. The proof bonus was not available (check_proof is not wired, STATUS-D).

Second run (lead 22:30): the same 5 tasks, prompt and limits. Tools: funcs, symbols and xrefs from the ELF itself (7635936); decompile, diff, stats and emulate working on RISC-V (E's 3b4a0f9, env 795a7cf); nocompiler and the server built at 4c691ec. Runner: solve.sh with the start fixes of the next commit (folder-trust answer, v2.1.330 input box, prompt only after the tools are listed); failed starts are listed under attempts.

Audit of the transcripts (STATUS-D, 2026-11-22): every tool call is an mcp__swebin__ tool; none was refused. From the solver's own text, each fix was found in the binary (micropython: the call the issue text suggests; valkey: lookupKey's command check, verified with decompile and diff; redis: the fcall wrappers made to feed MONITOR as evalCommand does; jq: a guard in decUnitCompare, checked with emulate against the original). jq and valkey tried to save notes to Claude Code's auto-memory and could not (per-run directory, empty afterwards). The jq solver found an emulator bug (mulh/mulhsu/mulhu computed as mul; R-D3 for the toolkit) and avoided mulhu.

axum's 0.0 was an environment bug (no editable_crates in the axum records, so the integrity check rejected the one changed function); re-judged after the fix: FAIL_TO_PASS 2/4, so 0 either way. See attempts.

Solved: 4 of 5.

| task | reward | FAIL_TO_PASS | PASS_TO_PASS | proof bonus | submitted by | attempts | claims to know the fix | wall | tool calls | submitted ELF sha256 | transcript |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| jqlang__jq-2839 | 1.0 | 1/1 | 6/6 | no | agent | 1 | no | 33 min 9 s | 107 | 38fa4e14b6f6cf22… | `/home/ec2-user/.claude/projects/-mnt-scratch-ec2-user-swe-bin-pilot-2026-11-21-r2-jqlang--jq-2839-cwd/0c75a6fa-54dd-4511-be3a-d15493e4d29f.jsonl` |
| micropython__micropython-13039 | 1.0 | 1/1 | 13/13 | no | agent | 2 | no | 1 min 12 s | 14 | 4cbb870ac001c8af… | `/home/ec2-user/.claude/projects/-mnt-scratch-ec2-user-swe-bin-pilot-2026-11-21-r2-micropython--micropython-13039-cwd/6700a121-7603-4bc5-a50c-f508a1988f8d.jsonl` |
| redis__redis-11510 | 1.0 | 1/1 | 4/4 | no | agent | 1 | no | 17 min 56 s | 50 | 17afcf3e59609bf4…, b8386c6734fc8a81… | `/home/ec2-user/.claude/projects/-mnt-scratch-ec2-user-swe-bin-pilot-2026-11-21-r2-redis--redis-11510-cwd/d3859efa-82a8-48b6-860b-1b31475b7b79.jsonl` |
| tokio-rs__axum-2096 | 0.0 | 0/4 | 0/17 | no | agent | 1 | no | 76 min 21 s | 92 | 86e2064e0d8fe8f8… | `/home/ec2-user/.claude/projects/-mnt-scratch-ec2-user-swe-bin-pilot-2026-11-21-r2-tokio-rs--axum-2096-cwd/c410a32e-47fd-4bec-aac1-f07ce3fae529.jsonl` |
| valkey-io__valkey-1499 | 1.0 | 1/1 | 46/46 | no | agent | 1 | no | 19 min 24 s | 46 | c6bc519107dd542e…, 67c44477f8a3fddc… | `/home/ec2-user/.claude/projects/-mnt-scratch-ec2-user-swe-bin-pilot-2026-11-21-r2-valkey-io--valkey-1499-cwd/56df60dc-4587-4cba-bc8c-d7a92f29801d.jsonl` |

Attempts:
- jqlang__jq-2839: 1 (one session)
- micropython__micropython-13039: 2 (4 starts. 22:26: Claude Code exited at the folder-trust question (runner's Down key lost; no session). 22:28: the runner did not recognize v2.1.330's input box and stopped (no prompt, no session). 22:30 (session bfe66882): the prompt went in before the swebin tools loaded; the solver had no tools, wrote '@swebin:list_files' as text and ended its turn, 0 tool calls; stopped by the operator, an infrastructure stop. 22:32: the counted attempt)
- redis__redis-11510: 1 (one session; an earlier start at 22:29 was stopped by the runner before the prompt (input box not recognized; no session))
- tokio-rs__axum-2096: 1 (one session. The recorded reward 0.0 is the environment's integrity check, not the tests: the 6 axum records had no editable_crates, so the one function the solver changed (axum::routing::Router::merge) counted as 'crate axum is not under test' and the tests did not run (an environment bug, fixed after the run by convert/editable.py). Re-judged afterwards with the fixed list (convert/harness.py run, same ELF, sha256 86e2064e…): integrity 0 violations, FAIL_TO_PASS 2/4, PASS_TO_PASS 17/17 (failing: routing::tests::fallback::merge_router_with_fallback_into_nested_router_with_fallback, ...::merging_nested_router_with_fallback_into_router_with_fallback), so 0 either way)
- valkey-io__valkey-1499: 1 (one session)

Every transcript per task (start and end UTC from the transcript; tool calls the solver made in it; run/contamination.py's flag on it, before audit; the task-level column above is the audited one, set in attempts.json where a reader overrode the scan):

| task | session | start | end | tool calls | counted | scan flag (matches) |
| --- | --- | --- | --- | --- | --- | --- |
| jqlang__jq-2839 | 0c75a6fa | 22:27:50 | 22:59:51 | 107 | yes | no (0) |
| micropython__micropython-13039 | bfe66882 | 22:31:00 | 22:31:01 | 0 | no | no (0) |
| micropython__micropython-13039 | 6700a121 | 22:32:18 | 22:33:16 | 14 | yes | no (0) |
| redis__redis-11510 | d3859efa | 22:33:41 | 22:51:20 | 50 | yes | no (0) |
| tokio-rs__axum-2096 | c410a32e | 23:00:28 | 00:16:28 | 92 | yes | no (0) |
| valkey-io__valkey-1499 | 56df60dc | 22:51:53 | 23:10:43 | 46 | yes | no (0) |

Claims to know the fix (run/contamination.py over every session of the task; the solver's own text):
- jqlang__jq-2839: no
- micropython__micropython-13039: no
- redis__redis-11510: no
- tokio-rs__axum-2096: no
- valkey-io__valkey-1499: no

SHA-256s are per submitted file; the environment's own message hashes a multi-file submission as the SHA-256 of the files' SHA-256s.

Full SHA-256s, the tools each run used and the session paths: rows.json. Transcripts are not committed.
