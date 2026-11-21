# swe-bin pilot, 2026-11-21

A pilot, not the benchmark. Patch mode, one counted attempt per task (the attempts column counts every session; see below). Solver: Claude Code TUI (`claude --model claude-opus-4-8`, run/solve.sh), with the environment's MCP tools as its only tools. 90 minutes wall per task, at most two at once. The prompt is run/prompt.md plus the issue. The proof bonus was not available (check_proof is not wired, STATUS-D).

Solved: 2 of 5.

| task | reward | FAIL_TO_PASS | PASS_TO_PASS | proof bonus | submitted by | attempts | claims to know the fix | wall | tool calls | submitted ELF sha256 | transcript |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| micropython__micropython-13039 | 1.0 | 1/1 | 13/13 | no | agent | 2 | yes | 3 min 43 s | 19 | 8c9991944fa83b84… | `/home/ec2-user/.claude/projects/-mnt-scratch-ec2-user-swe-bin-pilot-2026-11-21-micropython--micropython-13039-cwd/d119aff5-f01c-4980-a489-bac760111f9d.jsonl` |
| jqlang__jq-2839 | 0.0 | 0/1 | 6/6 | no | agent | 2 | no | 35 min 5 s | 86 | 6199ead9536e163c… | `/home/ec2-user/.claude/projects/-mnt-scratch-ec2-user-swe-bin-pilot-2026-11-21-jqlang--jq-2839-cwd/e9cc558e-e334-4764-bfe2-f8ba4bacebda.jsonl` |
| redis__redis-11510 | 0.0 | 0/1 | 4/4 | no | agent | 1 | no | 16 min 48 s | 50 | 381e808447a4d37d…, b8386c6734fc8a81… | `/home/ec2-user/.claude/projects/-mnt-scratch-ec2-user-swe-bin-pilot-2026-11-21-redis--redis-11510-cwd/dcf0330b-1287-4358-9f44-36e6d8412d05.jsonl` |
| valkey-io__valkey-1499 | 1.0 | 1/1 | 46/46 | no | agent | 1 | no | 13 min 48 s | 45 | e1d260c91be1426b…, 67c44477f8a3fddc… | `/home/ec2-user/.claude/projects/-mnt-scratch-ec2-user-swe-bin-pilot-2026-11-21-valkey-io--valkey-1499-cwd/2bd760a1-fd34-44a6-ac50-7db87b5282b5.jsonl` |
| tokio-rs__axum-2096 | none | – | – | no | none (ended its turn with a question) | 1 | yes | 95 min 52 s | 109 |  | `/home/ec2-user/.claude/projects/-mnt-scratch-ec2-user-swe-bin-pilot-2026-11-21-tokio-rs--axum-2096-cwd/47854e77-2369-4b55-94aa-f4d75266a5d8.jsonl` |

Attempts:
- micropython__micropython-13039: 2 (attempt 1 (session ddc9074a, 15:12:18-15:12:56) stopped by the operator after 38 s: a mistaken task check (ISSUE.md compared with \r\n line ends) reported a mismatch; an infrastructure stop, not the solver's. The episode was reset (same episode id: the server recreated the directory, a new bridge session reset it). Attempt 2 is the one counted)
- jqlang__jq-2839: 2 (attempt 1 (session 6bffc95c, 15:12:37-15:12:52) stopped by the operator after 15 s, for the same mistaken check; an infrastructure stop. The episode was reset. Attempt 2 is the one counted)
- redis__redis-11510: 1 (one session)
- valkey-io__valkey-1499: 1 (one session)
- tokio-rs__axum-2096: 1 (one session; the solver ended its turn at 16:29 with a question to the user, and no one answered (lead 16:55). Recorded as no submission at the 90-minute limit. (This run's bridge still had the old deadline behaviour and submitted the untouched starting binary at 17:20: F2P 0/4, P2P 17/17, sha256 8965e9cb…; the bridge no longer does that))

Claims to know the fix (run/contamination.py over every session of the task; the solver's own text):
- micropython__micropython-13039: yes: "The upstream fix changes `mp_obj_int_get_checked` (which blindly interprets any object as an int) to `mp_obj_get_int` (which raises TypeError for non-int types " / "This is exactly the upstream fix." / "For a float, `mp_obj_get_int` → `mp_obj_get_int_maybe` calls `mp_unary_op(arg, MP_UNARY_OP_INT_MAYBE)` which returns NULL for floats, so `mp_obj_get_int` raises"
- jqlang__jq-2839: no: "I'll test the assembler syntax with a small function before writing the real fix."
- redis__redis-11510: no
- valkey-io__valkey-1499: no
- tokio-rs__axum-2096: yes: "If you can get me the symbol table (even a grep of it for `routing`, `path_router`, `merge`, `nest`, `fallback`), or a build where those routing functions aren'"

SHA-256s are per submitted file; the environment's own message hashes a multi-file submission as the SHA-256 of the files' SHA-256s.

Full SHA-256s, the tools each run used and the session paths: rows.json. Transcripts are not committed.
