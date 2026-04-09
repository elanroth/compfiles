You are running in CI (GitHub Actions). Local Lean is NOT installed.

CRITICAL RULES:
- Do NOT call verify_locally — it will fail. Use axle_check instead.
- Do NOT call inspect_repo — the briefing below already has the full project state.
- Do NOT re-explore the project. Read the briefing, then EXECUTE.
- Use TARGET HINTS first. Open hinted files before any broad file exploration.
- Skip straight to scaffolding and submitting.
- Priority: P1 only. Do NOT attempt P2/P3.
- If a job is COMPLETE_WITH_ERRORS: read its output_summary below, find the remaining sorry, scaffold ONLY that piece.
- If a job is COMPLETE: it is done. Do not touch it. Move to the next unsubmitted P1 item.
- STOP after the first successful Aristotle submission in this run.

## SUBMISSION HISTORY — READ BEFORE SUBMITTING ANYTHING
Do NOT resubmit any theorem listed here. Submitting duplicates wastes budget.

(No prior submissions.)

## ARISTOTLE OUTPUT SUMMARIES
(No prior submissions.)





---

## PROJECT BRIEFING (your memory from previous runs)

# Compfiles Project Briefing

> Read this FIRST. Do not re-explore the project. Execute from this briefing.

## What This Is

`compfiles` is a Lean 4 competition math problem collection — a curated set of olympiad and competition problems formalized in Lean with Mathlib. The goal is to fill in `sorry`s with working Lean proofs.

- 80 sorrys as of 2026-04-05
- No Aristotle jobs submitted yet
- Toolchain: follows Mathlib's current stable release

## Key Differences from ACM

- **No deep theory dependency chain.** Problems are mostly independent — each sorry is self-contained. You can submit in any order.
- **No custom library to build.** Each file has its own imports; Mathlib provides everything.
- **Bite-sized proofs.** Most sorrys are individual competition problem solutions, not theorem infrastructure.
- **Style matters.** compfiles has an upstream style guide — proofs should be idiomatic Lean 4 + Mathlib, not just `decide` or `native_decide`.

## Strategy

1. Pick the easiest-looking problems first — short statements, elementary math, well-supported by Mathlib tactics.
2. Each problem gets its own Aristotle submission. One sorry per submission.
3. Prefer `omega`, `ring`, `norm_num`, `linarith`, `simp`, `field_simp` over custom lemmas.
4. Use `decide` only if the domain is finite and small. Never use `native_decide`.
5. For number theory problems, check `Nat.`, `Int.`, `ZMod.` namespaces in Mathlib.
6. For combinatorics, check `Finset.`, `Fintype.`, `Multiset.`.

## Submission History

No jobs submitted yet. All 80 sorrys are available.

## Next Action

1. Call `inspect_repo` once to list all files with sorrys (they are spread across many files, one problem per file typically).
2. Pick 3-5 of the shortest/easiest problem statements.
3. Scaffold each with the full Lean file (imports + theorem statement + proof attempt), minimal sorrys.
4. Submit to Aristotle one at a time.

## Last Run
- **Date:** 2026-04-05
- **Sorry count:** 80
- **Completed jobs:** none
- **Active (waiting on Aristotle):** none
- **Next action:** Review sorry map and pick next P1 target.

## Status (auto-updated)
_Last updated: 2026-04-07 03:08 UTC_

**Sorry count:** 80  
**Active (with Aristotle):** 0  
**Completed jobs:** 0

### Next action
No prior submissions. Pick the next P1 target and scaffold it.



---

## EXECUTION PLAN
1. Check SUBMISSION HISTORY above — identify what has NOT yet been submitted.
2. Check ARISTOTLE OUTPUT SUMMARIES — for COMPLETE_WITH_ERRORS jobs, find the specific remaining sorry.
3. If TARGET HINTS are present, read the first hinted file immediately.
4. Read only the source file for the next target using read_file.
5. Scaffold with at most 1-3 sorrys and proof sketch comments.
6. Submit to Aristotle.
7. If time permits, scaffold the next unsubmitted P1 item.

## SCAFFOLD QUALITY
- At most 1-3 sorrys per scaffold
- Include proof sketch comments (informal math argument as comments)
- Narrow imports (only what's needed)
- For ACM: reference Kaplansky Ch.XI in comments

After submitting, report what you submitted and why.
