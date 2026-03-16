---
name: Code reuse — only Mathlib and FormalConjecturesForMathlib
description: Section 1 code reuse should only search Mathlib and FormalConjecturesForMathlib/ for existing definitions, not other Erdős problem files, and never create new library definitions.
type: feedback
---

When applying FIX_REVIEW_ISSUES.md Section 1 (Code Reuse): only search Mathlib and `FormalConjecturesForMathlib/` for library equivalents. Do NOT look at other Erdős problem files for code to reuse. If no drop-in library equivalent exists, skip Section 1 entirely. Do NOT create new definitions in the shared library.

**Why:** Other Erdős problem files are not a reuse source — they are peer files at the same level. Only Mathlib and FormalConjecturesForMathlib/ are proper library code.

**How to apply:** When the review flags a local definition for replacement, search only in Mathlib and `FormalConjecturesForMathlib/` dirs. Ignore hits in `FormalConjectures/ErdosProblems/`.
