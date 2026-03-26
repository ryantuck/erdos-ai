---
name: Use Filter.Tendsto for limits
description: Prefer Filter.Tendsto/atTop/nhds over epsilon-delta formulations for limit statements in Lean formalizations
type: feedback
---

Use `Filter.Tendsto`, `Filter.atTop`, and `TopologicalSpace.nhds` instead of manual epsilon-delta formulations (∀ ε > 0, ∃ N₀, ∀ n ≥ N₀, ...) for limit statements. Similarly, use `∀ᶠ ... in atTop` for "for all sufficiently large" patterns instead of `∃ N₀, ∀ n, N₀ ≤ n →`.

**Why:** Reviewer feedback on Erdős problem 1014 — the filter-based API is the idiomatic Mathlib way to state limits and asymptotic results.

**How to apply:** When formalizing any conjecture that involves a limit (ratio → 1, function → ∞, asymptotic formula), use `Tendsto f atTop (nhds c)` or `Tendsto f atTop atTop`. For "eventually" bounds, use `∀ᶠ n in atTop, P n`. Open `Filter` and `open scoped Topology` as needed.
