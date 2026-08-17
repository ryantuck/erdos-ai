import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Erdős Problem 31

*Reference:* [erdosproblems.com/31](https://www.erdosproblems.com/31)
(accessed 2026-02-22; page content recovered from archived session logs — the live site
is unreachable from the review container).

Statement (verbatim from the site): "Given any infinite set $A\subset \mathbb{N}$ there
is a set $B$ of density $0$ such that $A+B$ contains all except finitely many integers."

Conjectured by Erdős and Straus. Proved by Lorentz [Lo54]. The site's status banner reads
**PROVED (LEAN)** — "This has been solved in the affirmative and the proof verified in
Lean"; the upstream formal-conjectures entry records a Lean 4 proof at
<https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos31.lean>.
The teorth/erdosproblems metadata mirror (`data/problems.yaml`, checked at commit
a09c7a21, 2026-08-14) agrees: status "proved (Lean)" (last update 2025-11-24); tags:
number theory, additive basis; no OEIS references; no prize.

[Er56] Erdős, P., _Problems and results in additive number theory_. Colloque sur la
Théorie des Nombres, Bruxelles, 1955 (1956), 127-137.

[Er59] Erdős, P., _Über einige Probleme der additiven Zahlentheorie_. Sammelband zu
Ehren des 250. Geburtstages Leonhard Eulers (1959), 116-119.

[Er65b] Erdős, Paul, _Some recent advances and current problems in number theory_.
Lectures on Modern Mathematics, Vol. III (1965), 196-244.

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins,
Colo., 1971) (1973), 117-138.

[Lo54] Lorentz, G. G., _On a problem of additive number theory_. Proc. Amer. Math. Soc.
(1954), 838-841. (The volume number is absent from the recovered `/latex/31`
extraction and is not fabricated here.)

Bibliographic provenance: [Lo54] from the original pipeline's fetch of
`erdosproblems.com/latex/31` preserved in the session logs (title, journal, year, pages;
volume reported "not specified"); [Er56], [Er59], [Er65b], [Er73] from the upstream
google-deepmind/formal-conjectures file `FormalConjectures/ErdosProblems/31.lean`
(commit dd1c2beb) — the erdosproblems.com page itself displays only the keys.
-/

open Classical

/-- The sumset `A + B`: the set of all `a + b` with `a ∈ A, b ∈ B`.

(Equivalent to Mathlib's pointwise `A + B` under `open scoped Pointwise`; kept as a
local definition to avoid compiler-dependent changes in this pipeline.) -/
def sumset31 (A B : Set ℕ) : Set ℕ := {n : ℕ | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/-- A set `B ⊆ ℕ` has natural density zero if
    `|B ∩ {0, …, N-1}| / N → 0` as `N → ∞`. -/
def HasNaturalDensityZero (B : Set ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (((Finset.range N).filter (· ∈ B)).card : ℝ) / (N : ℝ) < ε

/--
**Erdős Problem #31** (Erdős–Straus, proved by Lorentz [Lo54]):

Given any infinite set $A \subset \mathbb{N}$, there exists a set $B \subseteq \mathbb{N}$
of natural density $0$ such that $A + B$ contains all except finitely many natural numbers.

Solved in the affirmative, so the direct-assertion form below states the true direction;
the proof has additionally been verified in Lean (see the module docstring).
-/
theorem erdos_problem_31 (A : Set ℕ) (hA : A.Infinite) :
    ∃ B : Set ℕ, HasNaturalDensityZero B ∧
      Set.Finite {n : ℕ | n ∉ sumset31 A B} :=
  sorry
