import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open Finset

open scoped Pointwise

noncomputable section

/-!
# Erdős Problem #819

Let $f(N)$ be maximal such that there exists $A\subseteq \{1,\ldots,N\}$ with
$|A|=\lfloor N^{1/2}\rfloor$ such that $|(A+A)\cap [1,N]|=f(N)$. Estimate $f(N)$.

Erdős and Freud [ErFr91] proved
$(3/8-o(1))N \leq f(N) \leq (1/2+o(1))N$,
and note that it is closely connected to the size of the largest quasi-Sidon set
(see [840]).

Tags: additive combinatorics
-/

/-- The maximum of `|(A + A) ∩ {1, ..., N}|` over all `A ⊆ {1, ..., N}` with
    `|A| = ⌊√N⌋`. -/
noncomputable def erdos819_f (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A => A.card = Nat.sqrt N)).sup
    (fun A => ((A + A) ∩ Finset.Icc 1 N).card)

/--
**Erdős Problem #819** — Lower bound (Erdős–Freud [ErFr91]):

For every ε > 0, for sufficiently large N,
$f(N) \geq (3/8 - \varepsilon) N$.
-/
theorem erdos_819_lower :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (↑(erdos819_f N) : ℝ) ≥ (3 / 8 - ε) * (↑N : ℝ) :=
  sorry

/--
**Erdős Problem #819** — Upper bound (Erdős–Freud [ErFr91]):

For every ε > 0, for sufficiently large N,
$f(N) \leq (1/2 + \varepsilon) N$.
-/
theorem erdos_819_upper :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (↑(erdos819_f N) : ℝ) ≤ (1 / 2 + ε) * (↑N : ℝ) :=
  sorry

end
