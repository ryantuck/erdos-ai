import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/-!
# Erdős Problem #669

Let $F_k(n)$ be minimal such that for any $n$ points in $\mathbb{R}^2$ there
exist at most $F_k(n)$ many distinct lines passing through at least $k$ of the
points, and $f_k(n)$ similarly but with lines passing through exactly $k$ points.

Estimate $f_k(n)$ and $F_k(n)$ — in particular, determine $\lim F_k(n)/n^2$
and $\lim f_k(n)/n^2$.

Trivially $f_k(n) \leq F_k(n)$ and $f_2(n) = F_2(n) = \binom{n}{2}$.
The problem with $k = 3$ is the classical 'Orchard problem' of Sylvester.
Burr, Grünbaum, and Sloane [BGS74] proved that $f_3(n) = n^2/6 - O(n)$ and
$F_3(n) = n^2/6 - O(n)$.

There is a trivial upper bound $F_k(n) \leq \binom{n}{2}/\binom{k}{2}$,
hence $\lim F_k(n)/n^2 \leq 1/(k(k-1))$.

A problem of Erdős [Er97f]. See also problem #101.

Tags: geometry
-/

open Classical

noncomputable section

/-- The number of affine lines in ℝ² passing through at least `k` points
    from a finite point set `P`. -/
noncomputable def atLeastKPointLineCount669
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    k ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L}}

/-- The number of affine lines in ℝ² passing through exactly `k` points
    from a finite point set `P`. -/
noncomputable def exactlyKPointLineCount669
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (k : ℕ) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L} = k}

/-- `bigF669 k n`: the maximum over all n-point sets P ⊆ ℝ² of the number of
    lines passing through at least k points of P. This is the function F_k(n)
    from Erdős Problem #669. -/
noncomputable def bigF669 (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
    P.card = n ∧ atLeastKPointLineCount669 P k = m}

/-- `littleF669 k n`: the maximum over all n-point sets P ⊆ ℝ² of the number of
    lines passing through exactly k points of P. This is the function f_k(n)
    from Erdős Problem #669. -/
noncomputable def littleF669 (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
    P.card = n ∧ exactlyKPointLineCount669 P k = m}

/--
**Erdős Problem #669, Part 1** [Er97f]:

The limit $\lim_{n \to \infty} F_k(n)/n^2$ exists for all $k \geq 2$.
-/
theorem erdos_problem_669_bigF_limit_exists (k : ℕ) (hk : k ≥ 2) :
    ∃ L : ℝ, ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        |((bigF669 k n : ℝ) / (n : ℝ) ^ 2) - L| ≤ ε :=
  sorry

/--
**Erdős Problem #669, Part 2** [Er97f]:

The limit $\lim_{n \to \infty} f_k(n)/n^2$ exists for all $k \geq 2$.
-/
theorem erdos_problem_669_littleF_limit_exists (k : ℕ) (hk : k ≥ 2) :
    ∃ L : ℝ, ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        |((littleF669 k n : ℝ) / (n : ℝ) ^ 2) - L| ≤ ε :=
  sorry

/--
**Erdős Problem #669, trivial upper bound**:

$F_k(n) \leq n(n-1)/(k(k-1))$ for all $n$ and $k \geq 2$.
This follows from $F_k(n) \leq \binom{n}{2}/\binom{k}{2}$ since each line
through at least $k$ points accounts for at least $\binom{k}{2}$ pairs.
-/
theorem erdos_problem_669_trivial_bound (k : ℕ) (hk : k ≥ 2) (n : ℕ) :
    (bigF669 k n : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / ((k : ℝ) * ((k : ℝ) - 1)) :=
  sorry

end
