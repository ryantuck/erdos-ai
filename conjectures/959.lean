import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open Classical

/-!
# Erdős Problem #959

Let $A \subset \mathbb{R}^2$ be a set of size $n$ and let $\{d_1, \ldots, d_k\}$
be the set of distinct distances determined by $A$. Let $f(d)$ be the number of
times the distance $d$ is determined (as an unordered pair), and suppose the $d_i$
are ordered such that $f(d_1) \geq f(d_2) \geq \cdots \geq f(d_k)$.

Estimate $\max (f(d_1) - f(d_2))$, where the maximum is taken over all $A$ of
size $n$.

Clemen, Dumitrescu, and Liu [CDL25] have shown that
$\max (f(d_1) - f(d_2)) \gg n \log n$.

They conjecture that $n \log n$ can be improved to $n^{1+c/\log\log n}$ for some
constant $c > 0$.
-/

/-- The set of distinct distances determined by a finite point set in ℝ². -/
noncomputable def distinctDistances959 (A : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).image (fun p => dist p.1 p.2)

/-- The multiplicity of distance d in A: the number of unordered pairs at distance d. -/
noncomputable def distMultiplicity959 (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card / 2

/--
**Erdős Problem #959** [Er84d]:

For any sufficiently large $n$, there exists a set $A$ of $n$ points in $\mathbb{R}^2$
such that the gap between the most frequent and every other distance multiplicity
is at least $c \cdot n \cdot \log n$ for some absolute constant $c > 0$.

Equivalently, $\max_A (f(d_1) - f(d_2)) \gg n \log n$ where $f(d_1) \geq f(d_2)$
are the two largest distance multiplicities.

This lower bound was proved by Clemen, Dumitrescu, and Liu [CDL25].
-/
theorem erdos_problem_959 :
    ∃ c : ℝ, c > 0 ∧ ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        A.card = n ∧
        ∃ d₁ ∈ distinctDistances959 A,
          (∀ d ∈ distinctDistances959 A, distMultiplicity959 A d ≤ distMultiplicity959 A d₁) ∧
          ∀ d₂ ∈ distinctDistances959 A, d₂ ≠ d₁ →
            (distMultiplicity959 A d₁ : ℝ) - (distMultiplicity959 A d₂ : ℝ) ≥
              c * (n : ℝ) * Real.log (n : ℝ) :=
  sorry

end
