import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

open Classical

/-!
# Erdős Problem #756

Let $A \subset \mathbb{R}^2$ be a set of $n$ points. Can there be $\gg n$ many
distinct distances each of which occurs for more than $n$ many pairs from $A$?

Asked by Erdős and Pach [ErPa90][Er97b]. The answer is yes: Bhowmick [Bh24]
constructs a set of $n$ points in $\mathbb{R}^2$ such that $\lfloor n/4 \rfloor$
distances occur at least $n + 1$ times.

See also problems #132 and #957.
-/

/-- For a finite point set $A \subseteq \mathbb{R}^2$ and a real value $d$,
    the number of ordered pairs $(x, y)$ with $x \neq y$ in $A$ at
    Euclidean distance $d$. -/
noncomputable def pairCount756 (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card

/-- The set of distances that occur with multiplicity greater than $|A|$
    (counting ordered pairs). -/
noncomputable def highMultiplicityDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : Set ℝ :=
  {d : ℝ | A.card < pairCount756 A d}

/--
Erdős Problem #756 [ErPa90, Er97b] (proved by Bhowmick [Bh24]):
There exists a constant $c > 0$ such that for all sufficiently large $n$,
there is a set $A$ of $n$ points in $\mathbb{R}^2$ with the number of
distinct distances occurring more than $n$ times (as ordered pairs) being
at least $c \cdot n$.
-/
theorem erdos_problem_756 :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n ∧
        c * (n : ℝ) ≤ Set.ncard (highMultiplicityDistances A) :=
  sorry
