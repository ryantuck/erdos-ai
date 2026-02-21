import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic

open Classical

/-!
# Erdős Problem #432

Let A, B ⊆ ℕ be two infinite sets. How dense can A + B be if all elements
of A + B are pairwise relatively prime?

Asked by Straus, inspired by a problem of Ostmann (see Problem #431).

We formalize this as: for any two infinite sets A, B ⊆ ℕ, if all elements
of the sumset A + B are pairwise coprime, then A + B has zero upper density.
The deeper open question is about the precise maximum growth rate of the
counting function |(A+B) ∩ {1,...,n}| — in particular, whether it can match
the density of the primes (~n/log n).
-/

/--
The upper density of A ⊆ ℕ:
  d*(A) = limsup_{N→∞} |A ∩ {0, 1, ..., N-1}| / N
-/
noncomputable def upperDensity432 (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/--
Erdős Problem #432 [ErGr80, p.85]:

Let A, B ⊆ ℕ be two infinite sets. If all elements of the sumset
A + B = {a + b | a ∈ A, b ∈ B} are pairwise coprime, then A + B has
zero upper density.
-/
theorem erdos_problem_432
    (A B : Set ℕ) (hA : A.Infinite) (hB : B.Infinite)
    (h_coprime : ∀ x ∈ Set.image2 (· + ·) A B,
      ∀ y ∈ Set.image2 (· + ·) A B, x ≠ y → Nat.Coprime x y) :
    upperDensity432 (Set.image2 (· + ·) A B) = 0 :=
  sorry
