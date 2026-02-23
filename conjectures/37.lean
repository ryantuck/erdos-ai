import Mathlib.Data.Real.Archimedean
import Mathlib.Data.PNat.Basic
import Mathlib.Order.Interval.Finset.Nat

open Classical

/--
The Schnirelmann density of a set A ⊆ ℕ, defined as
  d_s(A) = inf_{n ≥ 1} |A ∩ {1,...,n}| / n
-/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  ⨅ n : ℕ+, (((Finset.Icc 1 (n : ℕ)).filter (· ∈ A)).card : ℝ) / ((n : ℕ) : ℝ)

/--
The sumset A + B = {a + b | a ∈ A, b ∈ B} for sets of natural numbers.
-/
def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/--
A set A ⊆ ℕ is an essential component if d_s(sumset A B) > d_s(B) for every
B ⊆ ℕ with 0 < d_s(B) < 1, where d_s is the Schnirelmann density.
-/
def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ (B : Set ℕ), 0 < schnirelmannDensity B → schnirelmannDensity B < 1 →
    schnirelmannDensity (sumset A B) > schnirelmannDensity B

/--
A set A ⊆ ℕ is lacunary if there exists q > 1 such that for any two
consecutive elements a < b of A (with no element of A strictly between them),
we have b ≥ q * a.
-/
def IsLacunary (A : Set ℕ) : Prop :=
  ∃ (q : ℝ), q > 1 ∧ ∀ (a b : ℕ), a ∈ A → b ∈ A → a < b →
    (∀ c ∈ A, ¬(a < c ∧ c < b)) → (b : ℝ) ≥ q * (a : ℝ)

/--
Erdős Problem #37 (Disproved by Ruzsa [Ru87]).
A lacunary set cannot be an essential component.
Ruzsa proved that if A is an essential component then there exists some constant
c > 0 such that |A ∩ {1,...,N}| ≥ (log N)^{1+c} for all large N, which rules
out lacunary sets (which satisfy |A ∩ {1,...,N}| = O(log N)).
-/
theorem erdos_problem_37 :
    ∀ (A : Set ℕ), IsLacunary A → ¬IsEssentialComponent A :=
  sorry
