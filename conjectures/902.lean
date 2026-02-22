import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

noncomputable section

/-!
# Erdős Problem #902

Let f(n) be minimal such that there is a tournament (a complete directed graph)
on f(n) vertices such that every set of n vertices is dominated by at least one
other vertex. Estimate f(n).

Schütte asked Erdős this in the early 1960s. It is easy to check that
f(1) = 3 and f(2) = 7. Erdős [Er63c] proved
  2^{n+1} - 1 ≤ f(n) ≪ n² · 2^n.
Szekeres and Szekeres [SzSz65] proved that f(3) = 19 and
  n · 2^n ≪ f(n).
-/

/-- A tournament on a type V: a relation where for any two distinct vertices,
    exactly one beats the other. -/
structure Tournament (V : Type*) where
  beats : V → V → Prop
  irrefl : ∀ v, ¬beats v v
  complete : ∀ v w, v ≠ w → (beats v w ∨ beats w v)
  antisymm : ∀ v w, beats v w → ¬beats w v

/-- A tournament has the n-domination property if every subset of size n
    is dominated by some vertex outside the subset (i.e., some vertex v ∉ S
    beats every member of S). -/
def Tournament.hasDominationProperty {V : Type*} (T : Tournament V)
    (n : ℕ) : Prop :=
  ∀ S : Finset V, S.card = n → ∃ v, v ∉ S ∧ ∀ u ∈ S, T.beats v u

/-- f(n): the minimum number of vertices in a tournament with the
    n-domination property. -/
noncomputable def tournamentDominationNumber (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (T : Tournament (Fin m)), T.hasDominationProperty n}

/--
Erdős Problem #902, lower bound [Er63c]: f(n) ≥ 2^{n+1} - 1 for all n ≥ 1.
-/
theorem erdos_problem_902_lower (n : ℕ) (hn : n ≥ 1) :
    tournamentDominationNumber n ≥ 2 ^ (n + 1) - 1 :=
  sorry

/--
Erdős Problem #902, upper bound [Er63c]: f(n) ≪ n² · 2^n.
There exists C > 0 such that f(n) ≤ C · n² · 2^n for all n ≥ 1.
-/
theorem erdos_problem_902_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (tournamentDominationNumber n : ℝ) ≤ C * (n : ℝ) ^ 2 * 2 ^ n :=
  sorry

/--
Szekeres-Szekeres improved lower bound [SzSz65]: f(n) ≫ n · 2^n.
There exists C > 0 such that f(n) ≥ C · n · 2^n for all n ≥ 1.
-/
theorem erdos_problem_902_szekeres_lower :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (tournamentDominationNumber n : ℝ) ≥ C * (n : ℝ) * 2 ^ n :=
  sorry

end
