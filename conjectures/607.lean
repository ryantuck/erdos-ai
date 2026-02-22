import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Classical

noncomputable section

/-!
# Erdős Problem #607

For a set of n points P ⊂ ℝ² let ℓ₁, …, ℓₘ be the lines determined by P, and
let A = {|ℓ₁ ∩ P|, …, |ℓₘ ∩ P|} be the set of distinct point-line incidence
counts.

Let F(n) count the number of possible sets A that can be constructed this way.
Is it true that F(n) ≤ exp(O(√n))?

Erdős writes it is 'easy to see' that this bound would be best possible.
This was proved by Szemerédi and Trotter [SzTr83].
-/

/-- Three points in ℝ² are collinear: the cross product of the displacement
    vectors (q - p) and (r - p) vanishes. -/
def Collinear607 (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/-- Given a finite point set P and two points p, q, the number of points in P
    lying on the line through p and q. -/
def lineIncidence607 (P : Finset (ℝ × ℝ)) (p q : ℝ × ℝ) : ℕ :=
  (P.filter (fun r => Collinear607 p q r)).card

/-- The line spectrum of a finite point set P ⊂ ℝ²: the set of all distinct
    values |ℓ ∩ P| as ℓ ranges over lines determined by P (lines through at
    least two points of P). -/
def lineSpectrum607 (P : Finset (ℝ × ℝ)) : Finset ℕ :=
  P.biUnion fun p =>
    (P.filter fun q => p ≠ q).image fun q => lineIncidence607 P p q

/-- The set of achievable line spectra for n-point configurations in ℝ². -/
def achievableSpectra607 (n : ℕ) : Set (Finset ℕ) :=
  {S | ∃ P : Finset (ℝ × ℝ), P.card = n ∧ lineSpectrum607 P = S}

/--
**Erdős Problem #607** [Er85]:

There exists a constant C > 0 such that for all sufficiently large n, the number
F(n) of distinct line spectra achievable by n-point configurations in ℝ²
satisfies F(n) ≤ exp(C · √n).

Proved by Szemerédi and Trotter [SzTr83].
-/
theorem erdos_problem_607 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (achievableSpectra607 n).Finite ∧
      ((achievableSpectra607 n).ncard : ℝ) ≤ Real.exp (C * Real.sqrt (n : ℝ)) :=
  sorry

end
