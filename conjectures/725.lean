import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic

open Filter

noncomputable section

/-- A k×n Latin rectangle: a function f : Fin k → Fin n → Fin n where each row
    is a bijection (permutation of Fin n) and each column has distinct entries. -/
def IsLatinRectangle {k n : ℕ} (f : Fin k → Fin n → Fin n) : Prop :=
  (∀ i : Fin k, Function.Bijective (f i)) ∧
  (∀ j : Fin n, Function.Injective (fun i : Fin k => f i j))

/-- The number of k×n Latin rectangles. -/
noncomputable def latinRectangleCount (k n : ℕ) : ℕ :=
  Set.ncard {f : Fin k → Fin n → Fin n | IsLatinRectangle f}

/-!
# Erdős Problem #725

Give an asymptotic formula for the number of k×n Latin rectangles.

Erdős and Kaplansky [ErKa46] proved the count L(k,n) satisfies
  L(k,n) ~ e^{-C(k,2)} · (n!)^k
when k = o((log n)^{3/2-ε}). Yamamoto [Ya51] extended this to k ≤ n^{1/3-o(1)}.

We formalize the conjecture that this asymptotic formula holds for all
k = o(√n), extending the known range.
-/

/--
Erdős Problem #725 [Er81]:

For any sequence k(n) with k(n) = o(√n) and k(n) ≥ 2 eventually,
the number L(k(n), n) of k(n)×n Latin rectangles satisfies

  L(k(n), n) / (e^{-C(k(n),2)} · (n!)^{k(n)}) → 1  as n → ∞.
-/
theorem erdos_problem_725 :
    ∀ (k : ℕ → ℕ),
    (∀ᶠ n in atTop, 2 ≤ k n) →
    (∀ n, k n ≤ n) →
    Tendsto (fun n => (k n : ℝ) / Real.sqrt ↑n) atTop (nhds 0) →
    Tendsto
      (fun n => (latinRectangleCount (k n) n : ℝ) /
        (Real.exp (-(↑(Nat.choose (k n) 2) : ℝ)) * ((Nat.factorial n : ℝ) ^ (k n))))
      atTop (nhds 1) :=
  sorry

end
