import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Classical Filter

noncomputable section

/-!
# Erdős Problem #136

Let f(n) be the smallest number of colours required to colour the edges of K_n
such that every K_4 contains at least 5 colours. Determine the size of f(n).

Asked by Erdős and Gyárfás, who proved that (5/6)(n-1) < f(n) < n and that
f(9) = 8. Erdős believed the upper bound is closer to the truth. In fact the
lower bound is: Bennett, Cushman, Dudek, and Pralat [BCDP22] proved that
f(n) ~ (5/6)n. Joos and Mubayi [JoMu22] found a shorter proof.
-/

/-- An edge coloring of K_n with colors from Fin k, represented as a function
    on ordered pairs of vertices. -/
def EdgeColoring (n k : ℕ) : Type := Fin n → Fin n → Fin k

/-- The set of distinct colors used on edges within vertex subset S
    under coloring χ (using offDiag to enumerate all ordered pairs of
    distinct vertices in S). -/
noncomputable def edgeColors {n k : ℕ} (χ : EdgeColoring n k)
    (S : Finset (Fin n)) : Finset (Fin k) :=
  S.offDiag.image (fun p => χ p.1 p.2)

/-- A coloring χ of K_n is K₄-five-colored if every 4-element vertex subset
    has at least 5 distinct colors on its edges. -/
def IsK4FiveColored {n k : ℕ} (χ : EdgeColoring n k) : Prop :=
  ∀ S : Finset (Fin n), S.card = 4 → 5 ≤ (edgeColors χ S).card

/-- f(n): the minimum number of colors k for which there exists a
    K₄-five-colored edge coloring of K_n. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ χ : EdgeColoring n k, IsK4FiveColored χ}

/--
Erdős Problem #136 – Erdős–Gyárfás bounds [Er97b]:
For all sufficiently large n, (5/6)(n-1) < f(n) < n.
Erdős and Gyárfás also established the exact value f(9) = 8.
-/
theorem erdos136_bounds :
    ∀ᶠ n : ℕ in atTop,
      (5 : ℝ) / 6 * ((n : ℝ) - 1) < (f n : ℝ) ∧ (f n : ℝ) < (n : ℝ) :=
  sorry

/--
Special value: f(9) = 8, proved by Erdős and Gyárfás [Er97b].
-/
theorem erdos136_f9 : f 9 = 8 :=
  sorry

/--
Erdős Problem #136 – asymptotic result
(Bennett–Cushman–Dudek–Pralat [BCDP22]; shorter proof by Joos–Mubayi [JoMu22]):
f(n) ~ (5/6)n. That is, for every ε > 0 and all sufficiently large n,
|(f n) / n - 5/6| < ε.
-/
theorem erdos136_asymptotic :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      |(f n : ℝ) / (n : ℝ) - 5 / 6| < ε :=
  sorry

end
