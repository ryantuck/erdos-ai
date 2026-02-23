import Mathlib.Analysis.InnerProductSpace.PiL2

/--
Erdős Problem #1127 (Independent of ZFC):

Can ℝⁿ be decomposed into countably many sets, such that within each set all the
pairwise distances are distinct?

This is true assuming the continuum hypothesis for n = 1 (Erdős-Kakutani [ErKa43]),
for n = 2 (Davies [Da72]), and for all n (Kunen [Ku87]). The dependence on the
continuum hypothesis is necessary by a result of Erdős and Hajnal.
-/
theorem erdos_problem_1127 (n : ℕ) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℕ,
      ∀ a b c d : EuclideanSpace ℝ (Fin n),
        f a = f b → f a = f c → f a = f d →
        a ≠ b → c ≠ d →
        dist a b = dist c d →
        ({a, b} : Set (EuclideanSpace ℝ (Fin n))) = {c, d} :=
  sorry
