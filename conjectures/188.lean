import Mathlib.Analysis.InnerProductSpace.PiL2

/--
Erdős Problem #188 [ErGr79, ErGr80]:

What is the smallest k such that ℝ² can be red/blue coloured with no pair
of red points unit distance apart, and no k-term arithmetic progression of
blue points with distance 1?

An arithmetic progression of blue points with distance 1 means k points of
the form p, p + v, p + 2v, …, p + (k−1)v where ‖v‖ = 1, all coloured blue.

Known bounds: k ≥ 6 (Tsaturian, 2017). Erdős and Graham claim k ≤ 10⁷
('more or less'), but give no proof.
-/
theorem erdos_problem_188 :
    ∃ k : ℕ, ∃ f : EuclideanSpace ℝ (Fin 2) → Bool,
      -- No two red (true) points at unit distance
      (∀ x y : EuclideanSpace ℝ (Fin 2),
        f x = true → f y = true → ‖x - y‖ = 1 → False) ∧
      -- No k-term arithmetic progression of blue (false) points with step distance 1
      (∀ (p v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 →
        ¬∀ i : Fin k, f (p + (i : ℕ) • v) = false) :=
  sorry
