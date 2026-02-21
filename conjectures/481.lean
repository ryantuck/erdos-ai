import Mathlib.Data.List.Nodup
import Mathlib.Data.Real.Basic

noncomputable section

/-- The affine map transformation T from Erdős Problem #481.
    Given parameters (aᵢ, bᵢ) and a sequence A = (x₁, ..., xₙ),
    T(A) is the sequence (aᵢ * xⱼ + bᵢ) for 1 ≤ j ≤ n, 1 ≤ i ≤ r. -/
def affineTransform481 (params : List (ℕ × ℕ)) (A : List ℤ) : List ℤ :=
  A.flatMap (fun x => params.map (fun ⟨a, b⟩ => (a : ℤ) * x + (b : ℤ)))

/-- Iterate the affine transform starting from A₁ = [1].
    iterateAffine481 params 0 = [1] and iterateAffine481 params (k+1) = T(iterateAffine481 params k). -/
def iterateAffine481 (params : List (ℕ × ℕ)) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => affineTransform481 params (iterateAffine481 params n)

/--
Erdős Problem #481 [ErGr80, p.96]:

Let a₁, ..., aᵣ, b₁, ..., bᵣ ∈ ℕ with ∑ᵢ 1/aᵢ > 1.
For a finite sequence A = (x₁, ..., xₙ) of (not necessarily distinct) integers,
let T(A) denote the sequence of length rn given by
  (aᵢ xⱼ + bᵢ)_{1 ≤ j ≤ n, 1 ≤ i ≤ r}.
If A₁ = (1) and A_{k+1} = T(Aₖ), then there must be some Aₖ with
repeated elements.
-/
theorem erdos_problem_481
    (params : List (ℕ × ℕ))
    (hne : params ≠ [])
    (hpos : ∀ p ∈ params, 0 < p.1)
    (hsum : (params.map (fun p => (1 : ℝ) / (p.1 : ℝ))).sum > 1) :
    ∃ k : ℕ, ¬ (iterateAffine481 params k).Nodup :=
  sorry

end
