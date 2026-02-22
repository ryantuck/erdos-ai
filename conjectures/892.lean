import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Erdős Problem #892

Is there a necessary and sufficient condition for a sequence of integers
b₁ < b₂ < ··· that ensures there exists a primitive sequence a₁ < a₂ < ···
(i.e. no element divides another) with aₙ ≪ bₙ for all n?

In particular, is this always possible if there are no non-trivial solutions
to gcd(bᵢ, bⱼ) = bₖ?

A problem of Erdős, Sárközy, and Szemerédi [ESS68].
-/

/-- A sequence of natural numbers is *primitive* if no element divides any other. -/
def IsPrimitiveSeq (a : ℕ → ℕ) : Prop :=
  ∀ i j, i ≠ j → ¬(a i ∣ a j)

/--
Erdős Problem #892 (particular case) [Er98]:

If b : ℕ → ℕ is a strictly increasing sequence of positive integers such that
gcd(bᵢ, bⱼ) ≠ bₖ for all distinct i, j and all k (no non-trivial GCD solutions),
then there exists a strictly increasing primitive sequence a : ℕ → ℕ with
aₙ ≪ bₙ (i.e. there exists C such that aₙ ≤ C · bₙ for all n).
-/
theorem erdos_problem_892
    (b : ℕ → ℕ)
    (hb_pos : ∀ n, 0 < b n)
    (hb_mono : StrictMono b)
    (hb_gcd : ∀ i j, i ≠ j → ∀ k, Nat.gcd (b i) (b j) ≠ b k) :
    ∃ (a : ℕ → ℕ) (C : ℕ),
      0 < C ∧
      StrictMono a ∧
      IsPrimitiveSeq a ∧
      ∀ n, a n ≤ C * b n :=
  sorry
