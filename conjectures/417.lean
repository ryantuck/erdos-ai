import Mathlib.Data.Nat.Totient
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter

noncomputable section

/--
V'(x) counts the number of distinct values in {φ(m) : 1 ≤ m ≤ x},
i.e., the number of distinct totient values achieved by inputs up to x.
-/
def totientImageCount (x : ℕ) : ℕ :=
  (Finset.image Nat.totient (Finset.range (x + 1))).card

/--
V(x) counts the number of n ≤ x such that φ(m) = n is solvable for some m,
i.e., the number of totient values up to x (where m is unrestricted).

We bound the search for m by (x * x + 1) since φ(m) ≤ x implies m is bounded.
-/
def totientValues (x : ℕ) : ℕ :=
  {n ∈ Finset.range (x + 1) | ∃ m ∈ Finset.range (x * x + 1), Nat.totient m = n}.card

/--
Erdős Problem #417 [Er79e, ErGr80, Er98]:

Let V'(x) = #{φ(m) : 1 ≤ m ≤ x} and V(x) = #{φ(m) ≤ x : 1 ≤ m}.
Does lim V(x)/V'(x) exist? Is it > 1?

It is trivial that V'(x) ≤ V(x). Erdős suggests the limit may be infinite.
-/
theorem erdos_problem_417 :
    ∃ L : ℝ, 1 < L ∧
      Tendsto (fun x : ℕ => (totientValues x : ℝ) / (totientImageCount x : ℝ))
        atTop (nhds L) :=
  sorry
