import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real.Lemmas

open Classical Filter Finset

noncomputable section

/--
The set of all finite subset sums of a set S ⊆ ℕ:
  P(S) = {∑_{n ∈ B} n : B ⊆ S finite}
-/
def finiteSubsetSums (S : Set ℕ) : Set ℕ :=
  {m : ℕ | ∃ B : Finset ℕ, (↑B : Set ℕ) ⊆ S ∧ B.sum id = m}

/--
The natural density of a set S ⊆ ℕ is 1:
  lim_{N → ∞} |S ∩ {0, ..., N-1}| / N = 1
-/
def HasDensityOne (S : Set ℕ) : Prop :=
  Tendsto (fun N : ℕ => ((Finset.range N).filter (· ∈ S)).card / (N : ℝ))
    atTop (nhds 1)

/--
A cofinite subsequence of a sequence a : ℕ → ℕ is the image of a
restricted to a cofinite index set — equivalently, the range of a
with finitely many terms removed.
-/
def IsCofiniteSubseq (A' : Set ℕ) (a : ℕ → ℕ) : Prop :=
  ∃ I : Finset ℕ, A' = Set.range a \ (a '' ↑I)

/--
Erdős Problem #347 [ErGr80]:

Is there a sequence A = {a₁ ≤ a₂ ≤ ⋯} of positive integers with
  lim a_{n+1} / a_n = 2
such that the set of finite subset sums P(A') has natural density 1
for every cofinite subsequence A' of A?

Here a "cofinite subsequence" means the range of the sequence with
finitely many terms removed.

Solved in the affirmative by ebarschkis (based on ideas of Tao and
van Doorn).
-/
theorem erdos_problem_347 :
    ∃ a : ℕ → ℕ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ a (n + 1)) ∧
      Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ)) atTop (nhds 2) ∧
      ∀ A' : Set ℕ, IsCofiniteSubseq A' a → HasDensityOne (finiteSubsetSums A') :=
  sorry

end
