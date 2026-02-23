import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic

open Finset

/-- A positive odd integer `m` is a Sierpinski number if `2^k * m + 1` is composite
    for all `k ≥ 0`. -/
def IsSierpinskiNumber (m : ℕ) : Prop :=
  0 < m ∧ ¬ 2 ∣ m ∧ ∀ k : ℕ, ¬ Nat.Prime (2 ^ k * m + 1)

/-- A finite set of primes `P` is a covering set for `m` if every `2^k * m + 1` is
    divisible by some prime in `P`. -/
def HasFiniteCoveringSet (m : ℕ) (P : Finset ℕ) : Prop :=
  (∀ p ∈ P, Nat.Prime p) ∧ ∀ k : ℕ, ∃ p ∈ P, p ∣ (2 ^ k * m + 1)

/--
Erdős Problem #1113 [ErGr80, p.27]:
A positive odd integer m such that none of 2^k * m + 1 are prime for k ≥ 0 is called a
Sierpinski number. A set of primes P is a covering set for m if every 2^k * m + 1 is
divisible by some p ∈ P.

Are there Sierpinski numbers with no finite covering set of primes?

Erdős and Graham conjectured the answer is yes, since otherwise this would imply there
are infinitely many Fermat primes. Filaseta, Finch, and Kozek [FFK08] give evidence
that m = 734110615000775^4 is a Sierpinski number without a covering set.
-/
theorem erdos_problem_1113 :
    ∃ m : ℕ, IsSierpinskiNumber m ∧ ∀ P : Finset ℕ, ¬ HasFiniteCoveringSet m P :=
  sorry
