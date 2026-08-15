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
are infinitely many Fermat primes. Izotov [Iz95] proved that m = 734110615000775^4 is
a Sierpinski number, and Filaseta, Finch, and Kozek [FFK08] gave a detailed argument that
it has no finite covering set.

See also: Problems #203, #276; Guy's Unsolved Problems in Number Theory [Gu04, F13].

Bibliography:
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number theory_. Monographies de L'Enseignement Mathématique (1980).
- [Iz95] Izotov, A., _A note on Sierpinski numbers_. Fibonacci Quart. **33** (1995), 206–207.
- [Gu04] Guy, Richard K., _Unsolved problems in number theory_. (2004).
- [FFK08] Filaseta, M., Finch, C., and Kozek, M., _On powers associated with Sierpinski numbers, Riesel numbers, and Polignac's conjecture_. J. Number Theory **128** (2008), 1916–1940.
-/
theorem erdos_problem_1113 :
    answer(sorry) ↔ (∃ m : ℕ, IsSierpinskiNumber m ∧ ∀ P : Finset ℕ, ¬ HasFiniteCoveringSet m P) :=
  sorry

/-- Filaseta, Finch, and Kozek [FFK08] conjectured that every Sierpinski number is either
    a perfect power or has a finite covering set of primes. This would be a refinement of
    the original question: it predicts that Sierpinski numbers without covering sets exist,
    but only among perfect powers. -/
theorem erdos_problem_1113_fk_variant :
    answer(sorry) ↔ (∀ m : ℕ, IsSierpinskiNumber m →
      (∃ b k : ℕ, 1 < k ∧ m = b ^ k) ∨ (∃ P : Finset ℕ, HasFiniteCoveringSet m P)) :=
  sorry
