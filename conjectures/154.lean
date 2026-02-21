import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open Filter Real Finset Topology

noncomputable section

/-- A finite set of natural numbers is a Sidon set (also called a B₂ set) if all
    pairwise sums a + b (allowing a = b) are distinct: whenever a + b = c + d
    with a, b, c, d ∈ A, we have {a, b} = {c, d} as multisets. Equivalently,
    all differences a - b with a ≠ b and a, b ∈ A are distinct. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The sumset A + A = {a + b | a, b ∈ A}. -/
def sumset (A : Finset ℕ) : Finset ℕ := Finset.image₂ (· + ·) A A

/-- The fraction of elements in a finite set of naturals that are congruent to r modulo m. -/
noncomputable def modFraction (m r : ℕ) (S : Finset ℕ) : ℝ :=
  ((S.filter (fun n => n % m = r)).card : ℝ) / (S.card : ℝ)

/--
Erdős Problem #154 [ESS94]:

Let A ⊂ {1,...,N} be a Sidon set with |A| ∼ N^(1/2). Must A + A be
well-distributed over all small moduli? In particular, must about half
the elements of A+A be even and half odd?

Proved in the affirmative. Lindström [Li98] showed that A itself is
well-distributed modulo small integers (e.g. |A ∩ {evens}| ≈ |A|/2),
subsequently strengthened by Kolountzakis [Ko99]. The extension to A + A
follows immediately from the Sidon property: if A has e even and o odd
elements, then A + A has exactly e*(e+1)/2 + o*(o+1)/2 even elements
and e*o odd elements (all distinct by the Sidon property), and the
distribution is approximately 1/2 each when e ≈ o ≈ |A|/2.

Formalized as: for any sequence (Aₙ)ₙ of Sidon sets Aₙ ⊂ {0,...,n}
with |Aₙ| / √n → 1 as n → ∞, and any fixed modulus m ≥ 1 and
residue 0 ≤ r < m, the fraction of elements of Aₙ + Aₙ in residue
class r mod m tends to 1/m.
-/
theorem erdos_problem_154 :
    ∀ (A : ℕ → Finset ℕ),
      (∀ n, IsSidonSet (A n)) →
      (∀ n, (A n) ⊆ Finset.range (n + 1)) →
      Tendsto (fun n => ((A n).card : ℝ) / Real.sqrt n) atTop (𝓝 1) →
      ∀ (m : ℕ), 1 ≤ m →
        ∀ r < m,
          Tendsto (fun n => modFraction m r (sumset (A n))) atTop (𝓝 (1 / (m : ℝ))) :=
  sorry

end
