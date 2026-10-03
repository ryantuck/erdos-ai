-- [AI - Claude Opus 5.5]: Erdős Problem 109 — second-pass formalization
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Set Filter

/-!
# Erdős Problem #109

*Source:* [erdosproblems.com/109](https://www.erdosproblems.com/109). Status at capture
(2026-02-19 and 2026-03-05; page last edited 27 September 2025): **PROVED** ("This has been
solved in the affirmative."). The `teorth/erdosproblems` mirror now records
`proved (Lean)` (formal status updated 2026-08-23). [ErGr80, p.85]

Any $A \subseteq \mathbb{N}$ of positive upper density contains a sumset $B + C$ where both
$B$ and $C$ are infinite.

Remarks recorded on the page: the Erdős sumset conjecture, proved by Moreira, Richter and
Robertson [MRR19]. See also Problem #656.

**Encoding.** The upper density is the `limsup` of $|A \cap \{0, \ldots, n-1\}| / n$. The
sequence lies in $[0, 1]$, with value $0$ at $n = 0$ because ℝ-division by zero is $0$. So
the real `limsup` is the genuine one, not a junk value.

Tags: additive combinatorics.

## References

* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
  number theory_. Monographies de L'Enseignement Mathématique (1980).
* [MRR19] Moreira, J., Richter, F. K. and Robertson, D., _A proof of a sumset conjecture of
  Erdős_. Ann. of Math. (2) 189 (2019), 605–652.

(Provenance: [ErGr80] comes from many agreeing `/latex` extractions in the original pipeline's
logs. [MRR19] comes from upstream formal-conjectures `ErdosProblems/109.lean` at `df3f12d`.)
-/

/--
The upper density of a set A ⊆ ℕ, defined as
  lim sup_{N → ∞} |A ∩ {0, …, N-1}| / N.
Expressed via limsup of the sequence n ↦ |A ∩ Finset.range n| / n.
-/
noncomputable def upperDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
  Filter.limsup (fun (n : ℕ) => (((Finset.range n).filter (· ∈ A)).card : ℝ) / n) atTop

/--
The sumset B + C = {b + c | b ∈ B, c ∈ C}.
-/
def sumset (B C : Set ℕ) : Set ℕ :=
  {n | ∃ b ∈ B, ∃ c ∈ C, n = b + c}

/--
Erdős Problem #109 [ErGr80,p.85] (PROVED):

Any A ⊆ ℕ of positive upper density contains a sumset B + C where both
B and C are infinite.

This is the Erdős sumset conjecture. Proved by Moreira, Richter, and
Robertson [MRR19].
-/
theorem erdos_problem_109
    (A : Set ℕ) [DecidablePred (· ∈ A)]
    (hA : 0 < upperDensity A) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ sumset B C ⊆ A :=
  sorry
