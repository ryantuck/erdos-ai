import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Nat

noncomputable section

/--
A natural number n is "representable" if it can be written as p + 2^k + 2^l
where p is prime and k, l ≥ 0 (so 2^0 = 1 is allowed). The predicate is
defined for every n; the restriction to odd n happens in `erdos9Set`.
-/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ p k l : ℕ, Nat.Prime p ∧ n = p + 2 ^ k + 2 ^ l

/--
The set A of all odd integers ≥ 1 that are NOT of the form p + 2^k + 2^l.

The conjunct `1 ≤ n` is implied by `Odd n` (0 is even) and is kept only to
mirror the source's "odd integers ≥ 1". Note the smallest representable
number is 4 (p ≥ 2 and 2^k, 2^l ≥ 1), so 1 and 3 belong to A. The sequence
of elements of A is OEIS A006286.
-/
def erdos9Set : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ Odd n ∧ ¬IsRepresentable n}

/--
The counting function for a set S ⊆ ℕ: the number of elements in S ∩ {0, ..., N}.
(`Set.Iic N` in ℕ is the finite set {0, …, N}, so the intersection is finite
and `Set.ncard` is its genuine cardinality.)
-/
noncomputable def countingFunction (S : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (S ∩ Set.Iic N)

/--
The upper density of a set S ⊆ ℕ:
  lim sup_{N → ∞} |S ∩ {0, ..., N}| / (N + 1)

The denominator N + 1 is exactly |{0, …, N}|, so this agrees with the usual
upper density limsup_N |S ∩ [1, N]| / N (the two ratios differ by O(1/N)).
The sequence lies in [0, 1], so the ℝ-valued `Filter.limsup` is a genuine
(finite) limit superior, no boundedness side conditions needed.
-/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => (countingFunction S N : ℝ) / (N + 1 : ℝ)) Filter.atTop

/--
Erdős Problem #9 (OPEN) [Er77c, ErGr80, Er85c, Er92c, Er95 p.167, Er97, Er97c, Er97e]:

Let A be the set of all odd integers ≥ 1 not of the form p + 2^k + 2^l
(where k, l ≥ 0 and p is prime). Is the upper density of A positive?

**Status**: OPEN ("This is open, and cannot be resolved with a finite
computation." — erdosproblems.com/9, page edition 20 January 2026, accessed
2026-03-05; the teorth/erdosproblems metadata mirror agrees: state open,
last update 2025-08-31). This theorem states the conjectured "yes" direction
of the question as a direct assertion; the upstream formal-conjectures
encoding is the question form `erdos_9 : answer(sorry) ↔ 0 < Erdos9A.upperDensity`,
whose right-hand side is exactly the proposition asserted here.

**Known partial results** (from the problem page):
- In [Er77c] Erdős credits Schinzel with proving that there are infinitely
  many odd integers not of this form, but gives no reference (formalized
  below as `erdos_problem_9.variants.infinite`).
- Crocker [Cr71] proved there are ≫ log log N such integers in {1, …, N}.
- Pan [Pa11] improved this to ≫_ε N^(1-ε) for any ε > 0.
  (Neither quantitative bound is formalized here: both need `Real.log` /
  real exponents, machinery not present in this file.)
- Erdős believed the positive-density claim cannot be proved by covering
  systems, i.e. integers of the form p + 2^k + 2^l exist in every infinite
  arithmetic progression (formalized below as
  `erdos_problem_9.variants.representable_in_every_ap`).

The sequence of such numbers is A006286 in the OEIS. See also problems
#10, #11, and #16. This is discussed in problem A19 of Guy's collection
[Gu04]. Tags: number theory, additive basis, primes.

References ([Er77c] as it appears in the upstream formal-conjectures file
for this problem; [ErGr80] and [Gu04] from sibling files in this repository;
the site's /latex/9 and /bibs payloads were not captured in the session
logs, so the remaining keys carry no bibliographic data — DEFERRED, not
fabricated):
- [Er77c] Erdős, P., _Problems and results on combinatorial number theory. III_.
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in
  combinatorial number theory. Monographies de L'Enseignement Mathématique
  (1980).
- [Gu04] Guy, Richard K., _Unsolved problems in number theory_. 3rd ed.,
  Springer (2004), xviii+437. Problem A19.
- [Cr71] Crocker (1971) — source of the ≫ log log N bound; title/venue not
  recovered.
- [Pa11] Pan (2011) — source of the ≫_ε N^(1-ε) bound; title/venue not
  recovered.
- [Er85c], [Er92c], [Er95], [Er97], [Er97c], [Er97e] — keys only.
-/
theorem erdos_problem_9 : upperDensity erdos9Set > 0 :=
  sorry

/--
Erdős Problem #9, infinitude variant (SOLVED): the set A of odd integers ≥ 1
not of the form p + 2^k + 2^l is infinite. In [Er77c] Erdős credits Schinzel
with this result, but gives no reference. The upstream formal-conjectures
file carries the same statement as `erdos_9.variants.infinite`
(category `research solved`).
-/
theorem erdos_problem_9.variants.infinite : erdos9Set.Infinite :=
  sorry

/--
Erdős Problem #9, covering-systems obstruction (OPEN — Erdős's belief, not a
theorem): integers of the form p + 2^k + 2^l exist in every infinite
arithmetic progression. From the problem page: "Erdős believed this cannot be
proved by covering systems, i.e. integers of the form p+2^k+2^l exist in
every infinite arithmetic progression." A covering-systems proof of the main
conjecture would exhibit a residue class containing no representable number;
this statement says no such class exists. Encoded over ℕ: every residue
class {a + kd : k ∈ ℕ} with d > 0 contains a representable number.
-/
theorem erdos_problem_9.variants.representable_in_every_ap :
    ∀ a d : ℕ, 0 < d → ∃ k : ℕ, IsRepresentable (a + k * d) :=
  sorry

end
