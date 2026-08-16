import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open Real Filter

/-!
# Erdős Problem #18

We call m practical if every integer 1 ≤ n < m is the sum of distinct divisors
of m. If m is practical then let h(m) be such that h(m) many divisors always
suffice (i.e., h(m) is the least k such that every 1 ≤ n < m is the sum of at
most k distinct divisors of m).

Three questions [verbatim from the source page]:
"Are there infinitely many practical m such that h(m) < (log log m)^{O(1)}?
Is it true that h(n!) < n^{o(1)}? Or perhaps even h(n!) < (log n)^{O(1)}?"

Known: it is easy to see that almost all numbers are not practical. Erdős
originally showed that h(n!) < n. Vose [Vo85] proved the existence of
infinitely many practical m such that h(m) ≪ (log m)^(1/2). The reward of
$250 is offered in [Er81h], apparently (although the source page notes this
is not entirely clear) for a proof or disproof of whether h(n!) < (log n)^O(1).

Status: OPEN ("cannot be resolved with a finite computation"), $250 prize
banner — erdosproblems.com/18, page edition 20 January 2026, accessed
2026-02-24 (recovered from the original pipeline session's page captures);
cross-checked open per the teorth/erdosproblems metadata mirror
(data/problems.yaml entry 18, last update 2025-08-31; note the mirror's
prize field says "no" while the page banner shows $250 — the page itself
flags the prize attribution as "not entirely clear").

Encoding notes:
- All three questions are open yes/no questions; per this pipeline's
  convention the theorems assert the conjectured ("yes") direction directly
  (no `answer()` elaborator exists here). For Conjecture (3) Erdős offered
  the prize for a proof *or disproof*, so the truth value is genuinely
  uncertain; the direct assertion records the direction asked.
- `practicalH m = 0` for non-practical m (the defining set is empty and
  `Nat.sInf ∅ = 0`). This is harmless: `erdos_problem_18a` constrains m to
  be practical, and n! is practical for every n (see
  `erdos_problem_18.variants.factorial_practical`).
- `Real.log` is 0 on nonpositive inputs and `rpow` of a nonpositive base is
  degenerate for small m/n; both are harmless under the `m ≥ N` /
  `∀ᶠ n in atTop` quantification, which only constrains large arguments.

Related: problems #304 and #825 (source page "See also"). The sequence of
practical numbers is A005153 in the OEIS. Tags: number theory, divisors,
factorials.

## References

Recovered from erdosproblems.com/latex/18 (two agreeing log captures):
- [Er81h] Erdős, P., _Some problems and results on additive and
  multiplicative number theory_. Analytic number theory (Philadelphia, Pa.,
  1980) (1981), 171-182. [Problem cited at p.172.]
- [Vo85] Vose, Michael D., _Egyptian fractions_. Bull. London Math. Soc.
  (1985), 21-24.

Stubs (keys from the problem page; bibliographic data NOT in the recovered
/latex/18 source — sibling-corpus data only, flagged, not source-verified):
- [Er74b] Erdős, P. (1974). [No further data recovered.]
- [Er79] Erdős, P., _Some unconventional problems in number theory_ (1979).
  [Corpus disagreement: Math. Mag. 52, 67-70 vs Acta Math. Acad. Sci.
  Hungar. 33, 71-80 — two 1979 Erdős papers share this title; unresolved.]
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
  combinatorial number theory_. Monographies de L'Enseignement Mathématique
  (1980).
- [Er95] Erdős, P., _Some of my favourite problems in various branches of
  combinatorics_. Combinatorics '94 (Catania), Congressus Numerantium 107
  (1995).
- [Er96b] Erdős, P., _Some problems I presented or planned to present in my
  short talk_. Analytic number theory, Vol. 1 (Allerton Park, IL, 1995)
  (1996), 333-335.
- [Er98] Erdős, P., _Some of my new and almost new problems and results in
  combinatorial number theory_. Number theory (Eger, 1996) (1998), 169-180.
-/

/-- m is practical if every integer 1 ≤ n < m can be represented as a sum
    of distinct divisors of m. -/
def IsPractical (m : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n < m →
    ∃ S : Finset ℕ, S ⊆ Nat.divisors m ∧ S.sum id = n

/-- For a practical number m, practicalH m is the minimum k such that every
    integer 1 ≤ n < m can be expressed as the sum of at most k distinct
    divisors of m.

    For non-practical m the defining set is empty and `Nat.sInf ∅ = 0`, so
    `practicalH m = 0`; every use below either hypothesizes practicality or
    applies this to n!, which is practical. -/
noncomputable def practicalH (m : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ n : ℕ, 1 ≤ n → n < m →
    ∃ S : Finset ℕ, S ⊆ Nat.divisors m ∧ S.card ≤ k ∧ S.sum id = n}

/--
Erdős Problem #18 [Er74b, Er79, ErGr80, Er81h (p.172), Er95, Er96b, Er98]:

Conjecture (1): There are infinitely many practical m such that
h(m) < (log log m)^O(1), i.e., there exists a constant C > 0 such that
infinitely many practical m satisfy h(m) < (log log m)^C.

Open yes/no question, asserted here in the conjectured ("yes") direction.
Vose [Vo85] proved the weaker bound h(m) ≪ (log m)^(1/2) for infinitely
many practical m (see `erdos_problem_18.variants.vose`).
-/
theorem erdos_problem_18a :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∃ m : ℕ, m ≥ N ∧ IsPractical m ∧
      (practicalH m : ℝ) < (Real.log (Real.log (m : ℝ))) ^ C :=
  sorry

/--
Erdős Problem #18 [Er74b, Er79, ErGr80, Er81h (p.172), Er95, Er96b, Er98]:

Conjecture (2): h(n!) < n^o(1), i.e., for every ε > 0, for all
sufficiently large n, h(n!) < n^ε.

Open yes/no question, asserted here in the conjectured ("yes") direction.
Implied by Conjecture (3), since (log n)^C < n^ε eventually.
-/
theorem erdos_problem_18b :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (practicalH n.factorial : ℝ) < (n : ℝ) ^ ε :=
  sorry

/--
Erdős Problem #18 [Er74b, Er79, ErGr80, Er81h (p.172), Er95, Er96b, Er98]:

Conjecture (3): h(n!) < (log n)^O(1), i.e., there exists a constant C > 0
such that for all sufficiently large n, h(n!) < (log n)^C.

Erdős offered $250 for a proof or disproof of this statement [Er81h, p.172]
(the source page notes the attribution of the prize to exactly this
statement "is not entirely clear"). Since the prize covers a disproof as
well, the truth value is genuinely uncertain; the direct assertion here
records the question's asked direction, per this pipeline's convention for
open problems.
-/
theorem erdos_problem_18c :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (practicalH n.factorial : ℝ) < (Real.log (n : ℝ)) ^ C :=
  sorry

/--
Supporting lemma (implicit in the problem; true): n! is practical for every
n. (For n = 0, 1 this is vacuous; in general, writing 1 ≤ m < n! in
factorial base m = ∑_{i<n} aᵢ·i! with 0 ≤ aᵢ ≤ i exhibits m as a sum of
distinct divisors of n!.) This is what makes `practicalH n.factorial` in
Conjectures (2) and (3) mean the genuine h(n!) rather than the junk value 0.

[Added by review; not compile-verified.]
-/
theorem erdos_problem_18.variants.factorial_practical (n : ℕ) :
    IsPractical n.factorial :=
  sorry

/--
Known result (Erdős, source page remark: "Erdős originally showed that
h(n!) < n"): for every n ≥ 1, h(n!) < n. (The factorial-base greedy
representation uses at most n - 1 distinct divisors of n!; the hypothesis
1 ≤ n is needed since practicalH 0! = practicalH 1 = 0 is not < 0.
Verified by hand for n = 1, 2, 3, 4: h(1) = 0, h(2) = 1, h(6) = 2,
h(24) = 3.)

[Added by review; not compile-verified.]
-/
theorem erdos_problem_18.variants.erdos_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    practicalH n.factorial < n :=
  sorry

/--
Known result (Vose [Vo85], source page remark): there exist infinitely many
practical m such that h(m) ≪ (log m)^(1/2), i.e., there is a constant
C > 0 with infinitely many practical m satisfying h(m) < C·(log m)^(1/2).
This resolves the (log m)^(1/2) weakening of Conjecture (1); the conjecture
proper asks for (log log m)^O(1).

[Added by review; not compile-verified.]
-/
theorem erdos_problem_18.variants.vose :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∃ m : ℕ, m ≥ N ∧ IsPractical m ∧
      (practicalH m : ℝ) < C * (Real.log (m : ℝ)) ^ ((1 : ℝ) / 2) :=
  sorry
