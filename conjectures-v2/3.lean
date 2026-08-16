import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
The set A ⊆ ℕ has divergent reciprocal sum, i.e., ∑_{n ∈ A} 1/n = ∞.
Expressed as: for every bound M, some finite subset of A has reciprocal sum ≥ M.

For the nonnegative terms 1/n this unbounded-partial-sums form is equivalent to
divergence of the series (and to ¬ Summable, the encoding used by the upstream
formal-conjectures statement of this problem). If 0 ∈ A the term 1/0 = 0 in ℝ
contributes nothing, so membership of 0 neither helps nor hurts divergence.
-/
def DivergentReciprocalSum (A : Set ℕ) : Prop :=
  ∀ M : ℝ, ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ A ∧
    M ≤ ∑ n ∈ F, (1 : ℝ) / (n : ℝ)

/--
The set A contains an arithmetic progression of length k:
there exist a, d ∈ ℕ with d ≥ 1 such that {a, a+d, a+2d, …, a+(k-1)d} ⊆ A.

The requirement d ≥ 1 makes the progression non-trivial (k distinct terms for
k ≥ 1). For k = 0 and k = 1 the condition is trivially, respectively easily,
satisfied, as it should be.
-/
def ContainsArithProg (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

/--
Erdős Problem #3 [Er74b, Er75b, Er77c, ErGr79, Er80, Er80c, ErGr80, Er81,
Er82e, Er83, Er83c, Er85c, Er90, Er97c, Va99]:

"If A ⊆ ℕ has ∑_{n ∈ A} 1/n = ∞ then must A contain arbitrarily long
arithmetic progressions?"

This is the Erdős conjecture on arithmetic progressions, one of his most
famous open problems. The problem is OPEN, with a $5000 prize
(erdosproblems.com/3, page last edited 23 January 2026, accessed 2026-02-18;
status cross-checked open against the teorth/erdosproblems metadata mirror).
The source phrases it as a yes/no question; this statement asserts the
conjectured "yes" direction, which is also the right-hand side of the
upstream formal-conjectures encoding `answer(sorry) ↔ …`.

Remarks from the source page: the problem is essentially asking for good
bounds on r_k(N), the size of the largest subset of {1,…,N} without a
non-trivial k-term arithmetic progression; a bound like
r_k(N) ≪_k N/((log N)(log log N)²) would be sufficient. Even the case k = 3
is non-trivial, but was proved by Bloom and Sisask [BlSi20]; much better
bounds for r₃(N) were subsequently proved by Kelley and Meka [KeMe23].
Green and Tao [GrTa17] proved r₄(N) ≪ N/(log N)^c for some small constant
c > 0. Gowers [Go01] proved r_k(N) ≪ N/(log log N)^{c_k}; the current best
bounds for general k are due to Leng, Sah, and Sawhney [LSS24]:
r_k(N) ≪ N/exp((log log N)^{c_k}). Erdős [Er83c] thought this conjecture was
the "only way to approach" the conjecture that there are arbitrarily long
arithmetic progressions of prime numbers, now a theorem of Green and Tao
[GrTa08] (see Erdős problem [219]). In [Er81] Erdős makes the stronger
conjecture r_k(N) ≪_C N/(log N)^C for every C > 0, now known for k = 3 by
Kelley–Meka — see problem [140]. See also problems [139] and [142]; the
problem is discussed as problem A5 of Guy's collection [Gu04]. Related OEIS
sequences: A003002, A003003, A003004, A003005.

References (recovered from the archived page and sibling files in this repo;
the /latex/3 bibliography was never captured, so entries marked "stub" lack
data that is DEFERRED, not fabricated):
- [Er74b] Erdős, P. (1974). (stub; sibling files disagree on the title)
- [Er75b] Erdős, P. (1975). (stub; sibling files disagree on the title)
- [Er77c] Erdős, P., Problems and results on combinatorial number theory.
  III. Number Theory Day (Proc. Conf., Rockefeller Univ., New York, 1976)
  (1977), 43-72.
- [ErGr79] Erdős, P. and Graham, R., Old and new problems and results in
  combinatorial number theory (1979). (stub; sibling files disagree on the
  subtitle)
- [Er80] Erdős, P., A survey of problems in combinatorial number theory.
  Ann. Discrete Math. (1980). (stub; thin sibling provenance)
- [Er80c] Erdős, P. (1980). (stub)
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in
  combinatorial number theory. Monographies de L'Enseignement Mathématique
  (1980). (cited at p. 11)
- [Er81] Erdős, P., On the combinatorial problems which I would most like
  to see solved. Combinatorica 1 (1981), 25-42.
- [Er82e] Erdős, P., Problems and results on finite and infinite
  combinatorial analysis II. L'Enseignement Math. 27 (1982), 163-176.
- [Er83] Erdős, P. (1983). (stub)
- [Er83c] Erdős, P., Old and new problems in combinatorial analysis and
  graph theory (1983). (stub; no venue data)
- [Er85c] Erdős, P. (1985). (stub; sibling files disagree on the title)
- [Er90] Erdős, P., Some of my favourite unsolved problems. A tribute to
  Paul Erdős (1990), 467-478.
- [Er97c] Erdős, P., Some recent problems and results in graph theory.
  Discrete Math. (1997). (majority sibling title; one sibling disagrees)
- [Va99] Various, Some of Paul's favorite problems. Booklet produced for
  the conference "Paul Erdős and his mathematics", Budapest (1999). (cited
  as item 1.28)
- [BlSi20] Bloom, T. F. and Sisask, O. (2020). (stub; authors and year from
  page prose)
- [KeMe23] Kelley, Z. and Meka, R., Strong Bounds for 3-Progressions.
  arXiv:2302.05537 (2023).
- [GrTa17] Green, B. and Tao, T. (2017). (stub)
- [Go01] Gowers, W. T. (2001). (stub)
- [LSS24] Leng, J., Sah, A. and Sawhney, M., Improved bounds for
  Szemerédi's theorem. arXiv:2402.17995 (2024).
- [GrTa08] Green, B. and Tao, T. (2008). (stub)
- [Gu04] Guy, R. K., Unsolved problems in number theory (2004), xviii+437.
-/
theorem erdos_problem_3
    (A : Set ℕ)
    (hA : DivergentReciprocalSum A) :
    ∀ k : ℕ, ContainsArithProg A k :=
  sorry

/--
Erdős Problem #3, k = 3 case [BlSi20]:

Even the case k = 3 is non-trivial, but was proved by Bloom and Sisask
(2020): every A ⊆ ℕ with ∑_{n ∈ A} 1/n = ∞ contains a non-trivial three-term
arithmetic progression. (Much better bounds for r₃(N) were subsequently
proved by Kelley and Meka [KeMe23].) SOLVED, per the source page.
-/
theorem erdos_problem_3.variants.k_eq_3
    (A : Set ℕ)
    (hA : DivergentReciprocalSum A) :
    ContainsArithProg A 3 :=
  sorry
