import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

/-!
# Erdős Problem #30

Let $h(N)$ be the maximum size of a Sidon set in $\{1,\ldots,N\}$. Is it
true that, for every $\epsilon>0$,
$$h(N) = N^{1/2}+O_\epsilon(N^\epsilon)?$$

A problem of Erdős and Turán.

**Status: OPEN** — banner tooltip: "This is open, and cannot be resolved
with a finite computation." **$1000** prize. (erdosproblems.com/30, page
last edited 23 January 2026, accessed 2026-03-05; the teorth/erdosproblems
metadata mirror agrees: state "open", last update 2025-08-31, prize $1000,
tags "number theory", "sidon sets", "additive combinatorics".)

Remarks from the source page:

- It may even be true that $h(N)=N^{1/2}+O(1)$, but Erdős remarks this is
  perhaps too optimistic. (Formalized below as
  `erdos_problem_30.variants.strong_conjecture`.)
- Erdős and Turán [ErTu41] proved an upper bound of $N^{1/2}+O(N^{1/4})$,
  with an alternative proof by Lindström [Li69]. Both proofs in fact give
  $h(N) \leq N^{1/2}+N^{1/4}+1$. (Formalized below as
  `erdos_problem_30.variants.erdos_turan_upper`.)
- Balogh, Füredi, and Roy [BFR21] improved the bound in the error term to
  $0.998N^{1/4}$. This was further optimised by O'Bryant [OB22]. The
  current record is $h(N)\leq N^{1/2}+0.98183N^{1/4}+O(1)$, due to Carter,
  Hunter, and O'Bryant [CHO25]. (Formalized below as
  `erdos_problem_30.variants.carter_hunter_obryant_upper`.)
- Singer [Si38] was the first to show that $h(N)\geq (1-o(1))N^{1/2}$ for
  all $N$. (Formalized below as `erdos_problem_30.variants.singer_lower`.)
- For a detailed survey of the literature we refer to [OB04].
- See also problems [241] and [840].
- This problem is Problem 31 on Green's open problems list
  (people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf), and is
  discussed in problem C9 of Guy's collection [Gu04].

## References

Problem sources on the page: [Er61] [Er69] [Er70b] [Er70c] [Er72] [Er73]
[Er77c] [Er80e] [Er81] [Er81h, p.174] [Er91] [Er92c] [Er94b] [Er95]
[Er97c] [Va99, 1.18]; remarks cite [ErTu41] [Li69] [BFR21] [OB22] [CHO25]
[Si38] [OB04] [Gu04]. No `/latex/30` fetch exists in the session logs, so
no bibliography could be recovered from the site itself; the entries below
are honest stubs with their provenance flagged, and the rest are keys
only: DEFERRED.

- [ErTu41] Erdős, P. and Turán, P., _On a problem of Sidon in additive
  number theory, and on some related problems_. J. London Math. Soc. 16
  (1941), 212–215. (Stub: details from sibling corpus file
  `conjectures-v2/28.lean`; unverified offline.)
- [Li69] Lindström, B., _An inequality for B₂-sequences_. J. Combinatorial
  Theory (1969), 211–212. (Stub: details from sibling corpus file
  `deepmind/deepmind/987.lean`; unverified offline.)
- [Si38] Singer, J., _A theorem in finite projective geometry and some
  applications to number theory_. Trans. Amer. Math. Soc. (1938). (Stub:
  reviewer knowledge, no corpus source; unverified offline.)
- [OB04] O'Bryant, K., _A complete annotated bibliography of work related
  to Sidon sequences_. Electron. J. Combin., Dynamic Survey (2004). (Stub:
  reviewer knowledge; unverified offline.)
- [BFR21] Balogh, J., Füredi, Z. and Roy, S. (2021). (Key-and-year stub
  from the page prose; no bibliographic data recoverable.)
- [OB22] O'Bryant, K. (2022). (Key-and-year stub from the page prose.)
- [CHO25] Carter, Hunter and O'Bryant (2025). (Key-and-year stub from the
  page prose.)
- [Gu04] Guy, R. K., _Unsolved problems in number theory_. 3rd ed.,
  Springer, 2004. Problem C9. (Stub: details from sibling corpus files
  `deepmind/deepmind/1053.lean`, `deepmind/deepmind/1057.lean`;
  unverified offline.)
- [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat.
  Kutató Int. Közl. 6 (1961), 221–254. (Stub: from sibling corpus files;
  unverified offline.)
- [Er69] Erdős, P., _On some applications of graph theory to number
  theoretic problems_. Publ. Ramanujan Inst. 1 (1969), 131–136. (Stub:
  from sibling corpus files; unverified offline.)
- [Er70b] Erdős, P., _Some applications of graph theory to number
  theory_. Proc. Second Chapel Hill Conf. on Combinatorial Mathematics and
  its Applications (1970), 136–145. (Stub: from
  `deepmind/deepmind/425.lean`; unverified offline.)
- [Er72] Erdős, P., _Quelques problèmes de théorie des nombres_ (1972).
  (Stub: from sibling corpus files; unverified offline.)
- [Er73] Erdős, P., _Problems and results on combinatorial number
  theory_. A survey of combinatorial theory (Proc. Internat. Sympos.,
  Colorado State Univ., Fort Collins, Colo., 1971) (1973), 117–138.
  (Stub: from `deepmind/deepmind/542.lean`; unverified offline.)
- [Er80e] Erdős, P., _Some applications of Ramsey's theorem to additive
  number theory_. European J. Combin. (1980), 43–46. (Stub: from
  `deepmind/deepmind/328.lean`; unverified offline.)
- [Er81h] Erdős, P., _Some problems and results on additive and
  multiplicative number theory_. Analytic number theory (Philadelphia,
  Pa., 1980) (1981), 171–182. This problem: p. 174. (Stub: from
  `conjectures-v2/1101.lean`; unverified offline.)
- [Er94b] Erdős, P., _Some problems in number theory, combinatorics and
  combinatorial geometry_. Math. Pannon. (1994), 261–269. (Stub: from
  `deepmind/deepmind/103.lean`; unverified offline.)
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
  the conference "Paul Erdős and his Mathematics" (Budapest, 1999). This
  problem: §1.18. (Stub: details from sibling corpus files, e.g.
  `deepmind/deepmind/1032.lean`; unverified offline.)
- [Er70c] [Er77c] [Er81] [Er91] [Er92c] [Er95] [Er97c] — keys only; no
  reliable corpus expansion (the corpus's [Er97c] entries conflict):
  DEFERRED.

Related OEIS sequences: A143824, A227590, A003022.
Formalised statement? **Yes** — upstream google-deepmind/formal-conjectures
`FormalConjectures/ErdosProblems/30.lean` (present at HEAD dd1c2beb)
defines `h N := Finset.maxSidonSubsetCard (Finset.Icc 1 N)` and states
`answer(sorry) ↔ ∀ᵉ (ε > 0), (fun N => h N - (N : Real).sqrt) =O[atTop]
fun N => (N : ℝ)^(ε : ℝ)` — the same question, encoded with `IsBigO`;
`sidonMaxCard` below computes the same value.

Tags: number theory, sidon sets, additive combinatorics
https://www.erdosproblems.com/30
-/

/--
A finite set of natural numbers is a **Sidon set** (or B₂ set) if all pairwise
sums are distinct: for a, b, c, d ∈ A with a ≤ b and c ≤ d,
a + b = c + d implies a = c and b = d.

This ordered-pair formulation is equivalent to the symmetric one
("a + b = c + d with a, b, c, d ∈ A forces {a, b} = {c, d}"): sorting each
pair reduces the symmetric statement to this one, and conversely under
a ≤ b, c ≤ d the case a = d ∧ b = c collapses to a = b = c = d. The empty
set and singletons are (vacuously) Sidon, as intended.
-/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → a ≤ b → c ≤ d → a = c ∧ b = d

/--
h(N) is the maximum size of a Sidon set contained in {1, …, N}.

The set of achievable cardinalities is nonempty (the empty set is Sidon,
giving k = 0) and bounded above by N (any qualifying A is a subset of
{1, …, N}), so ℕ's `sSup` is a genuine maximum — no junk values, including
at N = 0 where only A = ∅ qualifies and h(0) = 0.
-/
noncomputable def sidonMaxCard (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ IsSidonSet A ∧ A.card = k}

/--
Erdős Problem #30 [Er61, Er69, Er70b, Er70c, Er72, Er73, Er77c, Er80e, Er81,
Er81h p.174, Er91, Er92c, Er94b, Er95, Er97c, Va99 1.18]:

Let h(N) be the maximum size of a Sidon set in {1,…,N}. Is it true that, for
every ε > 0,
  h(N) = N^{1/2} + O_ε(N^ε)?

A problem of Erdős and Turán ($1000 prize). Erdős and Turán [ErTu41] proved
h(N) ≤ N^{1/2} + N^{1/4} + 1 (alternative proof by Lindström [Li69]; current
record N^{1/2} + 0.98183·N^{1/4} + O(1) [CHO25]). Singer [Si38] showed
h(N) ≥ (1 - o(1))N^{1/2}.

The problem is a yes/no question and is **OPEN**; this theorem asserts the
conjectured ("yes") direction, per this corpus's convention for open
questions. The two-sided bound |h(N) − N^{1/2}| ≤ C·N^ε renders the
equality h(N) = N^{1/2} + O_ε(N^ε); note the lower-bound half is also
genuinely open (Singer's construction gives N^{1/2} − h(N) = O(N^{θ/2})
only for prime-gap exponents θ, far from N^ε). Quantifying over all N ≥ 1
rather than "N sufficiently large" is equivalent here: finitely many
initial N contribute bounded error while N^ε ≥ 1, so C absorbs them.
-/
theorem erdos_problem_30 :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ N : ℕ, 0 < N →
          |((sidonMaxCard N : ℝ) - (N : ℝ) ^ ((1 : ℝ) / 2))| ≤ C * (N : ℝ) ^ ε :=
  sorry

/--
Erdős and Turán [ErTu41] proved h(N) ≤ N^{1/2} + O(N^{1/4}); an alternative
proof was given by Lindström [Li69]. Both proofs in fact give the explicit
bound formalized here, h(N) ≤ N^{1/2} + N^{1/4} + 1, quoted verbatim from
the source page. **Solved.** (The bound also holds trivially at N = 0,
where h(0) = 0 ≤ 1, so no positivity guard is needed.)
-/
theorem erdos_problem_30.variants.erdos_turan_upper :
    ∀ N : ℕ,
      (sidonMaxCard N : ℝ) ≤
        (N : ℝ) ^ ((1 : ℝ) / 2) + (N : ℝ) ^ ((1 : ℝ) / 4) + 1 :=
  sorry

/--
The current record in the error term, due to Carter, Hunter, and O'Bryant
[CHO25], improving Balogh–Füredi–Roy [BFR21] and O'Bryant [OB22]:
h(N) ≤ N^{1/2} + 0.98183·N^{1/4} + O(1). **Solved.** The O(1) is encoded
as a uniform additive constant over all N, equivalent to the eventual form
because h is finite on any initial segment of ℕ.
-/
theorem erdos_problem_30.variants.carter_hunter_obryant_upper :
    ∃ C : ℝ,
      ∀ N : ℕ,
        (sidonMaxCard N : ℝ) ≤
          (N : ℝ) ^ ((1 : ℝ) / 2) + 0.98183 * (N : ℝ) ^ ((1 : ℝ) / 4) + C :=
  sorry

/--
Singer [Si38] was the first to show that h(N) ≥ (1 − o(1))·N^{1/2} (via
perfect difference sets in finite projective planes). **Solved.** The
(1 − o(1)) factor is encoded in the standard way: for every ε > 0 the
bound (1 − ε)·N^{1/2} ≤ h(N) holds for all sufficiently large N.
-/
theorem erdos_problem_30.variants.singer_lower :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (1 - ε) * (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (sidonMaxCard N : ℝ) :=
  sorry

/--
From the remarks on the source page: "It may even be true that
h(N) = N^{1/2} + O(1), but Erdős remarks this is perhaps too optimistic."
**OPEN** — stated as the (speculative) direct assertion; it strengthens
`erdos_problem_30` by replacing C·N^ε with a constant.
-/
theorem erdos_problem_30.variants.strong_conjecture :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 0 < N →
        |((sidonMaxCard N : ℝ) - (N : ℝ) ^ ((1 : ℝ) / 2))| ≤ C :=
  sorry
