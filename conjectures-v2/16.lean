import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter

/--
The set of odd positive integers that cannot be expressed as 2^k + p for any
non-negative integer k and any prime p.

Encoding notes:

- **k ≥ 0 convention.** The exponent `k` ranges over all of ℕ, so `2^0 = 1`
  is a permitted power of 2. This matches Erdős's original paper [Er50] and
  OEIS A006285 (which, per its standard listing 1, 127, 149, 251, 331, ...,
  excludes 3 = 2^0 + 2 — reviewer knowledge, contents not verifiable
  offline). Some formulations of de Polignac's conjecture instead use k ≥ 1,
  under which 3 would enter the set. **The choice is immaterial to
  `erdos_problem_16`:** the two conventions produce sets differing in at most
  the single element 3, and the property "equals the union of an infinite
  arithmetic progression and a density-zero set" is invariant under finite
  symmetric difference (adding finitely many points enlarges D by a finite —
  hence density-zero — set; removing a point of the AP leaves an infinite AP
  tail plus a finite set that can be absorbed into D).
- `Odd n` is false for `n = 0` in Mathlib, so the set contains only positive
  integers; `1` belongs to the set (the smallest value of `2^k + p` is
  `2^0 + 2 = 3`).
- The docstring's prime `p` is the bound variable `p` below (renamed from the
  input file's `q` for consistency; pure α-renaming).
-/
def oddNotPowerOfTwoPlusPrime : Set ℕ :=
  {n : ℕ | Odd n ∧ ∀ (k : ℕ) (p : ℕ), Nat.Prime p → n ≠ 2 ^ k + p}

/--
A set S ⊆ ℕ has natural density zero if |S ∩ {1, ..., N}| / N → 0 as N → ∞.

Encoding notes: `Set.Icc 1 N = {1, ..., N}` is exactly the source's counting
window (no off-by-one; `0 ∉ Icc 1 N`, so membership of `0 ∈ S` is invisible,
as it should be for a density on positive integers); the intersection with the
finite set `Icc 1 N` is finite, so `Set.ncard` is the honest cardinality; at
`N = 0` the field-division convention gives `0 / 0 = 0`, harmless under
`atTop`. Requiring the limit to exist and equal 0 is the standard notion of
natural density zero (equivalently, upper density 0, since the lower density
is trivially ≥ 0).
-/
def HasNaturalDensityZero (S : Set ℕ) : Prop :=
  Tendsto (fun N : ℕ => (Set.ncard (S ∩ Set.Icc 1 N) : ℝ) / (N : ℝ))
    atTop (nhds 0)

/--
A set AP ⊆ ℕ is an infinite arithmetic progression if there exist a, d : ℕ
with d > 0 and AP = {a + m * d | m : ℕ}.

Encoding notes: the condition `0 < d` is essential — without it the singleton
`{a}` would qualify as an "infinite AP". With `d > 0` the set
`{a, a + d, a + 2d, ...}` is genuinely infinite, and one-sided (as it must be
in ℕ), which is the intended reading for a progression inside a set of
positive integers.
-/
def IsInfiniteAP (AP : Set ℕ) : Prop :=
  ∃ (a d : ℕ), 0 < d ∧ AP = {n : ℕ | ∃ m : ℕ, n = a + m * d}

/--
Erdős Problem #16 [Er95, p.167] (DISPROVED — Chen 2023):

> Is the set of odd integers not of the form $2^k+p$ the union of an infinite
> arithmetic progression and a set of density $0$?

**Status: DISPROVED** ("This has been solved in the negative." —
erdosproblems.com/16, page edition 28 December 2025, accessed 2026-02-24;
re-confirmed against the teorth/erdosproblems metadata mirror,
`data/problems.yaml` entry 16: status "disproved (Lean)", last update
2026-02-24 — the mirror further records `formal_status: Lean`, i.e. the
resolution itself has since been verified in Lean, and `formalized: yes`,
last update 2026-05-26; the page capture predates both and still shows
"Formalised statement? No").

Erdős asked whether the set of odd integers not of the form 2^k + p (where p
is prime and k ≥ 0) is the union of an infinite arithmetic progression and a
set of natural density 0. He called this conjecture 'rather silly'.

Using covering congruences, Erdős [Er50] proved that this set contains an
infinite arithmetic progression (see
`erdos_problem_16.variants.erdos_contains_ap`). Chen [Ch23] proved the answer
is no: the set is NOT the union of an infinite arithmetic progression and a
density-0 set.

Formally: there do not exist sets AP and D such that AP is an infinite
arithmetic progression, D has natural density 0, and the set of odd integers
not of the form 2^k + p equals AP ∪ D. This is the direct assertion of the
solved problem in its true (negative) direction; `D` is not required to be
disjoint from `AP` or to consist of odd numbers, matching the source's
unrestricted "set of density 0".

See also Erdős Problems #9, #10, and #11 (the page's cross-references — the
p + 2^k + 2^l cluster). Tags: number theory, additive basis, primes. Related
OEIS sequence: A006285.

References (bibliographic data for [Er50] and [Ch23] recovered from the
original pipeline's fetch of `erdosproblems.com/latex/16`, preserved in the
session logs; [Er50]'s volume number and the whole [Er95] entry are *not* in
that recovery and are marked accordingly rather than silently fabricated):

- [Er50] Erdős, P., On integers of the form 2^k + p and some related
  problems. Summa Brasil. Math. (1950), 113-123. (Journal, year, pages from
  the /latex/16 recovery; the volume number **2** carried by sibling files
  `deepmind/deepmind/16.lean` and `237.lean` is corpus data, not
  source-recovered.)
- [Er95] Erdős, P., Some of my favourite problems in various branches of
  combinatorics (1995). (Stub: the /latex/16 recovery contains no [Er95]
  entry — it is the problem-source key on the page, cited at p.167. Sibling
  files render it as "Combinatorics '94 (1995), 167-189" and, in one case,
  "Combinatorics '94 (Catania), Congressus Numerantium 107 (1995)"; both
  are consistent with the article beginning at p.167 but neither is
  source-verified here.)
- [Ch23] Chen, Y.-G., A conjecture of Erdős on p + 2^k. arXiv:2312.04120
  (2023). (Author initial, title, and arXiv id from the /latex/16 recovery.)
-/
theorem erdos_problem_16 :
    ¬ ∃ (AP D : Set ℕ),
        IsInfiniteAP AP ∧
        HasNaturalDensityZero D ∧
        oddNotPowerOfTwoPlusPrime = AP ∪ D :=
  sorry

/--
Erdős Problem #16, Erdős's covering-congruence result (SOLVED) [Er50]:

Using covering congruences, Erdős [Er50] proved that the set of odd integers
not of the form 2^k + p **contains** an infinite arithmetic progression
(page remark, recovered verbatim: "Using covering congruences Erdős [Er50]
proved that the set of such odd integers contains an infinite arithmetic
progression."). This is the positive result that made the question
non-trivial: containment (⊆) rather than the equality-of-union asked about
and refuted in `erdos_problem_16`. The classical construction produces an
explicit residue class; only the existential form stated on the page is
formalized here.

Note this also shows the set has positive lower density, so the set itself is
not a candidate for the density-zero part of any decomposition.
-/
theorem erdos_problem_16.variants.erdos_contains_ap :
    ∃ AP : Set ℕ, IsInfiniteAP AP ∧ AP ⊆ oddNotPowerOfTwoPlusPrime :=
  sorry
