import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup

open scoped Classical
open Filter

/-!
# Erdős Problem #40

For what functions $g(N)\to \infty$ is it true that
$$\lvert A\cap \{1,\ldots,N\}\rvert \gg \frac{N^{1/2}}{g(N)}$$
implies $\limsup 1_A\ast 1_A(n)=\infty$?

**Status: OPEN** — banner tooltip: "This is open, and cannot be resolved
with a finite computation." **$500** prize. (erdosproblems.com/40, accessed
2026-03-05 — the capture is the tidied problem box, which carries no
page-edition date; the teorth/erdosproblems metadata mirror, commit
a09c7a21 of 2026-08-14, agrees: state "open", last update 2025-08-31,
prize $500, no OEIS refs, tags "number theory", "additive basis".)

Remark from the source page:

- This is a stronger form of the Erdős–Turán conjecture [Problem #28]
  (since establishing this for any function $g(N)\to\infty$ would imply a
  positive solution to #28). Formalized below as
  `erdos_problem_40.variants.implies_erdos_28`.

Formalised statement? **Yes** — upstream google-deepmind/formal-conjectures
`FormalConjectures/ErdosProblems/40.lean` (present at HEAD dd1c2beb)
encodes the classification question itself with the `answer()` device:
`Erdos40ForSet answer(sorry)`, where `Erdos40For g` is the per-function
implication (with the growth hypothesis as
`(√N / g N) =O[atTop] (counting)`) and `Erdos40ForSet G` says every
`g ∈ G` with `g → ∞` satisfies it. This raw pipeline has no `answer()`
elaborator, so the classification request is recorded here in prose and
the theorem below states the weakest nontrivial substrate (see its
docstring). Upstream's only unconditional theorem about this problem is
likewise an implication (`erdos_40.variants.implies_erdos_28`), not an
assertion that any particular `g` works.

## References

Problem sources on the page: [Er95] [Er97c]. No `/latex/40` fetch exists
in the session logs, so no bibliography could be recovered from the site
itself; the entry below is an honest stub with its provenance flagged:
DEFERRED.

- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas 1 (1995), 165-186. (Stub:
  corpus-majority entry; unverified offline.)
- [Er97c] — key only; no reliable corpus expansion (the corpus's entries
  for this key conflict): DEFERRED.

Additional thanks to: Sarosh Adenwalla.

Tags: number theory, additive basis
https://www.erdosproblems.com/40
-/

/--
The counting function for A up to N: |A ∩ {1, …, N}|.

(`Finset.Icc 1 N` is exactly {1, …, N}; membership in `A : Set ℕ` is
decided classically via `open scoped Classical`, which is why this is
`noncomputable`. An element `0 ∈ A` is never counted, matching the
source's $A\cap\{1,\ldots,N\}$.)
-/
noncomputable def countingFn40 (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

/--
The representation function for a set A ⊆ ℕ, counting the number of ways
to write n as a + b with a, b ∈ A (i.e. 1_A ∗ 1_A(n)).

(This counts **ordered** representations: `a` ranges over
`Finset.range (n + 1)` = {0, …, n} and the partner is `n - a`, so each
pair (a, b) with a + b = n and a ≠ b is counted twice — exactly the
convolution $1_A\ast 1_A(n) = \sum_{a+b=n} 1_A(a)1_A(b)$, and the same
convention as `repFunction` in `conjectures/28.lean` and `sumRep`
upstream. The ℕ subtraction `n - a` is exact since `a ≤ n` on the range;
each value `repFunction40 A n ≤ n + 1` is finite, so unboundedness of
`n ↦ repFunction40 A n` is equivalent to $\limsup 1_A\ast 1_A(n)=\infty$
— finitely many finite values never carry the limsup.)
-/
noncomputable def repFunction40 (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ (n - a) ∈ A)).card

/--
The problem's per-function property: `erdos40For g` says that every
A ⊆ ℕ with |A ∩ {1, …, N}| ≫ N^{1/2} / g(N) (Vinogradov ≫: some C > 0
and the bound for all sufficiently large N) has unbounded representation
function, i.e. limsup 1_A ∗ 1_A(n) = ∞.

Erdős Problem #40 asks: **for what** functions g(N) → ∞ does
`erdos40For g` hold? (Mirrors upstream formal-conjectures' `Erdos40For`,
whose hypothesis `(√N / g N) =O[atTop] (counting)` is the same eventual
bound up to the eventual sign of `g`.)
-/
def erdos40For (g : ℕ → ℝ) : Prop :=
  ∀ A : Set ℕ,
    (∃ C : ℝ, 0 < C ∧
      ∀ᶠ N in atTop,
        (countingFn40 A N : ℝ) ≥ C * (N : ℝ) ^ ((1 : ℝ) / 2) / g N) →
    ∀ M : ℕ, ∃ n : ℕ, repFunction40 A n ≥ M

/--
Erdős Problem #40 [Er95, Er97c] — OPEN, $500 prize (erdosproblems.com/40,
accessed 2026-03-05; status cross-checked open against the
teorth/erdosproblems metadata mirror):

For what functions g(N) → ∞ is it true that
  |A ∩ {1, …, N}| ≫ N^{1/2} / g(N)
implies limsup 1_A ∗ 1_A(n) = ∞?

This is a stronger form of the Erdős–Turán conjecture (#28), since
establishing this for any function g(N) → ∞ would imply a positive
solution to #28 (see `erdos_problem_40.variants.implies_erdos_28`).

**Encoding note.** The question is a classification request; without the
upstream `answer()` device (upstream: `Erdos40ForSet answer(sorry)`) the
theorem below states the weakest nontrivial substrate: **some** g → ∞
satisfies the implication. This is precisely the reading under which the
page's remark gives #28, it is open (it implies open #28), and it is the
direction Erdős implicitly conjectures. The **universal** form "every
g → ∞ works" — which an earlier pass of this file asserted — is provably
FALSE: for g(N) = N the growth hypothesis degenerates (N^{1/2}/g(N) =
N^{-1/2} ≤ 1), so already A = {1} satisfies it with C = 1 while
1_A ∗ 1_A ≤ 1 is bounded; see
`erdos_problem_40.variants.not_all_functions`. The classification's
content lives at slowly growing g, and the answer set is genuinely
constrained: by Ruzsa's infinite Sidon set with counting function
N^{√2−1+o(1)} (see problem #39's page), `erdos40For g` also fails for
every g with g(N) ≥ N^{1/2−(√2−1)+ε}, so only slowly growing g can work.
-/
theorem erdos_problem_40 :
    ∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ erdos40For g :=
  sorry

/--
Erdős Problem #40, sanity complement (PROVABLE — this documents why the
"for all g → ∞" strengthening is not the right reading): not every
g(N) → ∞ satisfies the implication. Witness g(N) = N and A = {1}: then
countingFn40 A N = 1 for N ≥ 1 while N^{1/2}/g(N) = N^{-1/2} ≤ 1, so the
growth hypothesis holds with C = 1; but n = 2 is the only n with
repFunction40 A n ≠ 0 (and repFunction40 A 2 = 1), so M = 2 has no
witness. More structurally, any infinite Sidon set defeats every fast
growing g.
-/
theorem erdos_problem_40.variants.not_all_functions :
    ∃ g : ℕ → ℝ, Tendsto g atTop atTop ∧ ¬ erdos40For g :=
  sorry

/--
Erdős Problem #40 implies Erdős–Turán (page remark, PROVABLE): if
`erdos40For g` holds for **any** g(N) → ∞, then Problem #28 follows —
if A + A contains all but finitely many naturals (encoded: 1_A ∗ 1_A(n)
≥ 1 for all n beyond some n₀), then 1_A ∗ 1_A is unbounded.

(Proof sketch, not formalized: representable n ≤ N are sums a + (n − a)
with both parts in A ∩ [0, N], so (countingFn40 A N + 1)² ≥ N − n₀ and
counting ≥ (1/2)·N^{1/2} eventually; since g(N) → ∞ makes g eventually
≥ 1, the hypothesis of `erdos40For g` holds with C = 1/2, and its
conclusion is #28's. Upstream proves exactly this implication as
`erdos_40.variants.implies_erdos_28`, instantiating at g = √N.)
-/
theorem erdos_problem_40.variants.implies_erdos_28
    (g : ℕ → ℝ) (hg : Tendsto g atTop atTop) (h : erdos40For g)
    (A : Set ℕ) (hA : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 1 ≤ repFunction40 A n) :
    ∀ M : ℕ, ∃ n : ℕ, repFunction40 A n ≥ M :=
  sorry
