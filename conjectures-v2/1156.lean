import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section

open SimpleGraph Filter Classical

namespace Erdos1156

/-!
# Erdős Problem #1156

Verbatim source statement (erdosproblems.com/1156): "Let $G$ be a random
graph on $n$ vertices, in which every edge is included independently with
probability $1/2$.

Is there some constant $C$ such that that [sic] chromatic number $\chi(G)$
is, almost surely, concentrated on at most $C$ values?

Is it true that, if $\omega(n)\to \infty$ sufficiently slowly, then for
every function $f(n)$ \[\mathbb{P}(\lvert\chi(G)-f(n)\rvert<\omega(n))<1/2\]
if $n$ is sufficiently large?"

Status: OPEN per erdosproblems.com/1156 (tooltip: "This is open, and cannot
be resolved with a finite computation."), plus the owner's standard
disclaimer. Page last edited 27 January 2026, accessed 2026-02-23. Source
line: #1156: [AlSp92][Va99,3.6].

Remarks from the source page:

* Bollobás [Bo88] proved that χ(G) ~ n/(2·log₂ n) with high probability.
  (Not formalized below: a faithful statement needs log₂, which is outside
  this file's import surface; recorded as deferred enrichment.)
* Shamir and Spencer [ShSp87] proved that, for any function ω(n) such that
  ω(n)/√n → ∞, there is a function f(n) such that
  ℙ(|χ(G) − f(n)| < ω(n)) → 1 as n → ∞. (Formalized below as
  `erdos_problem_1156.variants.shamir_spencer`.) This is proved with
  ω(n)·(log n)/√n → ∞ — i.e. concentration in windows of width o(√n) — in
  Exercise 3 of Section 7.9 of Alon and Spencer [AlSp16]; a proof is also
  given by Scott [Sc17]. (Not formalized: needs log.) NOTE: the input
  file's docstring attributed "concentration within o(√n)" to Shamir and
  Spencer; per the source page that refinement is [AlSp16]/[Sc17], while
  [ShSp87] gives concentration in windows of any width ω(n) with
  ω(n)/√n → ∞.
* Heckel [He21] proved that if f and ω are such that
  ℙ(|χ(G) − f(n)| < ω(n)) → 1 as n → ∞ then, for any c < 1/4, there are
  infinitely many n such that ω(n) > n^c. This was improved to any c < 1/2
  by Heckel and Riordan [HeRi23]. (The improved form is formalized below as
  `erdos_problem_1156.variants.heckel_riordan`; it subsumes [He21].)

Encoding notes:

* The source poses two yes/no questions and the problem is OPEN; this raw
  corpus has no `answer()` elaborator (Mathlib-only imports), and its
  uniform convention for open yes/no questions is a direct assertion of the
  asked ("yes") direction with a `sorry` proof, as here — one theorem per
  part. In styled question form each would be `answer(sorry) ↔ …`.
* Part 2's "if ω(n) → ∞ sufficiently slowly, then P" idiom is encoded as
  "∃ ω with ω(n) → ∞ such that P". The two are equivalent because the event
  |χ(G) − f(n)| < ω(n) shrinks as ω decreases: any ω' → ∞ growing more
  slowly than a witnessing ω is eventually below it, so the property passes
  down to every sufficiently slow ω'.
* `chromaticNumberProb` is a concrete uniform-counting definition (see its
  docstring); since p = 1/2, the Erdős–Rényi model G(n, 1/2) is exactly the
  uniform distribution over all 2^(n choose 2) labelled simple graphs on n
  vertices. The input file had `noncomputable def … := sorry` here (a
  data-level `sorry` riding on `sorryAx`); the concrete definition follows
  the prior review's recommendation, adapted to Mathlib's ℕ∞-valued
  `chromaticNumber`. NOT compile-verified (this container has no compiler);
  the `import Mathlib.SetTheory.Cardinal.Finite` line (for `Nat.card`) is
  new relative to the input, following siblings 1042/1106 which compiled
  with it.
* Both parts are consistent with each other and with [HeRi23]: a set of at
  most C concentration values need not lie in one short interval, so Part 1
  is not refuted by the interval-anticoncentration results.

Tags (per the page): graph theory | chromatic number.
Formalised statement (per the page, as of access): No.
The page records 1 forum comment, no OEIS entries, and "Additional thanks
to: Wouter van Doorn".

References (honest stubs; [Bo88], [ShSp87], [AlSp16], [Sc17], [He21],
[HeRi23] are from the log-recovered `/latex/1156` extraction, which carries
**no volume numbers** — none are fabricated here; that extraction has no
entry for [AlSp92] or [Va99]):

[AlSp92] Alon, N. and Spencer, J. H., _The Probabilistic Method_. Wiley
  (1992). (First edition of [AlSp16]; identification from reviewer
  knowledge, corroborated by the [AlSp16] entry below — the `/latex/1156`
  extraction itself carries no AlSp92 entry.)

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
  the conference "Paul Erdős and his mathematics", Budapest, July 1999
  (1999), §3.6. (Corpus-canonical identity of this site-global key,
  confirmed by sibling `/latex` extractions, e.g. problem 1155's. The input
  file glossed [Va99,3.6] as "Vu"; the archived styled copy glossed it as
  "Vu, V. H. (1999), 3.64" — hallucinated attributions, with the styled
  copy also contradicting the page's section number 3.6; neither is
  reproduced here.)

[Bo88] Bollobás, B., _The chromatic number of random graphs_. Combinatorica
  (1988), 49–55.

[ShSp87] Shamir, E. and Spencer, J., _Sharp concentration of the chromatic
  number on random graphs $G_{n,p}$_. Combinatorica (1987), 121–129.

[AlSp16] Alon, N. and Spencer, J. H., _The probabilistic method_. Wiley
  (2016), xiv+375.

[Sc17] Scott, A., _On the concentration of the chromatic number of random
  graphs_. arXiv:0806.0178 (2017).

[He21] Heckel, A., _Non-concentration of the chromatic number of a random
  graph_. J. Amer. Math. Soc. (2021), 245–260.

[HeRi23] Heckel, A. and Riordan, O., _How does the chromatic number of a
  random graph vary?_ J. Lond. Math. Soc. (2) (2023), 1769–1815.
-/

/-- The probability that the chromatic number of a uniformly random graph
    G(n,1/2) on n vertices satisfies predicate P. Here G(n,1/2) is the
    Erdős–Rényi model where each edge is included independently with
    probability 1/2, equivalently (since p = 1/2) the uniform distribution
    over all 2^(n choose 2) simple graphs on n labelled vertices — which is
    how it is defined here: the fraction of graphs on `Fin n` whose
    chromatic number satisfies P.

    Implementation notes. Mathlib's `SimpleGraph.chromaticNumber` is
    ℕ∞-valued; for a graph on `Fin n` it is finite (at most n), so `.toNat`
    is faithful. `Nat.card` needs no `Fintype`/decidability instances, and
    `SimpleGraph (Fin n)` is a finite type, so the denominator is the true
    count 2^(n choose 2) ≥ 1 and the division is never by zero (including
    at n = 0, where the single empty graph has chromatic number 0).

    (The input file declared this as `noncomputable def … := sorry`, a
    data-level `sorry` depending on the unsound `sorryAx`; replaced by this
    concrete definition, as the prior review recommended. NOTE: fix not
    compile-verified.) -/
noncomputable def chromaticNumberProb (n : ℕ) (P : ℕ → Prop) : ℝ :=
  (Nat.card {G : SimpleGraph (Fin n) // P G.chromaticNumber.toNat} : ℝ) /
    (Nat.card (SimpleGraph (Fin n)) : ℝ)

/--
Erdős Problem #1156, Part 1 [AlSp92][Va99,3.6] (OPEN):

There exists a constant C such that χ(G(n,1/2)) is almost surely concentrated
on at most C values. That is, for every ε > 0 and all sufficiently large n,
there is a set S of at most C natural numbers with P(χ(G) ∈ S) ≥ 1 - ε.

This asserts the "yes" direction of the open question, per this corpus's
convention for open yes/no questions. C is a single constant, uniform in ε
and n; the value set S may depend on both.
-/
theorem erdos_problem_1156_concentration :
    ∃ C : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        ∃ S : Finset ℕ, S.card ≤ C ∧
          chromaticNumberProb n (· ∈ S) ≥ 1 - ε :=
  sorry

/--
Erdős Problem #1156, Part 2 [AlSp92][Va99,3.6] (OPEN):

There exists a function ω : ℕ → ℝ with ω(n) → ∞ such that for every function
f : ℕ → ℝ, for all sufficiently large n,
  P(|χ(G) - f(n)| < ω(n)) < 1/2.
That is, the chromatic number cannot be concentrated in any interval of width
2ω(n) with probability ≥ 1/2.

This asserts the "yes" direction of the open question, per this corpus's
convention for open yes/no questions. The source's "if ω(n) → ∞ sufficiently
slowly" idiom is equivalent to this ∃ω form — see the module docstring.
-/
theorem erdos_problem_1156_anticoncentration :
    ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧
      ∀ f : ℕ → ℝ, ∀ᶠ n in atTop,
        chromaticNumberProb n (fun k => |(k : ℝ) - f n| < ω n) < 1 / 2 :=
  sorry

/--
Shamir and Spencer [ShSp87] proved that, for any function ω(n) such that
ω(n)/√n → ∞, there is a function f(n) such that P(|χ(G) − f(n)| < ω(n)) → 1
as n → ∞.

Encoding note: this file's import surface has no `Real.sqrt`/`rpow`, so the
hypothesis ω(n)/√n → ∞ is encoded as "ω(n) is eventually positive and
ω(n)²/n → ∞". For eventually-positive ω the two are equivalent, since there
ω(n)/√n = √(ω(n)²/n); the positivity conjunct is genuinely needed — e.g.
ω(n) = −n satisfies ω(n)²/n → ∞ but ω(n)/√n → −∞.

(Solved partial result, recorded from the source page's remarks. NOTE: new
statement, not compile-verified.)
-/
theorem erdos_problem_1156.variants.shamir_spencer :
    ∀ ω : ℕ → ℝ,
      (∀ᶠ n in atTop, 0 < ω n) →
      Tendsto (fun n : ℕ => (ω n) ^ 2 / (n : ℝ)) atTop atTop →
      ∃ f : ℕ → ℝ,
        Tendsto (fun n : ℕ =>
          chromaticNumberProb n (fun k => |(k : ℝ) - f n| < ω n))
          atTop (nhds 1) :=
  sorry

/--
Heckel [He21] proved that if f and ω are such that P(|χ(G) − f(n)| < ω(n)) → 1
as n → ∞ then, for any c < 1/4, there are infinitely many n such that
ω(n) > n^c. This was improved to any c < 1/2 by Heckel and Riordan [HeRi23];
the improved form is formalized here (it subsumes [He21]).

Encoding note: this file's import surface has no `rpow`, so real exponents
c < 1/2 are encoded through rational ones: for all p, q : ℕ with 0 < q and
2p < q (i.e. p/q < 1/2), there are infinitely many n with n^p < ω(n)^q.
Since the rationals are dense in [0, 1/2) and c ↦ n^c is monotone (n ≥ 1),
this captures the full real-exponent statement; and under the theorem's
hypothesis ω(n) is eventually positive (otherwise the events are eventually
empty and the probability could not tend to 1), so on the relevant n,
n^p < ω(n)^q is equivalent to ω(n) > n^(p/q). "There are infinitely many n"
is `∃ᶠ n in atTop`.

(Solved result, recorded from the source page's remarks. NOTE: new
statement, not compile-verified.)
-/
theorem erdos_problem_1156.variants.heckel_riordan :
    ∀ f ω : ℕ → ℝ,
      Tendsto (fun n : ℕ =>
        chromaticNumberProb n (fun k => |(k : ℝ) - f n| < ω n))
        atTop (nhds 1) →
      ∀ p q : ℕ, 0 < q → 2 * p < q →
        ∃ᶠ n in atTop, (n : ℝ) ^ p < (ω n) ^ q :=
  sorry

end Erdos1156

end
