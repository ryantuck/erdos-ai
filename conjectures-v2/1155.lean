import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

noncomputable section

open SimpleGraph Filter Classical

namespace Erdos1155

/-!
# Erdős Problem #1155

Verbatim source statement (erdosproblems.com/1155): "Construct a random
graph on $n$ vertices in the following way: begin with the complete graph
$K_n$. At each stage, choose uniformly a random triangle in the graph and
delete all the edges of this triangle. Repeat until the graph is
triangle-free.

Describe the typical parameters and structure of such a graph. In
particular, if $f(n)$ is the number of edges remaining, then is it true
that \[\mathbb{E}f(n)\asymp n^{3/2}\] and that $f(n) \ll n^{3/2}$ almost
surely?"

Status: OPEN per erdosproblems.com/1155 (tooltip: "This is open, and cannot
be resolved with a finite computation."), plus the owner's standard
disclaimer. Page last edited 25 January 2026, accessed 2026-02-23. Source
line: #1155: [Bo98,p.231][Va99,3.61].

A problem of Bollobás and Erdős, described in [Va99] as "motivated by the
task of generating a random triangle-free graph". In [Bo98] it says they
asked this at the "Quo Vadis, Graph Theory?" conference in Fairbanks,
Alaska, in 1990, "while admiring the playful bears".

Remarks from the source page:

* Grable [Gr97] proved that, for every ε > 0, ℙ(f(n) > n^{7/4+ε}) → 0.
  (Formalized below as `erdos_problem_1155.variants.grable`.)
* Bohman, Frieze, and Lubetzky [BFL15] proved that f(n) = n^{3/2+o(1)}
  almost surely — in other words, for every ε > 0,
  ℙ(n^{3/2-ε} < f(n) < n^{3/2+ε}) → 1. (Formalized below as
  `erdos_problem_1155.variants.bfl15`.) Note this does *not* resolve the
  problem: neither the two-sided expectation bound nor the a.s. bound
  f(n) ≤ C·n^{3/2} follows from n^{3/2+o(1)}.

Encoding notes:

* The source poses a (two-part) yes/no question and the problem is OPEN;
  this raw corpus has no `answer()` elaborator (Mathlib-only imports), and
  its uniform convention for open yes/no questions is a direct assertion of
  the asked ("yes") direction with a `sorry` proof, as here — one theorem
  per part. In styled question form each would be `answer(sorry) ↔ …` (the
  archived styled copy of this problem uses exactly that shape over these
  same propositions).
* The random triangle removal process is a stochastic process with a random
  number of steps; `triangleRemovalExpectedEdges` (𝔼[f(n)]) and
  `triangleRemovalEdgeProb` (ℙ(f(n) satisfies P)) are declared `opaque` and
  are **specification-only**: no axiom ties them to an actual probability
  space, and both are understood to refer to the *same* underlying process.
  A genuine construction is possible in principle via Mathlib's `PMF` monad
  (well-founded recursion on the edge count: while a triangle exists,
  `bind` a uniform choice over the triangle set and recurse on the graph
  minus that triangle's three edges), but writing it compile-unverified is
  out of scope here; it is recorded as deferred future work. "Almost
  surely" is encoded as "with probability tending to 1" (convergence in
  probability / w.h.p.), the standard meaning here — confirmed by the
  source page's own gloss of [BFL15]'s result.

Tags (per the page): graph theory.
Formalised statement (per the page, as of access): No.
The page records 1 forum comment, no OEIS entries, and "Additional thanks
to: Jake Mallen".

References (honest stubs; all bibliographic data below is from the
log-recovered `/latex/1155` extraction, which carries **no volume numbers**
— none are fabricated here):

[Bo98] Bollobás, B., _To prove and conjecture: Paul Erdős and his
  mathematics_. Amer. Math. Monthly (1998), 209–237. (The cited p. 231
  falls in this range. The archived styled copy glossed [Bo98] as "_Modern
  Graph Theory_, Graduate Texts in Mathematics 184, Springer (1998)" — an
  attribution contradicted by the recovered `/latex/1155` bibliography and
  not reproduced here.)

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
  the conference "Paul Erdős and his mathematics", Budapest, July 1999
  (1999), §3.61. (Corpus-canonical identity of this site-global key,
  confirmed for this problem by the log-recovered `/latex/1155` extraction.
  The archived styled copy glossed [Va99] as "Vu, V. H. (1999), 3.61" — a
  hallucinated attribution, not reproduced here.)

[Gr97] Grable, D. A., _On random greedy triangle packing_. Electron. J.
  Combin. (1997), Research Paper 11, 19 pp.

[BFL15] Bohman, T., Frieze, A., and Lubetzky, E., _Random triangle
  removal_. Adv. Math. (2015), 379–438.
-/

/-- A simple graph contains a triangle if there exist three distinct mutually
    adjacent vertices. (The three distinctness conjuncts are redundant —
    adjacency in a `SimpleGraph` is irreflexive, so `G.Adj a b → a ≠ b` —
    but harmless. Equivalent to `¬G.CliqueFree 3` in Mathlib's vocabulary;
    kept local to preserve this file's import surface.) -/
def ContainsTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- A simple graph is triangle-free if it contains no triangle. (Equivalent
    to Mathlib's `G.CliqueFree 3`.) These two definitions document the
    termination condition of the (unformalized) removal process; they are
    not referenced by the theorems below, which speak only about the opaque
    summary quantities of the process. -/
def TriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬ContainsTriangle G

/-- The triangle removal process on Kₙ: starting from the complete graph on n
    vertices, repeatedly choose a uniformly random triangle and remove all three
    of its edges, until the graph is triangle-free.

    `triangleRemovalExpectedEdges n` is 𝔼[f(n)], the expected number of edges
    remaining when the process terminates.

    Specification-only `opaque` constant: no axiom ties it to an actual
    probability space. It refers to the same underlying random process as
    `triangleRemovalEdgeProb`. (The input file declared this as
    `noncomputable def … := sorry`, a data-level `sorry` depending on
    `sorryAx`; `opaque` is the honest form of the same modeling compromise.
    A genuine `PMF`-based construction is deferred — see the module
    docstring.) -/
opaque triangleRemovalExpectedEdges (n : ℕ) : ℝ

/-- The probability that the number of edges remaining after the triangle
    removal process on Kₙ satisfies a given predicate P.

    Specification-only `opaque` constant, referring to the same underlying
    random process as `triangleRemovalExpectedEdges`; see that declaration's
    docstring and the module docstring. -/
opaque triangleRemovalEdgeProb (n : ℕ) (P : ℕ → Prop) : ℝ

/--
Erdős Problem #1155, Part 1 [Bo98,p.231][Va99,3.61] (OPEN):

𝔼[f(n)] ≍ n^{3/2}, i.e., there exist constants c₁, c₂ > 0 such that for all
sufficiently large n, c₁ · n^{3/2} ≤ 𝔼[f(n)] ≤ c₂ · n^{3/2}.

This asserts the "yes" direction of the open question, per this corpus's
convention for open yes/no questions.
-/
theorem erdos_problem_1155_expectation :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        c₁ * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ triangleRemovalExpectedEdges n ∧
        triangleRemovalExpectedEdges n ≤ c₂ * (n : ℝ) ^ ((3 : ℝ) / 2) :=
  sorry

/--
Erdős Problem #1155, Part 2 [Bo98,p.231][Va99,3.61] (OPEN):

f(n) ≪ n^{3/2} almost surely, i.e., there exists C > 0 such that with
probability tending to 1, f(n) ≤ C · n^{3/2}.

This asserts the "yes" direction of the open question, per this corpus's
convention for open yes/no questions. "Almost surely" is the standard
w.h.p. reading, matching the source page's own gloss of [BFL15]. Note
[BFL15]'s f(n) = n^{3/2+o(1)} does not imply this bound (e.g. n^{3/2}·log n
is n^{3/2+o(1)}), so the problem remains open.
-/
theorem erdos_problem_1155_almost_sure :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun n : ℕ =>
        triangleRemovalEdgeProb n (fun k => (k : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2)))
        atTop (nhds 1) :=
  sorry

/--
Grable [Gr97] proved that, for every ε > 0, ℙ(f(n) > n^{7/4+ε}) → 0.
(Solved partial result toward Part 2, recorded from the source page's
remarks. NOTE: new statement, not compile-verified.)
-/
theorem erdos_problem_1155.variants.grable :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ =>
        triangleRemovalEdgeProb n (fun k => (k : ℝ) > (n : ℝ) ^ ((7 : ℝ) / 4 + ε)))
        atTop (nhds 0) :=
  sorry

/--
Bohman, Frieze, and Lubetzky [BFL15] proved that f(n) = n^{3/2+o(1)} almost
surely — in the source page's own gloss, for every ε > 0,
ℙ(n^{3/2-ε} < f(n) < n^{3/2+ε}) → 1. (Solved result; strict inequalities as
on the page. This gives an a.s. two-sided bound up to n^{o(1)} factors but
resolves neither Part 1 nor Part 2. NOTE: new statement, not
compile-verified.)
-/
theorem erdos_problem_1155.variants.bfl15 :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ =>
        triangleRemovalEdgeProb n (fun k =>
          (n : ℝ) ^ ((3 : ℝ) / 2 - ε) < (k : ℝ) ∧
          (k : ℝ) < (n : ℝ) ^ ((3 : ℝ) / 2 + ε)))
        atTop (nhds 1) :=
  sorry

end Erdos1155

end
