import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

/-- An injective graph homomorphism from H to G; witnesses that G contains a
    subgraph isomorphic to H. (Non-induced containment: adjacency is only
    required in the forward direction. Isolated vertices of H must also embed,
    matching Mathlib's `SimpleGraph.IsContained`.) -/
def containsSubgraph59 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph.

    The candidate set is bounded above by n(n-1)/2 (since `Fintype.card V = n`),
    so `sSup` on ℕ is well-behaved. Degenerate input: if H has no edges and
    `Fintype.card U ≤ n`, every graph on n vertices contains H, the set is empty,
    and `sSup ∅ = 0` — the conventional junk value for an ex(n;H) that is
    undefined; no statement in this file depends on that case.

    (Fix note, semantically neutral: a `DecidableEq V` witness was added to the
    existential chain so that `F.edgeFinset` can find its `Fintype F.edgeSet`
    instance, which in Mathlib requires `Fintype (Sym2 V)` and hence
    `DecidableEq V`. Since the binder sits under a propositional `∃`,
    `Classical.decEq V` always provides a witness, so the set of achievable `m`
    values — and hence the supremum — is unchanged. Not compile-verified.) -/
noncomputable def turanNumber59 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (de : DecidableEq V)
    (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := de; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph59 F H ∧ F.edgeFinset.card = m}

/-- The number of labeled simple graphs on n vertices that do not contain H as a subgraph. -/
noncomputable def countGFreeGraphs59 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  Nat.card {F : SimpleGraph (Fin n) // ¬containsSubgraph59 F H}

/-- The cycle C₆ on vertex set {0, …, 5}: i is adjacent to i ± 1 (mod 6). Built with
    `SimpleGraph.fromRel`, whose symmetrization and irreflexivity guard
    (`Adj a b ↔ a ≠ b ∧ (r a b ∨ r b a)`) make this exactly the 6-cycle: the edges
    are {0,1}, {1,2}, {2,3}, {3,4}, {4,5}, {5,0} (Fin 6 addition wraps, and
    i = j + 1 ∧ j = i + 1 would force 2 ≡ 0 (mod 6), so no double edges collapse). -/
def cycle6Graph59 : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel (fun i j => j = i + 1)

/-- The cycle C₄ on vertex set {0, …, 3}: i is adjacent to i ± 1 (mod 4). Edges
    {0,1}, {1,2}, {2,3}, {3,0}; as for `cycle6Graph59`, i = j + 1 ∧ j = i + 1 would
    force 2 ≡ 0 (mod 4), so this is exactly the 4-cycle. -/
def cycle4Graph59 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun i j => j = i + 1)

/--
Erdős Problem #59 [Er90, Er93 p.335, Er97c, Va99 3.56]:

"Is it true that the number of graphs on $n$ vertices which do not contain $G$ is
$\leq 2^{(1+o(1))\mathrm{ex}(n;G)}$?" (verbatim from the archived problem page,
last edited 23 January 2026; status banner DISPROVED — "This has been solved in
the negative". Status cross-checked against the teorth/erdosproblems metadata
mirror: disproved, last update 2025-08-31.)

That is (the refuted reading): for every graph G and every ε > 0, for all
sufficiently large n, #{G-free labeled graphs on [n]} ≤ 2^{(1+ε)·ex(n;G)}.

This was DISPROVED: the answer is no for G = C₆ (the 6-cycle).
Erdős, Frankl, and Rödl [EFR86] proved the answer is yes when G is not bipartite.
Morris and Saxton [MoSa16] showed there are at least 2^{(1+c)·ex(n;C₆)} such graphs
for infinitely many n, for some constant c > 0. Morris and Saxton conjecture that
the weaker bound 2^{O(ex(n;G))} still holds for all G, and [Va99] also asks the
specific case G = C₄; both are open (see the variants below).

The theorem asserts the NEGATION of the quoted universal statement — the true
direction of this solved problem. The original first-pass file asserted the
refuted universal statement itself; that polarity was fixed by the Fable review
([defect]-class) and the fix is NOT compile-verified.

References (page/section data from the archived page and its /latex/59 source;
volume/number data absent there and left unverified offline — journal titles and
page ranges for [Er90], [Er93], [Er97c] follow the corpus-wide expansions of
these shared keys):

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul
Erdős (1990), 467-478.

[Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph
theory_. Quaestiones Mathematicae (1993), 333-350. (Problem cited at p.335.)

[Er97c] Erdős, P., _Some recent problems and results in graph theory_. Discrete
Math. (1997), 81-85.

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
(Problem cited at §3.56, where the C₄ case is also asked.)

[EFR86] Erdős, P., Frankl, P., and Rödl, V., _The asymptotic number of graphs
not containing a fixed subgraph and a problem for hypergraphs having no
exponent_. Graphs Combin. (1986), 113-121.

[MoSa16] Morris, R. and Saxton, D., _The number of C_{2ℓ}-free graphs_.
Adv. Math. (2016), 534-580.

Tags: graph theory | turan number. No OEIS references. No prize.
Source: https://www.erdosproblems.com/59
-/
theorem erdos_problem_59 :
    ¬ (∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
      ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (countGFreeGraphs59 H n : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * (turanNumber59 H n : ℝ))) :=
  sorry

/--
The positive half of Erdős Problem #59, proved by Erdős, Frankl, and Rödl
[EFR86] (page-confirmed): if G is NOT bipartite, then the number of labeled
G-free graphs on n vertices is at most 2^{(1+o(1))·ex(n;G)}.

"Not bipartite" is encoded inline as the nonexistence of a proper 2-coloring
`f : U → Bool` (adjacent vertices get different colors). Degenerate inputs
behave correctly: an empty or edgeless graph is 2-colorable, hence excluded by
the hypothesis, as EFR86 (chromatic number ≥ 3) requires.

NOTE: this variant was added by the Fable review (page-confirmed enrichment)
and is NOT compile-verified.
-/
theorem erdos_problem_59.variants.efr_nonbipartite :
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
    (¬ ∃ f : U → Bool, ∀ u v : U, H.Adj u v → f u ≠ f v) →
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (countGFreeGraphs59 H n : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * (turanNumber59 H n : ℝ)) :=
  sorry

/--
The disproof of Erdős Problem #59, by Morris and Saxton [MoSa16]
(page-confirmed): there is a constant c > 0 such that, for infinitely many n,
there are at least 2^{(1+c)·ex(n;C₆)} labeled C₆-free graphs on n vertices.
This witnesses the negation asserted in `erdos_problem_59` (for ε < c the
claimed eventual bound fails along this sequence, since ex(n;C₆) > 0 for
n ≥ 6).

NOTE: this variant was added by the Fable review (page-confirmed enrichment)
and is NOT compile-verified.
-/
theorem erdos_problem_59.variants.morris_saxton_c6 :
    ∃ c : ℝ, 0 < c ∧
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        (2 : ℝ) ^ ((1 + c) * (turanNumber59 cycle6Graph59 n : ℝ))
          ≤ (countGFreeGraphs59 cycle6Graph59 n : ℝ) :=
  sorry

/--
Morris–Saxton weaker conjecture (page-confirmed, OPEN): for every graph G there
is a constant C > 0 (depending on G) such that the number of labeled G-free
graphs on n vertices is at most 2^{C·ex(n;G)} for all sufficiently large n —
i.e. the bound 2^{O(ex(n;G))} survives even though the 2^{(1+o(1))·ex(n;G)}
bound was disproved for C₆.

The constant C is existentially quantified AFTER the graph binders and before
n, so it may depend on G but must be uniform in n, matching the intended
O(ex(n;G)) reading.

NOTE: this variant was added by the Fable review (page-confirmed enrichment)
and is NOT compile-verified.
-/
theorem erdos_problem_59.variants.weak_bound :
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (countGFreeGraphs59 H n : ℝ) ≤ (2 : ℝ) ^ (C * (turanNumber59 H n : ℝ)) :=
  sorry

/--
The C₄ case of Erdős Problem #59, asked in [Va99, 3.56] (page-confirmed, OPEN):
is the number of labeled C₄-free graphs on n vertices at most
2^{(1+o(1))·ex(n;C₄)}? The general conjecture fails for C₆, but this specific
case remains open; it is stated here in the asked (affirmative) direction, for
the concrete 4-cycle `cycle4Graph59` (not for arbitrary graphs on 4 vertices).

NOTE: this variant was added by the Fable review (page-confirmed enrichment)
and is NOT compile-verified.
-/
theorem erdos_problem_59.variants.c4_case :
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (countGFreeGraphs59 cycle4Graph59 n : ℝ)
        ≤ (2 : ℝ) ^ ((1 + ε) * (turanNumber59 cycle4Graph59 n : ℝ)) :=
  sorry
