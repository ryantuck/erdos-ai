import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Aleph

open SimpleGraph Cardinal

/-- A graph G has chromatic number ℵ₁ if it cannot be properly colored by any
    countable set of colors, but can be colored by a set of cardinality ℵ₁.

    The two clauses together pin χ(G) = ℵ₁ exactly: the first says χ(G) > ℵ₀
    (no countable color type suffices, so χ(G) ≥ ℵ₁), the second says
    χ(G) ≤ ℵ₁ (a color type of size exactly ℵ₁ suffices; a smaller-χ graph
    would still be colorable by such a type, so this clause alone only bounds
    χ from above — the conjunction is what forces equality).

    Universe note: `Type*` gives the two color quantifiers independent
    auto-bound universe parameters. This is harmless: colorability by a
    countable type and colorability by a type of size ℵ₁ are both
    universe-invariant (compose with an injection into ℕ, resp. transport
    along an equivalence from `Cardinal.lift_mk_eq`, since `lift (aleph 1)
    = aleph 1`), so every universe instantiation of this predicate is
    equivalent to the intended property χ(G) = ℵ₁. -/
def HasChromaticNumberAleph1 {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ (α : Type*) [Countable α], IsEmpty (G.Coloring α)) ∧
  (∃ α : Type*, #α = aleph 1 ∧ Nonempty (G.Coloring α))

/-- G contains H as a subgraph via an injective adjacency-preserving map.
    (Non-induced containment: adjacency is only required in the forward
    direction; isolated vertices of H must also embed. This is the same
    notion as Mathlib's `SimpleGraph.IsContained` / `H ⊑ G`, via
    `SimpleGraph.Copy`.) -/
def containsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Problem #62 (weak version):

"If $G_1,G_2$ are two graphs with chromatic number $\aleph_1$ then must there
exist a graph $G$ whose chromatic number is $4$ (or even $\aleph_0$) which is a
subgraph of both $G_1$ and $G_2$?" (verbatim from the archived problem page,
last edited 23 January 2026; status banner OPEN — "This is open, and cannot be
resolved with a finite computation". Status cross-checked against the
teorth/erdosproblems metadata mirror: open, last update 2025-08-31.)

This weak version asks for a common subgraph H with chromatic number 4,
encoded as `¬ H.Colorable 3`, i.e. χ(H) ≥ 4. Encoding note: the page asks for
χ exactly 4, but under the existential over H the two readings are equivalent
(in ZFC): any H with χ(H) ≥ 4 has, by de Bruijn–Erdős, a finite subgraph F
that is not 3-colorable, and deleting edges of F one at a time (each deletion
lowers χ by at most 1) yields a subgraph with χ exactly 4, which is still a
common subgraph by transitivity of `containsSubgraph`.

The problem is a yes/no question, OPEN; the theorem asserts the questioned
(affirmative) direction, as posed. Every graph with chromatic number ℵ₁
contains all sufficiently large odd cycles (chromatic number 3), proved by
Erdős, Hajnal, and Shelah [EHS74] — see erdosproblems.com problem #594.
Erdős wrote [Er87] that 'probably' every graph with chromatic number ℵ₁
contains as subgraphs all graphs with chromatic number 4 with sufficiently
large girth. (Neither of those two statements is formalized here: both need
cycle/girth machinery not present in this file.)
-/
theorem erdos_problem_62_weak :
    ∀ (V₁ : Type*) (V₂ : Type*) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    HasChromaticNumberAleph1 G₁ →
    HasChromaticNumberAleph1 G₂ →
    ∃ (U : Type*) (H : SimpleGraph U),
      ¬ H.Colorable 3 ∧
      containsSubgraph G₁ H ∧
      containsSubgraph G₂ H :=
  sorry

/--
Erdős Problem #62 (strong version) [Er87]:

If G₁, G₂ are two graphs with chromatic number ℵ₁, must there exist a graph H
with infinite chromatic number (χ ≥ ℵ₀) which is a subgraph of both G₁ and G₂?
This is the "(or even $\aleph_0$)" reading of the page's question — the
stronger form of the conjecture. `H.chromaticNumber = ⊤` (in ℕ∞) says H is
not colorable by any finite number of colors, i.e. χ(H) ≥ ℵ₀; as with the
weak version this is equivalent, under the existential over H, to asking for
χ(H) = ℵ₀ exactly (a graph with χ ≥ ℵ₀ contains a countable subgraph — a
union of finite subgraphs of unbounded chromatic number — with χ = ℵ₀).

Status: OPEN (archived page, last edited 23 January 2026; teorth/erdosproblems
mirror: open, 2025-08-31; "Formalised statement? No" on the page, and no
`ErdosProblems/62.lean` at upstream formal-conjectures HEAD dd1c2be).
The page's citation line is [Er87][Er90][Er95d][Va99,7.89]; tags: graph
theory; no OEIS references; no prize.

References ([EHS74] and [Er87] recovered from the page's /latex/62 source;
bold volume numbers follow the archived styled copy of this formalization and
are not re-verified offline; [Er90], [Er95d], [Va99] have no /latex/62
entries — their expansions follow the corpus-wide shared keys):

[Er87] Erdős, P., _Some problems on finite and infinite graphs_. Logic and
combinatorics (Arcata, Calif., 1985), Contemp. Math. **65** (1987), 223-228.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul
Erdős (1990), 467-478.

[Er95d] Erdős, P., _Problems and results in discrete mathematics_.
Discrete Math. (1995).

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
(Problem cited at §7.89.)

[EHS74] Erdős, P., Hajnal, A., and Shelah, S., _On some general properties of
chromatic numbers_. Topics in topology (Proc. Colloq., Keszthely, 1972),
Colloq. Math. Soc. Janos Bolyai **8** (1974), 243-255.

Source: https://www.erdosproblems.com/62
-/
theorem erdos_problem_62 :
    ∀ (V₁ : Type*) (V₂ : Type*) (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂),
    HasChromaticNumberAleph1 G₁ →
    HasChromaticNumberAleph1 G₂ →
    ∃ (U : Type*) (H : SimpleGraph U),
      H.chromaticNumber = ⊤ ∧
      containsSubgraph G₁ H ∧
      containsSubgraph G₂ H :=
  sorry

/--
Erdős Problem #62, finite-collection variant (strong form), page-confirmed:
"Erdős also asked [Er87] about finding a common subgraph $H$ (with chromatic
number either $4$ or $\aleph_0$) in any finite collection of graphs with
chromatic number $\aleph_1$."

Here the ℵ₀ (strong) form: any finite family G i (i : Fin n) of graphs of
chromatic number ℵ₁ admits a common subgraph of infinite chromatic number.
Degenerate cases are harmless and true: for n = 0 the containment condition
is vacuous and any graph of infinite chromatic number (e.g. a complete graph
on an infinite type) witnesses the existential; for n = 1 the graph G 0
itself works (its own chromatic number is infinite since it is not even
countably colorable). The mathematical content starts at n = 2, where this
subsumes `erdos_problem_62`.

NOTE: this variant was added by the Fable review (page-confirmed enrichment)
and is NOT compile-verified.
-/
theorem erdos_problem_62.variants.finite_collection :
    ∀ (n : ℕ) (V : Fin n → Type*) (G : ∀ i, SimpleGraph (V i)),
    (∀ i, HasChromaticNumberAleph1 (G i)) →
    ∃ (U : Type*) (H : SimpleGraph U),
      H.chromaticNumber = ⊤ ∧
      ∀ i, containsSubgraph (G i) H :=
  sorry

/--
Erdős Problem #62, finite-collection variant (weak form), page-confirmed:
any finite family of graphs of chromatic number ℵ₁ admits a common subgraph
of chromatic number at least 4 (`¬ Colorable 3`; equivalent to "exactly 4"
under the existential, as documented at `erdos_problem_62_weak`). This is the
"chromatic number $4$" half of the page's finite-collection question.

NOTE: this variant was added by the Fable review (page-confirmed enrichment)
and is NOT compile-verified.
-/
theorem erdos_problem_62.variants.finite_collection_weak :
    ∀ (n : ℕ) (V : Fin n → Type*) (G : ∀ i, SimpleGraph (V i)),
    (∀ i, HasChromaticNumberAleph1 (G i)) →
    ∃ (U : Type*) (H : SimpleGraph U),
      ¬ H.Colorable 3 ∧
      ∀ i, containsSubgraph (G i) H :=
  sorry
