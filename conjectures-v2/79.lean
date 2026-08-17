import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #79

*Reference:* [erdosproblems.com/79](https://www.erdosproblems.com/79)
(accessed 2026-02-22; content recovered from archived session-log captures —
the live site is unreachable from the review container).

Statement (verbatim from the site): "We say $G$ is Ramsey size linear if
$R(G,H)\ll m$ for all graphs $H$ with $m$ edges and no isolated vertices.

Are there infinitely many graphs $G$ which are not Ramsey size linear but such
that all of its subgraphs are?"

Here $R(G,H)$ is the *classical* (vertex) Ramsey number — the minimal $n$ such
that every red/blue colouring of the edges of $K_n$ contains a red copy of $G$
or a blue copy of $H$; "size linear" means linear in the *size* (edge count)
$m$ of $H$. The site's `/latex/79` source (recovered as a WebFetch summary)
confirms this reading: "R(G,H) is O(m)". This differs from the *size Ramsey
number* $\hat{r}(G,H)$; see the NOTE below.

Interpretive note: the page says "all of its subgraphs", but read literally
(with $G$ a subgraph of itself) that condition is unsatisfiable; the intended
and standard reading — used by [EFRS93] and by Wigderson's paper on "minimally
Ramsey size-linear graphs" [Wi24] — is all *proper* subgraphs, as this file
formalizes.

Sources cited on the statement: [EFRS93] [Er95] — tags: graph theory,
ramsey theory.

Status: **PROVED** ("This has been solved in the affirmative."). The
teorth/erdosproblems metadata mirror (`data/problems.yaml`, commit a09c7a2,
2026-08-14) agrees: state "proved", last update 2025-08-31; no prize; no OEIS
reference; not formalized upstream (no `FormalConjectures/ErdosProblems/79.lean`
exists at upstream HEAD dd1c2beb, 2026-08-16).

Remarks (from the page): asked by Erdős, Faudree, Rousseau, and Schelp
[EFRS93]. $K_4$ is the only known example of such a graph. Wigderson [Wi24]
has proved that there are infinitely many such graphs (although his proof is
not explicit, and an explicit example of such a graph apart from $K_4$ is
still unknown).

NOTE (definition provenance): the upstream repository's helper library
(`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/SizeRamsey.lean`)
defines `SimpleGraph.IsRamseySizeLinear` via the *size Ramsey number*
$\hat{r}(G,H)$ (minimum edge count of a host graph), which is a different
quantity from the classical $R(G,H)$ that the problem page and [EFRS93] use.
This file deliberately keeps the classical-Ramsey-number definition, matching
the source; do not "fix" it to the library definition.

References (provenance per entry; the `/latex/79` fetch survives in the
session logs only as WebFetch summaries — two independent captures agree on
both entries below; nothing fabricated):

- [EFRS93] Erdős, P., Faudree, R. J., Rousseau, C. C., and Schelp, R. H.,
  _Ramsey size linear graphs_. Combin. Probab. Comput. (1993), 389-399.
  (From the `/latex/79` WebFetch summaries; volume number not captured.)
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165-186. (Cited on the
  page's statement line; bibliographic data is a shared-key expansion from
  sibling recoveries of the same site-global key — DEFERRED against
  `/latex/79` itself.)
- [Wi24] Wigderson, Y., _Infinitely many minimally Ramsey size-linear
  graphs_. arXiv:2409.05931 (2024). (From the `/latex/79` WebFetch
  summaries; model-summarized, so title/identifier verification against the
  raw source is DEFERRED.)

NOTE (review pipeline): the `variants` theorem below was added by the Fable
review from page-confirmed content, using only constructs already present in
the original file; it is NOT compile-verified. The four `def`s and the main
theorem are unchanged from `conjectures/79.lean`, which the original pipeline
session built successfully with `lake build` (only the expected `sorry`
warning).
-/

/-- `IsSubgraphOf H G` means H is isomorphic to a subgraph of G: there exists an
    injection from V(H) to V(G) that preserves adjacency. -/
def IsSubgraphOf {α β : Type*} (H : SimpleGraph α) (G : SimpleGraph β) : Prop :=
  ∃ f : α → β, Function.Injective f ∧ ∀ u v, H.Adj u v → G.Adj (f u) (f v)

/-- The Ramsey property: every 2-coloring of K_n contains G in one color or H in the
    other. A 2-coloring of K_n is a graph S on Fin n; one color class is S and the
    other is Sᶜ (the complement). -/
def RamseyProp {p q : ℕ} (G : SimpleGraph (Fin p)) (H : SimpleGraph (Fin q))
    (n : ℕ) : Prop :=
  ∀ S : SimpleGraph (Fin n), IsSubgraphOf G S ∨ IsSubgraphOf H Sᶜ

/-- A graph has no isolated vertices if every vertex has at least one neighbor. -/
def NoIsolatedVertices {q : ℕ} (H : SimpleGraph (Fin q)) : Prop :=
  ∀ v : Fin q, ∃ w : Fin q, H.Adj v w

/-- A graph G is Ramsey size linear if there exists C > 0 such that for every graph H
    with no isolated vertices, the Ramsey property R(G,H) holds at some n ≤ C · |E(H)|. -/
def IsRamseySizeLinear {p : ℕ} (G : SimpleGraph (Fin p)) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ (q : ℕ) (H : SimpleGraph (Fin q)) [DecidableRel H.Adj],
    NoIsolatedVertices H →
    ∃ n : ℕ, (n : ℝ) ≤ C * (H.edgeFinset.card : ℝ) ∧ RamseyProp G H n

/-- **Erdős Problem #79**: There exist infinitely many graphs which are not Ramsey
    size linear but all of whose proper subgraphs are. A graph H is a proper subgraph
    of G if H embeds into G (as a subgraph) but G does not embed into H.

    Encoding notes:
    * "Infinitely many graphs" is encoded as "graphs on arbitrarily many
      vertices" (`∀ N, ∃ p ≥ N, …`). This is faithful: there are only finitely
      many graphs on any fixed vertex count, and padding a fixed witness with
      isolated vertices cannot cheat the statement — the unpadded core is a
      proper subgraph of the padded graph and is itself not Ramsey size
      linear, violating the all-proper-subgraphs clause.
    * The page's phrase "all of its subgraphs" is read as "all of its *proper*
      subgraphs" (the literal reading is unsatisfiable since G is a subgraph
      of itself); this is the standard reading of [EFRS93] and [Wi24].
    * The problem is SOLVED in the affirmative by Wigderson [Wi24]
      (non-explicitly; $K_4$ remains the only explicitly known example), so
      the statement is asserted directly, in the true polarity. -/
theorem erdos_conjecture_79 :
    ∀ N : ℕ, ∃ (p : ℕ) (G : SimpleGraph (Fin p)),
      p ≥ N ∧
      ¬ IsRamseySizeLinear G ∧
      ∀ (q : ℕ) (H : SimpleGraph (Fin q)),
        IsSubgraphOf H G →
        ¬ IsSubgraphOf G H →
        IsRamseySizeLinear H := by
  sorry

/-- **Erdős Problem #79, K₄ example** (page-confirmed known result): $K_4$ is
    not Ramsey size linear, but every proper subgraph of $K_4$ is. The page
    remarks "$K_4$ is the only known example of such a graph" (only *explicitly*
    known, after [Wi24]). The non-linearity of $K_4$ follows from the
    superquadratic lower bounds on $R(K_4, K_n)$ noted in [EFRS93], and the
    linearity of its proper subgraphs (all of which embed in $K_4$ minus an
    edge) is proved in [EFRS93]. Here $K_4$ is `⊤ : SimpleGraph (Fin 4)`. -/
theorem erdos_conjecture_79.variants.k4 :
    ¬ IsRamseySizeLinear (⊤ : SimpleGraph (Fin 4)) ∧
    ∀ (q : ℕ) (H : SimpleGraph (Fin q)),
      IsSubgraphOf H (⊤ : SimpleGraph (Fin 4)) →
      ¬ IsSubgraphOf (⊤ : SimpleGraph (Fin 4)) H →
      IsRamseySizeLinear H := by
  sorry

end
