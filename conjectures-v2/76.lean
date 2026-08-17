import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #76

*Reference:* [erdosproblems.com/76](https://www.erdosproblems.com/76)

Verbatim statement (recovered from the archived page — two agreeing captures,
accessed 2026-02-22 and 2026-02-23; page edition 23 January 2026):

> Is it true that in any 2-colouring of the edges of K_n there must exist at least
> (1 + o(1)) n²/12 many edge-disjoint monochromatic triangles?

Source citation line: [Er95][Er97d][Va99, 3.54]. Tags: graph theory; ramsey theory.
Related OEIS sequence: A060407.

**Status: PROVED** (page banner, tooltip "This has been solved in the affirmative.";
cross-checked against the teorth/erdosproblems metadata mirror at commit a09c7a2,
2026-08-14: state "proved", last update 2025-08-31; formalized state "no").
The answer is yes, proved by Gruslys and Letzter [GrLe20].

Remarks from the page:
- Conjectured by Erdős, Faudree, and Ordman. The bound would be best possible, as
  witnessed by dividing the vertices of K_n into two equal parts and colouring all
  edges between the parts red and all edges inside the parts blue. (In this
  colouring no triangle is red — every triangle has two vertices in the same part
  and hence a blue edge — so the monochromatic triangles are exactly the triangles
  inside the two parts. Those span ≈ 2·C(n/2, 2) ≈ n²/4 blue edges, each triangle
  uses 3 of them, so an edge-disjoint family has size at most ≈ n²/12; near-optimal
  triangle decompositions of each half show ≈ n²/12 is also achievable.)
- In [Er97d] Erdős also asks for a lower bound for the count of edge-disjoint
  monochromatic triangles in a single colour (the colour chosen to maximise this
  quantity), and speculates that the answer is ≥ c n² for some constant c > 1/24.
  This remains open; formalized below as `erdos_problem_76_single_colour`.

Bibliography (from the archived `erdosproblems.com/latex/76` fetch — two agreeing
log captures of the extraction; the latex page serves full entries only for
[Er97d] and [GrLe20]):

[Er97d] Erdős, P., _Some recent problems and results in graph theory_.
Discrete Math. (1997), 81-85. (Volume 164 per sibling corpus; unverified offline.)

[GrLe20] Gruslys, V. and Letzter, S., _Monochromatic triangle packings in red-blue
graphs_. arXiv:2008.05311 (2020). (Journal data DEFERRED. Note: the archived styled
copy and the prior ai-review instead carry "Minimising the number of triangles in a
two-colouring of the edges of K_n, J. Combin. Theory Ser. B (2020)", which
contradicts the recovered /latex/76 data and appears to be a fabricated entry.)

[Er95] Erdős, Paul, _Some of my favourite problems in number theory, combinatorics,
and geometry_. Resenhas (1995), 165-186. (Key not served by /latex/76; entry
recovered from the agreeing /latex/75 captures of the same key.)

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999. §3.54.
(Corpus-consensus stub; not served by /latex/76; unverified offline.)
-/

/-- A 2-edge-colouring of K_n assigns a Bool to each unordered pair of vertices.
    (Values at diagonal elements ⟦(v, v)⟧ are irrelevant: `triangleEdges` filters
    diagonals out, so they are never queried.) -/
def EdgeTwoColoring (n : ℕ) := Sym2 (Fin n) → Bool

/-- The set of (non-diagonal) edges of a triangle T ⊆ V(K_n):
    all unordered pairs {x, y} with x ≠ y and x, y ∈ T. -/
def triangleEdges {n : ℕ} (T : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  ((T ×ˢ T).image (fun p : Fin n × Fin n => s(p.1, p.2))).filter (fun e => ¬e.IsDiag)

/-- A 3-vertex set T ⊆ V(K_n) is a monochromatic triangle under colouring col if
    all three edges of T receive the same colour. -/
def IsMonochromaticTriangle {n : ℕ} (col : EdgeTwoColoring n) (T : Finset (Fin n)) : Prop :=
  T.card = 3 ∧ ∃ c : Bool, ∀ e ∈ triangleEdges T, col e = c

/-- A family 𝒯 of triangles is edge-disjoint if any two distinct triangles in 𝒯
    share no edge. -/
def IsEdgeDisjointFamily {n : ℕ} (𝒯 : Finset (Finset (Fin n))) : Prop :=
  ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → Disjoint (triangleEdges T₁) (triangleEdges T₂)

/--
**Erdős Problem #76** [Er95][Er97d][Va99, 3.54] (Erdős–Faudree–Ordman conjecture,
PROVED by Gruslys–Letzter [GrLe20]):

In any 2-colouring of the edges of K_n, there exist at least (1 + o(1)) n²/12
edge-disjoint monochromatic triangles.

The source phrases this as a yes/no question ("Is it true that ...?"); it was
answered affirmatively, and this theorem asserts the true direction directly.

Formally: for every ε > 0 there exists N such that for all n ≥ N and any
2-colouring col of the edges of K_n, there is an edge-disjoint family of
monochromatic triangles of size at least (1 - ε) · n² / 12. (This ε–N form is the
standard rendering of the asymptotic lower bound "≥ (1 + o(1)) n²/12", i.e. of
liminf over the worst-case colouring of the count divided by n²/12 being ≥ 1.)
-/
theorem erdos_problem_76 :
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ col : EdgeTwoColoring n,
    ∃ 𝒯 : Finset (Finset (Fin n)),
      (∀ T ∈ 𝒯, IsMonochromaticTriangle col T) ∧
      IsEdgeDisjointFamily 𝒯 ∧
      (1 - ε) * (n : ℝ) ^ 2 / 12 ≤ (𝒯.card : ℝ) :=
  sorry

/--
**Erdős Problem #76, single-colour variant** [Er97d] (OPEN):

In [Er97d] Erdős asks for a lower bound on the number of edge-disjoint
monochromatic triangles *in a single colour* (the colour chosen to maximise this
quantity), and speculates that in any 2-colouring of the edges of K_n this
maximum is ≥ c n² for some constant c > 1/24.

Stated as a direct assertion of Erdős's speculated (affirmative) direction; the
question is open. The bound is asserted for all sufficiently large n, as it must
be (small n admit no triangles at all). The threshold 1/24 is exactly the trivial
barrier: a red and a blue triangle can never share an edge (each edge has a single
colour), so the main theorem's mixed family of size (1 + o(1)) n²/12 already
yields (1 + o(1)) n²/24 edge-disjoint triangles in its majority colour; the
content here is a constant *strictly* above 1/24. Note `T.card = 3` together with
the uniform-colour condition implies `IsMonochromaticTriangle col T`.

**Caveat:** this variant is a new statement written without compile verification
(it uses only constructs already present in this file).
-/
theorem erdos_problem_76_single_colour :
    ∃ c : ℝ, 1 / 24 < c ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ col : EdgeTwoColoring n,
    ∃ (b : Bool) (𝒯 : Finset (Finset (Fin n))),
      (∀ T ∈ 𝒯, T.card = 3 ∧ ∀ e ∈ triangleEdges T, col e = b) ∧
      IsEdgeDisjointFamily 𝒯 ∧
      c * (n : ℝ) ^ 2 ≤ (𝒯.card : ℝ) :=
  sorry
