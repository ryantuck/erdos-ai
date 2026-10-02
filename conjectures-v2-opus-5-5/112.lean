-- [AI - Claude Opus 5.5]: Erdős Problem 112 — second-pass formalization
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice

/-!
# Erdős Problem #112: Directed Ramsey Numbers k(n,m)

*Source:* [erdosproblems.com/112](https://www.erdosproblems.com/112) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; captured 2026-02-19 as the
tidied problem box). [ErRa67]

A problem of Erdős and Rado [ErRa67]:
Let k = k(n,m) be minimal such that any directed graph on k vertices must contain
either an independent set of size n or a transitive tournament of size m.
Determine k(n,m).

Remarks recorded on the page:
* Erdős and Rado [ErRa67] showed $k(n,m) \ll_m n^{m-1}$; more precisely,
  $k(n,m) \le \frac{2^{m-1}(n-1)^m + n - 2}{2n-3}$.
* Larson and Mitchell [LaMi97] improved the dependence on $m$, in particular proving
  $k(n,3) \le n^2$.
* Zach Hunter observed $R(n,m) \le k(n,m) \le R(n,m,m)$, which gives $k(n,m) \le 3^{n+2m}$.
* In the graphs problem collection the problem is stated with "directed path" in place of
  "transitive tournament". For that variant, Hunter and Steiner have a simple argument giving
  $k(n,m) = (n-1)(m-1)$.

**Status of the formal statement.** "Determine $k(n,m)$" asks for a formula, and none is
conjectured on the page, so there is no formal target for the open part.
`erdos_problem_112` records the PROVED Erdős–Rado upper bound. The first pass presented that
bound as "the Erdős–Rado Conjecture (Problem #112)".

**Directed graphs are oriented** (`antisymm`: at most one arc between two vertices). The
first pass allowed both arcs `u → v` and `v → u`. Then the complete symmetric digraph has no
independent pair and no transitive tournament on two vertices: `IsTransTournament` demands
`adj (f i) (f j) ↔ i < j`, so a backward arc is forbidden. The defining set of
`dirRamseyNum` was therefore empty for all `n, m ≥ 2`, `sInf ∅ = 0`, and every bound held
vacuously. With orientation, k(n,m) is the classical directed Ramsey number. Allowing
2-cycles but reading "contains a transitive tournament" non-inducedly gives the same value,
since one arc of each 2-cycle can be deleted.

## References

* [ErRa67] Erdős, P. and Rado, R., _Partition relations and transitivity domains of binary
  relations_. J. London Math. Soc. (1967), 624–633.
* [LaMi97] Larson, J. A. and Mitchell, W. J., _On a problem of Erdős and Rado_. Ann. Comb.
  (1997), 245–252.

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/112`. Its extraction
gives surnames only; the initials are given as standard and were not checked against
the bibliography.)
-/

/-- A directed graph on vertex type V: an irreflexive binary relation representing
    directed edges (adj u v means there is a directed edge from u to v), with at most one
    arc between any two vertices (an oriented graph). -/
structure Digraph (V : Type*) where
  adj : V → V → Prop
  loopless : ∀ v, ¬ adj v v
  antisymm : ∀ u v, adj u v → ¬ adj v u

/-- An independent set in a directed graph: a set S of vertices with no directed
    edges between any two of its members (in either direction). -/
def Digraph.IsIndepSet {V : Type*} (G : Digraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ G.adj u v

/-- A transitive tournament on vertex set S in directed graph G: there is a bijection
    f : Fin (S.card) → S (via the subtype) such that G.adj (f i) (f j) holds
    if and only if i < j.  This encodes a total ordering of S compatible with the
    edge relation. -/
def Digraph.IsTransTournament {V : Type*} (G : Digraph V) (S : Finset V) : Prop :=
  ∃ f : Fin S.card → {x : V // x ∈ S}, Function.Bijective f ∧
    ∀ i j : Fin S.card, G.adj (f i : V) (f j : V) ↔ i < j

/-- The directed Ramsey number k(n,m): the minimal k such that every directed graph
    on k vertices contains either an independent set of size n or a transitive
    tournament of size m. -/
noncomputable def dirRamseyNum (n m : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (V : Type) [Fintype V], Fintype.card V = k →
    ∀ G : Digraph V,
      (∃ S : Finset V, S.card = n ∧ G.IsIndepSet S) ∨
      (∃ S : Finset V, S.card = m ∧ G.IsTransTournament S)}

/--
Erdős Problem #112 [ErRa67], the PROVED Erdős–Rado upper bound. Determining k(n,m) exactly is
the open problem, and it has no formal target here:
  k(n,m) ≤ (2^(m-1) * (n-1)^m + n - 2) / (2*n - 3).

The ℕ arithmetic is exact for n, m ≥ 2. The subtractions do not truncate, and for an integer,
the floor of the right-hand side is as strong as the real bound.
-/
theorem erdos_problem_112 :
    ∀ n m : ℕ, 2 ≤ n → 2 ≤ m →
      dirRamseyNum n m ≤ (2 ^ (m - 1) * (n - 1) ^ m + n - 2) / (2 * n - 3) :=
  sorry

/--
Well-definedness (PROVED, by Ramsey's theorem): for n, m ≥ 1 the set defining `dirRamseyNum`
is nonempty, so `dirRamseyNum n m` is a genuine minimum and not the junk value `sInf ∅ = 0`.
-/
theorem erdos_problem_112.variants.well_defined (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ∃ k : ℕ, ∀ (V : Type) [Fintype V], Fintype.card V = k →
      ∀ G : Digraph V,
        (∃ S : Finset V, S.card = n ∧ G.IsIndepSet S) ∨
        (∃ S : Finset V, S.card = m ∧ G.IsTransTournament S) :=
  sorry

/--
A small value (PROVED): k(2,3) = 4. Every tournament on 4 vertices has a transitive triple,
and the cyclic triangle has neither an independent pair nor a transitive triple.
-/
theorem erdos_problem_112.variants.small_case : dirRamseyNum 2 3 = 4 :=
  sorry

/--
Larson and Mitchell [LaMi97] (PROVED): k(n,3) ≤ n².
-/
theorem erdos_problem_112.variants.larson_mitchell (n : ℕ) (hn : 2 ≤ n) :
    dirRamseyNum n 3 ≤ n ^ 2 :=
  sorry

/--
Hunter's observation (PROVED): k(n,m) ≤ R(n,m,m) ≤ 3^(n+2m). For the first inequality, colour
each pair, in a fixed vertex order, by: no arc, forward arc, backward arc.
-/
theorem erdos_problem_112.variants.hunter (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    dirRamseyNum n m ≤ 3 ^ (n + 2 * m) :=
  sorry
