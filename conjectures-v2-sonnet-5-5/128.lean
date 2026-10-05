-- [AI - Claude Sonnet 5.5]: Erdős Problem 128 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Erdős Problem #128: A Local Density Condition for Triangles

*Source:* [erdosproblems.com/128](https://www.erdosproblems.com/128) (status **FALSIFIABLE**,
prize $250: "Open, but could be disproved with a finite counterexample."; captured 2026-02-20 and
2026-03-05 as the tidied problem box). [Er93, p.344] [ErRo93] [Er97b]

Let $G$ be a graph with $n$ vertices such that every induced subgraph on $\geq \lfloor n/2\rfloor$
vertices has more than $n^2/50$ edges. Must $G$ contain a triangle?

Remarks recorded on the page:
* A problem of Erdős and Rousseau. The constant $50$ would be best possible as witnessed by a
  blow-up of $C_5$ or the Petersen graph.
* Erdős, Faudree, Rousseau, and Schelp [EFRS94] proved that this is true with $50$ replaced by
  $16$. More generally, they prove that, for any $0<\alpha<1$, if every set of $\geq \alpha n$
  vertices contains $>\alpha^3n^2/2$ edges then $G$ contains a triangle.
* Krivelevich [Kr95] has proved this with $n/2$ replaced by $3n/5$ (and $50$ replaced by $25$).
* Keevash and Sudakov [KeSu06] have proved this under the additional assumption that either $G$
  has at most $n^2/12$ edges, or that $G$ has at least $n^2/5$ edges. Norin and Yepremyan
  [NoYe15] proved that this is true if $G$ has at least $(1/5-c)n^2$ edges, for some constant
  $c>0$.
* Razborov [Ra22] proved this is true if $\frac{1}{50}$ is replaced by $\frac{27}{1024}$.
* See also the entry in the graphs problem collection.

Tags: graph theory. Page last edited 31 October 2025; 4 comments (not captured).

**Status.** OPEN. The mirror (`teorth/erdosproblems`) has `falsifiable` (2025-10-31) with a $250
prize, and upstream `erdos_128` is `answer(sorry)` with category `research open`. The statement
asserts the asked ("yes") direction, that every such $G$ contains a triangle, which is the corpus
convention while a problem is open. A finite counterexample would refute it.

**Encoding.**
* `inducedEdgeCount G S` counts the ordered adjacent pairs in `S ×ˢ S` and halves the count.
  Each edge of $G[S]$ gives two ordered pairs, so the division is exact.
* `n / 2 ≤ S.card` is $\lfloor n/2\rfloor\le|S|$, as on the page. Upstream writes
  `2 * |S| + 1 ≥ n`, which is the same condition for every $n$.
* `50 * e > n ^ 2` is exactly $e>n^2/50$ over the naturals, with no rounding.
* The triangle is an explicit triple of distinct, pairwise adjacent vertices, equivalent to
  `¬ G.CliqueFree 3`.
* The hypothesis is vacuous for $n\le3$, since a set of $\lfloor n/2\rfloor\le1$ vertices has no
  edges.
* The strict inequality matters. The Petersen graph is triangle-free, and every induced subgraph
  on at least $5$ of its $10$ vertices has at least $n^2/50=2$ edges, with equality attained.
  `variants.strict_needed` states this and is proved by `decide`. The $C_5$ blow-up with parts of
  an even size $t$ behaves the same way: the least number of edges over sets of $\lfloor n/2\rfloor$
  vertices is exactly $n^2/50$ (checked by minimizing over part sizes for $t\le40$, not
  formalized).

## References

* [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
  Quaestiones Math. (1993), 333–350. The page cites p. 344.
* [ErRo93] Erdős, P. and Rousseau, C. C., _The size Ramsey number of a complete bipartite graph_.
  Discrete Math. (1993). Pages not recovered.
* [Er97b] Erdős, P., _Some old and new problems in various branches of combinatorics_. Discrete
  Math. (1997), 227–231.
* [EFRS94] Erdős, Faudree, Rousseau and Schelp (1994), in the page's remarks. **DEFERRED:** no
  bibliographic details were recovered.
* [Kr95] Krivelevich (1995), in the page's remarks. **DEFERRED:** no bibliographic details were
  recovered.
* [KeSu06] Keevash and Sudakov (2006), in the page's remarks. **DEFERRED:** no bibliographic
  details were recovered.
* [NoYe15] Norin and Yepremyan (2015), in the page's remarks. **DEFERRED:** no bibliographic
  details were recovered.
* [Ra22] Razborov (2022), in the page's remarks. **DEFERRED:** no bibliographic details were
  recovered.

(Provenance: no `/latex/128` fetch exists in the session logs, and upstream `128.lean` has no
bibliography. [Er93] and [Er97b] are from the bibliographies of `/latex` pages of other problems
in the logs. [ErRo93] is from the reference block of an earlier formalization of problem 560 in
the logs, which gives journal and year only. The five DEFERRED keys appear only in the remarks.)
-/

/--
The number of edges in the induced subgraph of G on vertex set S.
-/
noncomputable def inducedEdgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ((S ×ˢ S).filter fun p : V × V => p.1 ≠ p.2 ∧ G.Adj p.1 p.2).card / 2

/--
Erdős Problem #128 (Erdős–Rousseau) [Er93, ErRo93, Er97b] — OPEN (page status FALSIFIABLE,
prize $250):
Let G be a graph with n vertices such that every induced subgraph on at least
⌊n/2⌋ vertices has more than n²/50 edges. Then G contains a triangle.

The statement asserts the asked direction ("must G contain a triangle?"). A finite
counterexample would refute it.
-/
theorem erdos_problem_128 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n)
    (h : ∀ S : Finset V, n / 2 ≤ S.card →
      50 * inducedEdgeCount G S > n ^ 2) :
    ∃ (a b c : V), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c :=
  sorry

/--
Erdős–Faudree–Rousseau–Schelp [EFRS94] (PROVED, as the page words it): for any $0<\alpha<1$, if
every set of at least $\alpha n$ vertices contains more than $\alpha^3n^2/2$ edges then G contains
a triangle. The size condition is `⌊αn⌋₊ ≤ |S|`, the floor convention of the main statement. It
constrains at least as many sets as "≥ αn", so this is the weaker of the two readings.
Taking $\alpha=1/2$ gives the page's "50 replaced by 16".
-/
theorem erdos_problem_128.variants.efrs94 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1)
    (h : ∀ S : Finset V, ⌊α * n⌋₊ ≤ S.card →
      α ^ 3 * (n : ℝ) ^ 2 / 2 < (inducedEdgeCount G S : ℝ)) :
    ∃ (a b c : V), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c :=
  sorry

/--
Krivelevich [Kr95] (PROVED): the conclusion holds with n/2 replaced by 3n/5 and 50 replaced by 25.
The size condition is `⌊3n/5⌋ ≤ |S|`, the floor convention of the main statement, which is the
weaker of the two readings.
-/
theorem erdos_problem_128.variants.krivelevich95 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n)
    (h : ∀ S : Finset V, 3 * n / 5 ≤ S.card →
      25 * inducedEdgeCount G S > n ^ 2) :
    ∃ (a b c : V), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c :=
  sorry

/--
Keevash–Sudakov [KeSu06] (PROVED): the conclusion holds under the additional assumption that
either G has at most n²/12 edges, or G has at least n²/5 edges.
-/
theorem erdos_problem_128.variants.keevash_sudakov06 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n)
    (h : ∀ S : Finset V, n / 2 ≤ S.card →
      50 * inducedEdgeCount G S > n ^ 2)
    (hE : 12 * inducedEdgeCount G Finset.univ ≤ n ^ 2 ∨
      n ^ 2 ≤ 5 * inducedEdgeCount G Finset.univ) :
    ∃ (a b c : V), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c :=
  sorry

/--
Norin–Yepremyan [NoYe15] (PROVED): there is a constant ε > 0 (the page's c) such that the
conclusion holds whenever G has at least (1/5 - ε)n² edges. The graphs live in `Type`, since a
constant cannot be chosen before a universe.
-/
theorem erdos_problem_128.variants.norin_yepremyan15 :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (n : ℕ), Fintype.card V = n →
      (∀ S : Finset V, n / 2 ≤ S.card → 50 * inducedEdgeCount G S > n ^ 2) →
      (1 / 5 - ε) * (n : ℝ) ^ 2 ≤ (inducedEdgeCount G Finset.univ : ℝ) →
      ∃ (a b c : V), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c :=
  sorry

/--
Razborov [Ra22] (PROVED): the conclusion holds with 1/50 replaced by 27/1024, that is, with the
hypothesis "more than 27n²/1024 edges" on every induced subgraph on at least ⌊n/2⌋ vertices.
-/
theorem erdos_problem_128.variants.razborov22 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : Fintype.card V = n)
    (h : ∀ S : Finset V, n / 2 ≤ S.card →
      1024 * inducedEdgeCount G S > 27 * n ^ 2) :
    ∃ (a b c : V), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c :=
  sorry

/-- The edges of the Petersen graph on `Fin 10`: an outer 5-cycle on 0..4, the spokes `i ~ i + 5`,
and an inner pentagram on 5..9. -/
def petersenEdges : List (ℕ × ℕ) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

/-- The Petersen graph on `Fin 10`. -/
def petersen : SimpleGraph (Fin 10) where
  Adj a b := (a.val, b.val) ∈ petersenEdges ∨ (b.val, a.val) ∈ petersenEdges
  symm := fun _ _ h => h.symm
  loopless := ⟨fun a h => by revert a; decide⟩

instance : DecidableRel petersen.Adj := fun a b => by unfold petersen; infer_instance

/--
The strict inequality in the main statement cannot be weakened to `≥` (PROVED, by `decide`). The
Petersen graph is triangle-free, every induced subgraph on at least ⌊10/2⌋ = 5 vertices has at
least 10²/50 = 2 edges, and some 5-set has exactly 2 (the page's "best possible" witness).
-/
theorem erdos_problem_128.variants.strict_needed :
    ∃ (G : SimpleGraph (Fin 10)) (_ : DecidableRel G.Adj),
      (∀ S : Finset (Fin 10), 10 / 2 ≤ S.card → 10 ^ 2 ≤ 50 * inducedEdgeCount G S) ∧
      (∃ S : Finset (Fin 10), 10 / 2 ≤ S.card ∧ 50 * inducedEdgeCount G S = 10 ^ 2) ∧
      ¬ ∃ (a b c : Fin 10), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c :=
  ⟨petersen, inferInstance, by decide +kernel, by decide +kernel, by decide⟩
