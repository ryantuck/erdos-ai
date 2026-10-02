-- [AI - Claude Opus 5.5]: Erdős Problem 110 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Set.Card

open SimpleGraph Cardinal

/-!
# Erdős Problem #110

*Source:* [erdosproblems.com/110](https://www.erdosproblems.com/110). The capture of
2026-02-19 (page last edited 01 October 2025) shows the banner **NOT PROVABLE** ("Open in
general, but there exist models of set theory where the result is false."). Its own remarks
already record a ZFC counterexample [La20]. The `teorth/erdosproblems` mirror now records
**disproved** (last update 2026-04-05). [EHS82] [Er87] [Er90] [Er95d] [Er97f]

Is there some $F(n)$ such that every graph with chromatic number $\aleph_1$ has, for all large
$n$, a subgraph with chromatic number $n$ on at most $F(n)$ vertices?

Remarks recorded on the page:
* Conjectured by Erdős, Hajnal and Szemerédi [EHS82]. This fails if the graph has chromatic
  number $\aleph_0$.
* A theorem of de Bruijn and Erdős [dBEr51] implies that if $G$ has infinite chromatic
  number, then $G$ has a finite subgraph of chromatic number $n$ for every $n \ge 1$.
* In [Er95d] Erdős suggests this is true, although such an $F$ must grow faster than the
  $k$-fold iterated exponential function for any $k$.
* Komjáth and Shelah [KoSh05] proved that it is consistent that the answer is no.
  Lambie-Hanson [La20] constructed a counterexample in ZFC.

**Polarity.** The answer is no, in ZFC [La20]. So `erdos_problem_110` asserts the negation
of the first-pass statement, which asserted the conjecture.

Tags: graph theory, chromatic number, cycles.

## References

* [EHS82] Erdős, P., Hajnal, A. and Szemerédi, E., _On almost bipartite large chromatic
  graphs_. Theory and Practice of Combinatorics (1982), 117–123.
* [Er87] Erdős, P., _Some problems on finite and infinite graphs_. Logic and combinatorics
  (Arcata, Calif., 1985) (1987), 223–228.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős
  (1990), 467–478.
* [Er95d] Erdős, P., _On some problems in combinatorial set theory_. Publ. Inst. Math.
  (Beograd) (N.S.) (1995), 61–65.
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1–10.
* [dBEr51] de Bruijn, N. G. and Erdős, P., _A colour problem for infinite graphs and a
  problem in the theory of relations_. Indag. Math. (1951), 369–373.
* [KoSh05] Komjáth, P. and Shelah, S., _Finite subgraphs of uncountably chromatic graphs_.
  J. Graph Theory (2005), 28–38.
* [La20] Lambie-Hanson, C., _On the growth rate of chromatic numbers of finite subgraphs_.
  Adv. Math. (2020), 107176.

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/110` for [EHS82],
[Er95d], [KoSh05], [La20] and [dBEr51]. Sibling extractions for [Er87], [Er90] and [Er97f].)
-/

/--
A graph G (on vertex type V) has chromatic number ℵ₁ if:
(1) G cannot be properly colored by any countable set of colors
    (i.e., the chromatic number exceeds ℵ₀), and
(2) G can be properly colored by a set of cardinality ℵ₁.
-/
def HasChromaticNumberAleph1 {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ (α : Type*) [Countable α], IsEmpty (G.Coloring α)) ∧
  (∃ α : Type*, #α = aleph 1 ∧ Nonempty (G.Coloring α))

/--
Erdős-Hajnal-Szemerédi Conjecture (Problem #110), DISPROVED:
Is there some function F : ℕ → ℕ such that every graph G with chromatic number ℵ₁
has, for all sufficiently large n, a subgraph with chromatic number n on at most
F(n) vertices? **No.** The statement under `¬` is the first-pass statement, byte for byte.

Conjectured by Erdős, Hajnal, and Szemerédi [EHS82].
The analogous statement fails for graphs of chromatic number ℵ₀.
Komjáth and Shelah [KoSh05] proved it is consistent with ZFC that the answer is no.
Lambie-Hanson [La20] constructed a ZFC counterexample, so the conjecture is FALSE.
-/
theorem erdos_problem_110 :
    ¬ (∃ F : ℕ → ℕ,
      ∀ (V : Type*) (G : SimpleGraph V),
        HasChromaticNumberAleph1 G →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∃ H : G.Subgraph,
            H.verts.Finite ∧
            H.verts.ncard ≤ F n ∧
            H.coe.chromaticNumber = ↑n) :=
  sorry

/--
de Bruijn and Erdős [dBEr51] (PROVED): a graph of infinite chromatic number has, for every
$n \ge 1$, a finite subgraph of chromatic number exactly $n$.
-/
theorem erdos_problem_110.variants.de_bruijn_erdos {V : Type*} (G : SimpleGraph V)
    (hG : G.chromaticNumber = ⊤) (n : ℕ) (hn : 1 ≤ n) :
    ∃ H : G.Subgraph, H.verts.Finite ∧ H.coe.chromaticNumber = ↑n :=
  sorry

/--
A graph has chromatic number ℵ₀: it is not finitely colorable, but it is colorable with
countably many colors.
-/
def HasChromaticNumberAleph0 {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ k : ℕ, IsEmpty (G.Coloring (Fin k))) ∧ Nonempty (G.Coloring ℕ)

/--
The ℵ₀ analogue fails (PROVED). For every `F` there is a graph of chromatic number ℵ₀ with
no such small subgraphs. Take a disjoint union of finite graphs `G_m` with `χ(G_m) = m` in
which every subgraph with at most `max_{j ≤ m} F j` vertices is 3-colorable (Erdős's
probabilistic construction).
-/
theorem erdos_problem_110.variants.aleph0_fails :
    ¬ (∃ F : ℕ → ℕ,
      ∀ (V : Type) (G : SimpleGraph V),
        HasChromaticNumberAleph0 G →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∃ H : G.Subgraph,
            H.verts.Finite ∧
            H.verts.ncard ≤ F n ∧
            H.coe.chromaticNumber = ↑n) :=
  sorry
