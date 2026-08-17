import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Erdős Problem 73

*Reference:* [erdosproblems.com/73](https://www.erdosproblems.com/73)
(accessed 2026-02-22; page content recovered from two agreeing archived session-log
captures — the live site is unreachable from the review container).

Statement (verbatim from the site): "Let $k\geq 0$. Let $G$ be a graph such that every
subgraph $H$ contains an independent set of size $\geq (n-k)/2$, where $n$ is the
number of vertices of $H$. Must $G$ be the union of a bipartite graph and $O_k(1)$
many vertices?" [EHS82][Er94b][Er95][Er96][Er97d] — tag: graph theory.

Status: **PROVED** ("This has been solved in the affirmative"), by Reed [Re99]. The
teorth/erdosproblems metadata mirror (`data/problems.yaml`, checked at commit a09c7a2,
2026-08-14) agrees: status "proved", last update 2025-08-31; no prize; OEIS N/A;
formalized: no. The upstream google-deepmind/formal-conjectures repository (HEAD
dd1c2beb, 2026-08-16) has no file for this problem.

Remarks from the page: "Proved by Reed [Re99]. (Thanks also to Reed for pointing out
that the case $k=0$ is trivial, since if $G$ is not bipartite then $G$ contains an odd
cycle.)" See also Erdős Problem [922] (the same independent-set hypothesis with a
bounded-chromatic-number conclusion) and the entry in the graphs problem collection
(mathweb.ucsd.edu/~erdosproblems/erdos/newproblems/AlmostBipartiteGraphs.html).

Note on the hypothesis: the site says "every subgraph $H$"; the formalization
quantifies over vertex subsets, i.e. induced subgraphs. The two readings are
equivalent: a subgraph on vertex set $S$ has at most the edges of the induced
subgraph $G[S]$, hence an independent set of at least the same size, so the binding
instances of the hypothesis are exactly the induced ones.

References (no raw `/latex/73` capture survives in the logs; provenance per entry):

- [Re99] Reed, B., _Mangoes and blueberries_. Combinatorica 19 (1999), 267–296.
  (Title/journal/year/pages from the original pipeline's structured extraction of
  `/latex/73`, which lists this as the page's single reference but omits the volume;
  volume 19 from two corroborating in-repo/log sources and reviewer knowledge —
  DEFERRED against the live `/latex/73`.)
- [EHS82] Erdős, P., Hajnal, A., and Szemerédi, E., _On almost bipartite large
  chromatic graphs_. Annals of Discrete Mathematics 12 (= Theory and Practice of
  Combinatorics) (1982), 117–123. (Sibling-corpus consensus entry; DEFERRED against
  the live source.)
- [Er94b] Erdős, P. (1994). (Key from the page header only; sibling expansions
  conflict — full data DEFERRED, not fabricated.)
- [Er95] Erdős, P. (1995). (Key from the page header only; full data DEFERRED.)
- [Er96] Erdős, P. (1996). (Key from the page header only; full data DEFERRED.)
- [Er97d] Erdős, P. (1997). (Key from the page header only; full data DEFERRED.)
-/

/--
An independent set of a simple graph within a vertex subset S:
a subset I ⊆ S such that no two vertices in I are adjacent in G.
-/
def SimpleGraph.IndepSetIn {V : Type*} (G : SimpleGraph V)
    (I S : Finset V) : Prop :=
  I ⊆ S ∧ ∀ ⦃u⦄, u ∈ I → ∀ ⦃v⦄, v ∈ I → u ≠ v → ¬G.Adj u v

/--
Erdős Problem #73 [EHS82][Er94b][Er95][Er96][Er97d] (PROVED):

> Let k ≥ 0. Let G be a graph such that every subgraph H contains an independent
> set of size ≥ (n − k)/2, where n is the number of vertices of H. Must G be the
> union of a bipartite graph and O_k(1) many vertices?

The answer is **yes**: proved by Reed [Re99]. This direct assertion states the
affirmative resolution: for every k, there exists a constant C (depending only
on k) such that for any finite graph G, if every vertex subset S contains an
independent set of size at least (|S| − k) / 2, then G can be made bipartite by
removing a set T of at most C vertices.

Quantifying over vertex subsets S (i.e. induced subgraphs) is equivalent to the
site's "every subgraph H": a subgraph on vertex set S has at most the edges of
the induced subgraph G[S], hence an independent set of at least the same size,
so the induced subgraphs are the binding instances.
-/
theorem erdos_problem_73 :
    ∀ k : ℕ, ∃ C : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        -- `2 * I.card ≥ S.card - k` encodes |I| ≥ (|S| - k) / 2; the ℕ-truncated
        -- subtraction makes the condition vacuous for |S| ≤ k, matching the
        -- (likewise vacuous) integer inequality 2|I| ≥ |S| - k there.
        (∀ S : Finset (Fin n), ∃ I : Finset (Fin n), G.IndepSetIn I S ∧
          2 * I.card ≥ S.card - k) →
        ∃ T : Finset (Fin n), T.card ≤ C ∧
          ∃ f : Fin n → Bool, ∀ ⦃u v⦄, u ∉ T → v ∉ T → G.Adj u v → f u ≠ f v :=
  sorry

/--
The k = 0 case of Erdős Problem #73, noted as trivial by Reed on the problem
page: if every vertex subset S of a finite graph G contains an independent set
of size ≥ |S| / 2, then G is bipartite outright (no vertex removal needed).

Reason (re-derived): if G is not bipartite it contains an odd cycle, hence a
*shortest* odd cycle, which is induced; the induced subgraph on its 2m + 1
vertices has independence number m < (2m + 1)/2, violating the hypothesis.

[Variant added by the Fable review from the recovered page remark; new Lean
statement, not compile-verified.]
-/
theorem erdos_problem_73.variants.k_eq_zero :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ S : Finset (Fin n), ∃ I : Finset (Fin n), G.IndepSetIn I S ∧
        2 * I.card ≥ S.card) →
      ∃ f : Fin n → Bool, ∀ ⦃u v⦄, G.Adj u v → f u ≠ f v :=
  sorry
