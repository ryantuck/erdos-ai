import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem 65

*Reference:* [erdosproblems.com/65](https://www.erdosproblems.com/65)
(accessed 2026-02-22, page edition 08 February 2026; page content recovered from two
agreeing archived session-log captures — the raw site page `html/65.html` and the
tidied `tidy/65.html`, both preserved in the original pipeline session's log — plus
three agreeing WebFetch extractions in the formal-conjectures pipeline logs; the live
site is unreachable from the review container).

Statement (verbatim from the site): "Let $G$ be a graph with $n$ vertices and $kn$
edges, and $a_1<a_2<\cdots$ be the lengths of cycles in $G$. Is it true that
\[\sum\frac{1}{a_i}\gg \log k?\] Is the sum $\sum\frac{1}{a_i}$ minimised when $G$ is
a complete bipartite graph?" A problem of Erdős and Hajnal. Cited on the page as
[Er74d][Er75][Er81][Er93, p.342][Er95]. Tags: graph theory | cycles. No prize; no
OEIS entry. 3 comments on the problem; additional thanks: ebarschkis and Jake Mallen.

Status: **OPEN** (tooltip: "This is open, and cannot be resolved with a finite
computation."), with the site's standard open-status disclaimer. The
teorth/erdosproblems metadata mirror (`data/problems.yaml`, commit a09c7a2,
2026-08-14) agrees: status "open" (last update 2025-08-31); formalized: no. The
upstream google-deepmind/formal-conjectures repository (HEAD dd1c2be, 2026-08-16) has
no `ErdosProblems/65.lean`, matching the page's "Formalised statement? No".

Remarks from the page: "Gyárfás, Komlós, and Szemerédi [GKS84] have proved that this
sum is $\gg \log k$, so that only the second question remains. Liu and Montgomery
[LiMo20] have proved the asymptotically sharp lower bound of
$\geq (\tfrac{1}{2}-o(1))\log k$." Further: "Montgomery has written a survey
[https://ems.press/content/serial-article-files/52107] including this problem, in
which he mentions forthcoming work of himself, Milojević, Pokrovskiy, and Sudakov
which proves that, if $k$ is sufficiently large, then $\sum\frac{1}{a_i}$ is
**maximised** when $G$ is a complete bipartite graph." The problem is "#65 in
Extremal Graph Theory" in the graphs problem collection
[https://mathweb.ucsd.edu/~erdosproblems/erdos/newproblems/HarmonicSumOfCycleLengths.html].
See also [57] (reciprocals of *odd* cycle lengths in graphs of infinite chromatic
number, also resolved by [LiMo20]).

NOTE on the second question's expected answer: the forthcoming
Montgomery–Milojević–Pokrovskiy–Sudakov maximisation result reported on the page, if
correct, implies the answer to "is the sum minimised when $G$ is complete bipartite?"
is **no** for all sufficiently large $k$ (a graph cannot be both the maximiser and
the minimiser unless all graphs in the class have equal sums). The site nevertheless
keeps the problem OPEN (the work is unpublished), and the main statement below
follows the raw-pipeline house convention of asserting the question in the direction
asked. It should be expected that the assertion, as universally quantified over all
$k$, is false once that work appears; at small parameters no counterexample is known
(spot-checked here for $K_{2,2}$, $K_{2,3}$, $K_{2,4}$ against all graphs with
matching vertex/edge counts).

References (per-entry provenance; the log-recovered `/latex/65` WebFetch extraction
covers only the two remark keys, and volume/journal data absent from it is NOT
fabricated — all such data is DEFERRED):

- [GKS84] Gyárfás, A., Komlós, J., and Szemerédi, E., _On the distribution of cycle
  lengths in graphs_. J. Graph Theory (1984), 441–462. (From the `/latex/65`
  extraction; volume **8** appears in the styled corpus copy and the prior review but
  not in the extraction — DEFERRED.)
- [LiMo20] Liu, H. and Montgomery, R., _A solution to Erdős and Hajnal's odd cycle
  problem_. arXiv:2010.15802 (2020). (From the `/latex/65` extraction. The prior
  review and reviewer knowledge give the published version as J. Amer. Math. Soc. 36
  (2023), 1191–1234; not page-verified — DEFERRED.)
- [Er74d] Erdős, P. (1974). (Key from the page; no expansion recoverable offline —
  DEFERRED.)
- [Er75] Erdős, P. (1975). (Key from the page; sibling corpus files expand this key
  inconsistently — key-only stub, DEFERRED.)
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to see
  solved_. Combinatorica (1981), 25–42. (Same key expanded in the log-recovered
  `/latex/57` extraction for the sibling problem; volume **1** not in the
  extraction — DEFERRED.)
- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph
  theory_. Quaestiones Mathematicae (1993), 333–350. (Corpus-consensus entry; the
  page's pointer [Er93, p.342] falls inside this page range, corroborating the
  entry — still DEFERRED against the live source.)
- [Er95] Erdős, P. (1995). (Key from the page; sibling corpus files expand this key
  inconsistently — key-only stub, DEFERRED.)
-/

open SimpleGraph Finset

/-- The complete bipartite graph K_{a,b} on Fin (a + b), where vertices {0,…,a-1} form one
    part and {a,…,a+b-1} form the other. -/
def completeBipartiteGraph65 (a b : ℕ) : SimpleGraph (Fin (a + b)) where
  Adj u v := (u.val < a ∧ a ≤ v.val) ∨ (a ≤ u.val ∧ v.val < a)
  symm u v h := by
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inr ⟨hv, hu⟩
    · exact Or.inl ⟨hv, hu⟩
  loopless := ⟨fun v h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩

/--
Erdős Problem #65 (Erdős-Hajnal):
Let G be a graph with n vertices and kn edges, and a₁ < a₂ < ⋯ be the distinct lengths
of cycles in G. Is it true that ∑ 1/aᵢ ≫ log k? Is the sum ∑ 1/aᵢ minimised when G is
a complete bipartite graph?

The first question was proved by Gyárfás, Komlós, and Szemerédi [GKS84].
Liu and Montgomery [LiMo20] proved the asymptotically sharp lower bound ≥ (1/2 - o(1)) log k.

The remaining open question is formalized below, in the direction asked: for any graph
G on n vertices whose edge count equals a * b for some partition a + b = n, the sum of
reciprocals of distinct cycle lengths of G is at least the corresponding sum for the
complete bipartite graph K_{a,b}. (Given n and the edge count e = a·b with a + b = n,
the pair {a, b} is uniquely determined — a and b are the roots of x² − nx + e — so
the comparison graph is unambiguous; edge counts not of this form are outside the
question's comparison class and are vacuously excluded by `hedge`.)

CAVEAT (page-reported counter-evidence): forthcoming work of Montgomery, Milojević,
Pokrovskiy, and Sudakov, reported in Montgomery's survey and quoted on the page,
proves that for sufficiently large k the sum is **maximised** (not minimised) when G
is complete bipartite — see `erdos_problem_65.variants.maximised_for_large_k`. If
that work is correct, this assertion is false for large k, i.e. the answer to the
question as posed is expected to be "no"; the problem is nevertheless still OPEN on
the source page (accessed 2026-02-22, edition 08 February 2026) and in the metadata
mirror (2026-08-14).
-/
theorem erdos_problem_65 {n : ℕ}
    (G : SimpleGraph (Fin n))
    (a b : ℕ) (hab : a + b = n) [DecidableRel G.Adj]
    (hedge : a * b = G.edgeFinset.card)
    (T_G : Finset ℕ)
    (hT_sub : ∀ m ∈ T_G, ∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m)
    (hT_sup : ∀ m : ℕ, (∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m) → m ∈ T_G) :
    ∃ (T_K : Finset ℕ),
      (∀ m ∈ T_K, ∃ v : Fin (a + b),
        ∃ p : (completeBipartiteGraph65 a b).Walk v v, p.IsCycle ∧ p.length = m) ∧
      (∀ m : ℕ, (∃ v : Fin (a + b),
        ∃ p : (completeBipartiteGraph65 a b).Walk v v, p.IsCycle ∧ p.length = m) → m ∈ T_K) ∧
      ∑ m ∈ T_K, (1 / (m : ℝ)) ≤ ∑ m ∈ T_G, (1 / (m : ℝ)) :=
  sorry

/--
Page-confirmed variant (SOLVED — the first question of the problem): "Gyárfás,
Komlós, and Szemerédi [GKS84] have proved that this sum is $\gg \log k$."

Since this file imports no logarithm machinery, "$\gg \log k$" is encoded on the
dyadic scale: there is a universal constant $c > 0$ such that every graph on
$n \ge 1$ vertices with at least $2^j \cdot n$ edges has reciprocal cycle-length sum
at least $c \cdot j$. This is equivalent to the $\gg \log k$ form up to the value of
the constant: a graph with $kn$ edges ($k \ge 2$) satisfies the hypothesis with
$j = \lfloor \log_2 k \rfloor \ge \tfrac{1}{2}\log_2 k$, giving a bound
$\gg \log k$; conversely the dyadic form follows from the $\gg \log k$ form at
$k = 2^j$. The hypothesis $0 < n$ is necessary: for $n = 0$ the edge hypothesis
$2^j \cdot 0 \le 0$ holds for every $j$ while the empty graph's sum is $0$, which
would falsify the unguarded statement (degenerate-input trap, documented rather than
silently absorbed). For $j = 0$ the conclusion is trivially true, matching the
vacuity of "$\gg \log k$" at bounded $k$.

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_65.variants.gyarfas_komlos_szemeredi :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ), 0 < n → ∀ (j : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        2 ^ j * n ≤ G.edgeFinset.card →
        ∀ (T : Finset ℕ),
          (∀ m ∈ T, ∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m) →
          (∀ m : ℕ, (∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m) → m ∈ T) →
          c * (j : ℝ) ≤ ∑ m ∈ T, (1 / (m : ℝ)) :=
  sorry

/--
Page-confirmed variant (FORTHCOMING/UNPUBLISHED — stated on the page as proved in
forthcoming work): "Montgomery … mentions forthcoming work of himself, Milojević,
Pokrovskiy, and Sudakov which proves that, if $k$ is sufficiently large, then
$\sum\frac{1}{a_i}$ is maximised when $G$ is a complete bipartite graph."

Encoded by mirroring the main statement's comparison class with the inequality
reversed and a largeness threshold on the edge density: there is a $k_0$ such that
whenever $a + b = n$, $a \cdot b = |E(G)|$ and $a \cdot b \ge k_0 \cdot n$ (i.e. the
edge count is at least $k_0 n$, the "$k \ge k_0$" of the informal statement), the sum
for $K_{a,b}$ is at least the sum for $G$. This is the result whose truth would give
a negative answer to the problem's second question for large $k$. CAVEAT: the
underlying work is reported as forthcoming and unpublished; this variant records the
page's remark, not established literature.

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_65.variants.maximised_for_large_k :
    ∃ k₀ : ℕ, ∀ {n : ℕ} (G : SimpleGraph (Fin n))
      (a b : ℕ), a + b = n → ∀ [DecidableRel G.Adj],
      a * b = G.edgeFinset.card → k₀ * n ≤ a * b →
      ∀ (T_G : Finset ℕ),
        (∀ m ∈ T_G, ∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m) →
        (∀ m : ℕ, (∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m) → m ∈ T_G) →
        ∃ (T_K : Finset ℕ),
          (∀ m ∈ T_K, ∃ v : Fin (a + b),
            ∃ p : (completeBipartiteGraph65 a b).Walk v v, p.IsCycle ∧ p.length = m) ∧
          (∀ m : ℕ, (∃ v : Fin (a + b),
            ∃ p : (completeBipartiteGraph65 a b).Walk v v, p.IsCycle ∧ p.length = m) → m ∈ T_K) ∧
          ∑ m ∈ T_G, (1 / (m : ℝ)) ≤ ∑ m ∈ T_K, (1 / (m : ℝ)) :=
  sorry
