import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem 57

*Reference:* [erdosproblems.com/57](https://www.erdosproblems.com/57)
(accessed 2026-02-22, page edition 23 January 2026; page content recovered from two
agreeing archived session-log captures (raw `html/57.html` and tidied `tidy/57.html`,
both in the original pipeline session's log) — the live site is unreachable from the
review container).

Statement (verbatim from the site): "If $G$ is a graph with infinite chromatic number
and $a_1<a_2<\cdots$ are lengths of the odd cycles of $G$ then
$\sum \frac{1}{a_i}=\infty$." Cited on the page as
[ErHa66][Er69b][Er74d][Er81][Er90][Er93, p.342][Er94b][Er95][Er95d][Er96][Er97b]
[Va99, 3.58]. Tags: graph theory | chromatic number | cycles. No prize; no OEIS entry.

Status: **PROVED** (tooltip: "This has been solved in the affirmative."). Conjectured
by Erdős and Hajnal [ErHa66] and solved by Liu and Montgomery [LiMo20]. The
teorth/erdosproblems metadata mirror (`data/problems.yaml`, commit a09c7a2,
2026-08-14) agrees: status "proved" (last update 2025-08-31); formalized: no. The
upstream google-deepmind/formal-conjectures repository (HEAD dd1c2be, 2026-08-16) has
no `ErdosProblems/57.lean`, matching the page's "Formalised statement? No".

Remarks from the page: "In [Er81] Erdős asks whether the $a_i$ must in fact have
positive upper density, and in [Er95d] and [Er96] he speculates whether the upper
density (or even upper logarithmic density) must be $\geq 1/2$. The lower density of
the set can be $0$ since there are graphs of arbitrarily large chromatic number and
girth. See also [65]." (Problem 65 concerns reciprocals of *all* cycle lengths in
finite graphs with $kn$ edges; [LiMo20] also resolved its sharp bound.) 0 comments on
the problem.

References (per-entry provenance; the log-recovered `/latex/57` extraction covers only
five of the page's thirteen keys and explicitly notes that volume numbers and DOIs are
absent — nothing below is fabricated, and all volume data is DEFERRED):

- [ErHa66] Erdős, P. and Hajnal, A., _On chromatic number of graphs and set-systems_.
  Acta Math. Acad. Sci. Hungar. (1966), 61–99. (From the `/latex/57` extraction;
  volume **17** appears in sibling corpus files and the prior review but not in the
  extraction — DEFERRED.)
- [LiMo20] Liu, H. and Montgomery, R., _A solution to Erdős and Hajnal's odd cycle
  problem_. arXiv:2010.15802 (2020). (From the `/latex/57` extraction. The prior
  review and reviewer knowledge give the published version as J. Amer. Math. Soc. 36
  (2023), 1191–1234; not page-verified — DEFERRED.)
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to see
  solved_. Combinatorica (1981), 25–42. (From the `/latex/57` extraction; volume **1**
  not in the extraction — DEFERRED.)
- [Er95d] Erdős, P., _On some problems in combinatorial set theory_. Publ. Inst. Math.
  (Beograd) (N.S.) (1995), 61–65. (From the `/latex/57` extraction.)
- [Er96] Erdős, P., _Some of my favourite problems on cycles and colourings_. Tatra
  Mt. Math. Publ. (1996), 7–9. (From the `/latex/57` extraction.)
- [Er69b] Erdős, P., _Problems and results in chromatic graph theory_. Proof
  Techniques in Graph Theory (1969). (Corpus-consensus entry; DEFERRED.)
- [Er74d] Erdős, P. (1974). (Key from the page; no expansion recoverable offline —
  DEFERRED.)
- [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős
  (1990). (Corpus-consensus entry; DEFERRED.)
- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph
  theory_. Quaestiones Mathematicae (1993), 333–350. (Corpus-consensus entry; the
  page's pointer [Er93, p.342] falls inside this page range, corroborating the entry —
  still DEFERRED against the live source.)
- [Er94b] Erdős, P. (1994). (Key from the page; sibling corpus files expand this key
  inconsistently — conflict noted, key-only stub, DEFERRED.)
- [Er95] Erdős, P. (1995). (Key from the page; sibling corpus files expand this key
  inconsistently — conflict noted, key-only stub, DEFERRED.)
- [Er97b] Erdős, P. (1997). (Key from the page; sibling corpus files expand this key
  inconsistently — conflict noted, key-only stub, DEFERRED.)
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999), §3.58.
  (Corpus-consensus entry; the page cites [Va99, 3.58] — DEFERRED.)
-/

open SimpleGraph Finset

/--
The set of lengths of odd cycles in a graph $G$: those $n$ such that $n$ is odd and
$G$ has a cycle of length $n$ (a closed walk that is a cycle in Mathlib's sense, so
$n \ge 3$; in particular $0 \notin$ this set, and `Odd` already excludes $0$).

This definition is verbatim the one in `conjectures/58.lean` (same corpus, same
problem family), and its membership predicate is exactly the inline conjunct used in
`erdos_problem_57` below — the main theorem is left in its original, compile-verified
inline form, and this def is used only by the density variants.

NOTE: this def was added by the Fable review and is NOT compile-verified.
-/
def oddCycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {n : ℕ | Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

/--
Erdős Problem #57 (Conjectured by Erdős-Hajnal [ErHa66], proved by Liu-Montgomery [LiMo20]):
If G is a graph with infinite chromatic number and a₁ < a₂ < ⋯ are the lengths of the odd
cycles of G, then ∑ 1/aᵢ = ∞.

We formalize "∑ 1/aᵢ = ∞" as: for any real bound B, there exists a finite set T of odd
natural numbers, each of which is the length of some cycle in G, whose reciprocals sum to
at least B. (Since T is a `Finset` of *lengths*, each length is counted once, matching the
source's enumeration a₁ < a₂ < ⋯ of the set of odd cycle lengths; unboundedness of the
finite partial sums over subsets of a set of positive terms is equivalent to divergence
of the series over that set.)

Status: PROVED — this direct assertion is the true direction, per the page banner
("solved in the affirmative"), the metadata mirror, and [LiMo20].
-/
theorem erdos_problem_57 {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    ∀ (B : ℝ), ∃ (T : Finset ℕ),
      (∀ n ∈ T, Odd n ∧ ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = n) ∧
      B ≤ ∑ n ∈ T, (1 / (n : ℝ)) :=
  sorry

/--
Page-confirmed variant (OPEN — this states the conjectured direction of a question,
not a known theorem): "In [Er81] Erdős asks whether the $a_i$ must in fact have
positive upper density."

Positive upper density of the set $S$ of odd cycle lengths is encoded elementarily:
there is a $c > 0$ such that for infinitely many $N$ (i.e. for every $m$ some
$N \ge m$) at least $c \cdot N$ of the integers in $[0, N]$ lie in $S$, witnessed by a
finite set $T \subseteq S \cap [0, N]$ with $c \cdot N \le |T|$. (Since
$S \cap [0, N]$ is finite, such a $T$ exists iff $|S \cap [0, N]| \ge c N$; and since
all elements of $S$ are odd, positivity of the upper density is the same whether
computed absolutely or relative to the odd numbers.)

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_57.variants.positive_upper_density {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, ∃ N : ℕ, m ≤ N ∧
      ∃ T : Finset ℕ, (∀ n ∈ T, n ≤ N ∧ n ∈ oddCycleLengths G) ∧
        c * (N : ℝ) ≤ (T.card : ℝ) :=
  sorry

/--
Page-confirmed variant (OPEN — this states the speculated direction of a question, not
a known theorem): "in [Er95d] and [Er96] he speculates whether the upper density (or
even upper logarithmic density) must be $\geq 1/2$."

Encoded as: for every $\varepsilon > 0$ there are infinitely many $N$ with at least
$(1/2 - \varepsilon) N$ odd cycle lengths in $[0, N]$ — i.e. the (absolute) upper
density of the set of odd cycle lengths is $\ge 1/2$, the maximum possible for a set
of odd numbers. CAVEAT: the page does not specify absolute vs relative-to-the-odds
upper density; this formalizes the literal (absolute) reading, under which $\ge 1/2$
means density-$1/2$ along a subsequence. Under the relative reading the bound would be
$(1/4 - \varepsilon) N$ instead. The upper *logarithmic* density strengthening
mentioned on the page is not formalized (no logarithmic-weight machinery in this
file). NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_57.variants.upper_density_ge_half {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ N : ℕ, m ≤ N ∧
      ∃ T : Finset ℕ, (∀ n ∈ T, n ≤ N ∧ n ∈ oddCycleLengths G) ∧
        (1 / 2 - ε) * (N : ℝ) ≤ (T.card : ℝ) :=
  sorry

/--
Page-confirmed variant (stated on the page as known): "The lower density of the set
can be $0$ since there are graphs of arbitrarily large chromatic number and girth."

Encoded as: there exists a graph with infinite chromatic number whose set of odd cycle
lengths has lower density $0$ — for every $c > 0$ there are infinitely many $N$ such
that *every* finite set of odd cycle lengths in $[0, N]$ has at most $c \cdot N$
elements (equivalently $|S \cap [0, N]| \le c N$, since $S \cap [0, N]$ is finite).
The witnessing construction is a disjoint union of finite graphs of chromatic number
$k$ and girth $\ge g_k$ for rapidly growing $g_k$ (Erdős's girth/chromatic-number
theorem); the vertex type can be taken in `Type` (universe 0).

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_57.variants.lower_density_can_be_zero :
    ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
      ∀ c : ℝ, 0 < c → ∀ m : ℕ, ∃ N : ℕ, m ≤ N ∧
        ∀ T : Finset ℕ, (∀ n ∈ T, n ≤ N ∧ n ∈ oddCycleLengths G) →
          (T.card : ℝ) ≤ c * (N : ℝ) :=
  sorry
