import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #78

*Reference:* [erdosproblems.com/78](https://www.erdosproblems.com/78)
(accessed 2026-02-22, page last edited 23 January 2026; page content recovered from an
archived session-log capture — the live site is unreachable from the review container).

Statement (verbatim from the site): "Let $R(k)$ be the Ramsey number for $K_k$, the
minimal $n$ such that every $2$-colouring of the edges of $K_n$ contains a monochromatic
copy of $K_k$. Give a constructive proof that $R(k)>C^k$ for some constant $C>1$."
[Er69b][Er71][Er88][Er93,p.337][Er95][Er97c][Va99,3.49] — tags: graph theory,
ramsey theory.

Status: **OPEN**, $100 prize ("This is open, and cannot be resolved with a finite
computation."). The teorth/erdosproblems metadata mirror (`data/problems.yaml`, checked
at commit a09c7a2, 2026-08-14) agrees: status "open", last update 2025-08-31; prize
$100; OEIS A059442; formalized upstream: no (confirmed — upstream
google-deepmind/formal-conjectures at HEAD dd1c2beb has no `ErdosProblems/78.lean`).

Remarks from the page: "Erdős gave a simple probabilistic proof that
$R(k) \gg k2^{k/2}$. Equivalently, this question asks for an explicit construction of a
graph on $n$ vertices which does not contain any clique or independent set of size
$\geq c\log n$ for some constant $c>0$. In [Er69b] Erdős asks for even a construction
whose largest clique or independent set has size $o(n^{1/2})$, which is now known.
Cohen [Co15] (see the introduction for further history) constructed a graph on $n$
vertices which does not contain any clique or independent set of size
$\geq 2^{(\log\log n)^{C}}$ for some constant $C>0$. Li [Li23b] has recently improved
this to $\geq (\log n)^{C}$ for some constant $C>0$. This problem is #4 in Ramsey
Theory in the graphs problem collection." Additional thanks: Jesse Goodman and Mehtaab
Sawhney. Related problems in this corpus: #77 (existence of $\lim R(k)^{1/k}$).

References (no `/latex/78` or `/bibs/` capture survives in the logs; provenance per
entry, none fabricated):

- [Er69b] Erdős, P., _Problems and results in chromatic graph theory_ (1969).
  (Expansion attested across sibling ai-review sessions for problems 917–925; full
  venue/pages DEFERRED against the live `/latex/78`. The styled
  `deepmind/deepmind/78.lean` expansion "Some applications of Ramsey's theorem to
  additive number theory, European J. Combin. (1969)" is anachronistic — that journal
  began in 1980 — and was not adopted.)
- [Er71] Erdős, P. (1971). (Key-only stub; sibling expansions conflict — full data
  DEFERRED.)
- [Er88] Erdős, P. (1988). (Key-only stub; sibling expansions conflict — full data
  DEFERRED.)
- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph
  theory_. Quaestiones Mathematicae **16** (1993), 333–350; cited at p. 337.
  (Sibling-corpus expansion; the cited p. 337 falls inside the 333–350 page range,
  unlike the competing "On some of my favourite theorems" expansion. DEFERRED against
  the live source.)
- [Er95] Erdős, P. (1995). (Key-only stub; sibling and upstream expansions conflict —
  full data DEFERRED.)
- [Er97c] Erdős, P., _Some recent problems and results in graph theory_. Discrete
  Math. **164** (1997), 81–85. (Sibling-corpus consensus; DEFERRED against the live
  source.)
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his Mathematics" (Budapest, 1999); item 3.49.
  (Sibling-corpus consensus. The styled file's attribution to "Vaughan, R. C." is
  unsupported and was not adopted.)
- [Co15] Cohen, G., _Two-source dispersers for polylogarithmic entropy and improved
  Ramsey graphs_ (2015). (Reviewer attribution: Gil Cohen, STOC 2016; the styled
  file's initial "Cohen, D." appears incorrect. DEFERRED against the live source.)
- [Li23b] Li, X. (2023). (The page credits Li with explicit Ramsey graphs having no
  clique or independent set of size $\geq (\log n)^C$; reviewer attribution: Xin Li,
  via two-source extractors. Full title DEFERRED.)
-/

open SimpleGraph

/--
Erdős Problem #78 (Open, $100 prize)
[Er69b][Er71][Er88][Er93,p.337][Er95][Er97c][Va99,3.49]:

Let R(k) be the Ramsey number for K_k, the minimal n such that every
2-colouring of the edges of K_n contains a monochromatic copy of K_k.
Give a constructive proof that R(k) > C^k for some constant C > 1.

Erdős gave a simple probabilistic (non-constructive) proof that
R(k) ≫ k · 2^{k/2}. This problem asks for an explicit/constructive
lower bound that is still exponential in k.

Equivalently, this asks for an explicit construction of a graph on n
vertices which does not contain any clique or independent set of size
≥ c · log(n) for some constant c > 0. Partial progress: Cohen [Co15]
constructed a graph on n vertices with no clique or independent set of
size ≥ 2^{(log log n)^C}; Li [Li23b] improved this to ≥ (log n)^C.

We formalize the core mathematical content: there exists C > 1 such that
for all k ≥ 3, there exists a graph on at least C^k vertices with no
clique or independent set of size k (an independent set of size k in G
is a clique of size k in Gᶜ). The "constructive" requirement pertains
to the nature of the proof, not the formal statement itself; as a bare
existential the statement below is in fact provable classically via the
probabilistic method, and its OPEN status refers to the demand for an
explicit construction.

Note on the range of k (fix applied by the Fable review): the first-pass
version quantified over k ≥ 2, which makes the statement *false* — since
C > 1 forces C^2 > 1, the witness n must satisfy n ≥ 2, and no graph on
n ≥ 2 vertices is simultaneously K_2-free (edgeless) and co-K_2-free
(complete). The informal inequality R(2) = 2 > C^2 survives for
1 < C < √2, but this encoding demands a graph on n ≥ ⌈C^k⌉ ≥ 2 vertices,
i.e. R(2) ≥ 3, which fails. Restricting to k ≥ 3 restores truth
(R(3) = 6 and R(k) > 2^{k/2} for k ≥ 3 give the claim for any
C ≤ 1.1, say) while preserving the problem's asymptotic content.
-/
theorem erdos_problem_78 :
    ∃ C : ℝ, C > 1 ∧ ∀ k : ℕ, k ≥ 3 →
      ∃ n : ℕ, (C ^ k : ℝ) ≤ ↑n ∧
        ∃ G : SimpleGraph (Fin n),
          G.CliqueFree k ∧ Gᶜ.CliqueFree k :=
  sorry

/--
Erdős Problem #78, o(√n) variant [Er69b] (SOLVED):

From the problem page: "In [Er69b] Erdős asks for even a construction whose
largest clique or independent set has size o(n^{1/2}), which is now known."
(Indeed the Frankl–Wilson construction and the later work of Cohen [Co15]
and Li [Li23b] achieve far smaller clique/independence numbers.)

Encoding: a bound function f : ℕ → ℕ with f(n) = o(n^{1/2}) — stated
equivalently as f(n)² = o(n) to avoid introducing square roots into the
file — such that every n admits a graph on n vertices with no clique and
no independent set of size f(n). The little-o is unfolded to its
ε–N definition, using only constructs already present in the file. As with
the main statement, the formal existential does not capture explicitness;
it is recorded here as the page reports the question solved.

[Variant added by the Fable review from the recovered page remark; new Lean
statement, not compile-verified.]
-/
theorem erdos_problem_78.variants.sqrt :
    ∃ f : ℕ → ℕ,
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ((f n : ℝ)) ^ 2 ≤ ε * ↑n) ∧
      ∀ n : ℕ, ∃ G : SimpleGraph (Fin n),
        G.CliqueFree (f n) ∧ Gᶜ.CliqueFree (f n) :=
  sorry
