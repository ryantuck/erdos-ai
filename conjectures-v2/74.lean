import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Data.Finset.Prod

/-!
# Erdős Problem 74

*Reference:* [erdosproblems.com/74](https://www.erdosproblems.com/74)
(accessed 2026-03-05, page last edited 25 January 2026; page content recovered from an
archived session-log capture — the live site is unreachable from the review container).

Statement (verbatim from the site): "Let $f(n)\to \infty$ (possibly very slowly). Is
there a graph of infinite chromatic number such that every finite subgraph on $n$
vertices can be made bipartite by deleting at most $f(n)$ edges?"
[EHS82][Er87][Er90][Er93,p.342][Er94b][Er95][Er95d,p.62][Er96][Er97b][Er97c][Er97d][Er97f]
— tags: graph theory, chromatic number, cycles.

Status: **OPEN**, $500 prize ("This is open, and cannot be resolved with a finite
computation."). The teorth/erdosproblems metadata mirror (`data/problems.yaml`, checked
at commit a09c7a2, 2026-08-14) agrees: status "open", last update 2025-08-31; prize
$500; OEIS N/A; formalized upstream: yes (2025-09-25). The upstream
google-deepmind/formal-conjectures repository (HEAD dd1c2beb, 2026-08-16) has
`FormalConjectures/ErdosProblems/74.lean` with an equivalent `answer(sorry) ↔`
formalization plus a √n variant.

Remarks from the page: "Conjectured by Erdős, Hajnal, and Szemerédi [EHS82]. Rödl
[Ro82] has proved this for hypergraphs, and also proved there is such a graph (with
chromatic number ℵ₀) if $f(n)=\epsilon n$ for any fixed constant $\epsilon>0$. It is
open even for $f(n)=\sqrt{n}$. Erdős offered \$500 for a proof but only \$250 for a
counterexample. This fails (even with $f(n)\gg n$) if the graph has chromatic number
ℵ₁ (see [111])." The prize asymmetry indicates the conjectured direction is
affirmative, which is the direction asserted below.

References (no raw `/latex/74` capture survives in the logs; provenance per entry):

- [EHS82] Erdős, P., Hajnal, A., and Szemerédi, E., _On almost bipartite large
  chromatic graphs_. Theory and Practice of Combinatorics (= Annals of Discrete
  Mathematics 12) (1982), 117–123. (From the upstream formal-conjectures 74.lean
  docstring, corroborated by sibling-corpus consensus; DEFERRED against the live
  `/latex/74`.)
- [Ro82] Rödl, V. (1982). (Cited in the page remarks only; full data not recoverable
  offline — the sibling `conjectures/1092.lean` records the same stub. DEFERRED, not
  fabricated.)
- [Er87] Erdős, P. (1987). (Key from the page header only; sibling expansions
  conflict — full data DEFERRED, not fabricated.)
- [Er90] Erdős, P. (1990). (Key-only stub; full data DEFERRED.)
- [Er93] Erdős, P. (1993), p. 342. (Key-only stub; full data DEFERRED.)
- [Er94b] Erdős, P. (1994). (Key-only stub; full data DEFERRED.)
- [Er95] Erdős, P. (1995). (Key-only stub; full data DEFERRED.)
- [Er95d] Erdős, P. (1995), p. 62. (Key-only stub; full data DEFERRED.)
- [Er96] Erdős, P. (1996). (Key-only stub; full data DEFERRED.)
- [Er97b] Erdős, P. (1997). (Key-only stub; full data DEFERRED.)
- [Er97c] Erdős, P. (1997). (Key-only stub; full data DEFERRED.)
- [Er97d] Erdős, P. (1997). (Key-only stub; full data DEFERRED.)
- [Er97f] Erdős, P. (1997). (Key-only stub; full data DEFERRED.)
-/

open Filter SimpleGraph Finset

/--
Erdős Problem #74 [EHS82][Er87][Er90][Er93,p.342][Er94b][Er95][Er95d,p.62][Er96][Er97b][Er97c][Er97d][Er97f]
(OPEN, $500):

Let f(n) → ∞ (possibly very slowly). Is there a graph of infinite chromatic
number such that every finite subgraph on n vertices can be made bipartite by
deleting at most f(n) edges?

Conjectured by Erdős, Hajnal, and Szemerédi [EHS82]. Rödl [Ro82] proved this for
hypergraphs and also proved there is such a graph (with chromatic number ℵ₀) if
f(n) = εn for any fixed ε > 0. It is open even for f(n) = √n. Erdős offered $500
for a proof but only $250 for a counterexample. The statement fails (even with
f(n) ≫ n) if the graph has chromatic number ℵ₁ (see Erdős Problem [111]).

The formalization states: for any f : ℕ → ℕ tending to infinity, there exists
a graph G with infinite chromatic number such that for every finite subset S
of vertices, there is a 2-coloring with at most f(|S|) monochromatic edges.
The count uses ordered pairs (each unordered edge counted twice), hence the
factor of 2.

Encoding note: the source poses a yes/no question that is open; this direct
assertion states the *conjectured* (affirmative) direction, per the pipeline
convention for open questions. A graph can be made bipartite by deleting at
most k edges iff some 2-coloring has at most k monochromatic edges, and
quantifying over finite vertex subsets (induced subgraphs) is equivalent to
quantifying over all finite subgraphs, since a subgraph has at most the edges
of the induced subgraph on the same vertices.
-/
theorem erdos_problem_74 :
    ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
      ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        (∀ k : ℕ, ¬G.Colorable k) ∧
        ∀ (S : Finset V),
          ∃ c : V → Bool,
            ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2 ∧ c p.1 = c p.2)).card
              ≤ 2 * f S.card :=
  sorry

/--
The √n case of Erdős Problem #74, singled out on the problem page: "It is open
even for f(n) = √n." Is there a graph of infinite chromatic number such that
every finite subgraph on n vertices can be made bipartite by deleting at most
√n edges? (The upstream formal-conjectures file carries the same variant.)

Encoding: with the ordered-pair count equal to 2m (m the number of
monochromatic unordered edges within S), the condition m ≤ √n for m, n : ℕ is
equivalent to m² ≤ n, i.e. (2m)² ≤ 4n — stated below as card² ≤ 4·|S| to avoid
introducing real numbers into the file.

[Variant added by the Fable review from the recovered page remark; new Lean
statement, not compile-verified.]
-/
theorem erdos_problem_74.variants.sqrt :
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      (∀ k : ℕ, ¬G.Colorable k) ∧
      ∀ (S : Finset V),
        ∃ c : V → Bool,
          ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2 ∧ c p.1 = c p.2)).card ^ 2
            ≤ 4 * S.card :=
  sorry

/--
Rödl's theorem [Ro82], from the problem page: "Rödl has proved … there is such
a graph (with chromatic number ℵ₀) if f(n) = εn for any fixed constant ε > 0."

Encoding: ε ranges over the positive rationals a/b (a, b : ℕ, positive); the
bound m ≤ (a/b)·n on the monochromatic-edge count m is stated multiplicatively
as b·(2m) ≤ 2a·n, avoiding real numbers. This is equivalent to the statement
for every fixed real ε > 0, since any such ε is bounded below by a positive
rational and the bound is monotone in ε. The vertex type is fixed to ℕ: a graph
on countably many vertices always has chromatic number ≤ ℵ₀, so together with
the first conjunct (no finite coloring) this captures "chromatic number ℵ₀"
exactly.

[Variant added by the Fable review from the recovered page remark; new Lean
statement, not compile-verified.]
-/
theorem erdos_problem_74.variants.rodl_linear :
    ∀ a b : ℕ, 0 < a → 0 < b →
      ∃ (G : SimpleGraph ℕ) (_ : DecidableRel G.Adj),
        (∀ k : ℕ, ¬G.Colorable k) ∧
        ∀ (S : Finset ℕ),
          ∃ c : ℕ → Bool,
            b * ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2 ∧ c p.1 = c p.2)).card
              ≤ 2 * a * S.card :=
  sorry
