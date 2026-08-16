import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Finset

/-!
# Erdős Problem #61 — the Erdős–Hajnal conjecture

For any graph H is there some c = c(H) > 0 such that every graph G on n
vertices that does not contain H as an induced subgraph contains either a
complete graph or independent set on ≥ n^c vertices?

Conjectured by Erdős and Hajnal [ErHa89], who proved that a complete graph or
independent set must exist on ≥ exp(c_H √(log n)) many vertices, where
c_H > 0 is some constant. This was improved by Bucić, Nguyen, Scott, and
Seymour [BNSS23] to ≥ exp(c_H √(log n · log log n)). (Both partial results
are formalized as variants below.)

This problem is #80 in Extremal Graph Theory in the graphs problem collection
(remark on the archived page).

**Status: OPEN** ("This is open, and cannot be resolved with a finite
computation." — erdosproblems.com/61, page edition 23 January 2026, accessed
2026-03-05; status re-confirmed open against the teorth/erdosproblems metadata
mirror, `data/problems.yaml` entry 61, last update 2025-08-31, mirror HEAD
a09c7a2 (2026-08-16); the upstream google-deepmind/formal-conjectures file
`FormalConjectures/ErdosProblems/61.lean` at HEAD dd1c2beb (2026-08-16) also
tags the main statement `research open`).

References (page citation line: [ErHa89][Er90][Er93,p.346][Er97f][Va99,3.52];
the page's remarks additionally cite [BNSS23]):

- [ErHa89] Erdős, P. and Hajnal, A., _Ramsey-type theorems_. Discrete Appl.
  Math. (1989), 37–52. (Entry as given in the upstream formal-conjectures
  file; the volume number is absent from every recovered source — DEFERRED,
  not fabricated.)
- [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to
  Paul Erdős (1990), 467–478. (Corpus-consensus entry for this key — DEFERRED
  against the live /latex source.)
- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in
  graph theory_. Quaestiones Mathematicae 16 (1993), 333–350.
  (Corpus-consensus entry; the page's locator [Er93, p.346] falls inside this
  page range, corroborating the identification — DEFERRED against the live
  source.)
- [Er97f] Erdős, P. (1997). (Bare stub: no bibliographic data for this key
  was recoverable from the session logs, sibling files, or the upstream
  file — DEFERRED, not fabricated.)
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
  the conference "Paul Erdős and his mathematics", Budapest, July 1999
  (1999), §3.52. (Corpus-consensus entry — DEFERRED against the live source.)
- [BNSS23] Bucić, M., Nguyen, T., Scott, A. and Seymour, P., _A loglog step
  towards Erdős–Hajnal_. (Title from the upstream formal-conjectures file;
  venue/identifier absent from the recovered page and logs — DEFERRED, not
  fabricated.)

Further known partial results, recorded in the upstream formal-conjectures
file but not in the archived page's remarks (hence noted here rather than
added as variants): Nguyen, Scott, and Seymour proved the conjecture for
H = P₅ (arXiv:2312.15333), and Chudnovsky, Scott, Seymour, and Spirkl proved
it for H = C₅ (Proc. Lond. Math. Soc. (3) 126 (2023), 997–1014).

Tags: graph theory. Related OEIS sequences: none (the metadata mirror records
N/A). https://www.erdosproblems.com/61
-/

/--
Erdős Problem #61 (Erdős-Hajnal Conjecture) [ErHa89, Er90, Er93, Er97f, Va99]:

For any graph H, is there some c = c(H) > 0 such that every graph G on n
vertices that does not contain H as an induced subgraph contains either a
complete graph or independent set on ≥ n^c vertices?

Conjectured by Erdős and Hajnal, who proved the weaker bound
exp(c_H √(log n)). Improved by Bucić, Nguyen, Scott, and Seymour [BNSS23] to
exp(c_H √(log n · log log n)).

The problem is an OPEN yes/no question; following this corpus's raw-pipeline
convention for open questions, this theorem asserts the conjectured "yes"
direction directly. Encoding notes: H ranges over `SimpleGraph (Fin k)` for
all k — every finite graph is isomorphic to one of these, and
induced-subgraph containment is isomorphism-invariant; "G does not contain H
as an induced subgraph" is the nonexistence of a vertex embedding under which
adjacency in H holds *iff* adjacency in G holds on the image; the bound
`(n : ℝ) ^ c` is real rpow, so at n = 0 the requirement `card ≥ 0 ^ c = 0`
(for c > 0) is met by the empty set and the statement stays true rather than
degenerating; and the all-n form is equivalent to the "sufficiently large n"
form used upstream, because every graph on n ≥ 2 vertices has a clique or an
independent set of size 2 (any two vertices form an edge or a non-edge), so
the finitely many small n are absorbed by shrinking c.
-/
theorem erdos_problem_61 :
    ∀ (k : ℕ) (H : SimpleGraph (Fin k)),
      ∃ c : ℝ, 0 < c ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          (¬ ∃ (f : Fin k ↪ Fin n), ∀ i j, H.Adj i j ↔ G.Adj (f i) (f j)) →
          ∃ (S : Finset (Fin n)),
            (S.card : ℝ) ≥ (n : ℝ) ^ c ∧
            (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) :=
  sorry

/--
**Variant (Erdős–Hajnal [ErHa89], solved):** for any graph H there is a
constant c_H > 0 such that every graph on n ≥ 1 vertices not containing H as
an induced subgraph contains a clique or independent set on
≥ exp(c_H √(log n)) vertices.

(The `1 ≤ n` hypothesis is essential: at n = 0, Lean's junk value
`Real.log 0 = 0` makes the bound `Real.exp 0 = 1 > 0 = card ∅`, so the
unguarded all-n form would be false for every H with at least one vertex. At
n = 1 the bound is `exp (c·0) = 1`, met by a singleton clique. The guarded
all-n form is equivalent to the "sufficiently large n" form by shrinking c_H,
since every graph on ≥ 2 vertices has a clique or independent set of size 2.
Page-confirmed remark; added by the fable-review pass; not compile-verified.)
-/
theorem erdos_problem_61.variants.erdos_hajnal_bound :
    ∀ (k : ℕ) (H : SimpleGraph (Fin k)),
      ∃ c : ℝ, 0 < c ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 1 ≤ n →
          (¬ ∃ (f : Fin k ↪ Fin n), ∀ i j, H.Adj i j ↔ G.Adj (f i) (f j)) →
          ∃ (S : Finset (Fin n)),
            (S.card : ℝ) ≥ Real.exp (c * Real.sqrt (Real.log n)) ∧
            (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) :=
  sorry

/--
**Variant (Bucić–Nguyen–Scott–Seymour [BNSS23], solved):** for any graph H
there is a constant c_H > 0 such that every graph on n ≥ 1 vertices not
containing H as an induced subgraph contains a clique or independent set on
≥ exp(c_H √(log n · log log n)) vertices.

(Junk-value audit as in the previous variant: `1 ≤ n` excludes the false
n = 0 case. At n = 1, `log 1 = 0` gives bound `exp 0 = 1`, met by a
singleton. At n = 2, `log (log 2) < 0` makes the product negative, and
`Real.sqrt` of a negative is 0, so the bound is again 1 — harmlessly weak,
never false. Page-confirmed remark; added by the fable-review pass; not
compile-verified.)
-/
theorem erdos_problem_61.variants.bnss_bound :
    ∀ (k : ℕ) (H : SimpleGraph (Fin k)),
      ∃ c : ℝ, 0 < c ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 1 ≤ n →
          (¬ ∃ (f : Fin k ↪ Fin n), ∀ i j, H.Adj i j ↔ G.Adj (f i) (f j)) →
          ∃ (S : Finset (Fin n)),
            (S.card : ℝ) ≥
              Real.exp (c * Real.sqrt (Real.log n * Real.log (Real.log n))) ∧
            (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) :=
  sorry
