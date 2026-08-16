import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #58

If G is a graph which contains odd cycles of ≤ k different lengths then
χ(G) ≤ 2k+2, with equality if and only if G contains K_{2k+2}.

Conjectured by Bollobás and Erdős [Er90]. Bollobás and Shelah confirmed it for k=1.
Proved by Gyárfás [Gy92], who showed the stronger result that if G is 2-connected,
then G is either K_{2k+2} or contains a vertex of degree at most 2k.

A stronger form was established by Gao, Huo, and Ma [GaHuMa21], who proved that if a
graph G has chromatic number χ(G) ≥ 2k+3 then G contains cycles of k+1 consecutive
odd lengths (formalized as a variant below).

Status: PROVED — "This has been solved in the affirmative" (erdosproblems.com/58,
archived captures accessed 2026-02-22 and 2026-02-23; metadata mirror
teorth/erdosproblems: proved, last update 2025-08-31).

References:

[Er90] Erdős, P., Some of my favourite unsolved problems. A tribute to Paul Erdős
(1990), 467–478.

[Gy92] Gyárfás, A., Graphs with k odd cycle lengths. Discrete Mathematics 103 (1992),
41–48.

[GaHuMa21] Gao, J., Huo, Q., Ma, J., A strengthening on odd cycles in graphs of given
chromatic number. SIAM Journal on Discrete Mathematics 35 (2021), 2317–2327.

(Provenance: titles, journals, years, and page ranges for [Gy92]/[GaHuMa21] are from
the archived /latex/58 fetch; the volume numbers 103 and 35 are not in that capture
and come from reviewer knowledge, matching the styled sibling deepmind/deepmind/58.lean.
The [Er90] entry follows the corpus-wide entry for that key.)

Tags: graph theory, chromatic number, cycles
https://www.erdosproblems.com/58
-/

/-- The set of lengths of odd cycles in a graph G.

(In Mathlib a `Walk.IsCycle` has length ≥ 3, so `1 ∉ oddCycleLengths G`; over a
`Fintype` vertex set every cycle has length ≤ |V|, so this set is finite and
`Set.ncard` counts it honestly.) -/
def oddCycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {n : ℕ | Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

/--
**Erdős Problem #58** (Bollobás–Erdős conjecture, proved by Gyárfás [Gy92]):

If G is a finite graph containing odd cycles of at most k different lengths,
then χ(G) ≤ 2k + 2, with equality if and only if G contains K_{2k+2} as a
clique subgraph.

The source says "graph"; this statement is restricted to finite graphs — the setting
of Gyárfás's proof. Finiteness also guards the `Set.ncard` hypothesis: on an infinite
set `ncard` returns the junk value 0, which would make the hypothesis vacuously true.
-/
theorem erdos_problem_58 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hk : (oddCycleLengths G).ncard ≤ k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ) ∧
    (G.chromaticNumber = (2 * k + 2 : ℕ) ↔ ∃ s : Finset V, G.IsNClique (2 * k + 2) s) :=
  sorry

/--
**Variant (Gao–Huo–Ma strengthening [GaHuMa21]):** if a finite graph G has chromatic
number χ(G) ≥ 2k+3, then G contains cycles of k+1 consecutive odd lengths
ℓ, ℓ+2, …, ℓ+2k. Since these are k+1 distinct odd cycle lengths, the contrapositive
recovers the bound χ(G) ≤ 2k+2 of the main statement. Recorded in the remarks of the
archived problem page. (Added by the fable-review pass; not compile-verified.)
-/
theorem erdos_problem_58.variants.gao_huo_ma {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hchi : (2 * k + 3 : ℕ) ≤ G.chromaticNumber) :
    ∃ ℓ : ℕ, Odd ℓ ∧ ∀ i ≤ k, ℓ + 2 * i ∈ oddCycleLengths G :=
  sorry

end
