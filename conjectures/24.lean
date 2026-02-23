import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic

open SimpleGraph Finset

/--
Erdős Problem #24 (Proved by Grzesik [Gr12] and Hatami-Hladky-Král-Norine-Razborov [HHKNR13]):
Every triangle-free graph on 5n vertices contains at most n^5 copies of C_5.

We count labeled 5-cycles: injective functions f : Fin 5 → Fin (5n) such that
f(i) is adjacent to f((i+1) mod 5) for all i. Each unordered C_5 yields exactly
10 labeled 5-cycles (5 rotations × 2 reflections), so the labeled count bound is 10 · n^5.
-/
theorem erdos_problem_24 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin (5 * n))) (h : DecidableRel G.Adj),
    haveI := h
    G.CliqueFree 3 →
    (Finset.univ.filter (fun (f : Fin 5 → Fin (5 * n)) =>
      Function.Injective f ∧
      ∀ i : Fin 5, G.Adj (f i) (f (i + 1)))).card
    ≤ 10 * n ^ 5 :=
  sorry
