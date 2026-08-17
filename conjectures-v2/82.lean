import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Finset Real Classical

noncomputable section

/--
The degree of vertex `v` in the subgraph of `G` induced by vertex set `S`:
the number of vertices in `S` adjacent to `v` in `G`.

(Note `G.Adj v v` is false, so `v` itself is never counted, even when `v ∈ S`;
this is exactly the degree of `v` in the induced subgraph on `S`.)
-/
def inducedDegree {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  (S.filter (G.Adj v)).card

/--
Erdős Problem #82 [Er93, p.340][Er95][Er97d]:

Let F(n) be maximal such that every graph on n vertices contains a regular
induced subgraph on at least F(n) vertices. Prove that F(n)/log n → ∞.

Conjectured by Erdős, Fajtlowicz, and Staton. (The problem page's remark
spells "Stanton" once, but the author of [FMRS95] and the standard attribution
is Staton.) It is known that F(5) = 3 and F(7) = 4. Ramsey's theorem implies
that F(n) ≫ log n (trivial subgraphs — cliques and independent sets — are
regular). Bollobás observed that F(n) ≪ n^{1/2+o(1)}. Alon, Krivelevich, and
Sudakov [AKS07] improved the upper bound to n^{1/2}(log n)^{O(1)}.

In [Er93] Erdős further asks: if t(n) is the largest trivial (empty or
complete) induced subgraph that every graph on n vertices must contain (so
t(n) ≫ log n by Ramsey), is it true that F(n) − t(n) → ∞? Equivalently, if
G(n) is the minimal m such that every graph on m vertices contains a regular
induced subgraph on at least n vertices, is G(n) ≤ 2^{o(n)}? Fajtlowicz,
McColgan, Reid, and Staton [FMRS95] showed G(1) = 1, G(2) = 2, G(3) = 5,
G(4) = 7, and G(5) ≥ 12; Alexeev and McKay computed G(5) = 17, G(6) ≥ 21,
and G(7) ≥ 29. (Not formalized here: t(n) and G(n) would need further
definitions.)

Status: OPEN (erdosproblems.com/82, page edition 06 October 2025, accessed
2026-03-05; confirmed open by the teorth/erdosproblems metadata mirror as of
2026-08-14). See also Problem #1031 for another question on induced regular
subgraphs. Related OEIS sequences: A120414, A390256, A390257 (page), and per
the metadata mirror also A390919, A392636, A394400, A394462, A394539,
A394563, A394564, A394573, A394574, A394930, A394933.

The statement below is equivalent to F(n)/log n → ∞: for every constant
C > 0 and all sufficiently large n, every graph on n vertices contains a
regular induced subgraph on at least C · log n vertices.

References (journal data beyond what is listed is not recoverable offline —
honest stubs only):

[Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph
theory_. Quaestiones Mathematicae **16** (1993), 333–350.

[Er95] Erdős, P., 1995. (Title/venue not recoverable offline; sibling files
in this corpus expand this key inconsistently, so no expansion is asserted.)

[Er97d] Erdős, P., 1997. (Title/venue not recoverable offline; sibling files
in this corpus expand this key inconsistently, so no expansion is asserted.)

[AKS07] Alon, N., Krivelevich, M., and Sudakov, B., _Large nearly regular
induced subgraphs_. arXiv:0710.2106 (2007).

[FMRS95] Fajtlowicz, S., McColgan, T., Reid, T., and Staton, W., 1995.
(Title/venue not recoverable offline.)
-/
theorem erdos_problem_82 :
    ∀ C : ℝ, 0 < C →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ G : SimpleGraph (Fin n),
          ∃ S : Finset (Fin n),
            (S.card : ℝ) ≥ C * Real.log n ∧
            ∃ d : ℕ, ∀ v ∈ S, inducedDegree G S v = d :=
  sorry

/--
Variant (solved): F(n) ≫ log n — there is a single constant c > 0 such that
every sufficiently large graph on n vertices contains a regular induced
subgraph on at least c · log n vertices. This follows from Ramsey's theorem,
since cliques and independent sets are regular induced subgraphs.
[erdosproblems.com/82, remarks]
-/
theorem erdos_problem_82.variants.lower_bound_ramsey :
    ∃ c : ℝ, 0 < c ∧
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ G : SimpleGraph (Fin n),
          ∃ S : Finset (Fin n),
            (S.card : ℝ) ≥ c * Real.log n ∧
            ∃ d : ℕ, ∀ v ∈ S, inducedDegree G S v = d :=
  sorry

/--
Variant (solved, [AKS07]): F(n) ≤ n^{1/2}(log n)^{O(1)} — for some constants
C > 0 and k, every sufficiently large n admits a graph on n vertices whose
every regular induced subgraph S satisfies |S|² ≤ C · n · (log n)^k.

The bound is stated in squared form to avoid `Real.sqrt` (not reachable from
this file's imports): |S|² ≤ C n (log n)^k is equivalent to
|S| ≤ √C · n^{1/2} (log n)^{k/2}, and any n^{1/2}(log n)^{O(1)} bound has
this form (AKS07 prove the stronger F(n) = O(n^{1/2} log^{3/4} n), which
gives this with k = 2 once log n ≥ 1).
-/
theorem erdos_problem_82.variants.upper_bound_aks :
    ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ G : SimpleGraph (Fin n),
          ∀ S : Finset (Fin n),
            (∃ d : ℕ, ∀ v ∈ S, inducedDegree G S v = d) →
            ((S.card : ℝ)) ^ 2 ≤ C * (n : ℝ) * (Real.log n) ^ k :=
  sorry

/--
Variant (solved): F(5) = 3 — every graph on 5 vertices contains a regular
induced subgraph on at least 3 vertices, and some graph on 5 vertices has no
regular induced subgraph on more than 3 vertices.
[erdosproblems.com/82, remarks: "It is known that F(5)=3 and F(7)=4."]
-/
theorem erdos_problem_82.variants.F_five :
    (∀ G : SimpleGraph (Fin 5), ∃ S : Finset (Fin 5),
      3 ≤ S.card ∧ ∃ d : ℕ, ∀ v ∈ S, inducedDegree G S v = d) ∧
    (∃ G : SimpleGraph (Fin 5), ∀ S : Finset (Fin 5),
      (∃ d : ℕ, ∀ v ∈ S, inducedDegree G S v = d) → S.card ≤ 3) :=
  sorry

/--
Variant (solved): F(7) = 4 — every graph on 7 vertices contains a regular
induced subgraph on at least 4 vertices, and some graph on 7 vertices has no
regular induced subgraph on more than 4 vertices.
[erdosproblems.com/82, remarks: "It is known that F(5)=3 and F(7)=4."]
-/
theorem erdos_problem_82.variants.F_seven :
    (∀ G : SimpleGraph (Fin 7), ∃ S : Finset (Fin 7),
      4 ≤ S.card ∧ ∃ d : ℕ, ∀ v ∈ S, inducedDegree G S v = d) ∧
    (∃ G : SimpleGraph (Fin 7), ∀ S : Finset (Fin 7),
      (∃ d : ℕ, ∀ v ∈ S, inducedDegree G S v = d) → S.card ≤ 4) :=
  sorry

end
