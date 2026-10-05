-- [AI - Claude Sonnet 5.5]: Erdős Problem 130 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open SimpleGraph

/-!
# Erdős Problem #130: Integer-Distance Graphs of General-Position Sets

*Source:* [erdosproblems.com/130](https://www.erdosproblems.com/130) (banner **OPEN** at capture:
"This is open, and cannot be resolved with a finite computation."; captured 2026-02-20 as the
tidied problem box). [Er97b] [AnEr45]

Let $A\subset\mathbb{R}^2$ be an infinite set which contains no three points on a line and no
four points on a circle. Consider the graph with vertices the points in $A$, where two vertices
are joined by an edge if and only if they are an integer distance apart.

How large can the chromatic number and clique number of this graph be? In particular, can the
chromatic number be infinite?

Remarks recorded on the page:
* Asked by Andrásfai and Erdős. Erdős [Er97b] also asked where such a graph could contain an
  infinite complete graph, but this is impossible by an earlier result of Anning and Erdős
  [AnEr45].
* See also [213].

Tags: graph theory, chromatic number. 0 comments at capture.

**Status.** At capture the banner was OPEN, and the mirror (`teorth/erdosproblems`) still has
`open` (2025-08-31). Upstream `erdos_130` is now `answer(True) ↔ …`, category `research solved`,
with a link to a Lean proof in an external repository. That proof has not been checked here. The
first pass asserts the asked ("yes") direction, which is the one upstream records as proved.

**What is formalized.** The "in particular" question: can the chromatic number be infinite? The
first question, how large the chromatic number and the clique number can be, is open-ended and
not a precise statement.

**The clique half and Problem 213.** An infinite general-position set whose graph contains an
$n$-clique exists exactly when there are $n$ points in general position with all pairwise distances
integers: such a set extends to an infinite one by adding generic points. So how large the clique
number can be is the question of Problem 213, which upstream lists as open, with $n=7$ the best
known construction (Kreisel and Kurz). If such sets existed for every $n$, the chromatic number
would be infinite at once.

**Encoding.**
* `Concyclic a b c d` says that four points lie at one positive distance from a common centre.
* `ErdosGeneralPosition A` quantifies over distinct points, as it must: three equal points are
  trivially collinear. A line contains no four points of $A$ by the first condition, so the
  "no four on a circle" condition loses nothing.
* `intDistGraph A` lives on the subtype `↥A`. Distinct points have positive distance, so the
  condition `0 < n` is redundant and harmless.
* `chromaticNumber = ⊤` means that no finite colouring is proper, which is the reading of
  "infinite chromatic number".
* **A correction to the first pass.** Its docstring said the clique number is always finite
  because of the Anning–Erdős theorem. That theorem excludes an infinite clique only. Cliques of
  unbounded finite size are not excluded, and whether they occur is Problem 213.

## References

* [Er97b] Erdős, P., _Some old and new problems in various branches of combinatorics_. Discrete
  Math. (1997), 227–231.
* [AnEr45] Anning, N. H. and Erdős, P., _Integral distances_. Bull. Amer. Math. Soc. (1945),
  598–600.

(Provenance: both entries are from the one `/latex/130` fetch in the session logs.)
-/

/-- A set of four points in ℝ² is concyclic if they all lie on a common circle
    (i.e., there exist a center O ∈ ℝ² and radius r > 0 such that each of the
    four points is at distance r from O). -/
def Concyclic (a b c d : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ (center : EuclideanSpace ℝ (Fin 2)) (radius : ℝ),
    0 < radius ∧
    dist a center = radius ∧
    dist b center = radius ∧
    dist c center = radius ∧
    dist d center = radius

/-- A point set A ⊆ ℝ² is in Erdős general position if no three distinct points
    of A are collinear, and no four distinct points of A are concyclic. -/
def ErdosGeneralPosition (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (∀ p q r : EuclideanSpace ℝ (Fin 2),
    p ∈ A → q ∈ A → r ∈ A →
    p ≠ q → p ≠ r → q ≠ r →
    ¬Collinear ℝ ({p, q, r} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
  (∀ p q r s : EuclideanSpace ℝ (Fin 2),
    p ∈ A → q ∈ A → r ∈ A → s ∈ A →
    p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
    ¬Concyclic p q r s)

/-- The integer-distance graph on a point set A ⊆ ℝ²: vertices are points of A,
    and two distinct points are adjacent if and only if their Euclidean distance
    is a positive integer. -/
noncomputable def intDistGraph (A : Set (EuclideanSpace ℝ (Fin 2))) :
    SimpleGraph ↥A where
  Adj p q := (p : EuclideanSpace ℝ (Fin 2)) ≠ q ∧
    ∃ n : ℕ, 0 < n ∧ dist (p : EuclideanSpace ℝ (Fin 2)) (q : EuclideanSpace ℝ (Fin 2)) = n
  symm := fun _p _q ⟨hne, n, hn, hd⟩ => ⟨hne.symm, n, hn, by rw [dist_comm]; exact hd⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/--
Erdős Problem #130 [Er97b] (asked by Andrásfai and Erdős) — OPEN on the page at capture, recorded
as PROVED upstream (that proof is not checked here):
Let A ⊆ ℝ² be an infinite set with no three points collinear and no four points
concyclic. Consider the integer-distance graph G on A, where two distinct points
are adjacent if and only if their Euclidean distance is a positive integer.

How large can the chromatic number and clique number of G be? In particular,
can the chromatic number be infinite?

This statement is YES: there exists such a set A for which the
integer-distance graph has infinite chromatic number.

The Anning–Erdős theorem [AnEr45] shows that an infinite set of points in the plane with all
pairwise distances integers is collinear, so such a graph has no infinite complete subgraph
(`variants.no_infinite_clique`). It does not bound the sizes of the finite cliques.
-/
theorem erdos_problem_130 :
    ∃ (A : Set (EuclideanSpace ℝ (Fin 2))),
      A.Infinite ∧ ErdosGeneralPosition A ∧
      (intDistGraph A).chromaticNumber = ⊤ :=
  sorry

/--
The Anning–Erdős theorem [AnEr45] (PROVED): an infinite set of points in the plane, all of whose
pairwise distances are integers, is collinear.
-/
theorem erdos_problem_130.variants.anning_erdos
    (B : Set (EuclideanSpace ℝ (Fin 2))) (hB : B.Infinite)
    (hd : ∀ p ∈ B, ∀ q ∈ B, p ≠ q → ∃ n : ℕ, dist p q = n) :
    Collinear ℝ B :=
  sorry

/--
Erdős's question whether such a graph can contain an infinite complete graph, which the page
answers in the negative by [AnEr45] (PROVED in Lean from `anning_erdos`): in the integer-distance
graph of a set in general position, every clique is finite.
-/
theorem erdos_problem_130.variants.no_infinite_clique
    (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : ErdosGeneralPosition A)
    (B : Set ↥A) (hB : (intDistGraph A).IsClique B) : B.Finite := by
  by_contra hinf
  have hB'inf : (Subtype.val '' B).Infinite :=
    (Set.infinite_image_iff Subtype.val_injective.injOn).mpr hinf
  have hd : ∀ p ∈ Subtype.val '' B, ∀ q ∈ Subtype.val '' B, p ≠ q → ∃ n : ℕ, dist p q = n := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    have hne : x ≠ y := fun h => hxy (congrArg Subtype.val h)
    obtain ⟨_, n, _, hn⟩ := hB hx hy hne
    exact ⟨n, hn⟩
  have hcol := erdos_problem_130.variants.anning_erdos _ hB'inf hd
  obtain ⟨S, hSsub, hScard⟩ := hB'inf.exists_subset_card_eq 3
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hScard
  have hp : p ∈ Subtype.val '' B := hSsub (by simp)
  have hq : q ∈ Subtype.val '' B := hSsub (by simp)
  have hr : r ∈ Subtype.val '' B := hSsub (by simp)
  obtain ⟨x, _, rfl⟩ := hp
  obtain ⟨y, _, rfl⟩ := hq
  obtain ⟨z, _, rfl⟩ := hr
  refine hA.1 x y z x.2 y.2 z.2 hpq hpr hqr (Collinear.subset ?_ hcol)
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl
  · exact hSsub (by simp)
  · exact hSsub (by simp)
  · exact hSsub (by simp)
