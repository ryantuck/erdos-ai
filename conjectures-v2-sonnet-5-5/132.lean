-- [AI - Claude Sonnet 5.5]: Erdős Problem 132 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

open Classical

/-!
# Erdős Problem #132: Distances Occurring Between Few Pairs of Points

*Source:* [erdosproblems.com/132](https://www.erdosproblems.com/132) (banner **OPEN**, prize
**\$100**: "This is open, and cannot be resolved with a finite computation."; captured 2026-02-20
as the tidied problem box). [Er84c] [ErPa90] [ErFi95] [Er97b] [Er97e]

Let $A\subset \mathbb{R}^2$ be a set of $n$ points. Must there be two distances which occur at
least once but between at most $n$ pairs of points? Must the number of such distances
$\to \infty$ as $n\to \infty$?

Remarks recorded on the page:
* Asked by Erdős and Pach. Hopf and Pannowitz [HoPa34] proved that the largest distance between
  points of $A$ can occur at most $n$ times, but it is unknown whether a second such distance must
  occur. (The page's bibliography spells the name Pannwitz.)
* It may be true that there are at least $n^{1-o(1)}$ many such distances. In [Er97e] Erdős
  offers \$100 for 'any nontrivial result'.
* Erdős [Er84c] believed that for $n\geq 5$ there must always exist at least two such distances.
  This is false for $n=4$, as witnessed by two equilateral triangles of the same side-length
  glued together. Erdős and Fishburn [ErFi95] proved this is true for $n=5$ and $n=6$.
* Clemen, Dumitrescu, and Liu [CDL25] have proved that there always at least two such distances
  if $A$ is in convex position (that is, no point lies inside the convex hull of the others).
  They also prove it is true if the set $A$ is 'not too convex', in a specific technical sense.
* See also [223], [756], and [957].

Tags: distances. 2 comments at capture (not captured).

**Status.** OPEN, with a \$100 prize. The mirror (`teorth/erdosproblems`) has `open` (2025-08-31)
with prize \$100, and upstream has no `132.lean` at the pinned snapshot. The two theorems assert
the asked ("yes") directions, with $n\ge5$ in the first, the corpus convention while a problem is
open.

**What changed from the first pass.** The first pass counted *ordered* pairs and bounded the count
by $n$. "Between at most $n$ pairs of points" means at most $n$ *unordered* pairs, which is at most
$2n$ ordered pairs, and the Hopf–Pannwitz theorem is about unordered pairs, since the diameter graph
has at most $n$ edges. v2 changes the bound in `IsLimitedOccurrence` from `A.card` to `2 * A.card`.
`pairCount` is byte-identical and still counts ordered pairs. With the first pass's bound the first
theorem is false: the vertices of a square together with its centre are five points with exactly
one distance that occurs for at most $5$ ordered pairs. `variants.first_pass_part1_false` proves
this in Lean. The regular pentagon is another example: both of its distances occur for $5$
unordered pairs, so with the first pass's bound it has no limited distance at all, and the
Hopf–Pannwitz distance is not always limited, against the first pass's docstring.

**Encoding.**
* `pairCount A d` counts the ordered pairs $(x,y)$ with $x\ne y$ in `A` at distance `d`. Each
  unordered pair is counted twice, once in each order.
* `IsLimitedOccurrence A d` asks for at least one and at most $2|A|$ ordered pairs, which is between
  $1$ and $|A|$ unordered pairs. Since distinct points are at positive distance, `0 < pairCount A d`
  also forces $d>0$.
* `limitedOccurrences A` is a finite set of distances, so `Set.ncard` is exact.
* The page's first question has no restriction on $n$, but the answer is no for $n\le4$: for
  $n=4$ by the rhombus of two equilateral triangles, for $n\le3$ because an equilateral triangle,
  a segment or a point has at most one such distance. The first theorem takes $n\ge5$, as Erdős
  believed. The convex-position result of [CDL25] also needs $n\ge5$, since the $60^\circ$ rhombus
  is in convex position. The page's remark omits that.
* The second theorem says that the least number of limited distances over all sets of $n$ points
  tends to infinity.

## References

* [Er84c] Erdős, P., _Some old and new problems in combinatorial geometry_. Convexity and graph
  theory (Jerusalem, 1981) (1984), 129–136.
* [ErPa90] Erdős, P. and Pach, J., _Variations on the theme of repeated distances_. Combinatorica
  (1990), 261–269.
* [ErFi95] Erdős, P. and Fishburn, P. C., _Multiplicities of interpoint distances in finite
  planar sets_. Discrete Appl. Math. (1995), 141–147.
* [Er97b] Erdős, P., _Some old and new problems in various branches of combinatorics_. Discrete
  Math. (1997), 227–231.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997), 527–537.
* [HoPa34] Hopf, H. and Pannwitz, E., _Aufgabe 167_. Jahresbericht der Deutschen
  Mathematiker-Vereinigung (1934), 114.
* [CDL25] Clemen, F., Dumitrescu, A. and Liu, D., _On multiplicities of interpoint distances_.
  arXiv:2505.04283 (2025).

(Provenance: [Er84c], [Er97e], [ErFi95], [HoPa34] and [CDL25] are from the `/latex/132` fetch in
the session logs. [ErPa90] and [Er97b] are from the bibliographies of the `/latex` pages of other
problems.)
-/

/-- For a finite point set $A \subseteq \mathbb{R}^2$ and a real value $d$,
    the number of ordered pairs $(x, y)$ with $x \neq y$ in $A$ at
    Euclidean distance $d$. -/
noncomputable def pairCount (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card

/-- A distance $d$ is a *limited-occurrence distance* for $A$ if it is
    achieved by at least one but at most $2|A|$ ordered pairs of distinct
    points of $A$, that is, by between $1$ and $|A|$ unordered pairs. -/
def IsLimitedOccurrence (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : Prop :=
  0 < pairCount A d ∧ pairCount A d ≤ 2 * A.card

/-- The set of all limited-occurrence distances for $A$. -/
noncomputable def limitedOccurrences (A : Finset (EuclideanSpace ℝ (Fin 2))) : Set ℝ :=
  {d : ℝ | IsLimitedOccurrence A d}

/--
Erdős Problem #132, Part 1 [Er84c, ErPa90, ErFi95] — OPEN (prize $100):
For any set $A$ of $n \geq 5$ points in the plane $\mathbb{R}^2$, there
must exist at least two distinct limited-occurrence distances.
-/
theorem erdos_problem_132_part1 :
    ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), 5 ≤ A.card →
      2 ≤ Set.ncard (limitedOccurrences A) :=
  sorry

/--
Erdős Problem #132, Part 2 [Er84c, ErPa90] — OPEN (prize $100):
The number of limited-occurrence distances must tend to infinity with $n$.
For every $k$, there exists $N$ such that any set $A$ of at least $N$ points
in $\mathbb{R}^2$ has at least $k$ limited-occurrence distances.
-/
theorem erdos_problem_132_part2 :
    ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ A.card →
      k ≤ Set.ncard (limitedOccurrences A) :=
  sorry

/--
Hopf and Pannwitz [HoPa34] (PROVED, not checked here): the largest distance between points of $A$
occurs for at most $n$ unordered pairs, that is, at most $2n$ ordered pairs. So the largest
distance is always a limited-occurrence distance.
-/
theorem erdos_problem_132.variants.hopf_pannwitz
    (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ)
    (hmax : ∀ p ∈ A, ∀ q ∈ A, dist p q ≤ d) (hocc : 0 < pairCount A d) :
    pairCount A d ≤ 2 * A.card :=
  sorry

/--
Erdős and Fishburn [ErFi95] (PROVED, not checked here): a set of exactly $5$ or $6$ points in the
plane has at least two limited-occurrence distances.
-/
theorem erdos_problem_132.variants.erdos_fishburn
    (A : Finset (EuclideanSpace ℝ (Fin 2))) (hA : A.card = 5 ∨ A.card = 6) :
    2 ≤ Set.ncard (limitedOccurrences A) :=
  sorry

/--
Clemen, Dumitrescu and Liu [CDL25] (PROVED, not checked here): a set of $n\ge5$ points in convex
position, that is, with no point in the convex hull of the others, has at least two
limited-occurrence distances. The hypothesis $n\ge5$ is necessary: the rhombus of two equilateral
triangles is in convex position and has one such distance.
-/
theorem erdos_problem_132.variants.convex_position
    (A : Finset (EuclideanSpace ℝ (Fin 2))) (hA : 5 ≤ A.card)
    (hconv : ∀ p ∈ A, p ∉ convexHull ℝ (↑(A.erase p) : Set (EuclideanSpace ℝ (Fin 2)))) :
    2 ≤ Set.ncard (limitedOccurrences A) :=
  sorry

/--
The page's example showing that $n\ge5$ is needed (PROVED, elementary, not checked here): two
equilateral triangles of the same side length glued along an edge are four points with only one
limited-occurrence distance. The side occurs for $5$ unordered pairs, which is more than $4$, and the
long diagonal occurs once.
-/
theorem erdos_problem_132.variants.four_points :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = 4 ∧ Set.ncard (limitedOccurrences A) < 2 :=
  sorry

/--
The page's remark "it may be true that there are at least $n^{1-o(1)}$ many such distances"
(OPEN): for every $\varepsilon>0$ and all large $n$, every set of $n$ points has at least
$n^{1-\varepsilon}$ limited-occurrence distances. It implies Part 2.
-/
theorem erdos_problem_132.variants.n_one_minus_o_one :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ A.card →
      (A.card : ℝ) ^ ((1 : ℝ) - ε) ≤ (Set.ncard (limitedOccurrences A) : ℝ) :=
  sorry

/-! ### Machine-checked examples

The two examples below are five points (the vertices of a square and its centre) and four points
(two equilateral triangles glued along an edge). Both are handled by a table of squared
distances, which `decide` can count. -/

/-- If the squared distances of the points `P i` are the natural numbers `D i j`, then the number of
ordered pairs at distance `√m` is the number of index pairs with `D i j = m`. -/
theorem erdos_problem_132.pairCount_table {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin 2))
    (D : Fin n → Fin n → ℕ) (hD : ∀ i j, dist (P i) (P j) = Real.sqrt (D i j))
    (hDne : ∀ i j, i ≠ j → D i j ≠ 0) (m : ℕ) :
    pairCount (Finset.univ.image P) (Real.sqrt m) =
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2 ∧ D p.1 p.2 = m)).card := by
  have hinj : Function.Injective P := by
    intro i j h
    by_contra hne
    have h0 : dist (P i) (P j) = 0 := by rw [h]; exact dist_self _
    rw [hD] at h0
    have h1 : ((D i j : ℕ) : ℝ) ≤ 0 := Real.sqrt_eq_zero'.mp h0
    have h2 : D i j = 0 := by
      have := le_antisymm h1 (Nat.cast_nonneg _)
      exact_mod_cast this
    exact hDne i j hne h2
  unfold pairCount
  symm
  apply Finset.card_bij (fun p _ => (P p.1, P p.2))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨⟨p.1, rfl⟩, ⟨p.2, rfl⟩⟩, fun h => hp.1 (hinj h), ?_⟩
    rw [hD]
    rw [hp.2]
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (hinj h.1) (hinj h.2)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Finset.mem_univ,
      true_and] at hq
    obtain ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hne, hd⟩ := hq
    refine ⟨(i, j), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun h => hne (by rw [← hi, ← hj, h]), ?_⟩
      rw [← hi, ← hj, hD] at hd
      have := (Real.sqrt_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mp hd
      exact_mod_cast this
    · simp [hi, hj]

/-- `√4 = 2`, used in the distance tables. -/
theorem erdos_problem_132.sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- The vertices of a square of side $2$ and its centre. -/
noncomputable def squareCentre : Fin 5 → EuclideanSpace ℝ (Fin 2) :=
  ![!₂[0, 0], !₂[2, 0], !₂[0, 2], !₂[2, 2], !₂[1, 1]]

/-- The squared distances between the five points of `squareCentre`. -/
def squareCentreD : Fin 5 → Fin 5 → ℕ :=
  ![![0, 4, 4, 8, 2], ![4, 0, 8, 4, 2], ![4, 8, 0, 4, 2], ![8, 4, 4, 0, 2], ![2, 2, 2, 2, 0]]

/-- The distances between the points of `squareCentre` are the square roots of the table
`squareCentreD`. -/
theorem erdos_problem_132.squareCentre_dist (i j : Fin 5) :
    dist (squareCentre i) (squareCentre j) = Real.sqrt (squareCentreD i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [squareCentre, squareCentreD, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq,
      erdos_problem_132.sqrt_four] <;> norm_num [erdos_problem_132.sqrt_four]

/--
The first pass's bound counted the ordered pairs at a distance against $n$, instead of against
$2n$. With that bound the first theorem is false (PROVED in Lean): the vertices of a square and its
centre are five points, and only the distance between opposite corners occurs for at most $5$
ordered pairs. The distances $2$ and $\sqrt2$ occur for $8$ ordered pairs each.
-/
theorem erdos_problem_132.variants.first_pass_part1_false :
    ¬ (∀ A : Finset (EuclideanSpace ℝ (Fin 2)), 5 ≤ A.card →
        2 ≤ Set.ncard {d : ℝ | 0 < pairCount A d ∧ pairCount A d ≤ A.card}) := by
  intro h
  have hne : ∀ i j : Fin 5, i ≠ j → squareCentreD i j ≠ 0 := by decide
  have hcard : (Finset.univ.image squareCentre).card = 5 := by
    have hinj : Function.Injective squareCentre := by
      intro i j hij
      by_contra hn
      have h0 : dist (squareCentre i) (squareCentre j) = 0 := by rw [hij]; exact dist_self _
      rw [erdos_problem_132.squareCentre_dist] at h0
      have h1 : ((squareCentreD i j : ℕ) : ℝ) ≤ 0 := Real.sqrt_eq_zero'.mp h0
      have h2 : squareCentreD i j = 0 := by
        have := le_antisymm h1 (Nat.cast_nonneg _)
        exact_mod_cast this
      exact hne i j hn h2
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have h5 := h (Finset.univ.image squareCentre) (by rw [hcard])
  have hsub : {d : ℝ | 0 < pairCount (Finset.univ.image squareCentre) d ∧
      pairCount (Finset.univ.image squareCentre) d ≤ (Finset.univ.image squareCentre).card} ⊆
      {Real.sqrt 8} := by
    intro d hd
    obtain ⟨h0, h1⟩ := hd
    rw [hcard] at h1
    -- some pair of distinct points realizes d
    have hpos := h0
    unfold pairCount at hpos
    obtain ⟨⟨a, b⟩, hp⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, Finset.mem_univ,
      true_and] at hp
    obtain ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, hij, hd'⟩ := hp
    have hij' : i ≠ j := fun h => hij (by simp [← hi, ← hj, h])
    have hvals : ∀ i j : Fin 5, i ≠ j →
        squareCentreD i j = 2 ∨ squareCentreD i j = 4 ∨ squareCentreD i j = 8 := by decide
    have hdist : d = Real.sqrt (squareCentreD i j) := by
      rw [← hd', ← hi, ← hj, erdos_problem_132.squareCentre_dist]
    rcases hvals i j hij' with h2 | h2 | h2
    · exfalso
      have hd2 : d = Real.sqrt ((2 : ℕ) : ℝ) := by rw [hdist, h2]
      rw [hd2, erdos_problem_132.pairCount_table squareCentre squareCentreD
        erdos_problem_132.squareCentre_dist hne] at h1
      have : ((Finset.univ : Finset (Fin 5 × Fin 5)).filter
          (fun p => p.1 ≠ p.2 ∧ squareCentreD p.1 p.2 = 2)).card = 8 := by decide
      omega
    · exfalso
      have hd2 : d = Real.sqrt ((4 : ℕ) : ℝ) := by rw [hdist, h2]
      rw [hd2, erdos_problem_132.pairCount_table squareCentre squareCentreD
        erdos_problem_132.squareCentre_dist hne] at h1
      have : ((Finset.univ : Finset (Fin 5 × Fin 5)).filter
          (fun p => p.1 ≠ p.2 ∧ squareCentreD p.1 p.2 = 4)).card = 8 := by decide
      omega
    · rw [Set.mem_singleton_iff, hdist, h2]
      norm_num
  have hle := Set.ncard_le_ncard hsub (Set.finite_singleton _)
  rw [Set.ncard_singleton] at hle
  omega
