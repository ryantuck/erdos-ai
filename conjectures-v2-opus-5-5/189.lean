-- [AI - Claude Opus 5.5]: Erdős Problem 189 — second-pass formalization
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Erdős Problem #189

*Source:* [erdosproblems.com/189](https://www.erdosproblems.com/189) (status **DISPROVED (LEAN)**:
"This has been solved in the negative and the proof verified in Lean."; captured 2026-03-05).
[ErGr79] [ErGr80]

If $\mathbb{R}^2$ is finitely coloured then must there exist some colour class which contains the
vertices of a rectangle of every area?

Remarks recorded on the page (abridged): Graham [Gr80] has shown that this is true if we replace
rectangle by right-angled triangle. The same question can be asked for parallelograms. It is not
true for rhombuses. This is false; Kovač [Ko23] provides an explicit (and elegantly simple)
colouring using 25 colours such that no colour class contains the vertices of a rectangle of area
$1$. The question for parallelograms remains open. This problem has been formalised in Lean as
part of the Google DeepMind Formal Conjectures project.

## The defect and its fix

The input asserted the "yes" answer, although the page (and the input's own docstring) record that
the answer is no. v2 replaces the theorem by its negation and **proves it in Lean**, with the input's
own definitions `IsRectangle` and `RectangleArea`.

The proof uses a 25-colouring of the same kind as Kovač's. For $z=x+iy$ let
$q_1=\operatorname{Re}z^2=x^2-y^2$ and $q_2=\operatorname{Im}z^2=2xy$, and colour $z$ by
$\lfloor q_1/s\rfloor$ and $\lfloor q_2/s\rfloor$ modulo $5$, with $s=7/10$.

* For a rectangle $A,B,C,D$ with $C=B+D-A$, the alternating sums
  $\Delta_j=q_j(A)-q_j(B)+q_j(C)-q_j(D)$ satisfy $\Delta_1^2+\Delta_2^2=4\,\mathrm{area}^2$
  (because $AB\perp AD$).
* If the four vertices have one colour, each $\Delta_j$ is $s(5m_j+\rho_j)$ with $m_j\in\mathbb Z$ and
  $|\rho_j|<2$. If $m_1=m_2=0$ then $\Delta_1^2+\Delta_2^2<8s^2<4$; otherwise some
  $\Delta_j^2>9s^2>4$. Either way the area is not $1$.

## References

No `/latex/189` fetch is in the session logs.
* [Ko23] Kovač, V., _Coloring and density theorems for configurations of a given volume_.
  arXiv:2309.09973 (2023). (From upstream `formal-conjectures`, `2befc3a`; **DEFERRED** as a site
  entry.)
* [Gr80] Graham, R. L., _On partitions of $\mathbb E^n$_. J. Combin. Theory Ser. A 28 (1980),
  89–91. (From upstream; **DEFERRED** as a site entry.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171.)

*Provenance:* second pass of `conjectures/189.lean` (Opus 5.5 review, `opus-5-5-review/189.md`).
-/

/--
Four points A, B, C, D in ℝ² form a (nondegenerate) rectangle if:
- ABCD is a parallelogram: C = B + D - A,
- adjacent sides are perpendicular: (B - A) · (D - A) = 0,
- and the rectangle is nondegenerate: A ≠ B and A ≠ D.
-/
def IsRectangle (A B C D : ℝ × ℝ) : Prop :=
  C = (B.1 + D.1 - A.1, B.2 + D.2 - A.2) ∧
  (B.1 - A.1) * (D.1 - A.1) + (B.2 - A.2) * (D.2 - A.2) = 0 ∧
  A ≠ B ∧ A ≠ D

/--
The area of a rectangle with vertex A and adjacent vertices B, D
(where AB ⊥ AD) is the absolute value of the cross product of the
two edge vectors, |AB × AD| = |(B₁-A₁)(D₂-A₂) - (B₂-A₂)(D₁-A₁)|.
-/
noncomputable def RectangleArea (A B D : ℝ × ℝ) : ℝ :=
  |(B.1 - A.1) * (D.2 - A.2) - (B.2 - A.2) * (D.1 - A.1)|

/-- $\operatorname{Re}z^2=x^2-y^2$ for $z=x+iy$. -/
def q1_189 (p : ℝ × ℝ) : ℝ := p.1 ^ 2 - p.2 ^ 2

/-- $\operatorname{Im}z^2=2xy$ for $z=x+iy$. -/
def q2_189 (p : ℝ × ℝ) : ℝ := 2 * p.1 * p.2

/-- An enumeration of the 25 colours. -/
noncomputable def colourEquiv189 : ZMod 5 × ZMod 5 ≃ Fin 25 :=
  Fintype.equivFinOfCardEq (by simp [ZMod.card])

/-- A 25-colouring of the plane of Kovač's kind: $z$ is coloured by $\lfloor q_1(z)/s\rfloor$ and
$\lfloor q_2(z)/s\rfloor$ modulo `5`, with $s=7/10$. -/
noncomputable def colouring189 (p : ℝ × ℝ) : Fin 25 :=
  colourEquiv189 ((⌊q1_189 p / (7 / 10)⌋ : ZMod 5), (⌊q2_189 p / (7 / 10)⌋ : ZMod 5))

/-- Equal colours give floors congruent modulo `5` (PROVED in Lean). -/
theorem erdos_problem_189.dvd_of_colour_eq {p p' : ℝ × ℝ}
    (h : colouring189 p' = colouring189 p) :
    (5 : ℤ) ∣ ⌊q1_189 p' / (7 / 10)⌋ - ⌊q1_189 p / (7 / 10)⌋ ∧
      (5 : ℤ) ∣ ⌊q2_189 p' / (7 / 10)⌋ - ⌊q2_189 p / (7 / 10)⌋ := by
  have h' := colourEquiv189.injective h
  simp only [Prod.mk.injEq] at h'
  have h1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 5).1 h'.1.symm
  have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 5).1 h'.2.symm
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- If `b, c, d` have floors (after dividing by `s`) congruent to that of `a` modulo `5`, then
`a - b + c - d = s (5m + ρ)` with `m ∈ ℤ` and `|ρ| < 2` (PROVED in Lean). -/
theorem erdos_problem_189.alt_sum {a b c d s : ℝ} (hs : 0 < s)
    (hb : (5 : ℤ) ∣ ⌊b / s⌋ - ⌊a / s⌋) (hc : (5 : ℤ) ∣ ⌊c / s⌋ - ⌊a / s⌋)
    (hd : (5 : ℤ) ∣ ⌊d / s⌋ - ⌊a / s⌋) :
    ∃ m : ℤ, ∃ ρ : ℝ, -2 < ρ ∧ ρ < 2 ∧ a - b + c - d = s * (5 * m + ρ) := by
  obtain ⟨mb, hmb⟩ := hb
  obtain ⟨mc, hmc⟩ := hc
  obtain ⟨md, hmd⟩ := hd
  have hmb' : (⌊b / s⌋ : ℝ) - ⌊a / s⌋ = 5 * mb := by exact_mod_cast hmb
  have hmc' : (⌊c / s⌋ : ℝ) - ⌊a / s⌋ = 5 * mc := by exact_mod_cast hmc
  have hmd' : (⌊d / s⌋ : ℝ) - ⌊a / s⌋ = 5 * md := by exact_mod_cast hmd
  have fa := Int.floor_le (a / s)
  have ga := Int.lt_floor_add_one (a / s)
  have fb := Int.floor_le (b / s)
  have gb := Int.lt_floor_add_one (b / s)
  have fc := Int.floor_le (c / s)
  have gc := Int.lt_floor_add_one (c / s)
  have fd := Int.floor_le (d / s)
  have gd := Int.lt_floor_add_one (d / s)
  refine ⟨-mb + mc - md,
    (a / s - ⌊a / s⌋) - (b / s - ⌊b / s⌋) + (c / s - ⌊c / s⌋) - (d / s - ⌊d / s⌋),
    by linarith, by linarith, ?_⟩
  push_cast
  have hfl : (5 : ℝ) * (-(mb : ℝ) + mc - md) =
      -((⌊b / s⌋ : ℝ) - ⌊a / s⌋) + ((⌊c / s⌋ : ℝ) - ⌊a / s⌋) - ((⌊d / s⌋ : ℝ) - ⌊a / s⌋) := by
    rw [hmb', hmc', hmd']
    ring
  rw [hfl]
  field_simp
  ring

/-- A nonzero integer `m` and `|ρ| < 2` give `(5m + ρ)² > 9` (PROVED in Lean). -/
theorem erdos_problem_189.nine_lt_sq {m : ℤ} {ρ : ℝ} (h1 : -2 < ρ) (h2 : ρ < 2) (hm : m ≠ 0) :
    9 < (5 * (m : ℝ) + ρ) ^ 2 := by
  rcases lt_or_gt_of_ne hm with h | h
  · have hm' : m ≤ -1 := by omega
    have : (m : ℝ) ≤ -1 := by exact_mod_cast hm'
    nlinarith
  · have hm' : 1 ≤ m := by omega
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm'
    nlinarith

/-- No colour class of `colouring189` contains the vertices of a rectangle of area `1` (PROVED in
Lean). -/
theorem erdos_problem_189.no_monochromatic_unit_rectangle {A B C D : ℝ × ℝ}
    (hB : colouring189 B = colouring189 A) (hC : colouring189 C = colouring189 A)
    (hD : colouring189 D = colouring189 A) (hrect : IsRectangle A B C D)
    (harea : RectangleArea A B D = 1) : False := by
  obtain ⟨hCdef, hperp, -, -⟩ := hrect
  have hid1 : q1_189 A - q1_189 B + q1_189 C - q1_189 D =
      2 * ((B.1 - A.1) * (D.1 - A.1) - (B.2 - A.2) * (D.2 - A.2)) := by
    rw [hCdef]
    simp only [q1_189]
    ring
  have hid2 : q2_189 A - q2_189 B + q2_189 C - q2_189 D =
      2 * ((B.1 - A.1) * (D.2 - A.2) + (B.2 - A.2) * (D.1 - A.1)) := by
    rw [hCdef]
    simp only [q2_189]
    ring
  have hcross : ((B.1 - A.1) * (D.2 - A.2) - (B.2 - A.2) * (D.1 - A.1)) ^ 2 = 1 := by
    unfold RectangleArea at harea
    rw [← sq_abs, harea]
    norm_num
  have hsum : (q1_189 A - q1_189 B + q1_189 C - q1_189 D) ^ 2 +
      (q2_189 A - q2_189 B + q2_189 C - q2_189 D) ^ 2 = 4 := by
    rw [hid1, hid2]
    linear_combination 4 * hcross +
      4 * ((B.1 - A.1) * (D.1 - A.1) + (B.2 - A.2) * (D.2 - A.2)) * hperp
  obtain ⟨hB1, hB2⟩ := erdos_problem_189.dvd_of_colour_eq hB
  obtain ⟨hC1, hC2⟩ := erdos_problem_189.dvd_of_colour_eq hC
  obtain ⟨hD1, hD2⟩ := erdos_problem_189.dvd_of_colour_eq hD
  have hs : (0 : ℝ) < 7 / 10 := by norm_num
  obtain ⟨m1, ρ1, h1l, h1u, h1⟩ := erdos_problem_189.alt_sum hs hB1 hC1 hD1
  obtain ⟨m2, ρ2, h2l, h2u, h2⟩ := erdos_problem_189.alt_sum hs hB2 hC2 hD2
  rw [h1, h2] at hsum
  have key : 49 / 100 * (5 * (m1 : ℝ) + ρ1) ^ 2 + 49 / 100 * (5 * (m2 : ℝ) + ρ2) ^ 2 = 4 := by
    linear_combination hsum
  by_cases hm1 : m1 = 0
  · by_cases hm2 : m2 = 0
    · subst hm1
      subst hm2
      simp only [Int.cast_zero, mul_zero, zero_add] at key
      nlinarith [mul_pos (by linarith : (0 : ℝ) < ρ1 + 2) (by linarith : (0 : ℝ) < 2 - ρ1),
        mul_pos (by linarith : (0 : ℝ) < ρ2 + 2) (by linarith : (0 : ℝ) < 2 - ρ2)]
    · have := erdos_problem_189.nine_lt_sq h2l h2u hm2
      nlinarith [sq_nonneg (5 * (m1 : ℝ) + ρ1)]
  · have := erdos_problem_189.nine_lt_sq h1l h1u hm1
    nlinarith [sq_nonneg (5 * (m2 : ℝ) + ρ2)]

/--
Erdős Problem #189 [ErGr79, ErGr80], with the answer recorded on the page: **no**.

There is a finite colouring of ℝ² (25 colours) in which no colour class contains the vertices of a
rectangle of every area: no class contains a rectangle of area `1`. (Status: DISPROVED (LEAN) on the
page [Ko23]; the negation is PROVED here in Lean.)
-/
theorem erdos_problem_189 :
    ¬ ∀ (k : ℕ) (f : ℝ × ℝ → Fin k),
      ∃ c : Fin k, ∀ t : ℝ, 0 < t →
        ∃ A B C D : ℝ × ℝ,
          f A = c ∧ f B = c ∧ f C = c ∧ f D = c ∧
          IsRectangle A B C D ∧
          RectangleArea A B D = t := by
  intro h
  obtain ⟨c, hc⟩ := h 25 colouring189
  obtain ⟨A, B, C, D, hA, hB, hC, hD, hrect, harea⟩ := hc 1 one_pos
  exact erdos_problem_189.no_monochromatic_unit_rectangle (hB.trans hA.symm)
    (hC.trans hA.symm) (hD.trans hA.symm) hrect harea

/-- Graham's theorem [Gr80] (SOLVED; not proved here): with "rectangle" replaced by "right-angled
triangle" the answer is yes. -/
theorem erdos_problem_189.variants.graham_right_triangles :
    ∀ (k : ℕ) (f : ℝ × ℝ → Fin k),
      ∃ c : Fin k, ∀ t : ℝ, 0 < t →
        ∃ A B D : ℝ × ℝ, f A = c ∧ f B = c ∧ f D = c ∧
          (B.1 - A.1) * (D.1 - A.1) + (B.2 - A.2) * (D.2 - A.2) = 0 ∧ A ≠ B ∧ A ≠ D ∧
          RectangleArea A B D / 2 = t :=
  sorry

/-- The page's parallelogram question (OPEN, asserted in the "yes" direction): some colour class
contains the vertices of a parallelogram of every area. -/
theorem erdos_problem_189.variants.parallelogram :
    ∀ (k : ℕ) (f : ℝ × ℝ → Fin k),
      ∃ c : Fin k, ∀ t : ℝ, 0 < t →
        ∃ A B C D : ℝ × ℝ,
          f A = c ∧ f B = c ∧ f C = c ∧ f D = c ∧
          C = (B.1 + D.1 - A.1, B.2 + D.2 - A.2) ∧
          RectangleArea A B D = t :=
  sorry
