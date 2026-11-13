-- [AI - Claude Fable 5.2]: Erdős Problem 210 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem #210

*Source:* [erdosproblems.com/210](https://www.erdosproblems.com/210) (status **PROVED**: "This has
been solved in the affirmative."; captured 2026-02-20; page last edited 16 October 2025).
[Er61, p.245] [Er75f, p.105] [Er81] [Er83c] [Er84] [Er85]

Let $f(n)$ be minimal such that the following holds. For any $n$ points in $\mathbb{R}^2$, not all
on a line, there must be at least $f(n)$ many lines which contain exactly 2 points (called
'ordinary lines'). Does $f(n)\to \infty$? How fast?

Remarks recorded on the page: conjectured by Erdős and de Bruijn. The Sylvester-Gallai theorem
states that $f(n)\geq 1$. The fact that $f(n)\geq 1$ was conjectured by Sylvester in 1893. Erdős
rediscovered this conjecture in 1933 and told it to Gallai who proved it. That $f(n)\to \infty$
was proved by Motzkin [Mo51]. Kelly and Moser [KeMo58] proved that $f(n)\geq\tfrac{3}{7}n$ for all
$n$. This is best possible for $n=7$. Motzkin conjectured that for $n\geq 13$ there are at least
$n/2$ such lines. Csima and Sawyer [CsSa93] proved a lower bound of $f(n)\geq \tfrac{6}{13}n$ when
$n\geq 8$. Green and Tao [GrTa13] proved that $f(n)\geq n/2$ for sufficiently large $n$. (A proof
that $f(n)\geq n/2$ for large $n$ was earlier claimed by Hansen but this proof was flawed.) The
bound of $n/2$ is best possible for even $n$, since one could take $n/2$ points on a circle and
$n/2$ points at infinity. Surprisingly, Green and Tao [GrTa13] show that if $n$ is odd (and
sufficiently large) then $f(n)\geq 3\lfloor n/4\rfloor$. OEIS A003034.

## Status

PROVED at capture and in the metadata mirror `teorth/erdosproblems` (`641a78e`, 2026-11-12; no
Lean proof recorded). Upstream `formal-conjectures` (`5258ab9`) states Motzkin's theorem as the
answer to the first question and the Green–Tao bound as `n ≤ 2 * f n`.

## Changes from the input

* **Defect fixed.** The input's conclusion is `ordinaryLineCount_210 S ≥ S.card / 2` with ℕ
  division, that is, at least `⌊n/2⌋` ordinary lines; for odd `n` this is one less than the
  page's `f(n) ≥ n/2`. The conclusion is now `S.card ≤ 2 * ordinaryLineCount_210 S`. The input's
  form follows (`erdos_problem_210.floor_form_of_main`, PROVED in Lean).

## Encoding notes

* The theorem states the Green–Tao bound, the strongest recorded answer to "how fast?". The first
  question (Motzkin's theorem) is `variants.motzkin`; it follows from the Kelly–Moser bound
  (`variants.motzkin_of_kelly_moser`, PROVED in Lean).
* `ordinaryLineCount_210` counts ordered ordinary pairs and halves. The halving is exact: the set
  of ordered ordinary pairs is closed under swapping and has no fixed point, so its cardinality is
  even (`even_card_ordinaryPairs`, `two_mul_ordinaryLineCount`, PROVED in Lean).
* `NotAllCollinear_210 S` needs three distinct points, so `S.card ≥ 3` (`three_le_card`, PROVED).
* The docstring of the input credits Green and Tao with "resolving the conjecture of Erdős and de
  Bruijn". On the page the conjecture of Erdős and de Bruijn is the problem itself (`f(n) → ∞`,
  proved by Motzkin); the bound `n/2` is the conjecture the page attributes to Motzkin. The
  docstring below is corrected.

## References

From the site's `/latex/210` bibliography:
* [CsSa93] Csima, J. and Sawyer, E. T., _There exist 6n/13 ordinary points_. Discrete Comput. Geom.
  (1993), 187–202.
* [GrTa13] Green, Ben and Tao, Terence, _On sets defining few ordinary lines_. Discrete Comput.
  Geom. (2013), 409–468.
* [KeMo58] Kelly, L. M. and Moser, W. O. J., _On the number of ordinary lines determined by n
  points_. Canad. J. Math. (1958), 210–219.
* [Mo51] Motzkin, Th., _The lines and planes connecting the points of a finite set_. Trans. Amer.
  Math. Soc. (1951), 451–464.

From other problems' site bibliographies (the heading keys are not in `/latex/210`):
* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221–254. (Site `/latex/511` and others.) The page cites p. 245.
* [Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_. Ann. Mat. Pura
  Appl. (4) (1975), 99–108. (Site `/latex/1090` and others.) The page cites p. 105.
* [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25–42. (Site `/latex/19` and others.)
* [Er83c] Erdős, P., _Combinatorial problems in geometry_. Math. Chronicle (1983), 35–54. (Site
  `/latex/217`.)
* [Er84] Erdős, P., _Research problems_. Period. Math. Hungar. (1984), 101–103. (Site
  `/latex/211`.)
* [Er85] Erdős, P., _Problems and results in combinatorial geometry_. Discrete geometry and
  convexity (New York, 1982) (1985), 1–11. (**DEFERRED:** from upstream's files; no site entry was
  recovered.)

*Provenance:* second pass of `conjectures/210.lean` (Fable 5.2 review,
`fable-5-2-review/210.md`).
-/

noncomputable section
open Classical

/-- Points in the Euclidean plane ℝ² -/
abbrev Point2_210 := EuclideanSpace ℝ (Fin 2)

/-- Point r lies on the line through distinct points p and q -/
def LiesOnLine_210 (p q r : Point2_210) : Prop :=
  ∃ t : ℝ, r - p = t • (q - p)

/-- A finite set of points is not all collinear: there exist three
    non-collinear points in S -/
def NotAllCollinear_210 (S : Finset Point2_210) : Prop :=
  ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S, p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ ¬LiesOnLine_210 p q r

/-- An ordered pair (p, q) determines an ordinary line for S if p ≠ q,
    both lie in S, and no third point of S lies on the line through p and q -/
def IsOrdinaryPair_210 (S : Finset Point2_210) (p q : Point2_210) : Prop :=
  p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ ∀ r ∈ S, r ≠ p → r ≠ q → ¬LiesOnLine_210 p q r

/-- The number of ordinary lines determined by S.
    Counts ordered pairs forming ordinary lines and divides by 2. -/
noncomputable def ordinaryLineCount_210 (S : Finset Point2_210) : ℕ :=
  ((S ×ˢ S).filter (fun pq => IsOrdinaryPair_210 S pq.1 pq.2)).card / 2

/--
Erdős Problem #210 (Proved by Green-Tao)
[Er61, Er75f, Er81, Er83c, Er84, Er85]:
Let f(n) be minimal such that for any n points in ℝ², not all on a line,
there are at least f(n) ordinary lines (lines containing exactly 2 of the
points). Does f(n) → ∞? How fast?

Green and Tao [GrTa13] proved that f(n) ≥ n/2 for all sufficiently large n, as Motzkin had
conjectured, strengthening earlier results of Motzkin [Mo51] (f(n) → ∞, the conjecture of Erdős
and de Bruijn), Kelly-Moser [KeMo58] (f(n) ≥ 3n/7), and Csima-Sawyer [CsSa93] (f(n) ≥ 6n/13).

Second pass: the bound is stated as `n ≤ 2 f`, not with the ℕ quotient `n / 2`. Not proved here.
-/
theorem erdos_problem_210 :
    ∃ N₀ : ℕ, ∀ (S : Finset Point2_210),
      S.card ≥ N₀ →
      NotAllCollinear_210 S →
      S.card ≤ 2 * ordinaryLineCount_210 S :=
  sorry

/-- The main statement implies the input's statement, with the ℕ quotient `S.card / 2`
(PROVED in Lean). The converse fails for odd cardinalities. -/
theorem erdos_problem_210.floor_form_of_main
    (h : ∃ N₀ : ℕ, ∀ (S : Finset Point2_210),
      S.card ≥ N₀ → NotAllCollinear_210 S → S.card ≤ 2 * ordinaryLineCount_210 S) :
    ∃ N₀ : ℕ, ∀ (S : Finset Point2_210),
      S.card ≥ N₀ →
      NotAllCollinear_210 S →
      ordinaryLineCount_210 S ≥ S.card / 2 := by
  obtain ⟨N₀, hN₀⟩ := h
  refine ⟨N₀, fun S hS hnc => ?_⟩
  have := hN₀ S hS hnc
  omega

/-- `LiesOnLine_210 p q r` is symmetric in `p` and `q` (PROVED in Lean): if `r - p = t (q - p)`
then `r - q = (1 - t) (p - q)`. -/
theorem LiesOnLine_210.symm {p q r : Point2_210} (h : LiesOnLine_210 p q r) :
    LiesOnLine_210 q p r := by
  obtain ⟨t, ht⟩ := h
  refine ⟨1 - t, ?_⟩
  have hr : r = t • (q - p) + p := eq_add_of_sub_eq ht
  rw [hr]
  simp only [sub_smul, smul_sub, one_smul]
  abel

/-- `IsOrdinaryPair_210 S p q` is symmetric in `p` and `q` (PROVED in Lean). -/
theorem IsOrdinaryPair_210.symm {S : Finset Point2_210} {p q : Point2_210}
    (h : IsOrdinaryPair_210 S p q) : IsOrdinaryPair_210 S q p :=
  ⟨h.2.1, h.1, h.2.2.1.symm, fun r hr hrq hrp hl => h.2.2.2 r hr hrp hrq hl.symm⟩

/-- The number of ordered ordinary pairs is even (PROVED in Lean): swapping the two points is an
involution of the set of ordered ordinary pairs without fixed points. -/
theorem erdos_problem_210.even_card_ordinaryPairs (S : Finset Point2_210) :
    Even ((S ×ˢ S).filter (fun pq => IsOrdinaryPair_210 S pq.1 pq.2)).card := by
  rw [← ZMod.natCast_eq_zero_iff_even]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h := Finset.sum_involution
    (s := (S ×ˢ S).filter (fun pq => IsOrdinaryPair_210 S pq.1 pq.2))
    (f := fun _ => (1 : ZMod 2)) (fun pq _ => (pq.2, pq.1))
    (fun _ _ => h11)
    (fun pq hpq _ heq => (Finset.mem_filter.1 hpq).2.2.2.1 (congrArg Prod.fst heq).symm)
    (fun pq hpq => Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨(Finset.mem_filter.1 hpq).2.2.1, (Finset.mem_filter.1 hpq).2.1⟩,
        (Finset.mem_filter.1 hpq).2.symm⟩)
    (fun _ _ => rfl)
  simpa using h

/-- The halving in `ordinaryLineCount_210` is exact (PROVED in Lean). -/
theorem erdos_problem_210.two_mul_ordinaryLineCount (S : Finset Point2_210) :
    2 * ordinaryLineCount_210 S =
      ((S ×ˢ S).filter (fun pq => IsOrdinaryPair_210 S pq.1 pq.2)).card :=
  Nat.two_mul_div_two_of_even (erdos_problem_210.even_card_ordinaryPairs S)

/-- A set that is not all collinear has at least three points (PROVED in Lean). -/
theorem erdos_problem_210.three_le_card {S : Finset Point2_210} (h : NotAllCollinear_210 S) :
    3 ≤ S.card := by
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr, -⟩ := h
  have hsub : ({p, q, r} : Finset Point2_210) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : ({p, q, r} : Finset Point2_210).card = 3 :=
    Finset.card_eq_three.2 ⟨p, q, r, hpq, hpr, hqr, rfl⟩
  have := Finset.card_le_card hsub
  omega

/-- The Sylvester–Gallai theorem, `f(n) ≥ 1` (SOLVED; not proved here). -/
theorem erdos_problem_210.variants.sylvester_gallai :
    ∀ (S : Finset Point2_210), NotAllCollinear_210 S → 1 ≤ ordinaryLineCount_210 S :=
  sorry

/-- The page's first question, `f(n) → ∞`, proved by Motzkin [Mo51] (SOLVED; not proved here). -/
theorem erdos_problem_210.variants.motzkin :
    ∀ K : ℕ, ∃ N₀ : ℕ, ∀ (S : Finset Point2_210),
      S.card ≥ N₀ → NotAllCollinear_210 S → K ≤ ordinaryLineCount_210 S :=
  sorry

/-- Kelly and Moser [KeMo58], `f(n) ≥ 3n/7` for all `n` (SOLVED; not proved here). -/
theorem erdos_problem_210.variants.kelly_moser :
    ∀ (S : Finset Point2_210), NotAllCollinear_210 S →
      3 * S.card ≤ 7 * ordinaryLineCount_210 S :=
  sorry

/-- Motzkin's theorem follows from the Kelly–Moser bound (PROVED in Lean, from the bound as a
hypothesis). -/
theorem erdos_problem_210.variants.motzkin_of_kelly_moser
    (hKM : ∀ (S : Finset Point2_210), NotAllCollinear_210 S →
      3 * S.card ≤ 7 * ordinaryLineCount_210 S) :
    ∀ K : ℕ, ∃ N₀ : ℕ, ∀ (S : Finset Point2_210),
      S.card ≥ N₀ → NotAllCollinear_210 S → K ≤ ordinaryLineCount_210 S := by
  intro K
  refine ⟨3 * K, fun S hS hnc => ?_⟩
  have := hKM S hnc
  omega

/-- Csima and Sawyer [CsSa93], `f(n) ≥ 6n/13` for `n ≥ 8` (SOLVED; not proved here). -/
theorem erdos_problem_210.variants.csima_sawyer :
    ∀ (S : Finset Point2_210), 8 ≤ S.card → NotAllCollinear_210 S →
      6 * S.card ≤ 13 * ordinaryLineCount_210 S :=
  sorry

/-- Green and Tao [GrTa13] for odd `n` (SOLVED; not proved here): `f(n) ≥ 3⌊n/4⌋` for all large
odd `n`. Here the ℕ quotient `S.card / 4` is the intended floor. -/
theorem erdos_problem_210.variants.green_tao_odd :
    ∃ N₀ : ℕ, ∀ (S : Finset Point2_210),
      S.card ≥ N₀ → Odd S.card → NotAllCollinear_210 S →
      3 * (S.card / 4) ≤ ordinaryLineCount_210 S :=
  sorry

/-- The bound `n/2` is best possible for even `n` (SOLVED per the page; not proved here): for all
large even `n` some set of `n` points, not all on a line, has at most `n/2` ordinary lines. The page
says "for even `n`" without a threshold; "all large even `n`" is the form used here. -/
theorem erdos_problem_210.variants.even_sharp :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∃ S : Finset Point2_210, S.card = n ∧ NotAllCollinear_210 S ∧
        2 * ordinaryLineCount_210 S ≤ n :=
  sorry

end
