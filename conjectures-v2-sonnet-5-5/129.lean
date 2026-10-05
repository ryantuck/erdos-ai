-- [AI - Claude Sonnet 5.5]: Erdős Problem 129 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

/-!
# Erdős Problem #129: A Multicolour Ramsey Variant

*Source:* [erdosproblems.com/129](https://www.erdosproblems.com/129) (banner **OPEN**: "This is
open, and cannot be resolved with a finite computation."; captured 2026-02-20 as the tidied
problem box). [Er97b]

Let $R(n;k,r)$ be the smallest $N$ such that if the edges of $K_N$ are $r$-coloured then there is
a set of $n$ vertices which does not contain a copy of $K_k$ in at least one of the $r$ colours.
Prove that there is a constant $C=C(r)>1$ such that
$$R(n;3,r) < C^{\sqrt{n}}.$$

Remarks recorded on the page:
* Conjectured by Erdős and Gyárfás, who proved the existence of some $C>1$ such that
  $R(n;3,r)>C^{\sqrt{n}}$. Note that when $r=k=2$ the classic Ramsey numbers are recovered. Erdős
  thought it likely that for all $r,k\geq 2$ there exists some $C_1,C_2>1$ (depending only on $r$)
  such that
  $$C_1^{n^{1/k-1}}< R(n;k,r) < C_2^{n^{1/k-1}}.$$
* Antonio Girao has pointed out that this problem as written is easily disproved, and indeed
  $R(n;3,2) \geq C^{n}$. The obvious probabilistic construction (randomly colour the edges
  red/blue independently uniformly at random) yields a 2-colouring of the edges of $K_N$ such
  that every set on $n$ vertices contains a red triangle and a blue triangle (using that every set
  of $n$ vertices contains $\gg n^2$ edge-disjoint triangles), provided $N \leq C^n$ for some
  absolute constant $C>1$. This implies $R(n;3,2) \geq C^{n}$, contradicting the conjecture.
* Perhaps Erdős had a different problem in mind, but it is not clear what that might be. It would
  presumably be one where the natural probabilistic argument would deliver a bound like
  $C^{\sqrt{n}}$, as Erdős and Gyárfás claim to have achieved via the probabilistic method.

Tags: graph theory, Ramsey theory. OEIS: "Possible", with the note that the original source is
ambiguous about what the problem is. 1 comment (not captured).

**Status and polarity.** The banner reads OPEN because the intended problem is unknown. The
statement as written is refuted by the page's own remark, and the first pass asserted it. v2
asserts the negation of the first pass's proposition, which is kept byte-identical inside `¬ (…)`.
That is the corpus convention for a refuted statement. The mirror (`teorth/erdosproblems`) has
`open` (2025-08-31) with the comment "ambiguous statement", and upstream has no `129.lean` at the
pinned snapshot. Girao's argument was re-derived in this review and holds: with at least $cn^2$
edge-disjoint triangles in every $n$-set, a fixed set has no red triangle with probability at most
$(7/8)^{cn^2}$, there are at most $N^n$ sets, and so $N\le C^n$ with $C>1$ close enough to $1$
leaves positive probability that every $n$-set has both a red and a blue triangle. It is not
machine-checked here. `variants.girao` states it, and `variants.main_of_girao` proves that it
implies the main theorem.

**Encoding.**
* `EdgeColoring N r` colours ordered pairs, including the diagonal pairs $(x,x)$, which are never
  examined. A $k$-set is monochromatic in colour $c$ when every ordered pair of distinct vertices
  in it has colour $c$. This gives the same Ramsey number as symmetric colourings. Replacing
  $\chi\,x\,y$ by $\chi\,(\min x\,y)\,(\max x\,y)$ makes any colouring symmetric and keeps every
  $c$-clique, so a set that is $K_k$-free for the symmetric colouring is $K_k$-free for the
  original. Hence "every colouring has the property" and "every symmetric colouring has it" hold
  for the same $N$.
* `multicolorRamseyNum n k r` is `sInf` of the set of admissible $N$. It is the true smallest $N$
  when that set is nonempty, which holds for $k=3$ and $r\ge2$ by Ramsey's theorem: a
  monochromatic $n$-set in one colour has no triangle in another. For $r=1$ and $n\ge3$ the set is
  empty, since every triple is a monochromatic triangle, and `sInf ∅ = 0`.
  `variants.one_color_junk` proves this. So the $r=1$ instance of the first pass's proposition is
  true only through the junk value. The negation is unaffected, because it is witnessed at $r=2$.
* For $n=0$ the value $N=0$ works, so $R(0;3,r)=0$ and the bound at $n=0$ reads $0<C^0=1$.
* The page prints the exponent of the general conjecture as $n^{1/k-1}$. For $k=3$ it has to be
  $1/(k-1)=\tfrac12$, to match $\sqrt n$, and the first pass wrote $1/(k-1)$.
* The general conjecture is not stated as a theorem. For $k\ge3$ the same argument applies with
  copies of $K_k$ in place of triangles, each red with probability $2^{-\binom k2}$, and gives
  $R(n;k,2)\ge e^{cn}$. That refutes the upper bound $C_2^{n^{1/(k-1)}}$ for every $k\ge3$. This
  extension is not on the page and is not checked here. For $k=2$ the page's two-sided bound is
  the classical exponential bound on Ramsey numbers.

## References

* [Er97b] Erdős, P., _Some old and new problems in various branches of combinatorics_. Discrete
  Math. (1997), 227–231.

(Provenance: the one `/latex/129` fetch in the session logs returned no bibliography, and no
upstream `129.lean` exists. [Er97b] is from the bibliographies of the `/latex` pages of other
problems in the logs. Girao is credited by name on the page, with no entry.)
-/

/-- An r-edge-coloring of the complete graph K_N: a function that assigns a
    color in Fin r to each ordered pair of vertices. Pairs (x, x) are never examined. -/
def EdgeColoring (N r : ℕ) : Type := Fin N → Fin N → Fin r

/-- A vertex set S is monochromatic-K_k-free in color c under coloring χ if
    there is no k-element subset of S in which every pair of distinct vertices
    receives color c. -/
def IsMonoKkFree {N r : ℕ} (χ : EdgeColoring N r) (c : Fin r)
    (k : ℕ) (S : Finset (Fin N)) : Prop :=
  ∀ T : Finset (Fin N), T ⊆ S → T.card = k →
    ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ χ x y ≠ c

/-- The generalized Ramsey number R(n; k, r): the smallest N such that for
    every r-coloring of the edges of K_N, there exists a set of n vertices and
    a color c such that the set is K_k-free in color c. It is 0 when no N
    works, which happens for r = 1 and n ≥ 3 (k = 3). -/
noncomputable def multicolorRamseyNum (n k r : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (χ : EdgeColoring N r),
    ∃ (S : Finset (Fin N)) (c : Fin r),
      S.card = n ∧ IsMonoKkFree χ c k S}

/--
Erdős Problem #129 [Er97b], as written on the page ("Prove that there is a constant C = C(r) > 1
such that R(n; 3, r) < C^√n") — REFUTED as written, although the page banner still reads OPEN
because the intended problem is unclear. The page's remark (Antonio Girao): R(n; 3, 2) ≥ C^n for
some C > 1, which exceeds C'^√n for every C' once n is large.

The first pass asserted the proposition below. This file asserts its negation, the corpus
convention for a refuted statement. The r = 1 instance of the proposition holds only through the
junk value `sInf ∅ = 0` (see `variants.one_color_junk`), which does not affect the negation, since
it is witnessed at r = 2.
-/
theorem erdos_problem_129 :
    ¬ (∀ r : ℕ, 1 ≤ r →
      ∃ C : ℝ, 1 < C ∧
        ∀ n : ℕ, (multicolorRamseyNum n 3 r : ℝ) < C ^ Real.sqrt (n : ℝ)) :=
  sorry

/--
Girao's bound, as recorded on the page (PROVED by the probabilistic argument in the module
docstring, not checked here): R(n; 3, 2) ≥ C^n for some C > 1 and all large n.
-/
theorem erdos_problem_129.variants.girao :
    ∃ C : ℝ, 1 < C ∧ ∀ᶠ n : ℕ in atTop, C ^ n ≤ (multicolorRamseyNum n 3 2 : ℝ) :=
  sorry

/--
The main theorem follows from Girao's bound (PROVED): an exponential lower bound at r = 2
contradicts R(n; 3, 2) < C'^√n for large n.
-/
theorem erdos_problem_129.variants.main_of_girao
    (hg : ∃ C : ℝ, 1 < C ∧ ∀ᶠ n : ℕ in atTop, C ^ n ≤ (multicolorRamseyNum n 3 2 : ℝ)) :
    ¬ (∀ r : ℕ, 1 ≤ r →
      ∃ C : ℝ, 1 < C ∧
        ∀ n : ℕ, (multicolorRamseyNum n 3 r : ℝ) < C ^ Real.sqrt (n : ℝ)) := by
  intro h
  obtain ⟨C₁, hC₁, hev⟩ := hg
  obtain ⟨C₂, hC₂, hall⟩ := h 2 (by norm_num)
  have ha0 : 0 < Real.log C₁ := Real.log_pos hC₁
  have hb0 : 0 < Real.log C₂ := Real.log_pos hC₂
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨M, hM1, hM2⟩ : ∃ M : ℕ, N0 ≤ M ∧ (Real.log C₂ / Real.log C₁) ^ 2 ≤ (M : ℝ) :=
    ⟨max N0 ⌈(Real.log C₂ / Real.log C₁) ^ 2⌉₊, le_max_left _ _,
      le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right _ _)⟩
  have h1 := hN0 M hM1
  have h2 := hall M
  have hsq : Real.log C₂ / Real.log C₁ ≤ Real.sqrt (M : ℝ) :=
    (Real.le_sqrt' (div_pos hb0 ha0)).mpr hM2
  have hMM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg M)
  have hs0 : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
  have hle : Real.log C₂ * Real.sqrt (M : ℝ) ≤ Real.log C₁ * (M : ℝ) := by
    have h3 : Real.log C₂ ≤ Real.log C₁ * Real.sqrt (M : ℝ) := by
      have := (div_le_iff₀ ha0).mp hsq
      linarith
    calc Real.log C₂ * Real.sqrt (M : ℝ)
        ≤ (Real.log C₁ * Real.sqrt (M : ℝ)) * Real.sqrt (M : ℝ) :=
          mul_le_mul_of_nonneg_right h3 hs0
      _ = Real.log C₁ * (M : ℝ) := by rw [mul_assoc, hMM]
  have e1 : C₂ ^ Real.sqrt (M : ℝ) = Real.exp (Real.log C₂ * Real.sqrt (M : ℝ)) :=
    Real.rpow_def_of_pos (by linarith) _
  have e2 : C₁ ^ M = Real.exp (Real.log C₁ * (M : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
  have h4 : Real.exp (Real.log C₂ * Real.sqrt (M : ℝ)) ≤ Real.exp (Real.log C₁ * (M : ℝ)) :=
    Real.exp_le_exp.mpr hle
  linarith [h1, h2, e1, e2, h4]

/--
Lower bound of Erdős and Gyárfás, as recorded on the page (PROVED): for every r ≥ 2 there is some
C > 1 with R(n; 3, r) > C^√n for all large n. The bound is stated for large n and r ≥ 2: at n = 0
the value is R = 0, and at r = 1 the value is the junk value 0, so a bound for every n or every
r ≥ 1 would be false.
-/
theorem erdos_problem_129.variants.erdos_gyarfas_lower :
    ∀ r : ℕ, 2 ≤ r → ∃ C : ℝ, 1 < C ∧
      ∀ᶠ n : ℕ in atTop, C ^ Real.sqrt (n : ℝ) < (multicolorRamseyNum n 3 r : ℝ) :=
  sorry

/--
The degenerate case r = 1 (PROVED): with one colour, every triple is a monochromatic triangle, no N
is admissible once n ≥ 3, and `sInf ∅ = 0` is returned. The r = 1 instance of the proposition in
the main theorem is therefore true only through this junk value.
-/
theorem erdos_problem_129.variants.one_color_junk (n : ℕ) (hn : 3 ≤ n) :
    multicolorRamseyNum n 3 1 = 0 := by
  unfold multicolorRamseyNum
  have : {N : ℕ | ∀ (χ : EdgeColoring N 1), ∃ (S : Finset (Fin N)) (c : Fin 1),
      S.card = n ∧ IsMonoKkFree χ c 3 S} = ∅ := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨S, c, hS, hfree⟩ := h (fun _ _ => 0)
    obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (s := S) (n := 3) (by omega)
    obtain ⟨x, _, y, _, _, hxy⟩ := hfree T hTS hT
    exact hxy (Subsingleton.elim _ _)
  rw [this]
  exact Nat.sInf_empty
