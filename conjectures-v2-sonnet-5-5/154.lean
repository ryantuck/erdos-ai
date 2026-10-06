-- [AI - Claude Sonnet 5.5]: Erdős Problem 154 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

open Filter Real Finset Topology

noncomputable section

/-!
# Erdős Problem #154: The sumset of a maximal Sidon set modulo $m$

*Source:* [erdosproblems.com/154](https://www.erdosproblems.com/154) (banner **PROVED (LEAN)**: "This has been solved in
the affirmative and the proof verified in Lean."; captured 2026-02-20 as the tidied problem box, "Formalised
statement? No", 1 comment, not captured). [ESS94]

Let $A\subset \{1,\ldots,N\}$ be a Sidon set with $\lvert A\rvert\sim N^{1/2}$. Must $A+A$ be well-distributed over all small
moduli? In particular, must about half the elements of $A+A$ be even and half odd?

Remark recorded on the page: Lindström [Li98] has shown this is true for $A$ itself, subsequently strengthened by
Kolountzakis [Ko99]. It follows immediately using the Sidon property that $A+A$ is similarly well-distributed.

Tags: sidon sets.

**Status.** PROVED in the affirmative, with a proof verified in Lean (the page banner at capture). The mirror
(`teorth/erdosproblems`, `b916d95`) has `proved (Lean)` (2026-02-06), no prize, formalised `yes` (2026-06-29), and
upstream's `154.lean` (`df3f12d`) is `research solved` and links two Lean proofs by others, one of this statement and one
of Lindström's theorem for `A` itself. **DEFERRED:** these proofs were not examined. The `sorry` of the main theorem stands
for a proved theorem, and is reduced to Lindström's theorem by `variants.main_of_lindstrom`.

**Encoding.**
* `IsSidonSet`, `sumset` and `modFraction m r S` (the proportion of the elements of `S` in the class `r` modulo `m`; for an
  empty `S` it is `0 / 0 = 0`, which matters only for finitely many `n`) are the input's. `variants.sumset_eq_add` proves
  that `sumset A` is Mathlib's pointwise `A + A`.
* The statement is about a sequence `A n ⊆ {0, …, n}` of Sidon sets with `|A n| / √n → 1`, which is the page's
  "$A\subset\{1,\ldots,N\}$ with $\lvert A\rvert\sim N^{1/2}$" for `N = n`, with `0` allowed (a translation changes the
  residues of `A` and of `A + A` and does not affect equidistribution). It concludes `modFraction m r (sumset (A n)) → 1 / m`
  for every modulus `m ≥ 1` and residue `r < m`; `m = 2` is the page's "half even and half odd". Upstream states it for
  sequences `A k ⊆ {0, …, N k}` with an arbitrary `N k → ∞` and `m ≥ 2`, which is slightly more general.
* `variants.card_sumset` proves that a Sidon set with `n` elements has `n (n + 1) / 2` sums, and
  `variants.parity_counts` the input's explicit counts, `e (e + 1) / 2 + o (o + 1) / 2` even and `e * o` odd sums.
* `variants.lindstrom` is Lindström's theorem for `A` itself (PROVED [Li98], strengthened by [Ko99]; `sorry` here), and
  `variants.sumset_of_lindstrom` and `variants.main_of_lindstrom` prove in Lean the page's "it follows immediately using the
  Sidon property": the equidistribution of `A + A` modulo every `m` follows from that of `A`. The counting uses that the
  sums `a + b` with `a ≤ b` are distinct, so the classes of `A + A` are counted by `∑ i, c i * c (r - i)` over the
  classes of `A`, up to `|A|` diagonal terms.
* That the hypotheses are satisfiable (Sidon sets with `|A n| ∼ √n` for every `n`, from the constructions of Singer and
  of Bose and Chowla and the density of primes) is not formalized.

## References

* [ESS94] Erdős, P., Sárközy, A. and Sós, T., _On sum sets of Sidon sets, I_. J. Number Theory (1994), 329–347. (From the
  `/latex/156` fetch in the session logs, which is the site's bibliography for another problem; upstream's docstring agrees.)
* [Li98] Lindström, B., _Well distribution of Sidon sets in residue classes_. J. Number Theory (1998), 197–200.
* [Ko99] Kolountzakis, M. N., _On the uniform distribution in residue classes of dense sets of integers with distinct
  sums_. J. Number Theory (1999), 147–153.

(Provenance: [Li98] and [Ko99] are from the `/latex/154` fetch. **DEFERRED:** the exact form of Kolountzakis's strengthening.)
-/

/-- A finite set of natural numbers is a Sidon set (also called a B₂ set) if all
    pairwise sums a + b (allowing a = b) are distinct: whenever a + b = c + d
    with a, b, c, d ∈ A, then {a, b} = {c, d} as multisets. Equivalently,
    all differences a - b with a ≠ b and a, b ∈ A are distinct. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The sumset A + A = {a + b | a, b ∈ A}. -/
def sumset (A : Finset ℕ) : Finset ℕ := Finset.image₂ (· + ·) A A

/-- The fraction of elements in a finite set of naturals that are congruent to r modulo m. -/
noncomputable def modFraction (m r : ℕ) (S : Finset ℕ) : ℝ :=
  ((S.filter (fun n => n % m = r)).card : ℝ) / (S.card : ℝ)

/--
Erdős Problem #154 [ESS94] (PROVED, see the module docstring):

Let A ⊂ {1,...,N} be a Sidon set with |A| ∼ N^(1/2). Must A + A be
well-distributed over all small moduli? In particular, must about half
the elements of A+A be even and half odd?

Proved in the affirmative. Lindström [Li98] showed that A itself is
well-distributed modulo small integers (e.g. |A ∩ {evens}| ≈ |A|/2),
subsequently strengthened by Kolountzakis [Ko99]. The extension to A + A
follows immediately from the Sidon property: if A has e even and o odd
elements, then A + A has exactly e*(e+1)/2 + o*(o+1)/2 even elements
and e*o odd elements (all distinct by the Sidon property), and the
distribution is approximately 1/2 each when e ≈ o ≈ |A|/2.

Formalized as: for any sequence (Aₙ)ₙ of Sidon sets Aₙ ⊂ {0,...,n}
with |Aₙ| / √n → 1 as n → ∞, and any fixed modulus m ≥ 1 and
residue 0 ≤ r < m, the fraction of elements of Aₙ + Aₙ in residue
class r mod m tends to 1/m.
-/
theorem erdos_problem_154 :
    ∀ (A : ℕ → Finset ℕ),
      (∀ n, IsSidonSet (A n)) →
      (∀ n, (A n) ⊆ Finset.range (n + 1)) →
      Tendsto (fun n => ((A n).card : ℝ) / Real.sqrt n) atTop (𝓝 1) →
      ∀ (m : ℕ), 1 ≤ m →
        ∀ r < m,
          Tendsto (fun n => modFraction m r (sumset (A n))) atTop (𝓝 (1 / (m : ℝ))) :=
  sorry

open scoped Pointwise in
/-- `sumset A` is Mathlib's pointwise sum `A + A` of finsets (PROVED in Lean). -/
theorem erdos_problem_154.variants.sumset_eq_add (A : Finset ℕ) : sumset A = A + A := rfl

/-- `A + A` is the image of the ordered pairs `a ≤ b` under addition (PROVED in Lean). -/
theorem erdos_problem_154.sumset_eq_image (A : Finset ℕ) :
    sumset A = ((A ×ˢ A).filter (fun p => p.1 ≤ p.2)).image (fun p => p.1 + p.2) := by
  ext s
  simp only [sumset, Finset.mem_image₂, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rcases le_total a b with h | h
    · exact ⟨(a, b), ⟨⟨ha, hb⟩, h⟩, rfl⟩
    · exact ⟨(b, a), ⟨⟨hb, ha⟩, h⟩, add_comm b a⟩
  · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, -⟩, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

/-- For a Sidon set, addition is injective on the pairs `a ≤ b` (PROVED in Lean). -/
theorem erdos_problem_154.injOn_sum (A : Finset ℕ) (hA : IsSidonSet A) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) ↑((A ×ˢ A).filter (fun p => p.1 ≤ p.2)) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
  simp only [Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq] at hab hcd
  simp only at h
  rcases hA a hab.1.1 b hab.1.2 c hcd.1.1 d hcd.1.2 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [h1, h2]
  · have h3 : a = b := le_antisymm hab.2 (by have := hcd.2; omega)
    simp only [Prod.mk.injEq]
    omega

/-- Counting ordered pairs against pairs with `a ≤ b`: twice the number of pairs `a ≤ b` with `q (a + b)` is the
number of ordered pairs with `q (a + b)` plus the number of `a` with `q (a + a)` (PROVED in Lean). -/
theorem erdos_problem_154.two_mul_card (A : Finset ℕ) (q : ℕ → Prop) [DecidablePred q] :
    2 * ((A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ q (p.1 + p.2))).card =
      ((A ×ˢ A).filter (fun p => q (p.1 + p.2))).card + (A.filter (fun a => q (a + a))).card := by
  simp only [Finset.card_filter, Finset.sum_product]
  have hcomm : ∑ a ∈ A, ∑ b ∈ A, (if b ≤ a ∧ q (b + a) then 1 else 0) =
      ∑ a ∈ A, ∑ b ∈ A, (if a ≤ b ∧ q (a + b) then 1 else 0) := Finset.sum_comm
  have hpt : ∀ a b : ℕ, (if a ≤ b ∧ q (a + b) then 1 else 0) + (if b ≤ a ∧ q (b + a) then 1 else 0) =
      (if q (a + b) then 1 else 0) + (if a = b then (if q (a + a) then 1 else 0) else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · have h1 : ¬ b ≤ a := by omega
      have h2 : a ≠ b := by omega
      simp [h1, h2, le_of_lt h]
    · subst h
      by_cases hq : q (a + a) <;> simp [hq]
    · have h1 : ¬ a ≤ b := by omega
      have h2 : a ≠ b := by omega
      have h3 : b + a = a + b := add_comm b a
      simp [h1, h2, le_of_lt h, h3]
  have key : ∑ a ∈ A, ∑ b ∈ A, ((if a ≤ b ∧ q (a + b) then 1 else 0) + (if b ≤ a ∧ q (b + a) then 1 else 0)) =
      ∑ a ∈ A, ∑ b ∈ A, ((if q (a + b) then 1 else 0) + (if a = b then (if q (a + a) then 1 else 0) else 0)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hpt a b
  simp only [Finset.sum_add_distrib] at key
  rw [hcomm] at key
  have hdiag : ∑ a ∈ A, ∑ b ∈ A, (if a = b then (if q (a + a) then 1 else 0) else 0) =
      ∑ a ∈ A, (if q (a + a) then 1 else 0) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.sum_ite_eq A a (fun _ => if q (a + a) then 1 else 0)]
    simp [ha]
  rw [hdiag] at key
  omega


/-- For a Sidon set, the elements of `A + A` satisfying `q` correspond to the pairs `a ≤ b` with `q (a + b)`
(PROVED in Lean). -/
theorem erdos_problem_154.card_filter_sumset (A : Finset ℕ) (hA : IsSidonSet A) (q : ℕ → Prop) [DecidablePred q] :
    ((sumset A).filter q).card =
      ((A ×ˢ A).filter (fun p => p.1 ≤ p.2 ∧ q (p.1 + p.2))).card := by
  rw [erdos_problem_154.sumset_eq_image, Finset.filter_image]
  rw [Finset.card_image_of_injOn]
  · congr 1
    ext p
    simp only [Finset.mem_filter, and_assoc]
  · exact (erdos_problem_154.injOn_sum A hA).mono (by
      intro p hp
      simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_setOf_eq] at hp ⊢
      exact hp.1)

/-- For a Sidon set, twice the number of elements of `A + A` satisfying `q` is the number of ordered pairs with
`q (a + b)` plus the number of `a` with `q (a + a)` (PROVED in Lean). -/
theorem erdos_problem_154.two_mul_card_sumset (A : Finset ℕ) (hA : IsSidonSet A) (q : ℕ → Prop) [DecidablePred q] :
    2 * ((sumset A).filter q).card =
      ((A ×ˢ A).filter (fun p => q (p.1 + p.2))).card + (A.filter (fun a => q (a + a))).card := by
  rw [erdos_problem_154.card_filter_sumset A hA q]
  exact erdos_problem_154.two_mul_card A q

/-- The sumset of a Sidon set with `n` elements has `n (n + 1) / 2` elements (PROVED in Lean): all the sums `a + b` with
`a ≤ b` are distinct. -/
theorem erdos_problem_154.variants.card_sumset (A : Finset ℕ) (hA : IsSidonSet A) :
    2 * (sumset A).card = A.card * A.card + A.card := by
  have h := erdos_problem_154.two_mul_card_sumset A hA (fun _ => True)
  simpa [Finset.filter_true_of_mem, Finset.card_product] using h


/-- `n % m = r` is `n = r` in `ZMod m`, for `r < m` (PROVED in Lean). -/
theorem erdos_problem_154.mod_eq_iff_zmod (m r n : ℕ) (hr : r < m) : n % m = r ↔ (n : ZMod m) = (r : ZMod m) := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr]

/-- The number of ordered pairs of `A` whose sum is in the class `r` modulo `m`, by the residue classes of the entries,
is `∑ i, c i * c (r - i)` for `c i` the number of elements of `A` in the class `i` (PROVED in Lean). -/
theorem erdos_problem_154.ordered_count (A : Finset ℕ) (m r : ℕ) [NeZero m] (hr : r < m) :
    ((A ×ˢ A).filter (fun p => (p.1 + p.2) % m = r)).card =
      ∑ i : ZMod m, (A.filter (fun a : ℕ => (a : ZMod m) = i)).card *
        (A.filter (fun a : ℕ => (a : ZMod m) = (r : ZMod m) - i)).card := by
  have h1 : ((A ×ˢ A).filter (fun p => (p.1 + p.2) % m = r)).card =
      ∑ a ∈ A, (A.filter (fun b : ℕ => (b : ZMod m) = (r : ZMod m) - (a : ZMod m))).card := by
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : (a + b) % m = r ↔ (b : ZMod m) = (r : ZMod m) - (a : ZMod m) := by
      rw [erdos_problem_154.mod_eq_iff_zmod m r _ hr]
      push_cast
      constructor <;> intro h <;> linear_combination h
    simp only [this]
  rw [h1, ← Finset.sum_fiberwise A (fun a : ℕ => (a : ZMod m))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => (A.filter (fun a : ℕ => (a : ZMod m) = (r : ZMod m) - i)).card)]
  · simp
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [ha.2]


/-- If `|A n| / √n → 1` then `|A n| → ∞` (PROVED in Lean). -/
theorem erdos_problem_154.tendsto_card (A : ℕ → Finset ℕ)
    (hcard : Tendsto (fun n => ((A n).card : ℝ) / Real.sqrt n) atTop (𝓝 1)) :
    Tendsto (fun n => ((A n).card : ℝ)) atTop atTop := by
  have hsq : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h := Filter.Tendsto.pos_mul_atTop (by norm_num : (0:ℝ) < 1) hcard hsq
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hs : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  field_simp

/-- If `|A n| / √n → 1` and each class of `A n` modulo `m` has `~ √n / m` elements (Lindström's conclusion), then each
class has the proportion `1 / m` of `A n` (PROVED in Lean). -/
theorem erdos_problem_154.tendsto_class (A : ℕ → Finset ℕ)
    (hcard : Tendsto (fun n => ((A n).card : ℝ) / Real.sqrt n) atTop (𝓝 1))
    (m : ℕ) [NeZero m]
    (hL : ∀ i < m, Tendsto (fun n => (((A n).filter (fun a => a % m = i)).card : ℝ) / Real.sqrt n)
      atTop (𝓝 (1 / (m : ℝ))))
    (i : ZMod m) :
    Tendsto (fun n => (((A n).filter (fun a : ℕ => (a : ZMod m) = i)).card : ℝ) / ((A n).card : ℝ))
      atTop (𝓝 (1 / (m : ℝ))) := by
  have h1 := hL i.val (ZMod.val_lt i)
  have h2 := h1.div hcard (by norm_num)
  rw [div_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hs : Real.sqrt n ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  have hfil : (A n).filter (fun a : ℕ => (a : ZMod m) = i) = (A n).filter (fun a => a % m = i.val) := by
    ext a
    simp only [Finset.mem_filter]
    rw [erdos_problem_154.mod_eq_iff_zmod m i.val a (ZMod.val_lt i), ZMod.natCast_zmod_val]
  rw [hfil]
  exact div_div_div_cancel_right₀ hs _ _


/--
The page's "it follows immediately using the Sidon property that `A + A` is similarly well-distributed" (PROVED in Lean):
if the residue classes of `A n` modulo `m` each have `~ √n / m` elements (Lindström's theorem, `variants.lindstrom`), and
`|A n| / √n → 1`, then the proportion of `A n + A n` in each class `r` modulo `m` tends to `1 / m`.
-/
theorem erdos_problem_154.variants.sumset_of_lindstrom (A : ℕ → Finset ℕ) (hS : ∀ n, IsSidonSet (A n))
    (hcard : Tendsto (fun n => ((A n).card : ℝ) / Real.sqrt n) atTop (𝓝 1))
    (m : ℕ) (hm : 1 ≤ m)
    (hL : ∀ i < m, Tendsto (fun n => (((A n).filter (fun a => a % m = i)).card : ℝ) / Real.sqrt n)
      atTop (𝓝 (1 / (m : ℝ))))
    (r : ℕ) (hr : r < m) :
    Tendsto (fun n => modFraction m r (sumset (A n))) atTop (𝓝 (1 / (m : ℝ))) := by
  haveI : NeZero m := ⟨by omega⟩
  have hNtop := erdos_problem_154.tendsto_card A hcard
  have hx := erdos_problem_154.tendsto_class A hcard m hL
  set N : ℕ → ℝ := fun n => ((A n).card : ℝ) with hN
  set c : ZMod m → ℕ → ℝ := fun i n => (((A n).filter (fun a : ℕ => (a : ZMod m) = i)).card : ℝ) with hc
  set D : ℕ → ℝ := fun n => (((A n).filter (fun a => (a + a) % m = r)).card : ℝ) with hD
  have hsum : Tendsto (fun n => ∑ i : ZMod m, (c i n / N n) * (c ((r : ZMod m) - i) n / N n))
      atTop (𝓝 (∑ i : ZMod m, (1 / (m : ℝ)) * (1 / (m : ℝ)))) :=
    tendsto_finset_sum _ (fun i _ => (hx i).mul (hx _))
  have hsumval : ∑ i : ZMod m, (1 / (m : ℝ)) * (1 / (m : ℝ)) = 1 / (m : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    have : (m : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hsumval] at hsum
  have hinv : Tendsto (fun n => 1 / N n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hNtop
  have hDlim : Tendsto (fun n => D n / (N n) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hinv
    filter_upwards [hNtop.eventually_ge_atTop 1] with n hn
    have hDle : D n ≤ N n := by
      simp only [hD, hN]
      exact_mod_cast Finset.card_filter_le _ _
    have hpos : 0 < N n := by linarith
    rw [div_le_div_iff₀ (by positivity) hpos]
    nlinarith
  have hlim : Tendsto (fun n => ((∑ i : ZMod m, (c i n / N n) * (c ((r : ZMod m) - i) n / N n)) + D n / (N n) ^ 2) / (1 + 1 / N n))
      atTop (𝓝 ((1 / (m : ℝ) + 0) / (1 + 0))) :=
    (hsum.add hDlim).div (tendsto_const_nhds.add hinv) (by norm_num)
  rw [add_zero, add_zero, div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hNtop.eventually_ge_atTop 1] with n hn
  have hpos : 0 < N n := by linarith
  have hSn := hS n
  -- the two counting identities
  have h2U := erdos_problem_154.two_mul_card_sumset (A n) hSn (fun s => s % m = r)
  have h2T := erdos_problem_154.variants.card_sumset (A n) hSn
  have hO := erdos_problem_154.ordered_count (A n) m r hr
  simp only [modFraction]
  have hU : (2 * (((sumset (A n)).filter (fun s => s % m = r)).card : ℝ)) =
      (∑ i : ZMod m, c i n * c ((r : ZMod m) - i) n) + D n := by
    have := congrArg (fun x : ℕ => (x : ℝ)) h2U
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at this
    rw [this, hO]
    simp [hc, hD]
  have hT : (2 * ((sumset (A n)).card : ℝ)) = N n * N n + N n := by
    have := congrArg (fun x : ℕ => (x : ℝ)) h2T
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at this
    simpa [hN] using this
  have hTpos : (0 : ℝ) < ((sumset (A n)).card : ℝ) := by nlinarith
  have : (∑ i : ZMod m, (c i n / N n) * (c ((r : ZMod m) - i) n / N n)) =
      (∑ i : ZMod m, c i n * c ((r : ZMod m) - i) n) / (N n) ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [this]
  have hden : (0 : ℝ) < 1 + 1 / N n := by positivity
  rw [div_eq_div_iff hden.ne' hTpos.ne']
  field_simp
  nlinarith [hU, hT]


/--
The input's docstring claims that, for a Sidon set with `e` even and `o` odd elements, `A + A` has `e (e + 1) / 2 + o (o + 1) / 2`
even elements and `e * o` odd elements (PROVED in Lean).
-/
theorem erdos_problem_154.variants.parity_counts (A : Finset ℕ) (hA : IsSidonSet A) :
    2 * ((sumset A).filter (fun s => s % 2 = 0)).card =
        (A.filter (fun a => a % 2 = 0)).card * ((A.filter (fun a => a % 2 = 0)).card + 1) +
          (A.filter (fun a => a % 2 = 1)).card * ((A.filter (fun a => a % 2 = 1)).card + 1) ∧
      ((sumset A).filter (fun s => s % 2 = 1)).card =
        (A.filter (fun a => a % 2 = 0)).card * (A.filter (fun a => a % 2 = 1)).card := by
  have hsplit : ∀ a : ℕ, a % 2 = 0 ∨ a % 2 = 1 := fun a => by omega
  have hcard : A.card = (A.filter (fun a => a % 2 = 0)).card + (A.filter (fun a => a % 2 = 1)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext a
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro ha; rcases hsplit a with h | h <;> [left; right] <;> exact ⟨ha, h⟩
      · rintro (h | h) <;> exact h.1
    · rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_filter] at ha hb
      omega
  -- ordered pair counts by parity of the first entry
  have hord : ∀ r : ℕ, ((A ×ˢ A).filter (fun p => (p.1 + p.2) % 2 = r)).card =
      ∑ a ∈ A, (A.filter (fun b => (a + b) % 2 = r)).card := by
    intro r
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.card_filter]
  set e := (A.filter (fun a => a % 2 = 0)).card with he
  set o := (A.filter (fun a => a % 2 = 1)).card with ho
  have hfib : ∀ r : ℕ, r < 2 → ∑ a ∈ A, (A.filter (fun b => (a + b) % 2 = r)).card =
      ∑ a ∈ A, (if a % 2 = 0 then (A.filter (fun b => b % 2 = r)).card else (A.filter (fun b => b % 2 = (r + 1) % 2)).card) := by
    intro r hr
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with h
    · congr 1
      ext b; simp only [Finset.mem_filter]
      constructor <;> rintro ⟨hb, h'⟩ <;> exact ⟨hb, by omega⟩
    · congr 1
      ext b; simp only [Finset.mem_filter]
      constructor <;> rintro ⟨hb, h'⟩ <;> exact ⟨hb, by omega⟩
  have hsum : ∀ (x y : ℕ), ∑ a ∈ A, (if a % 2 = 0 then x else y) = e * x + o * y := by
    intro x y
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, smul_eq_mul]
    have h1 : A.filter (fun a => ¬ a % 2 = 0) = A.filter (fun a => a % 2 = 1) := by
      ext a; simp only [Finset.mem_filter]
      constructor <;> rintro ⟨ha, h'⟩ <;> exact ⟨ha, by omega⟩
    rw [h1]
  have hO0 : ((A ×ˢ A).filter (fun p => (p.1 + p.2) % 2 = 0)).card = e * e + o * o := by
    rw [hord, hfib 0 (by norm_num), hsum]
  have hO1 : ((A ×ˢ A).filter (fun p => (p.1 + p.2) % 2 = 1)).card = e * o + o * e := by
    rw [hord, hfib 1 (by norm_num), hsum]
  have hD0 : (A.filter (fun a => (a + a) % 2 = 0)).card = A.card := by
    congr 1
    exact Finset.filter_true_of_mem (fun a _ => by omega)
  have hD1 : (A.filter (fun a => (a + a) % 2 = 1)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a _; omega
  have h0 := erdos_problem_154.two_mul_card_sumset A hA (fun s => s % 2 = 0)
  have h1 := erdos_problem_154.two_mul_card_sumset A hA (fun s => s % 2 = 1)
  simp only at h0 h1
  rw [hO0, hD0] at h0
  rw [hO1, hD1] at h1
  refine ⟨by nlinarith [h0, hcard], by nlinarith [h1]⟩


/--
Lindström's theorem [Li98], strengthened by Kolountzakis [Ko99] (PROVED, not checked here): for a sequence of Sidon sets
`A n ⊆ {0, …, n}` with `|A n| / √n → 1`, each residue class `i` modulo `m` contains `∼ √n / m` elements of `A n`.
**DEFERRED:** the exact form of the strengthening, and the proof, were not seen.
-/
theorem erdos_problem_154.variants.lindstrom :
    ∀ (A : ℕ → Finset ℕ),
      (∀ n, IsSidonSet (A n)) →
      (∀ n, (A n) ⊆ Finset.range (n + 1)) →
      Tendsto (fun n => ((A n).card : ℝ) / Real.sqrt n) atTop (𝓝 1) →
      ∀ (m : ℕ), 1 ≤ m →
        ∀ i < m,
          Tendsto (fun n => (((A n).filter (fun a => a % m = i)).card : ℝ) / Real.sqrt n)
            atTop (𝓝 (1 / (m : ℝ))) :=
  sorry

/-- The main theorem follows from Lindström's theorem (PROVED in Lean): this is the page's "it follows immediately using
the Sidon property that `A + A` is similarly well-distributed". -/
theorem erdos_problem_154.variants.main_of_lindstrom
    (h : ∀ (A : ℕ → Finset ℕ),
      (∀ n, IsSidonSet (A n)) →
      (∀ n, (A n) ⊆ Finset.range (n + 1)) →
      Tendsto (fun n => ((A n).card : ℝ) / Real.sqrt n) atTop (𝓝 1) →
      ∀ (m : ℕ), 1 ≤ m →
        ∀ i < m,
          Tendsto (fun n => (((A n).filter (fun a => a % m = i)).card : ℝ) / Real.sqrt n)
            atTop (𝓝 (1 / (m : ℝ)))) :
    ∀ (A : ℕ → Finset ℕ),
      (∀ n, IsSidonSet (A n)) →
      (∀ n, (A n) ⊆ Finset.range (n + 1)) →
      Tendsto (fun n => ((A n).card : ℝ) / Real.sqrt n) atTop (𝓝 1) →
      ∀ (m : ℕ), 1 ≤ m →
        ∀ r < m,
          Tendsto (fun n => modFraction m r (sumset (A n))) atTop (𝓝 (1 / (m : ℝ))) := by
  intro A hS hsub hcard m hm r hr
  exact erdos_problem_154.variants.sumset_of_lindstrom A hS hcard m hm
    (fun i hi => h A hS hsub hcard m hm i hi) r hr

end
