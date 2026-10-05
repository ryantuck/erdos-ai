-- [AI - Claude Sonnet 5.5]: Erdős Problem 136 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Classical Filter

noncomputable section

/-!
# Erdős Problem #136: The Erdős–Gyárfás Function f(n, 4, 5)

*Source:* [erdosproblems.com/136](https://www.erdosproblems.com/136) (banner **SOLVED**: "This has
been resolved in some other way than a proof or disproof."; captured 2026-02-20 as the tidied
problem box). [Er97b]

Let $f(n)$ be the smallest number of colours required to colour the edges of $K_n$ such that every
$K_4$ contains at least 5 colours. Determine the size of $f(n)$.

Remarks recorded on the page:
* Asked by Erdős and Gyárfás, who proved that $\frac56(n-1) < f(n) < n$, and that $f(9)=8$. Erdős
  believed the upper bound is closer to the truth. In fact the lower bound is: Bennett, Cushman,
  Dudek and Pralat [BCDP22] have shown that $f(n) \sim \frac56 n$. Joos and Mubayi [JoMu22] have
  found a shorter proof of this.
* See also [135].

Tags: graph theory. OEIS: "Possible". 0 comments at capture.

**Status.** SOLVED at capture. The mirror (`teorth/erdosproblems`) has `solved` since 2025-08-31.
Upstream has `erdos_136`, category `research solved`, asserting `f n / n → 5/6`, with a link to a Lean
proof in an external repository (`plby/lean-proofs`) that has not been checked here. The main theorem
below is the same asymptotic statement as the first pass's `erdos136_asymptotic`.

**What the first pass got wrong, and what this file does.** The first pass's `EdgeColoring n k` is a
function on *ordered* pairs with no symmetry, and `edgeColors` collects the colours of both orders of
every pair. A colouring with `χ x y ≠ χ y x` therefore gives every edge up to two colours, and the
first pass's `f` is not the page's $f$. It is much smaller, and all three of the first pass's
theorems are false for it. Each is proved false in Lean below (`f_first_pass` is the first pass's `f`):
* `variants.first_pass_f9_false`: an explicit 9-vertex colouring with 5 colours has at least 5 colours
  on every 4 vertices, so `f_first_pass 9 ≤ 5` and `f_first_pass 9 ≠ 8`.
* `variants.first_pass_upper`: for every $n\ge4$, `f_first_pass n ≤ 8 (⌊√n⌋ + 1)`. A counting argument
  shows that a colouring of the ordered pairs with that many colours exists.
* `variants.first_pass_bounds_false` and `variants.first_pass_asymptotic_false`: the first pass's
  bounds and asymptotic statements are false for `f_first_pass`, because it is $O(\sqrt n)$.

v2 adds the symmetry condition `∀ x y, χ x y = χ y x` to the set that defines `f`. For a symmetric
colouring the 12 ordered pairs of a 4-set give the colours of its 6 edges. The other three
definitions are unchanged.

**Encoding.**
* `EdgeColoring n k` is a function `Fin n → Fin n → Fin k`. A symmetric one is a colouring of the
  edges of $K_n$ with at most `k` colours. The diagonal values are never read.
* `edgeColors χ S` is the set of colours on the ordered pairs of distinct points of `S`.
* `IsK4FiveColored χ` says that every 4-element vertex set has at least 5 colours. It is vacuous for
  $n\le3$.
* `f n` is the least `k` for which a symmetric `χ` with `IsK4FiveColored χ` exists. The set is
  non-empty for every `n` (colour `{x,y}` by `min x y * n + max x y` in `Fin (n * n)`), and a colouring
  with colours in `Fin k` is also one in `Fin k'` for `k ≤ k'`, so `sInf` is the minimum, with no
  `sInf ∅ = 0` junk value.
* The bounds are stated for all sufficiently large `n`. The page gives no range, and a range is needed:
  an exhaustive search (a C program, not part of this file) gives $f(4)=5$, $f(5)=5$, $f(7)=7$, so
  $f(n)<n$ fails at $n=4,5,7$.
* `variants.f9_le` proves $f(9)\le8$ in Lean from an explicit colouring. The same exhaustive search
  finds no symmetric colouring of $K_9$ with 7 colours, which agrees with the page's $f(9)=8$. That
  half is not proved in Lean.
* `variants.belief_false_of_main` records that Erdős's belief ($f(n)/n \to 1$) contradicts the main
  theorem.

## References

* [Er97b] Erdős, P., _Some old and new problems in various branches of combinatorics_. Discrete
  Math. (1997), 227–231. The page's heading gives this key for the problem. The page attributes the
  bounds and $f(9)=8$ to Erdős and Gyárfás without a citation.
* [BCDP22] Bennett, P., Cushman, R., Dudek, A., Pralat, P., _The Erdős–Gyárfás function
  $f(n,4,5)=\frac56 n+o(n)$ — so Gyárfás was right_. arXiv:2207.02920 (2022).
* [JoMu22] Joos, F., Mubayi, D., _Ramsey theory constructions from hypergraph matchings_.
  arXiv:2208.12563 (2022).
* [135] The page's cross-reference.

(Provenance: [BCDP22] and [JoMu22] are from the `/latex/136` fetch in the session logs. [Er97b] is
from the bibliographies of the `/latex` pages of other problems and from upstream `136.lean`.
**DEFERRED:** whether [Er97b] states or proves the Erdős–Gyárfás bounds and $f(9)=8$ was not checked,
since the survey was not recovered. No bibliographic data was recovered for the Erdős–Gyárfás paper
in which $f(n,p,q)$ was introduced, which the page does not cite.)
-/

/-- An edge coloring of K_n with colors from Fin k, represented as a function
    on ordered pairs of vertices. -/
def EdgeColoring (n k : ℕ) : Type := Fin n → Fin n → Fin k

/-- The set of distinct colors used on edges within vertex subset S
    under coloring χ (using offDiag to enumerate all ordered pairs of
    distinct vertices in S). -/
noncomputable def edgeColors {n k : ℕ} (χ : EdgeColoring n k)
    (S : Finset (Fin n)) : Finset (Fin k) :=
  S.offDiag.image (fun p => χ p.1 p.2)

/-- A coloring χ of K_n is K₄-five-colored if every 4-element vertex subset
    has at least 5 distinct colors on its edges. -/
def IsK4FiveColored {n k : ℕ} (χ : EdgeColoring n k) : Prop :=
  ∀ S : Finset (Fin n), S.card = 4 → 5 ≤ (edgeColors χ S).card

/-- f(n): the minimum number of colors k for which there exists a K₄-five-colored edge coloring of
    K_n. The coloring must be symmetric (`χ x y = χ y x`), so that it colors the unordered pairs,
    that is, the edges of K_n. -/
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ χ : EdgeColoring n k, (∀ x y, χ x y = χ y x) ∧ IsK4FiveColored χ}

/-- The first pass's `f`, kept to state its refutations: the same minimum without the symmetry
    condition. An unordered pair can then contribute two colors to `edgeColors`. -/
noncomputable def f_first_pass (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ χ : EdgeColoring n k, IsK4FiveColored χ}

/-- Decidability of `IsK4FiveColored`, so that `decide +kernel` can check explicit colorings
    (`open Classical` would otherwise supply the stuck instance `Classical.propDecidable`). -/
instance (n k : ℕ) (χ : EdgeColoring n k) : Decidable (IsK4FiveColored χ) := by
  unfold IsK4FiveColored; infer_instance

/--
Erdős Problem #136 – asymptotic result
(Bennett–Cushman–Dudek–Pralat [BCDP22]; shorter proof by Joos–Mubayi [JoMu22]; PROVED in the
literature, not checked here):
f(n) ~ (5/6)n. That is, for every ε > 0 and all sufficiently large n,
|(f n) / n - 5/6| < ε.
-/
theorem erdos_problem_136 :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      |(f n : ℝ) / (n : ℝ) - 5 / 6| < ε :=
  sorry

/--
The bounds proved by Erdős and Gyárfás, as the page records them (PROVED, not checked here):
for all sufficiently large n, (5/6)(n-1) < f(n) < n.
-/
theorem erdos_problem_136.variants.bounds :
    ∀ᶠ n : ℕ in atTop,
      (5 : ℝ) / 6 * ((n : ℝ) - 1) < (f n : ℝ) ∧ (f n : ℝ) < (n : ℝ) :=
  sorry

/--
Special value: f(9) = 8, proved by Erdős and Gyárfás as the page records (not checked here).
-/
theorem erdos_problem_136.variants.f9 : f 9 = 8 :=
  sorry

/-- An explicit symmetric coloring of K₉ with 8 colors. -/
def sym9 : EdgeColoring 9 8 :=
  (![![0, 6, 5, 4, 1, 0, 2, 7, 3], ![6, 0, 7, 5, 0, 3, 2, 4, 1], ![5, 7, 0, 0, 6, 7, 4, 1, 2],
     ![4, 5, 0, 0, 2, 6, 3, 0, 7], ![1, 0, 6, 2, 0, 5, 7, 3, 5], ![0, 3, 7, 6, 5, 0, 1, 2, 4],
     ![2, 2, 4, 3, 7, 1, 0, 5, 0], ![7, 4, 1, 0, 3, 2, 5, 0, 6], ![3, 1, 2, 7, 5, 4, 0, 6, 0]] :
    Fin 9 → Fin 9 → Fin 8)

/-- `sym9` is symmetric (PROVED in Lean by kernel evaluation). -/
theorem erdos_problem_136.variants.sym9_symm : ∀ x y, sym9 x y = sym9 y x := by
  decide +kernel

/-- `sym9` has at least 5 colors on every 4 vertices (PROVED in Lean by kernel evaluation). -/
theorem erdos_problem_136.variants.sym9_ok : IsK4FiveColored sym9 := by
  decide +kernel

/--
The upper half of `f 9 = 8` (PROVED in Lean): `sym9` is a symmetric K₄-five-colored coloring of K₉
with 8 colors.
-/
theorem erdos_problem_136.variants.f9_le : f 9 ≤ 8 :=
  Nat.sInf_le ⟨sym9, erdos_problem_136.variants.sym9_symm, erdos_problem_136.variants.sym9_ok⟩

/--
Erdős's belief that the upper bound is closer to the truth, read as `f n / n → 1`, contradicts the
asymptotic result (PROVED in Lean, with the asymptotic result as hypothesis): the two limits 5/6
and 1 cannot both hold.
-/
theorem erdos_problem_136.variants.belief_false_of_main
    (hmain : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, |(f n : ℝ) / (n : ℝ) - 5 / 6| < ε) :
    ¬ ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, |(f n : ℝ) / (n : ℝ) - 1| < ε := by
  intro h
  obtain ⟨n, h1, h2⟩ := ((hmain (1 / 12) (by norm_num)).and (h (1 / 12) (by norm_num))).exists
  have h3 := (abs_lt.mp h1).2
  have h4 := (abs_lt.mp h2).1
  linarith

/--
Counting step (PROVED in Lean): the number of maps from the ordered pairs of `Fin n` to `Fin k` that
send the 12 ordered pairs of a 4-set `S` into a 4-set `T` of colors is `4 ^ 12 * k ^ (n * n - 12)`.
-/
theorem erdos_problem_136.card_boxed (n k : ℕ) (S : Finset (Fin n)) (hS : S.card = 4)
    (T : Finset (Fin k)) (hT : T.card = 4) :
    (Fintype.piFinset (fun p : Fin n × Fin n => if p ∈ S.offDiag then T else Finset.univ)).card
      = 4 ^ 12 * k ^ (n * n - 12) := by
  rw [Fintype.card_piFinset]
  have h1 : ∀ p : Fin n × Fin n,
      (if p ∈ S.offDiag then T else (Finset.univ : Finset (Fin k))).card
        = if p ∈ S.offDiag then 4 else k := by
    intro p
    split_ifs <;> simp [hT]
  simp only [h1]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hO : S.offDiag.card = 12 := by
    rw [Finset.offDiag_card, hS]
  have hf1 : (Finset.univ.filter (fun p : Fin n × Fin n => p ∈ S.offDiag)).card = 12 := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hO]
  have hf2 : (Finset.univ.filter (fun p : Fin n × Fin n => ¬ p ∈ S.offDiag)).card
      = n * n - 12 := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n × Fin n)))
      (fun p => p ∈ S.offDiag)
    rw [hf1, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
    omega
  rw [hf1, hf2]

/--
First-moment bound (PROVED in Lean): if `n ^ 4 * k ^ 4 * 4 ^ 12 < k ^ 12`, some coloring of the
ordered pairs of `Fin n` with `k` colors has at least 5 colors on every 4 vertices. There are at most
`C(n,4) * C(k,4) * 4 ^ 12 * k ^ (n * n - 12)` maps that send the 12 ordered pairs of some 4-set into
some 4-set of colors, which is fewer than the `k ^ (n * n)` maps in all.
-/
theorem erdos_problem_136.exists_ordered_colouring (n k : ℕ) (hk : 4 ≤ k) (hn : 4 ≤ n)
    (h : n ^ 4 * k ^ 4 * 4 ^ 12 < k ^ 12) :
    ∃ χ : EdgeColoring n k, IsK4FiveColored χ := by
  let B : Finset (Fin n) → Finset (Fin k) → Finset (Fin n × Fin n → Fin k) :=
    fun S T => Fintype.piFinset (fun p : Fin n × Fin n => if p ∈ S.offDiag then T else Finset.univ)
  let I : Finset (Finset (Fin n) × Finset (Fin k)) :=
    (Finset.univ.powersetCard 4) ×ˢ (Finset.univ.powersetCard 4)
  have hI : I.card = n.choose 4 * k.choose 4 := by
    simp [I, Finset.card_product, Finset.card_powersetCard]
  have hcard : ∀ x ∈ I, (B x.1 x.2).card = 4 ^ 12 * k ^ (n * n - 12) := by
    intro x hx
    simp only [I, Finset.mem_product, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hx
    exact erdos_problem_136.card_boxed n k x.1 hx.1 x.2 hx.2
  have hsum : (I.biUnion (fun x => B x.1 x.2)).card
      ≤ n.choose 4 * k.choose 4 * (4 ^ 12 * k ^ (n * n - 12)) := by
    refine le_trans Finset.card_biUnion_le ?_
    rw [Finset.sum_congr rfl hcard, Finset.sum_const, hI, smul_eq_mul]
  have hnn : 12 ≤ n * n := by nlinarith
  have hpow : k ^ (n * n) = k ^ 12 * k ^ (n * n - 12) := by
    rw [← pow_add]; congr 1; omega
  have hkpos : 0 < k ^ (n * n - 12) := by positivity
  have hlt : (I.biUnion (fun x => B x.1 x.2)).card < k ^ (n * n) := by
    refine lt_of_le_of_lt hsum ?_
    rw [hpow]
    have h1 : n.choose 4 * k.choose 4 * 4 ^ 12 < k ^ 12 := by
      refine lt_of_le_of_lt ?_ h
      have := Nat.choose_le_pow n 4
      have := Nat.choose_le_pow k 4
      calc n.choose 4 * k.choose 4 * 4 ^ 12 ≤ n ^ 4 * k ^ 4 * 4 ^ 12 := by gcongr
        _ = _ := rfl
    calc n.choose 4 * k.choose 4 * (4 ^ 12 * k ^ (n * n - 12))
        = (n.choose 4 * k.choose 4 * 4 ^ 12) * k ^ (n * n - 12) := by ring
      _ < k ^ 12 * k ^ (n * n - 12) := by gcongr
  have hex : ∃ ψ : Fin n × Fin n → Fin k, ψ ∉ I.biUnion (fun x => B x.1 x.2) := by
    by_contra hcon
    push_neg at hcon
    have : (I.biUnion (fun x => B x.1 x.2)) = Finset.univ := Finset.eq_univ_iff_forall.mpr hcon
    rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨ψ, hψ⟩ := hex
  refine ⟨Function.curry ψ, ?_⟩
  intro S hS
  by_contra hlt5
  push_neg at hlt5
  have hcol : edgeColors (Function.curry ψ) S = S.offDiag.image ψ := by
    unfold edgeColors
    simp [Function.curry]
  obtain ⟨T, hsub, hT⟩ := Finset.exists_superset_card_eq (s := edgeColors (Function.curry ψ) S)
    (n := 4) (by omega) (by simpa using hk)
  apply hψ
  rw [Finset.mem_biUnion]
  refine ⟨(S, T), ?_, ?_⟩
  · simp [I, Finset.mem_product, Finset.mem_powersetCard, hS, hT]
  · simp only [B, Fintype.mem_piFinset]
    intro p
    split_ifs with hp
    · apply hsub
      rw [hcol]
      exact Finset.mem_image_of_mem _ hp
    · exact Finset.mem_univ _

/--
The first pass's `f` is $O(\sqrt n)$ (PROVED in Lean): for every `n ≥ 4`,
`f_first_pass n ≤ 8 * (⌊√n⌋ + 1)`. With `k = 8 * (⌊√n⌋ + 1)` one has `n < (k / 8) ^ 2`, hence
`n ^ 4 * k ^ 4 * 4 ^ 12 < k ^ 12`, and the first-moment bound applies.
-/
theorem erdos_problem_136.variants.first_pass_upper (n : ℕ) (hn : 4 ≤ n) :
    f_first_pass n ≤ 8 * (Nat.sqrt n + 1) := by
  have hk : 4 ≤ 8 * (Nat.sqrt n + 1) := by omega
  have hlt : n < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
  have h4 : n ^ 4 < ((Nat.sqrt n + 1) ^ 2) ^ 4 := Nat.pow_lt_pow_left hlt (by norm_num)
  have h : n ^ 4 * (8 * (Nat.sqrt n + 1)) ^ 4 * 4 ^ 12 < (8 * (Nat.sqrt n + 1)) ^ 12 := by
    calc n ^ 4 * (8 * (Nat.sqrt n + 1)) ^ 4 * 4 ^ 12
        < ((Nat.sqrt n + 1) ^ 2) ^ 4 * (8 * (Nat.sqrt n + 1)) ^ 4 * 4 ^ 12 := by gcongr
      _ = (8 * (Nat.sqrt n + 1)) ^ 12 := by ring
  exact Nat.sInf_le (erdos_problem_136.exists_ordered_colouring n _ hk hn h)

/--
The first pass's bounds theorem is false (PROVED in Lean): with `f_first_pass` in place of `f`, the
statement "for all large `n`, `(5/6)(n-1) < f n < n`" fails, because `f_first_pass n` is $O(\sqrt n)$.
-/
theorem erdos_problem_136.variants.first_pass_bounds_false :
    ¬ (∀ᶠ n : ℕ in atTop,
      (5 : ℝ) / 6 * ((n : ℝ) - 1) < (f_first_pass n : ℝ) ∧ (f_first_pass n : ℝ) < (n : ℝ)) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  set n := max N 400 with hn
  have hnN : N ≤ n := le_max_left _ _
  have hn400 : 400 ≤ n := le_max_right _ _
  have h1 := (hN n hnN).1
  have h2 : (f_first_pass n : ℝ) ≤ 8 * ((Nat.sqrt n : ℝ) + 1) := by
    exact_mod_cast erdos_problem_136.variants.first_pass_upper n (by omega)
  have hs20 : 20 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hs20' : (20 : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast hs20
  have hsq' : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsq
  nlinarith

/--
The first pass's asymptotic theorem is false (PROVED in Lean): with `f_first_pass` in place of `f`,
`|f n / n - 5/6| < ε` fails for `ε = 1/2` and all large `n`, because `f_first_pass n / n → 0`.
-/
theorem erdos_problem_136.variants.first_pass_asymptotic_false :
    ¬ (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      |(f_first_pass n : ℝ) / (n : ℝ) - 5 / 6| < ε) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h (1 / 2) (by norm_num))
  set n := max N 900 with hn
  have hnN : N ≤ n := le_max_left _ _
  have hn900 : 900 ≤ n := le_max_right _ _
  have h1 := hN n hnN
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h2 : (f_first_pass n : ℝ) ≤ 8 * ((Nat.sqrt n : ℝ) + 1) := by
    exact_mod_cast erdos_problem_136.variants.first_pass_upper n (by omega)
  have hs30 : 30 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hs30' : (30 : ℝ) ≤ (Nat.sqrt n : ℝ) := by exact_mod_cast hs30
  have hsq' : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsq
  have h3 : (1 : ℝ) / 3 < (f_first_pass n : ℝ) / (n : ℝ) := by
    have := (abs_lt.mp h1).1
    linarith
  rw [lt_div_iff₀ hnpos] at h3
  nlinarith

/-- An explicit coloring of K₉ with 5 colors, not symmetric. -/
def asym9 : EdgeColoring 9 5 :=
  (![![0, 1, 4, 3, 2, 0, 4, 2, 2], ![0, 0, 3, 3, 4, 0, 2, 2, 0], ![2, 4, 0, 1, 4, 3, 0, 2, 2],
     ![4, 2, 0, 0, 3, 2, 1, 4, 2], ![3, 1, 0, 0, 0, 3, 2, 1, 4], ![1, 2, 3, 0, 0, 0, 0, 2, 1],
     ![0, 3, 1, 0, 4, 4, 0, 4, 1], ![4, 1, 3, 1, 0, 3, 1, 0, 3], ![3, 0, 1, 4, 1, 4, 3, 0, 0]] :
    Fin 9 → Fin 9 → Fin 5)

/-- `asym9` has at least 5 colors on every 4 vertices, counting both orders of each pair (PROVED in
Lean by kernel evaluation). -/
theorem erdos_problem_136.variants.asym9_ok : IsK4FiveColored asym9 := by
  decide +kernel

/--
The first pass's `f 9 = 8` is false (PROVED in Lean): `asym9` shows `f_first_pass 9 ≤ 5`.
-/
theorem erdos_problem_136.variants.first_pass_f9_false : f_first_pass 9 ≠ 8 := by
  have h : f_first_pass 9 ≤ 5 :=
    Nat.sInf_le ⟨asym9, erdos_problem_136.variants.asym9_ok⟩
  omega

end
