-- [AI - Claude Sonnet 5.5]: Erdős Problem 138 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Real Classical
open scoped Topology

/-!
# Erdős Problem #138: The Growth of the van der Waerden Number W(k)

*Source:* [erdosproblems.com/138](https://www.erdosproblems.com/138) (banner **OPEN**, prize
**\$500**: "This is open, and cannot be resolved with a finite computation."; page last edited
28 December 2025; captured 2026-03-05 as the tidied problem box). [Er57] [Er61] [Er73] [Er74b]
[Er75b] [Er77c] [ErGr79] [Er80] [ErGr80] [Er81] [Er97c]

Let the van der Waerden number $W(k)$ be such that whenever $N\geq W(k)$ and $\{1,\ldots,N\}$ is
$2$-coloured there must exist a monochromatic $k$-term arithmetic progression. Improve the bounds
for $W(k)$ - for example, prove that $W(k)^{1/k}\to \infty$.

Remarks recorded on the page:
* When $p$ is prime Berlekamp [Be68] has proved $W(p+1)\geq p2^p$. Gowers [Go01] has proved
  $W(k) \leq 2^{2^{2^{2^{2^{k+9}}}}}$. The best general lower bound is $W(k)\gg 2^k$, due to Kozik
  and Shabanov [KoSh16].
* In [Er81] Erdős further asks whether $W(k+1)/W(k)\to \infty$, or $W(k+1)-W(k)\to \infty$.
* In [Er80] Erdős asks whether $W(k)/2^k\to \infty$, and offers \$500 for a proof or disproof of
  $W(k)^{1/k}\to \infty$.

Tags: additive combinatorics. OEIS: A005346. 4 comments at capture (not captured).

**Status.** OPEN. The mirror (`teorth/erdosproblems`) has `open` since 2025-08-31 with prize \$500.
Upstream has `erdos_138 : answer(sorry) ↔ …` for the main question, category `research open`. Upstream
also records two of the further questions as solved *after* the capture: $W(k)/2^k\to\infty$
(attributed to Campos–Fox–Schildkraut, who prove $W(k)\ge(1-o(1))k2^{k-1}$) and
$W(k+1)-W(k)\to\infty$ (a DeepMind prover agent), each with a link to a Lean proof. Neither was
checked here. Neither settles the main question, because $W(k)^{1/k}\to\infty$ implies
$W(k)/2^k\to\infty$ (`variants.er80_of_main`) and not conversely.

**What the first pass got wrong, and what this file does.** The first pass declared van der
Waerden's theorem as `axiom vanDerWaerden` and defined `W` from it with `Nat.find`. The axiom is a true
theorem, but it is an axiom: every statement about `W`, including the main theorem, depended on it, and
the compiler does not report that. This file replaces it by a theorem with the same name and
statement, proved from Mathlib's `Combinatorics.exists_mono_homothetic_copy` (the infinite form, a
consequence of the Hales–Jewett theorem) by a compactness argument. `HasMonoArithProg`,
`VanDerWaerdenProp`, `W` and the main statement are unchanged.

**Encoding.**
* `HasMonoArithProg c N k` says there are $a$ and $d>0$ such that $a,a+d,\dots,a+(k-1)d$ lie in
  $\{0,\dots,N-1\}$ and have one colour. The page uses $\{1,\dots,N\}$, and a shift by one changes
  nothing. For $k=0$ the term `k - 1` truncates and the condition reduces to `a < N`, so `W 0 = 1`
  where the empty progression would give $0$. That is irrelevant to the asymptotic statements. For
  $k\ge1$ the definition is exact.
* `VanDerWaerdenProp k N` quantifies over all `c : ℕ → Bool`. Only the values on `{0,…,N-1}` matter, and
  the property is monotone in `N` (`mono`), so `W k` is the least such `N` and the page's "whenever
  $N\ge W(k)$" holds.
* `W k` is `Nat.find` of the existence theorem. `variants.W_one`, `variants.W_two` and
  `variants.W_three` prove $W(1)=1$, $W(2)=3$ and $W(3)=9$ in Lean. The last is the known value and fixes
  the off-by-one in `a + (k - 1) * d < N`.
* The main theorem is the page's example, $W(k)^{1/k}\to\infty$, with real powers. The page's open-ended
  "improve the bounds" is not a statement, and is covered by the variants.
* `variants.berlekamp`, `variants.gowers` and `variants.kozik_shabanov` are the bounds on the page.
  `variants.er80` and `variants.er81_ratio`, `variants.er81_difference` are Erdős's further questions,
  asserted in the asked direction.

## References

* [Er57] Erdős, P., _Some unsolved problems_. Michigan Math. J. (1957), 291–300.
* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221–254.
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. In: A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117–138.
* [Er74b] Erdős, P., _Remarks on some problems in number theory_. Math. Balkanica (1974), 197–202.
* [Er75b] Erdős, P., _Problems and results in combinatorial number theory_. Journées Arithmétiques de
  Bordeaux (Conf., Univ. Bordeaux, 1974) (1975), 295–310.
* [Er77c] Erdős, P., _Problems and results on combinatorial number theory. III_. Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72.
* [Er80] Erdős, P., _A survey of problems in combinatorial number theory_. Ann. Discrete Math. (1980),
  89–115.
* [ErGr80] Erdős, P., Graham, R., _Old and new problems and results in combinatorial number theory_.
  Monographies de L'Enseignement Mathématique (1980).
* [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25–42.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. In: The mathematics of Paul Erdős, I
  (1997), 47–67.
* [Be68] Berlekamp, E. R., _A construction for partitions which avoid long arithmetic progressions_.
  Canad. Math. Bull. (1968), 409–414.
* [Go01] Gowers, W. T., _A new proof of Szemerédi's theorem_. Geom. Funct. Anal. (2001), 465–588.
* [ErGr79], [KoSh16]: cited on the page. **DEFERRED:** no bibliographic data was recovered.

(Provenance: [Er57] to [Er97c] and [Be68] are from the bibliographies of the `/latex` pages of other
problems, and [Go01] is from upstream `138.lean`. **DEFERRED:** no `/latex/138` fetch exists in the
logs, so the entries were not checked against the page's own bibliography.)
-/

/--
A monochromatic k-term arithmetic progression exists in a 2-coloring c of
{0, …, N-1}: there exist a, d with d > 0 such that a, a+d, …, a+(k-1)d are
all in {0, …, N-1} and all receive the same color.
-/
def HasMonoArithProg (c : ℕ → Bool) (N k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < N ∧
    ∀ i : ℕ, i < k → c (a + i * d) = c a

/--
The van der Waerden property: N is large enough that every 2-coloring of
{0, …, N-1} contains a monochromatic k-term arithmetic progression.
-/
def VanDerWaerdenProp (k N : ℕ) : Prop :=
  ∀ c : ℕ → Bool, HasMonoArithProg c N k

/--
Van der Waerden's theorem (PROVED in Lean): for every k there exists N such that
VanDerWaerdenProp k N holds. The first pass declared this as an `axiom`. Here it follows from
Mathlib's `Combinatorics.exists_mono_homothetic_copy`, the infinite form of the theorem, by
compactness: if for every N some coloring had no monochromatic k-term progression in {0, …, N-1}, a
cluster point of these colorings in the compact space `ℕ → Bool` would have none at all.
-/
theorem vanDerWaerden (k : ℕ) : ∃ N : ℕ, VanDerWaerdenProp k N := by
  by_contra hcon
  push_neg at hcon
  have hc : ∀ N : ℕ, ∃ c : ℕ → Bool, ¬ HasMonoArithProg c N k := by
    intro N
    have h := hcon N
    unfold VanDerWaerdenProp at h
    push_neg at h
    exact h
  choose c hc using hc
  haveI : (Filter.map c atTop).NeBot := Filter.map_neBot
  obtain ⟨x, hx⟩ := exists_clusterPt_of_compactSpace (Filter.map c atTop)
  obtain ⟨d, hd, b, col, hb⟩ := Combinatorics.exists_mono_homothetic_copy (Finset.range k) x
  have hU : ∀ᶠ y in 𝓝 x, ∀ s ∈ Finset.range k, y (d • s + b) = x (d • s + b) := by
    rw [Filter.eventually_all_finset]
    intro s _
    have h := (continuous_apply (d • s + b)).tendsto x
    rw [nhds_discrete Bool] at h
    exact tendsto_pure.mp h
  have hfreq : ∃ᶠ N in atTop, ∀ s ∈ Finset.range k, c N (d • s + b) = x (d • s + b) :=
    (mapClusterPt_iff_frequently.mp hx) _ hU
  obtain ⟨N, hN, hNge⟩ := (hfreq.and_eventually (eventually_ge_atTop (b + (k - 1) * d + 1))).exists
  apply hc N
  refine ⟨b, d, hd, by omega, ?_⟩
  intro i hi
  have key : ∀ s : ℕ, d • s + b = b + s * d := by
    intro s
    have : d • s = d * s := rfl
    rw [this, Nat.mul_comm, Nat.add_comm]
  have h1 := hN i (Finset.mem_range.mpr hi)
  have h0 := hN 0 (Finset.mem_range.mpr (by omega))
  have e1 := hb i (Finset.mem_range.mpr hi)
  have e0 := hb 0 (Finset.mem_range.mpr (by omega))
  rw [key] at h1 e1 h0 e0
  simp only [Nat.zero_mul, Nat.add_zero] at h0 e0
  calc c N (b + i * d) = x (b + i * d) := h1
    _ = col := e1
    _ = x b := e0.symm
    _ = c N b := h0.symm

/--
The van der Waerden number W(k): the smallest N such that every 2-coloring
of {0, …, N-1} contains a monochromatic k-term arithmetic progression.
-/
noncomputable def W (k : ℕ) : ℕ :=
  Nat.find (vanDerWaerden k)

/--
Erdős Problem #138 [Er57, Er61, Er73, Er74b, Er75b, Er77c, ErGr79, Er80, ErGr80, Er81, Er97c] —
OPEN (\$500):

Let W(k) be the van der Waerden number, the smallest N such that every
2-coloring of {1, …, N} contains a monochromatic k-term arithmetic progression.
Prove that W(k)^{1/k} → ∞ as k → ∞.

Erdős offered $500 for a proof or disproof [Er80]. The best known upper bound is a
tower of exponentials due to Gowers (2001) [Go01], while the best lower bound is
W(k) ≫ 2^k due to Kozik and Shabanov (2016) [KoSh16].
-/
theorem erdos_problem_138 :
    Tendsto (fun k => (W k : ℝ) ^ ((1 : ℝ) / (k : ℝ))) atTop atTop :=
  sorry

/-- The van der Waerden property is monotone in `N` (PROVED in Lean). -/
theorem erdos_problem_138.mono {k N N' : ℕ} (h : VanDerWaerdenProp k N) (hle : N ≤ N') :
    VanDerWaerdenProp k N' := by
  intro c
  obtain ⟨a, d, hd, hlt, hmono⟩ := h c
  exact ⟨a, d, hd, lt_of_lt_of_le hlt hle, hmono⟩

/--
If `n` has the van der Waerden property and `n - 1` does not, then `W k = n` (PROVED in Lean).
-/
theorem erdos_problem_138.W_eq_of {k n : ℕ} (h1 : VanDerWaerdenProp k n)
    (h2 : ¬ VanDerWaerdenProp k (n - 1)) : W k = n := by
  unfold W
  rw [Nat.find_eq_iff]
  refine ⟨h1, fun m hm hP => h2 ?_⟩
  exact erdos_problem_138.mono hP (by omega)

/-- Extend a coloring of `Fin n` to `ℕ`, with the color `false` outside `Fin n`. -/
def erdos_problem_138.extN (n : ℕ) (f : Fin n → Bool) (m : ℕ) : Bool :=
  if h : m < n then f ⟨m, h⟩ else false

/--
A finite check suffices for the van der Waerden property (PROVED in Lean): if every coloring of
`Fin n` has a monochromatic `k`-term progression with `a, d < n`, then `n` has the property.
-/
theorem erdos_problem_138.P_of_fin (k n : ℕ)
    (h : ∀ f : Fin n → Bool, ∃ a < n, ∃ d < n, 0 < d ∧ a + (k - 1) * d < n ∧
      ∀ i < k, erdos_problem_138.extN n f (a + i * d) = erdos_problem_138.extN n f a) :
    VanDerWaerdenProp k n := by
  intro c
  obtain ⟨a, ha, d, hd', hd, hlt, hmono⟩ := h (fun i => c i)
  refine ⟨a, d, hd, hlt, fun i hi => ?_⟩
  have hi' : a + i * d < n := by
    refine lt_of_le_of_lt ?_ hlt
    have : i ≤ k - 1 := by omega
    have := Nat.mul_le_mul_right d this
    omega
  have := hmono i hi
  simp only [erdos_problem_138.extN, dif_pos hi', dif_pos ha] at this
  exact this

/--
An explicit coloring shows that `n` lacks the property (PROVED in Lean): if no `k`-term progression
with `a, d < n` is monochromatic under `c`, and `k ≥ 2`, then `n` does not have the property.
-/
theorem erdos_problem_138.not_P_of_col (k n : ℕ) (hk : 2 ≤ k) (c : ℕ → Bool)
    (h : ∀ a < n, ∀ d < n, 0 < d → a + (k - 1) * d < n → ¬ ∀ i < k, c (a + i * d) = c a) :
    ¬ VanDerWaerdenProp k n := by
  intro hP
  obtain ⟨a, d, hd, hlt, hm⟩ := hP c
  have h1 : (1 : ℕ) ≤ k - 1 := by omega
  have h2 : d ≤ (k - 1) * d := by nlinarith
  exact h a (by omega) d (by omega) hd hlt hm

/-- $W(1)=1$ (PROVED in Lean). -/
theorem erdos_problem_138.variants.W_one : W 1 = 1 := by
  refine erdos_problem_138.W_eq_of ?_ ?_
  · intro c
    refine ⟨0, 1, by norm_num, by norm_num, ?_⟩
    intro i hi
    have : i = 0 := by omega
    subst this
    simp
  · intro h
    obtain ⟨a, d, hd, hlt, _⟩ := h (fun _ => true)
    simp at hlt

/-- $W(2)=3$ (PROVED in Lean by kernel evaluation). -/
theorem erdos_problem_138.variants.W_two : W 2 = 3 := by
  refine erdos_problem_138.W_eq_of ?_ ?_
  · refine erdos_problem_138.P_of_fin 2 3 ?_
    decide +kernel
  · refine erdos_problem_138.not_P_of_col 2 2 le_rfl (fun i => decide (i % 2 = 0)) ?_
    decide +kernel

/--
$W(3)=9$ (PROVED in Lean by kernel evaluation over the 512 colorings of `Fin 9`). This is the known
value, and it fixes the off-by-one in the definition of `HasMonoArithProg`: the coloring `RRBBRRBB`
has no monochromatic 3-term progression in `{0, …, 7}`.
-/
theorem erdos_problem_138.variants.W_three : W 3 = 9 := by
  refine erdos_problem_138.W_eq_of ?_ ?_
  · refine erdos_problem_138.P_of_fin 3 9 ?_
    decide +kernel
  · refine erdos_problem_138.not_P_of_col 3 8 (by norm_num) (fun i => decide ((i / 2) % 2 = 0)) ?_
    decide +kernel

/--
Berlekamp [Be68] (PROVED, not checked here): for a prime `p`, `W(p+1) ≥ p 2^p`.
-/
theorem erdos_problem_138.variants.berlekamp :
    ∀ p : ℕ, p.Prime → p * 2 ^ p ≤ W (p + 1) :=
  sorry

/--
Gowers [Go01] (PROVED, not checked here): `W(k) ≤ 2^2^2^2^2^(k+9)`.
-/
theorem erdos_problem_138.variants.gowers :
    ∀ k : ℕ, W k ≤ 2 ^ 2 ^ 2 ^ 2 ^ 2 ^ (k + 9) :=
  sorry

/--
Kozik and Shabanov [KoSh16], as the page words it (PROVED, not checked here): `W(k) ≫ 2^k`, that is,
`W(k) ≥ c 2^k` for a constant `c > 0` and all `k`.
-/
theorem erdos_problem_138.variants.kozik_shabanov :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, c * 2 ^ k ≤ (W k : ℝ) :=
  sorry

/--
Erdős's question [Er80] (OPEN at capture; upstream records it as solved after the capture, which was
not checked here): does `W(k) / 2^k → ∞`? Asserted in the asked direction.
-/
theorem erdos_problem_138.variants.er80 :
    Tendsto (fun k : ℕ => (W k : ℝ) / 2 ^ k) atTop atTop :=
  sorry

/--
Erdős's question [Er81] (OPEN): does `W(k+1) / W(k) → ∞`? Asserted in the asked direction.
-/
theorem erdos_problem_138.variants.er81_ratio :
    Tendsto (fun k : ℕ => (W (k + 1) : ℝ) / (W k : ℝ)) atTop atTop :=
  sorry

/--
Erdős's question [Er81] (OPEN at capture; upstream records it as solved after the capture, which was
not checked here): does `W(k+1) - W(k) → ∞`? Asserted in the asked direction.
-/
theorem erdos_problem_138.variants.er81_difference :
    Tendsto (fun k : ℕ => (W (k + 1) : ℝ) - (W k : ℝ)) atTop atTop :=
  sorry

/--
The main statement implies Erdős's question [Er80] (PROVED in Lean): if `W(k)^{1/k} → ∞` then
`W(k) / 2^k → ∞`. For large `k`, `W(k)^{1/k} ≥ 2M` gives `W(k) ≥ (2M)^k ≥ 2^k M`.
-/
theorem erdos_problem_138.variants.er80_of_main
    (h : Tendsto (fun k => (W k : ℝ) ^ ((1 : ℝ) / (k : ℝ))) atTop atTop) :
    Tendsto (fun k : ℕ => (W k : ℝ) / 2 ^ k) atTop atTop := by
  rw [tendsto_atTop] at h ⊢
  intro M
  have hM1 : (1 : ℝ) ≤ max M 1 := le_max_right _ _
  filter_upwards [h (2 * max M 1), eventually_ge_atTop 1] with k hk hk1
  have hW : (0 : ℝ) ≤ (W k : ℝ) := Nat.cast_nonneg _
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have e : ((W k : ℝ) ^ ((1 : ℝ) / (k : ℝ))) ^ k = (W k : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW, one_div, inv_mul_cancel₀ hkpos.ne', Real.rpow_one]
  have h1 : (2 * max M 1) ^ k ≤ (W k : ℝ) := by
    rw [← e]
    exact pow_le_pow_left₀ (by positivity) hk k
  have h2 : max M 1 ≤ (max M 1) ^ k := le_self_pow₀ hM1 (by omega)
  have h3 : (0 : ℝ) < 2 ^ k := by positivity
  rw [mul_pow] at h1
  rw [le_div_iff₀ h3]
  calc M * 2 ^ k ≤ max M 1 * 2 ^ k := by gcongr; exact le_max_left _ _
    _ ≤ (max M 1) ^ k * 2 ^ k := by gcongr
    _ = 2 ^ k * (max M 1) ^ k := by ring
    _ ≤ W k := h1
