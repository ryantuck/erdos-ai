-- [AI - Claude Opus 5.5]: Erdős Problem 179 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat


/-!
# Erdős Problem #179

*Source:* [erdosproblems.com/179](https://www.erdosproblems.com/179) (status **PROVED**: "This has
been solved in the affirmative."; captured 2026-02-20). [Er73] [Er75b] [ErGr79] [ErGr80]

Let $1\leq k<\ell$ be integers and define $F_k(N,\ell)$ to be minimal such that every set
$A\subset \mathbb{N}$ of size $N$ which contains at least $F_k(N,\ell)$ many $k$-term arithmetic
progressions must contain an $\ell$-term arithmetic progression. Find good upper bounds for
$F_k(N,\ell)$. Is it true that $F_3(N,4)=o(N^2)$? Is it true that for every $\ell>3$
$\lim_{N\to \infty}\frac{\log F_3(N,\ell)}{\log N}=2$?

Remarks recorded on the page (abridged): Erdős remarks the upper bound $o(N^2)$ is certainly false
for $\ell>\epsilon\log N$. The answer is yes: Fox and Pohoata [FoPo20] have shown that, for all
fixed $1\leq k<\ell$, $F_k(N,\ell)=N^{2-o(1)}$ and in fact
$F_k(N,\ell)\leq N^2/(\log\log N)^{C_\ell}$ for some constant $C_\ell>0$, with bounds in terms
of $r_\ell(N)$. The bounds of Leng, Sah and Sawhney [LSS24] imply
$F_k(N,\ell)\leq N^2/\exp((\log\log N)^{c_\ell})$.

## Encoding notes

* Both yes/no questions are answered yes; part 1 asserts $F_3(N,4)=o(N^2)$ directly, and part 2
  asserts the nontrivial half of the limit: an $\ell$-AP-free $N$-set with at least $N^{2-\varepsilon}$
  three-term progressions. The other half is trivial: an `N`-set has at most `N²` such progressions
  (`numAP_le_sq`, PROVED). "Find good upper bounds" has no formal target.
* `numAP A k` counts pairs `(a, d)`, `d ≥ 1`, with `a, a + d, …, a + (k - 1) d ∈ A`. For `k ≥ 2` this is
  the number of `k`-term progressions (`numAP_examples`, PROVED by `decide`). For `k = 1` it is
  `|A| · max A`, not `|A|` (`numAP_one_example`); only `k = 3` is used.

## References

From the site's `/latex/179` bibliography:
* [FoPo20] Fox, J. and Pohoata, C., _Sets without k-term progressions can have many shorter
  progressions_. arXiv:1908.09905 (2020).
* [LSS24] Leng, J., Sah, A. and Sawhney, M., _Improved bounds for Szemerédi's theorem_.
  arXiv:2402.17995 (2024).

Erdős's sources:
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of combinatorial
  theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971) (1973),
  117–138. (Site `/latex/783` and others.)
* [Er75b] Erdős, P., _Problems and results in combinatorial number theory_. Journées Arithmétiques
  de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295–310. (Site `/latex/656` and
  others.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/179.lean` (Opus 5.5 review, `opus-5-5-review/179.md`).
-/

open Finset

/--
A finite set of natural numbers contains a k-term arithmetic progression
if there exist natural numbers a and d with d ≥ 1 such that
a + i * d ∈ A for all 0 ≤ i < k.
-/
def ContainsAP (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d ≥ 1 ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

/--
The number of k-term arithmetic progressions in A, counted as pairs (a, d)
with d ≥ 1 such that a + i * d ∈ A for all 0 ≤ i < k.
-/
def numAP (A : Finset ℕ) (k : ℕ) : ℕ :=
  if h : A.Nonempty then
    let M := A.max' h
    ((Finset.Icc 0 M ×ˢ Finset.Icc 1 M).filter
      fun p => ∀ i ∈ Finset.range k, p.1 + i * p.2 ∈ A).card
  else 0

/--
Erdős Problem #179, Part 1:
Let 1 ≤ k < ℓ be integers and define F_k(N, ℓ) to be the minimum number of
k-term arithmetic progressions that an N-element set A ⊆ ℕ must contain to
guarantee an ℓ-term arithmetic progression. Is it true that F_3(N, 4) = o(N²)?

Proved by Fox and Pohoata [FoPo20]. (Status: PROVED; the true direction.)
-/
theorem erdos_problem_179_part1 :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    ∀ A : Finset ℕ, A.card = N →
    (numAP A 3 : ℝ) ≥ ε * (N : ℝ) ^ 2 →
    ContainsAP A 4 :=
  sorry

/--
Erdős Problem #179, Part 2:
For every ℓ > 3, lim_{N→∞} log F_3(N,ℓ) / log N = 2.
The nontrivial direction: for every ε > 0, for sufficiently large N,
there exists an N-element set with at least N^(2-ε) three-term arithmetic
progressions but no ℓ-term arithmetic progression.

Proved by Fox and Pohoata [FoPo20]. (Status: PROVED; the true direction.)
-/
theorem erdos_problem_179_part2 :
    ∀ ℓ : ℕ, ℓ > 3 → ∀ ε : ℝ, ε > 0 → ε < 2 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    ∃ A : Finset ℕ, A.card = N ∧
    (numAP A 3 : ℝ) ≥ (N : ℝ) ^ (2 - ε) ∧
    ¬ContainsAP A ℓ :=
  sorry

/-- An `N`-set has at most `N²` progressions of length `k ≥ 2`: `(a, d) ↦ (a, a + d)` is injective
into `A × A` (PROVED in Lean). So $\log F_3(N,\ell)\le2\log N+O(1)$ is trivial. -/
theorem erdos_problem_179.numAP_le_sq (A : Finset ℕ) {k : ℕ} (hk : 2 ≤ k) : numAP A k ≤ A.card ^ 2 := by
  unfold numAP
  split_ifs with h
  · simp only
    rw [sq, ← Finset.card_product]
    apply Finset.card_le_card_of_injOn (fun p => (p.1, p.1 + p.2))
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      have h0 := hp.2 0 (Finset.mem_range.mpr (by omega))
      have h1 := hp.2 1 (Finset.mem_range.mpr (by omega))
      simp only [zero_mul, add_zero, one_mul] at h0 h1
      exact Finset.mem_product.mpr ⟨h0, h1⟩
    · intro p _ q _ hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 (by omega)
  · exact Nat.zero_le _

/-- `numAP` counts progressions for `k = 3` (PROVED by `decide`): `{0,1,2,3}` has two 3-term
progressions, `{0,2,4}` one, `{0,1,3}` none. -/
theorem erdos_problem_179.numAP_examples : numAP {0, 1, 2, 3} 3 = 2 ∧ numAP {0, 2, 4} 3 = 1 ∧
    numAP {0, 1, 3} 3 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- For `k = 1`, `numAP A 1 = |A| · max A`: here `numAP {5} 1 = 5`, not `1` (PROVED by `decide`). -/
theorem erdos_problem_179.numAP_one_example : numAP {5} 1 = 5 := by decide

/-- Fox and Pohoata [FoPo20] (SOLVED; not proved here): for fixed `2 ≤ k < ℓ` there is `C > 0` with
$F_k(N,\ell)\le N^2/(\log\log N)^{C}$ for large `N`. -/
theorem erdos_problem_179.variants.fox_pohoata_upper :
    ∀ k ℓ : ℕ, 2 ≤ k → k < ℓ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∀ A : Finset ℕ, A.card = N →
      (numAP A k : ℝ) ≥ (N : ℝ) ^ 2 / Real.log (Real.log N) ^ C →
      ContainsAP A ℓ :=
  sorry

/-- Fox and Pohoata [FoPo20] (SOLVED; not proved here): $F_k(N,\ell)=N^{2-o(1)}$ for fixed
`2 ≤ k < ℓ`; the lower half, as in part 2. -/
theorem erdos_problem_179.variants.fox_pohoata_lower :
    ∀ k ℓ : ℕ, 2 ≤ k → k < ℓ → ∀ ε : ℝ, ε > 0 → ε < 2 →
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∃ A : Finset ℕ, A.card = N ∧ (numAP A k : ℝ) ≥ (N : ℝ) ^ (2 - ε) ∧ ¬ContainsAP A ℓ :=
  sorry
