-- [AI - Claude Sonnet 5.5]: Erdős Problem 137 — second-pass formalization
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith

open Filter

/-!
# Erdős Problem #137: Powerful Products of Consecutive Integers

*Source:* [erdosproblems.com/137](https://www.erdosproblems.com/137) (banner **OPEN**: "This is open,
and cannot be resolved with a finite computation."; page last edited 20 January 2026; captured
2026-03-05 as the tidied problem box). [ErGr80] [Er82c, p.28] [Er97c]

We say that $N$ is powerful if whenever $p\mid N$ we also have $p^2\mid N$. Let $k\geq 3$. Can the
product of any $k$ consecutive positive integers ever be powerful?

Remarks recorded on the page:
* Conjectured by Erdős and Selfridge. There are infinitely many $n$ such that $n(n+1)$ is powerful
  (see [364]). Erdős and Selfridge [ErSe75] proved that the product of $k\geq 3$ consecutive positive
  integers can never be a perfect power. Erdős remarked that this "seems hopeless at present".
* In [Er82c] he further conjectures that, if $k$ is fixed and $n$ is sufficiently large, then, for
  all $m$, there must be at least $k$ distinct primes $p$ such that $p\mid m(m+1)\cdots(m+n)$ and yet
  $p^2$ does not divide the right-hand side.
* See also [364].

Tags: number theory, powerful. 0 comments at capture.

**Status.** OPEN. The mirror (`teorth/erdosproblems`) has `open` since 2025-08-31. Upstream has
`erdos_137 : answer(sorry) ↔ ∃ k ≥ 3, ∃ n, (∏ x ∈ Finset.Ioc n (n + k), x).Powerful`, category
`research open`.

**Direction.** The question as asked is existential ("can … ever be powerful?"), and the main theorem
asserts its negation: for every $k\ge3$ no product of $k$ consecutive positive integers is powerful.
That is the Erdős–Selfridge conjecture, and it is what upstream's `answer(sorry) ↔ …` would say if its
answer were `False`. The page says "conjectured by Erdős and Selfridge" without stating the content.
The content "never powerful" is read from the surrounding remarks: [ErSe75] proves it for perfect
powers, which are powerful, and the further conjecture of [Er82c] points the same way.

**Encoding.**
* `IsPowerful N` is the page's definition, over all of ℕ. It holds for `0` and `1`, which does not
  matter here, since every product below is positive. It is equivalent to upstream's `Nat.Powerful`,
  which quantifies over `N.primeFactors`.
* `consecutiveProduct m k` is $(m+1)(m+2)\cdots(m+k)$, the product of $k$ consecutive positive
  integers, with $m\ge0$. `variants.consecutiveProduct_eq_ascFactorial` identifies it with
  `(m + 1).ascFactorial k`.
* `variants.erdos_selfridge` is the theorem of [ErSe75]. `variants.isPowerful_pow` shows that perfect
  powers are powerful, so the main theorem implies it (`variants.no_perfect_power_of_main`).
* `variants.two_consecutive` proves that $k=2$ has infinitely many powerful products, so the
  hypothesis $k\ge3$ cannot be dropped.
* `variants.exact_primes` is the further conjecture of [Er82c], with the product of $n+1$ factors
  $m,\dots,m+n$ and $m>0$ (for $m=0$ the product is $0$). `variants.large_k_of_exact_primes` shows
  that its case "at least one such prime" implies the main theorem for all large $k$.

## References

* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathématique (1980).
* [Er82c] Erdős, P., _Miscellaneous problems in number theory_. Congr. Numer. (1982), 25–45. The page
  cites p. 28.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. In: The mathematics of Paul Erdős,
  I (1997), 47–67.
* [ErSe75] Erdős, P. and Selfridge, J. L., _The product of consecutive integers is never a power_.
  Illinois J. Math. (1975), 292–301. (Upstream writes the key `[ES75]` and gives vol. 19(2).)
* [364] The page's cross-reference.

(Provenance: [ErGr80] and [Er97c] are from the bibliographies of the `/latex` pages of other
problems. [Er82c] and [ErSe75] are from upstream `137.lean` and from upstream-derived files in the
session logs. **DEFERRED:** no `/latex/137` fetch exists in the logs, so the entries were not checked
against the page's own bibliography.)
-/

/-- A positive natural number N is *powerful* if for every prime p dividing N,
    p² also divides N. -/
def IsPowerful (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → p ^ 2 ∣ N

/-- The product of k consecutive positive integers starting at m+1:
    (m+1)(m+2)⋯(m+k). -/
def consecutiveProduct (m k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (m + 1 + i)

/--
Erdős Problem #137 (Erdős–Selfridge conjecture) [ErGr80, Er82c, Er97c] — OPEN:

For all k ≥ 3, the product of k consecutive positive integers is never powerful.
This is the negation of the question as asked ("can the product ever be powerful?").
-/
theorem erdos_problem_137 :
    ∀ k : ℕ, 3 ≤ k →
      ∀ m : ℕ, ¬ IsPowerful (consecutiveProduct m k) :=
  sorry

/--
The theorem of Erdős and Selfridge [ErSe75] (PROVED, not checked here): for `k ≥ 3`, the product of
`k` consecutive positive integers is never a perfect power.
-/
theorem erdos_problem_137.variants.erdos_selfridge :
    ∀ k : ℕ, 3 ≤ k →
      ∀ m : ℕ, ¬ ∃ x l : ℕ, 2 ≤ l ∧ consecutiveProduct m k = x ^ l :=
  sorry

/-- Every perfect power with exponent at least 2 is powerful (PROVED in Lean). -/
theorem erdos_problem_137.variants.isPowerful_pow (x l : ℕ) (hl : 2 ≤ l) :
    IsPowerful (x ^ l) := by
  intro p hp hdvd
  have hpx : p ∣ x := hp.dvd_of_dvd_pow hdvd
  exact dvd_trans (pow_dvd_pow p hl) (pow_dvd_pow_of_dvd hpx l)

/--
The main theorem implies the theorem of Erdős and Selfridge (PROVED in Lean): a perfect power is
powerful, so a product that is never powerful is never a perfect power.
-/
theorem erdos_problem_137.variants.no_perfect_power_of_main
    (hmain : ∀ k : ℕ, 3 ≤ k → ∀ m : ℕ, ¬ IsPowerful (consecutiveProduct m k)) :
    ∀ k : ℕ, 3 ≤ k →
      ∀ m : ℕ, ¬ ∃ x l : ℕ, 2 ≤ l ∧ consecutiveProduct m k = x ^ l := by
  rintro k hk m ⟨x, l, hl, h⟩
  exact hmain k hk m (h ▸ erdos_problem_137.variants.isPowerful_pow x l hl)

/-- `consecutiveProduct m k` is Mathlib's `Nat.ascFactorial (m + 1) k` (PROVED in Lean). -/
theorem erdos_problem_137.variants.consecutiveProduct_eq_ascFactorial (m k : ℕ) :
    consecutiveProduct m k = (m + 1).ascFactorial k :=
  (Nat.ascFactorial_eq_prod_range (m + 1) k).symm

/-- A number `8 * z ^ 2` is powerful (PROVED in Lean). -/
theorem erdos_problem_137.eight_mul_sq_powerful (z : ℕ) : IsPowerful (8 * z ^ 2) := by
  intro p hp hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h8 | hz
  · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using h8)
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    subst hp2
    exact Dvd.dvd.mul_right (by norm_num) _
  · have hpz : p ∣ z := hp.dvd_of_dvd_pow hz
    exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hpz 2) 8

/-- The solutions `(x, y)` of the Pell equation `x ^ 2 = 8 * y ^ 2 + 1`: `(3, 1)`, `(17, 6)`,
`(99, 35)`, … -/
def erdos_problem_137.pell8 : ℕ → ℕ × ℕ
  | 0 => (3, 1)
  | j + 1 => (3 * (erdos_problem_137.pell8 j).1 + 8 * (erdos_problem_137.pell8 j).2,
      (erdos_problem_137.pell8 j).1 + 3 * (erdos_problem_137.pell8 j).2)

/-- Each `pell8 j` solves `x ^ 2 = 8 * y ^ 2 + 1` (PROVED in Lean). -/
theorem erdos_problem_137.pell8_eq (j : ℕ) :
    (erdos_problem_137.pell8 j).1 ^ 2 = 8 * (erdos_problem_137.pell8 j).2 ^ 2 + 1 := by
  induction j with
  | zero => norm_num [erdos_problem_137.pell8]
  | succ j ih =>
    simp only [erdos_problem_137.pell8]
    nlinarith [ih]

/-- The second coordinate of `pell8 j` is positive (PROVED in Lean). -/
theorem erdos_problem_137.pell8_pos (j : ℕ) : 1 ≤ (erdos_problem_137.pell8 j).2 := by
  induction j with
  | zero => simp [erdos_problem_137.pell8]
  | succ j ih =>
    simp only [erdos_problem_137.pell8]
    omega

/-- The second coordinate of `pell8` is strictly increasing (PROVED in Lean). -/
theorem erdos_problem_137.pell8_strictMono :
    StrictMono (fun j => (erdos_problem_137.pell8 j).2) := by
  refine strictMono_nat_of_lt_succ (fun j => ?_)
  have hx : (erdos_problem_137.pell8 j).1 ≠ 0 := by
    intro h
    have := erdos_problem_137.pell8_eq j
    rw [h] at this
    omega
  simp only [erdos_problem_137.pell8]
  omega

/--
The case `k = 2` has infinitely many powerful products (PROVED in Lean, see [364]), which is why the
page needs `k ≥ 3`: if `x ^ 2 = 8 * y ^ 2 + 1` then `8 * y ^ 2` and `x ^ 2` are consecutive and
`8 * y ^ 2 * x ^ 2 = 8 * (x * y) ^ 2` is powerful. For example `8 * 9 = 72`.
-/
theorem erdos_problem_137.variants.two_consecutive :
    {m : ℕ | IsPowerful (consecutiveProduct m 2)}.Infinite := by
  have hmem : ∀ j : ℕ, 8 * (erdos_problem_137.pell8 j).2 ^ 2 - 1 ∈
      {m : ℕ | IsPowerful (consecutiveProduct m 2)} := by
    intro j
    have hy := erdos_problem_137.pell8_pos j
    have hx := erdos_problem_137.pell8_eq j
    have hpos : 1 ≤ 8 * (erdos_problem_137.pell8 j).2 ^ 2 := by
      have : 1 ≤ (erdos_problem_137.pell8 j).2 ^ 2 := Nat.one_le_pow _ _ hy
      omega
    show IsPowerful (consecutiveProduct _ 2)
    have hprod : consecutiveProduct (8 * (erdos_problem_137.pell8 j).2 ^ 2 - 1) 2
        = 8 * ((erdos_problem_137.pell8 j).1 * (erdos_problem_137.pell8 j).2) ^ 2 := by
      have e1 : 8 * (erdos_problem_137.pell8 j).2 ^ 2 - 1 + 1
          = 8 * (erdos_problem_137.pell8 j).2 ^ 2 := by omega
      simp only [consecutiveProduct, Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
        add_zero, e1]
      rw [mul_pow, hx]
      ring
    rw [hprod]
    exact erdos_problem_137.eight_mul_sq_powerful _
  refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ =>
    8 * (erdos_problem_137.pell8 j).2 ^ 2 - 1) ?_ hmem
  intro a b hab
  have ha := erdos_problem_137.pell8_pos a
  have hb := erdos_problem_137.pell8_pos b
  have hpa : 1 ≤ 8 * (erdos_problem_137.pell8 a).2 ^ 2 := by
    have : 1 ≤ (erdos_problem_137.pell8 a).2 ^ 2 := Nat.one_le_pow _ _ ha
    omega
  have hpb : 1 ≤ 8 * (erdos_problem_137.pell8 b).2 ^ 2 := by
    have : 1 ≤ (erdos_problem_137.pell8 b).2 ^ 2 := Nat.one_le_pow _ _ hb
    omega
  have h1 : 8 * (erdos_problem_137.pell8 a).2 ^ 2 = 8 * (erdos_problem_137.pell8 b).2 ^ 2 := by
    simp only at hab
    omega
  have h2 : (erdos_problem_137.pell8 a).2 = (erdos_problem_137.pell8 b).2 := by
    have : (erdos_problem_137.pell8 a).2 ^ 2 = (erdos_problem_137.pell8 b).2 ^ 2 := by omega
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) this
  exact erdos_problem_137.pell8_strictMono.injective h2

/--
Erdős's further conjecture [Er82c] (OPEN): for fixed `k` and all sufficiently large `n`, for every
positive `m` there are at least `k` distinct primes `p` that divide `m (m + 1) ⋯ (m + n)` while
`p ^ 2` does not.
-/
theorem erdos_problem_137.variants.exact_primes (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m →
      ∃ P : Finset ℕ, P.card = k ∧ ∀ p ∈ P, p.Prime ∧
        p ∣ ∏ i ∈ Finset.range (n + 1), (m + i) ∧
        ¬ p ^ 2 ∣ ∏ i ∈ Finset.range (n + 1), (m + i) :=
  sorry

/--
The case `k = 1` of the further conjecture of [Er82c] implies the main theorem for all sufficiently
large `k` (PROVED in Lean): a prime that divides the product but whose square does not shows that the
product is not powerful.
-/
theorem erdos_problem_137.variants.large_k_of_exact_primes
    (h : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m →
      ∃ P : Finset ℕ, P.card = 1 ∧ ∀ p ∈ P, p.Prime ∧
        p ∣ ∏ i ∈ Finset.range (n + 1), (m + i) ∧
        ¬ p ^ 2 ∣ ∏ i ∈ Finset.range (n + 1), (m + i)) :
    ∀ᶠ k : ℕ in atTop, ∀ m : ℕ, ¬ IsPowerful (consecutiveProduct m k) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  filter_upwards [eventually_ge_atTop (N + 1)] with k hk m
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨P, hP, hPp⟩ := hN n (by omega) (m + 1) (by omega)
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hP
  obtain ⟨hp, hdvd, hnd⟩ := hPp p (Finset.mem_singleton_self p)
  intro hpow
  exact hnd (hpow p hp hdvd)
