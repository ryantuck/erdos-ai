-- [AI - Claude Fable 5.2]: Erdős Problem 203 — second-pass formalization
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Ring

/-!
# Erdős Problem #203

*Source:* [erdosproblems.com/203](https://www.erdosproblems.com/203) (status **OPEN**: "This is
open, and cannot be resolved with a finite computation."; captured 2026-03-05; page last edited
20 January 2026). [ErGr80, p.27]

Is there an integer $m\geq 1$ with $(m,6)=1$ such that none of $2^k3^\ell m+1$ are prime, for any
$k,\ell\geq 0$?

Remarks recorded on the page: positive odd integers $m$ such that none of $2^km+1$ are prime are
called Sierpinski numbers - see [1113] for more details. Erdős and Graham also ask more generally
about $p_1^{k_1}\cdots p_r^{k_r}m+1$ for distinct primes $p_i$, or $q_1\cdots q_rm+1$ where the
$q_i$ are primes congruent to $1\pmod{4}$. (Dogmachine has noted in the comments this latter
question has the trivial answer $m=1$ - perhaps some condition such as $m$ even is meant.)

## Status

OPEN at capture and in the metadata mirror `teorth/erdosproblems` (`641a78e`, 2026-11-12). Upstream
`formal-conjectures` (`5258ab9`) states the same existence assertion (without `1 ≤ m`, which
`Nat.Coprime m 6` implies).

## Encoding notes

* The theorem asserts the "yes" answer (OPEN; corpus convention for open yes/no questions).
* `1 ≤ m` is implied by `Nat.Coprime m 6`, since `gcd(0, 6) = 6`
  (`erdos_problem_203.pos_of_coprime`, PROVED in Lean).
* The case `k = ℓ = 0` requires `m + 1` not to be prime, and the case `ℓ = 0` requires `m` to be a
  Sierpiński number. Sierpiński numbers coprime to 6 exist: `78557` is one
  (`erdos_problem_203.sierpinski_78557`, PROVED in Lean with the covering set
  `{3, 5, 7, 13, 19, 37, 73}`), so the `ℓ = 0` restriction of the problem has the answer yes
  (`erdos_problem_203.variants.sierpinski`, PROVED).
* `78557` itself does not answer the problem: `2^13 · 3 · 78557 + 1 = 1930616833` is prime
  (`erdos_problem_203.not_78557`, PROVED).
* No `m < 100` answers the problem (`erdos_problem_203.small_m`, PROVED).
* The page's second generalisation is trivial with `m = 1`, as the page says
  (`erdos_problem_203.variants.one_mod_four_trivial`, PROVED). The first generalisation is trivial
  unless `2` is among the primes (`erdos_problem_203.variants.odd_primes_trivial`, PROVED).

## References

No `/latex/203` fetch is in the session logs; the page cites only Erdős and Graham.
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.) The
  page cites p. 27.

*Provenance:* second pass of `conjectures/203.lean` (Fable 5.2 review,
`fable-5-2-review/203.md`).
-/

/--
Erdős Problem #203 [ErGr80,p.27]:

Is there an integer m ≥ 1 with gcd(m, 6) = 1 such that none of
2^k · 3^ℓ · m + 1 are prime, for any k, ℓ ≥ 0?

This is a generalization of Sierpiński numbers (where only powers of 2 are
considered) to products of powers of 2 and 3.

Status: OPEN; the "yes" direction is asserted.
-/
theorem erdos_problem_203 :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.Coprime m 6 ∧
      ∀ k ℓ : ℕ, ¬ Nat.Prime (2 ^ k * 3 ^ ℓ * m + 1) :=
  sorry

/-- `Nat.Coprime m 6` already forces `1 ≤ m` (PROVED in Lean), so the hypothesis `1 ≤ m` of the
main theorem is redundant. -/
theorem erdos_problem_203.pos_of_coprime {m : ℕ} (h : Nat.Coprime m 6) : 1 ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact absurd h (by decide)
  · exact hm

/-- If `2^36 ≡ 1 (mod p)` and `p` divides `2^r · 78557 + 1`, then `p` divides
`2^(36q+r) · 78557 + 1` (PROVED in Lean). -/
theorem erdos_problem_203.sierpinski_dvd_aux (p : ℕ) (hp : 2 ^ 36 % p = 1 % p) (q r : ℕ)
    (hr : (2 ^ r * 78557 + 1) % p = 0) : p ∣ 2 ^ (36 * q + r) * 78557 + 1 := by
  have h1 : (2 ^ 36) ^ q ≡ 1 [MOD p] := by
    have h := Nat.ModEq.pow q (show 2 ^ 36 ≡ 1 [MOD p] from hp)
    rwa [one_pow] at h
  have h2 : 2 ^ (36 * q + r) * 78557 + 1 ≡ 2 ^ r * 78557 + 1 [MOD p] := by
    rw [pow_add, pow_mul]
    have h3 : (2 ^ 36) ^ q * 2 ^ r * 78557 + 1 ≡ 1 * 2 ^ r * 78557 + 1 [MOD p] :=
      ((h1.mul_right (2 ^ r)).mul_right 78557).add_right 1
    rwa [one_mul] at h3
  exact Nat.dvd_of_mod_eq_zero (Eq.trans h2 hr)

/-- `78557` is a Sierpiński number (Selfridge; PROVED in Lean): every `2^k · 78557 + 1` is
divisible by one of `3, 5, 7, 13, 19, 37, 73`, according to `k mod 36`. -/
theorem erdos_problem_203.sierpinski_78557 (k : ℕ) : ¬ Nat.Prime (2 ^ k * 78557 + 1) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 36 ∧ k = 36 * q + r :=
    ⟨k / 36, k % 36, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 36).symm⟩
  have hbig : 73 < 2 ^ (36 * q + r) * 78557 + 1 := by
    have h1 : 1 ≤ 2 ^ (36 * q + r) := Nat.one_le_two_pow
    omega
  have key : ∀ p : ℕ, 2 ≤ p → p ≤ 73 → 2 ^ 36 % p = 1 % p →
      (2 ^ r * 78557 + 1) % p = 0 → ¬ Nat.Prime (2 ^ (36 * q + r) * 78557 + 1) :=
    fun p h2 h73 hp hr' =>
      Nat.not_prime_of_dvd_of_lt (erdos_problem_203.sierpinski_dvd_aux p hp q r hr') h2
        (by omega)
  interval_cases r
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 5 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 73 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 5 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 7 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 5 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 13 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 5 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 19 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 5 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 7 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 5 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 13 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 5 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 37 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 5 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 7 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 5 (by decide) (by decide) (by decide) (by decide)
  · exact key 3 (by decide) (by decide) (by decide) (by decide)
  · exact key 13 (by decide) (by decide) (by decide) (by decide)

/-- The restriction of the problem to `ℓ = 0` has the answer yes (PROVED in Lean): `78557` is
coprime to 6 and is a Sierpiński number. -/
theorem erdos_problem_203.variants.sierpinski :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.Coprime m 6 ∧ ∀ k : ℕ, ¬ Nat.Prime (2 ^ k * m + 1) :=
  ⟨78557, by norm_num, by norm_num, erdos_problem_203.sierpinski_78557⟩

/-- `78557` does not answer the problem (PROVED in Lean): `2^13 · 3 · 78557 + 1 = 1930616833` is
prime. -/
theorem erdos_problem_203.not_78557 :
    ¬ ∀ k ℓ : ℕ, ¬ Nat.Prime (2 ^ k * 3 ^ ℓ * 78557 + 1) := by
  intro h
  exact h 13 1 (by norm_num)

/-- No `m < 100` answers the problem (PROVED in Lean): for each such `m` coprime to 6 some
`2^k · 3^ℓ · m + 1` with `k ≤ 3`, `ℓ ≤ 1` is prime. -/
theorem erdos_problem_203.small_m (m : ℕ) (hm : m < 100) (hc : Nat.Coprime m 6) :
    ∃ k ℓ : ℕ, Nat.Prime (2 ^ k * 3 ^ ℓ * m + 1) := by
  interval_cases m
  · exact absurd hc (by decide)
  · exact ⟨0, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 1, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 1, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 1, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 1, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨1, 1, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨2, 1, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨1, 1, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨3, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 1, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 1, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨1, 1, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)
  · exact ⟨1, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact ⟨2, 0, by norm_num⟩
  · exact absurd hc (by decide)
  · exact absurd hc (by decide)

/-- The page's second generalisation, with primes `q_i ≡ 1 (mod 4)`, is trivial with `m = 1`
(PROVED in Lean), as the page notes: if `n > 1` is a product of primes congruent to `1` modulo `4`
then `n · 1 + 1` is even and greater than `2`. -/
theorem erdos_problem_203.variants.one_mod_four_trivial (n : ℕ) (hn : 1 < n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p % 4 = 1) : ¬ Nat.Prime (n * 1 + 1) := by
  have hodd : ¬ 2 ∣ n := fun h2 => by
    have := h 2 Nat.prime_two h2
    omega
  have h2 : 2 ∣ n * 1 + 1 := by omega
  exact Nat.not_prime_of_dvd_of_lt h2 (by norm_num) (by omega)

/-- The page's first generalisation, with distinct primes `p_1, …, p_r` in place of `2, 3`, is
trivial unless `2` is among the primes (PROVED in Lean): if `n` is odd (for instance a product of
powers of odd primes) and `m ≥ 3` is odd, then `n · m + 1` is even and at least `4`. So only sets of
primes containing `2` give a real question, as in the problem itself. -/
theorem erdos_problem_203.variants.odd_primes_trivial (n m : ℕ) (hn : Odd n) (hm : Odd m)
    (hm3 : 3 ≤ m) : ¬ Nat.Prime (n * m + 1) := by
  obtain ⟨s, rfl⟩ := hn
  obtain ⟨t, rfl⟩ := hm
  have h2 : 2 ∣ (2 * s + 1) * (2 * t + 1) + 1 := ⟨2 * s * t + s + t + 1, by ring⟩
  have h3 := Nat.mul_le_mul (show 1 ≤ 2 * s + 1 by omega) hm3
  exact Nat.not_prime_of_dvd_of_lt h2 (by norm_num) (by omega)
