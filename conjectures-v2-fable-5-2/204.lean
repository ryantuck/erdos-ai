-- [AI - Claude Fable 5.2]: Erdős Problem 204 — second-pass formalization
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Erdős Problem #204

*Source:* [erdosproblems.com/204](https://www.erdosproblems.com/204) (status **DISPROVED**: "This
has been solved in the negative."; captured 2026-03-05; page last edited 28 December 2025).
[ErGr80, p.27]

Are there $n$ such that there is a covering system with moduli the divisors of $n$ which is 'as
disjoint as possible'?

That is, for all $d\mid n$ with $d>1$ there is an associated $a_d$ such that every integer is
congruent to some $a_d\pmod{d}$, and if there is some integer $x$ with
$$x\equiv a_d\pmod{d}\textrm{ and }x\equiv a_{d'}\pmod{d'}$$
then $(d,d')=1$.

Remarks recorded on the page: the density of such $n$ is zero. Erdős and Graham believed that no
such $n$ exist. Adenwalla [Ad25] has proved there are no such $n$. In general, for any $n$ one can
try to choose such $a_d$ to maximise the density of integers so covered, and ask what this density
is. This was also investigated by Adenwalla [Ad25].

## Status after capture

The metadata mirror `teorth/erdosproblems` (`641a78e`, 2026-11-12) lists the problem as
**disproved (Lean)** since 2026-03-15. Upstream `formal-conjectures` (`5258ab9`) states
`¬ ∃ n a, …` and links a Lean proof ("formalized by van Doorn in Lean using Aristotle"). Neither
[Ad25] nor the Lean proof was read in this review.

## Encoding notes

* The question "are there `n`?" has the answer no, and the theorem asserts that no `n > 0` has
  such a system. The restriction `n > 0` is harmless: `Nat.divisors 0 = ∅`, so `n = 0` has no
  covering either, and the theorem is equivalent to upstream's `¬ ∃ n a, …`
  (`erdos_problem_204.iff_not_exists`, PROVED in Lean).
* The disjointness clause is read for `d ≠ d'`, as it must be (for `d = d'` the conclusion
  `(d, d) = 1` is false).
* Sanity checks, PROVED in Lean: the covering clause alone already fails for every prime power
  `n = p^k` (`not_covering_prime_pow`), in particular for `n = 1` and for primes; so the content of
  the theorem lies in `n` with at least two prime factors.
* The maximal-density question at the end of the page is not formalized.

## References

No `/latex/204` fetch is in the session logs.
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.) The
  page cites p. 27.
* [Ad25] Adenwalla, S., _A Question of Erdős and Graham on Covering Systems_. arXiv:2501.15170
  (2025). (**DEFERRED:** from upstream's Problem 204 file; no site entry was recovered.)

*Provenance:* second pass of `conjectures/204.lean` (Fable 5.2 review,
`fable-5-2-review/204.md`).
-/

/--
A "disjoint covering system from divisors of n" is a choice of residues
a_d for each divisor d > 1 of n such that:
1. Every integer is covered by some residue class a_d mod d (covering).
2. If some integer x lies in both a_d mod d and a_{d'} mod d', then gcd(d,d')=1.
-/
def DisjointDivisorCovering (n : ℕ) (a : ℕ → ℤ) : Prop :=
  -- Covering: every integer is covered by some divisor class
  (∀ x : ℤ, ∃ d ∈ n.divisors, d > 1 ∧ x ≡ a d [ZMOD (d : ℤ)]) ∧
  -- Disjointness: overlapping classes must have coprime moduli
  (∀ d ∈ n.divisors, d > 1 →
    ∀ d' ∈ n.divisors, d' > 1 → d ≠ d' →
      (∃ x : ℤ, x ≡ a d [ZMOD (d : ℤ)] ∧ x ≡ a d' [ZMOD (d' : ℤ)]) →
        Nat.Coprime d d')

/--
Erdős Problem #204 [ErGr80, p.27]:

Are there n such that there is a covering system with moduli the divisors
of n which is 'as disjoint as possible'? That is, for all d ∣ n with d > 1
there is an associated a_d such that every integer is congruent to some
a_d (mod d), and if some integer x satisfies x ≡ a_d (mod d) and
x ≡ a_{d'} (mod d'), then gcd(d, d') = 1.

Erdős and Graham believed no such n exist. The density of such n is zero.
Adenwalla [Ad25] proved that no such n exist (DISPROVED; the mirror and upstream record a Lean
proof, 2026-03-15). Not proved here.
-/
theorem erdos_problem_204 :
    ∀ n : ℕ, n > 0 →
      ¬∃ a : ℕ → ℤ, DisjointDivisorCovering n a :=
  sorry

/-- `n = 0` has no covering: `Nat.divisors 0 = ∅` (PROVED in Lean). -/
theorem erdos_problem_204.not_covering_zero : ¬∃ a : ℕ → ℤ, DisjointDivisorCovering 0 a := by
  rintro ⟨a, hc, -⟩
  obtain ⟨d, hd, -⟩ := hc 0
  simp at hd

/-- The theorem is equivalent to upstream's form without the hypothesis `n > 0`
(PROVED in Lean). -/
theorem erdos_problem_204.iff_not_exists :
    (∀ n : ℕ, n > 0 → ¬∃ a : ℕ → ℤ, DisjointDivisorCovering n a) ↔
      ¬∃ (n : ℕ) (a : ℕ → ℤ), DisjointDivisorCovering n a := by
  constructor
  · rintro h ⟨n, a, hc⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact erdos_problem_204.not_covering_zero ⟨a, hc⟩
    · exact h n hn ⟨a, hc⟩
  · rintro h n - ⟨a, hc⟩
    exact h ⟨n, a, hc⟩

/-- For `p ≥ 2` and any residues there is an integer outside the classes `a(p^j) mod p^j`,
`1 ≤ j ≤ k` (PROVED in Lean): lift step by step, each step having at least two lifts of which at
most one is excluded. -/
theorem erdos_problem_204.exists_uncovered {p : ℕ} (hp : 2 ≤ p) (a : ℕ → ℤ) (k : ℕ) :
    ∃ x : ℤ, ∀ j : ℕ, 1 ≤ j → j ≤ k → ¬ x ≡ a (p ^ j) [ZMOD ((p ^ j : ℕ) : ℤ)] := by
  induction k with
  | zero => exact ⟨0, fun j h1 h2 => by omega⟩
  | succ k ih =>
    obtain ⟨x, hx⟩ := ih
    by_cases h : x ≡ a (p ^ (k + 1)) [ZMOD ((p ^ (k + 1) : ℕ) : ℤ)]
    · refine ⟨x + ((p ^ k : ℕ) : ℤ), fun j h1 h2 => ?_⟩
      rcases Nat.lt_or_ge j (k + 1) with hj | hj
      · intro hcon
        apply hx j h1 (by omega)
        have hdiv : ((p ^ j : ℕ) : ℤ) ∣ ((p ^ k : ℕ) : ℤ) := by
          exact_mod_cast pow_dvd_pow p (show j ≤ k by omega)
        have h3 : x ≡ x + ((p ^ k : ℕ) : ℤ) [ZMOD ((p ^ j : ℕ) : ℤ)] := by
          rw [Int.modEq_iff_dvd, add_sub_cancel_left]
          exact hdiv
        exact h3.trans hcon
      · have hj' : j = k + 1 := by omega
        subst hj'
        intro hcon
        have h3 : x + ((p ^ k : ℕ) : ℤ) ≡ x [ZMOD ((p ^ (k + 1) : ℕ) : ℤ)] := hcon.trans h.symm
        rw [Int.modEq_iff_dvd] at h3
        have h4 : ((p ^ (k + 1) : ℕ) : ℤ) ∣ ((p ^ k : ℕ) : ℤ) := by
          have h5 : x - (x + ((p ^ k : ℕ) : ℤ)) = -((p ^ k : ℕ) : ℤ) := by ring
          rw [h5] at h3
          exact dvd_neg.1 h3
        have h6 : p ^ (k + 1) ∣ p ^ k := by exact_mod_cast h4
        have hpos : 0 < p ^ k := pow_pos (by omega) k
        have h7 := Nat.le_of_dvd hpos h6
        rw [pow_succ] at h7
        nlinarith
    · refine ⟨x, fun j h1 h2 => ?_⟩
      rcases Nat.lt_or_ge j (k + 1) with hj | hj
      · exact hx j h1 (by omega)
      · have hj' : j = k + 1 := by omega
        subst hj'
        exact h

/-- No prime power `p^k` has a covering by classes modulo its divisors `> 1`, even without the
disjointness clause (PROVED in Lean). This includes `n = 1` (`k = 0`) and the primes (`k = 1`). -/
theorem erdos_problem_204.not_covering_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ¬∃ a : ℕ → ℤ, DisjointDivisorCovering (p ^ k) a := by
  rintro ⟨a, hc, -⟩
  obtain ⟨x, hx⟩ := erdos_problem_204.exists_uncovered hp.two_le a k
  obtain ⟨d, hd, hd1, hxd⟩ := hc x
  obtain ⟨j, hjk, rfl⟩ := (Nat.mem_divisors_prime_pow hp k).1 hd
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with rfl | h
    · simp at hd1
    · exact h
  exact hx j hj1 hjk hxd

/-- `n = 1` has no covering (PROVED in Lean): there are no moduli. -/
theorem erdos_problem_204.not_covering_one : ¬∃ a : ℕ → ℤ, DisjointDivisorCovering 1 a := by
  have h := erdos_problem_204.not_covering_prime_pow Nat.prime_two 0
  simpa using h

/-- A prime `p` has no covering (PROVED in Lean): one class modulo `p ≥ 2` is not all of `ℤ`. -/
theorem erdos_problem_204.not_covering_prime {p : ℕ} (hp : p.Prime) :
    ¬∃ a : ℕ → ℤ, DisjointDivisorCovering p a := by
  have h := erdos_problem_204.not_covering_prime_pow hp 1
  simpa using h
