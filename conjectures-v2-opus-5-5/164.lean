-- [AI - Claude Opus 5.5]: Erdős Problem 164 — second-pass formalization
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Antichain

/-!
# Erdős Problem #164 (the Erdős primitive set conjecture)

*Source:* [erdosproblems.com/164](https://www.erdosproblems.com/164) (status **PROVED**: "This has
been solved in the affirmative."; captured 2026-02-20; page edited 23 January 2026; OEIS A137245).
[Er76g] [Er86] [Va99, 1.12]

A set $A\subset \mathbb{N}$ is primitive if no member of $A$ divides another. Is the sum
$\sum_{n\in A}\frac{1}{n\log n}$ maximised over all primitive sets when $A$ is the set of primes?

Remarks recorded on the page: Erdős [Er35] proved that this sum always converges for a primitive
set. Lichtman [Li23] proved that the answer is yes.

After the capture, upstream `formal-conjectures` (`df3f12d`) records a simpler proof [ABLLPSTT26],
and the mirror (`b916d95`) records the status `proved (Lean)` (2026-04-23). Neither was examined
here.

## Encoding notes

* The question is a yes/no question whose answer is yes. The input asserts the inequality for every
  primitive `A ⊆ {2, 3, …}`; since the primes are such a set (`primes_isPrimitive`), this is the
  same as "the primes attain the maximum" (`variants.maximised_of_main`, PROVED in Lean).
* `IsPrimitive` is Mathlib's `IsAntichain (· ∣ ·)` (`isPrimitive_iff`, PROVED). The hypothesis
  `A ⊆ {n | 2 ≤ n}` excludes `1`, where `log 1 = 0`.
* `∑'` is `0` for a non-summable family. The left side is summable by [Er35] (`variants.erdos35`),
  and even without that a junk `0` would only make the inequality easier. The right side must be
  summable for the statement to be true; it is ($\sum_p 1/(p\log p)=1.6366\ldots$, A137245), but
  this is not proved here (`variants.primes_summable`).

## References

* [Er35] Erdős, P., _Note on sequences of integers no one of which is divisible by any other_.
  J. London Math. Soc. (1935), 126–128. (Site `/latex/164`.)
* [Li23] Lichtman, J. D., _A proof of the Erdős primitive set conjecture_. arXiv:2202.02384
  (2023). (Site `/latex/164`.)
* [Er76g] Erdős, P., _Problems and results on combinatorial number theory. II_. J. Indian Math. Soc.
  (N.S.) (1976), 285–298. (From upstream's docstring; no site entry was recovered.)
* [Er86] Erdős, P., _Problèmes et résultats en théorie des nombres_ (1986). (From upstream's
  docstring; no site entry was recovered.)
* [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999. (Site `/latex/59` and others.)
* [ABLLPSTT26] Alexeev, B., Barreto, K., Li, Y., Lichtman, J. D., Price, L., Shah, J. I., Tang, Q.
  and Tao, T., _Primitive sets and von Mangoldt chains: Erdős problem #1196 and beyond_.
  arXiv:2605.00301 (2026). (From upstream; not on the captured page.)

*Provenance:* second pass of `conjectures/164.lean` (Opus 5.5 review, `opus-5-5-review/164.md`).
-/

open Real

noncomputable section

/-- A set A of natural numbers is primitive (an antichain under divisibility)
    if no element divides a distinct element: for all a, b ∈ A, a ∣ b → a = b. -/
def IsPrimitive (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b

/--
Erdős Conjecture (Problem #164) [Er76g, Er86]:

For any primitive set A ⊆ {2, 3, 4, ...} of natural numbers,
  ∑_{n ∈ A} 1/(n · log n) ≤ ∑_{p prime} 1/(p · log p).

That is, the sum ∑ 1/(n log n) over any primitive set is maximised when
the set is the set of all primes.

Proved by Lichtman [Li23]. (Status: PROVED; the statement is the true direction.)
-/
theorem erdos_problem_164 :
    ∀ A : Set ℕ, IsPrimitive A → A ⊆ {n : ℕ | 2 ≤ n} →
    ∑' n : A, (1 : ℝ) / (((n : ℕ) : ℝ) * Real.log ((n : ℕ) : ℝ)) ≤
    ∑' p : {p : ℕ | Nat.Prime p}, (1 : ℝ) / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ)) :=
  sorry

/-- `IsPrimitive` is Mathlib's `IsAntichain (· ∣ ·)` (PROVED in Lean). -/
theorem erdos_problem_164.isPrimitive_iff (A : Set ℕ) :
    IsPrimitive A ↔ IsAntichain (· ∣ ·) A := by
  constructor
  · intro h a ha b hb hne hdvd
    exact hne (h a ha b hb hdvd)
  · intro h a ha b hb hdvd
    by_contra hne
    exact h ha hb hne hdvd

/-- The primes form a primitive subset of `{2, 3, …}` (PROVED in Lean). -/
theorem erdos_problem_164.primes_isPrimitive :
    IsPrimitive {p : ℕ | Nat.Prime p} ∧ {p : ℕ | Nat.Prime p} ⊆ {n : ℕ | 2 ≤ n} :=
  ⟨fun _ ha _ hb hdvd => (Nat.prime_dvd_prime_iff_eq ha hb).mp hdvd, fun _ hp => hp.two_le⟩

/-- The input's inequality is the page's question "is the sum maximised at the primes?": given the
main theorem, the value at the primes is the greatest value of the sum over primitive subsets of
`{2, 3, …}` (PROVED in Lean from the main theorem). -/
theorem erdos_problem_164.variants.maximised_of_main
    (h : ∀ A : Set ℕ, IsPrimitive A → A ⊆ {n : ℕ | 2 ≤ n} →
      ∑' n : A, (1 : ℝ) / (((n : ℕ) : ℝ) * Real.log ((n : ℕ) : ℝ)) ≤
      ∑' p : {p : ℕ | Nat.Prime p}, (1 : ℝ) / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ))) :
    IsGreatest
      {s : ℝ | ∃ A : Set ℕ, IsPrimitive A ∧ A ⊆ {n : ℕ | 2 ≤ n} ∧
        s = ∑' n : A, (1 : ℝ) / (((n : ℕ) : ℝ) * Real.log ((n : ℕ) : ℝ))}
      (∑' p : {p : ℕ | Nat.Prime p}, (1 : ℝ) / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ))) := by
  refine ⟨⟨{p : ℕ | Nat.Prime p}, erdos_problem_164.primes_isPrimitive.1,
    erdos_problem_164.primes_isPrimitive.2, rfl⟩, ?_⟩
  rintro s ⟨A, hA, hA2, rfl⟩
  exact h A hA hA2

/-- Erdős [Er35] (SOLVED; not proved here): the sum converges for every primitive
`A ⊆ {2, 3, …}`. -/
theorem erdos_problem_164.variants.erdos35 :
    ∀ A : Set ℕ, IsPrimitive A → A ⊆ {n : ℕ | 2 ≤ n} →
    Summable (fun n : A => (1 : ℝ) / (((n : ℕ) : ℝ) * Real.log ((n : ℕ) : ℝ))) :=
  sorry

/-- The prime sum converges (SOLVED, by Chebyshev's bound $p_k\gg k\log k$; not proved here), so the
right side of the main theorem is a true sum, $1.6366\ldots$ (OEIS A137245). -/
theorem erdos_problem_164.variants.primes_summable :
    Summable (fun p : {p : ℕ | Nat.Prime p} =>
      (1 : ℝ) / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ))) :=
  sorry

end
