-- [AI - Claude Fable 5.2]: Erdős Problem 202 — second-pass formalization
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat

open Filter

/-!
# Erdős Problem #202

*Source:* [erdosproblems.com/202](https://www.erdosproblems.com/202) (status **OPEN** at capture:
"This is open, and cannot be resolved with a finite computation."; captured 2026-02-20; page last
edited 23 January 2026). [Er61] [Er65] [Er65b] [Er73] [Er77c] [ErGr80] [Va99, 1.29]

Let $n_1<\cdots < n_r\leq N$ with associated $a_i\pmod{n_i}$ such that the congruence classes are
disjoint (that is, every integer is $\equiv a_i\pmod{n_i}$ for at most one $1\leq i\leq r$). How
large can $r$ be in terms of $N$?

Remarks recorded on the page: let $f(N)$ be the maximum possible $r$. Erdős and Stein conjectured
that $f(N)=o(N)$, which was proved by Erdős and Szemerédi [ErSz68], who showed that, for every
$\epsilon>0$,
$$\frac{N}{\exp((\log N)^{1/2+\epsilon})} \ll_\epsilon f(N) < \frac{N}{(\log N)^c}$$
for some $c>0$. Erdős believed the lower bound is closer to the truth. These bounds were improved
by Croot [Cr03b] who proved
$$\frac{N}{L(N)^{\sqrt{2}+o(1)}}< f(N)<\frac{N}{L(N)^{1/6-o(1)}},$$
where $L(N)=\exp(\sqrt{\log N\log\log N})$. These bounds were further improved by Chen [Ch05] and
then by de la Bretèche, Ford, and Vandehey [BFV13] to
$$\frac{N}{L(N)^{1+o(1)}}<f(N) < \frac{N}{L(N)^{\sqrt{3}/2+o(1)}}.$$
The latter authors conjecture that the lower bound here is the truth. OEIS A389975.

## Status after capture

The metadata mirror `teorth/erdosproblems` (`641a78e`, 2026-11-12) lists the problem as
**solved (Lean)** since 2026-05-14. Upstream `formal-conjectures` (`5258ab9`) records
$f(N)=N\,L(N)^{-1+o(1)}$, "proved by GPT-5.4 Pro (prompted by Ho Boon Suan), using the argument of
[BFV13] together with the resolution of the Kahn–Kalai conjecture by Park and Pham [PaPh24]", with
a linked Lean proof. Neither the argument nor the Lean proof was read in this review; the main
theorem below is the upper-bound half of that asymptotic, which was the open half at capture.

## Encoding notes

* The page's question ("How large can $r$ be?") is a value question. The main theorem states the
  conjecture of [BFV13] recorded on the page, in the form of its open half: for every `ε > 0` and
  large `N`, `f(N) ≤ N / L(N)^(1-ε)`. The matching lower bound was known at capture and is
  `erdos_problem_202.variants.lower`.
* A class is a pair `(n, a)`; `x % n = a % n` over `ℤ` is `x ≡ a (mod n)` (Mathlib's `Int.ModEq`
  unfolds to exactly this). Moduli `≥ 1` are allowed; a class of modulus `1` is all of `ℤ`.
* Sanity checks, PROVED in Lean: every system has at most `N` classes (`card_le`), so the
  conclusion is a real restriction only through the factor `L(N)^(1-ε)`; and
  `{1 mod 2, 2 mod 4, 4 mod 8}` is a system for `N = 8` (`example_system`).

## References

From the site's `/latex/202` bibliography:
* [BFV13] de la Bretèche, Régis, Ford, Kevin and Vandehey, Joseph, _On non-intersecting arithmetic
  progressions_. Acta Arith. (2013), 381–392.
* [Ch05] Chen, Yong-Gao, _On disjoint arithmetic progressions_. Acta Arith. (2005), 143–148.
* [Cr03b] Croot, III, Ernest S., _On non-intersecting arithmetic progressions_. Acta Arith. (2003),
  233–238.
* [ErSz68] Erdős, P. and Szemerédi, E., _On a problem of P. Erdős and S. Stein_. Acta Arith.
  (1968), 85–90.

From other problems' site bibliographies (the heading keys are not in `/latex/202`):
* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221–254. (Site `/latex/511` and others.)
* [Er65] Erdős, P., _Extremal problems in number theory_. Proc. Sympos. Pure Math., Vol. VIII
  (1965), 181–189. (Site `/latex/792` and others.)
* [Er65b] Erdős, P., _Some recent advances and current problems in number theory_. Lectures on
  Modern Mathematics, Vol. III (1965), 196–244. (Site `/latex/976` and others.)
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117–138. (Site `/latex/783` and others.)
* [Er77c] Erdős, P., _Problems and results on combinatorial number theory. III_. Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72. (Site `/latex/460` and others.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999. The page cites item 1.29. (Site `/latex/1172`
  and others.)

From upstream's Problem 202 file (**DEFERRED:** not on the captured page):
* [PaPh24] Park, Jinyoung and Pham, Huy Tuan, _A proof of the Kahn-Kalai conjecture_. J. Amer.
  Math. Soc. (2024), 235–243.

*Provenance:* second pass of `conjectures/202.lean` (Fable 5.2 review,
`fable-5-2-review/202.md`).
-/

/-- A system of congruence classes with distinct positive moduli at most N is
    *pairwise disjoint* if no integer belongs to more than one class.
    Each element (n, a) represents the congruence class {x ∈ ℤ : x ≡ a (mod n)}. -/
def IsPairwiseDisjointSystem (S : Finset (ℕ × ℤ)) (N : ℕ) : Prop :=
  (∀ p ∈ S, 1 ≤ p.1 ∧ p.1 ≤ N) ∧
  (∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.1 ≠ q.1) ∧
  (∀ p ∈ S, ∀ q ∈ S, p ≠ q →
    ∀ x : ℤ, ¬(x % (↑p.1 : ℤ) = p.2 % (↑p.1 : ℤ) ∧
               x % (↑q.1 : ℤ) = q.2 % (↑q.1 : ℤ)))

/--
Erdős Problem #202 (de la Bretèche–Ford–Vandehey conjecture)
[Er61, Er65, Er65b, Er73, Er77c, ErGr80, Va99]:

The maximum number f(N) of pairwise disjoint congruence classes with distinct
moduli at most N satisfies f(N) ≤ N / L(N)^{1-ε} for every ε > 0 and all
sufficiently large N, where L(N) = exp(√(log N · log log N)).

Combined with the proved lower bound f(N) ≥ N / L(N)^{1+ε} [BFV13], this
gives the conjectured asymptotics f(N) = N / L(N)^{1+o(1)}.

Status: OPEN at capture (2026-02-20); the mirror and upstream now record
f(N) = N · L(N)^{-1+o(1)} as proved, with a Lean proof (2026-05-14). Not proved here.
-/
theorem erdos_problem_202 :
    ∀ ε : ℝ, ε > 0 →
    ∀ᶠ N : ℕ in atTop,
    ∀ S : Finset (ℕ × ℤ),
    IsPairwiseDisjointSystem S N →
    (S.card : ℝ) ≤ (N : ℝ) /
      Real.exp ((1 - ε) * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) := by
  sorry

/-- The trivial bound `f(N) ≤ N` (PROVED in Lean): the moduli are distinct elements of
`{1, …, N}`. -/
theorem erdos_problem_202.card_le {S : Finset (ℕ × ℤ)} {N : ℕ}
    (h : IsPairwiseDisjointSystem S N) : S.card ≤ N := by
  have hinj : Set.InjOn (fun p : ℕ × ℤ => p.1) (S : Set (ℕ × ℤ)) := by
    intro p hp q hq hpq
    by_contra hne
    exact h.2.1 p hp q hq hne hpq
  have hmaps : Set.MapsTo (fun p : ℕ × ℤ => p.1) (S : Set (ℕ × ℤ))
      ((Finset.Icc 1 N : Finset ℕ) : Set ℕ) :=
    fun p hp => Finset.mem_coe.2 (Finset.mem_Icc.2 (h.1 p (Finset.mem_coe.1 hp)))
  have hle := Finset.card_le_card_of_injOn (fun p : ℕ × ℤ => p.1) hmaps hinj
  rw [Nat.card_Icc] at hle
  omega

/-- A system that contains a class of modulus `1` has no other class (PROVED in Lean): the class
is all of `ℤ`. -/
theorem erdos_problem_202.eq_of_modulus_one {S : Finset (ℕ × ℤ)} {N : ℕ}
    (h : IsPairwiseDisjointSystem S N) {p q : ℕ × ℤ} (hp : p ∈ S) (hq : q ∈ S)
    (hp1 : p.1 = 1) : p = q := by
  by_contra hne
  refine h.2.2 p hp q hq hne q.2 ⟨?_, rfl⟩
  rw [hp1]
  simp

/-- Sanity check (PROVED in Lean): the classes `1 mod 2`, `2 mod 4`, `4 mod 8` form a pairwise
disjoint system with moduli at most `8`. -/
theorem erdos_problem_202.example_system :
    IsPairwiseDisjointSystem {(2, 1), (4, 2), (8, 4)} 8 := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl <;> simp
  · intro p hp q hq hne
    simp at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> simp at hne ⊢
  · intro p hp q hq hne x
    simp at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | (simp only [Nat.cast_ofNat]; omega)

/-- The lower bound of de la Bretèche, Ford and Vandehey [BFV13] (SOLVED at capture; not proved
here): for every `ε > 0` and all large `N` there is a system with at least `N / L(N)^(1+ε)`
classes. With the main theorem this is `f(N) = N / L(N)^(1+o(1))`. -/
theorem erdos_problem_202.variants.lower :
    ∀ ε : ℝ, ε > 0 →
    ∀ᶠ N : ℕ in atTop,
    ∃ S : Finset (ℕ × ℤ),
    IsPairwiseDisjointSystem S N ∧
    (N : ℝ) /
      Real.exp ((1 + ε) * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) ≤
        (S.card : ℝ) := by
  sorry

/-- The Erdős–Stein conjecture `f(N) = o(N)`, proved by Erdős and Szemerédi [ErSz68] (SOLVED; not
proved here). -/
theorem erdos_problem_202.variants.erdos_szemeredi :
    ∀ ε : ℝ, ε > 0 →
    ∀ᶠ N : ℕ in atTop,
    ∀ S : Finset (ℕ × ℤ),
    IsPairwiseDisjointSystem S N →
    (S.card : ℝ) ≤ ε * (N : ℝ) := by
  sorry
