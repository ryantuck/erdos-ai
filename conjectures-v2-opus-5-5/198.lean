-- [AI - Claude Opus 5.5]: Erdős Problem 198 — second-pass formalization
import Mathlib.Data.Set.Function
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set

/-!
# Erdős Problem #198

*Source:* [erdosproblems.com/198](https://www.erdosproblems.com/198) (status **DISPROVED (LEAN)**:
"This has been solved in the negative and the proof verified in Lean."; captured 2026-03-05).
[ErGr79] [ErGr80]

If $A\subset \mathbb{N}$ is a Sidon set then must the complement of $A$ contain an infinite
arithmetic progression?

Remarks recorded on the page (abridged): the answer is no; Erdős and Graham report this was proved
by Baumgartner, presumably referring to [Ba75], which does not state this exactly, but a simple
construction is implicit there: choose $a_n$ in the $n$-th infinite progression with
$a_n>2a_{n-1}$; the result meets every infinite progression and is lacunary, hence Sidon.
AlphaProof found the explicit construction $A=\{(n+1)!+n : n\geq 0\}$: it is Sidon, and for any
$a,d$, $(a+d+1)!+(a+d)\in A$ and $d$ divides $(a+d+1)!+d$. See also [199].

## Encoding notes

* The theorem is the negative answer, stated as the negation of the property for infinite Sidon
  sets. The restriction to infinite sets is harmless: the complement of a finite set contains a
  tail of `ℕ`.
* **v2 proves the theorem in Lean**, with the AlphaProof set `A = {(n+1)! + n}`: the sequence
  more than doubles at each step (`s198_lacunary`), so it is Sidon (`isSidonSet_range_s198`); and
  `(a+d+1)! + (a+d) = a + ((a+d+1)!/d + 1)·d` meets every progression `a + n·d`, `d > 0`
  (`range_s198_meets`).

## References

No `/latex/198` fetch is in the session logs.
* [Ba75] Baumgartner, James E., _Partitioning vector spaces_. J. Combinatorial Theory Ser. A (1975),
  231–233. (From upstream `formal-conjectures`, `2befc3a`; **DEFERRED** as a site entry.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171.)

*Provenance:* second pass of `conjectures/198.lean` (Opus 5.5 review, `opus-5-5-review/198.md`).
-/

/--
A set A ⊆ ℕ is a **Sidon set** (or B₂ set) if all pairwise sums are distinct:
for a, b, c, d ∈ A with a ≤ b and c ≤ d, a + b = c + d implies a = c and b = d.
-/
def IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → a ≤ b → c ≤ d → a = c ∧ b = d

/--
The complement of A contains an **infinite arithmetic progression**: there exist
a ≥ 0 and d ≥ 1 such that a + n * d ∉ A for all n ∈ ℕ.
-/
def ComplementContainsInfiniteAP (A : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ n : ℕ, a + n * d ∉ A

/-- The AlphaProof sequence `s n = (n+1)! + n`. -/
def s198 (n : ℕ) : ℕ := (n + 1).factorial + n

/-- `s198` more than doubles at each step (PROVED in Lean). -/
theorem erdos_problem_198.s198_lacunary (n : ℕ) : 2 * s198 n < s198 (n + 1) := by
  unfold s198
  have hF : n + 1 ≤ (n + 1).factorial := Nat.self_le_factorial _
  have hsucc : (n + 1 + 1).factorial = (n + 2) * (n + 1).factorial := Nat.factorial_succ _
  rw [hsucc]
  nlinarith

/-- `s198` is strictly increasing (PROVED in Lean). -/
theorem erdos_problem_198.s198_strictMono : StrictMono s198 :=
  strictMono_nat_of_lt_succ fun n => by
    have := erdos_problem_198.s198_lacunary n
    have : 0 < s198 n := by unfold s198; positivity
    omega

/-- A later term exceeds twice an earlier one (PROVED in Lean). -/
theorem erdos_problem_198.two_mul_lt {j m : ℕ} (h : j < m) : 2 * s198 j < s198 m :=
  lt_of_lt_of_le (erdos_problem_198.s198_lacunary j) (erdos_problem_198.s198_strictMono.monotone h)

/-- The range of `s198` is a Sidon set (PROVED in Lean). -/
theorem erdos_problem_198.isSidonSet_range_s198 : IsSidonSet (range s198) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ hsum hij hkl
  have hjl : j = l := by
    rcases lt_trichotomy j l with h | h | h
    · have := erdos_problem_198.two_mul_lt h
      omega
    · exact h
    · have := erdos_problem_198.two_mul_lt h
      omega
  subst hjl
  have hik : s198 i = s198 k := by omega
  exact ⟨hik, rfl⟩

/-- The range of `s198` meets every infinite arithmetic progression `a + n·d`, `d > 0` (PROVED in
Lean): `(a+d+1)! + (a+d)` lies on it. -/
theorem erdos_problem_198.range_s198_meets (a d : ℕ) (hd : 0 < d) :
    ∃ n : ℕ, a + n * d ∈ range s198 := by
  obtain ⟨q, hq⟩ := Nat.dvd_factorial hd (show d ≤ a + d + 1 by omega)
  refine ⟨q + 1, a + d, ?_⟩
  unfold s198
  rw [hq]
  ring

/--
Erdős Problem #198 [ErGr79, ErGr80]:

If A ⊂ ℕ is a Sidon set then must the complement of A contain an infinite
arithmetic progression?

The answer is **no** (DISPROVED). Erdős and Graham report this was proved by
Baumgartner [Ba75]. A simple construction: enumerate all infinite arithmetic
progressions P₁, P₂, … and greedily choose aₙ ∈ Pₙ with aₙ > 2aₙ₋₁. The
resulting lacunary set is Sidon and hits every infinite AP.

AlphaProof gave the explicit construction A = {(n+1)! + n : n ≥ 0}, which is
Sidon and intersects every infinite arithmetic progression. (PROVED here in Lean.)
-/
theorem erdos_problem_198 :
    ¬ (∀ A : Set ℕ, Set.Infinite A → IsSidonSet A →
      ComplementContainsInfiniteAP A) := by
  intro h
  obtain ⟨a, d, hd, hA⟩ := h (range s198)
    (Set.infinite_range_of_injective erdos_problem_198.s198_strictMono.injective)
    erdos_problem_198.isSidonSet_range_s198
  obtain ⟨n, hn⟩ := erdos_problem_198.range_s198_meets a d hd
  exact hA n hn
