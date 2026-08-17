import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
A finite set A of natural numbers has **distinct subset sums** if for any two
subsets S₁, S₂ ⊆ A, equality of their sums implies S₁ = S₂.
-/
def DistinctSubsetSums (A : Finset ℕ) : Prop :=
  ∀ S₁ ∈ A.powerset, ∀ S₂ ∈ A.powerset,
    S₁.sum id = S₂.sum id → S₁ = S₂

/--
Erdős Problem #1 [Er56, Er57, Er59, Er61, Er65b, Er69, Er70b, Er70c, Er73,
BeEr74, ErSp74, Er75b, Er77c, ErGr80, Er81, Er82e, Er85c, Er90, Er91, Er92b,
Er95, Er97c, Er98, Va99]:

If A ⊆ {1,…,N} with |A| = n is such that the subset sums ∑_{a ∈ S} a are
distinct for all S ⊆ A, then N ≫ 2ⁿ, i.e., there exists an absolute constant
C > 0 such that N ≥ C · 2ⁿ.

This problem is OPEN, with a $500 prize (erdosproblems.com, page last edited
23 January 2026, accessed 2026-02-13; status cross-checked open against the
teorth/erdosproblems metadata mirror).

Erdős called this "perhaps my first serious problem" (in [Er98] he dates it
to 1931). The powers of 2 show that 2ⁿ would be best possible. The trivial
lower bound is N ≫ 2ⁿ/n, since all 2ⁿ distinct subset sums must lie in
[0, Nn). Erdős and Moser [Er56] proved N ≥ (1/4 − o(1)) · 2ⁿ/√n; in [Er85c]
Erdős offered $100 for any improvement of the constant 1/4. After a series of
improvements (see [St23] for a history), the current record constant √(2/π)
was first proved in unpublished work of Elkies and Gleason; Dubroff, Fox, and
Xu [DFX21] give two proofs achieving this constant, and in fact prove the
exact bound N ≥ C(n, ⌊n/2⌋).

The hypothesis N ≠ 0 excludes the degenerate case N = 0, A = ∅, n = 0
(permitted by the remaining hypotheses), which would otherwise falsify the
statement outright: it would force 0 ≥ C · 2⁰ = C > 0. The upstream
formal-conjectures statement of this problem carries the same guard.

In [Er73] and [ErGr80] the generalisation where A ⊆ (0, N] is a set of real
numbers whose subset sums all differ by at least 1 is proposed, with the same
conjectured bound (see variant below); this generalisation seems to have
first appeared in [Gr71]. The sequence of minimal N for a given n is OEIS
A276661. See also Erdős problem [350]; the problem is discussed as problem C8
of Guy's collection [Gu04].

References (recovered from the archived page, the upstream formal-conjectures
file, and sibling files in this repo; entries marked "stub" lack full
journal/volume/page data, which is DEFERRED, not fabricated):
- [Er56] Erdős, P., Problems and results in additive number theory. Colloque
  sur la Théorie des Nombres, Bruxelles, 1955 (1956), 127-137.
- [Er57] Erdős, P., Some unsolved problems (1957). (stub)
- [Er61] Erdős, P., Some unsolved problems. Magyar Tud. Akad. Mat. Kutató
  Int. Közl. 6 (1961), 221-254.
- [Er65b] Erdős, P., Extremal problems in number theory (1965). (stub;
  sibling files disagree on the title of this key)
- [Er73] Erdős, P., Problems and results on combinatorial number theory.
  A survey of combinatorial theory (Proc. Internat. Sympos., Colorado State
  Univ., Fort Collins, Colo., 1971) (1973), 117-138.
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in
  combinatorial number theory. Monographies de L'Enseignement Mathématique
  (1980).
- [Er98] Erdős, P., Some of my new and almost new problems and results in
  combinatorial number theory. Number theory (Eger, 1996) (1998), 169-180.
- [DFX21] Dubroff, Q., Fox, J., and Xu, M. W. (2021). (stub)
- [Gu04] Guy, R. K., Unsolved problems in number theory (2004), xviii+437.
- [Gr71], [St23], [Ru99], and the remaining page keys: see
  erdosproblems.com/latex/1 (bibliographic data not recoverable offline).
-/
theorem erdos_problem_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N n : ℕ) (A : Finset ℕ),
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
        A.card = n →
        DistinctSubsetSums A →
        N ≠ 0 →
        (N : ℝ) ≥ C * 2 ^ n :=
  sorry

/--
Erdős Problem #1, trivial-bound variant:

The trivial lower bound is N ≫ 2ⁿ/n, since all 2ⁿ distinct subset sums must
lie in [0, Nn) (erdosproblems.com remarks; an exercise, stated here for
completeness). At n = 0 the real division by zero makes the right-hand side
0 and the inequality trivially true, which is harmless.
-/
theorem erdos_problem_1.variants.trivial_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (A : Finset ℕ),
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
        DistinctSubsetSums A →
        N ≠ 0 →
        (N : ℝ) ≥ C * 2 ^ A.card / (A.card : ℝ) :=
  sorry

/--
Erdős Problem #1, Dubroff–Fox–Xu variant [DFX21]:

Dubroff, Fox, and Xu (2021) proved the exact bound N ≥ C(n, ⌊n/2⌋) for any
A ⊆ {1,…,N} with |A| = n and distinct subset sums. This is the current record
lower bound; asymptotically it gives the constant √(2/π) in
N ≥ (√(2/π) − o(1)) · 2ⁿ/√n, first obtained in unpublished work of Elkies and
Gleason. Consistent with OEIS A276661: for n = 3, 5, 9 the minimal N is
4, 13, 161 against C(n, ⌊n/2⌋) = 3, 10, 126. Note ⌊n/2⌋ is ℕ division n / 2.
-/
theorem erdos_problem_1.variants.dubroff_fox_xu :
    ∀ (N : ℕ) (A : Finset ℕ),
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      DistinctSubsetSums A →
      N ≠ 0 →
      A.card.choose (A.card / 2) ≤ N :=
  sorry

/--
Erdős Problem #1, real-number generalisation [Er73, ErGr80, Gr71]:

If A ⊆ (0, N] is a finite set of real numbers whose subset sums all differ
by at least 1 (for distinct subsets), then N ≫ 2ⁿ, with the same conjectured
bound as the integer problem. Proposed in [Er73] and [ErGr80]; it seems to
have first appeared in [Gr71]. The second proof of [DFX21] applies to this
generalisation as well, giving the same √(2/π) constant. OPEN, like the main
problem. The N ≠ 0 guard excludes the same degenerate falsifying case
(N = 0 forces A = ∅ since (0, 0] = ∅).
-/
theorem erdos_problem_1.variants.real_generalisation :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (A : Finset ℝ),
        (∀ a ∈ A, 0 < a ∧ a ≤ N) →
        (∀ S₁ ∈ A.powerset, ∀ S₂ ∈ A.powerset,
          S₁ ≠ S₂ → 1 ≤ |S₁.sum id - S₂.sum id|) →
        N ≠ 0 →
        (N : ℝ) ≥ C * 2 ^ A.card :=
  sorry
