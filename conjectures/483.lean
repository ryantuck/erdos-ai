import Mathlib.Data.Real.Basic

/-- A coloring `f : ℕ → Fin k` has a *monochromatic Schur triple* in `{1,…,N}` if
    there exist `a, b ≥ 1` with `a + b ≤ N` and `f a = f b = f (a + b)`. -/
def HasMonochromaticSchurTriple (k N : ℕ) (f : ℕ → Fin k) : Prop :=
  ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ a + b ≤ N ∧ f a = f b ∧ f b = f (a + b)

/--
Erdős Problem #483 [Er61, p.233] [Er65, p.188]:

Let f(k) be the minimal N such that if {1,…,N} is k-coloured then there is a
monochromatic solution to a + b = c. The values f(k) are known as Schur numbers.

Estimate f(k). In particular, is it true that f(k) < c^k for some constant c > 0?

The best-known bounds for large k are
  (380)^(k/5) - O(1) ≤ f(k) ≤ ⌊(e - 1/24) k!⌋ - 1.
The known values are f(1)=2, f(2)=5, f(3)=14, f(4)=45, f(5)=161 (OEIS A030126).

We formalize the conjecture: there exists c > 0 such that for all k ≥ 1,
every k-coloring of {1,…,N} with N ≥ c^k has a monochromatic Schur triple.
Equivalently, the Schur number f(k) grows at most exponentially in k.
-/
theorem erdos_problem_483 :
    ∃ c : ℝ, 0 < c ∧
      ∀ k : ℕ, 1 ≤ k →
        ∀ N : ℕ, c ^ k ≤ (N : ℝ) →
          ∀ f : ℕ → Fin k,
            HasMonochromaticSchurTriple k N f :=
  sorry
