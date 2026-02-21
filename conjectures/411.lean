import Mathlib.Data.Nat.Totient

/-- The function g(n) = n + φ(n) from Erdős Problem #411. -/
def erdos411_g (n : ℕ) : ℕ := n + Nat.totient n

/-!
# Erdős Problem #411

Let g(n) = n + φ(n) and g_k denote the k-th iterate of g, so
g₁(n) = g(n) = n + φ(n) and g_k(n) = g(g_{k-1}(n)).

For which n and r is it true that g_{k+r}(n) = 2·g_k(n) for all
sufficiently large k?

The known solutions to g_{k+2}(n) = 2·g_k(n) are n = 10 and n = 94.
Selfridge and Weintraub found solutions to g_{k+9}(n) = 9·g_k(n) and
Weintraub found g_{k+25}(3114) = 729·g_k(3114) for all k ≥ 6.

Cambie conjectures that the only solutions have r = 2 and
n = 2^l · p for some l ≥ 1 and p ∈ {2, 3, 5, 7, 35, 47}.
We formalize Cambie's conjecture.
-/

/--
Erdős Problem #411 [ErGr80, p.81] — Cambie's conjecture:

If g(n) = n + φ(n) and g_{k+r}(n) = 2·g_k(n) for all sufficiently large k,
then r = 2 and n = 2^l · p for some l ≥ 1 and p ∈ {2, 3, 5, 7, 35, 47}.
-/
theorem erdos_problem_411 (n r : ℕ) (hn : 0 < n) (hr : 0 < r)
    (h : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → erdos411_g^[k + r] n = 2 * erdos411_g^[k] n) :
    r = 2 ∧ ∃ l : ℕ, 1 ≤ l ∧
      ∃ p : ℕ, (p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 35 ∨ p = 47) ∧
        n = 2 ^ l * p :=
  sorry
