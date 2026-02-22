import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Real

/-!
# Erdős Problem #962

Let $k(n)$ be the maximal $k$ such that there exists $m \leq n$ such that each
of the integers $m+1, \ldots, m+k$ are divisible by at least one prime $> k$.
Estimate $k(n)$.

A problem of Erdős [Er65].

Erdős wrote it is 'not hard to prove' that $k(n) \gg_\epsilon \exp((\log n)^{1/2-\epsilon})$
and it 'seems likely' that $k(n) = o(n^\epsilon)$.

Tao gave a simple argument proving $k(n) \leq (1+o(1))n^{1/2}$.

Tang proved a lower bound of $k(n) \geq \exp((1/\sqrt{2} - o(1))\sqrt{\log n \log\log n})$.
-/

/--
`erdos962_k n` is the maximal `k` such that there exists `m ≤ n` with every
integer in {m+1, …, m+k} divisible by at least one prime greater than `k`.
-/
noncomputable def erdos962_k (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ m : ℕ, m ≤ n ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ k → ∃ p : ℕ, Nat.Prime p ∧ p > k ∧ p ∣ (m + i)}

/--
Erdős Problem #962, conjecture [Er65]:

$k(n) = o(n^\epsilon)$ for every $\epsilon > 0$. That is, for every $\epsilon > 0$,
$k(n) / n^\epsilon \to 0$ as $n \to \infty$.
-/
theorem erdos_problem_962 (ε : ℝ) (hε : ε > 0) :
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos962_k n : ℝ) ≤ δ * (n : ℝ) ^ ε :=
  sorry

/--
Erdős Problem #962, Tao's upper bound:

$k(n) \leq (1+o(1)) n^{1/2}$. Formulated as: for every $\epsilon > 0$, there
exists $N_0$ such that for all $n \geq N_0$, $k(n) \leq (1+\epsilon) \sqrt{n}$.
-/
theorem erdos_problem_962_tao_upper (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos962_k n : ℝ) ≤ (1 + ε) * (n : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

/--
Erdős Problem #962, Erdős lower bound [Er65]:

$k(n) \gg_\epsilon \exp((\log n)^{1/2-\epsilon})$ for every $\epsilon > 0$.
Formulated as: for every $\epsilon > 0$, there exist $C > 0$ and $N_0$ such that
for all $n \geq N_0$, $k(n) \geq C \cdot \exp((\log n)^{1/2-\epsilon})$.
-/
theorem erdos_problem_962_erdos_lower (ε : ℝ) (hε : ε > 0) :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos962_k n : ℝ) ≥ C * exp ((log (n : ℝ)) ^ ((1 : ℝ) / 2 - ε)) :=
  sorry

/--
Erdős Problem #962, Tang's lower bound:

$k(n) \geq \exp((1/\sqrt{2} - o(1))\sqrt{\log n \cdot \log\log n})$.
Formulated as: for every $\epsilon > 0$, there exists $N_0$ such that for all
$n \geq N_0$, $k(n) \geq \exp((1/\sqrt{2} - \epsilon) \cdot \sqrt{\log n \cdot \log(\log n)})$.
-/
theorem erdos_problem_962_tang_lower (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos962_k n : ℝ) ≥
        exp ((1 / sqrt 2 - ε) * sqrt (log (n : ℝ) * log (log (n : ℝ)))) :=
  sorry

end
