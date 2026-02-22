import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

noncomputable section

/-!
# Erdős Problem #781

Let $f(k)$ be the minimal $n$ such that any 2-colouring of $\{1,\ldots,n\}$ contains
a monochromatic $k$-term descending wave: a sequence $x_1 < \cdots < x_k$ such that,
for $1 < j < k$, $x_j \geq (x_{j+1} + x_{j-1}) / 2$.

A problem of Brown, Erdős, and Freedman [BEF90], who proved
  $k^2 - k + 1 \leq f(k) \leq (k^3 - 4k + 9) / 3$.

They conjectured $f(k) = k^2 - k + 1$ for all $k$.
Disproved by Alon and Spencer [AlSp89] who proved $f(k) \gg k^3$.
-/

/-- A k-term descending wave in {0, …, n-1}: a strictly increasing sequence
    x : Fin k → Fin n such that for every interior index j (0 < j and j+1 < k),
    2 * x(j) ≥ x(j+1) + x(j-1).

    Equivalently, the gaps x(j+1) - x(j) are non-increasing. -/
def IsDescendingWave (k n : ℕ) (x : Fin k → Fin n) : Prop :=
  StrictMono x ∧
  ∀ (j : Fin k) (_ : 0 < j.val) (hj : j.val + 1 < k),
    2 * (x j).val ≥ (x ⟨j.val + 1, hj⟩).val + (x ⟨j.val - 1, by omega⟩).val

/-- A 2-colouring of {0, …, n-1} contains a monochromatic k-term descending wave. -/
def HasMonochromaticDescendingWave (k n : ℕ) (c : Fin n → Bool) : Prop :=
  ∃ x : Fin k → Fin n, IsDescendingWave k n x ∧
    ∃ a : Bool, ∀ i : Fin k, c (x i) = a

/-- f(k): the minimal n such that every 2-colouring of {0, …, n-1} contains
    a monochromatic k-term descending wave. -/
noncomputable def descendingWaveNumber (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ c : Fin n → Bool, HasMonochromaticDescendingWave k n c}

/--
Erdős Problem #781, lower bound [BEF90]:

For all k ≥ 1, f(k) ≥ k² - k + 1.
-/
theorem erdos_problem_781_lower (k : ℕ) (hk : k ≥ 1) :
    descendingWaveNumber k ≥ k ^ 2 - k + 1 :=
  sorry

/--
Erdős Problem #781, upper bound [BEF90]:

For all k ≥ 2, f(k) ≤ (k³ - 4k + 9) / 3.
-/
theorem erdos_problem_781_upper (k : ℕ) (hk : k ≥ 2) :
    descendingWaveNumber k ≤ (k ^ 3 - 4 * k + 9) / 3 :=
  sorry

/--
Alon-Spencer [AlSp89]: f(k) ≫ k³.

There exists C > 0 such that for all sufficiently large k,
f(k) ≥ C · k³. This disproves the conjecture that f(k) = k² - k + 1.
-/
theorem erdos_problem_781_alon_spencer :
    ∃ C : ℝ, C > 0 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (descendingWaveNumber k : ℝ) ≥ C * (k : ℝ) ^ 3 :=
  sorry

end
