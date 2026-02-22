import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Lattice

noncomputable section

/-!
# Erdős Problem #724

Let f(n) be the maximum number of mutually orthogonal Latin squares of order n.
Is it true that f(n) ≫ n^{1/2}?

A Latin square of order n is an n × n array filled with n symbols such that
each symbol occurs exactly once in each row and each column.

Two Latin squares L₁, L₂ of order n are orthogonal if the map
(i, j) ↦ (L₁(i,j), L₂(i,j)) is injective (equivalently bijective) on
Fin n × Fin n, i.e., every ordered pair of symbols occurs exactly once
when the squares are superimposed.

Chowla, Erdős, and Straus [CES60] proved f(n) ≫ n^{1/91}.
Wilson [Wi74] improved this to f(n) ≫ n^{1/17}.
Beth [Be83c] improved this to f(n) ≫ n^{1/14.8}.
-/

/-- A Latin square of order n: a function `Fin n → Fin n → Fin n` such that
    each row and each column is a bijection. -/
def IsLatinSquare {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ i : Fin n, Function.Bijective (L i)) ∧
  (∀ j : Fin n, Function.Bijective (fun i => L i j))

/-- Two Latin squares of order n are orthogonal if the map
    `(i, j) ↦ (L₁ i j, L₂ i j)` is injective on `Fin n × Fin n`. -/
def AreOrthogonalLatinSquares {n : ℕ} (L₁ L₂ : Fin n → Fin n → Fin n) : Prop :=
  Function.Injective (fun p : Fin n × Fin n => (L₁ p.1 p.2, L₂ p.1 p.2))

/-- A family of k Latin squares of order n is mutually orthogonal if each
    is a Latin square and every distinct pair is orthogonal. -/
def IsMOLS {n k : ℕ} (L : Fin k → Fin n → Fin n → Fin n) : Prop :=
  (∀ i : Fin k, IsLatinSquare (L i)) ∧
  (∀ i j : Fin k, i ≠ j → AreOrthogonalLatinSquares (L i) (L j))

/-- The maximum number of mutually orthogonal Latin squares of order n. -/
noncomputable def maxMOLS (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ L : Fin k → Fin n → Fin n → Fin n, IsMOLS L}

/--
Erdős Problem #724 [Er81]:

Let f(n) be the maximum number of mutually orthogonal Latin squares of order n.
Is it true that f(n) ≫ n^{1/2}?

Formalized as: there exists a constant C > 0 such that for all sufficiently
large n, maxMOLS(n) ≥ C · √n.
-/
theorem erdos_problem_724 :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxMOLS n : ℝ) ≥ C * Real.sqrt (n : ℝ) :=
  sorry

end
