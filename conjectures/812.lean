import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #812

Is it true that R(n+1)/R(n) ≥ 1 + c for some constant c > 0, for all large n?
Is it true that R(n+1) - R(n) ≫ n²?

Here R(n) denotes the diagonal Ramsey number R(n,n): the minimum N such that
every simple graph on N vertices contains either a clique of size n or an
independent set of size n.

Burr, Erdős, Faudree, and Schelp [BEFS89] proved that R(n+1) - R(n) ≥ 4n - 8
for all n ≥ 2. The lower bound from Problem #165 implies that
R(n+2) - R(n) ≫ n^{2-o(1)}.
-/

/-- The diagonal Ramsey number R(n) = R(n,n): the minimum N such that every
    simple graph on N vertices contains either an n-clique or an independent
    set of size n (an n-clique in the complement). -/
noncomputable def diagonalRamsey (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree n ∨ ¬Gᶜ.CliqueFree n}

/--
**Erdős Problem #812, Part 1** [Er91]:

There exists a constant c > 0 such that R(n+1)/R(n) ≥ 1 + c for all
sufficiently large n. That is, the diagonal Ramsey numbers grow at least
geometrically.
-/
theorem erdos_problem_812a :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (diagonalRamsey (n + 1) : ℝ) / (diagonalRamsey n : ℝ) ≥ 1 + c :=
  sorry

/--
**Erdős Problem #812, Part 2** [Er91]:

R(n+1) - R(n) ≫ n², i.e., there exists a constant c > 0 such that
R(n+1) - R(n) ≥ c · n² for all sufficiently large n.
-/
theorem erdos_problem_812b :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (diagonalRamsey (n + 1) : ℝ) - (diagonalRamsey n : ℝ) ≥ c * (n : ℝ) ^ 2 :=
  sorry

end
