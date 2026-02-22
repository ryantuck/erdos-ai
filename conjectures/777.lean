import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #777

If F is a family of subsets of {1,…,n}, write G_F for the comparability graph
on F where A ~ B iff A ⊆ B or B ⊆ A. Let m = |F|.

Three questions of Daykin and Erdős:

1. If ε > 0 and n is sufficiently large, whenever m ≤ (2-ε)·2^{n/2} does G_F
   have < 2^n edges?

2. If G_F has ≥ c·m² edges, must m ≪_c 2^{n/2}?

3. For any ε > 0, does there exist δ > 0 such that if there are > m^{2-δ}
   edges then m < (2+ε)^{n/2}?

The first question was answered affirmatively by Alon, Das, Glebov, and Sudakov.
The second question was answered negatively by Alon and Frankl.
The third question was answered affirmatively by Alon and Frankl.

https://www.erdosproblems.com/777

Tags: graph theory, combinatorics
-/

/-- The number of edges of the comparability graph of a family F of subsets of
    Fin n: the number of ordered pairs (A, B) in F × F with A ≠ B and A ⊆ B.
    Each unordered comparable pair {A, B} is counted exactly once (the one with
    A ⊊ B). -/
def comparableEdges777 (n : ℕ) (F : Finset (Finset (Fin n))) : ℕ :=
  ((F ×ˢ F).filter (fun p => p.1 ≠ p.2 ∧ p.1 ⊆ p.2)).card

/--
**Erdős Problem #777, Question 1** (SOLVED, affirmative — Alon-Das-Glebov-Sudakov):

For all ε > 0, if n is sufficiently large and F is a family of at most
⌊(2 - ε) · 2^{n/2}⌋ subsets of {0,…,n-1}, then the comparability graph of F
has fewer than 2^n edges.
-/
theorem erdos_problem_777_q1 :
    ∀ ε : ℝ, ε > 0 → ε < 2 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ F : Finset (Finset (Fin n)),
        (F.card : ℝ) ≤ (2 - ε) * (2 : ℝ) ^ ((n : ℝ) / 2) →
        comparableEdges777 n F < 2 ^ n :=
  sorry

/--
**Erdős Problem #777, Question 2** (SOLVED, negative — Alon-Frankl):

The answer to Question 2 is no. There exists c > 0 such that for all C > 0,
for sufficiently large n, there is a family F of subsets of {0,…,n-1} with
|F| > C · 2^{n/2} and at least c · |F|² comparable pairs.

(Alon and Frankl show one may take c = 2⁻⁵ and |F| ≫ n · 2^{n/2}.)
-/
theorem erdos_problem_777_q2_counterexample :
    ∃ c : ℝ, c > 0 ∧
    ∀ C : ℝ, C > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        ∃ F : Finset (Finset (Fin n)),
          (F.card : ℝ) > C * (2 : ℝ) ^ ((n : ℝ) / 2) ∧
          (comparableEdges777 n F : ℝ) ≥ c * (F.card : ℝ) ^ 2 :=
  sorry

/--
**Erdős Problem #777, Question 3** (SOLVED, affirmative — Alon-Frankl):

For all ε > 0, there exists δ > 0 such that for all n and every family F of
subsets of {0,…,n-1}, if the number of comparable pairs exceeds |F|^{2-δ},
then |F| < (2 + ε)^{n/2}.
-/
theorem erdos_problem_777_q3 :
    ∀ ε : ℝ, ε > 0 →
    ∃ δ : ℝ, δ > 0 ∧
      ∀ (n : ℕ) (F : Finset (Finset (Fin n))),
        (comparableEdges777 n F : ℝ) > (F.card : ℝ) ^ ((2 : ℝ) - δ) →
        (F.card : ℝ) < ((2 : ℝ) + ε) ^ ((n : ℝ) / 2) :=
  sorry

end
