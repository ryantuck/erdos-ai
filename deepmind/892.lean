/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 892

*Reference:* [erdosproblems.com/892](https://www.erdosproblems.com/892)

Is there a necessary and sufficient condition for a sequence of integers
$b_1 < b_2 < \cdots$ that ensures there exists a primitive sequence
$a_1 < a_2 < \cdots$ (i.e. no element divides another) with $a_n \ll b_n$
for all $n$?

[ESS68] Erdős, P., Sárközy, A., and Szemerédi, E.

[Er98] Erdős, P.
-/

namespace Erdos892

/-- A sequence of natural numbers is *primitive* if no element divides any other. -/
def IsPrimitiveSeq (a : ℕ → ℕ) : Prop :=
  ∀ i j, i ≠ j → ¬(a i ∣ a j)

/--
Erdős Problem 892 (particular case) [Er98]:

If $b : \mathbb{N} \to \mathbb{N}$ is a strictly increasing sequence of positive integers such that
$\gcd(b_i, b_j) \neq b_k$ for all distinct $i, j$ and all $k$ (no non-trivial GCD solutions),
then there exists a strictly increasing primitive sequence $a : \mathbb{N} \to \mathbb{N}$ with
$a_n \ll b_n$ (i.e. there exists $C$ such that $a_n \leq C \cdot b_n$ for all $n$).
-/
@[category research open, AMS 11]
theorem erdos_892
    (b : ℕ → ℕ)
    (hb_pos : ∀ n, 0 < b n)
    (hb_mono : StrictMono b)
    (hb_gcd : ∀ i j, i ≠ j → ∀ k, Nat.gcd (b i) (b j) ≠ b k) :
    ∃ (a : ℕ → ℕ) (C : ℕ),
      0 < C ∧
      StrictMono a ∧
      IsPrimitiveSeq a ∧
      ∀ n, a n ≤ C * b n := by
  sorry

end Erdos892
