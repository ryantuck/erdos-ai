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
# Erdős Problem 281

*Reference:* [erdosproblems.com/281](https://www.erdosproblems.com/281)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Classical

namespace Erdos281

/-- Count of integers in $\{0, \ldots, N-1\}$ not in any congruence class $a(i) \bmod n(i)$
for all $i$. -/
noncomputable def avoidCountAll (n a : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun m =>
    ∀ i : ℕ, ¬(m ≡ a i [MOD n i])).card

/-- Count of integers in $\{0, \ldots, N-1\}$ avoiding congruences $a(i) \bmod n(i)$
for $i < k$. -/
noncomputable def avoidCountFin (n a : ℕ → ℕ) (k N : ℕ) : ℕ :=
  ((Finset.range N).filter fun m =>
    ∀ i, i < k → ¬(m ≡ a i [MOD n i])).card

/--
Erdős Problem 281 (Proved) [ErGr80, p.29]:

Let $n_1 < n_2 < \cdots$ be a strictly increasing sequence of positive integers such that,
for any choice of congruence classes $a_i \pmod{n_i}$, the set of integers not satisfying
any of the congruences has density $0$. Then for every $\varepsilon > 0$ there exists some $k$
such that, for every choice of congruence classes $a_i$, the density of integers not
satisfying any of the congruences $a_i \pmod{n_i}$ for $i < k$ is less than $\varepsilon$.

The proof combines the Davenport–Erdős theorem with Rogers' optimal sieve bound.
-/
@[category research solved, AMS 11]
theorem erdos_281
    (n : ℕ → ℕ)
    (hn_pos : ∀ i, 0 < n i)
    (hn_mono : StrictMono n)
    (h_cover : ∀ a : ℕ → ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (avoidCountAll n a N : ℝ) / (N : ℝ) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ,
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (avoidCountFin n a k N : ℝ) / (N : ℝ) < ε := by
  sorry

end Erdos281
