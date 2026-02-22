import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open Finset

noncomputable section

/-!
# Erdős Problem #1015

Let f(t, n) be minimal such that, in any two-colouring of the edges of Kₙ,
the vertices can be covered by vertex-disjoint monochromatic copies of Kₜ
(not necessarily the same colour) with at most f(t, n) vertices remaining.

Estimate f(t). In particular, is it true that f(t)^{1/t} → 1?
Is it true that f(t) ≪ t?

A question of Moon [Mo66b], who proved that f(3, n) = 4 for n ≥ 8.
Erdős notes that f(t) ≪ 4^t, by comparing to the Ramsey number R(t).

Burr, Erdős, and Spencer [BES75] proved that, for n sufficiently large
depending on t,
  f(t, n) = R(t, t−1) + x(t, n),
where 0 ≤ x(t, n) < t is such that n + 1 ≡ R(t, t−1) + x (mod t).
-/

/-- A set `S` of vertices in `Fin n` is a monochromatic clique of colour `b`
    under the edge-colouring `c` if every pair of distinct vertices in `S`
    has colour `b`. -/
def IsMonoClique (n : ℕ) (c : Fin n → Fin n → Bool) (S : Finset (Fin n))
    (b : Bool) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = b

/-- The minimum number of leftover vertices f(t, n): the smallest r such
    that for every symmetric 2-colouring of the edges of Kₙ, one can find
    pairwise disjoint monochromatic Kₜ's covering all but at most r
    vertices. -/
def minLeftover (t n : ℕ) : ℕ :=
  sInf {r : ℕ | ∀ (c : Fin n → Fin n → Bool), (∀ i j, c i j = c j i) →
    ∃ (cliques : Finset (Finset (Fin n))),
      (∀ S ∈ cliques, S.card = t) ∧
      (∀ S ∈ cliques, ∃ b : Bool, IsMonoClique n c S b) ∧
      (∀ S₁ ∈ cliques, ∀ S₂ ∈ cliques, S₁ ≠ S₂ → Disjoint S₁ S₂) ∧
      (Finset.univ \ cliques.biUnion id).card ≤ r}

/-- The 2-colour Ramsey number R(s, t): the minimum N such that every
    symmetric 2-colouring of the edges of Kₙ contains a monochromatic
    clique of size s in one colour or of size t in the other. -/
def ramseyNumber₂ (s t : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Bool), (∀ i j, c i j = c j i) →
    (∃ S : Finset (Fin N), S.card = s ∧ IsMonoClique N c S false) ∨
    (∃ S : Finset (Fin N), S.card = t ∧ IsMonoClique N c S true)}

/--
Erdős Problem #1015 [Er71]:

For all t ≥ 2, for n sufficiently large depending on t, the minimum number
of leftover vertices when partitioning any 2-colouring of Kₙ into
vertex-disjoint monochromatic Kₜ's is exactly
  f(t, n) = R(t, t−1) + x,
where x ∈ {0, …, t−1} satisfies n + 1 ≡ R(t, t−1) + x (mod t).

Proved by Burr, Erdős, and Spencer [BES75].
-/
theorem erdos_problem_1015 (t : ℕ) (ht : t ≥ 2) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      minLeftover t n =
        ramseyNumber₂ t (t - 1) + (n + 1 - ramseyNumber₂ t (t - 1)) % t :=
  sorry

end
