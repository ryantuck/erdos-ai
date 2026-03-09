import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
Erdős Problem #541 [Er73, ErGr80]:

Let a₁, …, aₚ be (not necessarily distinct) residues modulo a prime p,
such that there exists some r so that every non-empty subset S ⊆ {1,…,p}
with ∑_{i ∈ S} aᵢ ≡ 0 (mod p) satisfies |S| = r. Must there be at most
two distinct residues amongst the aᵢ?

A question of Graham. Proved by Erdős and Szemerédi for p sufficiently large,
and by Gao, Hamidoune, and Wang for all moduli (not necessarily prime).
-/
theorem erdos_problem_541 (p : ℕ) [hp : Fact (Nat.Prime p)]
    (a : Fin p → ZMod p)
    (r : ℕ)
    (hr : ∀ S : Finset (Fin p), S.Nonempty →
      ∑ i ∈ S, a i = 0 → S.card = r) :
    (Finset.image a Finset.univ).card ≤ 2 :=
  sorry
