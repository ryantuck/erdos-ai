import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Erdős Problem #924

Let k ≥ 2 and l ≥ 3. Is there a graph G which contains no K_{l+1} such that
every k-colouring of the edges of G contains a monochromatic copy of K_l?

A question of Erdős and Hajnal [Er69b][Er75b]. Folkman [Fo70] proved this
when k = 2. The case for general k was proved by Nešetřil and Rödl [NeRo76].

See #582 for the special case k = 2, l = 3 and #966 for an arithmetic analogue.
-/

/--
Erdős Problem #924 [Er69b][Er75b]:

For all k ≥ 2 and l ≥ 3, there exists a K_{l+1}-free graph G such that every
k-colouring of the edges of G contains a monochromatic K_l.

Proved by Nešetřil and Rödl [NeRo76].
-/
theorem erdos_problem_924 (k : ℕ) (l : ℕ) (hk : k ≥ 2) (hl : l ≥ 3) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.CliqueFree (l + 1) ∧
        ∀ (c : Fin n → Fin n → Fin k),
          (∀ i j, c i j = c j i) →
          ∃ (a : Fin k) (S : Finset (Fin n)),
            G.IsNClique l S ∧
            ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → c x y = a :=
  sorry
