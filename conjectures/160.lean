import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

open Finset

/--
A coloring `f : ℕ → Fin k` is **rainbow on 4-APs** in `{1,…,N}` if every
four-term arithmetic progression `{a, a+d, a+2d, a+3d} ⊆ {1,…,N}` uses at
least three distinct colours.
-/
def RainbowOn4AP (N : ℕ) (k : ℕ) (f : ℕ → Fin k) : Prop :=
  ∀ a d : ℕ, 0 < d → 1 ≤ a → a + 3 * d ≤ N →
    2 < ({f a, f (a + d), f (a + 2 * d), f (a + 3 * d)} : Finset (Fin k)).card

/--
There exists a coloring of `{1,…,N}` with `k` colours that is rainbow on 4-APs.
-/
def AdmitsRainbow4AP (N k : ℕ) : Prop :=
  ∃ f : ℕ → Fin k, RainbowOn4AP N k f

/--
Erdős Problem #160 [Er89]:

Let h(N) be the smallest k such that {1,…,N} can be coloured with k colours
so that every four-term arithmetic progression must contain at least three
distinct colours. Estimate h(N).

In particular, h(N) → ∞: for every k there exists N₀ such that for all N ≥ N₀,
no k-colouring of {1,…,N} is rainbow on 4-APs.

Known bounds (not formalised here):
  - Upper: h(N) ≪ N^{log3/log22 + o(1)} (Hunter)
  - Lower: h(N) ≫ exp(c(log N)^{1/9}) (via Bloom–Sisask / Kelley–Meka)
-/
theorem erdos_problem_160 :
    ∀ k : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ¬ AdmitsRainbow4AP N k := sorry
