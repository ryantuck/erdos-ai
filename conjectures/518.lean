import Mathlib.Data.List.Chain
import Mathlib.Data.Nat.Sqrt

/-!
# Erdős Problem #518

Is it true that, in any two-colouring of the edges of $K_n$, there exist
$\sqrt{n}$ monochromatic paths, all of the same colour, which cover all
vertices?

A problem of Erdős and Gyárfás [ErGy95]. Gerencsér and Gyárfás [GeGy67]
proved that, if the paths do not need to be of the same colour, then two
paths suffice. Erdős and Gyárfás proved that $2\sqrt{n}$ paths suffice and
observed that $\sqrt{n}$ would be best possible.

Solved in the affirmative by Pokrovskiy, Versteegen, and Williams [PVW24].
-/

/-- A path is monochromatic of color `b` under edge coloring `c` if every
    consecutive pair of vertices in the path receives color `b`. A path
    of length ≤ 1 is trivially monochromatic. -/
def IsMonochromaticPath {α : Type*} (c : α → α → Bool) (b : Bool) (p : List α) : Prop :=
  p.IsChain (fun u v => c u v = b)

/--
Erdős Problem #518 [ErGy95]:

In any two-colouring of the edges of K_n, there exist at most ⌈√n⌉
monochromatic paths, all of the same colour, which together cover all
vertices.

The bound is formalized as `Nat.sqrt n + 1`, which satisfies
⌈√n⌉ ≤ Nat.sqrt n + 1 for all n.
-/
theorem erdos_problem_518 (n : ℕ)
    (c : Fin n → Fin n → Bool)
    (hc : ∀ i j : Fin n, c i j = c j i) :
    ∃ (b : Bool) (paths : List (List (Fin n))),
      paths.length ≤ Nat.sqrt n + 1 ∧
      (∀ p ∈ paths, p.Nodup ∧ IsMonochromaticPath c b p) ∧
      (∀ v : Fin n, ∃ p ∈ paths, v ∈ p) :=
  sorry
