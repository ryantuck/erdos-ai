import Mathlib.Algebra.Group.Even

/-!
# Erdős Problem #439

Is it true that, in any finite colouring of the integers, there must be two
integers x ≠ y of the same colour such that x + y is a square? What about
a k-th power?

A question of Roth, Erdős, Sárközy, and Sós. Erdős, Sárközy, and Sós proved
this for 2 or 3 colours.

Equivalently, the infinite graph on ℕ where m and n are connected iff m + n
is a perfect square has infinite chromatic number.

This was proved by Khalfalah and Szemerédi [KhSz06], who showed the general
result with x + y = z² replaced by x + y = f(z) for any non-constant
f(z) ∈ ℤ[z] such that 2 ∣ f(z) for some z ∈ ℤ. Since k-th powers include
even values (take z even), the k-th power case follows.
-/

/-- Erdős Problem #439, square case (PROVED):
In any finite colouring of the natural numbers, there exist distinct x and y
of the same colour such that x + y is a perfect square.

Proved by Khalfalah and Szemerédi [KhSz06]. -/
theorem erdos_problem_439_squares (c : ℕ) (f : ℕ → Fin c) :
    ∃ x y : ℕ, x ≠ y ∧ f x = f y ∧ IsSquare (x + y) :=
  sorry

/-- Erdős Problem #439, k-th power generalization (PROVED):
In any finite colouring of the natural numbers, there exist distinct x and y
of the same colour such that x + y is a perfect k-th power (i.e., z^k for
some z).

Also follows from the result of Khalfalah and Szemerédi [KhSz06]. -/
theorem erdos_problem_439_kth_powers (k : ℕ) (hk : 2 ≤ k)
    (c : ℕ) (f : ℕ → Fin c) :
    ∃ x y : ℕ, x ≠ y ∧ f x = f y ∧ ∃ z : ℕ, z ^ k = x + y :=
  sorry
