import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Erdős Problem #938

Let A = {n₁ < n₂ < ⋯} be the sequence of powerful numbers (if p ∣ n then
p² ∣ n). Are there only finitely many three-term arithmetic progressions
among consecutive terms, i.e., indices k such that n_{k+2} - n_{k+1} =
n_{k+1} - n_k?

Erdős [Er76d] also conjectured (see [364]) that there are no triples of
powerful numbers of the shape n, n+1, n+2.
-/

/-- A positive natural number N is *powerful* if for every prime p dividing N,
    p² also divides N. -/
def IsPowerful (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → p ^ 2 ∣ N

/-- The set of powerful numbers (including 1). -/
def powerfulNumbers : Set ℕ := { n | 1 ≤ n ∧ IsPowerful n }

/--
Erdős Problem #938 [Er76d]:

Let {n_k} be the sequence of powerful numbers in increasing order. Then
there are only finitely many k such that n_k, n_{k+1}, n_{k+2} form an
arithmetic progression (i.e., n_{k+2} - n_{k+1} = n_{k+1} - n_k).
-/
theorem erdos938 (enum : ℕ → ℕ)
    (h_powerful : ∀ k, enum k ∈ powerfulNumbers)
    (h_strict_mono : StrictMono enum)
    (h_surj : ∀ n ∈ powerfulNumbers, ∃ k, enum k = n) :
    Set.Finite { k : ℕ | enum (k + 2) - enum (k + 1) = enum (k + 1) - enum k } :=
  sorry
