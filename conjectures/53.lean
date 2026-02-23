import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

/-!
# Erdős Problem #53

Let $A$ be a finite set of integers. Is it true that, for every $k$, if $|A|$
is sufficiently large depending on $k$, then there are at least $|A|^k$ many
integers which are either the sum or product of distinct elements of $A$?

Asked by Erdős and Szemerédi [ErSz83]. Solved in this form by Chang [Ch03].

Tags: number theory, additive combinatorics
-/

/--
The set of all subset sums of a finite set of integers:
$\{ \sum_{i \in S} i \mid S \subseteq A \}$.
-/
def subsetSums (A : Finset ℤ) : Finset ℤ :=
  A.powerset.image (fun S => ∑ i ∈ S, i)

/--
The set of all subset products of a finite set of integers:
$\{ \prod_{i \in S} i \mid S \subseteq A \}$.
-/
def subsetProducts (A : Finset ℤ) : Finset ℤ :=
  A.powerset.image (fun S => ∏ i ∈ S, i)

/--
**Erdős Problem #53**:

For every $k$, there exists $N$ such that for any finite set $A$ of integers
with $|A| \geq N$, the number of integers that are either a sum or product of
distinct elements of $A$ is at least $|A|^k$.
-/
theorem erdos_53 :
    ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℤ,
    A.card ≥ N →
    (subsetSums A ∪ subsetProducts A).card ≥ A.card ^ k :=
  sorry
