import Mathlib.Combinatorics.Configuration

open Configuration Classical Finset

noncomputable section

/-!
# Erdős Problem #1159

Determine whether there exists a constant C > 1 such that the following holds:
Let P be a finite projective plane. Must there exist a set of points S such that
1 ≤ |S ∩ ℓ| ≤ C for all lines ℓ?

A set which meets all lines is called a blocking set. The conjecture asks whether
every finite projective plane has a blocking set where no line is hit more than
a bounded number of times.

Erdős, Silverman, and Stein [ESS83] proved this is true with |S ∩ ℓ| ≪ log n
for all lines ℓ (where n is the order of the projective plane).

Tags: combinatorics
-/

/--
Erdős Problem #1159 [Va99,4.70]:

Does there exist an absolute constant C > 1 such that every finite projective plane
has a set of points S meeting every line in at least 1 and at most C points?
-/
theorem erdos_problem_1159 :
    ∃ C : ℕ, 1 < C ∧
      ∀ (P L : Type) [Membership P L] [Fintype P] [Fintype L]
        [Configuration.ProjectivePlane P L],
        ∃ S : Finset P,
          ∀ l : L, 1 ≤ (S.filter (fun p => p ∈ l)).card ∧
                    (S.filter (fun p => p ∈ l)).card ≤ C :=
  sorry

end
