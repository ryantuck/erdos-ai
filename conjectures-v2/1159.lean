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

Status: OPEN (erdosproblems.com/1159; page last edited 23 January 2026, accessed
2026-02-23; cross-checked against the teorth/erdosproblems metadata mirror:
state "open", last update 2026-01-23). Tags: combinatorics. Related OEIS
sequences: none (listed "N/A" in the metadata mirror).

In [Er81] Erdős asks the stronger question of whether this is true for all
pairwise balanced block designs. See also problem #664 for a stronger question.

Erdős, Silverman, and Stein [ESS83] proved this is true with |S ∩ ℓ| ≪ log n
for all lines ℓ (where n is the order of the projective plane).

On the constant "C > 1": no C ≤ 1 can work in any projective plane, so the
strict inequality is forced, not cosmetic. Indeed, a set S meeting every line
in exactly one point cannot exist: any two distinct points of S lie on a common
line (which would then meet S twice), so |S| ≤ 1; a singleton {p} misses every
line not through p (such lines exist by nondegeneracy); and the empty set meets
no line. Hence C = 1 fails in every plane and the question starts at C = 2.

References:

[Er81] Erdős, P., "On the combinatorial problems which I would most like to see
solved". Combinatorica 1 (1981), 25-42. (Authors/title/journal/year/pages per
the pipeline's /latex/1159 fetch preserved in the session logs; the volume
number is carried from the upstream formal-conjectures fix-session capture in
the same logs.)

[ESS83] Erdős, P., Silverman, R., and Stein, A., "Intersection properties of
families containing sets of nearly the same size". Ars Combinatoria (1983),
247-259. (Per the pipeline's /latex/1159 fetch preserved in the session logs;
the volume number was not captured there and is left out rather than invented.)

[Va99] Various, "Some of Paul's favorite problems". Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999), §4.70.
(Identification recovered from the pipeline logs: the site's /latex/1159 source
cites only [Er81] and [ESS83] in its bibliography, and [Va99] is the site's tag
for this booklet, as for the sibling problems 1157 = §3.64, 1158 = §3.65, etc.
The section number 4.70 is from the recovered page's [Va99,4.70] citation link.)

Tags: combinatorics
-/

/--
Erdős Problem #1159 [Va99, 4.70]:

Does there exist an absolute constant C > 1 such that every finite projective plane
has a set of points S meeting every line in at least 1 and at most C points?

The problem is OPEN; this theorem asserts the asked ("yes") direction, per this
corpus's convention for open yes/no questions. Since |S ∩ ℓ| is a natural
number, a real constant C > 1 works iff a natural constant C ≥ 2 does, so
`C : ℕ` with `1 < C` is a faithful encoding of the source's "constant C > 1".
-/
theorem erdos_problem_1159 :
    ∃ C : ℕ, 1 < C ∧
      ∀ (P L : Type) [Membership P L] [Fintype P] [Fintype L]
        [ProjectivePlane P L],
        ∃ S : Finset P,
          ∀ l : L, 1 ≤ (S.filter (fun p => p ∈ l)).card ∧
                    (S.filter (fun p => p ∈ l)).card ≤ C :=
  sorry

/--
Erdős, Silverman, and Stein [ESS83] proved that every finite projective plane of
order n has a blocking set S with |S ∩ ℓ| ≪ log n for all lines ℓ (recorded in
the source page's remarks).

Encoding of the logarithmic bound without real logarithms: for a natural number
k, `2 ^ k ≤ (n + 2) ^ C` holds iff k ≤ C · log₂(n + 2), and since the order n
of a projective plane is at least 2 (so that log₂(n + 2) ≤ 2 · log₂ n), the
existence of an absolute C in this form is equivalent to the existence of an
absolute C with |S ∩ ℓ| ≤ C · log n, i.e. to |S ∩ ℓ| ≪ log n. The `+ 2` also
keeps the bound honest at the degenerate value order = 0 (log 0 junk).

Added by the fable-review pass from page-confirmed content; not
compile-verified.
-/
theorem erdos_problem_1159.variants.ess_log_bound :
    ∃ C : ℕ, 0 < C ∧
      ∀ (P L : Type) [Membership P L] [Fintype P] [Fintype L]
        (pp : ProjectivePlane P L),
        ∃ S : Finset P,
          ∀ l : L, 1 ≤ (S.filter (fun p => p ∈ l)).card ∧
            2 ^ (S.filter (fun p => p ∈ l)).card ≤ (pp.order + 2) ^ C :=
  sorry

end
