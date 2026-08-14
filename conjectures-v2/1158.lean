import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #1158

Let K_t(r) be the complete t-partite t-uniform hypergraph with r vertices
in each class.

Is it true that ex_t(n, K_t(r)) ≥ n^{t - r^{1-t} - o(1)} for all t, r?

Status: OPEN (erdosproblems.com/1158; page last edited 23 January 2026,
accessed 2026-02-23; cross-checked against the teorth/erdosproblems metadata
mirror: state "open", last update 2026-01-23). Tags: hypergraphs, turan number.
Related OEIS sequences: listed as "possible" on the page (none specified).

Erdős [Er64f] proved that
n^{t - O(r^{1-t})} ≤ ex_t(n, K_t(r)) ≪ n^{t - r^{1-t}}.
The conjectured lower bound n^{t - r^{1-t} - o(1)} (equivalently, the tight
exponent t - r^{1-t}) is only known when t = 2 and 2 ≤ r ≤ 3. The case t = 2
is problem #714 (which asks for the sharper bound ≫ n^{2 - 1/r}, without the
o(1) loss).

On the quantification "for all t, r": the statements below take t, r ≥ 2.
This is forced, not cosmetic — for r = 1 the literal claim is false, since
every edge of a t-uniform hypergraph is itself a copy of K_t(1) (partition it
into singletons), so ex_t(n, K_t(1)) = 0 < n^{t - 1 - ε}; and for t = 1 the
claim is trivially true (ex_1(n, K_1(r)) = r - 1 ≥ 1 ≥ n^{-ε}). The
nondegenerate content of "for all t, r" is exactly t, r ≥ 2.

References:

[Er64f] Erdős, P., "On extremal problems of graphs and generalized graphs".
Israel J. Math. 2 (1964), 183-190. (Journal/pages per the pipeline's
/latex/1158 fetch preserved in the session logs; the volume number is carried
from the upstream formal-conjectures file capture in the same logs.)

[Va99] Various, "Some of Paul's favorite problems". Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
§3.65. (Identification recovered from the upstream formal-conjectures logs:
the site's /latex/1158 source cites only [Er64f], and the [Va99] key is the
site's tag for this booklet, as for the sibling problems 1157 = §3.64 etc.)

Tags: hypergraphs, turan number
-/

/-- A t-uniform hypergraph on Fin n: every edge has exactly t vertices. -/
def IsUniformHypergraph1158 (t : ℕ) {n : ℕ} (E : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ E, e.card = t

/-- A t-uniform hypergraph E on Fin n contains a copy of the complete t-partite
    t-uniform hypergraph K_t(r) if there exist t pairwise disjoint vertex classes,
    each of size r, such that every transversal forms an edge of E.

    Since the classes are pairwise disjoint, any transversal f is injective, so
    its image has exactly t vertices, as an edge of a t-uniform E must.

    Degenerate parameters (excluded by the t, r ≥ 2 hypotheses of every theorem
    below): for r = 0 this holds for any E via the empty classes (the transversal
    condition is vacuous); for t = 0 it holds iff ∅ ∈ E. -/
def HasKtrCopy1158 (t r : ℕ) {n : ℕ} (E : Finset (Finset (Fin n))) : Prop :=
  ∃ classes : Fin t → Finset (Fin n),
    (∀ i, (classes i).card = r) ∧
    (∀ i j, i ≠ j → Disjoint (classes i) (classes j)) ∧
    (∀ f : Fin t → Fin n, (∀ i, f i ∈ classes i) →
      Finset.image f Finset.univ ∈ E)

/--
**Erdős Problem #1158** [Va99, 3.65]:

Let K_t(r) be the complete t-partite t-uniform hypergraph with r vertices in
each class. Is it true that ex_t(n, K_t(r)) ≥ n^{t - r^{1-t} - o(1)} for all t, r?

Formally: for all t ≥ 2, r ≥ 2, and ε > 0, for sufficiently large n, there exists
a t-uniform hypergraph on n vertices with no K_t(r) copy and at least
n^{t - r^{1-t} - ε} edges.

The problem is OPEN; this theorem asserts the asked ("yes") direction, per this
corpus's convention for open yes/no questions.
-/
theorem erdos_problem_1158 :
    ∀ (t r : ℕ), 2 ≤ t → 2 ≤ r →
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ E : Finset (Finset (Fin n)),
        IsUniformHypergraph1158 t E ∧
        ¬HasKtrCopy1158 t r E ∧
        (E.card : ℝ) ≥ (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ)) - ε) := by
  sorry

/--
Erdős's upper bound [Er64f], recorded on the source page:
ex_t(n, K_t(r)) ≪ n^{t - r^{1-t}}, i.e. there is a constant C = C(t, r) > 0
such that every K_t(r)-free t-uniform hypergraph on n vertices has at most
C · n^{t - r^{1-t}} edges.

(The bound is stated for all n: the finitely many small n below any threshold
are absorbed into C, since for each n there are only finitely many hypergraphs
on Fin n.)

Added by the fable-review pass from page-confirmed content; not
compile-verified.
-/
theorem erdos_problem_1158.variants.erdos_upper_bound :
    ∀ (t r : ℕ), 2 ≤ t → 2 ≤ r →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ E : Finset (Finset (Fin n)),
      IsUniformHypergraph1158 t E →
      ¬HasKtrCopy1158 t r E →
      (E.card : ℝ) ≤ C * (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ))) := by
  sorry

/--
Erdős's lower bound [Er64f], recorded on the source page:
n^{t - O(r^{1-t})} ≤ ex_t(n, K_t(r)), i.e. for each t there is a constant
C = C(t) > 0 such that for every r ≥ 2 and all sufficiently large n there is a
K_t(r)-free t-uniform hypergraph on n vertices with at least
n^{t - C · r^{1-t}} edges.

Interpretation of the O: the implied constant is taken uniform in r (that
uniformity is the content of the bound — it matches the upper bound's
exponent deficit r^{1-t} up to a constant factor) but may depend on t; the
standard random-deletion construction gives exponent deficit
t(r-1)/(r^t - 1) ≈ t · r^{1-t}, so C ≈ t suffices.

Added by the fable-review pass from page-confirmed content; not
compile-verified.
-/
theorem erdos_problem_1158.variants.erdos_lower_bound :
    ∀ t : ℕ, 2 ≤ t →
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ E : Finset (Finset (Fin n)),
        IsUniformHypergraph1158 t E ∧
        ¬HasKtrCopy1158 t r E ∧
        (E.card : ℝ) ≥ (n : ℝ) ^ ((t : ℝ) - C * (r : ℝ) ^ (1 - (t : ℝ))) := by
  sorry

end
