import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Filter

namespace Erdos1102

/-!
# Erdős Problem #1102

Verbatim statement (erdosproblems.com/1102):

We say that $A \subseteq \mathbb{N}$ has property $P$ if, for all $n \geq 1$,
there are only finitely many $a \in A$ such that $n + a$ is squarefree.

We say that $A$ has property $Q$ if there are infinitely many $n$ such that
$n + a$ is squarefree for all $a < n$.

How fast must sequences $A = \{a_1 < a_2 < \cdots\}$ with properties $P$ or $Q$
increase?

(In the property-$Q$ sentence the variable $a$ implicitly ranges over $A$: the
literal reading "all naturals $a < n$" would demand every integer in $[n, 2n)$
be squarefree, impossible for $n \geq 4$, making $Q$ unsatisfiable; and the
page's distinct property $P'$ — "for all $a \in A$", no restriction $a < n$ —
only makes sense in contrast to $Q$ under the $a \in A$, $a < n$ reading. The
upstream formalization reads it the same way.)

Status on erdosproblems.com/1102: SOLVED (LEAN) — "This has been resolved in
some other way than a proof or disproof, and that resolution verified in
Lean." (Page edition 02 December 2025, accessed 2026-03-09.) Source citation
on the page: [Er81h, p.179]. Tags: number theory.

Remarks from the page: Erdős [Er81h] notes it is easy to see that there exist
$A$ with property $P$, and that any set which increases sufficiently quickly
has property $Q$. He also asks about property $P'$ — there are infinitely many
$n$ such that $n + a$ is squarefree for all $a \in A$ — and property
$P'_\infty$ — there are infinitely many $n$ such that $n + a$ is squarefree
for all but finitely many $a \in A$. Erdős also asks whether certain special
sequences, such as $2^n \pm 1$ or $n! \pm 1$, have properties $P$ or $Q$.

Most of these questions have been resolved by van Doorn and Tao [vDTa25]. In
particular they show that any sequence with property $P$ has density $0$, but
can have density going to $0$ arbitrarily slowly. They also show that any
sequence with property $Q$ has upper density at most $6/\pi^2$, and sequences
with property $Q$ exist with density equal to $6/\pi^2$. They further show
that any sequence with properties either $P'$ or $P'_\infty$ has upper density
$< 6/\pi^2$, and this is best possible in that for any $\epsilon > 0$ there
exist such sequences with lower density $> 6/\pi^2 - \epsilon$. Finally, they
also show that $2^n \pm 1$ and $n! \pm 1$ have property $Q$. It remains OPEN
whether these sequences have property $P$ (not formalized here: no believed
direction is stated on the page, so a direct assertion would over-claim).

Also not formalized (noted only): Erdős's unquantified remark that "any set
which increases sufficiently quickly has property $Q$" (no precise threshold
is given), and the $n! \pm 1$ property-$Q$ results (`Nat.factorial` is not
among the constructs already present in this file; per the pipeline's
constructs-already-present rule the $2^n \pm 1$ cases are formalized and the
factorial cases recorded here in prose).

References (honest stubs; the site loads full bibliographic data via separate
`/bibs/` requests that were not captured in the session logs):
- [Er81h] Erdős, P., _Some problems and results on additive and multiplicative
  number theory_. Analytic number theory (Philadelphia, Pa., 1980) (1981),
  171–182. This problem: p. 179. (Journal data carried from sibling files
  `deepmind/deepmind/18.lean`, `deepmind/deepmind/840.lean`, and the
  `/latex/1100` extraction recovered for fable-review/1100, which cite the
  same key; volume number unknown.)
- [vDTa25] van Doorn and Tao (2025). Authors and year are backed by the
  recovered page; full bibliographic details were not recoverable (no
  `/latex/1102` or `/bibs/` capture). A sibling file
  (`deepmind/deepmind/1103.lean`) records the title _Sumsets of squarefree
  numbers_ for this key, but that entry is model-written and unverified —
  DEFERRED, not asserted here.

Note: the problem page links "Formalised statement? Yes" to the authoritative
upstream formalization in google-deepmind/formal-conjectures
(`FormalConjectures/ErdosProblems/1102.lean`); only a prose summary of that
file was recoverable from the session logs. Its four theorems match the four
below (its Part 4 witness is additionally a set of squarefree numbers, a
strengthening this file does not assert).

NOTE: the Part 2 quantifier fix, the docstring enrichments, and the added
definitions/variants below are from the fable review of 2026-08-13 and are
not compile-verified (the review container cannot run `lake build`).

Tags: number theory
-/

/-- Property P: for all n ≥ 1, only finitely many a ∈ A satisfy "n + a is squarefree".

(Source-faithful: the source restricts to n ≥ 1, and with n ≥ 1 we have
n + a ≥ 1, so no `Squarefree 0` degeneracy arises.) -/
def HasPropertyP (A : Set ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → Set.Finite {a ∈ A | Squarefree (n + a)}

/-- Property Q: infinitely many n such that n + a is squarefree for all a ∈ A with a < n.

(The source writes "for all a < n" with a implicitly ranging over A — see the
module docstring. Degenerate note: n = 0 satisfies the inner condition
vacuously (no a < 0), and n = 1 requires at most `Squarefree 1 = True` (when
0 ∈ A), so small n are always members of the set; finitely many junk members
cannot affect `Set.Infinite`.) -/
def HasPropertyQ (A : Set ℕ) : Prop :=
  Set.Infinite {n : ℕ | ∀ a ∈ A, a < n → Squarefree (n + a)}

/-- Property P′ (from the page's remarks): infinitely many n such that n + a is
squarefree for all a ∈ A (no restriction a < n; contrast `HasPropertyQ`).

NOTE: added from the recovered source page; not compile-verified. -/
def HasPropertyP' (A : Set ℕ) : Prop :=
  Set.Infinite {n : ℕ | ∀ a ∈ A, Squarefree (n + a)}

/-- Property P′_∞ (from the page's remarks): infinitely many n such that n + a
is squarefree for all but finitely many a ∈ A. Implied by P′ (the exceptional
set is then empty). Degenerate note: every finite A satisfies this trivially
(the exceptional set is a subset of A, hence finite, for every n).

NOTE: added from the recovered source page; not compile-verified. -/
def HasPropertyP'inf (A : Set ℕ) : Prop :=
  Set.Infinite {n : ℕ | Set.Finite {a ∈ A | ¬ Squarefree (n + a)}}

/-- The counting function for a set S ⊆ ℕ: the number of elements ≤ N
(`Set.Iic N = {0, …, N}`, so the count is over N + 1 candidates — hence the
N + 1 normalization in the density definitions below, which does not change
any of the asymptotic notions). -/
noncomputable def countingFn (S : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (S ∩ Set.Iic N)

/-- The upper density of a set S ⊆ ℕ: limsup of the counting ratio. (The ratio
sequence lies in [0, 1], so the real `limsup` is well-behaved — no junk-value
regime.) -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  limsup (fun N : ℕ => (countingFn S N : ℝ) / (N + 1 : ℝ)) atTop

/-- The lower density of a set S ⊆ ℕ: liminf of the counting ratio (dual of
`upperDensity`; same boundedness remark).

NOTE: added from the recovered source page (needed for the best-possible
variant); not compile-verified. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  liminf (fun N : ℕ => (countingFn S N : ℝ) / (N + 1 : ℝ)) atTop

/-- The natural density of a set S ⊆ ℕ equals d if the ratio converges to d. -/
def hasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (countingFn S N : ℝ) / (N + 1 : ℝ)) atTop (nhds d)

/-- Erdős Problem #1102, Part 1 (SOLVED) [Er81h, p.179; vDTa25]:

Any strictly increasing sequence with property P has density 0.
Equivalently, a(j)/j → ∞: for a strictly increasing enumeration, the counting
function satisfies A(a_j) = j + 1, so A(x)/x → 0 ⟺ (j+1)/a_j → 0 ⟺
a_j/j → ∞ — the two formulations are interchangeable, and this file states the
quotient form. (The j = 0 term divides by zero and is 0 by Lean's field
convention; harmless under `atTop`.) -/
theorem density_zero_of_P (a : ℕ → ℕ) (ha : StrictMono a)
    (hP : HasPropertyP (Set.range a)) :
    Tendsto (fun j : ℕ => (a j : ℝ) / (j : ℝ)) atTop atTop :=
  sorry

/-- Erdős Problem #1102, Part 2 (SOLVED) [Er81h, p.179; vDTa25]:

For any function going to infinity, there exists a strictly increasing
sequence with property P satisfying a(j) ≤ f(j)·j for all sufficiently
large j. That is, density can go to 0 arbitrarily slowly.

The growth bound is (and must be) eventual: `Tendsto f atTop atTop` allows f
to be negative or tiny initially (e.g. f(j) = j − 10⁶), in which case a
universal bound `∀ j, (a j : ℝ) ≤ f j * j` is unsatisfiable over ℕ — and at
j = 0 it would force a 0 = 0 regardless of f. [Fixed in the fable review of
2026-08-13: the first-pass statement quantified the bound over all j and was
therefore false. Not compile-verified.] -/
theorem exists_sequence_with_P (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ HasPropertyP (Set.range a) ∧
      ∀ᶠ j : ℕ in atTop, (a j : ℝ) ≤ f j * (j : ℝ) :=
  sorry

/-- Erdős Problem #1102, Part 3 (SOLVED) [Er81h, p.179; vDTa25]:

Any set with property Q has upper density at most 6/π². (The page says
"sequence"; stating it for an arbitrary `Set ℕ` is a harmless generalization —
finite sets have upper density 0.) -/
theorem upper_density_Q (A : Set ℕ) (hQ : HasPropertyQ A) :
    upperDensity A ≤ 6 / Real.pi ^ 2 :=
  sorry

/-- Erdős Problem #1102, Part 4 (SOLVED) [Er81h, p.179; vDTa25]:

There exists an infinite set with property Q and natural density equal to
6/π². (Per the recovered summary of the upstream formalization, the witness
can moreover be taken inside the squarefree numbers; that strengthening is
not asserted here.) -/
theorem exists_Q_with_max_density :
    ∃ A : Set ℕ, Set.Infinite A ∧ HasPropertyQ A ∧
      hasNaturalDensity A (6 / Real.pi ^ 2) :=
  sorry

/-- Erdős's easy remark on the page (SOLVED) [Er81h, p.179]:

There exist (infinite) sets with property P. This also shows Part 1 is not
vacuously quantified.

NOTE: added from the recovered source page; not compile-verified. -/
theorem erdos_1102.variants.exists_P :
    ∃ A : Set ℕ, Set.Infinite A ∧ HasPropertyP A :=
  sorry

/-- van Doorn–Tao, remark on the page (SOLVED) [vDTa25]:

Any sequence with property P′ has upper density strictly less than 6/π².
(For an arbitrary set the statement remains true: finite sets have upper
density 0 < 6/π².)

NOTE: added from the recovered source page; not compile-verified. -/
theorem erdos_1102.variants.upper_density_P' (A : Set ℕ)
    (h : HasPropertyP' A) :
    upperDensity A < 6 / Real.pi ^ 2 :=
  sorry

/-- van Doorn–Tao, remark on the page (SOLVED) [vDTa25]:

Any sequence with property P′_∞ has upper density strictly less than 6/π².
(Implies the P′ case, since P′ ⇒ P′_∞.)

NOTE: added from the recovered source page; not compile-verified. -/
theorem erdos_1102.variants.upper_density_P'inf (A : Set ℕ)
    (h : HasPropertyP'inf A) :
    upperDensity A < 6 / Real.pi ^ 2 :=
  sorry

/-- van Doorn–Tao, remark on the page (SOLVED) [vDTa25]:

The bound 6/π² for P′/P′_∞ is best possible: for any ε > 0 there exist such
sequences with lower density > 6/π² − ε. (The page's "such sequences" is
ambiguous between P′ and P′_∞; this states the weaker, safe reading P′_∞ —
which either reading implies, since P′ ⇒ P′_∞.)

NOTE: added from the recovered source page; not compile-verified. -/
theorem erdos_1102.variants.best_possible_P'inf (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Set ℕ, Set.Infinite A ∧ HasPropertyP'inf A ∧
      6 / Real.pi ^ 2 - ε < lowerDensity A :=
  sorry

/-- van Doorn–Tao, remark on the page (SOLVED) [vDTa25]:

The sequence 2^k − 1 (k ≥ 1) has property Q. (Encoded subtraction-free as
{m | m + 1 = 2^k, k ≥ 1} = {1, 3, 7, 15, …}; the page writes 2^n ± 1 with the
usual n ≥ 1 convention. Whether this sequence has property P remains OPEN and
is not asserted.)

NOTE: added from the recovered source page; not compile-verified. -/
theorem erdos_1102.variants.pow_two_sub_one_Q :
    HasPropertyQ {m : ℕ | ∃ k : ℕ, 1 ≤ k ∧ m + 1 = 2 ^ k} :=
  sorry

/-- van Doorn–Tao, remark on the page (SOLVED) [vDTa25]:

The sequence 2^k + 1 (k ≥ 1) has property Q ({3, 5, 9, 17, …}; same
conventions as `pow_two_sub_one_Q`). Whether this sequence has property P
remains OPEN and is not asserted. The analogous n! ± 1 results are recorded
in the module docstring only (factorial is not among this file's constructs).

NOTE: added from the recovered source page; not compile-verified. -/
theorem erdos_1102.variants.pow_two_add_one_Q :
    HasPropertyQ {m : ℕ | ∃ k : ℕ, 1 ≤ k ∧ m = 2 ^ k + 1} :=
  sorry

end Erdos1102

end
