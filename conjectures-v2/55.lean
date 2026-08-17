import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Set.Basic

open Finset Real

attribute [local instance] Classical.propDecidable

/-!
# Erdős Problem #55

Verbatim from erdosproblems.com/55 (archived capture, accessed 2026-02-22):

"A set of integers $A$ is Ramsey $r$-complete if, whenever $A$ is
$r$-coloured, all sufficiently large integers can be written as a
monochromatic sum of elements of $A$. Prove any non-trivial bounds about the
growth rate of such an $A$ for $r>2$."

Source: [Er95]. Prize: $250. Tags: number theory | ramsey theory.

Status and provenance (Fable review):
- Page banner at capture: SOLVED, tooltip "This has been resolved in some
  other way than a proof or disproof." (The problem is an imperative "prove
  bounds" task, not a yes/no question, hence this tooltip.)
- The metadata mirror (github.com/teorth/erdosproblems, data/problems.yaml,
  commit a09c7a2, 2026-08-14) agrees: state "solved", last update
  2025-08-31; prize $250; tags number theory, ramsey theory; OEIS N/A;
  formal status "unformalized".
- The upstream formal-conjectures repository at HEAD dd1c2be (2026-08-16)
  has no `FormalConjectures/ErdosProblems/55.lean`, consistent with the
  mirror and the page's "Formalised statement? No" at capture.
- "See also [54] and [843]." Problem 54 is the $r = 2$ instance (its
  `IsRamsey2Complete` in `conjectures/54.lean` is definitionally
  `IsRamseyComplete A 2`). "Additional thanks to: Mehtaab Sawhney."

Page remarks:
- Burr and Erdős [BuEr85] proved both upper and lower bounds for $r = 2$:
  there exists some $c > 0$ such that it cannot be true that
  $\lvert A \cap \{1,\ldots,N\}\rvert \leq c (\log N)^2$ for all large $N$,
  and there is a Ramsey $2$-complete $A$ with
  $\lvert A \cap \{1,\ldots,N\}\rvert \ll (\log N)^3$ for all large $N$.
- Burr has shown that the sequence of $k$th powers is Ramsey $r$-complete
  for every $r, k \geq 1$.
- Solved by Conlon, Fox, and Pham [CFP21], who constructed for every
  $r \geq 2$ an $r$-Ramsey complete $A$ such that for all large $N$
  $\lvert A \cap \{1,\ldots,N\}\rvert \ll r (\log N)^2$, and showed that
  this is best possible: there exists some constant $c > 0$ such that if
  $A \subset \mathbb{N}$ satisfies
  $\lvert A \cap \{1,\ldots,N\}\rvert \leq c r (\log N)^2$ for all large
  $N$ then $A$ cannot be $r$-Ramsey complete. (The original ask was for
  $r > 2$; the resolution covers every $r \geq 2$, subsuming [BuEr85]'s
  $(\log N)^3$ upper bound for $r = 2$.)

References (assembled by the Fable review; the raw input cited
"Conlon, Fox, and Pham [2021]" with no bibliography):
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_ (1995). (Key from the page's problem line;
  expansion recovered from another problem page's bibliography in the
  session logs. Sibling corpus files expand [Er95] inconsistently, and no
  journal/volume/pages were recovered — DEFERRED.)
- [BuEr85] Burr, S. A. and Erdős, P., _A Ramsey-type property in additive
  number theory_. Glasgow Math. J. (1985), 5-10. (Title/journal/year/pages
  from the log-recovered `/latex/55` extraction; the volume number was not
  in the extraction — DEFERRED, not fabricated.)
- [CFP21] Conlon, D., Fox, J., and Pham, H. T., _Subset sums, completeness
  and colorings_. arXiv:2104.14766 (2021). (From the log-recovered
  `/latex/55` extraction, which notes it as a preprint with no
  journal/volume/pages. A prior AI review's guess of a J. Combin. Theory
  Ser. B publication is unverified and not adopted.)

Fable-review fix (not compile-verified): in the raw input both constants
were existentially quantified *inside* `∀ r`, so `C` and `c` could depend
on `r` — which makes the explicit `r` factor in `C * r * (log N)^2`
mathematically inert (absorbable into `C(r)`) and loses the uniform
$r$-dependence that is the content of [CFP21] and of the page's
"$\ll r(\log N)^2$ ... best possible" claims. Both theorems below hoist
the constant outside `∀ r`, matching the source. The archived styled
artifact (`deepmind/deepmind/55.lean`) had already applied the same fix.

Tags: number theory, ramsey theory
-/

/--
A set A of natural numbers is Ramsey r-complete if for every r-coloring of ℕ,
all sufficiently large natural numbers can be represented as a sum of distinct
elements of A that all receive the same color.

Note (Fable review): colouring all of ℕ rather than just A is equivalent to
the source's "whenever $A$ is $r$-coloured" (every colouring of A extends to
ℕ and conversely restricts to A; only the colours on S ⊆ A matter). `Finset`
membership enforces the distinctness of the summands, matching the
Burr–Erdős subset-sum definition. Degenerate inputs: for `r = 0` there is no
colouring `ℕ → Fin 0`, so every `A` is vacuously Ramsey 0-complete, and the
empty `S` (sum 0, monochromatic vacuously) only ever represents `n = 0` —
both invisible to the theorems below, which take `r ≥ 2` (or `r ≥ 1`) and
concern all sufficiently large `n`.
-/
def IsRamseyComplete (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ (χ : ℕ → Fin r),
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A ∧
        (∃ c : Fin r, ∀ x ∈ S, χ x = c) ∧
        S.sum id = n

/--
Erdős Problem #55 [Er95] — SOLVED (Conlon, Fox, and Pham [CFP21]):
There is a single constant C > 0 such that for every r ≥ 2 there exists an
r-Ramsey complete set A with |A ∩ {1,...,N}| ≤ C · r · (log N)² for all
sufficiently large N, and this is best possible (see
`erdos_problem_55_lower`).

Upper bound: the constant C is uniform in r (hoisted outside `∀ r` by the
Fable review — with C inside, the r factor in the bound is inert), matching
[CFP21]'s "$\ll r(\log N)^2$" with an absolute implied constant. The
threshold N₀ may depend on r and A, matching "for all large N". -/
theorem erdos_problem_55_upper :
    ∃ C : ℝ, C > 0 ∧
      ∀ r : ℕ, 2 ≤ r →
        ∃ (A : Set ℕ),
          IsRamseyComplete A r ∧
            ∃ N₀ : ℕ, ∀ N ≥ N₀,
              (((Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
                C * (r : ℝ) * (log (N : ℝ)) ^ 2 :=
  sorry

/-- Lower bound ([CFP21], "best possible"): there exists a single c > 0 such
    that for every r ≥ 2, any set A with |A ∩ {1,...,N}| ≤ c · r · (log N)²
    for all large N cannot be r-Ramsey complete. Together with
    `erdos_problem_55_upper` this pins the extremal growth rate at
    Θ(r (log N)²), uniformly in r (the constant c is hoisted outside `∀ r`
    by the Fable review, matching the page's "there exists some constant
    $c>0$" with r free). -/
theorem erdos_problem_55_lower :
    ∃ c : ℝ, c > 0 ∧
      ∀ r : ℕ, 2 ≤ r →
        ∀ (A : Set ℕ),
          (∃ N₀ : ℕ, ∀ N ≥ N₀,
            (((Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
              c * (r : ℝ) * (log (N : ℝ)) ^ 2) →
          ¬ IsRamseyComplete A r :=
  sorry

/-- Variant (page-confirmed, Burr): the sequence of kth powers
    {1^k, 2^k, 3^k, ...} is Ramsey r-complete for every r, k ≥ 1.
    (Added by the Fable review from the page remarks; not compile-verified.) -/
theorem erdos_problem_55_burr_kth_powers :
    ∀ r k : ℕ, 1 ≤ r → 1 ≤ k →
      IsRamseyComplete {m : ℕ | ∃ n : ℕ, 1 ≤ n ∧ m = n ^ k} r :=
  sorry

/-- Variant (page-confirmed, Burr–Erdős [BuEr85], upper bound for r = 2):
    there exists a Ramsey 2-complete set A with
    |A ∩ {1,...,N}| ≪ (log N)³ for all large N. This is the historical
    bound that [CFP21] improved to Θ((log N)²); it is the content of
    Problem 54, recorded here because the page for #55 states it.
    (Added by the Fable review; not compile-verified.) -/
theorem erdos_problem_55_burr_erdos_upper_two :
    ∃ (A : Set ℕ),
      IsRamseyComplete A 2 ∧
        ∃ C : ℝ, C > 0 ∧
          ∃ N₀ : ℕ, ∀ N ≥ N₀,
            (((Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
              C * (log (N : ℝ)) ^ 3 :=
  sorry

/-- Variant (page-confirmed, Burr–Erdős [BuEr85], lower bound for r = 2):
    there exists c > 0 such that no set satisfying
    |A ∩ {1,...,N}| ≤ c (log N)² for all large N is Ramsey 2-complete —
    the page's "it cannot be true that |A ∩ {1,...,N}| ≤ c(log N)² for all
    large N" for Ramsey 2-complete A, in contrapositive form.
    (Added by the Fable review; not compile-verified.) -/
theorem erdos_problem_55_burr_erdos_lower_two :
    ∃ c : ℝ, c > 0 ∧
      ∀ (A : Set ℕ),
        (∃ N₀ : ℕ, ∀ N ≥ N₀,
          (((Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
            c * (log (N : ℝ)) ^ 2) →
        ¬ IsRamseyComplete A 2 :=
  sorry
