import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Nat BigOperators

noncomputable section

/--
Erdős Problem #15 [Er97, p.158; Er97e, p.535; Er98]:

> Is it true that
> $\sum_{n=1}^\infty(-1)^n\frac{n}{p_n}$
> converges, where $p_n$ is the sequence of primes?

**Status: OPEN** ("This is open, and cannot be resolved with a finite
computation." — erdosproblems.com/15, accessed 2026-02-24; status
re-confirmed open against the teorth/erdosproblems metadata mirror,
`data/problems.yaml` entry 15, last update 2025-08-31). This is a yes/no
question; following this corpus's convention for open yes/no questions
(direct assertion of the believed/conjectured direction), the theorem
asserts convergence — the direction Erdős implicitly conjectured and the
direction Tao [Ta23] has proved conditionally.

Remarks from the problem page:

- Erdős suggested that a computer could be used to explore this, and did
  not see any other method to attack this.
- Tao [Ta23] has proved that this series does converge assuming a strong
  form of the Hardy-Littlewood prime tuples conjecture.
- In [Er98] Erdős further conjectures that
  $\sum_{n=1}^\infty (-1)^n \frac{1}{n(p_{n+1}-p_n)}$ converges and
  $\sum_{n=1}^\infty (-1)^n \frac{1}{p_{n+1}-p_n}$ diverges. Weisenberg
  notes that the existence of infinitely many bounded gaps between primes
  (as proved by Zhang [Zh14]) implies the latter series does not converge.
  Weisenberg also has an argument which shows that, assuming the
  Hardy-Littlewood prime $k$-tuples conjecture, the series is unbounded in
  at least one direction (positive or negative).
- Erdős further conjectured that
  $\sum_{n=1}^\infty (-1)^n \frac{1}{n(p_{n+1}-p_n)(\log\log n)^c}$
  converges for every $c>0$, and reports that he and Nathanson can prove
  that this series converges absolutely for $c>2$ (and can show,
  conditional on 'hopeless' conjectures about the primes, that this sum
  does not converge absolutely for $c=2$). Sawhney has provided a proof
  (via the Selberg sieve) that this series converges absolutely for $c>2$.

See `erdos_problem_15.variants.*` below for the three [Er98] companion
series and the Erdős–Nathanson/Sawhney partial result.

Tags: number theory, primes. Additional thanks (page): Mehtaab Sawhney and
Desmond Weisenberg. The page (as of access) listed no upstream
formalization; the metadata mirror now records one
(google-deepmind/formal-conjectures `ErdosProblems/15.lean`, since
2026-04-17) — note that the upstream statement encodes convergence via
`Summable` over ℚ, which is provably false for this series (unconditional
summability entails absolute convergence, and
$\sum n/p_n \asymp \sum 1/\log n$ diverges); the partial-sums encoding used
here is the faithful one.

References (assembled from the recovered `erdosproblems.com/latex/15`
extraction and sibling files in this corpus; honest stubs where noted, with
missing journal/volume data omitted rather than guessed):

- [Er97] Erdős, P. (1997). Cited by the page as a problem source, p.158.
  (Stub: the corpus-unanimous title for this key, "Some of my new and
  almost new problems and results in combinatorial number theory",
  coincides with the corpus title of [Er98] — a possible corpus-level
  conflation, unresolved offline.)
- [Er97e] Erdős, P. (1997). Cited by the page as a problem source, p.535.
  (Stub: sibling files disagree on this key's title.)
- [Er98] Erdős, P., Some of my new and almost new problems and results in
  combinatorial number theory. Number theory (Eger, 1996), (1998), 169-180.
  (From the recovered `/latex/15` extraction.)
- [Ta23] Tao, T., The convergence of an alternating series of Erdős,
  assuming the Hardy-Littlewood prime tuples conjecture. arXiv:2308.07205
  (2023). (From the recovered `/latex/15` extraction.)
- [Zh14] Zhang, Y., Bounded gaps between primes. Ann. of Math. (2) 179
  (2014), 1121-1174. (Journal/year/pages from the recovered `/latex/15`
  extraction; volume 179 per sibling corpus files.)

We state the conjecture as: the sequence of partial sums
  S_N = ∑_{n=1}^N (-1)^n · n/pₙ
converges to a real limit L.

Using 0-indexed `Nat.nth Nat.Prime` (so `Nat.nth Nat.Prime 0 = 2 = p_1`),
the n-th term (n : ℕ, 0-indexed) is
  (-1)^(n+1) · (n+1) / (Nat.nth Nat.Prime n : ℝ),
which corresponds to the 1-indexed term (-1)^(n+1) · (n+1)/p_{n+1}.
-/
theorem erdos_problem_15 :
    ∃ L : ℝ,
      Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N,
          (-1 : ℝ) ^ (n + 1) * ((n + 1 : ℝ) / (Nat.nth Nat.Prime n : ℝ)))
        atTop (nhds L) :=
  sorry

/--
Erdős Problem #15, first companion conjecture [Er98] — **OPEN**:

> $\sum_{n=1}^\infty (-1)^n \frac{1}{n(p_{n+1}-p_n)}$ converges.

Direct assertion of the conjectured direction (convergence), per the corpus
convention for open questions.

Encoding notes: the Lean summand at 0-indexed `n` is the 1-indexed source
term at index `n + 1`, so the sign is `(-1)^(n+1)`, the weight is
`n + 1`, and the gap $p_{(n+1)+1} - p_{n+1}$ is
`Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n` (each factor cast to ℝ
*before* subtracting, so no ℕ-truncation can occur; the difference is
≥ 1 > 0 since `Nat.nth Nat.Prime` is strictly monotone, and the weight is
≥ 1, so no division by zero occurs at any index, including `n = 0`).
-/
theorem erdos_problem_15.variants.weighted_gap_converges :
    ∃ L : ℝ,
      Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N,
          (-1 : ℝ) ^ (n + 1) *
            (1 / ((n + 1 : ℝ) *
              ((Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime n : ℝ)))))
        atTop (nhds L) :=
  sorry

/--
Erdős Problem #15, second companion conjecture [Er98] — **effectively
SOLVED** (in the direction Erdős conjectured):

> $\sum_{n=1}^\infty (-1)^n \frac{1}{p_{n+1}-p_n}$ diverges.

Weisenberg (page remark) notes that the existence of infinitely many
bounded gaps between primes, proved unconditionally by Zhang [Zh14],
implies this series does not converge: infinitely many terms have absolute
value bounded below by a positive constant, so the terms do not tend to 0
and the partial sums are not Cauchy. Weisenberg also has an argument that,
under the Hardy-Littlewood prime $k$-tuples conjecture, the partial sums
are unbounded in at least one direction (that conditional refinement is not
formalized here).

Stated as the negation of convergence of the partial sums — the true (and
conjectured) direction. Indexing as in
`erdos_problem_15.variants.weighted_gap_converges`.
-/
theorem erdos_problem_15.variants.gap_diverges :
    ¬ ∃ L : ℝ,
      Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.range N,
          (-1 : ℝ) ^ (n + 1) *
            (1 / ((Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime n : ℝ))))
        atTop (nhds L) :=
  sorry

/--
Erdős Problem #15, third companion conjecture [Er98] — **OPEN**:

> $\sum_{n=1}^\infty (-1)^n \frac{1}{n(p_{n+1}-p_n)(\log\log n)^c}$
> converges for every $c > 0$.

Direct assertion of the conjectured direction (convergence for every
$c > 0$), per the corpus convention.

Encoding notes: the summation is re-indexed to start at the 1-indexed
source term $n = 3$ (Lean summand `n` ↦ source index `n + 3`): the source
series' first two terms are degenerate ($\log\log 1$ is undefined and
$\log\log 2 < 0$, making a real power ill-behaved), and dropping finitely
many terms does not affect convergence. For source index `n + 3` the sign
is `(-1)^(n+3)`, the weight is `n + 3`, the gap $p_{(n+3)+1} - p_{n+3}$ is
`Nat.nth Nat.Prime (n + 3) - Nat.nth Nat.Prime (n + 2)` (real subtraction
of casts, ≥ 1), and `Real.log (Real.log (n + 3 : ℝ)) ^ c` is a real
(rpow) power with strictly positive base (`log (log 3) > 0` since
`log 3 > 1`), so every factor of the denominator is positive.
-/
theorem erdos_problem_15.variants.weighted_gap_loglog_converges :
    ∀ c : ℝ, 0 < c →
      ∃ L : ℝ,
        Tendsto
          (fun N : ℕ => ∑ n ∈ Finset.range N,
            (-1 : ℝ) ^ (n + 3) *
              (1 / ((n + 3 : ℝ) *
                ((Nat.nth Nat.Prime (n + 3) : ℝ) - (Nat.nth Nat.Prime (n + 2) : ℝ)) *
                Real.log (Real.log (n + 3 : ℝ)) ^ c)))
          atTop (nhds L) :=
  sorry

/--
Erdős Problem #15, partial result for the third companion series —
**SOLVED** (Erdős–Nathanson, reported in [Er98]; independent proof by
Sawhney via the Selberg sieve, page remark):

> $\sum_{n=1}^\infty (-1)^n \frac{1}{n(p_{n+1}-p_n)(\log\log n)^c}$
> converges *absolutely* for every $c > 2$.

(Erdős reports that, conditional on 'hopeless' conjectures about the
primes, absolute convergence fails at $c = 2$; that conditional statement
is not formalized here.)

Stated as convergence of the partial sums of the absolute values of the
same terms as `erdos_problem_15.variants.weighted_gap_loglog_converges`
(same re-indexing from source index 3; dropping finitely many terms does
not affect absolute convergence).
-/
theorem erdos_problem_15.variants.weighted_gap_loglog_abs_converges :
    ∀ c : ℝ, 2 < c →
      ∃ L : ℝ,
        Tendsto
          (fun N : ℕ => ∑ n ∈ Finset.range N,
            |(-1 : ℝ) ^ (n + 3) *
              (1 / ((n + 3 : ℝ) *
                ((Nat.nth Nat.Prime (n + 3) : ℝ) - (Nat.nth Nat.Prime (n + 2) : ℝ)) *
                Real.log (Real.log (n + 3 : ℝ)) ^ c))|)
          atTop (nhds L) :=
  sorry

end
