-- [AI - Claude Sonnet 5.5]: Erdős Problem 125 — second-pass formalization
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Filter Set
open scoped Topology

/-!
# Erdős Problem #125: The Density of A + B for Base-3 and Base-4 Digit Sets

*Source:* [erdosproblems.com/125](https://www.erdosproblems.com/125) (status **OPEN** when
captured: "This is open, and cannot be resolved with a finite computation."; captured 2026-02-20
and 2026-03-05 as the tidied problem box; **disproved since**, see below). [BEGL96] [Er97]

Let $A = \{ \sum\epsilon_k3^k : \epsilon_k\in \{0,1\}\}$ be the set of integers which have only
the digits $0,1$ when written base $3$, and $B=\{ \sum\epsilon_k4^k : \epsilon_k\in \{0,1\}\}$ be
the set of integers which have only the digits $0,1$ when written base $4$.

Does $A+B$ have positive density?

Remarks recorded on the page:
* A problem of Burr, Erdős, Graham, and Li [BEGL96]. More generally, if $n_1<\cdots<n_k$ have
  $\sum_{i=1}^k\log_{n_k}(2)>1$ and $A_i$ is the set of integers with only the digits $0,1$ in
  base $n_i$ then does $A_1+\cdots+A_k$ have positive density? Melfi [Me01] noted this is false
  as written, with a counterexample given by $\{3,9,81\}$, but suggests it is true if the
  $n_k$ are further required to be pairwise coprime. (The page prints $\log_{n_k}$ inside a
  sum over $i$. The index must be $i$.)
* If $C=A+B$ then Melfi [Me01] showed $\lvert C\cap[1,x]\rvert \gg x^{0.965}$ and Hasler and
  Melfi [HaMe24] improved this to $\lvert C\cap [1,x]\rvert \gg x^{0.9777}$. Hasler and Melfi
  also show that the lower density of $C$ is at most $\frac{1015}{1458}\approx 0.69616$.
* See also Problem #124.

Tags: number theory, base representations. OEIS: A367090.

**Status after capture.** The site owner's mirror (`teorth/erdosproblems`) records this problem as
`disproved (Lean)`, with the status dated 2026-03-30 (present by commit `d46d4eb`, 2026-05-13).
Upstream `125.lean` splits "positive density" into readings:
* `erdos_125 : answer(False) ↔ (A + B).HasPosDensity`, the literal reading, "which was
  falsified", with a formal-proof link;
* `variants.positive_lower_density : answer(False) ↔ 0 < (A + B).lowerDensity`, "This has been
  falsified", with a formal-proof link;
* `variants.positive_upper_density`: **open**;
* `variants.positive_unequal_density : answer(False)`, a consequence of the above.

This second-pass review has not checked those proofs.

**What the first pass states.** `∃ δ > 0, ∀ᶠ N, δ ≤ #(C ∩ [0,N]) / (N+1)`. That is exactly
`0 < lowerDensity C`: a bounded sequence has positive liminf iff it is eventually bounded below
by a positive constant. Upstream's `lowerDensity` is the liminf of the partial densities
$\lvert S\cap[0,b)\rvert/b$, which is the same quantity at $b=N+1$. So the first pass asserts the
refuted direction. v2 negates the byte-identical proposition.

**Readings of "positive density".** Three readings are in play, and they are nested:
* (i) the density exists and is positive;
* (ii) the lower density is positive (the first pass's reading);
* (iii) the upper density is positive.

(i) implies (ii), and (ii) implies (iii). The refutation of (ii) refutes (i) as well, which is
`variants.no_positive_density`. Reading (iii) stays open, and is `variants.positive_upper_density`.

**Numerical check.** For $N\le4\cdot10^6$ the ratio $\lvert C\cap[0,N]\rvert/(N+1)$ stays between
$0.78$ and $0.93$, with its minimum $0.7785$ at $N=3^{10}-1$. That is consistent with
Hasler–Melfi's bound $\le0.696$ on the lower density, which it does not reach. It neither
supports nor contradicts a lower density of $0$: any such decay would have to occur at far larger
scales.

**Encoding.** `digitSet d` is the set of sums of distinct powers of $d$, which for $d\ge2$ is the
set of integers with base-$d$ digits in $\{0,1\}$. It contains $0$. The count
`Set.ncard (C ∩ Set.Iic N)` is genuine, since the set is finite.

## References

* [BEGL96] Burr, S. A., Erdős, P., Graham, R. L. and Li, W. W.-C., _Complete sequences of sets of
  integer powers_. Acta Arith. (1996), 133–138.
* [Er97] Erdős, P., _Problems in number theory_. New Zealand J. Math. (1997), 155–160.
* [Me01] Melfi (2001), in the page's remarks. **DEFERRED:** no bibliographic details were
  recovered.
* [HaMe24] Hasler and Melfi (2024), in the page's remarks. **DEFERRED:** no bibliographic details
  were recovered.

(Provenance: no `/latex/125` fetch exists in the session logs. [BEGL96] is from upstream
`124.lean`, and [Er97] from the bibliographies of upstream sibling files. No source for [Me01] or
[HaMe24] was found in the logs or upstream.)
-/

/-- The set of natural numbers expressible as a sum of distinct powers of d.
    These are the numbers whose base-d representation uses only digits 0 and 1. -/
def digitSet (d : ℕ) : Set ℕ :=
  {n : ℕ | ∃ S : Finset ℕ, n = ∑ i ∈ S, d ^ i}

/-- The sumset A + B of two sets of natural numbers. -/
def sumSet (A B : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/--
Erdős Problem #125 [BEGL96, Er97] — OPEN when captured; recorded as DISPROVED since (see the
module docstring).

Let A = {∑ εₖ 3ᵏ : εₖ ∈ {0,1}} be the set of integers which have only the
digits 0,1 when written in base 3, and B = {∑ εₖ 4ᵏ : εₖ ∈ {0,1}} be the set
of integers which have only the digits 0,1 when written in base 4.

Does A + B have positive density?

The first pass asserted that A + B has positive lower density (a positive δ below the proportion
of C ∩ [0, N] for all large N). That is the refuted reading, so v2 asserts its negation: the
lower density of A + B is 0.

A problem of Burr, Erdős, Graham, and Li. Melfi showed
|C ∩ [1,x]| ≫ x^{0.965} where C = A + B, and Hasler–Melfi improved this to
x^{0.9777}. Hasler–Melfi also show the lower density of C is at most
1015/1458 ≈ 0.69616.
-/
theorem erdos_problem_125 :
    ¬ (let A := digitSet 3
       let B := digitSet 4
       let C := sumSet A B
       ∃ δ : ℝ, 0 < δ ∧
         ∀ᶠ N in atTop, δ ≤ (Set.ncard (C ∩ Set.Iic N) : ℝ) / (N + 1)) :=
  sorry

/--
The literal reading is false too (PROVED; a corollary of `erdos_problem_125`): there is no
positive δ with the proportion of C ∩ [0, N] tending to δ. If it did, it would eventually exceed
δ / 2.
-/
theorem erdos_problem_125.variants.no_positive_density :
    ¬ ∃ δ : ℝ, 0 < δ ∧
      Tendsto (fun N : ℕ =>
        (Set.ncard (sumSet (digitSet 3) (digitSet 4) ∩ Set.Iic N) : ℝ) / (N + 1))
        atTop (𝓝 δ) := by
  rintro ⟨δ, hδ, hlim⟩
  have h := erdos_problem_125
  dsimp only at h
  exact h ⟨δ / 2, by linarith,
    (hlim.eventually (lt_mem_nhds (by linarith : δ / 2 < δ))).mono fun N hN => hN.le⟩

/--
The reading with positive upper density (OPEN; asserted in the asked direction): there is a
positive δ such that the proportion of C ∩ [0, N] is at least δ for infinitely many N.
-/
theorem erdos_problem_125.variants.positive_upper_density :
    ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ N in atTop,
      δ ≤ (Set.ncard (sumSet (digitSet 3) (digitSet 4) ∩ Set.Iic N) : ℝ) / (N + 1) :=
  sorry

/--
Hasler and Melfi [HaMe24] (PROVED): |C ∩ [1, x]| ≫ x^{0.9777}, improving Melfi's [Me01] exponent
0.965.
-/
theorem erdos_problem_125.variants.hasler_melfi :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ (0.9777 : ℝ) ≤
        (Set.ncard (sumSet (digitSet 3) (digitSet 4) ∩ Set.Iic N) : ℝ) :=
  sorry
