import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem 84

*Reference:* [erdosproblems.com/84](https://www.erdosproblems.com/84)
(page content recovered from archived session-log captures, accessed 2026-03-05;
the live site is unreachable from the review container).

Statement (verbatim from the site): "The cycle set of a graph $G$ on $n$ vertices
is a set $A\subseteq \{3,\ldots,n\}$ such that there is a cycle in $G$ of length
$\ell$ if and only if $\ell \in A$. Let $f(n)$ count the number of possible such
$A$. Prove that $f(n)=o(2^n)$. Prove that $f(n)/2^{n/2}\to \infty$."
[Er94b][Er95][Er96][Er97d] — tags: graph theory, cycles.

Status: **OPEN** (the second part; the first part is solved). The site banner reads
OPEN ("This is open, and cannot be resolved with a finite computation."). The
teorth/erdosproblems metadata mirror (`data/problems.yaml`, checked at commit
a09c7a2, 2026-08-14) agrees: status "open", last update 2025-08-31; no prize;
OEIS: "possible"; formalized upstream: no. The upstream
google-deepmind/formal-conjectures repository (HEAD dd1c2beb, 2026-08-16) has no
`ErdosProblems/84.lean`.

Remarks from the page: "Conjectured by Erdős and Faudree, who showed that
$2^{n/2}<f(n) \leq 2^{n-2}$. The first problem was solved by Verstraëte [Ve04],
who proved $f(n)\ll 2^{n-n^{1/10}}$. This was improved by Nenadov [Ne25] to
$f(n) \ll 2^{n-n^{1/2-o(1)}}$. One can also ask about the existence and value of
$\lim f(n)^{1/n}$."

Small-case caveat (brute-force verified during review over all labeled graphs on
up to 6 vertices): $f(0)=f(1)=f(2)=1$, $f(3)=2$, $f(4)=4$, $f(5)=6$, $f(6)=11$.
The page's strict lower bound $2^{n/2}<f(n)$ is therefore literally false for
$n\le 4$ (e.g. $f(3)=2<2^{3/2}$ and $f(4)=4=2^{4/2}$, not $>$) and first holds at
$n=5$; the variant below states the eventual form. The upper bound
$f(n)\le 2^{n-2}$ holds for every $n\ge 2$, since every cycle set is a subset of
$\{3,\ldots,n\}$, a set of $n-2$ elements.

References (no raw `/latex/84` page survives in the logs; a WebFetch summary of
`/latex/84` and one `/bibs/Er97d` fetch do — provenance per entry):

- [Er94b] Erdős, P., _Some problems in number theory, combinatorics and
  combinatorial geometry_. Math. Pannon. **5** (1994), 261–269. (Expansion from
  the upstream formal-conjectures corpus, consistently attested there; DEFERRED
  against the live `/bibs/Er94b`.)
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165–186. (Expansion attested in
  the upstream formal-conjectures `76.lean`; sibling files in this corpus expand
  the key inconsistently, so DEFERRED against the live `/bibs/Er95`.)
- [Er96] Erdős, P., 1996. (Key-only stub; sibling expansions conflict and no
  authoritative capture survives — full data DEFERRED, not fabricated.)
- [Er97d] Erdős, P., _Some recent problems and results in graph theory_.
  Discrete Math. (1997), 81–85. MR 1432220. (From an archived `/bibs/Er97d`
  fetch of erdosproblems.com itself; the volume number is not in the capture.)
- [Ve04] Verstraëte, J., _On the number of sets of cycle lengths_. Combinatorica
  (2004), 719–730. (From the archived `/latex/84` WebFetch summary; the volume
  number is not in the capture.)
- [Ne25] Nenadov, R., _Improved bound on the number of cycle sets_.
  arXiv:2501.09904 (2025). (From the archived `/latex/84` WebFetch summary.)
-/

noncomputable section

open SimpleGraph

/--
The cycle spectrum of a simple graph: the set of all cycle lengths present in G.

In a simple graph every cycle has length at least 3
(`SimpleGraph.Walk.IsCycle.three_le_length`) and, on `Fin n`, at most `n` (a
cycle visits distinct vertices), so this set is automatically a subset of
`{3, …, n}` as in the source statement — no explicit constraint is needed.

(Reuse note: the upstream formal-conjectures repository now has the identical
definition as `SimpleGraph.cycleLengths` in
`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean`;
that helper is not available from this repository's Mathlib-only imports.)
-/
def cycleSpectrum84 {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {ℓ : ℕ | ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = ℓ}

/--
The number of distinct cycle spectra realizable by simple graphs on Fin n.
This is the $f(n)$ of the problem: every realizable spectrum is a subset of the
finite set $\{3,\ldots,n\}$, so the collection is finite and `Set.ncard` is its
true cardinality (no junk value). Labeled vs. unlabeled graphs is immaterial:
the spectrum is an isomorphism invariant, so the *set* of realizable spectra is
the same either way. Brute-force values: $f(0)=f(1)=f(2)=1$, $f(3)=2$, $f(4)=4$,
$f(5)=6$, $f(6)=11$.
-/
noncomputable def cycleSetCount84 (n : ℕ) : ℕ :=
  Set.ncard {A : Set ℕ | ∃ G : SimpleGraph (Fin n), cycleSpectrum84 G = A}

/--
Erdős Problem #84, Part 1 (conjectured by Erdős and Faudree
[Er94b][Er95][Er96][Er97d]; proved by Verstraëte [Ve04]):

$f(n) = o(2^n)$, where $f(n)$ counts the distinct cycle sets
$A \subseteq \{3,\ldots,n\}$ realizable by graphs on $n$ vertices.
That is, for every ε > 0, for all sufficiently large n, f(n) ≤ ε · 2^n.

Verstraëte proved the stronger $f(n) \ll 2^{n - n^{1/10}}$ (see
`erdos_problem_84.variants.verstraete`), improved by Nenadov [Ne25] to
$f(n) \ll 2^{n - n^{1/2 - o(1)}}$ (see `erdos_problem_84.variants.nenadov`).
-/
theorem erdos_problem_84_part1 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (cycleSetCount84 n : ℝ) ≤ ε * (2 : ℝ) ^ n :=
  sorry

/--
Erdős Problem #84, Part 2 (conjectured by Erdős and Faudree
[Er94b][Er95][Er96][Er97d]; **open**):

$f(n)/2^{n/2} \to \infty$.
That is, for every B > 0, for all sufficiently large n, f(n) ≥ B · 2^{n/2}
(with the real exponent $n/2$, i.e. $2^{n/2} = \sqrt{2^n}$).

Erdős and Faudree showed $2^{n/2} < f(n) \leq 2^{n-2}$ (for large $n$; the
strict lower bound fails for $n \le 4$ — see the module docstring and
`erdos_problem_84.variants.erdos_faudree_lower`).
-/
theorem erdos_problem_84_part2 :
    ∀ B : ℝ, B > 0 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (cycleSetCount84 n : ℝ) ≥ B * (2 : ℝ) ^ ((n : ℝ) / 2) :=
  sorry

/--
Variant (solved, Erdős–Faudree, page remarks): $2^{n/2} < f(n)$ for all
sufficiently large $n$.

The page states the bound without a range, but it is literally false at small
$n$: brute force gives $f(3) = 2 < 2^{3/2}$ and $f(4) = 4 = 2^{4/2}$ (not $>$),
with the bound first holding at $n = 5$ ($f(5) = 6 > 2^{5/2} \approx 5.66$).
Following the 1004-precedent, the eventual form is formalized and the
counterexamples are documented here.
[erdosproblems.com/84, remarks: "Conjectured by Erdős and Faudree, who showed
that $2^{n/2}<f(n) \leq 2^{n-2}$."]
-/
theorem erdos_problem_84.variants.erdos_faudree_lower :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 : ℝ) ^ ((n : ℝ) / 2) < (cycleSetCount84 n : ℝ) :=
  sorry

/--
Variant (solved, Erdős–Faudree, page remarks): $f(n) \leq 2^{n-2}$ for every
$n \geq 2$.

This direction holds for all $n \ge 2$ (not just eventually): every realizable
cycle set is a subset of $\{3,\ldots,n\}$, which has $n-2$ elements. The
exponent is taken in ℝ (with the hypothesis $2 \le n$ keeping it nonnegative);
without that hypothesis the real-exponent form is false at $n \in \{0,1\}$
since $f(0) = f(1) = 1 > 2^{n-2}$.
[erdosproblems.com/84, remarks]
-/
theorem erdos_problem_84.variants.erdos_faudree_upper :
    ∀ n : ℕ, 2 ≤ n →
      (cycleSetCount84 n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) - 2) :=
  sorry

/--
Variant (solved, Verstraëte [Ve04]): $f(n) \ll 2^{n - n^{1/10}}$, i.e. there is
a constant $C > 0$ with $f(n) \leq C \cdot 2^{n - n^{1/10}}$ for all $n$.
(All exponents are real; since the right-hand side is strictly positive for
every $n$, the "for all $n$" and "for all large $n$" forms are equivalent here.)
[erdosproblems.com/84, remarks: "The first problem was solved by Verstraëte
[Ve04], who proved $f(n)\ll 2^{n-n^{1/10}}$."]
-/
theorem erdos_problem_84.variants.verstraete :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (cycleSetCount84 n : ℝ) ≤ C * (2 : ℝ) ^ ((n : ℝ) - (n : ℝ) ^ ((1 : ℝ) / 10)) :=
  sorry

/--
Variant (solved, Nenadov [Ne25]): $f(n) \ll 2^{n - n^{1/2 - o(1)}}$, encoded as:
for every $\varepsilon > 0$ and all sufficiently large $n$,
$f(n) \leq 2^{n - n^{1/2 - \varepsilon}}$. (The multiplicative constant of
$\ll$ is absorbed by the eventual quantifier, since shrinking the exponent gap
by any fixed $\varepsilon' < \varepsilon$ dominates any constant for large $n$.)
[erdosproblems.com/84, remarks: "This was improved by Nenadov [Ne25] to
$f(n) \ll 2^{n-n^{1/2-o(1)}}$."]
-/
theorem erdos_problem_84.variants.nenadov :
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (cycleSetCount84 n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) - (n : ℝ) ^ ((1 : ℝ) / 2 - ε)) :=
  sorry

/--
Variant (**open question**, page remarks): does $\lim_{n\to\infty} f(n)^{1/n}$
exist (and what is its value)?

Encoding note: the page poses this as a question, not a conjecture in either
direction; following the affirmative-assertion convention it is stated here as
the existence of the limit. If the limit exists it lies in $[\sqrt 2, 2]$ by
the Erdős–Faudree bounds. The $n = 0$ term is the harmless junk value
$f(0)^{1/0} = f(0)^0 = 1$ (Lean: `(0 : ℝ)⁻¹ = 0`), which does not affect the
limit. Not compile-verified: `Filter.Tendsto`/`nhds` are expected to be
reachable from `Mathlib.Analysis.SpecialFunctions.Pow.Real`.
[erdosproblems.com/84, remarks: "One can also ask about the existence and value
of $\lim f(n)^{1/n}$."]
-/
theorem erdos_problem_84.variants.limit_exists :
    ∃ L : ℝ, Filter.Tendsto
      (fun n : ℕ => (cycleSetCount84 n : ℝ) ^ ((n : ℝ)⁻¹))
      Filter.atTop (nhds L) :=
  sorry

end
