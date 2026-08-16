import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

/-!
# Erdős Problem #53

Verbatim from erdosproblems.com/53 (archived capture, accessed 2026-02-22):

"Let $A$ be a finite set of integers. Is it true that, for every $k$, if
$\lvert A\rvert$ is sufficiently large depending on $k$, then there are
[at] least $\lvert A\rvert^k$ many integers which are either the sum or
product of distinct elements of $A$?"

(The bracketed "at" corrects an evident typo on the page, which reads
"there are least".)

Asked by Erdős and Szemerédi [ErSz83]. Solved in this form by Chang [Ch03].

Status and provenance (Fable review):
- Page banner at capture: PROVED, tooltip "This has been solved in the
  affirmative." Tags: number theory | additive combinatorics. OEIS:
  "Possible" (no specific sequence listed). Cross-reference: "See also
  [52]" (the pairwise Erdős–Szemerédi sum-product conjecture, a distinct
  problem formalized separately). 0 forum comments; no prize.
- The metadata mirror (github.com/teorth/erdosproblems, data/problems.yaml,
  commit a09c7a2, 2026-08-14) agrees: state "proved", last update
  2025-08-31; tags number theory, additive combinatorics; formal status
  "unformalized".
- The upstream formal-conjectures repository at HEAD dd1c2beb (2026-08-16)
  has no `FormalConjectures/ErdosProblems/53.lean`, consistent with the
  mirror's "unformalized".
- Since the problem is solved in the affirmative, the direct-assertion form
  below (asserting the "yes" direction) is the correct polarity.

Page remark (upper bound, [ErSz83]): Erdős and Szemerédi proved that there
exist arbitrarily large sets $A$ such that the number of integers which are
the sum or product of distinct elements of $A$ is at most
$\exp(c (\log \lvert A\rvert)^2 \log\log \lvert A\rvert)$ for some constant
$c > 0$ — so the $\lvert A\rvert^k$ growth asked for here is essentially
best possible in the superpolynomial-but-subexponential sense. (Not
formalized as a variant here: `Real.exp`/`Real.log` are not among this
file's imports and this pipeline adds no unverified import chains —
deferred.)

References (assembled by the Fable review; the raw input used the keys with
no bibliography):
- [ErSz83] Erdős, P. and Szemerédi, E., _On sums and products of integers_.
  Studies in Pure Mathematics (To the memory of Paul Turán), Birkhäuser,
  Basel (1983), 213-218. (Title/venue/year/pages from the log-recovered
  `/latex/53` extraction; the Birkhäuser volume identification also
  corroborated by sibling corpus files 52/808.)
- [Ch03] Chang, M.-C., _The Erdős-Szemerédi problem on sum set and product
  set_. Annals of Mathematics 157 (2003), no. 3, 939-957. (Journal/year/
  pages from the log-recovered `/latex/53` extraction, which lacked the
  volume; volume 157(3) from the archived styled artifact and the upstream
  branch capture — live verification DEFERRED.)
- The page's statement line additionally cites [Er77c], [ErGr80], [Er91],
  [Er97], [Er97e] (general Erdős problem collections discussing this
  problem). Honest stubs from sibling corpus files, no /bibs payload in the
  logs: [Er77c] Erdős, P., _Problems and results on combinatorial number
  theory. III_. Number Theory Day (Proc. Conf., Rockefeller Univ., New
  York, 1976) (1977), 43-72. [ErGr80] Erdős, P. and Graham, R., _Old and
  new problems and results in combinatorial number theory_. Monographies de
  L'Enseignement Mathématique (1980). [Er91], [Er97], [Er97e]: Erdős
  problems papers whose expansions are inconsistent across sibling corpus
  files — key-only stubs, DEFERRED.

Tags: number theory, additive combinatorics
-/

/--
The set of all subset sums of a finite set of integers:
$\{ \sum_{i \in S} i \mid S \subseteq A \}$.

Note (Fable review): the powerset includes `∅` (empty sum `0`) and all
singletons (each element of `A` is its own subset sum). Including these at
most enlarges the set — direction-safe for the lower-bound assertion below —
and matches the upstream formal-conjectures convention for `subsetSums`
(`∃ B : Finset M, ↑B ⊆ A ∧ n = ∑ i ∈ B, i`, which also admits `B = ∅`).
-/
def subsetSums (A : Finset ℤ) : Finset ℤ :=
  A.powerset.image (fun S => ∑ i ∈ S, i)

/--
The set of all subset products of a finite set of integers:
$\{ \prod_{i \in S} i \mid S \subseteq A \}$.

Note (Fable review): the powerset includes `∅` (empty product `1`) and all
singletons. As with `subsetSums`, this enlarges the union by at most the two
constants `0` and `1` beyond the strictest reading of "sum or product of
distinct elements", which cannot hurt a lower bound of the form
`card ≥ |A|^k`.
-/
def subsetProducts (A : Finset ℤ) : Finset ℤ :=
  A.powerset.image (fun S => ∏ i ∈ S, i)

/--
**Erdős Problem #53** [ErSz83] — PROVED (Chang [Ch03]):

For every $k$, there exists $N$ such that for any finite set $A$ of integers
with $|A| \geq N$, the number of integers that are either a sum or product of
distinct elements of $A$ is at least $|A|^k$.

The source poses this as a yes/no question ("Is it true that...?"); Chang
solved it in the affirmative, so this direct assertion states the true
direction. $N$ depends only on $k$, matching "sufficiently large depending
on $k$". The instances $k = 0, 1$ are trivially true (every element of $A$
is a singleton subset sum, so the union has at least $|A|$ elements); their
inclusion is harmless.
-/
theorem erdos_53 :
    ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset ℤ,
    A.card ≥ N →
    (subsetSums A ∪ subsetProducts A).card ≥ A.card ^ k :=
  sorry
