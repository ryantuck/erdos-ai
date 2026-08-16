import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open Filter Nat Real

noncomputable section

/--
The normalized prime gap at index n (0-indexed):
  (p_{n+1} - p_n) / log(n+1)
where p_n = nth Nat.Prime n is the n-th prime (so p_0 = 2, p_1 = 3, …).

Indexing note: since `nth Nat.Prime` is 0-indexed while the source's pₙ is
1-indexed (p₁ = 2), Lean index n corresponds to source index m = n + 1, and
the denominator log(n+1) is exactly log m — so this definition agrees with
the source's (p_{m+1} - p_m)/log m term-by-term, not merely asymptotically.

Degenerate value: at n = 0 (source m = 1) the denominator is log 1 = 0 and
Lean's division-by-zero convention gives normalizedPrimeGap 0 = 0, a junk
value. This is the only degenerate index (log(n+1) > 0 for n ≥ 1), and it is
harmless in the theorem below: a strictly monotone index sequence f has
f i ≥ i → ∞, so at most the single term i = 0 can hit it, which cannot
affect any limit.
-/
def normalizedPrimeGap (n : ℕ) : ℝ :=
  ((nth Nat.Prime (n + 1) : ℝ) - (nth Nat.Prime n : ℝ)) / Real.log ((n : ℝ) + 1)

/--
Erdős Problem #5 [Er55c, Er57, Er61, Er65b, Er85c, Er90, Er97c]:

"Let $C\geq 0$. Is there an infinite sequence of $n_i$ such that
$\lim_{i\to \infty}\frac{p_{n_i+1}-p_{n_i}}{\log n_i}=C$?"

Let pₙ denote the n-th prime. Let S be the set of limit points of the sequence
  (p_{n+1} - pₙ) / log n.
The problem asks whether S = [0, ∞], i.e., every value C ∈ [0, ∞] is attained
as a limit along some subsequence.

The problem is OPEN (erdosproblems.com/5, accessed 2026-02-18; status
cross-checked open against the teorth/erdosproblems metadata mirror,
last_update 2025-08-31). The source phrases it as a yes/no question; this
statement asserts the conjectured "yes" direction for finite C, matching the
direct-assertion form of the styled artifact in this repo's archive.

Formally (for finite C): for every C ≥ 0 there exists a strictly increasing
sequence of indices n₁ < n₂ < ⋯ such that
  (p_{nᵢ+1} - p_{nᵢ}) / log nᵢ → C   as i → ∞.
The case C = ∞ is a theorem of Westzynthius [We31] (see the variant below),
so the finite case stated here is the full open content.

Known results toward this conjecture:
- ∞ ∈ S (Westzynthius 1931 [We31]): prime gaps are unbounded relative to log n.
- 0 ∈ S (Goldston–Pintz–Yıldırım 2009 [GPY09]): normalized gaps can be
  arbitrarily small.
- S has positive Lebesgue measure (Erdős 1955 [Er55]; Ricci 1956 [Ri56]).
- S contains arbitrarily large finite numbers (Hildebrand–Maier 1988 [HiMa88]).
- [0, c] ⊆ S for some c > 0 (Pintz 2016 [Pi16]).
- At least 12.5% of [0, ∞) belongs to S (Banks–Freiberg–Maynard 2016 [BFM16]).
- At least 1/3 of [0, ∞) belongs to S, and S has bounded gaps (Merikoski 2020
  [Me20]).

In [Er65b], [Er85c], and [Er97c] Erdős asks whether S is everywhere dense
(but Weisenberg notes that clearly S is closed, so this is equivalent to
asking whether S = [0, ∞]). See also Erdős problem [234] (density of
normalized prime gaps). Tags: number theory, primes. Related OEIS sequence:
A001223 (prime gaps). Additional thanks (per the source page): Desmond
Weisenberg.

References (journal/pages recovered from the original pipeline's fetch of
erdosproblems.com/latex/5; entries marked "sibling consensus" were absent
from that extraction and come from sibling files in this repo; volume
numbers are DEFERRED, not fabricated):
- [Er55c] Erdős, P., Some problems on number theory (1955). (sibling
  consensus; title + year only)
- [Er57] Erdős, P., Some unsolved problems (1957). (sibling consensus;
  title + year only)
- [Er61] Erdős, P., Some unsolved problems. Magyar Tud. Akad. Mat. Kutató
  Int. Közl. 6 (1961), 221-254. (sibling consensus)
- [Er65b] Erdős, P., Some recent advances and current problems in number
  theory. Lectures on Modern Mathematics, Vol. III (1965), 196-244.
- [Er85c] Erdős, P., On some of my problems in number theory I would most
  like to see solved. Number theory (Ootacamund, 1984) (1985), 74-84.
- [Er90] Erdős, P., Some of my favourite unsolved problems. A tribute to
  Paul Erdős (1990), 467-478. (sibling consensus)
- [Er97c] Erdős, P., Some of my favorite problems and results. The
  mathematics of Paul Erdős, I (1997).
- [We31] Westzynthius, E., Über die Verteilung der Zahlen, die zu den n
  ersten Primzahlen teilerfremd sind. Commentationes Physico-Mathematicae
  (1931), 1-37.
- [GPY09] Goldston, D. A., Pintz, J. and Yıldırım, C. Y., Primes in
  tuples. I. Annals of Mathematics (2) (2009), 819-862.
- [Er55] Erdős, P., Some remarks on number theory. Riveon Lematematika
  (1955), 45-48.
- [Ri56] Ricci, G., Recherches sur l'allure de la suite
  {(p_{n+1} - p_n)/log p_n}. Colloque sur la Théorie des Nombres,
  Bruxelles, 1955 (1956), 93-106.
- [HiMa88] Hildebrand, A. and Maier, H., Gaps between prime numbers.
  Proceedings of the American Mathematical Society (1988), 1-9.
- [Pi16] Pintz, J., Polignac numbers, conjectures of Erdős on gaps between
  primes, arithmetic progressions in primes, and the bounded gap
  conjecture. From arithmetic to zeta-functions (2016), 367-384.
- [BFM16] Banks, W. D., Freiberg, T. and Maynard, J., On limit points of
  the sequence of normalized prime gaps. Proceedings of the London
  Mathematical Society (3) (2016), 515-539.
- [Me20] Merikoski, J., Limit points of normalized prime gaps. Journal of
  the London Mathematical Society (2) (2020), 99-124.
-/
theorem erdos_problem_5 :
    ∀ C : ℝ, 0 ≤ C →
      ∃ f : ℕ → ℕ, StrictMono f ∧
        Tendsto (fun i => normalizedPrimeGap (f i)) atTop (nhds C) :=
  sorry

/--
Erdős Problem #5, the C = ∞ case [We31]:

∞ ∈ S: there is a subsequence along which the normalized prime gaps tend to
infinity. This is a theorem of Westzynthius (1931) on large prime gaps —
prime gaps are unbounded relative to log n — and is the reason the main
conjecture above needs to quantify only over finite C ≥ 0 to capture
S = [0, ∞]. SOLVED, per the source page.
-/
theorem erdos_problem_5.variants.westzynthius :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      Tendsto (fun i => normalizedPrimeGap (f i)) atTop atTop :=
  sorry

/--
Erdős Problem #5, the C = 0 case [GPY09]:

0 ∈ S: there is a subsequence along which the normalized prime gaps tend
to 0. This is the celebrated small-gaps theorem of Goldston, Pintz, and
Yıldırım (2009), i.e., the instance C = 0 of the main conjecture above.
SOLVED, per the source page.
-/
theorem erdos_problem_5.variants.goldston_pintz_yildirim :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      Tendsto (fun i => normalizedPrimeGap (f i)) atTop (nhds 0) :=
  sorry

end
