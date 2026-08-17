import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

open scoped Classical

/-!
# Erdős Problem #27

An $\epsilon$-almost covering system is a set of congruences $a_i \pmod{n_i}$
for distinct moduli $n_1 < \ldots < n_k$ such that the density of those
integers which satisfy none of them is $\leq \epsilon$.

Is there a constant $C > 1$ such that for every $\epsilon > 0$ and $N \geq 1$
there is an $\epsilon$-almost covering system with
$N \leq n_1 < \cdots < n_k \leq CN$?

**Status: DISPROVED** — banner tooltip: "This has been solved in the
negative." $100 prize. (erdosproblems.com/27, page last edited
06 December 2025; the teorth/erdosproblems metadata mirror agrees: state
"disproved", last update 2025-08-31.) We formalize the negation (the proved
result) as a direct assertion.

Remarks from the source page:

- By a simple averaging argument the set of moduli $[m_1, m_2] \cap \mathbb{N}$
  has a choice of residue classes which form an
  $\epsilon(m_1, m_2)$-almost covering system with
  $\epsilon(m_1, m_2) = \prod_{m_1 \leq m \leq m_2} (1 - 1/m)$.
  (Formalized below as `erdos_problem_27.variants.averaging`.)
- A $0$-covering system is just a covering system, and so by Hough [Ho15]
  these only exist for $n_1 < 10^{18}$ (now $< 616000$ thanks to [BBMST22]).
- The answer is no, as proved by Filaseta, Ford, Konyagin, Pomerance, and Yu
  [FFKPY07], who (among other results) prove that if
  $1 < C \leq N^{\frac{\log\log\log N}{4\log\log N}}$ then, for any
  $N \leq n_1 < \cdots < n_k \leq CN$, the density of integers not covered
  for any fixed choice of residue classes is at least
  $(1 - o(1)) \prod_i (1 - 1/n_i)$ (and this density is achieved for some
  choice of residue classes as above).

## References

Problem source: [Er95, p.4].

- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas 1 (1995), 165-186. (Stub: the page
  capture gives only the key `[Er95,p.4]`; the log-recovered `/latex/27`
  extraction does not include the problem-source entry. Title/journal/pages
  from sibling corpus files sharing this site-global key for number-theory
  problems, e.g. `deepmind/deepmind/29.lean`, `conjectures-v2/25.lean`.)
- [FFKPY07] Filaseta, M., Ford, K., Konyagin, S., Pomerance, C., and Yu, G.,
  _Sieving by large integers and covering systems of congruences_.
  J. Amer. Math. Soc. 20 (2007), no. 2, 495-517. (Authors/title/journal/
  year/pages from the log-recovered `/latex/27` extraction; volume and issue
  from the sibling corpus entries `deepmind/deepmind/2.lean` and
  `deepmind/deepmind/27.lean`, unverified offline.)
- [Ho15] Hough, R. D., _Solution of the minimum modulus problem for covering
  systems_. Ann. of Math. (2) 181 (2015), no. 1, 361-382. (Authors/title/
  journal/year/pages from the log-recovered `/latex/27` extraction; volume
  and issue from the sibling corpus entry `deepmind/deepmind/2.lean`,
  unverified offline.)
- [BBMST22] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J., and
  Tiba, M., _On the Erdős covering problem: the density of the uncovered
  set_. Invent. Math. (2022), 377-414. (From the log-recovered `/latex/27`
  extraction; no volume number recovered.)

No related OEIS sequences (mirror: "N/A").
Formalised statement? No, per the page capture and the mirror
("unformalized"); upstream google-deepmind/formal-conjectures has no
`ErdosProblems/27.lean` at HEAD dd1c2beb.

Tags: number theory, covering systems
https://www.erdosproblems.com/27
-/

/-- A congruence system has distinct moduli if no two pairs share the same modulus. -/
def Erdos27.hasDistinctModuli (S : Finset (ℤ × ℕ)) : Prop :=
  S.card = (S.image Prod.snd).card

/-- The LCM of all moduli in a congruence system.

Degenerate cases: for `S = ∅` this is `1` (the empty LCM); if any modulus
is `0` it is `0`. The theorems below only apply it to nonempty systems
whose moduli are all positive. -/
noncomputable def Erdos27.systemLcm (S : Finset (ℤ × ℕ)) : ℕ :=
  (S.image Prod.snd).lcm id

/-- The density of uncovered integers for a congruence system,
    measured as the proportion of integers in {0, …, L-1} not covered
    by any congruence, where L = lcm of all moduli.

Since every modulus divides L, the uncovered set is periodic with period L,
so this proportion equals the natural density of the uncovered integers.

Degenerate cases: for `S = ∅` the value is `1` (nothing is covered); if
some modulus is `0` then `L = 0` and the value is the division-by-zero junk
value `0`. The theorems below exclude both cases (`S.Nonempty`, positive
moduli). -/
noncomputable def Erdos27.uncoveredDensity (S : Finset (ℤ × ℕ)) : ℝ :=
  let L := Erdos27.systemLcm S
  ((range L).filter (fun x =>
    ∀ p ∈ S, ¬((↑p.2 : ℤ) ∣ (↑x - p.1)))).card / (L : ℝ)

/-- Erdős Problem #27 [Er95, p.4]:

Is there a constant $C > 1$ such that for every $\epsilon > 0$ and
$N \geq 1$ there is an $\epsilon$-almost covering system with
$N \leq n_1 < \cdots < n_k \leq CN$?

The answer is **no**, proved by Filaseta, Ford, Konyagin, Pomerance, and Yu
[FFKPY07]; the negation is asserted directly.

(The side conditions `S.Nonempty` and `∀ p ∈ S, p.2 ≥ 2` restrict the
witnesses to genuine systems — at `N = 1` they rule out the empty system and
the trivial modulus-1 congruence that covers everything. This does not
change the truth of the statement: for `C ≥ 12` the classical covering
system `{0 (mod 2), 0 (mod 3), 1 (mod 4), 5 (mod 6), 7 (mod 12)}` handles
`N = 1` even with the restrictions, and for `N ≥ 2` the constraint
`N ≤ p.2` makes them automatic, so the restricted and unrestricted
questions have the same answer.) -/
theorem erdos_problem_27 :
    ¬ ∃ C : ℝ, C > 1 ∧
      ∀ ε : ℝ, ε > 0 →
      ∀ N : ℕ, N ≥ 1 →
      ∃ S : Finset (ℤ × ℕ),
        Erdos27.hasDistinctModuli S ∧
        S.Nonempty ∧
        (∀ p ∈ S, p.2 ≥ 2) ∧
        (∀ p ∈ S, N ≤ p.2 ∧ (p.2 : ℝ) ≤ C * N) ∧
        Erdos27.uncoveredDensity S ≤ ε :=
  sorry

/-- [Er95, p.4], remarks on the source page:

By a simple averaging argument the set of moduli $[m_1, m_2] \cap \mathbb{N}$
has a choice of residue classes which form an
$\epsilon(m_1, m_2)$-almost covering system with
$\epsilon(m_1, m_2) = \prod_{m_1 \leq m \leq m_2} (1 - 1/m)$.

(Choosing the residues independently and uniformly at random makes each
integer uncovered with probability exactly the product, so some choice
does at least as well as the average. The hypothesis `1 ≤ m₁` keeps the
degenerate modulus `0` out of the system; the statement is trivially true
at `m₁ = 1`, where the modulus-1 congruence covers everything and the
product vanishes.) -/
theorem erdos_problem_27.variants.averaging (m₁ m₂ : ℕ) (h₁ : 1 ≤ m₁) (h₂ : m₁ ≤ m₂) :
    ∃ S : Finset (ℤ × ℕ),
      Erdos27.hasDistinctModuli S ∧
      S.image Prod.snd = Icc m₁ m₂ ∧
      Erdos27.uncoveredDensity S ≤ ∏ m ∈ Icc m₁ m₂, (1 - 1 / (m : ℝ)) :=
  sorry
