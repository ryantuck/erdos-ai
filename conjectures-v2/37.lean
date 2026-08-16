import Mathlib.Data.Real.Archimedean
import Mathlib.Data.PNat.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős Problem 37

*Reference:* [erdosproblems.com/37](https://www.erdosproblems.com/37)
(accessed 2026-02-22, page last edited 23 January 2026; page content recovered from
two agreeing archived session-log captures — the live site is unreachable from the
review container).

Statement (verbatim from the site): "We say that $A\subset \mathbb{N}$ is an
essential component if $d_s(A+B)>d_s(B)$ for every $B\subset \mathbb{N}$ with
$0<d_s(B)<1$ where $d_s$ is the Schnirelmann density.

Can a lacunary set $A\subset\mathbb{N}$ be an essential component?"
[Er56, p.136] [Er61, p.229] [Er73, p.135] [ErGr80, p.49]

Status: **DISPROVED** ("This has been solved in the negative."). The
teorth/erdosproblems metadata mirror (`data/problems.yaml`, checked at commit
a09c7a21, 2026-08-14) agrees: status "disproved" (last update 2025-08-31); tags:
number theory, additive combinatorics; no OEIS references; no prize. The site lists
no upstream formalization ("Formalised statement? No").

Remarks from the page: The answer is no by Ruzsa [Ru87], who proved that if $A$ is an
essential component then there exists some constant $c>0$ such that
$\lvert A\cap \{1,\ldots,N\}\rvert \geq (\log N)^{1+c}$ for all large $N$.
Furthermore, Ruzsa proves that this is best possible, in that for any $c>0$ there
exists an essential component $A$ for which
$\lvert A\cap \{1,\ldots,N\}\rvert \leq (\log N)^{1+c}$ for all large $N$.
See also Erdős Problem 1146 for whether $\{2^m3^n\}$ is an essential component
(formalized in this corpus as `conjectures/1146.lean`). Additional thanks: Wouter
van Doorn.

[Er56] Erdős, P., _Problems and results in additive number theory_. Colloque sur la
Théorie des Nombres, Bruxelles, 1955 (1956), 127-137.

[Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl.
6 (1961), 221-254.

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins,
Colo., 1971) (1973), 117-138.

[ErGr80] Erdős, P. and Graham, R.L., _Old and new problems and results in
combinatorial number theory_. Monographies de L'Enseignement Mathématique 28 (1980).

[Ru87] Ruzsa, I.Z., _Essential components_. Proc. London Math. Soc. (3) 54 (1987),
38-56. (Author/title/journal/year/pages as on the site's `/latex/37` bibliography,
which gives no volume number; the volume "(3) 54" is the standard citation of this
paper, as already adopted by the archived styled pipeline.)

Bibliographic provenance: [Er56], [Er61], [Er73], [ErGr80] are the canonical entries
shared across this corpus's sibling files (e.g. `conjectures-v2/31.lean`,
`conjectures-v2/34.lean`) and the upstream google-deepmind/formal-conjectures
repository (checked at commit dd1c2beb); [Ru87] is from the
`erdosproblems.com/latex/37` bibliography fetch captured in the original pipeline
session logs.
-/

open Classical

/--
The Schnirelmann density of a set A ⊆ ℕ, defined as
  d_s(A) = inf_{n ≥ 1} |A ∩ {1,...,n}| / n

The `⨅` over `ℕ+` is a genuine infimum in ℝ: the index type is nonempty and every
term is nonnegative, so the range is nonempty and bounded below (no `Real.sInf`
junk-value degeneracy). Mathlib's own `schnirelmannDensity`
(`Mathlib.Combinatorics.Schnirelmann`, via `Finset.Ioc 0 n`) is mathematically
identical; the local definition is kept to preserve this file's import closure.
-/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  ⨅ n : ℕ+, (((Finset.Icc 1 (n : ℕ)).filter (· ∈ A)).card : ℝ) / ((n : ℕ) : ℝ)

/--
The sumset A + B = {a + b | a ∈ A, b ∈ B} for sets of natural numbers.
(Identical to Mathlib's pointwise `A + B` under `open Pointwise`, up to the
orientation of the defining equation.)
-/
def sumset (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/--
A set A ⊆ ℕ is an essential component if d_s(sumset A B) > d_s(B) for every
B ⊆ ℕ with 0 < d_s(B) < 1, where d_s is the Schnirelmann density.
(Verbatim the definition given on the problem page.)
-/
def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ (B : Set ℕ), 0 < schnirelmannDensity B → schnirelmannDensity B < 1 →
    schnirelmannDensity (sumset A B) > schnirelmannDensity B

/--
A set A ⊆ ℕ is lacunary if there exists q > 1 such that for any two
consecutive elements a < b of A (with no element of A strictly between them),
we have b ≥ q * a.

Degenerate-input notes: (i) any finite set (including ∅ and singletons) satisfies
this predicate vacuously or by taking q slightly above 1 below the finitely many
consecutive ratios — a benign extension of the usual notion (which concerns infinite
sequences), since by Ruzsa's bound [Ru87] essential components are necessarily
infinite, so the main theorem below remains true over this wider class; (ii) if
0 ∈ A, the constraint for the consecutive pair (0, b) reads b ≥ q·0 and is trivially
satisfied, so lacunarity constrains only the ratios of positive consecutive elements
— for an infinite lacunary set the counting function is still O(log N).
-/
def IsLacunary (A : Set ℕ) : Prop :=
  ∃ (q : ℝ), q > 1 ∧ ∀ (a b : ℕ), a ∈ A → b ∈ A → a < b →
    (∀ c ∈ A, ¬(a < c ∧ c < b)) → (b : ℝ) ≥ q * (a : ℝ)

/--
Erdős Problem #37 (Disproved by Ruzsa [Ru87]).

The page asks (yes/no question): "Can a lacunary set A ⊂ ℕ be an essential
component?" The answer is **no** [Ru87], and this theorem asserts that negative
resolution directly: a lacunary set cannot be an essential component.
Ruzsa proved that if A is an essential component then there exists some constant
c > 0 such that |A ∩ {1,...,N}| ≥ (log N)^{1+c} for all large N, which rules
out lacunary sets (which satisfy |A ∩ {1,...,N}| = O(log N)); see
`erdos_problem_37.variants.ruzsa_lower`. Ruzsa also proved this growth exponent is
best possible; see `erdos_problem_37.variants.ruzsa_optimal`.

Problem sources on the page: [Er56, p.136] [Er61, p.229] [Er73, p.135]
[ErGr80, p.49]. See also Erdős Problem 1146 (whether {2^m 3^n} is an essential
component).
-/
theorem erdos_problem_37 :
    ∀ (A : Set ℕ), IsLacunary A → ¬IsEssentialComponent A :=
  sorry

/--
Ruzsa's lower bound [Ru87] (page-confirmed variant, not compile-verified): if A is
an essential component, then there exists a constant c > 0 such that
|A ∩ {1,...,N}| ≥ (log N)^{1+c} for all large N.

Encoding note: this file's import closure has no `Real.log` or real-exponent power
(`rpow`), so the bound is stated in an equivalent dyadic, natural-number form:
there is a k ≥ 1 with |A ∩ {1,...,2^m}|^k ≥ m^(k+1) for all large m. Equivalence
with the page's statement (for the nondecreasing counting function
f(N) = |A ∩ {1,...,N}|, any fixed log base — base change is absorbed by the
exponent gap):
* (⇒) Given c > 0 with f(N) ≥ (ln N)^{1+c} for large N, pick k > 1/c. Then
  f(2^m) ≥ (m ln 2)^{1+c} = (ln 2)^{1+c}·m^{1+c} ≥ m^{1+1/k} for large m (the
  constant is beaten by m^{c-1/k} → ∞), and for naturals
  f(2^m) ≥ m^{1+1/k} ⟺ f(2^m)^k ≥ m^{k+1}.
* (⇐) Given k with f(2^m)^k ≥ m^{k+1} for m ≥ M, take any N ≥ 2^{M+1} and
  m = ⌊log₂ N⌋ ≥ M: f(N) ≥ f(2^m) ≥ m^{1+1/k} ≥ (log₂ N - 1)^{1+1/k} ≥
  (ln N)^{1+c} for large N with c = 1/(2k), since log₂ N - 1 ≥ ln N once
  ln N ≥ ln 2/(1 - ln 2), and the exponent gap 1/k - c > 0 absorbs constants.
-/
theorem erdos_problem_37.variants.ruzsa_lower :
    ∀ (A : Set ℕ), IsEssentialComponent A →
      ∃ k : ℕ, 1 ≤ k ∧ ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((Finset.Icc 1 (2 ^ m)).filter (· ∈ A)).card ^ k ≥ m ^ (k + 1) :=
  sorry

/--
Optimality of Ruzsa's lower bound [Ru87] (page-confirmed variant, not
compile-verified): for any c > 0 there exists an essential component A with
|A ∩ {1,...,N}| ≤ (log N)^{1+c} for all large N.

Encoding note: stated in the dyadic, natural-number form dual to
`erdos_problem_37.variants.ruzsa_lower`: for every k ≥ 1 there is an essential
component A with |A ∩ {1,...,2^m}|^k ≤ m^(k+1) for all large m. Equivalence with
the page's ∀c-statement (f nondecreasing): (⇐, the direction making this form
sufficient) given c > 0 pick k > 1/c and A as here; for large N and
m = ⌊log₂ N⌋, f(N) ≤ f(2^{m+1}) ≤ (m+1)^{1+1/k} ≤ (log₂ N + 1)^{1+1/k} ≤
(ln N)^{1+c}, the exponent gap c - 1/k > 0 absorbing the base-change constant
1/ln 2 > 1. (⇒) conversely, given the page's statement, apply it with any positive
c' < 1/k: f(2^m) ≤ (m ln 2)^{1+c'} ≤ m^{1+1/k} for large m since ln 2 < 1, whence
f(2^m)^k ≤ m^{k+1}.
-/
theorem erdos_problem_37.variants.ruzsa_optimal :
    ∀ k : ℕ, 1 ≤ k →
      ∃ (A : Set ℕ), IsEssentialComponent A ∧ ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((Finset.Icc 1 (2 ^ m)).filter (· ∈ A)).card ^ k ≤ m ^ (k + 1) :=
  sorry
