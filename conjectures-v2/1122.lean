import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős Problem #1122

Source: https://www.erdosproblems.com/1122 (page last edited 30 December 2025;
archived capture accessed 2026-02-23).

Verbatim statement: "Let $f:\mathbb{N}\to \mathbb{R}$ be an additive function
(i.e. $f(ab)=f(a)+f(b)$ whenever $(a,b)=1$). Let
\[A=\{ n \geq 1: f(n+1)< f(n)\}.\]
If $\lvert A\cap [1,X]\rvert =o(X)$ then must $f(n)=c\log n$ for some
$c\in \mathbb{R}$?"

Status: OPEN (banner tooltip: "This is open, and cannot be resolved with a
finite computation"). Tag: number theory. Attribution: [Er46].

Remarks from the page:

* Erdős proved that $f(n)=c\log n$ for some $c\in\mathbb{R}$ if $A$ is empty,
  or if $f(n+1)-f(n)=o(1)$. (Both cases are formalized below as variants.)
* Partial progress was made by Mangerel [Ma22], who proved that this is true if
  $\lvert A\cap [1,X]\rvert \ll X/(\log X)^{2+c}$ for some $c>0$, and if $g(p)$
  does not have very large values (in a certain technical sense). (Recorded in
  prose only: the page does not specify the "certain technical sense" side
  condition — note it also switches notation from $f$ to $g(p)$ without
  defining $g$ — so formalizing only the density bound would overstate
  Mangerel's theorem.)
* See also problem #491 (which asks about additive functions satisfying the
  stronger hypothesis $|f(n+1)-f(n)| < c$).

Encoding note. The source poses a yes/no question ("must $f(n)=c\log n$…?")
and the problem is OPEN. This raw-file corpus has no `answer()` elaborator (a
formal-conjectures construct), so, following the corpus convention for open
yes/no questions (cf. `conjectures-v2/1113.lean`, `1117.lean`), the main
theorem below is a direct assertion of the conjectured direction — the answer
"yes", the direction toward which all of the page's partial results point. If
the true answer is "no", the statement below is false; what is open is the
question itself.

The hypothesis $\lvert A\cap [1,X]\rvert = o(X)$ (equivalently: $A$ has
natural density zero) is encoded in ε–N form: for every $\varepsilon > 0$,
eventually $\#\{n \in [1,X] : f(n+1) < f(n)\} \le \varepsilon X$.

References (keys as on the recovered page):

[Er46] Erdős, P., _On the distribution function of additive functions_. Ann.
of Math. (2) 47 (1946), 1-20. (Key recovered from the page; the bibliographic
data is carried from the archived styled sibling files
`deepmind/deepmind/491.lean` and `deepmind/deepmind/1122.lean` and is
consistent with reviewer knowledge, but is NOT site-verified — the recovered
`/latex/1122` bibliography lists only [Ma22].)

[Ma22] Mangerel, Alexander P., _Additive functions in short intervals, gaps
and a conjecture of Erdős_. Ramanujan J. (2022), 1023-1090. (Recovered
verbatim from the site's `/latex/1122` page via the session logs; the volume
number was not in the recovered data and is omitted rather than invented.)

Related OEIS sequences: none listed. Additional thanks to: Alfaiz. Formalised
statement in external databases: No (as of the archived capture).
-/

noncomputable section
open Classical Finset

namespace Erdos1122

/--
Erdős Problem #1122 (OPEN) — [Er46]:

Let f : ℕ → ℝ be an additive function (i.e., f(ab) = f(a) + f(b) whenever
gcd(a,b) = 1). Let A = {n ≥ 1 : f(n+1) < f(n)}.

The source asks: if |A ∩ [1,X]| = o(X) (i.e. the set A has natural density
zero), must f(n) = c·log(n) for some c ∈ ℝ?

This theorem asserts the conjectured direction ("yes"); see the module
docstring's encoding note. Erdős proved the answer is yes if A is empty, or if
f(n+1) - f(n) = o(1) [Er46] — see the variants below. Partial progress was
made by Mangerel [Ma22], who proved it under the stronger bound
|A ∩ [1,X]| ≪ X/(log X)^{2+c} for some c > 0, together with a technical
restriction on values at primes (see the module docstring).
-/
theorem erdos_problem_1122
    (f : ℕ → ℝ)
    (hf_add : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a + f b)
    (hA : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ X : ℕ, X ≥ N →
      (((Icc 1 X).filter (fun n => f (n + 1) < f n)).card : ℝ) ≤ ε * (X : ℝ)) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → f n = c * Real.log (n : ℝ) :=
  sorry

/--
Erdős [Er46] (page-confirmed, SOLVED): if f is additive and the set A is
*empty* — that is, f(n+1) ≥ f(n) for every n ≥ 1, so f is non-decreasing on
the positive integers — then f(n) = c·log(n) for some c ∈ ℝ.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1122.variants.monotone
    (f : ℕ → ℝ)
    (hf_add : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a + f b)
    (hA_empty : ∀ n : ℕ, 1 ≤ n → f n ≤ f (n + 1)) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → f n = c * Real.log (n : ℝ) :=
  sorry

/--
Erdős [Er46] (page-confirmed, SOLVED): if f is additive and
f(n+1) - f(n) = o(1) — the consecutive differences tend to 0 — then
f(n) = c·log(n) for some c ∈ ℝ. The o(1) hypothesis is encoded in the same
ε–N style as the main theorem's density hypothesis.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1122.variants.small_gaps
    (f : ℕ → ℝ)
    (hf_add : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a + f b)
    (hgap : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |f (n + 1) - f n| ≤ ε) :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → f n = c * Real.log (n : ℝ) :=
  sorry

end Erdos1122
