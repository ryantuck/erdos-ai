import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #1114

Source: https://www.erdosproblems.com/1114 (page last edited 29 December 2025;
archived capture accessed 2026-02-23).

Verbatim statement: "Let $f(x)\in \mathbb{R}[x]$ be a polynomial of degree $n$
whose roots $\{a_0<\cdots<a_n\}$ are all real and form an arithmetic
progression. The differences between consecutive zeros of $f'(x)$, beginning
from the midpoint of $(a_0,a_m)$ towards the endpoints, are monotonically
increasing."

Two typos in the source are noted for the record: a degree-$n$ polynomial
cannot have the $n+1$ listed roots $a_0 < \cdots < a_n$ (this file follows the
root count, so `f` below has degree $n+1$ and the parameter `n` is the degree
of $f'$); and the undefined $a_m$ is read as $a_n$ (the right endpoint), as
also in the page's remark quoted next.

Status: PROVED (banner tooltip: "This has been solved in the affirmative.").
Tags: polynomials, analysis.

Remarks from the page:

* "All the zeros of $f'(x)$ are all distinct real numbers in $(a_0,a_m)$
  [read: $(a_0,a_n)$] by Rolle's theorem." (Formalized as a variant below.)
* "This was proved by Balint [Ba60b]. Balint gives no source for the
  conjecture - presumably it was from Erdős in personal communication. Some
  generalisations of this were given by Lorch [Lo76]." (The page does not say
  what Lorch's generalisations are, so no variant is attempted for them.)

Encoding notes. The source states the result as a direct assertion and it is
PROVED, so the theorem is a bare proposition (no answer-wrapper; this raw
corpus has none anyway). The polynomial is normalized to the monic
$\prod_{i=0}^{n}(X - (a + i\,d))$ with $d > 0$: any real polynomial with the
given roots is a nonzero scalar multiple of this one, and scaling changes
neither $f'$'s zero set nor the gaps, so the normalization is without loss of
generality. The zeros of $f'$ are $b_0 < \cdots < b_{n-1}$, with $n - 1$ gaps
$g_i = b_{i+1} - b_i$ ($0 \le i \le n-2$), and "monotonically increasing from
the midpoint towards the endpoints" is rendered as BOTH monotone runs: the
right run $g_i \le g_j$ for $\lfloor(n-1)/2\rfloor \le i < j \le n-2$ (note
$\lfloor(n-1)/2\rfloor = \lceil(n-2)/2\rceil$, the first gap index at or right
of center), and the left run $g_j \le g_i$ for $i < j \le \lfloor(n-2)/2\rfloor$.
The first-pass file stated only the right run, delegating the left run to an
unstated symmetry lemma; v2 states both (see fable-review/1114.md).

References (authors, titles, journals, years, and pages recovered from the
site's `/latex/1114` bibliography via the session logs; volume numbers were
not in the recovered data and are omitted rather than invented):

[Ba60b] Bálint, Elemér, _Proof of a conjecture of P. Erdős_. Mathematikai
Lapok (1960), 33–40.

[Lo76] Lorch, L., _Some monotonicity properties of polynomials with equally
spaced zeros_. Acta Mathematica Academiae Scientiarum Hungaricae (1976),
293–300.

Additional thanks to: Alfaiz. Formalised statement in external databases: No
(as of the archived capture). No related OEIS sequences are listed.
-/

open scoped BigOperators
open Polynomial Finset

noncomputable section

namespace Erdos1114

/--
Erdős Problem #1114 (PROVED, by Bálint [Ba60b]; generalisations by Lorch [Lo76]):

Let f(x) ∈ ℝ[x] be a polynomial whose (n+1) roots are all real, distinct, and
form an arithmetic progression: a, a+d, a+2d, ..., a+n·d for some a ∈ ℝ, d > 0.
By Rolle's theorem, f'(x) has n distinct real zeros b₀ < b₁ < ⋯ < b_{n-1}
in the interval (a, a+n·d).

The conjecture (now proved) states that the differences between consecutive
zeros of f'(x), beginning from the midpoint towards the endpoints, are
monotonically increasing. Writing g_i = b_{i+1} - b_i for the n-1 gaps
(0 ≤ i ≤ n-2), this is stated as both monotone runs:

* right run — for ⌊(n-1)/2⌋ ≤ i < j ≤ n-2 (encoded as j + 1 < n), g_i ≤ g_j;
  here ⌊(n-1)/2⌋ = ⌈(n-2)/2⌉ is the first gap index at or right of center;
* left run — for i < j ≤ ⌊(n-2)/2⌋, g_j ≤ g_i (gaps grow towards the left
  endpoint, i.e. as the index decreases).

The zeros are also symmetric about the center a + n·d/2 (so g_i = g_{n-2-i});
this is a provable fact about the configuration, not an assumption, and the
statement above does not rely on it. The subtraction n - 1 and the divisions
by 2 are ℕ operations; with hn : 2 ≤ n they are the intended ⌊·⌋ values.

Balint gives no source for the conjecture — presumably it was from Erdős in
personal communication.
-/
theorem erdos_problem_1114 (n : ℕ) (hn : 2 ≤ n) (a d : ℝ) (hd : 0 < d) :
    let f := ∏ i ∈ range (n + 1), (X - C (a + ↑i * d))
    ∃ b : ℕ → ℝ,
      (∀ i j, i < n → j < n → i < j → b i < b j) ∧
      (∀ j, j < n → (derivative f).IsRoot (b j)) ∧
      (∀ x : ℝ, (derivative f).IsRoot x → ∃ j, j < n ∧ b j = x) ∧
      (∀ i j, (n - 1) / 2 ≤ i → i < j → j + 1 < n →
        b (i + 1) - b i ≤ b (j + 1) - b j) ∧
      ∀ i j, i < j → j ≤ (n - 2) / 2 →
        b (j + 1) - b j ≤ b (i + 1) - b i :=
  sorry

/--
Page-confirmed remark (SOLVED, classical): "All the zeros of $f'(x)$ are all
distinct real numbers in $(a_0,a_n)$ by Rolle's theorem." With the same setup
and the same enumeration clauses as the main statement, every zero of f' lies
strictly between the smallest root a and the largest root a + n·d. Distinctness
is carried by the strict ordering of b.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1114.variants.rolle_interval (n : ℕ) (hn : 2 ≤ n) (a d : ℝ)
    (hd : 0 < d) :
    let f := ∏ i ∈ range (n + 1), (X - C (a + ↑i * d))
    ∃ b : ℕ → ℝ,
      (∀ i j, i < n → j < n → i < j → b i < b j) ∧
      (∀ j, j < n → (derivative f).IsRoot (b j)) ∧
      (∀ x : ℝ, (derivative f).IsRoot x → ∃ j, j < n ∧ b j = x) ∧
      ∀ j, j < n → a < b j ∧ b j < a + ↑n * d :=
  sorry

end Erdos1114
