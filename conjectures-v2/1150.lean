import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem #1150

Does there exist a constant c > 0 such that, for all large n and all
polynomials P of degree n with coefficients ±1,
max_{|z|=1} |P(z)| > (1+c)√n?

Verbatim source statement (erdosproblems.com/1150): "Does there exist a
constant $c>0$ such that, for all large $n$ and all polynomials $P$ of
degree $n$ with coefficients $\pm 1$,
\[\max_{\lvert z\rvert=1}\lvert P(z)\rvert > (1+c)\sqrt{n}?\]"

Status: OPEN per erdosproblems.com/1150 (page last edited 23 January 2026,
accessed 2026-03-09) — "This is open, and cannot be resolved with a finite
computation."

Remarks from the source page:
* "In other words, does there exist an 'ultraflat' polynomial with
  coefficients $\pm 1$. The answer is yes if the coefficients can take any
  values on the unit circle (see [230])." (Note on polarity: the two
  phrasings point in opposite directions — a "yes" to the displayed
  question, i.e. the existence of c, means that ultraflat ±1 polynomials do
  NOT exist. The unimodular-coefficient case [230] is Kahane's ultraflat
  construction, formalized in this corpus as `erdos_problem_230`.)
* "The lower bound \[\max_{\lvert z\rvert=1}\lvert P(z)\rvert \geq
  \sqrt{n}\] is trivial from Parseval's theorem." (Formalized below as
  `erdos_problem_1150.variants.parseval_lower_bound`; Parseval in fact
  gives the slightly sharper √(n+1), since a degree-n ±1 polynomial has
  n+1 unimodular coefficients.)
* "A weaker 'flatness' question is the subject of [228]." (Littlewood's
  two-sided flatness conjecture, solved by Balister–Bollobás–Morris–
  Sahasrabudhe–Tiba; formalized in this corpus as `erdos_problem_228`,
  which shares this file's `IsLittlewoodCoeff`/`evalLittlewood` helpers.)

The source poses this as a yes/no question and the problem is OPEN; this raw
corpus has no `answer()` elaborator (Mathlib-only imports), and its uniform
convention for open yes/no questions is a direct assertion of the asked
("yes") direction with a `sorry` proof, as here. In styled question form it
would be `answer(sorry) ↔ ∃ c > 0, …` (the upstream formal-conjectures file
for this problem, recovered from the session logs, uses exactly that shape
over the same proposition).

Computational cross-check (performed during the second-pass review; context,
not formal content): for every degree n ≤ 10, the minimum over all 2^n
sign patterns (leading symmetry fixed) of max_{|z|=1} |P(z)|, sampled at
2048 roots of unity, stays above 1.14·√(n+1) — consistent with the
conjectured existence of c > 0 and with the non-vacuity of the statement.

Tags (per the page): analysis, polynomials.
Formalised statement (per the page, as of access): Yes —
google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/1150.lean.
The page records 4 forum comments; their contents were not captured.
No related OEIS sequences are listed on the page.

References (honest stubs; no `/latex/1150` or `/bibs/` fetch was captured in
the session logs, so entries carry only corpus-corroborated data — nothing
fabricated):

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_
  (1974), 155–180, Problem 4.31. (Identity of this key corroborated by the
  log-captured `/latex/1118` bibliography and by upstream formal-conjectures
  files for the sibling polynomial problems 225, 226, 229, 230, 485, 511,
  973, which all expand [Ha74] to this Hayman collection.)

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §2.36. (Corpus-canonical identity of this key, settled by sibling reviews
  1068 and 1131–1148 against upstream formal-conjectures; sibling styled
  files sometimes glossed [Va99] with invented single authors — none of
  that is reproduced here.)

[228], [230] in the remarks are erdosproblems.com problem numbers
(cross-references), not citation keys.
-/

open BigOperators Finset

noncomputable section

/--
A Littlewood polynomial of degree n is a polynomial with all coefficients in {-1, +1}.
We represent it as a function ε : Fin (n + 1) → ℤ with each ε i ∈ {-1, 1}, and its
evaluation at z ∈ ℂ is ∑ i, ε i * z ^ (i : ℕ).
-/
def IsLittlewoodCoeff (n : ℕ) (ε : Fin (n + 1) → ℤ) : Prop :=
  ∀ i, ε i = -1 ∨ ε i = 1

/-- The evaluation at z ∈ ℂ of the Littlewood polynomial with coefficient
sequence ε : Fin (n + 1) → ℤ, namely ∑_{i=0}^{n} ε i · z^i. -/
def evalLittlewood (n : ℕ) (ε : Fin (n + 1) → ℤ) (z : ℂ) : ℂ :=
  ∑ i : Fin (n + 1), (ε i : ℂ) * z ^ (i : ℕ)

/--
Erdős Problem #1150 [Ha74,4.31] [Va99,2.36] (Open):

Does there exist a constant c > 0 such that, for all large n and all polynomials P
of degree n with coefficients ±1,
  max_{|z|=1} |P(z)| > (1+c)√n?

In other words (per the source page), does there exist an 'ultraflat' polynomial
with coefficients ±1 — note the flip of polarity: this theorem asserts the "yes"
direction of the displayed question, i.e. that the constant c exists, which is
precisely the statement that ultraflat ±1 polynomials do NOT exist.
The lower bound max_{|z|=1} |P(z)| ≥ √n is trivial from Parseval's theorem
(see `erdos_problem_1150.variants.parseval_lower_bound`).
The answer is yes (ultraflat unimodular polynomials exist) if the coefficients can
take any values on the unit circle (see [230]), but this problem asks specifically
about ±1 coefficients. A weaker 'flatness' question is the subject of [228].

Since the maximum of ‖P‖ over the compact unit circle is attained, "max > b" is
encoded equivalently as "∃ z on the circle with ‖P(z)‖ > b".

Tags: analysis, polynomials
-/
theorem erdos_problem_1150 :
    ∃ c : ℝ, 0 < c ∧
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∀ ε : Fin (n + 1) → ℤ,
          IsLittlewoodCoeff n ε →
          ∃ z : ℂ, ‖z‖ = 1 ∧
            (1 + c) * Real.sqrt n < ‖evalLittlewood n ε z‖ :=
  sorry

/--
The page's remark: "The lower bound max_{|z|=1} |P(z)| ≥ √n is trivial from
Parseval's theorem." Stated as the page states it, with the witness form
justified by compactness (the maximum is attained, so max ≥ b gives a point
with ‖P(z)‖ ≥ b). Parseval in fact gives the sharper bound √(n+1) — the mean
square of ‖P‖ on the circle is n+1 (n+1 coefficients of modulus 1) — which is
the form the upstream formal-conjectures file states; the page's √n follows
a fortiori and holds for every n and every ±1 coefficient sequence.
-/
theorem erdos_problem_1150.variants.parseval_lower_bound
    (n : ℕ) (ε : Fin (n + 1) → ℤ) (hε : IsLittlewoodCoeff n ε) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ Real.sqrt n ≤ ‖evalLittlewood n ε z‖ :=
  sorry

end
