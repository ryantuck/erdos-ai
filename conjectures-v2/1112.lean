import Mathlib.Data.Set.Function
import Mathlib.Order.Monotone.Basic

/-!
# Erdős Problem #1112

Source: https://www.erdosproblems.com/1112 (page last edited 28 December 2025;
archived capture accessed 2026-02-23).

Verbatim statement: "Let $1\leq d_1<d_2$ and $k\geq 3$. Does there exist an
integer $r$ such that if $B=\{b_1<\cdots\}$ is a lacunary sequence of positive
integers with $b_{i+1}\geq rb_i$ then there exists a sequence of positive
integers $A=\{a_1<\cdots\}$ such that $d_1\leq a_{i+1}-a_i\leq d_2$ for all
$i\geq 1$ and $(kA)\cap B=\emptyset$, where $kA$ is the $k$-fold sumset?"

Status: OPEN (banner tooltip: "This is open, and cannot be resolved with a
finite computation"). Tags: additive combinatorics. Attribution: [ErGr80, p.18].
The page itself cautions: "the stated problem is a generous interpretation of a
very ambiguous remark in [ErGr80], so it might be more appropriate to call this
a problem 'inspired by Erdős and Graham'."

Remarks from the page:

* Erdős and Graham [ErGr80] noted that if $B=\{b_1<b_2<\cdots\}$ with
  $b_1\geq 5$ and $b_{i+1}\geq 2b_i$ then there is a set $A=\{a_1<a_2<\cdots\}$
  with $2\leq a_{k+1}-a_k\leq 3$ for all $k$ such that $(A+A)\cap B=\emptyset$.
* Bollobás, Hegyvári, and Jin [BHJ97] showed such an $A$ must exist if
  $b_{i+1}\geq 2b_i-O(1)$, and that this is best possible. They also gave a
  negative answer for three summands: for any sequence of integers
  $1\leq r_1<r_2<\cdots$, there is a $B$ as above with $b_{i+1}\geq r_ib_i$
  such that $(A+A+A)\cap B\neq\emptyset$ for any $A$ with
  $2\leq a_{i+1}-a_i\leq 3$.
* [BHJ97] define, more generally, $r_k(d_1,d_2)$ as the smallest $r$ (if it
  exists) such that if $b_{i+1}\geq rb_i$ then there exists $A$ with
  $d_1\leq a_{i+1}-a_i\leq d_2$ such that $(kA)\cap B=\emptyset$. It follows
  from the above results ([ErGr80] + [BHJ97]) that $r_2(2,3)=2$ and that
  $r_3(2,3)$ does not exist. Chen [Ch00] proved $r_2(a,b)\leq 2$ for any
  integers $a<b$ with $b\neq 2a$, and $r_2(a,2a)\geq 2$ for all integers $a$.
  "The more general question of existence of $r_k(a,b)$ for $k\geq 3$ remains
  open." Some further technical non-existence results are given by Tang and
  Yang [TaYa21].

Encoding note. The source is a parameterized yes/no question. Its literal
universal reading — "for all $1\leq d_1<d_2$ and $k\geq 3$ there exists such an
$r$" — is *refuted* by [BHJ97] ($r_3(2,3)$ does not exist), so a formalization
asserting that direction, or presenting it behind an open-answer wrapper, would
be wrong; a styled question form would need to be per-parameter
(`answer(sorry) ↔ …` for fixed $d_1,d_2,k$). Following this corpus's raw-file
convention for open questions, the main theorem below is a direct assertion of
the only uniform direction consistent with all known results (every known
$k\geq 3$ result is a non-existence result): $r_k(d_1,d_2)$ exists for *no*
admissible parameters. This is an interpretive strengthening, not the question
itself: if $r_k(d_1,d_2)$ turns out to exist for some parameters, the statement
below is false while those instances of the problem are solved affirmatively.
Its $(d_1,d_2,k)=(2,3,3)$ instance is Bollobás–Hegyvári–Jin's theorem (see the
variants); all other instances are open.

References (authors, titles, journals, years, and pages recovered from the
site's `/latex/1112` bibliography via the session logs; volume numbers were not
in the recovered data and are omitted rather than invented):

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
combinatorial number theory_. Monographies de L'Enseignement Mathématique
(1980). Cited at p. 18.

[BHJ97] Bollobás, B., Hegyvári, N. and Jin, G., _On a problem of Erdős and
Graham_. Discrete Mathematics (1997), 253–257.

[Ch00] Chen, Y.-G., _On sums and intersects of sequences_. Discrete Mathematics
(2000), 351–354.

[TaYa21] Tang, M. and Yang, Q.-H., _On a problem of Erdős and Graham_.
Publicationes Mathematicae Debrecen (2021), 485–493.

Additional thanks to: Alfaiz. Formalised statement in external databases: No
(as of the archived capture).
-/

namespace Erdos1112

/-- The k-fold sumset of a set S of natural numbers: all sums s₁ + ⋯ + sₖ
    with each sᵢ ∈ S (repetitions allowed). Defined recursively: 0S = {0},
    (k+1)S = {a + b | a ∈ S, b ∈ kS}; in particular 1S = S, 2S = S + S.
    (Mathlib's pointwise `Set` algebra provides an equivalent iterated sumset
    as the `AddMonoid (Set ℕ)` scalar action `k • S`; the local definition is
    kept to avoid the pointwise-vs-`nsmul` scalar-action ambiguity for ℕ
    scalars, and because this file must stay plain Mathlib and compile-safe.) -/
def kFoldSumset : ℕ → Set ℕ → Set ℕ
  | 0, _ => {0}
  | k + 1, S => {n | ∃ a ∈ S, ∃ b ∈ kFoldSumset k S, n = a + b}

/--
Erdős Problem #1112 (OPEN) — [ErGr80, p.18]:

The source asks: for $1 \leq d_1 < d_2$ and $k \geq 3$, does there exist an
integer $r$ such that for every lacunary sequence $B = \{b_1 < b_2 < \cdots\}$
of positive integers with $b_{i+1} \geq r\,b_i$ there is a sequence
$A = \{a_1 < a_2 < \cdots\}$ of positive integers with
$d_1 \leq a_{i+1} - a_i \leq d_2$ for all $i$ and $(kA) \cap B = \emptyset$?
Equivalently (with $r_k(d_1,d_2)$ the smallest such $r$, as defined by
Bollobás–Hegyvári–Jin [BHJ97]): does $r_k(d_1,d_2)$ exist?

Known results (from the problem page):
- $r_2(2,3) = 2$, which follows from Erdős–Graham [ErGr80] together with
  Bollobás–Hegyvári–Jin [BHJ97]; Chen [Ch00] proved $r_2(a,b) \leq 2$ for all
  integers $a < b$ with $b \neq 2a$, and $r_2(a,2a) \geq 2$.
- $r_3(2,3)$ does not exist [BHJ97]: for any (even arbitrarily fast growing)
  sequence of lacunary ratios there is a $B$ such that
  $(A+A+A) \cap B \neq \emptyset$ for every $A$ with gaps in $[2,3]$.
- Further technical non-existence results by Tang and Yang [TaYa21].
- "The more general question of existence of $r_k(a,b)$ for $k \geq 3$ remains
  open."

This theorem states the non-existence direction uniformly — for all $k \geq 3$
and admissible $d_1 < d_2$, $r_k(d_1,d_2)$ does not exist: for every candidate
ratio $r$ there is a lacunary sequence $B$ with ratio $r$ such that no
gap-bounded sequence $A$ avoids $B$ with its $k$-fold sumset. This is the only
uniform direction consistent with all known results (the universal existence
reading is refuted by $r_3(2,3)$); see the module docstring for the
interpretive caveats. The instance $(d_1,d_2,k) = (2,3,3)$ is proved in
[BHJ97] (it follows from `variants.bhj_r3_2_3_nonexistence` below by taking
$\rho_i = \max(r,1) + i$); all other instances are open.
-/
theorem erdos_problem_1112 (d₁ d₂ : ℕ) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂)
    (k : ℕ) (hk : 3 ≤ k) (r : ℕ) :
    ∃ (B : ℕ → ℕ), StrictMono B ∧ (∀ i, 0 < B i) ∧
      (∀ i, r * B i ≤ B (i + 1)) ∧
      ∀ (A : ℕ → ℕ), StrictMono A → (∀ i, 0 < A i) →
        (∀ i, d₁ ≤ A (i + 1) - A i) →
        (∀ i, A (i + 1) - A i ≤ d₂) →
        ∃ n, n ∈ kFoldSumset k (Set.range A) ∧ n ∈ Set.range B :=
  sorry

/--
Erdős–Graham [ErGr80] (page-confirmed, SOLVED): if $B = \{b_1 < b_2 < \cdots\}$
with $b_1 \geq 5$ and $b_{i+1} \geq 2b_i$, then there is a set
$A = \{a_1 < a_2 < \cdots\}$ with $2 \leq a_{k+1} - a_k \leq 3$ for all $k$
such that $(A+A) \cap B = \emptyset$. (The positivity hypothesis on $B$ is
implied by $5 \leq b_1$ and strict monotonicity; it is kept for uniformity
with the other statements in this file.)

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1112.variants.erdos_graham_two_summands (B : ℕ → ℕ)
    (hB : StrictMono B) (hBpos : ∀ i, 0 < B i) (hB₁ : 5 ≤ B 0)
    (hBlac : ∀ i, 2 * B i ≤ B (i + 1)) :
    ∃ (A : ℕ → ℕ), StrictMono A ∧ (∀ i, 0 < A i) ∧
      (∀ i, 2 ≤ A (i + 1) - A i) ∧
      (∀ i, A (i + 1) - A i ≤ 3) ∧
      ∀ n, n ∈ kFoldSumset 2 (Set.range A) → n ∉ Set.range B :=
  sorry

/--
Bollobás–Hegyvári–Jin [BHJ97] (page-confirmed, SOLVED): such an $A$ (gaps in
$[2,3]$, $(A+A) \cap B = \emptyset$) must exist whenever
$b_{i+1} \geq 2b_i - O(1)$, and this is best possible. Encoded with an
explicit constant $C$ and the subtraction-free inequality
$2b_i \leq b_{i+1} + C$ (which is $b_{i+1} \geq 2b_i - C$ without ℕ-truncation
issues). The instance $C = 0$ is exactly $r_2(2,3) \leq 2$; the page's
complementary claim $r_2(2,3) \geq 2$ is trivial in the integer-ratio reading
(the ratio-1 growth condition admits $B = $ all positive integers, which every
2-fold sumset meets), so $r_2(2,3) = 2$ carries no formal content beyond this
statement. The "best possible" half (the $O(1)$ slack cannot be weakened) is
recorded in prose only, since its precise quantitative form is not given on
the page.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1112.variants.bhj_two_summands (C : ℕ) (B : ℕ → ℕ)
    (hB : StrictMono B) (hBpos : ∀ i, 0 < B i)
    (hBlac : ∀ i, 2 * B i ≤ B (i + 1) + C) :
    ∃ (A : ℕ → ℕ), StrictMono A ∧ (∀ i, 0 < A i) ∧
      (∀ i, 2 ≤ A (i + 1) - A i) ∧
      (∀ i, A (i + 1) - A i ≤ 3) ∧
      ∀ n, n ∈ kFoldSumset 2 (Set.range A) → n ∉ Set.range B :=
  sorry

/--
Bollobás–Hegyvári–Jin [BHJ97] (page-confirmed, SOLVED): for any sequence of
integers $1 \leq r_1 < r_2 < \cdots$, there is a lacunary sequence
$B = \{b_1 < b_2 < \cdots\}$ of positive integers with $b_{i+1} \geq r_i b_i$
such that $(A+A+A) \cap B \neq \emptyset$ for every $A$ with
$2 \leq a_{i+1} - a_i \leq 3$. In particular $r_3(2,3)$ does not exist: the
$(d_1,d_2,k) = (2,3,3)$ instance of `erdos_problem_1112` follows by applying
this with $\rho_i = \max(r,1) + i$.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1112.variants.bhj_r3_2_3_nonexistence (ρ : ℕ → ℕ)
    (hρ₁ : 1 ≤ ρ 0) (hρ : StrictMono ρ) :
    ∃ (B : ℕ → ℕ), StrictMono B ∧ (∀ i, 0 < B i) ∧
      (∀ i, ρ i * B i ≤ B (i + 1)) ∧
      ∀ (A : ℕ → ℕ), StrictMono A → (∀ i, 0 < A i) →
        (∀ i, 2 ≤ A (i + 1) - A i) →
        (∀ i, A (i + 1) - A i ≤ 3) →
        ∃ n, n ∈ kFoldSumset 3 (Set.range A) ∧ n ∈ Set.range B :=
  sorry

/--
Chen [Ch00] (page-confirmed, SOLVED): $r_2(a,b) \leq 2$ for any integers
$a < b$ with $b \neq 2a$ — every lacunary $B$ with $b_{i+1} \geq 2b_i$ is
avoided by the 2-fold sumset of some $A$ with gaps in $[a,b]$. The hypothesis
$1 \leq a$ makes the gap window admissible per the problem's convention
$1 \leq d_1$. Chen's companion result $r_2(a,2a) \geq 2$ is not formalized:
in the integer-ratio reading it is trivially true (ratio 1 admits
$B = $ all positive integers, met by every 2-fold sumset), and its substantive
content requires a finer-than-integer ratio scale not present in this file's
definitions.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1112.variants.chen_r2_upper (a b : ℕ) (ha : 1 ≤ a)
    (hab : a < b) (hne : b ≠ 2 * a) (B : ℕ → ℕ)
    (hB : StrictMono B) (hBpos : ∀ i, 0 < B i)
    (hBlac : ∀ i, 2 * B i ≤ B (i + 1)) :
    ∃ (A : ℕ → ℕ), StrictMono A ∧ (∀ i, 0 < A i) ∧
      (∀ i, a ≤ A (i + 1) - A i) ∧
      (∀ i, A (i + 1) - A i ≤ b) ∧
      ∀ n, n ∈ kFoldSumset 2 (Set.range A) → n ∉ Set.range B :=
  sorry

end Erdos1112
