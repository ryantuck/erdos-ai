import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic

/-!
# Erdős Problem #1113

Source: https://www.erdosproblems.com/1113 (page last edited 29 December 2025;
archived capture accessed 2026-02-23).

Verbatim statement: "A positive odd integer $m$ such that none of $2^km+1$ are
prime for $k\geq 0$ is called a Sierpinski number. We say that a set of primes
$P$ is a covering set for $m$ if every $2^km+1$ is divisible by some $p\in P$.
Are there Sierpinski numbers with no finite covering set of primes?"

Status: OPEN (banner tooltip: "This is open, and cannot be resolved with a
finite computation"). Tags: number theory, covering systems.
Attribution: [ErGr80, p.27].

Remarks from the page:

* Sierpinski [Si60] proved that there are infinitely many Sierpinski numbers,
  using covering systems to construct suitable covering sets for any $m$
  satisfying a certain congruence. This establishes that there is a positive
  density set of such $m$. (Infinitude is formalized below; the
  positive-density strengthening is recorded in prose only, since stating it
  needs density machinery not present in this file.)
* The smallest Sierpinski number is believed to be $78557$, which was found by
  Selfridge.
* Erdős and Graham [ErGr80] asked whether there are Sierpinski numbers for
  which a covering system is not 'responsible', for which the best
  interpretation seems to be the above question. This is formulated precisely
  in problem F13 of Guy's collection [Gu04]. Erdős and Graham thought the
  answer is yes (in that there are such Sierpinski numbers), since otherwise
  this would imply there are infinitely many Fermat primes. (That implication
  is recorded in prose only: the page does not spell out the argument, so no
  formal statement of it is attempted here.)
* There is now further evidence with a concrete example: an argument of
  Izotov [Iz95], given in more detail by Filaseta, Finch, and Kozek [FFK08],
  suggests that $m = 734110615000775^4$ is a Sierpinski number without a
  covering set. (Izotov proved that this $m$ is indeed a Sierpinski number;
  the absence of a covering set is supported by the argument, not proved.)
* Filaseta, Finch, and Kozek [FFK08] give a revised conjecture, suggesting
  that every Sierpinski number is either a perfect power or else has a finite
  covering set of primes. They also prove that for every $l \geq 1$ there is
  an $m$ such that $2^k m^i + 1$ is composite for all $1 \leq i \leq l$ and
  $k \geq 0$.
* See also problems #203 and #276 (the latter is another problem in which the
  question is whether covering systems are always responsible).

Encoding note. The source poses a yes/no question and the problem is OPEN.
This raw-file corpus has no `answer()` elaborator (a formal-conjectures
construct), so, following the corpus convention for open yes/no questions, the
main theorem below is a direct assertion of the conjectured direction: Erdős
and Graham thought the answer is yes, and the statement asserts that such a
Sierpinski number exists. If the true answer is "no", the statement below is
false; what is open is the question itself.

References (authors, titles, journals, years, and pages recovered from the
site's `/latex/1113` bibliography via the session logs; volume numbers were
not in the recovered data and are omitted rather than invented):

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
combinatorial number theory_. Monographies de L'Enseignement Mathématique
(1980). Cited at p. 27.

[Si60] Sierpiński, W., _Sur un problème concernant les nombres
$k\cdot 2^n+1$_. Elem. Math. (1960), 73–74.

[Gu04] Guy, Richard K., _Unsolved problems in number theory_. (2004),
xviii+437.

[Iz95] Izotov, Anatoly S., _A note on Sierpinski numbers_. Fibonacci Quart.
(1995), 206–207.

[FFK08] Filaseta, Michael, Finch, Carrie and Kozek, Mark, _On powers
associated with Sierpinski numbers, Riesel numbers and Polignac's conjecture_.
J. Number Theory (2008), 1916–1940.

Related OEIS sequence: A076336. Additional thanks to: Dogmachine and Wouter
van Doorn. Formalised statement in external databases: No (as of the archived
capture).
-/

/-- A positive odd integer `m` is a Sierpinski number if `2^k * m + 1` is composite
    for all `k ≥ 0`. Since `1 ≤ m` forces `2 ^ k * m + 1 ≥ 2`, compositeness is
    faithfully rendered as `¬ Nat.Prime`, and the `k = 0` case (`m + 1` not prime)
    is included, exactly as in the source statement. (`0 < m` is formally redundant
    given `¬ 2 ∣ m` — since `2 ∣ 0` — but is kept for clarity.) -/
def IsSierpinskiNumber (m : ℕ) : Prop :=
  0 < m ∧ ¬ 2 ∣ m ∧ ∀ k : ℕ, ¬ Nat.Prime (2 ^ k * m + 1)

/-- A finite set of primes `P` is a covering set for `m` if every `2^k * m + 1` is
    divisible by some prime in `P`. The empty set is never a covering set: the
    divisibility condition fails at every `k`. -/
def HasFiniteCoveringSet (m : ℕ) (P : Finset ℕ) : Prop :=
  (∀ p ∈ P, Nat.Prime p) ∧ ∀ k : ℕ, ∃ p ∈ P, p ∣ (2 ^ k * m + 1)

/--
Erdős Problem #1113 (OPEN) — [ErGr80, p.27]:
A positive odd integer m such that none of 2^k * m + 1 are prime for k ≥ 0 is called a
Sierpinski number. A set of primes P is a covering set for m if every 2^k * m + 1 is
divisible by some p ∈ P.

The source asks: are there Sierpinski numbers with no finite covering set of primes?

Erdős and Graham thought the answer is yes, since otherwise this would imply there are
infinitely many Fermat primes; this theorem asserts their conjectured direction (see
the module docstring's encoding note). An argument of Izotov [Iz95], given in more
detail by Filaseta, Finch, and Kozek [FFK08], suggests that m = 734110615000775^4 is
such a Sierpinski number without a covering set (Izotov proved that this m is indeed a
Sierpinski number; the absence of a covering set is supported, not proved).
-/
theorem erdos_problem_1113 :
    ∃ m : ℕ, IsSierpinskiNumber m ∧ ∀ P : Finset ℕ, ¬ HasFiniteCoveringSet m P :=
  sorry

/--
Sierpinski [Si60] (page-confirmed, SOLVED): there are infinitely many Sierpinski
numbers, constructed via covering systems (which supply a finite covering set for any
`m` satisfying a certain congruence; a covering system covers every residue, in
particular `k = 0`, so the construction meets the `k ≥ 0` convention used here).
Infinitude is encoded arithmetically — arbitrarily large witnesses — to avoid imports
not already in this file. The page's positive-density strengthening is recorded in
prose only (module docstring).

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1113.variants.si60_infinitely_many :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsSierpinskiNumber m :=
  sorry

/--
Selfridge (page-confirmed, SOLVED): 78557 is a Sierpinski number. Per the page, "the
smallest Sierpinski number is believed to be $78557$, which was found by Selfridge."
The extra `k = 0` requirement of the `k ≥ 0` convention holds trivially here:
`78558 = 2 * 3 * 13093` is composite.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1113.variants.selfridge : IsSierpinskiNumber 78557 :=
  sorry

/--
(page-confirmed, OPEN): 78557 is believed to be the *smallest* Sierpinski number.
Note that the `k ≥ 0` convention used in this file is more restrictive than the
classical `k ≥ 1` one, so this statement is implied by the classical belief (fewer
`m` qualify, and 78557 still does).

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1113.variants.selfridge_smallest :
    ∀ m : ℕ, IsSierpinskiNumber m → 78557 ≤ m :=
  sorry

/--
Izotov [Iz95] (page-confirmed, SOLVED): $m = 734110615000775^4$ is a Sierpinski
number ("Izotov proved that this $m$ is indeed a Sierpinski number"). The `k = 0`
case is trivial: the base is odd, so `m` is odd and `m + 1` is even and greater
than 2, hence composite.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1113.variants.izotov_sierpinski :
    IsSierpinskiNumber (734110615000775 ^ 4) :=
  sorry

/--
(page-confirmed, OPEN — conjectural): the Izotov example has *no* finite covering set
of primes. Per the page this is "suggested" by Izotov's argument as given in more
detail by Filaseta, Finch, and Kozek [FFK08] — supported by evidence, not proved.
Together with `erdos_problem_1113.variants.izotov_sierpinski` this would resolve
`erdos_problem_1113` affirmatively.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1113.variants.izotov_no_covering_set :
    ∀ P : Finset ℕ, ¬ HasFiniteCoveringSet (734110615000775 ^ 4) P :=
  sorry

/--
Filaseta–Finch–Kozek [FFK08] revised conjecture (page-confirmed, OPEN): every
Sierpinski number is either a perfect power or else has a finite covering set of
primes. (This predicts that Sierpinski numbers without covering sets exist only among
perfect powers, consistent with the Izotov example being a fourth power.)

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1113.variants.ffk_perfect_power_conjecture :
    ∀ m : ℕ, IsSierpinskiNumber m →
      (∃ b k : ℕ, 1 < k ∧ m = b ^ k) ∨ (∃ P : Finset ℕ, HasFiniteCoveringSet m P) :=
  sorry

/--
Filaseta–Finch–Kozek [FFK08] (page-confirmed, SOLVED): for every $l \geq 1$ there is
an $m$ such that $2^k m^i + 1$ is composite for all $1 \leq i \leq l$ and $k \geq 0$.
Encoded as: each power $m^i$ with $1 \leq i \leq l$ is itself a Sierpinski number.
The oddness/positivity packaged in `IsSierpinskiNumber` is the intended reading and is
essential: without it the page's literal compositeness condition would be vacuously
witnessed by $m = 0$, since $2^k \cdot 0^i + 1 = 1$ is neither prime nor composite.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1113.variants.ffk_powers :
    ∀ l : ℕ, 1 ≤ l → ∃ m : ℕ, ∀ i : ℕ, 1 ≤ i → i ≤ l → IsSierpinskiNumber (m ^ i) :=
  sorry
