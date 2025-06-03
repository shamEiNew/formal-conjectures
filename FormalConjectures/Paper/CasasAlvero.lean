/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Casas-Alvero Conjecture

*Reference:*
* [The Casas-Alvero conjecture for infinitely many degrees](https://arxiv.org/pdf/math/0605090)
* [MathOverflow](https://mathoverflow.net/questions/27851)

The Casas-Alvero conjecture states that if a univariate polynomial P of degree d over a field
of characteristic zero shares a root with each of its derivatives up to order d-1, then P must
be of the form (X - α)^d for some α.

The conjecture has been proven for:
* Degrees d ≤ 8
* Degrees of the form p^k where p is prime
* Degrees of the form 2p^k where p is prime

The conjecture is false in positive characteristic p for polynomials of degree d > p.
-/

open Polynomial

/--
A polynomial P satisfies the Casas-Alvero property if it shares a root with each
of its derivatives up to order d-1, where d is the degree of P.
-/
def HasCasasAlveroProp {R : Type} [Field R] (P : R[X]) : Prop :=
  ∀ i ∈ Finset.range P.natDegree, ∃ α : R, IsRoot P α ∧ IsRoot (derivative^[i] P) α

/--
The Casas-Alvero conjecture states that in characteristic zero, if a monic polynomial P
has the Casas-Alvero property, then P = (X - α)^d for some α.
-/
@[category research open, AMS 12]
theorem casas_alvero_conjecture {K : Type} [Field K] [CharZero K] (P : K[X]) (hP : Monic P) :
    HasCasasAlveroProp P → ∃ α : K, P = (X - C α) ^ P.natDegree := by
  sorry

/--
The Casas-Alvero conjecture holds for polynomials of prime power degree.
This was proved by Graf von Bothmer, Labs, Schicho, and van de Woestijne.

Reference: [The Casas-Alvero conjecture for infinitely many degrees](https://arxiv.org/pdf/math/0605090)
-/
@[category research solved, AMS 12]
theorem casas_alvero.prime_power {K : Type} [Field K] [CharZero K]
    (p k : ℕ) (hp : p.Prime) (P : K[X]) (hP : Monic P) (hd : P.natDegree = p^k) :
    HasCasasAlveroProp P → ∃ α : K, P = (X - C α) ^ P.natDegree := by
  sorry

/--
The Casas-Alvero conjecture holds for polynomials of degree 2p^k where p is prime.
This was proved by Graf von Bothmer, Labs, Schicho, and van de Woestijne.

Reference: [The Casas-Alvero conjecture for infinitely many degrees](https://arxiv.org/pdf/math/0605090)
-/
@[category research solved, AMS 12]
theorem casas_alvero.double_prime_power {K : Type} [Field K] [CharZero K]
    (p k : ℕ) (hp : p.Prime) (P : K[X]) (hP : Monic P) (hd : P.natDegree = 2 * p^k) :
    HasCasasAlveroProp P → ∃ α : K, P = (X - C α) ^ P.natDegree := by
  sorry

/--
The Casas-Alvero conjecture fails in positive characteristic p for polynomials of degree d > p.
This was shown by Graf von Bothmer, Labs, Schicho, and van de Woestijne.

Reference: [The Casas-Alvero conjecture for infinitely many degrees](https://arxiv.org/pdf/math/0605090)
-/
@[category research solved, AMS 12]
theorem casas_alvero.positive_char_counterexample {p : ℕ} (hp : p.Prime) :
    ∃ K : Type, ∃ (_ : Field K) (_ : CharP K p) (d : ℕ) (hd : d > p) (P : K[X]),
      Monic P ∧ P.natDegree = d ∧ HasCasasAlveroProp P ∧
      ¬∃ α : K, P = (X - C α) ^ P.natDegree := by
  sorry
