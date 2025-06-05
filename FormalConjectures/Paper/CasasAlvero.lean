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

The conjecture is now claimed to be proven in this paper:
* [The Casas-Alvero conjecture for infinitely many degrees](https://arxiv.org/pdf/2505.18000)

-/

open Polynomial

/--
A polynomial P satisfies the Casas-Alvero property if it shares a root with each
of its Hasse derivatives up to order d-1, where d is the degree of P.
-/
def HasCasasAlveroProp {K : Type} [Field K] (P : K[X]) : Prop :=
  ∀ i ∈ Finset.range P.natDegree, ∃ α : K, IsRoot P α ∧ IsRoot (hasseDeriv i P) α

/--
Alternative characterization of the Casas-Alvero property using non-coprimality with derivatives.
A polynomial has this property if it is not coprime with any of its Hasse derivatives up to
order d-1, where d is the degree of P.
-/
def HasCasasAlveroPropCoprime {K : Type} [Field K] (P : K[X]) : Prop :=
  ∀ i ∈ Finset.range P.natDegree, ¬ IsCoprime P (hasseDeriv i P)

/--
The two characterizations of the Casas-Alvero property are equivalent.
-/
@[category API, AMS 12]
lemma casas_alvero_iff_coprime {K : Type} [Field K] (P : K[X]) (hP : Monic P) :
  HasCasasAlveroProp P ↔ HasCasasAlveroPropCoprime P := by
  sorry

/--
The Casas-Alvero conjecture states that in characteristic zero, if a monic polynomial P
has the Casas-Alvero property, then P = (X - α)^d for some α.
-/
@[category research open, AMS 12]
theorem casas_alvero_conjecture {K : Type} [Field K] [CharZero K] (P : K[X]) (hP : Monic P) :
    HasCasasAlveroProp P → ∃ α : K, P = (X - C α) ^ P.natDegree := by
  sorry

/--
The Casas-Alvero conjecture (coprimality version) states that in characteristic zero,
if a monic polynomial P is not coprime with any of its Hasse derivatives up to order d-1,
then P = (X - α)^d for some α.
-/
@[category research open, AMS 12]
theorem casas_alvero_conjecture_coprime {K : Type} [Field K] [CharZero K] (P : K[X]) (hP : Monic P) :
    HasCasasAlveroPropCoprime P → ∃ α : K, P = (X - C α) ^ P.natDegree := by
  intro h
  apply casas_alvero_conjecture P hP
  exact (casas_alvero_iff_coprime P hP).mpr h

/--
The two versions of the Casas-Alvero conjecture are equivalent.
-/
lemma casas_alvero_conjecture_iff {K : Type} [Field K] [CharZero K] (P : K[X]) (hP : Monic P) :
    (HasCasasAlveroProp P → ∃ α : K, P = (X - C α) ^ P.natDegree) ↔
    (HasCasasAlveroPropCoprime P → ∃ α : K, P = (X - C α) ^ P.natDegree) := by
  constructor
  · intro h1 h2
    apply h1
    exact (casas_alvero_iff_coprime P hP).mpr h2
  · intro h1 h2
    apply h1
    exact (casas_alvero_iff_coprime P hP).mp h2

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
    ∃ K : Type, ∃ (_ : Field K) (_ : CharP K p) (P : K[X]) (hd : P.natDegree > p),
      Monic P ∧ HasCasasAlveroProp P ∧
      ¬∃ α : K, P = (X - C α) ^ P.natDegree := by
  sorry
