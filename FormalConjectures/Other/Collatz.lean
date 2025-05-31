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
# The Collatz Conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Collatz_conjecture)
-/

open Function

/-- The next number in the Collatz sequence -/
def nextCollatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then
    n / 2
  else
    3 * n + 1

/-- The Collatz sequence starting from a given number -/
def collatzSeq (start : ℕ) : List ℕ :=
  let rec loop (n : ℕ) (acc : List ℕ) (fuel : ℕ) : List ℕ :=
    match fuel with
    | 0 => acc.reverse
    | fuel + 1 =>
      if n = 1 then
        (1 :: acc).reverse
      else
        loop (nextCollatz n) (n :: acc) fuel
  loop start [] 1000  -- Using 1000 as a reasonable bound for demonstration

/-- Predicate stating that a number eventually reaches 1 in the Collatz sequence -/
def reachesOne (n : ℕ) : Prop :=
  ∃ k : ℕ, nextCollatz^[k] n = 1

/-- The Collatz conjecture: every positive natural number eventually reaches 1 -/
@[category research open, AMS 11]
theorem collatz_conjecture : ∀ n : ℕ, n > 0 → reachesOne n := by
  sorry
