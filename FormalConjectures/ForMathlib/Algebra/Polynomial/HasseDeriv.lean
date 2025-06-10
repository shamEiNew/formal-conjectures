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

import Mathlib.Algebra.Polynomial.HasseDeriv

open scoped Polynomial in -- probably removable in the mathlib file
theorem Polynomial.hasseDeriv_map {R S : Type*} [Semiring R] [Semiring S]
    {f : R →+* S} {k : ℕ} {p : R[X]} : (p.map f).hasseDeriv k = (p.hasseDeriv k).map f := by
  ext; simp [hasseDeriv_coeff]
