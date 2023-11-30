import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.Adjoin

open Polynomial

variable [Field F] [Field K] [Field K]
-- /- ℝ ⊂ K ⊂ L -/
-- variable [f : K[X]]

theorem nth_sqrt_is_splitting_field
  [Field K]
  [Field L]
  (n : ℕ+)
  (h : K = CyclotomicField n ℝ)
  (K : Subfield L)
  (a : K)
  (f : K[X])
  (hf : f = (X ^ (n : ℕ) - C a : K[X]))
  : f.SplittingField = (IntermediateField.adjoin K { b : L | b ^ (n : ℕ) = (a : L) }) := by {
  sorry
}
