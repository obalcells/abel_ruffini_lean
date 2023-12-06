import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.Adjoin
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Field.InjSurj
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Subfield
import Mathlib.FieldTheory.Tower
import Mathlib.FieldTheory.IntermediateField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.RingTheory.TensorProduct

open Polynomial
open IntermediateField


theorem nth_sqrt_is_splitting_field
  [Field L]
  (K : Subfield L)
  (h : K = CyclotomicField n ℝ)
  (a : K)
  (f : K[X])
  (hf : f = (X ^ (n : ℕ) - C a : K[X]))
  : f.SplittingField = adjoin K { b : L | b ^ (n : ℕ) = a } := by {
    sorry
}


theorem field_equal_field
  [Field L]
  (K : Subfield L)
  (S : Set L)
  (E : Set L)
  : (∀ x, x ∈ adjoin K S ↔ x ∈ adjoin K E) ↔
    adjoin K S = adjoin K E := by {
constructor
· apply IntermediateField.ext -- theorem IntermediateField.ext; Two intermediate fields are equal if they have the same elements
· intro h
  rw [h]
  intro x
  rfl
}


theorem generators_equal_fields_equal
  [Field L]
  (K : Subfield L)
  [Algebra K L]
  (S : Set L)
  (E : Set L)
  : (∀ x, x ∈ S → x ∈ adjoin K E) ∧ (∀ x, x ∈ E → x ∈ adjoin K S) ↔
    adjoin K S = adjoin K E := by {
constructor
· intro k
  apply IntermediateField.ext
  intro X
  let d : S ≤ adjoin K E := by {
    apply k.1
  }
/-
  let e : IntermediateField.adjoin K E ≤ L := by { -- use theorem IntermediateField.adjoin_le_subfield ; If K is a field with F ⊆ K and S ⊆ K then adjoin F S ≤ K
      apply IntermediateField.adjoin_le_subfield
  }
-/
  let f : adjoin K S ≤ adjoin K E := by { -- use theorem adjoin_le_iff {S : Set E} {T : IntermediateField F E} : adjoin F S ≤ T ↔ S ≤ T
    --apply adjoin_le_iff
    sorry
  }
  let c : X ∈ adjoin K S → X ∈ adjoin K E := by {
    apply f
  }
  let f' : adjoin K E ≤ adjoin K S := by {
    sorry
  }
  let c' : X ∈ adjoin K E → X ∈ adjoin K S := by {
    apply f'
  }
  constructor
  exact c
  exact c'

· intro h
  let a : ∀ x, x ∈ S → x ∈ adjoin K E := by {
    intro y
    rw [← h]
    apply subset_adjoin
  }
  let b : ∀ x, x ∈ E → x ∈ adjoin K S := by {
    intro z
    rw [h]
    apply subset_adjoin
  }
  apply And.intro a b
}
