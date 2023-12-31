/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.EisensteinCriterion
import Mathlib.Algebra.MonoidAlgebra.Basic

-- set_option profiler true
-- set_option synthInstance.maxHeartbeats 140000 -- default is 20000; five times that not enough here
-- set_option trace.Meta.synthInstance true

/-!
# Construction of an algebraic number that is not solvable by radicals.

The main ingredients are:
 * `solvableByRad.isSolvable'` in `Mathlib/FieldTheory/AbelRuffini.lean` :
  an irreducible polynomial with an `IsSolvableByRad` root has solvable Galois group
 * `galActionHom_bijective_of_prime_degree'` in `Mathlib/FieldTheory/PolynomialGaloisGroup.lean` :
  an irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group
 * `Equiv.Perm.not_solvable` in `Mathlib/GroupTheory/Solvable.lean` : the symmetric group is not
  solvable

Then all that remains is the construction of a specific polynomial satisfying the conditions of
`galActionHom_bijective_of_prime_degree'`, which is done in this file.

-/


namespace AbelRuffini

open Function Polynomial Polynomial.Gal Ideal
open scoped Polynomial
open AddMonoidAlgebra

attribute [local instance] splits_ℚ_ℂ

variable (R : Type*) [CommRing R] [Nontrivial R] (a b : ℕ)

noncomputable def Φ : R[X] := X ^ 5 - 4 * X + 2

variable {R}
variable (n : ℕ+)

theorem map_Phi
  {S : Type*}
  [CommRing S]
  (f : R →+* S)
  : (Φ R).map f = Φ S := by
  simp [Φ]

theorem coeff_zero_Phi
  : (Φ R).coeff 0 = 2 := by
  rw [Φ]
  simp

theorem coeff_five_Phi
  : (Φ R).coeff 5 = 1 := by
  rw [Φ]
  simp
  rw [← pow_one X]
  rw [coeff_X_pow]
  simp

theorem degree_Phi_eq_5
  [Nontrivial R]
  : (Φ R).degree = (5 : ℕ) := by
  rw [Φ]
  compute_degree
  simp

theorem nat_degree_Phi_eq_5
  [Nontrivial R]
  : natDegree (Φ R) = 5 := by
  apply natDegree_eq_of_degree_eq_some degree_Phi_eq_5


variable [Nontrivial R]

theorem leading_coeff_Phi_eq_one
  : (Φ R).leadingCoeff = 1 := by
  rw [Polynomial.leadingCoeff]
  rw [nat_degree_Phi_eq_5]
  apply coeff_five_Phi

theorem is_monic_Phi
  : (Φ R).Monic := by
  unfold Monic
  rw [Polynomial.leadingCoeff]
  apply leading_coeff_Phi_eq_one

theorem is_irreducible_Phi
  : Irreducible (Φ ℚ) := by
  sorry
  --unfold



-- theorem irreducible_Phi (p : ℕ) (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) :
--     Irreducible (Φ ℚ a b) := by
--   rw [← map_Phi a b (Int.castRingHom ℚ), ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
--   apply irreducible_of_eisenstein_criterion
--   · rwa [span_singleton_prime (Int.coe_nat_ne_zero.mpr hp.ne_zero), Int.prime_iff_natAbs_prime]
--   · rw [leadingCoeff_Phi, mem_span_singleton]
--     exact mod_cast mt Nat.dvd_one.mp hp.ne_one
--   · intro n hn
--     rw [mem_span_singleton]
--     rw [degree_Phi] at hn; norm_cast at hn
--     interval_cases hn : n <;>
--     simp (config := {decide := true}) only [Φ, coeff_X_pow, coeff_C, Int.coe_nat_dvd.mpr, hpb,
--       if_true, coeff_C_mul, if_false, coeff_X_zero, hpa, coeff_add, zero_add, mul_zero, coeff_sub,
--       add_zero, zero_sub, dvd_neg, neg_zero, dvd_mul_of_dvd_left]
--   · simp only [degree_Phi, ← WithBot.coe_zero, WithBot.coe_lt_coe, Nat.succ_pos']
--     decide
--   · rw [coeff_zero_Phi, span_singleton_pow, mem_span_singleton]
--     exact mt Int.coe_nat_dvd.mp hp2b
--   all_goals exact Monic.isPrimitive (monic_Phi a b)
-- #align abel_ruffini.irreducible_Phi AbelRuffini.irreducible_Phi


theorem real_roots_Phi_le : Fintype.card ((Φ ℚ).rootSet ℝ) ≤ 3 := by
   rw [← map_Phi (algebraMap ℤ ℚ)]
   rw [Φ]
   refine' (card_rootSet_le_derivative _).trans
     (Nat.succ_le_succ ((card_rootSet_le_derivative _).trans (Nat.succ_le_succ _)))
   suffices : (Polynomial.rootSet (C (20 : ℚ) * X ^ 3) ℝ).Subsingleton
   · norm_num [Fintype.card_le_one_iff_subsingleton]
     norm_num [← mul_assoc]
     exact this
   rw [rootSet_C_mul_X_pow]
   norm_num
   norm_num
   norm_num


-- theorem real_roots_Phi_le : Fintype.card ((Φ ℚ a b).rootSet ℝ) ≤ 3 := by
--   rw [← map_Phi a b (algebraMap ℤ ℚ), Φ, ← one_mul (X ^ 5), ← C_1]
--   refine' (card_rootSet_le_derivative _).trans
--     (Nat.succ_le_succ ((card_rootSet_le_derivative _).trans (Nat.succ_le_succ _)))
--   suffices : (Polynomial.rootSet (C (20 : ℚ) * X ^ 3) ℝ).Subsingleton
--   · norm_num [Fintype.card_le_one_iff_subsingleton, ← mul_assoc] at *
--     exact this
--   rw [rootSet_C_mul_X_pow] <;>
--   norm_num
-- #align abel_ruffini.real_roots_Phi_le AbelRuffini.real_roots_Phi_le

-- theorem real_roots_Phi_ge_aux (hab : b < a) :
--     ∃ x y : ℝ, x ≠ y ∧ aeval x (Φ ℚ a b) = 0 ∧ aeval y (Φ ℚ a b) = 0 := by
--   let f : ℝ → ℝ := fun x : ℝ => aeval x (Φ ℚ a b)
--   have hf : f = fun x : ℝ => x ^ 5 - a * x + b := by simp [Φ]
--   have hc : ∀ s : Set ℝ, ContinuousOn f s := fun s => (Φ ℚ a b).continuousOn_aeval
--   have ha : (1 : ℝ) ≤ a := Nat.one_le_cast.mpr (Nat.one_le_of_lt hab)
--   have hle : (0 : ℝ) ≤ 1 := zero_le_one
--   have hf0 : 0 ≤ f 0 := by simp [hf]
--   by_cases hb : (1 : ℝ) - a + b < 0
--   · have hf1 : f 1 < 0 := by simp [hf, hb]
--     have hfa : 0 ≤ f a := by
--       -- Porting note: was `simp_rw`
--       simp only [hf, ← sq]
--       refine' add_nonneg (sub_nonneg.mpr (pow_le_pow ha _)) _ <;> norm_num
--     obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Ico' hle (hc _) (Set.mem_Ioc.mpr ⟨hf1, hf0⟩)
--     obtain ⟨y, ⟨hy1, -⟩, hy2⟩ := intermediate_value_Ioc ha (hc _) (Set.mem_Ioc.mpr ⟨hf1, hfa⟩)
--     exact ⟨x, y, (hx1.trans hy1).ne, hx2, hy2⟩
--   · replace hb : (b : ℝ) = a - 1 := by linarith [show (b : ℝ) + 1 ≤ a from mod_cast hab]
--     have hf1 : f 1 = 0 := by simp [hf, hb]
--     have hfa :=
--       calc
--         f (-a) = (a : ℝ) ^ 2 - (a : ℝ) ^ 5 + b := by
--           norm_num [hf, ← sq, sub_eq_add_neg, add_comm, Odd.neg_pow (by decide : Odd 5)]
--         _ ≤ (a : ℝ) ^ 2 - (a : ℝ) ^ 3 + (a - 1) := by
--           refine' add_le_add (sub_le_sub_left (pow_le_pow ha _) _) _ <;> linarith
--         _ = -((a : ℝ) - 1) ^ 2 * (a + 1) := by ring
--         _ ≤ 0 := by nlinarith
--     have ha' := neg_nonpos.mpr (hle.trans ha)
--     obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Icc ha' (hc _) (Set.mem_Icc.mpr ⟨hfa, hf0⟩)
--     exact ⟨x, 1, (hx1.trans_lt zero_lt_one).ne, hx2, hf1⟩
-- #align abel_ruffini.real_roots_Phi_ge_aux AbelRuffini.real_roots_Phi_ge_aux

-- theorem real_roots_Phi_ge (hab : b < a) : 2 ≤ Fintype.card ((Φ ℚ a b).rootSet ℝ) := by
--   have q_ne_zero : Φ ℚ a b ≠ 0 := (monic_Phi a b).ne_zero
--   obtain ⟨x, y, hxy, hx, hy⟩ := real_roots_Phi_ge_aux a b hab
--   have key : ↑({x, y} : Finset ℝ) ⊆ (Φ ℚ a b).rootSet ℝ := by
--     simp [Set.insert_subset, mem_rootSet_of_ne q_ne_zero, hx, hy]
--   convert Fintype.card_le_of_embedding (Set.embeddingOfSubset _ _ key)
--   simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_singleton,
--     Finset.card_insert_of_not_mem (mt Finset.mem_singleton.mp hxy)]
-- #align abel_ruffini.real_roots_Phi_ge AbelRuffini.real_roots_Phi_ge

-- theorem complex_roots_Phi (h : (Φ ℚ a b).Separable) : Fintype.card ((Φ ℚ a b).rootSet ℂ) = 5 :=
--   (card_rootSet_eq_natDegree h (IsAlgClosed.splits_codomain _)).trans (natDegree_Phi a b)
-- #align abel_ruffini.complex_roots_Phi AbelRuffini.complex_roots_Phi

-- theorem gal_Phi (hab : b < a) (h_irred : Irreducible (Φ ℚ a b)) :
--     Bijective (galActionHom (Φ ℚ a b) ℂ) := by
--   apply galActionHom_bijective_of_prime_degree' h_irred
--   · simp only [natDegree_Phi]; decide
--   · rw [complex_roots_Phi a b h_irred.separable, Nat.succ_le_succ_iff]
--     exact (real_roots_Phi_le a b).trans (Nat.le_succ 3)
--   · simp_rw [complex_roots_Phi a b h_irred.separable, Nat.succ_le_succ_iff]
--     exact real_roots_Phi_ge a b hab
-- #align abel_ruffini.gal_Phi AbelRuffini.gal_Phi

-- theorem not_solvable_by_rad (p : ℕ) (x : ℂ) (hx : aeval x (Φ ℚ a b) = 0) (hab : b < a)
--     (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) : ¬IsSolvableByRad ℚ x := by
--   have h_irred := irreducible_Phi a b p hp hpa hpb hp2b
--   apply mt (solvableByRad.isSolvable' h_irred hx)
--   intro h
--   refine' Equiv.Perm.not_solvable _ (le_of_eq _)
--     (solvable_of_surjective (gal_Phi a b hab h_irred).2)
--   rw_mod_cast [Cardinal.mk_fintype, complex_roots_Phi a b h_irred.separable]
-- #align abel_ruffini.not_solvable_by_rad AbelRuffini.not_solvable_by_rad

-- theorem not_solvable_by_rad' (x : ℂ) (hx : aeval x (Φ ℚ 4 2) = 0) : ¬IsSolvableByRad ℚ x := by
--   apply not_solvable_by_rad 4 2 2 x hx <;> decide
-- #align abel_ruffini.not_solvable_by_rad' AbelRuffini.not_solvable_by_rad'

-- /-- **Abel-Ruffini Theorem** -/
-- theorem exists_not_solvable_by_rad : ∃ x : ℂ, IsAlgebraic ℚ x ∧ ¬IsSolvableByRad ℚ x := by
--   obtain ⟨x, hx⟩ := exists_root_of_splits (algebraMap ℚ ℂ) (IsAlgClosed.splits_codomain (Φ ℚ 4 2))
--     (ne_of_eq_of_ne (degree_Phi 4 2) (mt WithBot.coe_eq_coe.mp (show 5 ≠ 0 by norm_num)))
--   exact ⟨x, ⟨Φ ℚ 4 2, (monic_Phi 4 2).ne_zero, hx⟩, not_solvable_by_rad' x hx⟩
-- #align abel_ruffini.exists_not_solvable_by_rad AbelRuffini.exists_not_solvable_by_rad

-- end AbelRuffini
