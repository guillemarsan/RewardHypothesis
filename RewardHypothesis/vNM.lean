/-
Copyright (c) 2026 Guillermo Martín-Sanchez . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guillermo Martín-Sánchez
-/


import RewardHypothesis.Fishburn

set_option linter.style.emptyLine false

/-
Define a mixture space and the vNM axioms.
Then, state and prove vNM theorem: vNM axioms are equivalent to
the existence of a utility function.
-/
namespace Utility
open OrdinalRep

/-
Lemmas for the mixture space
-/

lemma comm_in_Icc (hp : p ∈ Set.Icc (0 : ℝ) 1) :
  1 - p ∈ Set.Icc (0 : ℝ) 1 :=
  by
    rcases hp with ⟨hp0, hp1⟩
    constructor
    · linarith
    · linarith

lemma assoc_in_Icc (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
  p * q ∈ Set.Icc (0 : ℝ) 1 := by
    have hprod0 : 0 ≤ p * q := by
      apply mul_nonneg hp.left hq.left
    have hprod1 : p * q ≤ 1 := by
      calc
        p * q ≤ p * 1 := by apply mul_le_mul_of_nonneg_left hq.right hp.left
        _ = p := by ring
        _ ≤ 1 := hp.right
    exact ⟨hprod0, hprod1⟩

lemma assoc_of_mix_in_Icc (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
  (hk : k ∈ Set.Icc (0 : ℝ) 1) : k * p + (1 - k) * q ∈ Set.Icc (0 : ℝ) 1 := by
    have hlin0 : 0 ≤ k * p + (1 - k) * q := by
      apply add_nonneg
      · apply mul_nonneg hk.left hp.left
      · apply mul_nonneg (comm_in_Icc hk).left hq.left
    have hlin1 : k * p + (1 - k) * q ≤ 1 := by
      calc
        k * p + (1 - k) * q ≤ k * 1 + (1 - k) * 1 := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left hp.right hk.left
          · apply mul_le_mul_of_nonneg_left hq.right (comm_in_Icc hk).left
        _ = 1 := by ring
    exact ⟨hlin0, hlin1⟩



/-
Define MixtureSpace with the p-mixture operation with its axioms
-/

def IntervalType : Type :=
  { p : ℝ // p ∈ Set.Icc 0 1 }

class MixSpace (α : Type) where
  mix :
    IntervalType →
    α → α → α

  mix_one :
    ∀ (p) (x y: α) (_ : p.1 = 1),
      mix p x y = x

  mix_comm :
    ∀ (p) (x y : α),
      mix p x y =
      mix ⟨1 - p.1, comm_in_Icc p.2⟩ y x

  mix_assoc :
    ∀ (p q) (x y : α),
      mix p (mix q x y) y = mix ⟨p.1 * q.1, assoc_in_Icc p.2 q.2⟩ x y


notation lhs " +[" p "]" rhs:50 => MixSpace.mix p lhs rhs

/-
Derived properties of the mixture operation
-/

lemma mix_zero [MixSpace α] (p : IntervalType) (x y : α) (h : p.1 = 0) :
  (x +[p] y) = y := by
    -- Use mix_comm to swap x and y
    have h_comm := MixSpace.mix_comm p x y
    rw [h_comm]
    -- Use mix_one on the swapped version
    have h_1 : (⟨1 - p.1, comm_in_Icc p.2⟩ : IntervalType).1 = 1 := by
      simp [h]
    have h_one := MixSpace.mix_one ⟨1 - p.1, comm_in_Icc p.2⟩ y x h_1
    rw [h_one]

lemma mix_idem [MixSpace α] (p : IntervalType) (x : α) :
  (x +[p] x) = x := by
    -- By mix_zero x+[0]x = x
    have h_zero : (x +[⟨0, by simp⟩] x) = x := mix_zero ⟨0, by simp⟩ x x rfl
    -- Then x +[p] x = (x +[0] x) +[p] x
    have h_eq : (x +[p] x) = (x +[⟨0, by simp⟩] x) +[p] x := by
      rw [h_zero]
    -- By associativity, we have (x +[0] x) +[p] x = x +[0] x
    have h_assoc := MixSpace.mix_assoc p ⟨0, by simp⟩ x x
    rw [h_assoc] at h_eq
    have h_p0_eq_0 : (⟨p.1 * 0, assoc_in_Icc p.2 (by simp)⟩ : IntervalType) = ⟨0, by simp⟩ := by
      apply Subtype.ext
      simp
    rw [h_p0_eq_0] at h_eq
    -- Finally, by mix_zero again, we have x +[0] x = x
    rw [h_zero] at h_eq
    exact h_eq

lemma associativity_of_mixtures [MixSpace α] :
  ∀ x y : α, ∀ p q k : IntervalType,
  ((x+[p]y) +[k] (x+[q]y)) = (x +[⟨k.1 * p.1 + (1 - k.1) * q.1,
    assoc_of_mix_in_Icc p.2 q.2 k.2⟩]y) := by
  intro x y p q k
  by_cases h_p_zero: p.1 = 0
  · -- Case 1: p = 0
    -- Then k * p + (1-k) * q = (1-k) * q
    have h_lp_eq : k.1 * p.1 + (1 - k.1) * q.1 = (1 - k.1) * q.1 := by
      rw [h_p_zero]
      simp
    have h_lp_eq_type : (⟨k.1 * p.1 + (1 - k.1) * q.1,
      assoc_of_mix_in_Icc p.2 q.2 k.2⟩ : IntervalType) =
      ⟨(1 - k.1) * q.1, assoc_in_Icc (comm_in_Icc k.2) q.2⟩ := by
      apply Subtype.ext h_lp_eq
    rw [h_lp_eq_type]
    -- Also (x +[p] y) = y
    have h_eq : (x +[p] y) = y := mix_zero p x y h_p_zero
    rw [h_eq]
    -- So we have to prove (y +[k] (x +[q] y)) = (x +[(1-k)q] y)
    -- First by commutativity we have (y +[k] (x +[q] y)) = ((x +[q] y) +[1-k] y)
    have h_comm := MixSpace.mix_comm k y (x +[q] y)
    rw [h_comm]
    -- Then by associativity we have ((x +[q] y) +[1-k] y) = (x +[(1-k)q] y)
    have h_assoc := MixSpace.mix_assoc ⟨1 - k.1, comm_in_Icc k.2⟩ q x y
    rw [h_assoc]
  · -- Case 2: p ≠ 0
    by_cases h_q_zero : q.1 = 0
    · -- Subcase 2.1: q = 0
      -- Then k * p + (1-k) * q = k * p
      have h_lp_eq : k.1 * p.1 + (1 - k.1) * q.1 = k.1 * p.1 := by
        rw [h_q_zero]
        simp
      have h_lp_eq_type : (⟨k.1 * p.1 + (1 - k.1) * q.1,
        assoc_of_mix_in_Icc p.2 q.2 k.2⟩ : IntervalType) =
        ⟨k.1 * p.1, assoc_in_Icc k.2 p.2⟩ := by
        apply Subtype.ext h_lp_eq
      rw [h_lp_eq_type]
      -- Also (x +[q] y) = y
      have h_eq : (x +[q] y) = y := mix_zero q x y h_q_zero
      rw [h_eq]
      -- So we have to prove ((x +[p] y) +[k] y) = (x +[kp] y)
      -- This is just associativity
      have h_assoc := MixSpace.mix_assoc k p x y
      rw [h_assoc]
    · -- Subcase 2.2: q ≠ 0
      -- Then both p,q ≠ 0
      by_cases h_p_le_q : p.1 ≤ q.1
      · -- Subsubcase 2.2.1: p ≤ q
        -- Then d = p/q is in [0,1]
        let d_val : ℝ := p.1 / q.1
        have h_d_in : d_val ∈ Set.Icc 0 1 := by
          have h_d_pos : 0 ≤ p.1 / q.1 := by
            exact div_nonneg (le_of_not_gt (not_lt_of_ge p.2.left))
              (le_of_lt (lt_iff_le_and_ne.mpr ⟨q.2.left, ne_comm.mp h_q_zero⟩))
          have h_d_le_one : p.1 / q.1 ≤ 1 := by
            exact (div_le_one (lt_iff_le_and_ne.mpr ⟨q.2.left, ne_comm.mp h_q_zero⟩)).mpr h_p_le_q
          exact ⟨h_d_pos, h_d_le_one⟩
        let d : IntervalType := ⟨d_val, h_d_in⟩
        -- By associativity we have
        -- x+[p]y = (x +[q]y) +[p/q] y
        have h_assoc := MixSpace.mix_assoc d q x y
        have h_p_eq : p.1 = d.1 * q.1 := by
          simp [d, d_val]
          field_simp
        have h_p_eq_subtype : p = ⟨d.1 * q.1, assoc_in_Icc d.2 q.2⟩ := by
          apply Subtype.ext h_p_eq
        have h_eq_mix : (x +[p] y) = ((x +[q] y) +[d] y) := by
          rw [h_assoc, h_p_eq_subtype]
        rw [h_eq_mix]
        -- And by commutativity we have
        -- x+[p]y = y +[1 - p/q] (x +[q]y)
        have h_comm := MixSpace.mix_comm d (x +[q] y) y
        rw [h_comm]
        -- So we have now to prove
        -- (y +[1 - p/q] (x +[q]y)) +[k] (x +[q]y) = (x +[k * p + (1 - k) * q] y)
        -- By associativity we have
        -- (y +[1 - p/q] (x +[q]y)) +[k] (x +[q]y) = y +[k(1-p/q)] (x +[q]y)
        have h_assoc_2 := MixSpace.mix_assoc k ⟨1 - d.1, comm_in_Icc d.2⟩ y (x +[q] y)
        rw [h_assoc_2]
        -- By commutativity we have
        -- y +[k(1-p/q)] (x +[q]y) = (x +[q]y) +[1 - k(1-p/q)] y
        have h_comm_2 := MixSpace.mix_comm ⟨k.1 * (1 - d.1),
          assoc_in_Icc k.2 (comm_in_Icc d.2)⟩ y (x +[q] y)
        rw [h_comm_2]
        -- By associativity we have
        -- (x +[q]y) +[1 - k(1-p/q)] y = x +[(1 - k(1-p/q)) * q] y
        have h_assoc_3 := MixSpace.mix_assoc ⟨1 - k.1 * (1 - d.1),
          comm_in_Icc (assoc_in_Icc k.2 (comm_in_Icc d.2))⟩ q x y
        rw [h_assoc_3]
        -- Now we just need to show that
        -- (1 - k(1-p/q)) * q = k * p + (1 - k) * q
        have h_final_eq : (1 - k.1 * (1 - d.1)) * q.1 = k.1 * p.1 + (1 - k.1) * q.1 := by
          rw [h_p_eq]
          ring
        have h_final_eq_subtype : (⟨(1 - k.1 * (1 - d.1)) * q.1,
          assoc_in_Icc (comm_in_Icc (assoc_in_Icc k.2 (comm_in_Icc d.2))) q.2⟩ : IntervalType) =
          ⟨k.1 * p.1 + (1 - k.1) * q.1, assoc_of_mix_in_Icc p.2 q.2 k.2⟩ := by
          apply Subtype.ext h_final_eq
        rw [h_final_eq_subtype]
      · -- Subsubcase 2.2.2: p > q
        -- Similarly as before
        -- Then d = q/p is in [0,1]
        let d_val : ℝ := q.1 / p.1
        have h_d_in : d_val ∈ Set.Icc 0 1 := by
          have h_d_pos : 0 ≤ q.1 / p.1 := by
            exact div_nonneg (le_of_not_gt (not_lt_of_ge q.2.left))
              (le_of_lt (lt_iff_le_and_ne.mpr ⟨p.2.left, ne_comm.mp h_p_zero⟩))
          have h_d_le_one : q.1 / p.1 ≤ 1 := by
            exact (div_le_one (lt_iff_le_and_ne.mpr ⟨p.2.left, ne_comm.mp h_p_zero⟩)).mpr
              (le_of_lt (lt_of_not_ge h_p_le_q))
          exact ⟨h_d_pos, h_d_le_one⟩
        let d : IntervalType := ⟨d_val, h_d_in⟩
        -- By associativity we have
        -- x+[q]y = (x +[p]y) +[q/p] y
        have h_assoc := MixSpace.mix_assoc d p x y
        have h_q_eq : q.1 = d.1 * p.1 := by
          simp [d, d_val]
          field_simp
        have h_q_eq_subtype : q = ⟨d.1 * p.1, assoc_in_Icc d.2 p.2⟩ := by
          apply Subtype.ext h_q_eq
        have h_eq_mix : (x +[q] y) = ((x +[p] y) +[d] y) := by
          rw [h_assoc, h_q_eq_subtype]
        rw [h_eq_mix]
        -- And by commutativity we have
        -- x+[q]y = y +[1 - q/p] (x +[p]y)
        have h_comm := MixSpace.mix_comm d (x +[p] y) y
        rw [h_comm]
        -- So we have now to prove
        -- (x +[p]y) +[k] (y +[1 - q/p] (x +[p]y)) = (x +[k * p + (1 - k) * q] y)
        -- By commutativity we have
        -- (x +[p]y) +[k] (y +[1 - q/p] (x +[p]y)) = (y +[1 - q/p] (x +[p]y)) +[1-k] (x +[p]y)
        have h_comm_2 := MixSpace.mix_comm k (x +[p] y) (y +[⟨1 - d.1, comm_in_Icc d.2⟩] (x +[p] y))
        rw [h_comm_2]
        -- By associativity we have
        -- (y +[1 - q/p] (x +[p]y)) +[1-k] (x +[p]y) = y +[(1-k)(1-q/p)] (x +[p]y)
        have h_assoc_2 := MixSpace.mix_assoc ⟨1 - k.1, comm_in_Icc k.2⟩
          ⟨1 - d.1, comm_in_Icc d.2⟩ y (x +[p] y)
        rw [h_assoc_2]
        -- By commutativity we have
        -- y +[(1-k)(1-q/p)] (x +[p]y) = (x +[p]y) +[1 - (1-k)(1-q/p)] y
        have h_comm_3 := MixSpace.mix_comm ⟨(1 - k.1) * (1 - d.1),
          assoc_in_Icc (comm_in_Icc k.2) (comm_in_Icc d.2)⟩ y (x +[p] y)
        rw [h_comm_3]
        -- By associativity we have
        -- (x +[p]y) +[1 - (1-k)(1-q/p)] y = x +[(1 - (1-k)(1-q/p)) * p] y
        have h_assoc_3 := MixSpace.mix_assoc ⟨1 - (1 - k.1) * (1 - d.1),
          comm_in_Icc (assoc_in_Icc (comm_in_Icc k.2) (comm_in_Icc d.2))⟩ p x y
        rw [h_assoc_3]
        -- Now we just need to show that
        -- (1 - (1-k)(1-q/p)) * p = k * p + (1 - k) * q
        have h_final_eq : (1 - (1 - k.1) * (1 - d.1)) * p.1 = k.1 * p.1 + (1 - k.1) * q.1 := by
          rw [h_q_eq]
          ring
        have h_final_eq_subtype : (⟨(1 - (1 - k.1) * (1 - d.1)) * p.1,
          assoc_in_Icc (comm_in_Icc (assoc_in_Icc (comm_in_Icc k.2) (comm_in_Icc d.2))) p.2⟩
          : IntervalType) =
          ⟨k.1 * p.1 + (1 - k.1) * q.1, assoc_of_mix_in_Icc p.2 q.2 k.2⟩ := by
          apply Subtype.ext h_final_eq
        rw [h_final_eq_subtype]

/-
Define what it means for a function to be an expected utility function.
-/

def p_linear [MixSpace α] (u : α → ℝ) : Prop :=
  ∀ x y : α, ∀ p : IntervalType, u (x +[p] y) = p.1 * u x + (1 - p.1) * u y

def utility_function [MixSpace α] (u : α → ℝ) (r : Relation α) : Prop :=
  ordinal_consistent u r ∧ p_linear u


/-
Define the vNM axioms for expected utility on a preference relation.
-/

def independence [MixSpace α] (r : Relation α) : Prop :=
  ∀ (x y z: α) (p : IntervalType), p.1 ∈ Set.Ioc 0 1 →
  ((x ≽[r] y) ↔ (x +[p] z) ≽[r] (y +[p] z))

def continuity [MixSpace α] (r : Relation α) : Prop :=
  ∀ x y z : α, (x ≽[r] y ∧ y ≽[r] z) → ∃ p : IntervalType, (x +[p] z) ∼[r] y

def vNM_axioms [MixSpace α] (r : Relation α) : Prop :=
  completeness r ∧
  transitivity r ∧
  independence r ∧
  continuity r

/-
Lemmas for the proof of the vNM theorem
-/

lemma full_indep_if_indep_and_comp [MixSpace α] (r : Relation α) :
  completeness r ∧ independence r → ∀ x y : α, (x ≽[r] y) →
  ∀ z : α, ∀ p : IntervalType, (x +[p] z) ≽[r] (y +[p] z) := by
  intro h_r_char x y hxy z p
  rcases h_r_char with ⟨h_completeness, h_indep⟩
  by_cases h_p_gt_zero : p.1 > 0
  · -- Case 1: p > 0 therefore p ∈ (0,1]
    have h_p_in_Ioc : p.1 ∈ Set.Ioc 0 1 := by
      exact ⟨h_p_gt_zero, p.2.right⟩
    -- Then this is just independence
    exact (h_indep x y z p h_p_in_Ioc).mp hxy
  · -- Case 2: ¬(p > 0) therefore p = 0
    have h_p_zero : p.1 = 0 := by
      exact le_antisymm (not_lt.mp h_p_gt_zero) p.2.left
    -- Then (x +[p] z) = z and (y +[p] z) = z, so we have z ≽ z
    have h_eq_xz : (x +[p] z) = z := mix_zero p x z h_p_zero
    have h_eq_yz : (y +[p] z) = z := mix_zero p y z h_p_zero
    rw [h_eq_xz, h_eq_yz]
    -- This is where we need the completeness to get z ≽ z
    have hzz : z ≽[r] z := (h_completeness z z).elim id id
    exact hzz

lemma full_indiff_indep [MixSpace α] (r : Relation α) :
  completeness r ∧ independence r →
  ∀ x y : α, (x ∼[r] y) → ∀ z : α, ∀ p : IntervalType, (x +[p] z) ∼[r] (y +[p] z) := by
  intro h_r_char x y
  have h_full_indep := full_indep_if_indep_and_comp r h_r_char
  intro hxy z p
  have hxy_ge : x ≽[r] y := hxy.left
  have hyx_ge : y ≽[r] x := hxy.right
  have h1 := h_full_indep x y hxy_ge z p
  have h2 := h_full_indep y x hyx_ge z p
  exact ⟨h1, h2⟩


lemma full_indiff_interior [MixSpace α] (r : Relation α) :
  completeness r ∧ independence r →
  ∀ x y : α, (x ∼[r] y) → ∀ p : IntervalType, (x ∼[r] (x +[p] y)) ∧ ((x +[p] y) ∼[r] y) := by
  intro h_r_char x y hxy p
  have h_full_indep := full_indiff_indep r h_r_char
  -- Apply independence x ~ y with y and p
  -- We get (x +[p] y) ∼ (y +[p] y)
  have h1 := full_indiff_indep r h_r_char x y hxy y p
  -- But (y +[p] y) = y by mix_idem
  have h_idem := mix_idem p y
  rw [h_idem] at h1
  -- So we have (x +[p] y) ∼ y
  -- Similarly for the other direction
  have h2 := full_indiff_indep r h_r_char x y hxy x ⟨1 - p.1, comm_in_Icc p.2⟩
  have h_idem' := mix_idem ⟨1 - p.1, comm_in_Icc p.2⟩ x
  rw [h_idem'] at h2
  have h_comm := MixSpace.mix_comm p x y
  rw [←h_comm] at h2
  exact ⟨h2, h1⟩

lemma full_partial_interior [MixSpace α] (r : Relation α) :
  completeness r ∧ independence r → ∀ x y : α, (x ≽[r] y) →
  ∀ p : IntervalType, (x ≽[r] (x +[p] y)) ∧ ((x +[p] y) ≽[r] y) := by
  intro h_r_char x y hxy p
  have h_full_independence := full_indep_if_indep_and_comp r h_r_char
  -- Mix x ≽ y with y and p to get (x +[p] y) ≽ (y +[p] y)
  have h1 := h_full_independence x y hxy y p
  -- But (y +[p] y) = y by mix_idem
  have h_idem := mix_idem p y
  rw [h_idem] at h1
  -- Similarly for the other direction,
  -- x ≽ y with x and 1-p to get (x +[1-p] x) ≽ (y +[1-p] x)
  have h2 := h_full_independence x y hxy x ⟨1 - p.1, comm_in_Icc p.2⟩
  -- But (x +[1-p] x) = x by mix_idem
  have h_idem2 := mix_idem ⟨1 - p.1, comm_in_Icc p.2⟩ x
  rw [h_idem2] at h2
  -- By commutativity we have (y +[1-p] x) = (x +[p] y)
  have h_comm := MixSpace.mix_comm p x y
  rw [←h_comm] at h2
  exact ⟨h2, h1⟩

lemma partial_interior [MixSpace α] (r : Relation α) :
  independence r → ∀ x y : α, (x ≽[r] y) →
  ∀ p : IntervalType, p.1 ∈ Set.Ioo 0 1 → (x ≽[r] (x +[p] y)) ∧ ((x +[p] y) ≽[r] y) := by
  intro h_indep x y hxy p h_p_in
  have h_p_in_Ioc : p.1 ∈ Set.Ioc 0 1 := by
    exact ⟨h_p_in.left, le_of_lt h_p_in.right⟩
  -- Mix x ≽ y with y and p to get (x +[p] y) ≽ (y +[p] y)
  have h1 := (h_indep x y y p h_p_in_Ioc).mp hxy
  -- But (y +[p] y) = y by mix_idem
  have h_idem := mix_idem p y
  rw [h_idem] at h1
  -- Similarly for the other direction,
  -- x ≽ y with x and 1-p to get (x +[1-p] x) ≽ (y +[1-p] x)
  have h_p_comm_in_Ioc : (1 - p.1) ∈ Set.Ioc 0 1 := by
    have h_p_comm_pos : 0 < 1 - p.1 := by
      have h_p_less_one := h_p_in.right
      linarith
    have h_p_comm_le_one : 1 - p.1 ≤ 1 := by
      have h_p_pos := h_p_in.left
      linarith
    exact ⟨h_p_comm_pos, h_p_comm_le_one⟩
  have h2 := (h_indep x y x ⟨1 - p.1, comm_in_Icc p.2⟩ h_p_comm_in_Ioc).mp hxy
  -- But (x +[1-p] x) = x by mix_idem
  have h_idem2 := mix_idem ⟨1 - p.1, comm_in_Icc p.2⟩ x
  rw [h_idem2] at h2
  -- By commutativity we have (y +[1-p] x) = (x +[p] y)
  have h_comm := MixSpace.mix_comm p x y
  rw [←h_comm] at h2
  exact ⟨h2, h1⟩


lemma strict_interior [MixSpace α] (r : Relation α) :
  independence r → ∀ x y : α, (x ≻[r] y) →
  ∀ p : IntervalType, p.1 ∈ Set.Ioo 0 1 → x ≻[r] (x +[p] y) ∧ (x +[p] y) ≻[r] y := by
  intro h_indep x y hxy p h_p_in
  have h_partial_interior : (x ≽[r] (x +[p] y)) ∧ ((x +[p] y) ≽[r] y) := by
    exact partial_interior r h_indep x y hxy.left p h_p_in
  have h_not_partial_interior_x : ¬((x +[p] y) ≽[r] x) := by
    intro h_contra
    -- By commmutativity we have (x +[p] y) = (y +[1-p] x) ≽ x
    have h_comm := MixSpace.mix_comm p x y
    rw [h_comm] at h_contra
    -- By idem we have (y +[1-p] x) ≽ (x +[1-p] x) = x
    let one_minus_p : IntervalType := ⟨1 - p.1, comm_in_Icc p.2⟩
    have h_aux_indep : (y +[one_minus_p] x) ≽[r] (x +[one_minus_p] x) := by
      have h_x_eq_xpx : (x +[one_minus_p] x) = x := mix_idem one_minus_p x
      nth_rewrite 2 [←h_x_eq_xpx] at h_contra
      exact h_contra
    -- Therefore by independence we have y ≽ x, contradiction
    have h_one_minus_p_in : one_minus_p.1 ∈ Set.Ioc 0 1 := by
      have h_one_minus_p_pos : 0 < one_minus_p.1 := by
        have h_p_less_one := h_p_in.right
        linarith
      have h_one_minus_p_le_one : one_minus_p.1 ≤ 1 := by
        have h_p_pos := h_p_in.left
        linarith
      exact ⟨h_one_minus_p_pos, h_one_minus_p_le_one⟩
    have h_y_ge_x : y ≽[r] x := by
      exact (h_indep y x x one_minus_p h_one_minus_p_in).mpr h_aux_indep
    exact absurd h_y_ge_x hxy.right
  have h_not_partial_interior_y : ¬(y ≽[r] (x +[p] y)) := by
    intro h_contra
    -- By idem we have (y +[p] y) ≽ (x +[p] y)
    have h_aux_indep : (y +[p] y) ≽[r] (x +[p] y) := by
      have h_y_eq_ypy : (y +[p] y) = y := mix_idem p y
      nth_rewrite 1 [←h_y_eq_ypy] at h_contra
      exact h_contra
    -- Therefore by independence we have y ≽ x, contradiction
    have h_x_ge_y : y ≽[r] x := by
      exact (h_indep y x y p ⟨h_p_in.left, le_of_lt h_p_in.right⟩).mpr h_aux_indep
    exact absurd h_x_ge_y hxy.right
  exact ⟨⟨h_partial_interior.left, h_not_partial_interior_x⟩,
     ⟨h_partial_interior.right, h_not_partial_interior_y⟩⟩


lemma strict_p_consistency [MixSpace α] (r : Relation α) :
  completeness r ∧ independence r →
  ∀ x y : α, (x ≻[r] y) → (∀ p q : IntervalType, ((x+[p]y) ≻[r] (x+[q]y)) ↔ p.1 > q.1) := by
  intro h_r_chars x y hxy p q
  rcases h_r_chars with ⟨h_complete, h_independence⟩
  have h_strict_interior := strict_interior r h_independence
  constructor
  · -- Forward direction
    -- Assume (x +[p] y) ≻ (x +[q] y) and show p.1 > q.1
    intro h_px_qy
    -- Then let's assume that p ≤ q and reach a contradiction
    by_contra h_p_ngt_q
    have h_p_le_q : p.1 ≤ q.1 := by
      exact not_lt.mp h_p_ngt_q
    by_cases h_p_eq_q : p.1 = q.1
    · -- Case 1: p = q
      -- Then (x +[p] y) = (x +[q] y), and we get (x +[p] y) ≻ (x +[p] y), contradiction
      have h_eq : (x +[p] y) = (x +[q] y) := by
        have h_eq_mix : p = q := by
          apply Subtype.ext h_p_eq_q
        rw [h_eq_mix]
      rw [←h_eq] at h_px_qy
      exact absurd ((h_complete (x +[p] y) (x +[p] y)).elim id id) h_px_qy.right
    · -- Case 2: p ≠ q
      -- Then p < q
      have h_p_lt_q : p.1 < q.1 := by
        exact lt_iff_le_and_ne.mpr ⟨h_p_le_q, h_p_eq_q⟩
      by_cases h_q_zero : q.1 = 0
      · -- Subcase 2.1: q = 0, (p,q) = (>0,0)
        -- Impossible cause p ≥ 0 and p < q = 0
        have h_p_ge_zero : p.1 ≥ 0 := by
          exact p.2.left
        linarith
      · -- Subcase 2.2: q ≠ 0
        -- Then q > 0, (p,q) = (>0, >0)
        have h_q_pos : q.1 > 0 := by
          exact lt_iff_le_and_ne.mpr ⟨q.2.left, ne_comm.mp h_q_zero⟩
        by_cases h_q_one : q.1 = 1
        · -- Subsubcase 2.1.1: q = 1, (p,q) = (<1,1)
          -- Then (x +[q] y) = x
          have h_eq' : (x +[q] y) = x := MixSpace.mix_one q x y h_q_one
          rw [h_eq'] at h_px_qy
          -- Since (x +[p] y) ≻ x, by strict_interior we have p ∉ (0,1)
          have h_p_not_in : ¬(p.1 ∈ Set.Ioo 0 1) := by
            -- Since x ≻ y, if p ∈ (0,1) then x ≻ (x +[p] y), contradiction
            intro h_p_in
            have h_strict := h_strict_interior x y hxy p h_p_in
            have h_px_ge : x ≽[r] (x +[p] y) := h_strict.left.left
            exact absurd h_px_ge h_px_qy.right
          -- Then since p ∉ (0,1) and p < 1, we have p = 0, (p,q) = (0,1)
          have h_p_lt_one : p.1 < 1 := by
            simpa [h_q_one] using h_p_lt_q
          have h_p_zero : p.1 = 0 := by
            have h_p_not_in_unfold : p.1 ≤ 0 ∨ p.1 ≥ 1 := by
              by_contra h_contra_unfold
              push_neg at h_contra_unfold
              exact h_p_not_in h_contra_unfold
            cases h_p_not_in_unfold with
            | inl h_le_zero =>
              exact le_antisymm h_le_zero p.2.left
            | inr h_ge_one =>
              exact absurd h_p_lt_one (not_lt_of_ge h_ge_one)
          -- Then (x +[p] y) = y, and we get y ≻ x, contradiction
          have h_eq : (x +[p] y) = y := mix_zero p x y h_p_zero
          rw [h_eq] at h_px_qy
          exact absurd h_px_qy.left hxy.right
        · -- Subsubcase 2.2.2: q ≠ 1, (p,q) = (<1, (0,1))
          -- Since q ∉ {0,1} then q ∈ (0,1) and by strict_interior we have
          -- (x +[q] y) ≻ y
          have h_q_in : q.1 ∈ Set.Ioo 0 1 := by
            exact ⟨h_q_pos, lt_iff_le_and_ne.mpr ⟨q.2.right, h_q_one⟩⟩
          have h_strict_prop_p := h_strict_interior x y hxy q h_q_in
          have h_qy_y_ge : (x +[q] y) ≻[r] y := h_strict_prop_p.right
          by_cases h_p_zero : p.1 = 0
          · -- Subsubsubcase 2.2.2.1: p = 0
            -- Then (x +[p] y) = y, and y ≻ (x +[q] y)
            have h_eq : (x +[p] y) = y := mix_zero p x y h_p_zero
            rw [h_eq] at h_px_qy
            -- Since q ∈ (0,1), by strict_interior we have (x +[q] y) ≻ y
            have h_strict_prop_q := h_strict_interior x y hxy q h_q_in
            exact absurd h_qy_y_ge.left h_px_qy.right
          · -- Subsubsubcase 2.2.2.2: p ≠ 0
            -- Then p > 0, and p ∈ (0,1), (p,q) = ((0,1), (0,1))
            have h_p_pos : p.1 > 0 := by
              exact lt_iff_le_and_ne.mpr ⟨p.2.left, ne_comm.mp h_p_zero⟩
            have h_p_in : p.1 ∈ Set.Ioo 0 1 := by
              exact ⟨h_p_pos, lt_trans h_p_lt_q h_q_in.right⟩
            -- Then k = p/q ∈ (0,1)
            let k_val : ℝ := p.1 / q.1
            have h_k_in : k_val ∈ Set.Ioo 0 1 := by
              have h_k_pos : 0 < p.1 / q.1 := by
                exact div_pos h_p_pos h_q_pos
              have h_k_lt_one : p.1 / q.1 < 1 := by
                exact (div_lt_one h_q_in.left).mpr h_p_lt_q
              exact ⟨h_k_pos, h_k_lt_one⟩
            let k : IntervalType := ⟨k_val, ⟨le_of_lt h_k_in.left, le_of_lt h_k_in.right⟩⟩
            -- By strict interior, we have (x +[q] y) ≻ (x +[q] y) +[k] y
            have h_strict_prop_k := h_strict_interior (x +[q] y) y h_qy_y_ge k h_k_in
            have h_q_qk := h_strict_prop_k.left
            -- By associativity, we have (x +[q] y) +[k] y = x +[p] y
            -- since k = p / q
            have h_assoc := MixSpace.mix_assoc k q x y
            have h_p_eq : p.1 = k.1 * q.1 := by
              simp [k, k_val]
              field_simp
            have h_p_eq_subtype : p = ⟨k.1 * q.1, assoc_in_Icc k.2 q.2⟩ := by
              apply Subtype.ext h_p_eq
            have h_eq_mix : ((x +[q] y) +[k] y) = x +[p] y := by
              rw [h_assoc, h_p_eq_subtype]
            -- Then we have (x +[q] y) ≻ (x +[p] y), contradiction
            rw [h_eq_mix] at h_q_qk
            exact absurd h_q_qk.left h_px_qy.right
  · -- Backward direction
    -- Assume p.1 > q.1 and show (x +[p] y) ≻ (x +[q] y)
    intro h_p_gt_q
    have h_p_pos : p.1 > 0 := by
      exact lt_of_le_of_lt q.2.left h_p_gt_q
    -- By cases on q = 0
    by_cases h_q_zero : q.1 = 0
    · -- Case 1: q = 0
      -- Then (x +[q] y) = y
      have h_eq : (x +[q] y) = y := mix_zero q x y h_q_zero
      rw [h_eq]
      by_cases h_p_one : p.1 = 1
      · -- Subcase 1.1: p = 1, (p,q) = (1,0)
        -- Then (x +[p] y) = x, and we have x ≻ y
        have h_eq' : (x +[p] y) = x := MixSpace.mix_one p x y h_p_one
        rw [h_eq']
        exact hxy
      · -- Subcase 1.2: p ≠ 1, (p,q) = ((0,1),0)
        -- Then p ∈ (0,1), and by strict_interior we have (x +[p] y) ≻ y
        have h_p_in : p.1 ∈ Set.Ioo 0 1 := by
          exact ⟨h_p_pos, lt_iff_le_and_ne.mpr ⟨p.2.right, h_p_one⟩⟩
        have h_strict := h_strict_interior x y hxy p h_p_in
        exact h_strict.right
    · -- Case 2: q ≠ 0
      -- Then q > 0, (p,q) = (>0, >0)
      have h_q_pos : q.1 > 0 := by
        exact lt_iff_le_and_ne.mpr ⟨q.2.left, ne_comm.mp h_q_zero⟩
      by_cases h_p_one : p.1 = 1
      · -- Subcase 2.1: p = 1, (p,q) = (1, (0,1))
        -- Then (x +[p] y) = x
        have h_eq' : (x +[p] y) = x := MixSpace.mix_one p x y h_p_one
        rw [h_eq']
        -- Since p > q and p = 1, we have q ∈ (0,1), and by strict_interior we have x ≻ (x +[q] y)
        have h_q_in : q.1 ∈ Set.Ioo 0 1 := by
          have h_q_not_one : q.1 ≠ 1 := by
            intro h_eq_one
            rw [h_eq_one] at h_p_gt_q
            linarith
          exact ⟨h_q_pos, lt_iff_le_and_ne.mpr ⟨q.2.right, h_q_not_one⟩⟩
        have h_strict := h_strict_interior x y hxy q h_q_in
        exact h_strict.left
      · -- Subcase 2.2: p ≠ 1, (p,q) = ((0,1), (0,1))
        -- Then p ∈ (0,1), and by strict_interior we have
        -- (x +[p] y) ≻ y
        have h_p_in : p.1 ∈ Set.Ioo 0 1 := by
          exact ⟨h_p_pos, lt_iff_le_and_ne.mpr ⟨p.2.right, h_p_one⟩⟩
        have h_strict_prop_p := h_strict_interior x y hxy p h_p_in
        have h_px_y_ge : (x +[p] y) ≻[r] y := h_strict_prop_p.right
        -- Then k = q/p ∈ (0,1)
        let k_val : ℝ := q.1 / p.1
        have h_k_in : k_val ∈ Set.Ioo 0 1 := by
          have h_k_pos : 0 < q.1 / p.1 := by
            exact div_pos h_q_pos h_p_pos
          have h_k_lt_one : q.1 / p.1 < 1 := by
            exact (div_lt_one h_p_pos).mpr h_p_gt_q
          exact ⟨h_k_pos, h_k_lt_one⟩
        let k : IntervalType := ⟨k_val, ⟨le_of_lt h_k_in.left, le_of_lt h_k_in.right⟩⟩
        -- By strict interior, we have (x +[p] y) ≻ (x +[p] y) +[k] y
        have h_strict_prop_k := h_strict_interior (x +[p] y) y h_px_y_ge k h_k_in
        have h_p_pk := h_strict_prop_k.left
        -- By associativity, we have (x +[p] y) +[k] y = x +[q] y
        -- since k = q / p
        have h_assoc := MixSpace.mix_assoc k p x y
        have h_q_eq : q.1 = k.1 * p.1 := by
          simp [k, k_val]
          field_simp
        have h_q_eq_subtype : q = ⟨k.1 * p.1, assoc_in_Icc k.2 p.2⟩ := by
          apply Subtype.ext h_q_eq
        have h_eq_mix : ((x +[p] y) +[k] y) = x +[q] y := by
          rw [h_assoc, h_q_eq_subtype]
        -- Then we have (x +[p] y) ≻ (x +[q] y)
        rw [h_eq_mix] at h_p_pk
        exact h_p_pk

lemma unique_continuity_strict [MixSpace α] (r : Relation α) :
  vNM_axioms r →
  ∀ x y z : α, (x ≻[r] y ∧ y ≻[r] z) → ∃! p : IntervalType, ((x+[p]z) ∼[r] y) := by
  intro h_vNM x y z h_xyz
  rcases h_vNM with ⟨h_complete, h_trans, h_independence, h_cont⟩
  have h_strict_interior := strict_interior r h_independence
  rcases h_xyz with ⟨h_xy, h_yz⟩
  have h_xz : x ≻[r] z := by
    have h_xy_ge : x ≽[r] y := h_xy.left
    have h_yz_ge : y ≽[r] z := h_yz.left
    have h_xz_ge : x ≽[r] z := h_trans x y z ⟨h_xy_ge, h_yz_ge⟩
    have h_not_zx_ge : ¬(z ≽[r] x) := by
      intro h_zx_ge
      have h_yx_ge : y ≽[r] x := h_trans y z x ⟨h_yz_ge, h_zx_ge⟩
      exact h_xy.right h_yx_ge
    exact ⟨h_xz_ge, h_not_zx_ge⟩
  -- First, show existence, this is just from continuity
  have h_exists := h_cont x y z ⟨h_xy.left, h_yz.left⟩
  rcases h_exists with ⟨p, h_eq⟩
  -- Now show uniqueness
  have h_unique : ∀ q : IntervalType, ((x +[q] z) ∼[r] y) → q = p := by
    intro q h_xq_y
    -- Since both (x +[p] z) ∼ y and (x +[q] z) ∼ y, we have
    -- (x +[p] z) ∼ (x +[q] z)
    have h_xpz_xqz := indiff_transitivity r h_trans (x +[p] z) y (x +[q] z)
      ⟨h_eq, ⟨h_xq_y.right, h_xq_y.left⟩⟩
    -- Assume p ≠ q and reach a contradiction
    by_contra h_p_neq_q
    by_cases h_p_lt_q : p.1 < q.1
    · -- Case 1: p < q
      -- Then by strict p-consistency we have (x +[p] z) ≻ (x +[q] z), contradiction
      have h_strict_p_cons := strict_p_consistency r ⟨h_complete, h_independence⟩ x z h_xz
      have h_qx_pz := (h_strict_p_cons q p).mpr h_p_lt_q
      exact absurd h_xpz_xqz.left h_qx_pz.right
    · -- Case 2: p ≥ q
      have h_q_lt_p : q.1 < p.1 := by
        have h_not_eq : q.1 ≠ p.1 := by
          intro h_eq
          exact h_p_neq_q (Subtype.ext h_eq)
        exact lt_iff_le_and_ne.mpr ⟨le_of_not_gt h_p_lt_q, h_not_eq⟩
      -- Then by strict p-consistency we have (x +[q] z) ≻ (x +[p] z), contradiction
      have h_strict_p_cons := strict_p_consistency r ⟨h_complete, h_independence⟩ x z h_xz
      have h_px_qz := (h_strict_p_cons p q).mpr h_q_lt_p
      exact absurd h_xpz_xqz.right h_px_qz.right
  exact ⟨p, h_eq, h_unique⟩

lemma unique_continuity [MixSpace α] (r : Relation α) :
  vNM_axioms r →
  ∀ x y z : α, (x ≻[r] z ∧ x ≽[r] y ∧ y ≽[r] z) → ∃! p : IntervalType, ((x+[p]z) ∼[r] y) := by
  intro h_vNM x y z h_xyz
  rcases h_vNM with ⟨h_complete, h_trans, h_independence, h_cont⟩
  have h_strict_interior := strict_interior r h_independence
  rcases h_xyz with ⟨h_xz, h_xy, h_yz⟩
  by_cases h_xy_eq : x ∼[r] y
  · -- Case 1: x ∼ y
    -- Then ∃ p = 1 such that (x +[p] z) ∼ y
    have h_exists : ∃ p : IntervalType, ((x +[p] z) ∼[r] y) ∧ p.1 = 1 := by
      let p : IntervalType := ⟨1, by simp⟩
      use p
      have h_eq : (x +[p] z) = x := MixSpace.mix_one p x z rfl
      rw [h_eq]
      exact ⟨h_xy_eq, rfl⟩
    -- Uniqueness: if (x +[q] z) ∼ y, then q = 1
    have h_unique : ∀ q : IntervalType, ((x +[q] z) ∼[r] y) → q.1 = 1 := by
      intro q h_xq_y
      -- First we get (x +[q] z) ∼ x
      have h_xq_x := indiff_transitivity r h_trans (x +[q] z) y x
        ⟨h_xq_y, ⟨h_xy_eq.right, h_xy_eq.left⟩⟩
      by_contra h_q_neq_one
      have h_q_lt_one : q.1 < 1 := by
        exact lt_iff_le_and_ne.mpr ⟨q.2.right, h_q_neq_one⟩
      by_cases h_q_zero : q.1 = 0
      · -- Subcase 1.1: q = 0
        -- Then (x +[q] z) = z, and we have z ∼ x, contradiction
        have h_eq : (x +[q] z) = z := mix_zero q x z h_q_zero
        rw [h_eq] at h_xq_x
        exact absurd h_xq_x.left h_xz.right
      · -- Subcase 1.2: q ≠ 0
        -- Then q ∈ (0,1), and by strict_interior we have x ≻ (x +[q] z), contradiction
        have h_q_pos : q.1 > 0 := by
          exact lt_iff_le_and_ne.mpr ⟨q.2.left, ne_comm.mp h_q_zero⟩
        have h_q_in : q.1 ∈ Set.Ioo 0 1 := by
          exact ⟨h_q_pos, h_q_lt_one⟩
        have h_strict := h_strict_interior x z h_xz q h_q_in
        exact absurd h_xq_x.left h_strict.left.right
    rcases h_exists with ⟨p, h_eq⟩
    rcases h_eq with ⟨h_eq_sim, h_p_one⟩
    have h_p_eq : ∀ q : IntervalType, ((x +[q] z) ∼[r] y) → q = p := by
      intro q h_xq_y
      have h_q_one : q.1 = 1 := h_unique q h_xq_y
      have h_q_p : q.1 = p.1 := by
        rw [h_q_one]
        exact h_p_one.symm
      exact Subtype.ext h_q_p
    exact ⟨p, h_eq_sim, h_p_eq⟩
  · -- Case 2: x ≁ y
    have h_xy_gt : x ≻[r] y := by
      exact ⟨h_xy, (not_and_or.mp h_xy_eq).resolve_left (not_not.mpr h_xy)⟩
    by_cases h_yz_eq : y ∼[r] z
    · -- Subcase 2.1: y ∼ z
      -- Then ∃ p = 0 such that (x +[p] z) ∼ y
      have h_exists : ∃ p : IntervalType, ((x +[p] z) ∼[r] y) ∧ p.1 = 0 := by
        let p : IntervalType := ⟨0, by simp⟩
        use p
        have h_eq : (x +[p] z) = z := mix_zero p x z rfl
        rw [h_eq]
        exact ⟨⟨h_yz_eq.right, h_yz_eq.left⟩, rfl⟩
      -- Uniqueness: if (x +[q] z) ∼ y, then q = 0
      have h_unique : ∀ q : IntervalType, ((x +[q] z) ∼[r] y) → q.1 = 0 := by
        intro q h_xq_y
        -- First we get (x +[q] z) ∼ z
        have h_xq_z := indiff_transitivity r h_trans (x +[q] z) y z
          ⟨h_xq_y, h_yz_eq⟩
        by_contra h_q_neq_zero
        have h_q_gt_zero : q.1 > 0 := by
          exact lt_iff_le_and_ne.mpr ⟨q.2.left, ne_comm.mp h_q_neq_zero⟩
        by_cases h_q_one : q.1 = 1
        · -- Subsubcase 2.1.1: q = 1
          -- Then (x +[q] z) = x, and we have x ∼ z, contradiction
          have h_eq : (x +[q] z) = x := MixSpace.mix_one q x z h_q_one
          rw [h_eq] at h_xq_z
          exact absurd h_xq_z.right h_xz.right
        · -- Subsubcase 2.1.2: q ≠ 1
          -- Then q ∈ (0,1), and by strict_interior we have (x +[q] z) ≻ z, contradiction
          have h_q_lt_one : q.1 < 1 := by
            exact lt_iff_le_and_ne.mpr ⟨q.2.right, h_q_one⟩
          have h_q_in : q.1 ∈ Set.Ioo 0 1 := by
            exact ⟨h_q_gt_zero, h_q_lt_one⟩
          have h_strict := h_strict_interior x z h_xz q h_q_in
          exact absurd h_xq_z.right h_strict.right.right
      rcases h_exists with ⟨p, h_eq⟩
      rcases h_eq with ⟨h_eq_sim, h_p_zero⟩
      have h_p_eq : ∀ q : IntervalType, ((x +[q] z) ∼[r] y) → q = p := by
        intro q h_xq_y
        have h_q_zero : q.1 = 0 := h_unique q h_xq_y
        have h_q_p : q.1 = p.1 := by
          rw [h_q_zero]
          exact h_p_zero.symm
        exact Subtype.ext h_q_p
      exact ⟨p, h_eq_sim, h_p_eq⟩
    · -- Subcase 2.2: y ≁ z
      have h_yz_gt : y ≻[r] z := by
        exact ⟨h_yz, (not_and_or.mp h_yz_eq).resolve_left (not_not.mpr h_yz)⟩
      -- Now we can use the strict version of unique continuity
      exact unique_continuity_strict r ⟨h_complete, h_trans, h_independence, h_cont⟩
        x y z ⟨h_xy_gt, h_yz_gt⟩

lemma strict_substitution (r : Relation α) :
  transitivity r → ∀ x y u v : α, (u ∼[r] x ∧ v ∼[r] y) → ((x ≻[r] y) ↔ u ≻[r] v) := by
  intro h_trans x y u v h_uxvy
  have h_one_direction : ∀ (x y u v: α), (u ∼[r] x ∧ v ∼[r] y) → ((x ≻[r] y) → u ≻[r] v) := by
    intro x y u v h_uv h_xy
    rcases h_uv with ⟨h_ux, h_vy⟩
    have h_u_ge_v : u ≽[r] v := by
      have h_ux_ge : u ≽[r] y := h_trans u x y ⟨h_ux.left, h_xy.left⟩
      exact h_trans u y v ⟨h_ux_ge, h_vy.right⟩
    have h_not_v_ge_u : ¬(v ≽[r] u) := by
      intro h_vu_ge
      have h_yu_ge : y ≽[r] u := h_trans y v u ⟨h_vy.right, h_vu_ge⟩
      have h_yx_ge : y ≽[r] x := h_trans y u x ⟨h_yu_ge, h_ux.left⟩
      exact h_xy.right h_yx_ge
    exact ⟨h_u_ge_v, h_not_v_ge_u⟩
  constructor
  · -- Forward direction
    intro h_xy
    exact h_one_direction x y u v h_uxvy h_xy
  · -- Backward direction
    intro h_uv
    exact h_one_direction u v x y
      ⟨⟨h_uxvy.left.right, h_uxvy.left.left⟩, ⟨h_uxvy.right.right, h_uxvy.right.left⟩⟩ h_uv



lemma linear_substitution [MixSpace α] (r : Relation α) :
  completeness r ∧ transitivity r ∧ independence r → ∀ x y u v : α, ∀ p q k : IntervalType,
  (x ∼[r] u+[p]v) ∧ (y ∼[r] u +[q]v) →
  (x+[k]y) ∼[r] (u +[⟨k.1 * p.1 + (1 - k.1) * q.1, assoc_of_mix_in_Icc p.2 q.2 k.2⟩]v) := by
  intro h_r_chars x y u v p q k h_xu_vy
  rcases h_r_chars with ⟨h_complete, h_trans, h_indep⟩
  rcases h_xu_vy with ⟨h_x_eq, h_y_eq⟩
  -- From independence on x ∼ (u+[p]v) mixing with k and (u +[q]v) we get
  -- (x +[k] (u +[q] v)) ∼ ((u +[p] v) +[k] (u +[q] v))
  have h_mix_x : (x +[k] (u +[q] v)) ∼[r] ((u +[p] v) +[k] (u +[q] v)) :=
    full_indiff_indep r ⟨h_complete, h_indep⟩ x (u +[p] v) h_x_eq (u +[q] v) k
  -- From independence on y ∼ (u+[q]v) mixing with 1-k and x we get
  -- (y +[1-k] x) ∼ ((u +[q] v) +[1-k] x)
  have h_mix_y : (y +[⟨1 - k.1, comm_in_Icc k.2⟩] x) ∼[r]
    ((u +[q] v) +[⟨1 - k.1, comm_in_Icc k.2⟩] x) :=
    full_indiff_indep r ⟨h_complete, h_indep⟩ y (u +[q] v) h_y_eq x ⟨1 - k.1, comm_in_Icc k.2⟩
  -- By commutativity, the rhs ((u +[q] v) +[1-k] x) = (x +[k] (u +[q] v))
  have h_comm := MixSpace.mix_comm k x (u +[q] v)
  rw [←h_comm] at h_mix_y
  -- By commutativity, the lhs (y +[1-k] x) = (x +[k] y)
  have h_comm_2 := MixSpace.mix_comm k x y
  rw [←h_comm_2] at h_mix_y
  -- So we get (x +[k] y) ∼ (x +[k] (u +[q] v))
  -- By transitivity we have
  -- (x +[k] y) ∼ ((u +[p] v) +[k] (u +[q] v))
  have h_result : (x +[k] y) ∼[r] ((u +[p] v) +[k] (u +[q] v)) :=
    indiff_transitivity r h_trans (x +[k] y) (x +[k] (u +[q] v)) ((u +[p] v) +[k] (u +[q] v))
      ⟨h_mix_y, h_mix_x⟩
  -- Now we just need to show that
  -- (u +[p] v) +[k] (u +[q] v) = (u +[k * p + (1 - k) * q] v)
  -- This is just associativity of mixtures
  have h_assoc := associativity_of_mixtures u v p q k
  rw [h_assoc] at h_result
  exact h_result

/-
Structures needed for the proof of the vNM theorem.
-/

def S (r : Relation α) (a b : α) [MixSpace α] : Set α :=
  { x : α | a ≽[r] x ∧ x ≽[r] b }

structure μ_Type (r : Relation α) (a b x : α) [MixSpace α] where
  p : IntervalType
  spec : ((a +[p] b) ∼[r] x)
  unique : ∀ (k : IntervalType), ((a +[k] b) ∼[r] x) → k = p

structure M_Type (r : Relation α) (a b x m n : α) [MixSpace α] where
  eval : ℝ
  μ_x : μ_Type r a b x
  μ_m : μ_Type r a b m
  μ_n : μ_Type r a b n
  spec : eval = (μ_x.p.val - μ_n.p.val) / (μ_m.p.val - μ_n.p.val)
  defined : μ_m.p.val - μ_n.p.val ≠ 0

structure u_Type (r : Relation α) (x m n : α) [MixSpace α] where
  a : α
  b : α
  eval : M_Type r a b x m n
  h_ab : a ≻[r] b
  hx : x ∈ S r a b
  hm : m ∈ S r a b
  hn : n ∈ S r a b

/-
vNM Theorem: A preference relation on a mixture space satisfies
completeness, transitivity, independence, and continuity,
↔ there exists a utility function u : α → ℝ.
Adapted from Herstein and Milnor (1953) "An Axiomatic Approach to
Measurable Utility" Theorem 8.
-/

theorem vNM_theorem [MixSpace α] (r : Relation α) :
  vNM_axioms r ↔ ∃ u : α → ℝ, utility_function u r := by
  apply Iff.intro
  · -- Forward direction
    intro h_vNM
    rcases h_vNM with ⟨h_complete, h_trans, h_indep, h_cont⟩
    have h_strict_interior := strict_interior r h_indep
    have h_strict_p_consistency := strict_p_consistency r ⟨h_complete, h_indep⟩
    -- By cases: ∃ m, n : α, m ≻ n or ∀ x y : α, x ∼ y
    by_cases h_same : ∀ x y : α, x ∼[r] y
    · -- Case 1: All elements are indifferent
      -- Then u(x) = 0 for all x is a valid utility function
      have h_exists : ∃ u : α → ℝ, utility_function u r := by
        let u := fun x : α => (0 : ℝ)
        have hu_ord : ordinal_consistent u r := by
          intro x y
          constructor
          · intro hxy
            simp [u]
          · intro h_eq
            exact (h_same x y).left
        have hu_plin : p_linear u := by
          intro x y p
          simp [u]
        exact ⟨u, ⟨hu_ord, hu_plin⟩⟩
      exact h_exists
    · -- Case 2: There exist m, n : α, m ≻ n
      have h_exists_elements : ∃ m n : α, m ≻[r] n := by
        rcases Classical.not_forall.mp h_same with ⟨m, h_neg_n⟩
        rcases Classical.not_forall.mp h_neg_n with ⟨n, h_nm⟩
        -- From h_nm : ¬(m ∼ n), we have m ≻ n or n ≻ m
        have h_mn_or_mn : m ≻[r] n ∨ n ≻[r] m := by
          have h_not_or := not_and_or.mp h_nm
          cases h_not_or with
          | inl h_mn => exact Or.inr ⟨(h_complete m n).resolve_left h_mn, h_mn⟩
          | inr h_nm => exact Or.inl ⟨(h_complete m n).resolve_right h_nm, h_nm⟩
        cases h_mn_or_mn with
        | inl h_mn => exact ⟨m, n, h_mn⟩
        | inr h_nm => exact ⟨n, m, h_nm⟩
      rcases h_exists_elements with ⟨m, n, h_mn⟩



      -- Define then the function μ : S(a, b) → ℝ
      -- with μ(a, b, x) = p where a +[p] b ∼ x
      -- Since the definition of μ involves choice, annoyingly we
      -- have to carry the proof of uniqueness around
      have h_unique_cont := unique_continuity r ⟨h_complete, h_trans, h_indep, h_cont⟩
      let μ (a b : α) (h_ab : a ≻[r] b) (x : α) (hx : x ∈ S r a b) : μ_Type r a b x :=
        have h_p : ∃! p : IntervalType, (a +[p] b) ∼[r] x := by
          exact h_unique_cont a x b ⟨h_ab, hx.left, hx.right⟩
        have h_spec := Classical.choose_spec h_p
        ⟨Classical.choose h_p, h_spec.left, h_spec.right⟩

      -- Show that if we have two μ of the same type, then they are equal
      have h_μ_unique : ∀ (a b : α) (x : α)
        (q1 q2 : μ_Type r a b x), q1.p = q2.p := by
        intro a b x q1 q2
        have h_q1_spec_prop : (a +[q1.p]b) ∼[r]x := q1.spec
        have h_q2_spec_unique : ∀ (k : IntervalType), (a +[k]b) ∼[r]x → k = q2.p := q2.unique
        exact h_q2_spec_unique q1.p h_q1_spec_prop

      -- Show that μ is strict ordinal consistent
      have hμ_ord : ∀ (a b : α) (h_ab: a ≻[r] b),
        (∀ (x y : α) (hx : x ∈ S r a b) (hy : y ∈ S r a b),
        ∀ (μ_x : μ_Type r a b x) (μ_y : μ_Type r a b y),
        (x ≻[r] y) ↔ (μ_x.p.1 > μ_y.p.1)) := by
        intro a b h_ab x y hx hy μ_x μ_y
        set h_μ_x := μ_x.spec
        set h_μ_y := μ_y.spec
        -- From x ≻ y ↔ (a +[μ x] b) ≻ (a +[μ y] b)
        have h_μx_μy : x ≻[r] y ↔ (a +[μ_x.p] b) ≻[r] (a +[μ_y.p] b) := by
          exact strict_substitution r h_trans x y (a +[μ_x.p] b) (a +[μ_y.p] b)
            ⟨h_μ_x, h_μ_y⟩
        -- By strict p-consistency, we have
        -- (a +[μ x] b) ≻ (a +[μ y] b) ↔ (μ x > μ y)
        have h_strict_p_cons := h_strict_p_consistency a b h_ab
        have h_μx_gt_μy := h_strict_p_cons μ_x.p μ_y.p
        -- Combine these two
        exact Iff.trans h_μx_μy h_μx_gt_μy

      -- Show that μ is p-linear
      -- First show that if x, y ∈ S(a, b), then x +[p] y ∈ S(a, b)
      have h_mix_in_S : ∀ (a b : α) (x y : α) (hx : x ∈ S r a b) (hy : y ∈ S r a b)
        (p : IntervalType), (x +[p] y) ∈ S r a b := by
        intro a b x y hx hy p
        have hxy := h_complete x y
        cases hxy with
        | inl hxy =>
          -- By partial_interior we have x ≽ x +[p] y ≽ y
          have h_partial_interior := full_partial_interior r ⟨h_complete, h_indep⟩
          have h_x_ge_mix := h_partial_interior x y hxy p
          -- By transitivity we have a ≽ x +[p] y ≽ b
          have h_a_ge_mix : a ≽[r] (x +[p] y) := h_trans a x (x +[p] y) ⟨hx.left, h_x_ge_mix.left⟩
          have h_mix_ge_b : (x +[p] y) ≽[r] b := h_trans (x +[p] y) y b ⟨h_x_ge_mix.right, hy.right⟩
          exact ⟨h_a_ge_mix, h_mix_ge_b⟩
        | inr hxy =>
          -- By partial_interior we have y ≽ x +[p] y ≽ x
          have h_partial_interior := full_partial_interior r ⟨h_complete, h_indep⟩
          have h_y_ge_mix := h_partial_interior y x hxy ⟨1 - p.1, comm_in_Icc p.2⟩
          have h_comm := MixSpace.mix_comm p x y
          rw [←h_comm] at h_y_ge_mix
          -- By transitivity we have a ≽ x +[p] y ≽ b
          have h_a_ge_mix : a ≽[r] (x +[p] y) := h_trans a y (x +[p] y) ⟨hy.left, h_y_ge_mix.left⟩
          have h_mix_ge_b : (x +[p] y) ≽[r] b := h_trans (x +[p] y) x b ⟨h_y_ge_mix.right, hx.right⟩
          exact ⟨h_a_ge_mix, h_mix_ge_b⟩
      -- Now we can show p-linearity
      have hμ_plin : ∀ (a b : α) (x y : α) (hx : x ∈ S r a b) (hy : y ∈ S r a b)
        (p : IntervalType) (μ_x : μ_Type r a b x) (μ_y : μ_Type r a b y)
        (μ_mix : μ_Type r a b (x +[p] y)),
        ∃ (h_mix_in : (x +[p] y) ∈ S r a b), μ_mix.p.1 = p.1 * μ_x.p.1 + (1 - p.1) * μ_y.p.1 := by
        intro a b x y hx hy p μ_x μ_y μ_mix

        -- By h_mix_in_S we have (x +[p] y) ∈ S(a, b)
        have h_mix_in : (x +[p] y) ∈ S r a b := h_mix_in_S a b x y hx hy p

        -- We want to show that μ_mix = p * μ_x + (1-p) * μ_y
        -- By linear_substitution, we have (x +[p] y) ∼ (a +[p * μ_x + (1-p) * μ_y] b)
        have h_x_eq : x ∼[r] (a +[μ_x.p] b) := (indiff_symm r (a +[μ_x.p] b) x) (μ_x.spec)
        have h_y_eq : y ∼[r] (a +[μ_y.p] b) := (indiff_symm r (a +[μ_y.p] b) y) (μ_y.spec)
        have h_mix_eq := by
          exact linear_substitution r ⟨h_complete, h_trans, h_indep⟩ x y a b
            μ_x.p μ_y.p p ⟨h_x_eq, h_y_eq⟩
        have h_mix_eq := (indiff_symm r (x +[p] y) (a +[⟨p.1 * μ_x.p.1 + (1 - p.1) * μ_y.p.1,
          assoc_of_mix_in_Icc μ_x.p.2 μ_y.p.2 p.2⟩] b)) h_mix_eq
        -- By uniqueness of μ, we have μ_mix = p * μ_x + (1-p) * μ_y
        have h_unique := μ_mix.unique
        have h_eq := h_unique (⟨p.1 * μ_x.p.1 + (1 - p.1) * μ_y.p.1,
          assoc_of_mix_in_Icc μ_x.p.2 μ_y.p.2 p.2⟩ : IntervalType) h_mix_eq
        have h_eq_values : μ_mix.1.1 =
          p.1 * μ_x.p.1 + (1 - p.1) * μ_y.p.1 := by
          exact (congrArg Subtype.val h_eq).symm
        exact ⟨h_mix_in, h_eq_values⟩


      -- Finally define M : S(a, b) → ℝ with
      -- M(a, b, x) = μ(a, b, x) - μ(a, b, n) / μ(a, b, m) - μ(a, b, n)
      let M (a b : α) (h_ab : a ≻[r] b) (x : α) (hx : x ∈ S r a b)
        (hm : m ∈ S r a b) (hn : n ∈ S r a b)
        : M_Type r a b x m n :=
        let μ_x := μ a b h_ab x hx
        let μ_m := μ a b h_ab m hm
        let μ_n := μ a b h_ab n hn
        let eval := (μ_x.p.val - μ_n.p.val) / (μ_m.p.val - μ_n.p.val)
        let spec : eval =
          (μ_x.p.val - μ_n.p.val) / (μ_m.p.val - μ_n.p.val) := by rfl
        let defined : μ_m.p.val - μ_n.p.val ≠ 0 := by
          have h_μm_gt_μn := (hμ_ord a b h_ab m n hm hn μ_m μ_n).mp h_mn
          linarith
        ⟨eval, μ_x, μ_m, μ_n, spec, defined⟩

      -- Show that M is strict ordinal consistent
      have hM_ord : ∀ (a b : α) (h_ab: a ≻[r] b),
        (∀ (x y : α) (hx : x ∈ S r a b) (hy : y ∈ S r a b)
        (hm : m ∈ S r a b) (hn: n ∈ S r a b) (M_x : M_Type r a b x m n)
        (M_y : M_Type r a b y m n),
        (x ≻[r] y) ↔ (M_x.eval > M_y.eval)) := by
        intro a b h_ab x y hx hy hm hn M_x M_y
        rw [M_x.spec, M_y.spec]
        -- Unfold the definition of M
        set μ_x_data := M_x.μ_x
        set μ_x := μ_x_data.p
        set μ_m_data := M_x.μ_m
        set μ_m := μ_m_data.p
        set μ_n_data := M_x.μ_n
        set μ_n := μ_n_data.p
        set μ_y_data := M_y.μ_x
        set μ_y := μ_y_data.p
        set μ_m_y_data := M_y.μ_m
        set μ_m_y := μ_m_y_data.p
        set μ_n_y_data := M_y.μ_n
        set μ_n_y := μ_n_y_data.p

        -- First μ_m = μ_m_y and μ_n = μ_n_y since μ is unique
        have h_μm_eq : μ_m = μ_m_y := by
          exact h_μ_unique a b m μ_m_data μ_m_y_data
        have h_μn_eq : μ_n = μ_n_y := by
          exact h_μ_unique a b n μ_n_data μ_n_y_data
        rw [←h_μm_eq, ←h_μn_eq]

        -- Since m ≻ n, we have μ_m > μ_n
        have h_μm_gt_μn := (hμ_ord a b h_ab m n hm hn μ_m_data μ_n_data).mp h_mn

        -- We have to show that x ≻ y ↔ M_x > M_y
        apply Iff.intro
        · -- Forward direction
          -- x ≻ y → M_x > M_y
          intro h_xy
          -- By hμ_ord we have μ_x > μ_y
          have h_μx_gt_μy := (hμ_ord a b h_ab x y hx hy μ_x_data μ_y_data).mp h_xy
          -- Therefore, M_x = (μ_x - μ_n)/((μ_m - μ_n)) > M_y = (μ_y - μ_n_y)/((μ_m_y - μ_n_y))
          have h_Mx_gt_My := by
            have h_numerators : (μ_x.1 - μ_n.1) > (μ_y.1 - μ_n.1) := by
              linarith
            have h_denominator_pos : (μ_m.1 - μ_n.1) > 0 := by
              linarith
            have h_inv_denom_pos : (μ_m.1 - μ_n.1)⁻¹ > 0 := by
              exact inv_pos.mpr h_denominator_pos
            exact (mul_lt_mul_of_pos_right h_numerators h_inv_denom_pos)
          exact h_Mx_gt_My
        · -- Backward direction
          -- M_x > M_y → x ≻ y
          intro h_Mx_gt_My

          -- We have (μ_x - μ_n)/(μ_m - μ_n) > (μ_y - μ_n)/(μ_m - μ_n)
          -- From this we can conclude that μ_x > μ_y
          have h_μx_gt_μy : μ_x.1 > μ_y.1 := by
            have h_numerator_gt : (μ_x.1 - μ_n.1) > (μ_y.1 - μ_n.1) := by
              have h_denominator_pos : (μ_m.1 - μ_n.1) > 0 := by
                linarith
              have h_inv_denom_pos : (μ_m.1 - μ_n.1)⁻¹ > 0 := by
                exact inv_pos.mpr h_denominator_pos
              have h := (mul_lt_mul_of_pos_right h_Mx_gt_My h_inv_denom_pos)
              field_simp at h
              exact h
            linarith

          -- By hμ_ord we have x ≻ y
          exact (hμ_ord a b h_ab x y hx hy μ_x_data μ_y_data).mpr h_μx_gt_μy

      -- Show that M is p-linear
      have hM_plin : ∀ (a b : α) (x y : α) (hx : x ∈ S r a b) (hy : y ∈ S r a b)
        (p : IntervalType) (hm : m ∈ S r a b) (hn: n ∈ S r a b)
        (M_x : M_Type r a b x m n) (M_y : M_Type r a b y m n) (M_mix : M_Type r a b (x +[p] y) m n),
        M_mix.eval = p.1 * M_x.eval + (1 - p.1) * M_y.eval := by
        intro a b x y hx hy p hm hn M_x M_y M_mix
        rw [M_mix.spec, M_x.spec, M_y.spec]

        -- Unfold the definition of M
        set h_μm_ne_μn := M_x.defined
        set μ_x_data := M_x.μ_x
        set μ_x := μ_x_data.1
        set μ_m_data := M_x.μ_m
        set μ_m := μ_m_data.1
        set μ_n_data := M_x.μ_n
        set μ_n := μ_n_data.1
        set μ_y_data := M_y.μ_x
        set μ_y := μ_y_data.1
        set μ_m_y_data := M_y.μ_m
        set μ_m_y := μ_m_y_data.1
        set μ_n_y_data := M_y.μ_n
        set μ_n_y := μ_n_y_data.1
        set μ_mix_data := M_mix.μ_x
        set μ_mix := μ_mix_data.1
        set μ_m_mix_data := M_mix.μ_m
        set μ_m_mix := μ_m_mix_data.1
        set μ_n_mix_data := M_mix.μ_n
        set μ_n_mix := μ_n_mix_data.1


        -- First , μ_m = μ_m_y = μ_m_mix and μ_n = μ_n_y = μ_n_mix since μ is unique
        have h_μm_eq : μ_m = μ_m_y := by
          exact h_μ_unique a b m μ_m_data μ_m_y_data
        have h_μn_eq : μ_n = μ_n_y := by
          exact h_μ_unique a b n μ_n_data μ_n_y_data
        have h_μm_eq_mix : μ_m = μ_m_mix := by
          exact h_μ_unique a b m μ_m_data μ_m_mix_data
        have h_μn_eq_mix : μ_n = μ_n_mix := by
          exact h_μ_unique a b n μ_n_data μ_n_mix_data
        rw [←h_μm_eq, ←h_μn_eq, ←h_μm_eq_mix, ←h_μn_eq_mix]

        -- By μ being p-linear we have μ_mix.1 = p.1 * μ_x.1 + (1 - p.1) * μ_y.1
        have h_μ_mix_plin := hμ_plin a b x y hx hy p μ_x_data μ_y_data μ_mix_data
        have h_μ_mix_eq : μ_mix.1 = p.1 * μ_x.1 + (1 - p.1) * μ_y.1 := by
          rcases h_μ_mix_plin with ⟨h_mix_in, h_eq⟩
          exact h_eq
        rw [h_μ_mix_eq]

        -- Therefore, M_mix = p * M_x + (1-p) * M_y
        field_simp [M_x.defined]
        ring_nf

      -- Since it is ordinal consistent, it is equal for indifference
      have hM_indiff_cons : ∀ (a b : α) (h_ab: a ≻[r] b),
        (∀ (x y : α) (hx : x ∈ S r a b) (hy : y ∈ S r a b)
        (hm : m ∈ S r a b) (hn: n ∈ S r a b) (M_x : M_Type r a b x m n) (M_y : M_Type r a b y m n),
        (x ∼[r] y) ↔ (M_x.eval = M_y.eval)) := by
        intro a b h_ab x y hx hy hm hn M_x M_y
        apply Iff.intro
        · -- Forward direction
          -- x ∼ y → M_x = M_y
          intro h_xy
          have h_neg_x_gt_y : ¬(x ≻[r] y) := by
            intro h_x_gt_y
            exact absurd h_xy.right h_x_gt_y.right
          have h_neg_y_gt_x : ¬(y ≻[r] x) := by
            intro h_y_gt_x
            exact absurd h_xy.left h_y_gt_x.right
          have h_Mx_ge_My : ¬(M_x.1 > M_y.1) := by
            intro h_Mx_gt_My
            exact absurd ((hM_ord a b h_ab x y hx hy hm hn M_x M_y).mpr h_Mx_gt_My) h_neg_x_gt_y
          have h_My_ge_Mx : ¬(M_y.1 > M_x.1) := by
            intro h_My_gt_Mx
            exact absurd ((hM_ord a b h_ab y x hy hx hm hn M_y M_x).mpr h_My_gt_Mx) h_neg_y_gt_x
          linarith
        · -- Backward direction
          -- M_x = M_y → x ∼ y
          intro h_Mx_eq_My
          have h_neg_Mx_gt_My : ¬(M_x.1 > M_y.1) := by
            intro h_Mx_gt_My
            exact absurd h_Mx_eq_My (ne_of_gt h_Mx_gt_My)
          have h_neg_My_gt_Mx : ¬(M_y.1 > M_x.1) := by
            intro h_My_gt_Mx
            exact absurd h_Mx_eq_My.symm (ne_of_gt h_My_gt_Mx)
          have h_neg_x_gt_y : ¬(x ≻[r] y) := by
            intro h_x_gt_y
            exact absurd ((hM_ord a b h_ab x y hx hy hm hn M_x M_y).mp h_x_gt_y) h_neg_Mx_gt_My
          have h_neg_y_gt_x : ¬(y ≻[r] x) := by
            intro h_y_gt_x
            exact absurd ((hM_ord a b h_ab y x hy hx hm hn M_y M_x).mp h_y_gt_x) h_neg_My_gt_Mx
          have h_xy : x ≽[r] y := by
            have h_complete_xy := h_complete x y
            cases h_complete_xy with
            | inl h_xy => exact h_xy
            | inr h_yx => exact not_not.mp ((not_and_or.mp h_neg_y_gt_x).resolve_left
              (not_not.mpr h_yx))
          have h_yx : y ≽[r] x := by
            have h_complete_yx := h_complete y x
            cases h_complete_yx with
            | inl h_yx => exact h_yx
            | inr h_xy => exact not_not.mp ((not_and_or.mp h_neg_x_gt_y).resolve_left
              (not_not.mpr h_xy))
          exact ⟨h_xy, h_yx⟩

      -- M_ab(m) = 1
      have hM_m : ∀ (a b : α)
        (hm : m ∈ S r a b) (hn: n ∈ S r a b) (M_m : M_Type r a b m m n),
        M_m.eval = 1 := by
        intro a b hm hn M_m
        rw [M_m.spec]
        set h_μm_ne_μn := M_m.defined
        set μ_m_data := M_m.μ_x
        set μ_m := μ_m_data.1
        set μ_m_m_data := M_m.μ_m
        set μ_m_m := μ_m_m_data.1
        set μ_n_data := M_m.μ_n
        set μ_n := μ_n_data.1

        -- By uniqueness of μ, we have μ_m = μ_m_m
        have h_μm_eq : μ_m = μ_m_m := by
          exact h_μ_unique a b m μ_m_data μ_m_m_data
        rw [←h_μm_eq]
        rw [←h_μm_eq] at h_μm_ne_μn

        -- So M(m) = (μ_m - μ_n)/(μ_m - μ_n) = 1
        exact div_self (h_μm_ne_μn)

      -- M_ab(n) = 0
      have hM_n : ∀ (a b : α)
        (hm : m ∈ S r a b) (hn: n ∈ S r a b) (M_n : M_Type r a b n m n),
        M_n.eval = 0 := by
        intro a b hm hn M_n
        rw [M_n.spec]
        set h_μm_ne_μn := M_n.defined
        set μ_n_data := M_n.μ_x
        set μ_n := μ_n_data.1
        set μ_m_data := M_n.μ_m
        set μ_m := μ_m_data.1
        set μ_n_n_data := M_n.μ_n
        set μ_n_n := μ_n_n_data.1

        -- By uniqueness of μ, we have μ_n = μ_n_n
        have h_μn_eq : μ_n = μ_n_n := by
          exact h_μ_unique a b n μ_n_data μ_n_n_data
        rw [←h_μn_eq]
        rw [←h_μn_eq] at h_μm_ne_μn

        -- So M(n) = (μ_n - μ_n)/(μ_m - μ_n) = 0
        rw [sub_self, zero_div]

      -- With this we can also show that M does not depend on the choice of a, b
      have hM_indep_ab : ∀ (a1 b1 a2 b2) (h_a1b1 : a1 ≻[r] b1) (h_a2b2 : a2 ≻[r] b2),
        ∀ (x : α) (hx1 : x ∈ S r a1 b1) (hx2 : x ∈ S r a2 b2)
        (hm1 : m ∈ S r a1 b1) (hm2 : m ∈ S r a2 b2)
        (hn1 : n ∈ S r a1 b1) (hn2 : n ∈ S r a2 b2)
        (M1 : M_Type r a1 b1 x m n) (M2 : M_Type r a2 b2 x m n),
        M1.eval = M2.eval := by
        intro a1 b1 a2 b2 h_a1b1 h_a2b2 x hx1 hx2 hm1 hm2 hn1 hn2 M1 M2

        -- M1(m) = M2(m) = 1 and M1(n) = M2(n) = 0
        let M1_m := M a1 b1 h_a1b1 m hm1 hm1 hn1
        let M1_n := M a1 b1 h_a1b1 n hn1 hm1 hn1
        have h_M1_m : M1_m.eval = 1 := by
          exact hM_m a1 b1 hm1 hn1 M1_m
        have h_M1_n : M1_n.eval = 0 := by
          exact hM_n a1 b1 hm1 hn1 M1_n
        let M2_m := M a2 b2 h_a2b2 m hm2 hm2 hn2
        let M2_n := M a2 b2 h_a2b2 n hn2 hm2 hn2
        have h_M2_m : M2_m.eval = 1 := by
          exact hM_m a2 b2 hm2 hn2 M2_m
        have h_M2_n : M2_n.eval = 0 := by
          exact hM_n a2 b2 hm2 hn2 M2_n

        by_cases hx_m : x ≽[r] m
        · -- Case 1: x ≽ m
          -- Then since m ≻ n, we have x ≻ n
          have hx_n : x ≻[r] n := by
            have hx_n_ge : x ≽[r] n := h_trans x m n ⟨hx_m, h_mn.left⟩
            have h_not_nx_ge : ¬(n ≽[r] x) := by
              intro h_nx_ge
              exact h_mn.right (h_trans n x m ⟨h_nx_ge, hx_m⟩)
            exact ⟨hx_n_ge, h_not_nx_ge⟩
          -- By continuity x ≽ m ≻ n, ∃ k, m ~ x +[k] n
          have h_m_xkn := h_cont x m n ⟨hx_m, h_mn.left⟩
          rcases h_m_xkn with ⟨k, h_k⟩
          -- Also k ≠ 0
          have h_k_nonzero : k.1 ≠ 0 := by
            intro h_k_zero
            rw [mix_zero k x n h_k_zero] at h_k
            exact absurd h_k.left h_mn.right

          -- (x +[k] n) ∈ S(a1, b1) and S(a2, b2)
          have h_xkn_in_S1 : (x +[k] n) ∈ S r a1 b1 := by
            exact h_mix_in_S a1 b1 x n hx1 hn1 k
          have h_xkn_in_S2 : (x +[k] n) ∈ S r a2 b2 := by
            exact h_mix_in_S a2 b2 x n hx2 hn2 k
          -- M1(x +[k] n) and M2(x +[k] n) are well defined
          let M1_xkn := M a1 b1 h_a1b1 (x +[k] n) h_xkn_in_S1 hm1 hn1
          let M2_xkn := M a2 b2 h_a2b2 (x +[k] n) h_xkn_in_S2 hm2 hn2

          -- Then by indiff consistent M1(m) = M1(x +[k] n) and M2(m) = M2(x +[k] n)
          have h_M1_m_xkn := (hM_indiff_cons a1 b1 h_a1b1 (x +[k] n)
            m h_xkn_in_S1 hm1 hm1 hn1 M1_xkn M1_m).mp h_k
          have h_M2_m_xkn := (hM_indiff_cons a2 b2 h_a2b2 (x +[k] n)
            m h_xkn_in_S2 hm2 hm2 hn2 M2_xkn M2_m).mp h_k
          -- Then by p-linearity M1(x +[k] n) = k * M1(x) + (1-k) * M1(n)
          -- and M2(x +[k] n) = k * M2(x) + (1-k) * M2(n)
          have h_M1_xkn_plin := hM_plin a1 b1 x n hx1 hn1 k hm1 hn1 M1 M1_n M1_xkn
          rw [h_M1_m_xkn] at h_M1_xkn_plin
          have h_M2_xkn_plin := hM_plin a2 b2 x n hx2 hn2 k hm2 hn2 M2 M2_n M2_xkn
          rw [h_M2_m_xkn] at h_M2_xkn_plin
          -- Since M1(m) = M2(m) = 1 and M1(n) = M2(n) = 0,
          -- we have M1(x) * k = 1 and M2(x) * k = 1
          have h_M1_eq_1k : 1 = k.1 * M1.eval := by
            rw [h_M1_m, h_M1_n] at h_M1_xkn_plin
            simp only [mul_zero, add_zero] at h_M1_xkn_plin
            exact h_M1_xkn_plin
          have h_M2_eq_1k : 1 = k.1 * M2.eval := by
            rw [h_M2_m, h_M2_n] at h_M2_xkn_plin
            simp only [mul_zero, add_zero] at h_M2_xkn_plin
            exact h_M2_xkn_plin
          -- Since k ≠ 0, we can conclude that M1(x) = M2(x)
          have h_M1_eq_M2 : M1.eval = M2.eval := by
            have h_M1_eq_M2_k : k.1 * M1.eval = k.1 * M2.eval := by
              set k_val := (k.1 : ℝ)
              rw [h_M1_eq_1k] at h_M2_eq_1k
              exact h_M2_eq_1k
            exact mul_left_cancel₀ h_k_nonzero h_M1_eq_M2_k
          exact h_M1_eq_M2
        · -- Case 2: ¬(x ≽ m)
          by_cases hx_n : n ≽[r] x
          · -- Subcase 2.1: n ≽ x
            -- Then since m ≻ n, we have m ≻ x
            have hm_x : m ≻[r] x := by
              have hm_x_ge : m ≽[r] x := h_trans m n x ⟨h_mn.left, hx_n⟩
              have h_not_xm_ge : ¬(x ≽[r] m) := by
                intro h_xm_ge
                exact h_mn.right (h_trans n x m ⟨hx_n, h_xm_ge⟩)
              exact ⟨hm_x_ge, h_not_xm_ge⟩
            -- By continuity m ≻ n ≽ x, ∃ k, n ~ m +[k] x
            have h_n_mkx := h_cont m n x ⟨h_mn.left, hx_n⟩
            rcases h_n_mkx with ⟨k, h_k⟩
            -- Also k ≠ 1
            have h_k_nonone : k.1 ≠ 1 := by
              intro h_k_one
              rw [MixSpace.mix_one k m x h_k_one] at h_k
              exact absurd h_k.right h_mn.right


            -- (m +[k] x) ∈ S(a1, b1) and S(a2, b2)
            have h_mkx_in_S1 : (m +[k] x) ∈ S r a1 b1 := by
              exact h_mix_in_S a1 b1 m x hm1 hx1 k
            have h_mkx_in_S2 : (m +[k] x) ∈ S r a2 b2 := by
              exact h_mix_in_S a2 b2 m x hm2 hx2 k
            -- M1(m +[k] x) and M2(m +[k] x) are well defined
            let M1_mkx := M a1 b1 h_a1b1 (m +[k] x) h_mkx_in_S1 hm1 hn1
            let M2_mkx := M a2 b2 h_a2b2 (m +[k] x) h_mkx_in_S2 hm2 hn2

            -- Then by indiff consistent M1(n) = M1(m +[k] x) and M2(m) = M2(m +[k] x)
            have h_M1_n_mkx := (hM_indiff_cons a1 b1 h_a1b1 (m +[k] x) n
              h_mkx_in_S1 hn1 hm1 hn1 M1_mkx M1_n).mp h_k
            have h_M2_n_mkx := (hM_indiff_cons a2 b2 h_a2b2 (m +[k] x) n
              h_mkx_in_S2 hn2 hm2 hn2 M2_mkx M2_n).mp h_k
            -- Then by p-linearity M1(m +[k] x) = k * M1(m) + (1-k) * M1(x)
            -- and M2(m +[k] x) = k * M2(m) + (1-k) * M2(x)
            have h_M1_mkx_plin := hM_plin a1 b1 m x hm1 hx1 k hm1 hn1 M1_m M1 M1_mkx
            rw [h_M1_n_mkx] at h_M1_mkx_plin
            have h_M2_mkx_plin := hM_plin a2 b2 m x hm2 hx2 k hm2 hn2 M2_m M2 M2_mkx
            rw [h_M2_n_mkx] at h_M2_mkx_plin
            -- Since M1(m) = M2(m) = 1 and M1(n) = M2(n) = 0,
            -- we have k + (1-k) M1(x) = 0 and k + (1-k) M1(x) = 0
            have h_M1_eq_1k : 0 = k.1 + (1-k.1) * M1.eval := by
              rw [h_M1_m, h_M1_n] at h_M1_mkx_plin
              simp only [mul_one] at h_M1_mkx_plin
              exact h_M1_mkx_plin
            have h_M2_eq_1k : 0 = k.1 + (1-k.1) * M2.eval := by
              rw [h_M2_m, h_M2_n] at h_M2_mkx_plin
              simp only [mul_one] at h_M2_mkx_plin
              exact h_M2_mkx_plin
            -- Since k ≠ 1, we can conclude that M1(x) = M2(x)
            have h_M1_eq_M2 : M1.eval = M2.eval := by
              have h_M1_eq_M2_k : (1 - k.1) * M1.eval = (1 - k.1) * M2.eval := by
                set k_val := (k.1 : ℝ)
                rw [h_M1_eq_1k] at h_M2_eq_1k
                exact add_left_cancel h_M2_eq_1k
              have h_one_minus_k_nonzero : (1 - k.1) ≠ 0 := by
                set k_val := (k.1 : ℝ)
                intro h_one_minus_k_zero
                have h_k_one : k.1 = 1 := by
                  linarith
                exact absurd h_k_one h_k_nonone
              exact mul_left_cancel₀ h_one_minus_k_nonzero h_M1_eq_M2_k
            exact h_M1_eq_M2

          · -- Subcase 2.2: ¬(n ≽ x)
            -- Then since x ≽ m is false and n ≽ x is false,
            -- by completeness we have m ≽ x ≽ n
            have hm_x : m ≽[r] x := by
              exact (h_complete x m).resolve_left hx_m
            have hx_n : x ≽[r] n := by
              exact (h_complete x n).resolve_right hx_n

            -- By continuity m ≽ x ≽ n,  ∃ k, x ~ m +[k] n
            have h_n_mkx := h_cont m x n ⟨hm_x, hx_n⟩
            rcases h_n_mkx with ⟨k, h_k⟩

            -- (m +[k] n) ∈ S(a1, b1) and S(a2, b2)
            have h_mkn_in_S1 : (m +[k] n) ∈ S r a1 b1 := by
              exact h_mix_in_S a1 b1 m n hm1 hn1 k
            have h_mkn_in_S2 : (m +[k] n) ∈ S r a2 b2 := by
              exact h_mix_in_S a2 b2 m n hm2 hn2 k
            -- M1(m +[k] n) and M2(m +[k] n) are well defined
            let M1_mkn := M a1 b1 h_a1b1 (m +[k] n) h_mkn_in_S1 hm1 hn1
            let M2_mkn := M a2 b2 h_a2b2 (m +[k] n) h_mkn_in_S2 hm2 hn2

            -- Then by indiff consistent M1(x) = M1(m +[k] n) and M2(x) = M2(m +[k] n)
            have h_M1_x_mkn := (hM_indiff_cons a1 b1 h_a1b1 (m +[k] n) x
              h_mkn_in_S1 hx1 hm1 hn1 M1_mkn M1).mp h_k
            have h_M2_x_mkn := (hM_indiff_cons a2 b2 h_a2b2 (m +[k] n) x
              h_mkn_in_S2 hx2 hm2 hn2 M2_mkn M2).mp h_k
            -- Then by p-linearity M1(m +[k] n) = k * M1(m) + (1-k) * M1(n)
            -- and M2(m +[k] n) = k * M2(m) + (1-k) * M2(n)
            have h_M1_mkn_plin := hM_plin a1 b1 m n hm1 hn1 k hm1 hn1 M1_m M1_n M1_mkn
            rw [h_M1_x_mkn] at h_M1_mkn_plin
            have h_M2_mkn_plin := hM_plin a2 b2 m n hm2 hn2 k hm2 hn2 M2_m M2_n M2_mkn
            rw [h_M2_x_mkn] at h_M2_mkn_plin
            -- Since M1(m) = M2(m) and M1(n) = M2(n),
            -- we have M1(x) = M2(x)
            have h_M1_eq_M2 : M1.eval = M2.eval := by
              have h_M1m_eq_M2m : M1_m.eval = M2_m.eval := by
                rw [h_M1_m, h_M2_m]
              have h_M1n_eq_M2n : M1_n.eval = M2_n.eval := by
                rw [h_M1_n, h_M2_n]
              rw [←h_M1m_eq_M2m, ←h_M1n_eq_M2n, ←h_M1_mkn_plin] at h_M2_mkn_plin
              exact h_M2_mkn_plin.symm
            exact h_M1_eq_M2

      -- Then, show that for any x, there exist a, b with a ≽ x, m, n ≽ b and a ≻ b
      have h_xyz_in_ab : ∀ x : α, ∃ a b : α, a ≽[r] x ∧ a ≽[r] m ∧ a ≽[r] n ∧
        x ≽[r] b ∧ m ≽[r] b ∧ n ≽[r] b ∧ a ≻[r] b := by
        intro x
        have hxm := h_complete x m
        have hxn := h_complete x n
        have hmn := h_complete m n
        -- First, there is a highest a and lowest element b between these three
        have h_largest: ∃ w, w ≽[r] x ∧ w ≽[r] m ∧ w ≽[r] n := by
          exact highest_element r ⟨h_complete, h_trans⟩ x m n
        have h_smallest: ∃ w, x ≽[r] w ∧ m ≽[r] w ∧ n ≽[r] w := by
          exact lowest_element r ⟨h_complete, h_trans⟩ x m n
        rcases h_largest with ⟨a, ha_x, ha_m, ha_n⟩
        rcases h_smallest with ⟨b, hx_b, hm_b, hn_b⟩
        -- a ≽ m ≻ n ≽ b, so a ≻ b
        have ha_b : a ≻[r] b := by
          have ha_n_ge : a ≽[r] n := h_trans a m n ⟨ha_m, h_mn.left⟩
          have ha_b_ge : a ≽[r] b := h_trans a n b ⟨ha_n, hn_b⟩
          have h_not_ba_ge : ¬(b ≽[r] a) := by
            intro h_ba_ge
            have h_na_ge : n ≽[r] a := h_trans n b a ⟨hn_b, h_ba_ge⟩
            exact h_mn.right (h_trans n a m ⟨h_na_ge, ha_m⟩)
          exact ⟨ha_b_ge, h_not_ba_ge⟩
        exact ⟨a, b, ha_x, ha_m, ha_n, hx_b, hm_b, hn_b, ha_b⟩

      -- This needs to be defined this way for lean to understand the choose
      have h_xyz_ab_pair : ∀ x : α, ∃ ab : α × α,
         ab.1 ≽[r] x ∧ ab.1 ≽[r] m ∧ ab.1 ≽[r] n ∧
          x ≽[r] ab.2 ∧ m ≽[r] ab.2 ∧ n ≽[r] ab.2 ∧ ab.1 ≻[r] ab.2 := by
        intro x
        rcases h_xyz_in_ab x with ⟨a, b, ha_x, ha_m, ha_n, hx_b, hm_b, hn_b, ha_b⟩
        exact ⟨(a, b), ha_x, ha_m, ha_n, hx_b, hm_b, hn_b, ha_b⟩
      let ab_type (x : α) := {ab : α × α //
        ab.1 ≽[r] x ∧ ab.1 ≽[r] m ∧ ab.1 ≽[r] n ∧
        x ≽[r] ab.2 ∧ m ≽[r] ab.2 ∧ n ≽[r] ab.2 ∧ ab.1 ≻[r] ab.2}
      let ab (r: Relation α) (x : α) : ab_type x :=
        let h_exists := h_xyz_ab_pair x
        ⟨Classical.choose (h_exists), Classical.choose_spec (h_exists)⟩

      -- Choose then a and b s.t. a ≽ x, m, n ≽ b and a ≽ b
      let u_const (x : α) : u_Type r x m n :=
        let ab_pair := ab r x
        let a := ab_pair.1.1
        let b := ab_pair.1.2
        let ⟨ha_x, ha_m, ha_n, hx_b, hm_b, hn_b, ha_b⟩ := ab_pair.2
        let hx_in_ab : x ∈ S r a b := ⟨ha_x, hx_b⟩
        let hm_in_ab : m ∈ S r a b := ⟨ha_m, hm_b⟩
        let hn_in_ab : n ∈ S r a b := ⟨ha_n, hn_b⟩
        ⟨a, b, M a b ha_b x ⟨ha_x, hx_b⟩ hm_in_ab hn_in_ab,
        ha_b, hx_in_ab, hm_in_ab, hn_in_ab⟩

      let u (x : α) : ℝ := (u_const x).eval.eval

      -- Show that u is ordinal consistent
      have hu_ord_cons : ordinal_consistent u r := by

        -- First gonna show it is strict ordinal consistent
        have hu_strict_ord_cons : ordinal_consistent_strict u (strict r) := by
          intro x y
          -- The biggest challenge is that each u x and u y are picking different a and b
          -- so we need to get a3 and b3 to compute M3(x) and M3(y) and compare it there
          set ux := u_const x
          set uy := u_const y
          set a1 := ux.a
          set b1 := ux.b
          set a2 := uy.a
          set b2 := uy.b
          set h_a1b1 := ux.h_ab
          set h_a2b2 := uy.h_ab
          set hx1 := ux.hx
          set hy1 := uy.hx
          set hm1 := ux.hm
          set hn1 := ux.hn
          set hm2 := uy.hm
          set hn2 := uy.hn

          -- Either a1 ≽ a2 or a2 ≽ a1
          have h_a_max : ∃ w, w ≽[r] a1 ∧ w ≽[r] a2 := by
            by_cases h_a1a2 : a1 ≽[r] a2
            · exact ⟨a1, ⟨(h_complete a1 a1).elim id id, h_a1a2⟩⟩
            · have h_a2a1 : a2 ≽[r] a1 := by
                exact (h_complete a2 a1).resolve_right h_a1a2
              exact ⟨a2, ⟨h_a2a1 ,(h_complete a2 a2).elim id id⟩⟩

          -- Either b1 ≽ b2 or b2 ≽ b1
          have h_b_min : ∃ w, b1 ≽[r] w ∧ b2 ≽[r] w := by
            by_cases h_b1b2 : b1 ≽[r] b2
            · exact ⟨b2, ⟨h_b1b2, (h_complete b2 b2).elim id id⟩⟩
            · have h_b2b1 : b2 ≽[r] b1 := by
                exact (h_complete b2 b1).resolve_right h_b1b2
              exact ⟨b1, ⟨(h_complete b1 b1).elim id id, h_b2b1⟩⟩

          rcases h_a_max with ⟨a3, ha3_a1, ha3_a2⟩
          rcases h_b_min with ⟨b3, hb1_b3, hb2_b3⟩
          -- Now a3 ≽ a1, a2 and b1, b2 ≽ b3
          -- So a3 ≻ b3
          have h_a3b3 : a3 ≻[r] b3 := by
            have ha3_b3_ge : a3 ≽[r] b3 := by
              have ha3_b2 : a3 ≽[r] b2 := h_trans a3 a2 b2 ⟨ha3_a2, h_a2b2.left⟩
              exact h_trans a3 b2 b3 ⟨ha3_b2, hb2_b3⟩
            have h_not_b3a3_ge : ¬(b3 ≽[r] a3) := by
              intro h_b3a3_ge
              have h_b1a3_ge : b1 ≽[r] a3 := h_trans b1 b3 a3 ⟨hb1_b3, h_b3a3_ge⟩
              exact h_a1b1.right (h_trans b1 a3 a1 ⟨h_b1a3_ge, ha3_a1⟩)
            exact ⟨ha3_b3_ge, h_not_b3a3_ge⟩
          -- So x, y ∈ S(a3, b3)
          have hx3 : x ∈ S r a3 b3 := by
            exact ⟨h_trans a3 a1 x ⟨ha3_a1, hx1.left⟩, h_trans x b1 b3 ⟨hx1.right, hb1_b3⟩⟩
          have hy3 : y ∈ S r a3 b3 := by
            exact ⟨h_trans a3 a2 y ⟨ha3_a2, hy1.left⟩, h_trans y b2 b3 ⟨hy1.right, hb2_b3⟩⟩
          -- And m, n ∈ S(a3, b3)
          have hm3 : m ∈ S r a3 b3 := by
            exact ⟨h_trans a3 a1 m ⟨ha3_a1, hm1.left⟩, h_trans m b1 b3 ⟨hm1.right, hb1_b3⟩⟩
          have hn3 : n ∈ S r a3 b3 := by
            exact ⟨h_trans a3 a1 n ⟨ha3_a1, hn1.left⟩, h_trans n b1 b3 ⟨hn1.right, hb1_b3⟩⟩

          -- So M3(x) and M3(y) are defined
          let M3_x := M a3 b3 h_a3b3 x hx3 hm3 hn3
          let M3_y := M a3 b3 h_a3b3 y hy3 hm3 hn3

          -- Now we have x ≻ y ↔ M3(x) > M3(y)
          have h_xy_iff_M3 : (x ≻[r] y) ↔ (M3_x.eval > M3_y.eval) := by
            exact hM_ord a3 b3 h_a3b3 x y hx3 hy3 hm3 hn3 M3_x M3_y

          -- Finally, u x = M3(x) and u y = M3(y)
          have hu_x_eq_M3x : u x = M3_x.eval := by
            -- Unfold u x
            dsimp [u]
            -- Unfold u_const x
            dsimp [u_const]
            -- Need to show that M1(x) = M3(x)
            have h_M13x_eq := by
              exact hM_indep_ab a1 b1 a3 b3 h_a1b1 h_a3b3 x hx1 hx3 hm1 hm3 hn1 hn3 ux.eval M3_x
            rw [h_M13x_eq]
          have hu_y_eq_M3y : u y = M3_y.eval := by
            -- Unfold u y
            dsimp [u]
            -- Unfold u_const y
            dsimp [u_const]
            -- Need to show that M1(y) = M3(y)
            have h_M13y_eq := by
              exact hM_indep_ab a2 b2 a3 b3 h_a2b2 h_a3b3 y hy1 hy3 hm2 hm3 hn2 hn3 uy.eval M3_y
            rw [h_M13y_eq]

          -- Combine all together
          rw [←hu_x_eq_M3x, ←hu_y_eq_M3y] at h_xy_iff_M3
          exact h_xy_iff_M3

        -- Now show ordinal consistency from strict ordinal consistency
        exact (c_strict_ordinal_consistent_iff_consistent h_complete).mpr hu_strict_ord_cons

      -- Show that u is p-linear
      have hu_plin : p_linear u := by
        intro x y k
        -- Similar to the ordinal consistency proof, we need to get a4 and b4 to
        -- compute M4(x +[k]p), M4(x) and M4(y) and compare it there
        set ux := u_const x
        set uy := u_const y
        set uk := u_const (x +[k] y)
        set a1 := ux.a
        set b1 := ux.b
        set h_a1b1 := ux.h_ab
        set hx1 := ux.hx
        set hm1 := ux.hm
        set hn1 := ux.hn
        set a2 := uy.a
        set b2 := uy.b
        set h_a2b2 := uy.h_ab
        set hy2 := uy.hx
        set hm2 := uy.hm
        set hn2 := uy.hn
        set a3 := uk.a
        set b3 := uk.b
        set h_a3b3 := uk.h_ab
        set hk3 := uk.hx
        set hm3 := uk.hm
        set hn3 := uk.hn

        -- First, pick up the highest a and lowest b among these three pairs
        have h_a4_ex : ∃ w, w ≽[r] a1 ∧ w ≽[r] a2 ∧ w ≽[r] a3 := by
          exact highest_element r ⟨h_complete, h_trans⟩ a1 a2 a3
        have h_b4_ex : ∃ w, b1 ≽[r] w ∧ b2 ≽[r] w ∧ b3 ≽[r] w := by
          exact lowest_element r ⟨h_complete, h_trans⟩ b1 b2 b3
        rcases h_a4_ex with ⟨a4, ha4_a1, ha4_a2, ha4_a3⟩
        rcases h_b4_ex with ⟨b4, hb1_b4, hb2_b4, hb3_b4⟩
        -- Now a4 ≽ a1, a2, a3 and b1, b2, b3 ≽ b4
        -- So a4 ≻ b4
        have h_a4b4 : a4 ≻[r] b4 := by
          have ha4_b4_ge : a4 ≽[r] b4 := by
            have ha4_b3 : a4 ≽[r] b3 := h_trans a4 a3 b3 ⟨ha4_a3, uk.h_ab.left⟩
            exact h_trans a4 b3 b4 ⟨ha4_b3, hb3_b4⟩
          have h_not_b4a4_ge : ¬(b4 ≽[r] a4) := by
            intro h_b4a4_ge
            have h_b1a4_ge : b1 ≽[r] a4 := h_trans b1 b4 a4 ⟨hb1_b4, h_b4a4_ge⟩
            exact h_a1b1.right (h_trans b1 a4 a1 ⟨h_b1a4_ge, ha4_a1⟩)
          exact ⟨ha4_b4_ge, h_not_b4a4_ge⟩
        -- So x, y, x +[k] y ∈ S(a4, b4)
        have hx4 : x ∈ S r a4 b4 := by
          exact ⟨h_trans a4 a1 x ⟨ha4_a1, ux.hx.left⟩, h_trans x b1 b4 ⟨ux.hx.right, hb1_b4⟩⟩
        have hy4 : y ∈ S r a4 b4 := by
          exact ⟨h_trans a4 a2 y ⟨ha4_a2, uy.hx.left⟩, h_trans y b2 b4 ⟨uy.hx.right, hb2_b4⟩⟩
        have hk4 : (x +[k] y) ∈ S r a4 b4 := by
          exact ⟨h_trans a4 a3 (x +[k] y) ⟨ha4_a3, uk.hx.left⟩,
            h_trans (x +[k] y) b3 b4 ⟨uk.hx.right, hb3_b4⟩⟩
        -- So m, n ∈ S(a4, b4)
        have hm4 : m ∈ S r a4 b4 := by
          exact ⟨h_trans a4 a1 m ⟨ha4_a1, ux.hm.left⟩, h_trans m b1 b4 ⟨ux.hm.right, hb1_b4⟩⟩
        have hn4 : n ∈ S r a4 b4 := by
          exact ⟨h_trans a4 a1 n ⟨ha4_a1, ux.hn.left⟩, h_trans n b1 b4 ⟨ux.hn.right, hb1_b4⟩⟩

        -- So M4(x), M4(y) and M4(x +[k] y) are defined
        let M4_x := M a4 b4 h_a4b4 x hx4 hm4 hn4
        let M4_y := M a4 b4 h_a4b4 y hy4 hm4 hn4
        let M4_k := M a4 b4 h_a4b4 (x +[k] y) hk4 hm4 hn4

        -- Now we have M4(x +[k] y) = k * M4(x) + (1-k) * M4(y)
        have h_plin_M4 : M4_k.eval = k.1 * M4_x.eval + (1 - k.1) * M4_y.eval := by
          exact hM_plin a4 b4 x y hx4 hy4 k hm4 hn4 M4_x M4_y M4_k

        -- Finally, u x = M4(x), u y = M4(y) and u (x +[k] y) = M4(x +[k] y)
        have hu_x_eq_M4x : u x = M4_x.eval := by
          -- Unfold u x
          dsimp [u]
          -- Unfold u_const x
          dsimp [u_const]
          -- Need to show that M1(x) = M4(x)
          have h_M14x_eq := by
            exact hM_indep_ab a1 b1 a4 b4 h_a1b1 h_a4b4 x hx1 hx4 hm1 hm4 hn1 hn4 ux.eval M4_x
          rw [h_M14x_eq]
        have hu_y_eq_M4y : u y = M4_y.eval := by
          -- Unfold u y
          dsimp [u]
          -- Unfold u_const y
          dsimp [u_const]
          -- Need to show that M1(y) = M4(y)
          have h_M14y_eq := by
            exact hM_indep_ab a2 b2 a4 b4 h_a2b2 h_a4b4 y hy2 hy4 hm2 hm4 hn2 hn4 uy.eval M4_y
          rw [h_M14y_eq]
        have hu_k_eq_M4k : u (x +[k] y) = M4_k.eval := by
          -- Unfold u (x +[k] y)
          dsimp [u]
          -- Unfold u_const (x +[k] y)
          dsimp [u_const]
          -- Need to show that M1(x +[k] y) = M4(x +[k] y)
          have h_M14k_eq := by
            exact hM_indep_ab a3 b3 a4 b4 h_a3b3 h_a4b4 (x +[k] y)
              hk3 hk4 hm3 hm4 hn3 hn4 uk.eval M4_k
          rw [h_M14k_eq]

        -- Combine all together
        rw [←hu_x_eq_M4x, ←hu_y_eq_M4y, ←hu_k_eq_M4k] at h_plin_M4
        exact h_plin_M4

      -- Finally, conclude that u is a utility function
      exact ⟨u, hu_ord_cons, hu_plin⟩

  · -- Backward direction:
    -- ∃ u, utility_function u r → vNM_axioms r
    rintro ⟨u, hu_ord_cons, hu_plin⟩
    -- Show vNM axioms
    have h_vNM : vNM_axioms r := by
      have h_complete : completeness r := by
        intro x y
        have h_either : u x ≥ u y ∨ u y ≥ u x := by
          exact le_total (u y) (u x)
        cases h_either with
        | inl h_xy => exact Or.inl ((hu_ord_cons x y).mpr h_xy)
        | inr h_yx => exact Or.inr ((hu_ord_cons y x).mpr h_yx)
      have h_trans : transitivity r := by
        intro x y z hxyz
        rcases hxyz with ⟨hx_y, hy_z⟩
        have h_xy : u x ≥ u y := (hu_ord_cons x y).mp hx_y
        have h_yz : u y ≥ u z := (hu_ord_cons y z).mp hy_z
        have h_xz : u x ≥ u z := by linarith
        exact (hu_ord_cons x z).mpr h_xz
      have h_independence : independence r := by
        intro x y z k h_k_in
        constructor
        · -- x ≽ y → x +[k] z ≽ y +[k] z
          intro hx_y
          have h_xy : u x ≥ u y := (hu_ord_cons x y).mp hx_y
          have h_kx : u (x +[k] z) = k.1 * u x + (1 - k.1) * u z := hu_plin x z k
          have h_ky : u (y +[k] z) = k.1 * u y + (1 - k.1) * u z := hu_plin y z k
          have h_kx_ky : u (x +[k] z) ≥ u (y +[k] z) := by
            have h_aux : k.1 * u x ≥ k.1 * u y := by
              have h_k1_nonneg : 0 ≤ k.1 := by
                exact k.2.left
              exact mul_le_mul_of_nonneg_left h_xy h_k1_nonneg
            linarith
          exact (hu_ord_cons (x +[k] z) (y +[k] z)).mpr h_kx_ky
        · -- x +[k] z ≽ y +[k] z → x ≽ y
          intro h_kx_ky
          have h_kx : u (x +[k] z) = k.1 * u x + (1 - k.1) * u z := hu_plin x z k
          have h_ky : u (y +[k] z) = k.1 * u y + (1 - k.1) * u z := hu_plin y z k
          have h_kx_ky : u (x +[k] z) ≥ u (y +[k] z) := by
            exact (hu_ord_cons (x +[k] z) (y +[k] z)).mp h_kx_ky
          have h_k1_nonneg : 0 < k.1 := by
              exact h_k_in.left
          have h_aux : k.1 * u x ≥ k.1 * u y := by
            linarith
          have h_xy : u x ≥ u y := by
            have h_1k1_pos : 0 ≤ 1/k.1 := by
              apply div_nonneg
              · linarith
              linarith
            have h := mul_le_mul_of_nonneg_left h_aux h_1k1_pos
            field_simp [h_k1_nonneg] at h
            exact h
          exact (hu_ord_cons x y).mpr h_xy
      have h_continuity : continuity r := by
        intro x y z hxyz
        rcases hxyz with ⟨hx_y, hy_z⟩
        have h_xy : u x ≥ u y := (hu_ord_cons x y).mp hx_y
        have h_yz : u y ≥ u z := (hu_ord_cons y z).mp hy_z
        have h_xz : u x ≥ u z := by linarith
        by_cases h_xz_strict : u x > u z
        · -- k = (u y - u z) / (u x - u z) is the right choice to make u(x +[k] z) = u y
          have h_aux : u x - u z > 0 := by
            linarith
          let k_val := (u y - u z) / (u x - u z)
          have h_k_nonneg : 0 ≤ k_val := by
            apply div_nonneg
            · linarith
            · linarith
          have h_k_le_one : k_val ≤ 1 := by
            have h_y_le_x : u y ≤ u x := h_xy
            have h_k_le_one_aux : u y - u z ≤ u x - u z := by
              linarith
            exact (div_le_one h_aux).mpr h_k_le_one_aux
          have h_k_in : k_val ∈ Set.Icc 0 1 := by
            exact ⟨h_k_nonneg, h_k_le_one⟩
          let k : IntervalType := ⟨k_val, h_k_in⟩
          have h_kx : u (x +[k] z) = k_val * u x + (1 - k_val) * u z := hu_plin x z k
          have h_rhs_y : k_val * u x + (1 - k_val) * u z = u y := by
            have h_kx_eq_y : k_val * u x + (1 - k_val) * u z = u y := by
              simp [k_val]
              field_simp [h_aux]
              ring_nf
            exact h_kx_eq_y
          rw [h_rhs_y] at h_kx
          have h_xkz_ge_y : (x +[k] z) ≽[r] y := (hu_ord_cons (x+[k]z) y).mpr (ge_of_eq h_kx)
          have h_y_ge_xkz : y ≽[r] (x +[k] z) := (hu_ord_cons y (x+[k]z)).mpr (le_of_eq h_kx)
          exact ⟨k, ⟨h_xkz_ge_y, h_y_ge_xkz⟩⟩
        · -- If ¬(u x > u z), then u x = u y = u z
          have h_xz_eq : u x = u z := by
            linarith
          have h_xy_eq : u x = u y := by
            linarith
          -- Then any k works, k = 1 for simplicity
          let k : IntervalType := ⟨1, by simp⟩
          have h_kx : u (x +[k] z) = 1 * u x + (1 - 1) * u z := hu_plin x z k
          have h_rhs_y : 1 * u x + (1 - 1) * u z = u y := by
            rw [←h_xz_eq, h_xy_eq]
            simp
          rw [h_rhs_y] at h_kx
          have h_xkz_ge_y : (x +[k] z) ≽[r] y := (hu_ord_cons (x+[k]z) y).mpr (ge_of_eq h_kx)
          have h_y_ge_xkz : y ≽[r] (x +[k] z) := (hu_ord_cons y (x+[k]z)).mpr (le_of_eq h_kx)
          exact ⟨k, ⟨h_xkz_ge_y, h_y_ge_xkz⟩⟩
      exact ⟨h_complete, h_trans, h_independence, h_continuity⟩

    -- And therefore we have vNM
    exact h_vNM


/-
Theorem (Utility generator): If u1 is a utility function representing r, then any
positive affine transformation of u1 is also a utility function representing r
-/

theorem utility_gen [MixSpace α] (r : Relation α) {u1 : α → ℝ}
  (h1 : utility_function u1 r) :
  ∀ a b : ℝ, ∀ u2 : α → ℝ, a > 0 ∧ (∀ x : α, u2 x = a * u1 x + b) →
    utility_function u2 r := by
  intro a b u2 h_conds
  rcases h_conds with ⟨h_a_pos, h_u2_def⟩
  -- Show that u2 is ordinal consistent
  have hu2_ord_cons : ordinal_consistent u2 r := by
    intro x y
    have h_u1_ord_cons := h1.left
    have h_u1_xy : u1 x ≥ u1 y ↔ x ≽[r] y := by
      exact (h_u1_ord_cons x y).symm
    have h_u2_xy : u2 x ≥ u2 y ↔ x ≽[r] y := by
      calc
        u2 x ≥ u2 y ↔ a * u1 x + b ≥ a * u1 y + b := by simp [h_u2_def]
        _ ↔ a * u1 x ≥ a * u1 y := by exact (add_le_add_iff_right b)
        _ ↔ u1 x ≥ u1 y := by
          have h_a_nonneg : 0 < a := h_a_pos
          exact (mul_le_mul_iff_of_pos_left h_a_nonneg)
      rw [h_u1_xy]
    exact h_u2_xy.symm
  -- Show that u2 is p-linear
  have hu2_plin : p_linear u2 := by
    intro x y k
    have h_u1_plin := h1.right
    have h_u1_k : u1 (x +[k] y) = k.1 * u1 x + (1 - k.1) * u1 y := h_u1_plin x y k
    have h_u2_k : u2 (x +[k] y) = a * u1 (x +[k] y) + b := by simp [h_u2_def]
    rw [h_u2_k, h_u1_k]
    have h_u2_xy : a * u1 x + b = u2 x ∧ a * u1 y + b = u2 y := by
      simp [h_u2_def]
    rw [←h_u2_xy.1, ←h_u2_xy.2]
    ring_nf

  -- Finally, conclude that u2 is a utility function
  exact ⟨hu2_ord_cons, hu2_plin⟩


/-
Theorem (Utility uniqueness): If u1 and u2 are both utility functions representing r,
then there exists a > 0 and b such that ∀ x, u2 x = a * u1 x + b
-/

theorem utility_unique [MixSpace α] (r : Relation α) {u1 u2 : α → ℝ}
  (h1 : utility_function u1 r) (h2 : utility_function u2 r) :
  vNM_axioms r → ∃ a b : ℝ, a > 0 ∧ (∀ x : α, u2 x = a * u1 x + b) := by
  -- have vNM_axioms := (vNM_theorem r).mpr ⟨u1, h1⟩
  intro vNM_axioms
  rcases vNM_axioms with ⟨h_complete, h_trans, h_independence, h_continuity⟩
  let h_u1_ord_cons := h1.left
  let h_u2_ord_cons := h2.left
  let h_u1_plin := h1.right
  let h_u2_plin := h2.right
  -- By cases, α is not empty
  by_cases h_empty : ¬(∃ x : α, True)
  · -- Case 1 : α is empty, then any a > 0 and b works
    exact ⟨1, 0, by simp, by intro x; exfalso; exact h_empty ⟨x, trivial⟩⟩
  · -- Case 2 : α is not empty
    have h_nonempty : ∃ x : α, True := by
      exact not_not.mp h_empty
    -- By cases, ∀ x y, x ∼ y
    by_cases h_no_strict : ∀ x y : α, x ∼[r] y
    · -- Then u1(x) = u1(y) and u2(x) = u2(y) for all x, y
      have h_u1_const : ∀ x y : α, u1 x = u1 y := by
        intro x y
        have h_xy_ge : u1 x ≥ u1 y := (h_u1_ord_cons x y).mp (h_no_strict x y).left
        have h_yx_ge : u1 y ≥ u1 x := (h_u1_ord_cons y x).mp (h_no_strict y x).left
        exact le_antisymm h_yx_ge h_xy_ge
      have h_u2_const : ∀ x y : α, u2 x = u2 y := by
        intro x y
        have h_xy_ge : u2 x ≥ u2 y := (h_u2_ord_cons x y).mp (h_no_strict x y).left
        have h_yx_ge : u2 y ≥ u2 x := (h_u2_ord_cons y x).mp (h_no_strict y x).left
        exact le_antisymm h_yx_ge h_xy_ge
      -- Then a = 1 and b = u2 - u1 works
      let x0 := Classical.choose h_nonempty
      let a := (1 : ℝ)
      have h_a_pos : a > 0 := zero_lt_one
      let b := u2 x0 - u1 x0
      have h_u2_def : ∀ x : α, u2 x = a * u1 x + b := by
        intro x
        simp only [a, b]
        have h_u1_x0 : u1 x0 = u1 x := by
          exact h_u1_const x0 x
        have h_u2_x0 : u2 x0 = u2 x := by
          exact h_u2_const x0 x
        rw [h_u1_x0, h_u2_x0]
        ring_nf
      exact ⟨a, b, h_a_pos, h_u2_def⟩
    · -- Then there exists x0, y0 such that ¬(x0 ∼[r] y0)
      have h_ex_no_strict : ∃ x0 y0 : α, ¬(x0 ∼[r] y0) := by
        rw [not_forall] at h_no_strict
        rcases h_no_strict with ⟨x, h⟩
        rw [not_forall] at h
        rcases h with ⟨y, h⟩
        exact ⟨x, y, h⟩
      -- Then there exists x0, y0 such that x0 ≻[r] y0
      have h_ex_strict : ∃ x0 y0 : α, x0 ≻[r] y0 := by
        rcases h_ex_no_strict with ⟨x0, y0, hxy⟩
        have h_not_or : ¬(x0 ≽[r] y0) ∨ ¬(y0 ≽[r] x0) := by
          exact not_and_or.mp hxy
        have h_or_u : u1 x0 ≥ u1 y0 ∨ u1 y0 ≥ u1 x0 := by
          exact le_total (u1 y0) (u1 x0)
        have h_or : x0 ≽[r] y0 ∨ y0 ≽[r] x0 := by
          exact h_complete x0 y0
        cases h_or with
        | inl h_x0_ge_y0 => exact ⟨x0, y0, ⟨h_x0_ge_y0,
          h_not_or.resolve_left (not_not.mpr h_x0_ge_y0)⟩⟩
        | inr h_y0_ge_x0 => exact ⟨y0, x0, ⟨h_y0_ge_x0,
          h_not_or.resolve_right (not_not.mpr h_y0_ge_x0)⟩⟩

      rcases h_ex_strict with ⟨x0, y0, hx0y0⟩
      -- Then u1 x0 > u1 y0 and u2 x0 > u2 y0
      have h_u1_x0_y0 : u1 x0 > u1 y0 := by
        have h_x0_ge_y0 : u1 x0 ≥ u1 y0 := (h_u1_ord_cons x0 y0).mp hx0y0.left
        have h_y0_ge_x0 : ¬(u1 y0 ≥ u1 x0) := by
          intro h_y_x
          have h := (h_u1_ord_cons y0 x0).mpr h_y_x
          exact absurd h hx0y0.right
        linarith
      have h_u2_x0_y0 : u2 x0 > u2 y0 := by
        have h_x0_ge_y0 : u2 x0 ≥ u2 y0 := (h_u2_ord_cons x0 y0).mp hx0y0.left
        have h_y0_ge_x0 : ¬(u2 y0 ≥ u2 x0) := by
          intro h_y_x
          have h := (h_u2_ord_cons y0 x0).mpr h_y_x
          exact absurd h hx0y0.right
        linarith

      -- Then we can define a = (u2 x0 - u2 y0) / (u1 x0 - u1 y0) and b = u2 x0 - a * u1 x0
      let a := (u2 x0 - u2 y0) / (u1 x0 - u1 y0)
      have h_a_pos : a > 0 := by
        apply div_pos
        · linarith
        · linarith
      have h_denom_nonzero : u1 x0 - u1 y0 ≠ 0 := by
        linarith
      let b := u2 x0 - a * u1 x0
      have h_u2_def : ∀ x : α, u2 x = a * u1 x + b := by
        intro x
        -- By cases
        by_cases hx_x0 : x ≽[r] x0
        · -- If x ≽ x0, then x ≽ x0 ≻ y0
          have hx_y0 : x ≽[r] y0 := h_trans x x0 y0 ⟨hx_x0, hx0y0.left⟩
          -- And therefore x0 = x +[k] y0 for some k > 0
          have h_ex_p : ∃ (k : IntervalType), ((x +[k] y0) ∼[r] x0) := by
            exact h_continuity x x0 y0 ⟨hx_x0, hx0y0.left⟩
          rcases h_ex_p with ⟨k, hk⟩
          have h_k_not_zero : k.1 ≠ 0 := by
            intro h_k_zero
            have h_x0_y0 : y0 ≽[r] x0 := by
              have h_x0_ge_k := hk.left
              have h_aux := mix_zero k x y0 h_k_zero
              rw [h_aux] at h_x0_ge_k
              exact h_x0_ge_k
            exact absurd h_x0_y0 hx0y0.right
          -- Then u1 x0 = u1 (x +[k] y0) = k * u1 x + (1-k) * u1 y0
          -- and u2 x0 = u2 (x +[k] y0) = k * u2 x + (1-k) * u2 y0
          have h_u1_x0 : u1 x0 ≥ k.1 * u1 x + (1 - k.1) * u1 y0 := by
            have h_ord := (h_u1_ord_cons x0 (x +[k] y0)).mp hk.right
            rw [h_u1_plin x y0 k] at h_ord
            exact h_ord
          have h_u1_x0_rev : k.1 * u1 x + (1 - k.1) * u1 y0 ≥ u1 x0 := by
            have h_ord := (h_u1_ord_cons (x +[k] y0) x0).mp hk.left
            rw [h_u1_plin x y0 k] at h_ord
            exact h_ord
          have h_u1_x0_eq : u1 x0 = k.1 * u1 x + (1 - k.1) * u1 y0 := by
            linarith
          have h_u2_x0 : u2 x0 ≥ k.1 * u2 x + (1 - k.1) * u2 y0 := by
            have h_ord := (h_u2_ord_cons x0 (x +[k] y0)).mp hk.right
            rw [h_u2_plin x y0 k] at h_ord
            exact h_ord
          have h_u2_x0_rev : k.1 * u2 x + (1 - k.1) * u2 y0 ≥ u2 x0 := by
            have h_ord := (h_u2_ord_cons (x +[k] y0) x0).mp hk.left
            rw [h_u2_plin x y0 k] at h_ord
            exact h_ord
          have h_u2_x0_eq : u2 x0 = k.1 * u2 x + (1 - k.1) * u2 y0 := by
            linarith
          -- Then u1 x = (u1 x0 - (1-k) * u1 y0)/k
          -- and u2 x = (u2 x0 - (1-k) * u2 y0)/k
          have h_u1_x : u1 x = (u1 x0 - (1 - k.1) * u1 y0)/k.1 := by
            rw [h_u1_x0_eq]
            ring_nf
            field_simp [h_k_not_zero]
          have h_u2_x : u2 x = (u2 x0 - (1 - k.1) * u2 y0)/k.1 := by
            rw [h_u2_x0_eq]
            ring_nf
            field_simp [h_k_not_zero]

          -- Combine all together to show u2 x = a * u1 x + b
          have h_u2_x_eq : u2 x = a * u1 x + b := by
            rw [h_u1_x, h_u2_x]
            simp [a, b]
            field_simp [h_denom_nonzero]
            ring_nf

          exact h_u2_x_eq
        · -- If ¬(x ≽ x0), then x0 ≻ x
          have hx0_x : x0 ≻[r] x := by
            exact ⟨(h_complete x x0).resolve_left hx_x0, hx_x0⟩
          by_cases hy0_x : y0 ≽[r] x
          · -- If y0 ≽ x, then x0 ≻ y0 ≽ x
            have hx0_x : x0 ≽[r] x := h_trans x0 y0 x ⟨hx0y0.left, hy0_x⟩
            -- And therefore y0 = x0 +[k] x for some k > 0
            have h_ex_p : ∃ (k : IntervalType), ((x0 +[k] x) ∼[r] y0) := by
              exact h_continuity x0 y0 x ⟨hx0y0.left, hy0_x⟩
            rcases h_ex_p with ⟨k, hk⟩
            have h_k_not_one : k.1 ≠ 1 := by
              intro h_k_one
              have h_y0_x0 : y0 ≽[r] x0 := by
                have h_k_ge_y0 := hk.right
                have h_aux := MixSpace.mix_one k x0 x h_k_one
                rw [h_aux] at h_k_ge_y0
                exact h_k_ge_y0
              exact absurd h_y0_x0 hx0y0.right
            have h_1k_not_zero : (1 - k.1) ≠ 0 := by
              exact sub_ne_zero_of_ne h_k_not_one.symm
            -- Then u1 y0 = u1 (x0 +[k] x) = k * u1 x0 + (1-k) * u1 x
            -- and u2 y0 = u2 (x0 +[k] x) = k * u2 x0 + (1-k) * u2 x
            have h_u1_x0 : u1 y0 ≥ k.1 * u1 x0 + (1 - k.1) * u1 x := by
              have h_ord := (h_u1_ord_cons y0 (x0 +[k] x)).mp hk.right
              rw [h_u1_plin x0 x k] at h_ord
              exact h_ord
            have h_u1_x0_rev : k.1 * u1 x0 + (1 - k.1) * u1 x ≥ u1 y0 := by
              have h_ord := (h_u1_ord_cons (x0 +[k] x) y0).mp hk.left
              rw [h_u1_plin x0 x k] at h_ord
              exact h_ord
            have h_u1_x0_eq : u1 y0 = k.1 * u1 x0 + (1 - k.1) * u1 x := by
              linarith
            have h_u2_x0 : u2 y0 ≥ k.1 * u2 x0 + (1 - k.1) * u2 x := by
              have h_ord := (h_u2_ord_cons y0 (x0 +[k] x)).mp hk.right
              rw [h_u2_plin x0 x k] at h_ord
              exact h_ord
            have h_u2_x0_rev : k.1 * u2 x0 + (1 - k.1) * u2 x ≥ u2 y0 := by
              have h_ord := (h_u2_ord_cons (x0 +[k] x) y0).mp hk.left
              rw [h_u2_plin x0 x k] at h_ord
              exact h_ord
            have h_u2_x0_eq : u2 y0 = k.1 * u2 x0 + (1 - k.1) * u2 x := by
              linarith
            -- Then u1 x = (u1 y0 - k * u1 x0)/(1 - k)
            -- and u2 x = (u2 y0 - k * u2 x0)/(1 - k)
            have h_u1_x : u1 x = (u1 y0 - k.1 * u1 x0)/(1 - k.1) := by
              rw [h_u1_x0_eq]
              field_simp [h_1k_not_zero]
              ring_nf
            have h_u2_x : u2 x = (u2 y0 - k.1 * u2 x0)/(1 - k.1) := by
              rw [h_u2_x0_eq]
              field_simp [h_1k_not_zero]
              ring_nf

            -- Combine all together to show u2 x = a * u1 x + b
            have h_u2_x_eq : u2 x = a * u1 x + b := by
              rw [h_u1_x, h_u2_x]
              simp [a, b]
              field_simp [h_denom_nonzero]
              ring_nf

            exact h_u2_x_eq
          · -- If ¬(y0 ≽ x), then x ≻ y0
            have hx_y0 : x ≻[r] y0 := by
              exact ⟨(h_complete x y0).resolve_right hy0_x, hy0_x⟩
            -- Then x = x0 +[k] y0 for some k > 0
            have h_ex_p : ∃ (k : IntervalType), ((x0 +[k] y0) ∼[r] x) := by
              exact h_continuity x0 x y0 ⟨hx0_x.left, hx_y0.left⟩
            rcases h_ex_p with ⟨k, hk⟩
            have h_k_not_one : k.1 ≠ 1 := by
              intro h_k_one
              have h_x_x0 : x ≽[r] x0 := by
                have h_k_ge_x := hk.right
                have h_aux := MixSpace.mix_one k x0 y0 h_k_one
                rw [h_aux] at h_k_ge_x
                exact h_k_ge_x
              exact absurd h_x_x0 hx0_x.right
            have h_1k_not_zero : (1 - k.1) ≠ 0 := by
              exact sub_ne_zero_of_ne h_k_not_one.symm
            -- Then u1 x = u1 (x0 +[k] y0) = k * u1 x0 + (1-k) * u1 y0
            -- and u2 x = u2 (x0 +[k] y0) = k * u2 x0 + (1-k) * u2 y0
            have h_u1_x : u1 x ≥ k.1 * u1 x0 + (1 - k.1) * u1 y0 := by
              have h_ord := (h_u1_ord_cons x (x0 +[k] y0)).mp hk.right
              rw [h_u1_plin x0 y0 k] at h_ord
              exact h_ord
            have h_u1_x_rev : k.1 * u1 x0 + (1 - k.1) * u1 y0 ≥ u1 x := by
              have h_ord := (h_u1_ord_cons (x0 +[k] y0) x).mp hk.left
              rw [h_u1_plin x0 y0 k] at h_ord
              exact h_ord
            have h_u1_x_eq : u1 x = k.1 * u1 x0 + (1 - k.1) * u1 y0 := by
              linarith
            have h_u2_x : u2 x ≥ k.1 * u2 x0 + (1 - k.1) * u2 y0 := by
              have h_ord := (h_u2_ord_cons x (x0 +[k] y0)).mp hk.right
              rw [h_u2_plin x0 y0 k] at h_ord
              exact h_ord
            have h_u2_x_rev : k.1 * u2 x0 + (1 - k.1) * u2 y0 ≥ u2 x := by
              have h_ord := (h_u2_ord_cons (x0 +[k] y0) x).mp hk.left
              rw [h_u2_plin x0 y0 k] at h_ord
              exact h_ord
            have h_u2_x_eq : u2 x = k.1 * u2 x0 + (1 - k.1) * u2 y0 := by
              linarith

            -- Combine all together to show u2 x = a * u1 x + b
            have h_u2_x_eq : u2 x = a * u1 x + b := by
              rw [h_u1_x_eq, h_u2_x_eq]
              simp [a, b]
              field_simp [h_denom_nonzero]
              ring_nf
            exact h_u2_x_eq
      exact ⟨a, b, h_a_pos, h_u2_def⟩



/-
Corollary: Given a utility function, we can construct
another utility function that gives any desired value
to a particular element.
-/

lemma utility_offset [MixSpace α] (r : Relation α)
  (hexists : ∃ u : α → ℝ, utility_function u r) :
  ∀ c : ℝ, ∀ x : α, ∃ u' : α → ℝ, utility_function u' r ∧
    u' x = c := by
  rcases hexists with ⟨u, hu⟩
  intro c x
  let a := (1 : ℝ)
  let b := c - u x
  let u' := fun y : α => a * u y + b
  have hau' : utility_function u' r :=
    utility_gen r hu a b u' ⟨by linarith, by intro y; rfl⟩
  use u'
  constructor
  · exact hau'
  · calc
      u' x = a * u x + b := by rfl
      _ = (1 : ℝ) * u x + (c - u x) := by rfl
      _ = c := by ring


end Utility
