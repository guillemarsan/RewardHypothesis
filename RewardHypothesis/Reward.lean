import RewardHypothesis.vNM


namespace Reward
open OrdinalRep
open Utility


lemma indiff_in_Icc (hg : g ∈ Set.Icc (0 : ℝ) 1) : 1/(g+1) ∈ Set.Icc (0 : ℝ) 1 :=
  by
    rcases hg with ⟨hg0, hg1⟩
    have hdenom_pos : 0 < g + 1 := by
        linarith
    constructor
    · exact (le_of_lt (div_pos zero_lt_one hdenom_pos))
    · have hdenom_ge_one : 1 ≤ g + 1 := by
        linarith
      have hdenom_pos : 0 < g + 1 := by
        linarith
      apply (div_le_one hdenom_pos).mpr hdenom_ge_one

/-
Define ConcatMixtureSpace with the T-concatenation operation with its axioms
-/

def UniType (T : Set α) : Type :=
  { t : α // t ∈ T }

class ConcatMixSpace (α : Type) extends MixSpace α where
  T : Set α
  concat :
    UniType T → α → α

  ε: α
  concat_idempotent :
    ∀ (t : UniType T), concat t ε = t.1

notation lhs "⊕" rhs:50 => ConcatMixSpace.concat lhs rhs

/-
Define the axiom for markov reward on a preference relation.
-/

def dynamic_consistency [inst : ConcatMixSpace α] (r : Relation α) : Prop :=
  ∀ x y : α, ∀ t : UniType inst.T, (x ≽[r] y) → (t ⊕ x) ≽[r] (t ⊕ y)

def γ_indifference [inst : ConcatMixSpace α] (r : Relation α) : Prop :=
  ∃ γ : UniType inst.T → IntervalType, ∀ x y : α, ∀ t : UniType inst.T,
    let pγ : IntervalType := ⟨1/((γ t).1 + 1), indiff_in_Icc (γ t).2⟩
    ((t ⊕ x)+[pγ]y) ∼[r] ((t ⊕ y)+[pγ]x)

/-
Completeness, transitivity, independence and continuity → (γ-indifference → dynamic consistency)
-/

theorem dc_if_γ_indiff [inst : ConcatMixSpace α] (r : Relation α) :
  vNM_axioms r → (γ_indifference r → dynamic_consistency r):= by
  intro h_vNM h_γ_indiff
  rcases h_γ_indiff with ⟨γ, h_γ_indiff⟩
  intro x y t h_xy
  -- Make utility function u representing r
  have h_u_exists := (vNM_theorem r).mp h_vNM
  rcases h_u_exists with ⟨u, h_utility_function⟩
  rcases h_utility_function with ⟨h_ordinal_consistent, h_p_linear⟩
  -- Apply this in the γ-indifference property
  let pγ : IntervalType := ⟨1/((γ t).1 + 1), indiff_in_Icc (γ t).2⟩
  have h_γ_prop := h_γ_indiff x y t
  -- Transform it into u
  -- u((t ⊕ x)+[pγ]y) = u((t ⊕ y)+[pγ]x)
  have h_u_prop := by
    have h_γ'_prop : ((t⊕x) +[pγ] y) ∼[r] ((t⊕y) +[pγ] x)  := by
      exact h_γ_prop
    have h_u_prop_geq := (h_ordinal_consistent ((t⊕x) +[pγ] y)
     ((t⊕y) +[pγ] x)).mp h_γ'_prop.left
    have h_u_prop_leq := (h_ordinal_consistent ((t⊕y) +[pγ] x)
     ((t⊕x) +[pγ] y)).mp h_γ'_prop.right
    have h_u_prop : u ((t⊕x) +[pγ] y) = u ((t⊕y) +[pγ] x) :=
      le_antisymm h_u_prop_leq h_u_prop_geq
    exact h_u_prop
  -- Use linear property to expand both sides
  -- pγ u(t ⊕ x) + (1 - pγ) u(y) = pγ u(t ⊕ y) + (1 - pγ) u(x)
  have h_u_prop_lin : pγ.1 * u ((t⊕x)) + (1 - pγ.1) * u (y) =
   pγ.1 * u ((t⊕y)) + (1 - pγ.1) * u (x) := by
    rw [h_p_linear ((t⊕x)) (y) pγ] at h_u_prop
    rw [h_p_linear ((t⊕y)) (x) pγ] at h_u_prop
    exact h_u_prop
  -- Rearranging terms
  -- pγ (u(t ⊕ x) - u(t ⊕ y)) = (1 - pγ) (u(x) - u(y))
  have h_u_rearranged : pγ.1 * (u (t⊕x) - u (t⊕y)) = (1 - pγ.1) * (u x - u y) := by
    linarith [h_u_prop_lin]
  -- Since x ≽[r] y, u(x) - u(y) ≥ 0
  have h_u_xy_geq : u x - u y ≥ 0 := by
    have h_ux_geq_uy := (h_ordinal_consistent x y).mp h_xy
    linarith
  -- Also, pγ.1 > 0 and (1 - pγ.1) ≥ 0
  have h_pγ_pos : pγ.1 > 0 := by
    have h_gt_zero : 0 < (γ t).1 + 1 := by
      have h_ge_zero : 0 ≤ (γ t).1 := by
        exact (γ t).2.left
      linarith
    exact one_div_pos.mpr h_gt_zero
  have h_one_minus_pγ_geq : (1 - pγ.1) ≥ 0 := by
    exact (comm_in_Icc pγ.2).1
  -- Therefore, u(t ⊕ x) - u(t ⊕ y) ≥ 0
  have h_u_txy_geq : u (t⊕x) - u (t⊕y) ≥ 0 := by
    have h_rhs_pos : (1 - pγ.1) * (u x - u y) ≥ 0 := by
      apply mul_nonneg h_one_minus_pγ_geq
      linarith
    have h_lhs_geq : pγ.1 * (u (t⊕x) - u (t⊕y)) ≥ 0 := by
      rw [h_u_rearranged]
      exact h_rhs_pos
    have h_pos_or_neg := by
      exact mul_nonneg_iff.mp h_lhs_geq
    have h_pos : pγ.1 ≥ 0 ∧ (u (t⊕x) - u (t⊕y)) ≥ 0 := by
      exact h_pos_or_neg.resolve_right (not_and_or.mpr (Or.inl (not_le_of_gt h_pγ_pos)))
    exact h_pos.2
  -- And so u(t ⊕ x) ≥ u(t ⊕ y)
  have h_u_txy_geq_final : u (t⊕x) ≥ u (t⊕y) := by
    linarith [h_u_txy_geq]
  -- Thus, (t ⊕ x) ≽[r] (t ⊕ y)
  have h_tx_ty : (t ⊕ x) ≽[r] (t ⊕ y) := by
    exact (h_ordinal_consistent (t⊕x) (t⊕y)).mpr h_u_txy_geq_final
  exact h_tx_ty


/-
Define what it means for a function to be a reward function.
-/

def markov_recursive [inst : ConcatMixSpace α] (u : α → ℝ) : Prop :=
  ∃ γ : UniType inst.T → IntervalType, ∀ x : α, ∀ t : UniType inst.T,
  (u (t ⊕ x) = u t.1 + (γ t).1 * u x) ∧ (u (inst.ε)) = 0

def reward_function [ConcatMixSpace α] (u : α → ℝ) (r : Relation α) : Prop :=
  ordinal_consistent u r ∧ p_linear u ∧ markov_recursive u


/-
Markov reward Theorem: A preference relation on a concatenable mixture space
satisfies completeness, transitivity, independence, continuity and γ-indifference,
↔ there exists a reward function u : α → ℝ that represents the preference relation.
-/

theorem Markov_Reward_theorem [inst : ConcatMixSpace α] (r : Relation α) :
  vNM_axioms r ∧ γ_indifference r ↔ ∃ u : α → ℝ, reward_function u r := by
  apply Iff.intro
  -- Forward direction
  · intro h
    rcases h with ⟨h_vNM, h_γ_indiff⟩
    rcases h_γ_indiff with ⟨γ, h_γ_indiff⟩
    -- Existence of utility function from vNM theorem
    have h_u_exists := (vNM_theorem r).mp h_vNM
    -- Set u(ε) = 0
    have h_u_offset := utility_offset r h_u_exists 0 inst.ε
    rcases h_u_offset with ⟨u, h_utility_function, h_u_ε_0⟩
    rcases h_utility_function with ⟨h_ordinal_consistent, h_p_linear⟩
    have h_u_markov : markov_recursive u := by
      use γ
      intro x t
      -- From γ-indifference choosing y = ε
      -- ((t ⊕ x)+[pγ]ε) ∼[r] ((t ⊕ ε)+[pγ]x)
      have h_γ_prop := h_γ_indiff x inst.ε t
      -- Transform it into u
      -- u((t ⊕ x)+[pγ]ε) = u((t ⊕ ε)+[pγ]x)
      let pγ' : IntervalType := ⟨1/((γ t).1 + 1), indiff_in_Icc (γ t).2⟩
      have h_γ'_prop : ((t⊕x) +[pγ'] inst.ε) ∼[r] ((t⊕inst.ε) +[pγ']x)  := by
        exact h_γ_prop
      have h_u_prop_geq := (h_ordinal_consistent ((t⊕x) +[pγ'] inst.ε)
       ((t⊕inst.ε) +[pγ']x)).mp h_γ'_prop.left
      have h_u_prop_leq := (h_ordinal_consistent ((t⊕inst.ε) +[pγ']x)
       ((t⊕x) +[pγ'] inst.ε)).mp h_γ'_prop.right
      have h_u_prop : u ((t⊕x) +[pγ']inst.ε) = u ((t⊕inst.ε) +[pγ']x) :=
        le_antisymm h_u_prop_leq h_u_prop_geq
      -- Use linear property to expand both sides
      -- pγ' u(t ⊕ x) + (1 - pγ') u(ε) = pγ' u(t ⊕ ε) + (1 - pγ') u(x)
      have h_u_prop_lin : pγ'.1 * u ((t⊕x)) + (1 - pγ'.1) * u (inst.ε) =
       pγ'.1 * u ((t⊕inst.ε)) + (1 - pγ'.1) * u x := by
        rw [h_p_linear ((t⊕x)) (inst.ε) pγ'] at h_u_prop
        rw [h_p_linear ((t⊕inst.ε)) x pγ'] at h_u_prop
        exact h_u_prop
      -- Reduce t ⊕ ε = t and u(ε) = 0
      -- pγ' u(t ⊕ x) = pγ' u(t) + (1 - pγ') u(x)
      have h_u_prop_reduced : pγ'.1 * u (t⊕x) = pγ'.1 * u t.1 + (1 - pγ'.1) * u x := by
        rw [inst.concat_idempotent t] at h_u_prop_lin
        rw [h_u_ε_0] at h_u_prop_lin
        simp only [mul_zero, add_zero] at h_u_prop_lin
        exact h_u_prop_lin
      -- Multiply both sides by ((γ t).1 + 1)
      -- u(t ⊕ x) = u(t) + (γ t).1 * u(x)
      have h_u_prop_final : u (t⊕x) = u t.1 + (γ t).1 * u x := by
        have h_mult_pos : 0 < (γ t).1 + 1 := by
          have h_gt_zero : 0 ≤ (γ t).1 := by
            exact (γ t).2.left
          linarith
        have h_mult_both_sides := by
          simp only [pγ'] at h_u_prop_reduced
          apply (congr_arg (fun z => ((γ t).1 + 1) * z)) at h_u_prop_reduced
          field_simp [h_mult_pos] at h_u_prop_reduced
          simp only [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero] at h_u_prop_reduced
          exact h_u_prop_reduced
        exact h_mult_both_sides
      exact ⟨h_u_prop_final, h_u_ε_0⟩
    -- So this u is ordinal consistent, p_linear and markov_recursive
    use u
    exact ⟨h_ordinal_consistent, h_p_linear, h_u_markov⟩
  -- Backward direction
  · intro h
    -- The vNM axioms come from the reward function being a utility function
    -- and the vNM theorem
    have h_vNM : vNM_axioms r := by
      rcases h with ⟨u, h_reward_function⟩
      rcases h_reward_function with ⟨h_ordinal_consistent, h_p_linear, h_markov_recursive⟩
      have h_u_utility : ∃ u, utility_function u r :=
        ⟨u, ⟨h_ordinal_consistent, h_p_linear⟩⟩
      exact (vNM_theorem r).mpr h_u_utility
    -- γ-indifference comes from the markov_recursive property
    have h_γ_indiff : γ_indifference r := by
      rcases h with ⟨u, h_reward_function⟩
      rcases h_reward_function with ⟨h_ordinal_consistent, h_p_linear, h_markov_recursive⟩
      rcases h_markov_recursive with ⟨γ, h_markov_prop⟩
      use γ
      intro x y t
      let pγ : IntervalType := ⟨1/((γ t).1 + 1), indiff_in_Icc (γ t).2⟩
      -- First, we express as u(t ⊕ x) - (γ t) * u x = u t.1
      have h_u_t_x : u (t⊕x) - (γ t).1 * u x = u t.1 := by
        linarith [ (h_markov_prop x t).1 ]
      have h_u_t_y : u (t⊕y) - (γ t).1 * u y = u t.1 := by
        linarith [ (h_markov_prop y t).1 ]
      -- Then, u(t ⊕ x) - (γ t) * u x = u(t ⊕ y) - (γ t) * u y
      have h_u_eq : u (t⊕x) - (γ t).1 * u x = u (t⊕y) - (γ t).1 * u y := by
        linarith [h_u_t_x, h_u_t_y]
      -- Rearranging, we get:
      -- u(t ⊕ x) + (γ t) * u y = u(t ⊕ y) + (γ t) * u x
      have h_u_rearranged : u (t⊕x) + (γ t).1 * u y = u (t⊕y) + (γ t).1 * u x := by
        linarith [h_u_eq]
      -- Now, we multiply both sides by 1/((γ t).1 + 1)
      -- (1/((γ t).1 + 1)) u(t ⊕ x) + (1 - (1/((γ t).1 + 1))) u y
      -- = (1/((γ t).1 + 1)) u(t ⊕ y) + (1 - (1/((γ t).1 + 1))) u x
      have h_u_multiplied : (1/((γ t).1 + 1)) * u (t⊕x) + (1 - (1/((γ t).1 + 1))) * u y =
       (1/((γ t).1 + 1)) * u (t⊕y) + (1 - (1/((γ t).1 + 1))) * u x := by
        have h_mult_pos : 0 < (γ t).1 + 1 := by
          have h_gt_zero : 0 ≤ (γ t).1 := by
            exact (γ t).2.left
          linarith
        have h_mult_inv : (1/((γ t).1 + 1)) * (γ t).1 = 1 - 1/((γ t).1 + 1) := by
          field_simp [h_mult_pos]
          linarith
        have h_mult_both_sides := by
          apply (congr_arg (fun z => (1/((γ t).1 + 1)) * z)) at h_u_rearranged
          rw [mul_add, ←mul_assoc, mul_add, ←mul_assoc] at h_u_rearranged
          rw [h_mult_inv] at h_u_rearranged
          exact h_u_rearranged
        exact h_mult_both_sides
      -- We use pγ to rewrite both sides (just syntax)
      -- pγ.1 * u(t ⊕ x) + (1 - pγ.1) * u y = pγ.1 * u(t ⊕ y) + (1 - pγ.1) * u x
      have h_u_multiplied : pγ.1 * u (t⊕x) + (1 - pγ.1) * u y =
       pγ.1 * u (t⊕y) + (1 - pγ.1) * u x := by
        exact h_u_multiplied
      -- Use linearity to rewrite as mixtures
      -- u((t ⊕ x)+[pγ]y) = u((t ⊕ y)+[pγ]x)
      have h_u_mixtures : u ((t⊕x) +[pγ] y) = u ((t⊕y) +[pγ] x) := by
        rw [←h_p_linear (t⊕x) y pγ] at h_u_multiplied
        rw [←h_p_linear (t⊕y) x pγ] at h_u_multiplied
        exact h_u_multiplied
      -- Use ordinal consistency to get indifference
      -- ((t⊕x) +[pγ]y) ∼[r] ((t⊕y) +[pγ]x)
      have h_indiff : ((t⊕x) +[pγ] y) ∼[r] ((t⊕y) +[pγ] x) := by
        have h_geq := (h_ordinal_consistent ((t⊕x) +[pγ] y)
         ((t⊕y) +[pγ] x)).mpr (ge_of_eq h_u_mixtures)
        have h_leq := (h_ordinal_consistent ((t⊕y) +[pγ] x)
         ((t⊕x) +[pγ] y)).mpr (ge_of_eq h_u_mixtures.symm)
        exact ⟨h_geq, h_leq⟩
      exact h_indiff
    -- So we have both parts
    exact ⟨h_vNM, h_γ_indiff⟩
end Reward
