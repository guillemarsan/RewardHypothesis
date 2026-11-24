/-
Copyright (c) 2026 Guillermo Martín-Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guillermo Martín-Sánchez
-/
import RewardHypothesis.vNM

/-!
# Markov reward theorem

Define a concatenable mixture space and the γ-indifference axiom.
Then, state and prove the Markov reward theorem: vNM axioms and γ-indifference
are equivalent to the existence of a Markov reward function.
-/

namespace Reward

open OrdinalRep Utility

variable {α : Type} {g : ℝ}

section ConcatMixSpace

/-! ## Concatenable mixture spaces -/

/-- Elements of T as a type (t ∈ T): `UniType T := {t : α // t ∈ T}`. -/
def UniType (T : Set α) : Type :=
  {t : α // t ∈ T}

/-- Concatenable mixture space, a mixture space with the T-concatenation operation and its
axioms (t ⊕ x for t ∈ T, and ε with t ⊕ ε = t):
`concat : UniType T → α → α`, `concat_idempotent : concat t ε = t.1`. -/
class ConcatMixSpace (α : Type) extends MixSpace α where
  T : Set α
  concat : UniType T → α → α
  ε : α
  concat_idempotent : ∀ (t : UniType T), concat t ε = t.1

notation lhs " ⊕ " rhs:50 => ConcatMixSpace.concat lhs rhs

end ConcatMixSpace

section RewardFunctions

/-! ## Reward functions and axioms -/

/-! ### Reward functions -/

/-- u Markov recursive (∃ γ : T → [0, 1] with u(t ⊕ x) = u(t) + γ(t) u(x) ∧ u(ε) = 0):
`∃ γ, ∀ x t, (u (t ⊕ x) = u t.1 + (γ t).1 * u x) ∧ u inst.ε = 0`. -/
def MarkovRecursive [inst : ConcatMixSpace α] (u : α → ℝ) : Prop :=
  ∃ γ : UniType inst.T → IntervalType, ∀ x : α, ∀ t : UniType inst.T,
    (u (t ⊕ x) = u t.1 + (γ t).1 * u x) ∧ u inst.ε = 0

/-- What it means for a function to be a reward function
(u ordinal consistent ∧ p-linear ∧ Markov recursive):
`OrdinalConsistent u r ∧ PLinear u ∧ MarkovRecursive u`. -/
def RewardFunction [ConcatMixSpace α] (u : α → ℝ) (r : Relation α) : Prop :=
  OrdinalConsistent u r ∧ PLinear u ∧ MarkovRecursive u

/-! ### Axioms for Markov reward

Define the axioms for Markov reward on a preference relation.
-/

/-! #### Lemma for the γ-indifference axiom -/

/-- g ∈ [0, 1] ⇒ 1/(g + 1) ∈ [0, 1]:
`g ∈ Set.Icc (0 : ℝ) 1 → 1/(g+1) ∈ Set.Icc (0 : ℝ) 1`. -/
lemma indiff_mem_Icc (hg : g ∈ Set.Icc (0 : ℝ) 1) : 1/(g+1) ∈ Set.Icc (0 : ℝ) 1 := by
  rcases hg with ⟨hg0, _⟩
  have hdenom : 0 < g + 1 := by
    linarith
  constructor
  · -- 0 ≤ 1/(g+1)
    exact le_of_lt (div_pos zero_lt_one hdenom)
  · -- 1/(g+1) ≤ 1
    have hge : 1 ≤ g + 1 := by
      linarith
    exact (div_le_one hdenom).mpr hge

/-! #### Dynamic consistency and γ-indifference -/

/-- Dynamic consistency (x ≽ y ⇒ t ⊕ x ≽ t ⊕ y):
`∀ x y t, (x ≽[r] y) → (t ⊕ x) ≽[r] (t ⊕ y)`. -/
def DynamicConsistency [inst : ConcatMixSpace α] (r : Relation α) : Prop :=
  ∀ x y : α, ∀ t : UniType inst.T, (x ≽[r] y) → (t ⊕ x) ≽[r] (t ⊕ y)

/-- γ-indifference (∃ γ : T → [0, 1] with (t ⊕ x) +[p] y ∼ (t ⊕ y) +[p] x, p = 1/(γ(t) + 1)):
`∃ γ, ∀ x y t, ((t ⊕ x) +[pγ] y) ∼[r] ((t ⊕ y) +[pγ] x)`, `pγ := 1/((γ t).1 + 1)`. -/
def γIndifference [inst : ConcatMixSpace α] (r : Relation α) : Prop :=
  ∃ γ : UniType inst.T → IntervalType, ∀ x y : α, ∀ t : UniType inst.T,
    let pγ : IntervalType := ⟨1/((γ t).1 + 1), indiff_mem_Icc (γ t).2⟩
    ((t ⊕ x) +[pγ] y) ∼[r] ((t ⊕ y) +[pγ] x)

end RewardFunctions

section DynamicConsistency

/-! ## Dynamic consistency -/

/-! ### vNM ⇒ (γ-indifference ⇒ dynamic consistency) -/

/-- vNM ⇒ (γ-indifference ⇒ dynamic consistency):
`VNMAxioms r → (γIndifference r → DynamicConsistency r)`. -/
theorem dynamicConsistency_of_γIndifference [ConcatMixSpace α] (r : Relation α) :
    VNMAxioms r → (γIndifference r → DynamicConsistency r) := by
  intro hvNM hγindiff
  rcases hγindiff with ⟨γ, hγindiff⟩
  intro x y t hxy
  -- ===== A utility function u representing r =====
  -- Make utility function u representing r
  have huexists := (vNM_theorem r).mp hvNM
  rcases huexists with ⟨u, hutility⟩
  rcases hutility with ⟨hoc, hplin⟩
  -- ===== γ-indifference in terms of u =====
  -- Apply this in the γ-indifference property
  let pγ : IntervalType := ⟨1/((γ t).1 + 1), indiff_mem_Icc (γ t).2⟩
  have hγprop := hγindiff x y t
  -- Transform it into u
  -- u((t ⊕ x)+[pγ]y) = u((t ⊕ y)+[pγ]x)
  have hueq := by
    have hγprop' : ((t ⊕ x) +[pγ] y) ∼[r] ((t ⊕ y) +[pγ] x) := hγprop
    have hge := (hoc ((t ⊕ x) +[pγ] y) ((t ⊕ y) +[pγ] x)).mp hγprop'.left
    have hle := (hoc ((t ⊕ y) +[pγ] x) ((t ⊕ x) +[pγ] y)).mp hγprop'.right
    have hueq : u ((t ⊕ x) +[pγ] y) = u ((t ⊕ y) +[pγ] x) := le_antisymm hle hge
    exact hueq
  -- Use linear property to expand both sides
  -- pγ u(t ⊕ x) + (1 - pγ) u(y) = pγ u(t ⊕ y) + (1 - pγ) u(x)
  have hulin : pγ.1 * u (t ⊕ x) + (1 - pγ.1) * u y =
      pγ.1 * u (t ⊕ y) + (1 - pγ.1) * u x := by
    rw [hplin (t ⊕ x) y pγ] at hueq
    rw [hplin (t ⊕ y) x pγ] at hueq
    exact hueq
  -- Rearranging terms
  -- pγ (u(t ⊕ x) - u(t ⊕ y)) = (1 - pγ) (u(x) - u(y))
  have hurearr : pγ.1 * (u (t ⊕ x) - u (t ⊕ y)) = (1 - pγ.1) * (u x - u y) := by
    linarith [hulin]
  -- ===== Sign argument: u(t ⊕ x) - u(t ⊕ y) ≥ 0 =====
  -- Since x ≽[r] y, u(x) - u(y) ≥ 0
  have hdiffxy : u x - u y ≥ 0 := by
    have huxy := (hoc x y).mp hxy
    linarith
  -- Also, pγ.1 > 0 and (1 - pγ.1) ≥ 0
  have hpγpos : pγ.1 > 0 := by
    have hpos : 0 < (γ t).1 + 1 := by
      have hnonneg : 0 ≤ (γ t).1 := (γ t).2.left
      linarith
    exact one_div_pos.mpr hpos
  have h1pγ : (1 - pγ.1) ≥ 0 := (comm_mem_Icc pγ.2).1
  -- Therefore, u(t ⊕ x) - u(t ⊕ y) ≥ 0
  have hdifftxy : u (t ⊕ x) - u (t ⊕ y) ≥ 0 := by
    have hrhs : (1 - pγ.1) * (u x - u y) ≥ 0 := by
      apply mul_nonneg h1pγ
      linarith
    have hlhs : pγ.1 * (u (t ⊕ x) - u (t ⊕ y)) ≥ 0 := by
      rw [hurearr]
      exact hrhs
    have hor := mul_nonneg_iff.mp hlhs
    have hboth : pγ.1 ≥ 0 ∧ (u (t ⊕ x) - u (t ⊕ y)) ≥ 0 :=
      hor.resolve_right (not_and_or.mpr (Or.inl (not_le_of_gt hpγpos)))
    exact hboth.2
  -- ===== Conclude: t ⊕ x ≽ t ⊕ y =====
  -- And so u(t ⊕ x) ≥ u(t ⊕ y)
  have hutxy : u (t ⊕ x) ≥ u (t ⊕ y) := by
    linarith [hdifftxy]
  -- Thus, (t ⊕ x) ≽[r] (t ⊕ y)
  have htxty : (t ⊕ x) ≽[r] (t ⊕ y) := (hoc (t ⊕ x) (t ⊕ y)).mpr hutxy
  exact htxty

/-! ### vNM ∧ dynamic consistency ⇒ u(t ⊕ x) = u(t) + F(t, x) u(x) with F(t, x) ≥ 0 -/

/-- vNM ∧ dynamic consistency ⇒ ∃ utility u and F ≥ 0 with u(t ⊕ x) = u(t) + F(t, x) u(x):
`VNMAxioms r ∧ DynamicConsistency r → ∃ u, UtilityFunction u r ∧
∃ F, ∀ x t, u (t ⊕ x) = u t.1 + F (t, x) * u x ∧ F (t, x) ≥ 0`. -/
theorem recursive_of_dynamicConsistency [inst : ConcatMixSpace α] (r : Relation α) :
    VNMAxioms r ∧ DynamicConsistency r → ∃ u : α → ℝ, UtilityFunction u r ∧
    ∃ F : (UniType inst.T) × α → ℝ, ∀ (x : α) (t : UniType inst.T),
    u (t ⊕ x) = u t.1 + F (t, x) * u x ∧ F (t, x) ≥ 0 := by
  intro h
  rcases h with ⟨hvNM, hdc⟩
  -- ===== A utility function u with u(ε) = 0 =====
  -- Existence of utility function from vNM theorem
  have huexists := (vNM_theorem r).mp hvNM
  -- Set u(ε) = 0
  have huoffset := utility_offset r huexists 0 inst.ε
  rcases huoffset with ⟨u, hutility, huε0⟩
  rcases hutility with ⟨hoc, hplin⟩
  -- ===== Define F =====
  -- Lets define F = (u(t ⊕ x) - u t.1) / u x if u x ≠ 0, and 0 otherwise
  let F : (UniType inst.T) × α → ℝ := fun tx ↦
    let t := tx.1
    let x := tx.2
    if u x = 0 then 0 else (u (t ⊕ x) - u t.1) / u x
  -- ===== F has the required properties =====
  have hF : ∀ (x : α) (t : UniType inst.T),
      u (t ⊕ x) = u t.1 + F (t, x) * u x ∧ F (t, x) ≥ 0 := by
    intro x t
    by_cases hux0 : u x = 0
    · -- ===== u(x) = 0 =====
      -- If u x = 0, u x = u ε
      have huxeε : u x = u inst.ε := by
        rw [← huε0] at hux0
        exact hux0
      -- So x ≽ ε and ε ≽ x
      have hxε : x ≽[r] inst.ε := (hoc x inst.ε).mpr (le_of_eq huxeε.symm)
      have hεx : inst.ε ≽[r] x := (hoc inst.ε x).mpr (le_of_eq huxeε)
      -- So by DC consistency, t ⊕ x ≽ t ⊕ ε and t ⊕ ε ≽ t ⊕ x
      have htxtε : (t ⊕ x) ≽[r] (t ⊕ inst.ε) := hdc x inst.ε t hxε
      have htεtx : (t ⊕ inst.ε) ≽[r] (t ⊕ x) := hdc inst.ε x t hεx
      -- So u(t ⊕ x) = u(t ⊕ ε) = u t.1
      have hutx : u (t ⊕ x) = u (t ⊕ inst.ε) := by
        have hge := (hoc (t ⊕ x) (t ⊕ inst.ε)).mp htxtε
        have hle := (hoc (t ⊕ inst.ε) (t ⊕ x)).mp htεtx
        exact le_antisymm hle hge
      have hutxred : u (t ⊕ x) = u t.1 := by
        rw [inst.concat_idempotent t] at hutx
        exact hutx
      -- So we have to prove u t.1 = u t.1 + F (t,x) * u x and F (t,x) ≥ 0
      -- which is true for any value F (t,x) ≥ 0, in particular F (t,x) = 0
      rw [hutxred]
      simp only [F, hux0, if_true, mul_zero, add_zero]
      exact ⟨trivial, le_rfl⟩
    · -- ===== u(x) ≠ 0 =====
      -- If u x ≠ 0, we can rearrange the definition of F
      have hFdef : F (t, x) = (u (t ⊕ x) - u t.1) / u x := by
        simp only [F, hux0, if_false]
      have hurec : u (t ⊕ x) = u t.1 + F (t, x) * u x := by
        rw [hFdef]
        field_simp [hux0]
        linarith
      -- We also need to show F (t,x) ≥ 0
      by_cases huxpos : u x > 0
      · -- If u x > 0 then x ≽ ε and
        -- u(x) ≥ 0 and u(t ⊕ x) - u(t) ≥ 0 by DC consistency
        have huxε : u x ≥ u inst.ε := by
          rw [← huε0] at huxpos
          exact le_of_lt huxpos
        have hxε : x ≽[r] inst.ε := (hoc x inst.ε).mpr huxε
        have htxtε : (t ⊕ x) ≽[r] (t ⊕ inst.ε) := hdc x inst.ε t hxε
        have hutxtε : u (t ⊕ x) ≥ u (t ⊕ inst.ε) := (hoc (t ⊕ x) (t ⊕ inst.ε)).mp htxtε
        have hutxt : u (t ⊕ x) ≥ u t.1 := by
          rw [inst.concat_idempotent t] at hutxtε
          exact hutxtε
        have hFnonneg : F (t, x) ≥ 0 := by
          rw [hFdef]
          field_simp [hux0]
          linarith
        exact ⟨hurec, hFnonneg⟩
      · -- If ¬ u(x) = 0 and ¬ u(x) > 0, then u(x) < 0
        have huxnonpos : u x ≤ 0 := by
          linarith
        have huεx : u x ≤ u inst.ε := by
          linarith
        -- So ε ≽ x and u(t ⊕ x) - u(t) ≤ 0 by DC consistency
        have hεx : inst.ε ≽[r] x := (hoc inst.ε x).mpr huεx
        have htεtx : (t ⊕ inst.ε) ≽[r] (t ⊕ x) := hdc inst.ε x t hεx
        have hutεtx : u (t ⊕ x) ≤ u (t ⊕ inst.ε) := (hoc (t ⊕ inst.ε) (t ⊕ x)).mp htεtx
        have huttx : u (t ⊕ x) ≤ u t.1 := by
          rw [inst.concat_idempotent t] at hutεtx
          exact hutεtx
        have hFnonneg : F (t, x) ≥ 0 := by
          rw [hFdef]
          field_simp [hux0]
          have hnum : u (t ⊕ x) - u t.1 ≤ 0 := by
            linarith
          exact div_nonneg_of_nonpos hnum huxnonpos
        exact ⟨hurec, hFnonneg⟩
  -- So we have u and F with the desired properties
  exact ⟨u, ⟨hoc, hplin⟩, F, hF⟩

end DynamicConsistency

section MarkovReward

/-! ## The Markov reward theorem -/

/-- Markov reward theorem (vNM axioms ∧ γ-indifference ⇔ ∃ reward function u):
`VNMAxioms r ∧ γIndifference r ↔ ∃ u : α → ℝ, RewardFunction u r`.

A preference relation on a concatenable mixture space satisfies completeness, transitivity,
independence, continuity and γ-indifference ⇔ there exists a reward function u : α → ℝ that
represents the preference relation.
Proof from Bowling et al. (2023) "Settling the Reward Hypothesis". -/
theorem markov_reward_theorem [inst : ConcatMixSpace α] (r : Relation α) :
    VNMAxioms r ∧ γIndifference r ↔ ∃ u : α → ℝ, RewardFunction u r := by
  constructor
  · -- ===== Forward direction: vNM ∧ γ-indifference → ∃ reward function =====
    intro h
    rcases h with ⟨hvNM, hγindiff⟩
    rcases hγindiff with ⟨γ, hγindiff⟩
    -- ===== A utility function u with u(ε) = 0 =====
    -- Existence of utility function from vNM theorem
    have huexists := (vNM_theorem r).mp hvNM
    -- Set u(ε) = 0
    have huoffset := utility_offset r huexists 0 inst.ε
    rcases huoffset with ⟨u, hutility, huε0⟩
    rcases hutility with ⟨hoc, hplin⟩
    -- ===== u is Markov recursive =====
    have humarkov : MarkovRecursive u := by
      refine ⟨γ, ?_⟩
      intro x t
      -- From γ-indifference choosing y = ε
      -- ((t ⊕ x)+[pγ]ε) ∼[r] ((t ⊕ ε)+[pγ]x)
      have hγprop := hγindiff x inst.ε t
      -- Transform it into u
      -- u((t ⊕ x)+[pγ]ε) = u((t ⊕ ε)+[pγ]x)
      let pγ' : IntervalType := ⟨1/((γ t).1 + 1), indiff_mem_Icc (γ t).2⟩
      have hγprop' : ((t ⊕ x) +[pγ'] inst.ε) ∼[r] ((t ⊕ inst.ε) +[pγ'] x) := hγprop
      have hge := (hoc ((t ⊕ x) +[pγ'] inst.ε) ((t ⊕ inst.ε) +[pγ'] x)).mp hγprop'.left
      have hle := (hoc ((t ⊕ inst.ε) +[pγ'] x) ((t ⊕ x) +[pγ'] inst.ε)).mp hγprop'.right
      have hueq : u ((t ⊕ x) +[pγ'] inst.ε) = u ((t ⊕ inst.ε) +[pγ'] x) :=
        le_antisymm hle hge
      -- Use linear property to expand both sides
      -- pγ' u(t ⊕ x) + (1 - pγ') u(ε) = pγ' u(t ⊕ ε) + (1 - pγ') u(x)
      have hulin : pγ'.1 * u (t ⊕ x) + (1 - pγ'.1) * u inst.ε =
          pγ'.1 * u (t ⊕ inst.ε) + (1 - pγ'.1) * u x := by
        rw [hplin (t ⊕ x) inst.ε pγ'] at hueq
        rw [hplin (t ⊕ inst.ε) x pγ'] at hueq
        exact hueq
      -- Reduce t ⊕ ε = t and u(ε) = 0
      -- pγ' u(t ⊕ x) = pγ' u(t) + (1 - pγ') u(x)
      have hured : pγ'.1 * u (t ⊕ x) = pγ'.1 * u t.1 + (1 - pγ'.1) * u x := by
        rw [inst.concat_idempotent t] at hulin
        rw [huε0] at hulin
        simp only [mul_zero, add_zero] at hulin
        exact hulin
      -- Multiply both sides by ((γ t).1 + 1)
      -- u(t ⊕ x) = u(t) + (γ t).1 * u(x)
      have hufinal : u (t ⊕ x) = u t.1 + (γ t).1 * u x := by
        have hmultpos : 0 < (γ t).1 + 1 := by
          have hnonneg : 0 ≤ (γ t).1 := (γ t).2.left
          linarith
        have hmult := by
          simp only [pγ'] at hured
          apply (congr_arg (fun z ↦ ((γ t).1 + 1) * z)) at hured
          field_simp [hmultpos] at hured
          simp only [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero] at hured
          exact hured
        exact hmult
      exact ⟨hufinal, huε0⟩
    -- So this u is ordinal consistent, p-linear and MarkovRecursive
    exact ⟨u, hoc, hplin, humarkov⟩
  · -- ===== Backward direction: ∃ reward function → vNM ∧ γ-indifference =====
    intro h
    -- ===== The vNM axioms =====
    -- The vNM axioms come from the reward function being a utility function
    -- and the vNM theorem
    have hvNM : VNMAxioms r := by
      rcases h with ⟨u, hreward⟩
      rcases hreward with ⟨hoc, hplin, _⟩
      have huutility : ∃ u, UtilityFunction u r := ⟨u, ⟨hoc, hplin⟩⟩
      exact (vNM_theorem r).mpr huutility
    -- ===== γ-indifference =====
    -- γ-indifference comes from the MarkovRecursive property
    have hγindiff : γIndifference r := by
      rcases h with ⟨u, hreward⟩
      rcases hreward with ⟨hoc, hplin, hmarkov⟩
      rcases hmarkov with ⟨γ, hrec⟩
      refine ⟨γ, ?_⟩
      intro x y t
      let pγ : IntervalType := ⟨1/((γ t).1 + 1), indiff_mem_Icc (γ t).2⟩
      -- First, we express as u(t ⊕ x) - (γ t) * u x = u t.1
      have hutx : u (t ⊕ x) - (γ t).1 * u x = u t.1 := by
        linarith [(hrec x t).1]
      have huty : u (t ⊕ y) - (γ t).1 * u y = u t.1 := by
        linarith [(hrec y t).1]
      -- Then, u(t ⊕ x) - (γ t) * u x = u(t ⊕ y) - (γ t) * u y
      have hueq : u (t ⊕ x) - (γ t).1 * u x = u (t ⊕ y) - (γ t).1 * u y := by
        linarith [hutx, huty]
      -- Rearranging, we get:
      -- u(t ⊕ x) + (γ t) * u y = u(t ⊕ y) + (γ t) * u x
      have hurearr : u (t ⊕ x) + (γ t).1 * u y = u (t ⊕ y) + (γ t).1 * u x := by
        linarith [hueq]
      -- Now, we multiply both sides by 1/((γ t).1 + 1)
      -- (1/((γ t).1 + 1)) u(t ⊕ x) + (1 - (1/((γ t).1 + 1))) u y
      -- = (1/((γ t).1 + 1)) u(t ⊕ y) + (1 - (1/((γ t).1 + 1))) u x
      have hmul : (1/((γ t).1 + 1)) * u (t ⊕ x) + (1 - (1/((γ t).1 + 1))) * u y =
          (1/((γ t).1 + 1)) * u (t ⊕ y) + (1 - (1/((γ t).1 + 1))) * u x := by
        have hmultpos : 0 < (γ t).1 + 1 := by
          have hnonneg : 0 ≤ (γ t).1 := (γ t).2.left
          linarith
        have hmultinv : (1/((γ t).1 + 1)) * (γ t).1 = 1 - 1/((γ t).1 + 1) := by
          field_simp [hmultpos]
          linarith
        have hmult := by
          apply (congr_arg (fun z ↦ (1/((γ t).1 + 1)) * z)) at hurearr
          rw [mul_add, ← mul_assoc, mul_add, ← mul_assoc] at hurearr
          rw [hmultinv] at hurearr
          exact hurearr
        exact hmult
      -- We use pγ to rewrite both sides (just syntax)
      -- pγ.1 * u(t ⊕ x) + (1 - pγ.1) * u y = pγ.1 * u(t ⊕ y) + (1 - pγ.1) * u x
      have hmulpγ : pγ.1 * u (t ⊕ x) + (1 - pγ.1) * u y =
          pγ.1 * u (t ⊕ y) + (1 - pγ.1) * u x := hmul
      -- Use linearity to rewrite as mixtures
      -- u((t ⊕ x)+[pγ]y) = u((t ⊕ y)+[pγ]x)
      have humix : u ((t ⊕ x) +[pγ] y) = u ((t ⊕ y) +[pγ] x) := by
        rw [← hplin (t ⊕ x) y pγ] at hmulpγ
        rw [← hplin (t ⊕ y) x pγ] at hmulpγ
        exact hmulpγ
      -- Use ordinal consistency to get indifference
      -- ((t ⊕ x) +[pγ] y) ∼[r] ((t ⊕ y) +[pγ] x)
      have hindiff : ((t ⊕ x) +[pγ] y) ∼[r] ((t ⊕ y) +[pγ] x) := by
        have hge := (hoc ((t ⊕ x) +[pγ] y) ((t ⊕ y) +[pγ] x)).mpr (ge_of_eq humix)
        have hle := (hoc ((t ⊕ y) +[pγ] x) ((t ⊕ x) +[pγ] y)).mpr (ge_of_eq humix.symm)
        exact ⟨hge, hle⟩
      exact hindiff
    -- So we have both parts
    exact ⟨hvNM, hγindiff⟩

end MarkovReward

end Reward
