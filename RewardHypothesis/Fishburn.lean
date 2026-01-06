/-
Copyright (c) 2025 Guillermo Martín-Sanchez . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guillermo Martín-Sánchez
-/

import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Data.Set.Countable
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Rat.Encodable



namespace OrdinalRep


/-
Define a preference measure on the space.
-/
def Relation (α : Type*) := α → α → Prop
notation lhs " ≽[" r "]" rhs:50 => r lhs rhs


/-
Useful definitions
-/
def strict (r : Relation α) : Relation α :=
  fun x y => (x ≽[r] y) ∧ ¬(y ≽[r] x)
notation lhs " ≻[" r "]" rhs:50 => strict r lhs rhs

def indiff (r : Relation α) : Relation α :=
  fun x y => (x ≽[r] y) ∧ (y ≽[r] x)
notation lhs " ∼[" r "]" rhs:50 => indiff r lhs rhs

def indiff_strict (r : Relation α) : Relation α :=
  fun x y => ¬ (x ≽[r] y) ∧ ¬ (y ≽[r] x)
notation lhs " ∼ₛ[" r "]" rhs:50 => indiff_strict r lhs rhs

/-
Define the axioms for ordinal representation on a preference relation.
-/
def completeness (r : Relation α) : Prop :=
  ∀ x y : α, x ≽[r] y ∨ y ≽[r] x

def transitivity (r : Relation α) : Prop :=
  ∀ x y z : α, (x ≽[r] y ∧ y ≽[r] z) → x ≽[r] z

def ordinal (r : Relation α) : Prop :=
  completeness r ∧
  transitivity r


/-
Define what it means for a function to represent the preference relation.
-/

def ordinal_consistent (u : α → ℝ) (r : Relation α) : Prop :=
  ∀ x y : α, (x ≽[r] y) ↔ (u x ≥ u y)

def ordinal_consistent_strict (u : α → ℝ) (rs : Relation α) : Prop :=
  ∀ x y : α, (x ≽[rs] y) ↔ (u x > u y)

/-
Axioms for the associated strict preference relation
-/

def asymmetry (rs : Relation α) : Prop :=
  ∀ x y : α, (x ≽[rs] y) → ¬(y ≽[rs] x)

def negative_transitivity (rs : Relation α) : Prop :=
  ∀ x y z : α, ¬(x ≽[rs] y) ∧ ¬(y ≽[rs] z) → ¬(x ≽[rs] z)

def weak_order (rs : Relation α) : Prop :=
  asymmetry rs ∧ negative_transitivity rs

/-
Definition of quotient space X \ ∼ and relation on the quotient >
-/
def IndiffQuot (rs : Relation α) : Type* :=
  Quot (fun x y  => (x ∼ₛ[rs] y))

def IndiffQuotRel (rs : Relation α) (h : weak_order rs) : IndiffQuot rs → IndiffQuot rs → Prop :=
  Quot.lift₂ (r := fun x y => x ∼ₛ[rs] y) (s := fun x y => x ∼ₛ[rs] y) (fun x y => x ≽[rs] y)
  (by
    intro a b₁ b₂ h_b1b2
    rcases h_b1b2 with ⟨h_nb1b2, h_nb2b1⟩
    apply propext
    constructor
    · intro h_ab1
      by_contra h_nab2
      have h_nab1 := h.right a b₂ b₁ ⟨h_nab2, h_nb2b1⟩
      exact h_nab1 h_ab1
    · intro h_ab2
      by_contra h_nab1
      have h_nab2 := h.right a b₁ b₂ ⟨h_nab1, h_nb1b2⟩
      exact h_nab2 h_ab2
  )
  (by
    intro a₁ a₂ b h_a1a2
    rcases h_a1a2 with ⟨h_na1a2, h_na2a1⟩
    apply propext
    constructor
    · intro h_a1b
      by_contra h_na2b
      have h_na1b := h.right a₁ a₂ b ⟨h_na1a2, h_na2b⟩
      exact h_na1b h_a1b
    · intro h_a2b
      by_contra h_na1b
      have h_na2b := h.right a₂ a₁ b ⟨h_na2a1, h_na1b⟩
      exact h_na2b h_a2b
  )

/-
Axioms for order separability in quotient space
-/
def order_dense (D : Set α) (rs : Relation α) : Prop :=
  ∀ x y : α, (x ≽[rs] y) ∧ x ∉ D ∧ y ∉ D → ∃ z ∈ D, (x ≽[rs] z ∧ z ≽[rs] y)

def order_separable (rs : Relation α) : Prop :=
  ∃ D : Set α, Countable D ∧ order_dense D rs

/-
If the relation is ordinal, then indifference and strict indifference are the same.
-/
theorem indiff_eq_indiff_strict {r : Relation α} (h_ordinal : ordinal r) :
  ∀ x y : α, (x ∼[r] y) ↔ (x ∼ₛ[strict r] y) := by
  intro x y
  apply Iff.intro
  · -- Forward direction: x ∼[r] y → x ∼ₛ[strict r] y
    intro h_xy
    rcases h_xy with ⟨h_xy1, h_xy2⟩
    constructor
    · -- ¬(x ≽[strict r] y)
      intro h_xgy
      rcases h_xgy with ⟨h_xgy1, h_xgy2⟩
      exact h_xgy2 h_xy2
    · -- ¬(y ≽[strict r] x)
      intro h_ygx
      rcases h_ygx with ⟨h_ygx1, h_ygx2⟩
      exact h_ygx2 h_xy1
  · -- Backward direction: x ∼ₛ[strict r] y → x ∼[r] y
    intro h_xy
    rcases h_xy with ⟨h_nxgy, h_nygx⟩
    have h_yx_exp := not_and_or.mp h_nygx
    have h_xgy_exp := not_and_or.mp h_nxgy
    constructor
    · -- x ≽[r] y
        by_contra h_not
        have h_yx := Or.resolve_left (h_ordinal.left x y) h_not
        have h_xy := not_not.mp (Or.resolve_left h_yx_exp (not_not.mpr h_yx))
        exact (h_not h_xy).elim
    · -- y ≽[r] x
      by_contra h_not
      have h_xy := Or.resolve_right (h_ordinal.left x y) h_not
      have h_yx := not_not.mp (Or.resolve_left h_xgy_exp (not_not.mpr h_xy))
      exact (h_not h_yx).elim

/-
Statment of Fishburn Theorem: A preference relation on a set satisfies
being a weak order and order separability on the quotient induced, if and only if
there exists a function f : Set → ℝ that strictly represents the preference relation.
-/
theorem Fishburn_theorem (rs : Relation α) :
  (∃ h : weak_order rs, order_separable (IndiffQuotRel rs h)) ↔ ∃ f : α → ℝ, ordinal_consistent_strict f rs := by
  apply Iff.intro
  · -- Forward direction: weak order ∧ order_separable → ∃ function
    sorry
  · -- Backward direction: ∃ function → weak order ∧ order_separable
    intro h_exists
    rcases h_exists with ⟨f, h_ord_cons_strict⟩

    -- Weak order
    have h_weak_order : weak_order rs := by
      -- rs is asymmetric
      have h_asym : asymmetry rs := by
        intro x y h_xy h_yx
        have h_fx_gt_fy := (h_ord_cons_strict x y).mp h_xy
        have h_fy_gt_fx := (h_ord_cons_strict y x).mp h_yx
        exact not_le.mpr h_fy_gt_fx (le_of_lt h_fx_gt_fy)
      -- rs is negatively transitive
      have h_neg_trans : negative_transitivity rs := by
        intro x y z h_not_xyz
        rcases h_not_xyz with ⟨h_not_xy, h_not_yz⟩
        have h_nfx_gt_fy : ¬ (f x > f y) := by
          intro h_fx_gt_fy
          exact h_not_xy ((h_ord_cons_strict x y).mpr h_fx_gt_fy)
        have h_nfy_gt_fz : ¬ (f y > f z) := by
          intro h_fy_gt_fz
          exact h_not_yz ((h_ord_cons_strict y z).mpr h_fy_gt_fz)
        have h_nfz_gt_fx : ¬ (f x > f z) := by
          intro h_fx_gt_fz
          have h_fy_ge_fz := le_of_not_gt h_nfy_gt_fz
          have h_fx_gt_fy := le_of_not_gt h_nfx_gt_fy
          exact (not_lt.mpr (le_trans h_fx_gt_fy h_fy_ge_fz)) h_fx_gt_fz
        intro h_xz
        exact h_nfz_gt_fx ((h_ord_cons_strict x z).mp h_xz)
      exact ⟨h_asym, h_neg_trans⟩

    -- Order separability
    have h_order_separable : order_separable (IndiffQuotRel rs h_weak_order) := by
      -- Define a countable dense subset A as one element of the quotient
      -- for each rational interval (a, b)

      -- Set of closed intervals with rational endpoints
      let Cs : Set (Set ℝ) :=
        { C | ∃ (p q : ℚ) (hpq : p < q), C = { x : ℝ | p ≤ x ∧ x ≤ q } }

      -- Subset of intervals that contain at least one image of f
      let Is : Set (Set ℝ) :=
        { I | ∃ (C : Set ℝ) (hc: C ∈ Cs) (x : α), f x ∈ C ∧ I = C}
      have h_Is_nonempty : ∀ I ∈ Is, ∃ fx, fx ∈ I := by
        intro I h_I
        rcases h_I with ⟨C, h_C_in_Cs, x, h_fx_in_C, h_I_eq_C⟩
        exact ⟨f x, by rw [h_I_eq_C]; exact h_fx_in_C⟩

      -- Set of images per interval
      let pAs : Set (Set (IndiffQuot rs)) :=
        { S | ∃ (I : Set ℝ) (hI : I ∈ Is) (x: α), f x ∈ I ∧ S = {Quot.mk _ x}}
      have h_pAs_nonempty : ∀ S ∈ pAs, ∃ a, a ∈ S := by
        intro S h_S
        rcases h_S with ⟨I, h_I_in_Is, x, h_fx_in_I, h_S_eq⟩
        exact ⟨Quot.mk _ x, by rw [h_S_eq]; exact Set.mem_singleton _⟩

      -- Random choice of one element per image set
      let A : Set (IndiffQuot rs) :=
        { a | ∃ (S : Set (IndiffQuot rs)) (hS : S ∈ pAs), a = Classical.choose (h_pAs_nonempty S hS)}

      -- Show that A is countable
      have h_A_countable : Countable A := by
        -- Show that Cs is countable
        have h_C_countable : Countable Cs := by
          let P := { pq : ℚ × ℚ | pq.1 < pq.2 }
          have h_P_countable : Countable P := by
            let QxQ := { pq : ℚ × ℚ | True }
            have h_QxQ_countable : Countable QxQ :=
              inferInstance
            have h_P_subset : P ⊆ QxQ := by
              intro pq h_pq
              trivial
            exact Set.Countable.mono h_P_subset h_QxQ_countable
          let f_Cs : (ℚ × ℚ) → Set ℝ := fun pq => { x : ℝ | pq.1 ≤ x ∧ x ≤ pq.2 }
          have h := Set.Countable.image h_P_countable f_Cs
          have h_C_img : Cs = f_Cs '' P := by
            ext C
            constructor
            · rintro ⟨p, q, hpq, rfl⟩
              have hpq_pair : (p,q) ∈ P := hpq
              use (p,q)
            · rintro ⟨⟨p,q⟩, hpq, rfl⟩
              exact ⟨p, q, hpq ,rfl⟩
          rw [←h_C_img] at h
          exact h
        -- Show that Is is countable
        have h_I_countable : Countable Is := by
          have h_I_subset : Is ⊆ Cs := by
            intro I h_I
            rcases h_I with ⟨C, h_C_in_Cs, x, h_fx_in_C, h_I_eq_C⟩
            rw [h_I_eq_C]
            exact h_C_in_Cs
          exact Set.Countable.mono h_I_subset h_C_countable
        -- Show that pAs is countable
        have h_pA_countable : Countable pAs := by
          let f_pAs : Is → Set (IndiffQuot rs) := fun I =>
            { Quot.mk _ x | ∃ x : α, f x ∈ I }





/-
If the relation is ordinal, then the associated strict relation is a weak order.
-/
theorem weak_if_ordinal {r : Relation α} :
  ordinal r → weak_order (strict r) := by
  intro h_ordinal
  -- Show that rs is a weak order from r being ordinal
  have h_comp := h_ordinal.left
  have h_trans := h_ordinal.right
  have h_weak_order : weak_order (strict r) := by
    constructor
    · -- Asymmetry
      intro x y h_xy h_yx
      exact h_yx.right h_xy.left
    · -- Negative transitivity
      -- We get y ≽ x and z ≽ y from the negations
      intro x y z h_not h_xz
      rcases h_not with ⟨h_not_xy, h_not_yz⟩
      have h_yx : y ≽[r] x := by
        rcases not_and_or.mp h_not_xy with h_nxy | h_nnyx
        · cases h_comp x y with
          | inl h_xy => cases h_nxy h_xy
          | inr h_yx => exact h_yx
        · exact not_not.mp h_nnyx
      have h_zy : z ≽[r] y := by
        rcases not_and_or.mp h_not_yz with h_nyz | h_nzy
        · cases h_comp y z with
          | inl h_yz => cases h_nyz h_yz
          | inr h_zy => exact h_zy
        · exact not_not.mp h_nzy
      -- Apply transitivity to get z ≽ x and contradiction with x > z
      exact h_xz.right (h_trans z y x ⟨h_zy, h_yx⟩)
  exact h_weak_order

/-
If the relation is complete, then previous results can be strengthened to an equivalence.
-/
theorem c_weak_iff_ordinal {r : Relation α} :
  completeness r → (ordinal r ↔ weak_order (strict r)) := by
  intro h_compl
  apply Iff.intro
  · -- Forward direction: ordinal r → weak_order (strict r)
    -- Always true, without completeness
    intro h_ordinal
    exact weak_if_ordinal h_ordinal
  · -- Backward direction: weak_order (strict r) → ordinal r
    intro h_weak_order
    rcases h_weak_order with ⟨h_asym, h_neg_trans⟩
    constructor
    · -- Completeness
      exact h_compl
    · -- Transitivity
      intro x y z h_xyz
      rcases h_xyz with ⟨h_xy, h_yz⟩
      have h_nzy : ¬(z ≻[r] x) := by
        have h_nyx : ¬(y ≻[r] x) := by
          intro h_yx
          exact h_yx.right h_xy
        have h_nzy : ¬(z ≻[r] y) := by
          intro h_zy
          exact h_zy.right h_yz
        exact h_neg_trans z y x ⟨h_nzy, h_nyx⟩
      cases not_and_or.mp h_nzy with
      | inl h_nzx =>
        cases (h_compl z x) with
        | inl h_zx => exact absurd h_zx h_nzx
        | inr h_xz => exact h_xz
      | inr h_nnxz => exact not_not.mp h_nnxz

/-
If f is ordinal consistent with r, then it is strictly ordinal consistent with strict r.
-/
theorem strict_ordinal_consistent_if_consistent {r : Relation α} {f : α → ℝ} :
  ordinal_consistent f r → ordinal_consistent_strict f (strict r) := by
  intro h_ord_consistency x y
  apply Iff.intro
  · -- x ≻[r] y → f x > f y
    intro h_xy
    have h_nfy_ge_fx : ¬(f y ≥ f x) := by
      intro h_fy_ge_fx
      have h_yx : y ≽[r] x := (h_ord_consistency y x).mpr h_fy_ge_fx
      exact h_xy.right h_yx
    exact lt_of_not_ge h_nfy_ge_fx
  · -- f x > f y → x ≻[r] y
    intro h_fx_g_fy
    have h_nyx : ¬(y ≽[r] x) := by
      intro h_yx
      have h_fy_ge_fx := (h_ord_consistency y x).mp h_yx
      exact not_lt.mpr h_fy_ge_fx h_fx_g_fy
    have h_xy : x ≽[r] y := (h_ord_consistency x y).mpr (le_of_lt h_fx_g_fy)
    exact ⟨h_xy, h_nyx⟩

/-
If r is complete, then f is ordinal consistent with r if and only if it is strictly
ordinal consistent with strict r.
-/
theorem c_strict_ordinal_consistent_iff_consistent {r : Relation α} {f : α → ℝ} :
  completeness r → (ordinal_consistent f r ↔ ordinal_consistent_strict f (strict r)) := by
  intro h_compl
  apply Iff.intro
  · -- Forward direction: ordinal_consistent f r → ordinal_consistent_strict f (strict r)
    -- Always true, without completeness
    intro h_ord_consistency
    exact strict_ordinal_consistent_if_consistent h_ord_consistency
  · -- Backward direction: ordinal_consistent_strict f (strict r) → ordinal_consistent f r
    intro h_ord_consistency_strict x y
    apply Iff.intro
    · -- x ≽[r] y → f x ≥ f y
      intro h_xy
      have h_ny_g_x : ¬ (y ≻[r] x) := by
        intro h_yx
        exact h_yx.right h_xy
      have h_yx : ¬ (f y > f x) := by
        intro h_fy_gt_fx
        exact h_ny_g_x ((h_ord_consistency_strict y x).mpr h_fy_gt_fx)
      exact le_of_not_gt h_yx
    · -- f x ≥ f y → x ≽[r] y
      intro h_fx_ge_fy
      have h_ny_g_x : ¬ (y ≻[r] x) := by
        intro h_yx
        have h_fy_gt_fx := (h_ord_consistency_strict y x).mp h_yx
        exact not_le.mpr h_fy_gt_fx h_fx_ge_fy
      cases not_and_or.mp h_ny_g_x with
      | inl h_nyx =>
        cases (h_compl x y) with
        | inl h_xy => exact h_xy
        | inr h_yx => exact absurd h_yx h_nyx
      | inr h_nnxy => exact not_not.mp h_nnxy

/-
Main Ordinal Theorem: A preference relation on a set satisfies
completeness and transitivity, and its order separable on the quotient induced
if and only if there exists a function f : Set → ℝ that represents the preference relation.
-/
theorem ordinal_theorem (r : Relation α) :
  (∃ h : ordinal r, order_separable (IndiffQuotRel (strict r) (weak_if_ordinal h)))
    ↔ ∃ f : α → ℝ, ordinal_consistent f r := by
  apply Iff.intro
  · -- Forward direction: ordinal axioms ∧ order_separable → ∃ function
    intro h
    rcases h with ⟨h_ordinal, h_order_sep⟩
    let h_comp := h_ordinal.left
    -- r is ordinal → strict r is weak order
    have h_weak_order := weak_if_ordinal h_ordinal
    -- Apply Fishburn theorem to strict r
    have h_f_strict : ∃ f : α → ℝ, ordinal_consistent_strict f (strict r) :=
      (Fishburn_theorem (strict r)).mp ⟨h_weak_order, h_order_sep⟩
    -- Strict ordinal consistency ↔ ordinal consistency
    rcases h_f_strict with ⟨f, h_ord_cons_strict⟩
    have h_ord_cons : ordinal_consistent f r :=
      (c_strict_ordinal_consistent_iff_consistent h_comp).mpr h_ord_cons_strict
    exact ⟨f, h_ord_cons⟩
  · -- Backward direction: ∃ function → ordinal axioms ∧ order_separable
    intro h_exists
    rcases h_exists with ⟨f, h_ord_cons⟩
    -- ∃ f → r is complete
    have h_comp : completeness r := by
      intro x y
      by_cases h_fx_ge_fy : f x ≥ f y
      · -- f x ≥ f y
        apply Or.inl
        exact (h_ord_cons x y).mpr h_fx_ge_fy
      · -- ¬(f x ≥ f y) → f y > f x
        apply Or.inr
        exact (h_ord_cons y x).mpr (le_of_not_ge h_fx_ge_fy)
    -- r complete → (f ordinal consistent → f strict r ordinal consistent)
    have h_ord_cons_strict : ordinal_consistent_strict f (strict r) :=
      strict_ordinal_consistent_if_consistent h_ord_cons
    -- Apply Fishburn theorem to get weak order and order separable
    have h_fishburn : ∃ h : weak_order (strict r), order_separable (IndiffQuotRel (strict r) h) :=
      (Fishburn_theorem (strict r)).mpr ⟨f, h_ord_cons_strict⟩
    rcases h_fishburn with ⟨h_weak_order, h_order_sep⟩
    -- r complete → (strict r wak order → r ordinal)
    have h_ordinal : ordinal r := (c_weak_iff_ordinal h_comp).mpr h_weak_order
    exact ⟨h_ordinal, h_order_sep⟩

end OrdinalRep
