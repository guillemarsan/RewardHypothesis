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
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real


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

lemma indiff_symm (r : Relation α) :
  ∀ x y : α, (x ∼[r] y) → (y ∼[r] x) := by
  intro x y h_xy
  exact ⟨h_xy.right, h_xy.left⟩

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

lemma indiff_transitivity (r : Relation α) :
  transitivity r → ∀ x y z : α, (x ∼[r] y ∧ y ∼[r] z) → (x ∼[r] z) := by
  intro h_trans x y z h_xyz
  rcases h_xyz with ⟨h_xy, h_yz⟩
  exact ⟨h_trans x y z ⟨h_xy.left, h_yz.left⟩, h_trans z y x ⟨h_yz.right, h_xy.right⟩⟩

lemma highest_element (r : Relation α) :
  ordinal r → ∀ x y z : α, ∃ w : α, w ≽[r] x ∧ w ≽[r] y ∧ w ≽[r] z := by
  intro h_ordinal
  rcases h_ordinal with ⟨h_complete, h_trans⟩
  intro x y z
  have hxy := h_complete x y
  have hxz := h_complete x z
  have hyz := h_complete y z
  have h_largest: (x ≽[r] y ∧ x ≽[r] z) ∨
    (y ≽[r] x ∧ y ≽[r] z) ∨ (z ≽[r] x ∧ z ≽[r] y) := by
    cases hxy <;> cases hxz <;> cases hyz <;> aesop
  cases h_largest with
    | inl h_x_l =>
        exact ⟨x, ⟨(h_complete x x).elim id id, h_x_l⟩⟩
    | inr h_inr =>
      cases h_inr with
      | inl h_y_l =>
        exact ⟨y, ⟨h_y_l.left, (h_complete y y).elim id id, h_y_l.right⟩⟩
      | inr h_z_l =>
        exact ⟨z, ⟨h_z_l.left, h_z_l.right, (h_complete z z).elim id id⟩⟩

lemma lowest_element (r : Relation α) :
  ordinal r → ∀ x y z : α, ∃ w : α, x ≽[r] w ∧ y ≽[r] w ∧ z ≽[r] w := by
  intro h_ordinal
  rcases h_ordinal with ⟨h_complete, h_trans⟩
  intro x y z
  have hxy := h_complete x y
  have hxz := h_complete x z
  have hyz := h_complete y z
  have h_smallest: (y ≽[r] x ∧ z ≽[r] x) ∨
    (x ≽[r] y ∧ z ≽[r] y) ∨ (x ≽[r] z ∧ y ≽[r] z) := by
    cases hxy <;> cases hxz <;> cases hyz <;> aesop
  cases h_smallest with
    | inl h_x_s =>
        exact ⟨x, ⟨(h_complete x x).elim id id, h_x_s⟩⟩
    | inr h_inr =>
      cases h_inr with
      | inl h_y_s =>
        exact ⟨y, ⟨h_y_s.left, (h_complete y y).elim id id, h_y_s.right⟩⟩
      | inr h_z_s =>
        exact ⟨z, ⟨h_z_s.left, h_z_s.right, (h_complete z z).elim id id⟩⟩


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

lemma interval_endpoint_inside_of_intersection
  {a l₁ u₁ l₂ u₂ : ℝ}
  (h₁ : l₁ < a ∧ a < u₁)
  (h₂ : l₂ < a ∧ a < u₂)
  (hneq :
      (l₁ = l₂ → u₁ ≠ u₂) ∧
      (u₁ = u₂ → l₁ ≠ l₂)) :
  (l₁ < l₂ ∧ l₂ < u₁) ∨
  (l₁ < u₂ ∧ u₂ < u₁) ∨
  (l₂ < l₁ ∧ l₁ < u₂) ∨
  (l₂ < u₁ ∧ u₁ < u₂) :=
by
  rcases h₁ with ⟨h₁l, h₁u⟩
  rcases h₂ with ⟨h₂l, h₂u⟩
  have h_overlap₁ : l₁ < u₂ := by linarith
  have h_overlap₂ : l₂ < u₁ := by linarith
  -- split on whether lower endpoints are equal
  by_cases hll : l₁ = l₂
  · -- lower endpoints equal → upper endpoints differ
    have huu : u₁ ≠ u₂ := hneq.1 hll
    have hu : u₂ < u₁ ∨ u₁ < u₂ := lt_or_gt_of_ne huu.symm
    cases hu with
    | inl h =>
        -- u₂ < u₁
        right; left
        exact ⟨h_overlap₁, h⟩
    | inr h =>
        -- u₁ < u₂
        right; right; right
        exact ⟨h_overlap₂, h⟩
  · -- lower endpoints differ
    have hl : l₁ < l₂ ∨ l₂ < l₁ := lt_or_gt_of_ne hll
    cases hl with
    | inl h =>
        -- l₁ < l₂
        left
        exact ⟨h, h_overlap₂⟩
    | inr h =>
        -- l₂ < l₁
        right; right; left
        exact ⟨h, h_overlap₁⟩

/-
Statment of Fishburn Theorem: A preference relation on a set satisfies
being a weak order and order separability on the quotient induced, if and only if
there exists a function f : Set → ℝ that strictly represents the preference relation.
-/
theorem Fishburn_theorem (rs : Relation α) :
  (∃ h : weak_order rs, order_separable (IndiffQuotRel rs h))
  ↔ ∃ f : α → ℝ, ordinal_consistent_strict f rs := by
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

    -- Since it is a weak order, we can define the quotient space
    -- and lift most of the operations to the quotient
    let QuotSet := {q : IndiffQuot rs | True}
    let rq := IndiffQuotRel rs h_weak_order
    let fq : IndiffQuot rs → ℝ :=
      Quot.lift (r := fun x y => x ∼ₛ[rs] y) f
      (by
        -- a ∼ₛ[rs] b → f a = f b
        intro a b h_ab
        rcases h_ab with ⟨h_nab, h_nba⟩
        have h_fa_eq_fb : f a = f b := by
          have h_fa_ge_fb : f a ≥ f b := by
            by_contra h_nfa_ge_fb
            have h_fb_lt_fa := lt_of_not_ge h_nfa_ge_fb
            exact h_nba ((h_ord_cons_strict b a).mpr h_fb_lt_fa)
          have h_fb_ge_fa : f b ≥ f a := by
            by_contra h_nfb_ge_fa
            have h_fa_lt_fb := lt_of_not_ge h_nfb_ge_fa
            exact h_nab ((h_ord_cons_strict a b).mpr h_fa_lt_fb)
          exact le_antisymm h_fb_ge_fa h_fa_ge_fb
        exact h_fa_eq_fb
      )

    let h_ord_cons_strict_q : ∀ (a b : IndiffQuot rs), (a ≽[rq] b) ↔ (fq a > fq b) := by
      intro a b
      apply Iff.intro
      · -- a ≽[rq] b → fq a > fq b
        refine Quot.induction_on₂ a b ?_
        intro x y h_ab
        have h_xy : x ≽[rs] y := by
          simp only [rq, IndiffQuotRel] at h_ab
          exact h_ab
        have h_fx_gt_fy : f x > f y := by
          exact (h_ord_cons_strict x y).mp h_xy
        exact h_fx_gt_fy
      · -- fq a > fq b → a ≽[rq] b
        refine Quot.induction_on₂ a b ?_
        intro x y h_fa_gt_fb
        have h_fx_gt_fy : f x > f y := by
          exact h_fa_gt_fb
        have h_xy : x ≽[rs] y := by
          exact (h_ord_cons_strict x y).mpr h_fx_gt_fy
        simp only [rq, IndiffQuotRel]
        exact h_xy

    let h_id_cons_strict_q : ∀ (a b : IndiffQuot rs), (a = b) ↔ (fq a = fq b) := by
      intro a b
      apply Iff.intro
      · -- a = b → fq a = fq b
        intro h_ab
        rw [h_ab]
      · -- fq a = fq b → a = b
        intro h_fa_eq_fb
        have h_nfa_gt_fb : ¬ (fq a > fq b) := by
          have h_fa_eq_or_lt_fb : (fq b = fq a) ∨ (fq a < fq b) := by
            exact Or.inl h_fa_eq_fb.symm
          exact not_lt_iff_eq_or_lt.mpr h_fa_eq_or_lt_fb
        have h_nfb_gt_fa : ¬ (fq b > fq a) := by
          have h_fb_eq_or_lt_fa : (fq a = fq b) ∨ (fq b < fq a) := by
            exact Or.inl h_fa_eq_fb
          exact not_lt_iff_eq_or_lt.mpr h_fb_eq_or_lt_fa
        have h_na_rq_b : ¬ (a ≽[rq] b) := by
          intro h_a_rb
          have h_fa_gt_fb := (h_ord_cons_strict_q a b).mp h_a_rb
          exact h_nfa_gt_fb h_fa_gt_fb
        have h_nb_rq_a : ¬ (b ≽[rq] a) := by
          intro h_b_ra
          have h_fb_gt_fa := (h_ord_cons_strict_q b a).mp h_b_ra
          exact h_nfb_gt_fa h_fb_gt_fa
        have h_ab : a = b := by
          revert h_na_rq_b h_nb_rq_a
          refine Quot.induction_on₂ a b ?_
          intro x y h_na_rq_b h_nb_rq_a
          have h_nxy : ¬ (x ≽[rs] y) := by
            intro h_xy
            simp only [rq, IndiffQuotRel] at h_na_rq_b
            exact h_na_rq_b h_xy
          have h_nyx : ¬ (y ≽[rs] x) := by
            intro h_yx
            simp only [rq, IndiffQuotRel] at h_nb_rq_a
            exact h_nb_rq_a h_yx
          have h_xy_equiv : x ∼ₛ[rs] y := by
            exact ⟨h_nxy, h_nyx⟩
          exact Quot.sound h_xy_equiv
        exact h_ab


    -- Order separability
    have h_order_separable : order_separable (IndiffQuotRel rs h_weak_order) := by

      -- Define a countable set A as one element of the quotient
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
        { S | ∃ (I : Set ℝ) (hI : I ∈ Is), S = (Quot.mk _ '' { x : α | f x ∈ I })}
      have h_pAs_nonempty : ∀ S ∈ pAs, ∃ a, a ∈ S := by
        intro S h_S
        rcases h_S with ⟨I, h_I_in_Is, rfl⟩
        rcases h_Is_nonempty I h_I_in_Is with ⟨fx, h_fx_in_I⟩
        rcases h_I_in_Is with ⟨C, h_C_in_Cs, x, h_fx_in_C, h_I_eq_C⟩
        have h_set_nonempty : ∃ x : α, x ∈ {x : α | f x ∈ I} := by
          rw [←h_I_eq_C] at h_fx_in_C
          use x
          exact h_fx_in_C
        rcases h_set_nonempty with ⟨x0, h_x0_in_set⟩
        exact ⟨Quot.mk _ x0, ⟨x0, h_x0_in_set, rfl⟩⟩

      -- Random choice of one element per image set
      let A : Set (IndiffQuot rs) :=
        { a | ∃ (S : Set (IndiffQuot rs)) (hS : S ∈ pAs),
        a = Classical.choose (h_pAs_nonempty S hS)}

      -- Show that A is countable by chaining countability results
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
        have h_pAs_countable : Countable pAs := by
          let f_pAs : Set ℝ → Set (IndiffQuot rs) := fun I =>
            Set.image (Quot.mk _) { x : α | f x ∈ I}
          have h := Set.Countable.image h_I_countable f_pAs
          have h_pAs_img : pAs = f_pAs '' Is := by
            ext S
            constructor
            · rintro ⟨I, h_I_in_Is, rfl⟩
              use I
            · rintro ⟨I, h_I_in_Is, rfl⟩
              exact ⟨I, h_I_in_Is, rfl⟩
          rw [←h_pAs_img] at h
          exact h
        -- Finally, show that A is countable
        -- This requires subtypes for the axiom of choice
        let pAs_subtype := {S // S ∈ pAs}
        let pAs_set := {S : {S // S ∈ pAs} | True}
        let f_A : pAs_subtype → IndiffQuot rs := fun S =>
          Classical.choose (h_pAs_nonempty S.val S.property)
        have h_pAs_subtype_countable : Countable pAs_subtype := by
          exact Set.Countable.to_subtype h_pAs_countable
        have h_pAs_univ_countable : Countable pAs_set := by
          exact Set.countable_univ_iff.mpr h_pAs_subtype_countable
        have h := Set.Countable.image h_pAs_univ_countable f_A
        have h_A_img : A = f_A '' pAs_set := by
          ext a
          constructor
          · rintro ⟨S, hS_in_pAs, rfl⟩
            exact ⟨⟨S, hS_in_pAs⟩, trivial, rfl⟩
          · rintro ⟨⟨S, hS_in_pAs⟩, _, rfl⟩
            exact ⟨S, hS_in_pAs, rfl⟩
        rw [←h_A_img] at h
        exact h

      -- Define K
      let K : Set (IndiffQuot rs × IndiffQuot rs) :=
        { bc | bc.1 ∈ QuotSet \ A ∧ bc.2 ∈ QuotSet \ A
        ∧ bc.2 ≽[rq] bc.1 ∧ ¬ ∃ a ∈ A, bc.2 ≽[rq] a ∧ a ≽[rq] bc.1}

      -- Show that K is countable
      have h_K_countable : Countable K := by

        -- Show that intervals are empty of other f(a)
        have h_fbc_empty_fa : ∀ bc ∈ K, ¬ ∃ a ∈ QuotSet, bc.2 ≽[rq] a ∧ a ≽[rq] bc.1 := by
          intro bc h_bc
          rcases h_bc with ⟨h_b1_notin_A, h_b2_notin_A, h_b2_ge_b1, h_no_a_in_A⟩
          rintro ⟨a, h_a_in_QuotSet, h_b2_ge_a, h_a_ge_b1⟩
          -- Assume that there is such a, then there is d in A with f(bc.1) < f(d) < f(bc.2)
          -- which leads to contradiction of (b,c) ∈ K
          have h_d_in_A : ∃ d ∈ A, bc.2 ≽[rq] d ∧ d ≽[rq] bc.1 := by
            -- f(c) > f(a) > f(b)
            have h_fa_gt_fb1 : fq a > fq bc.1 := by
              exact (h_ord_cons_strict_q a bc.1).mp h_a_ge_b1
            have h_fbc2_gt_fa : fq bc.2 > fq a := by
              exact (h_ord_cons_strict_q bc.2 a).mp h_b2_ge_a
            -- Find an interval (p, q) with rational endpoints such that
            -- f(a) ∈ (p, q)
            obtain ⟨prat, h_prat1, h_prat2⟩ := exists_rat_btwn h_fa_gt_fb1
            obtain ⟨qrat, h_qrat1, h_qrat2⟩ := exists_rat_btwn h_fbc2_gt_fa
            have h_prat_lt_qrat : prat < qrat := by
              exact Rat.cast_lt.1 (lt_trans h_prat2 h_qrat1)
            -- Define the interval and show it is in Is
            let C := { x : ℝ | prat ≤ x ∧ x ≤ qrat }
            have h_C_in_Cs : C ∈ Cs := by
              use prat, qrat, h_prat_lt_qrat
            let I := C
            have h_fqa_in_I : fq a ∈ I := by
              exact ⟨le_of_lt h_prat2, le_of_lt h_qrat1⟩
            have h_I_in_Is : I ∈ Is := by
              cases a using Quot.inductionOn with
              | _ x =>
                have h_fx_in_C : f x ∈ C := by
                  simp only [fq] at h_fqa_in_I
                  exact h_fqa_in_I
                use C, h_C_in_Cs, x, h_fx_in_C
            -- Consider the set S in pAs
            let S := Quot.mk (fun x y => x ∼ₛ[rs] y) '' { x : α | f x ∈ I }
            have h_S_in_pAs : S ∈ pAs := by
              use I, h_I_in_Is
            -- The chosen element d in A
            let d := Classical.choose (h_pAs_nonempty S h_S_in_pAs)
            have h_d_in_A : d ∈ A := by
              use S, h_S_in_pAs
            -- Show that d satisfies the inequalities
            have h_d_in_bc : bc.2 ≽[rq] d ∧ d ≽[rq] bc.1 := by
              have h_d_in_S : d ∈ S := by
                exact Classical.choose_spec (h_pAs_nonempty S h_S_in_pAs)
              rcases h_d_in_S with ⟨x, h_fx_in_I, h_x_quotd⟩
              have h_fx_in_C : f x ∈ C := by
                simp only [I] at h_fx_in_I
                exact h_fx_in_I
              have h_d_ge_b1 : d ≽[rq] bc.1 := by
                have h_fx_gt_fb1 : f x > fq bc.1 := by
                  exact lt_of_lt_of_le h_prat1 h_fx_in_C.left
                have h_fqd_gt_fb1 : fq d > fq bc.1 := by
                  rw [←h_x_quotd]
                  simp only [fq]
                  exact h_fx_gt_fb1
                exact (h_ord_cons_strict_q d bc.1).mpr h_fqd_gt_fb1
              have h_b2_ge_d : bc.2 ≽[rq] d := by
                have h_fbc2_gt_fx : fq bc.2 > f x := by
                  exact lt_of_le_of_lt h_fx_in_C.right h_qrat2
                have h_fbc2_gt_fqd : fq bc.2 > fq d := by
                  rw [←h_x_quotd]
                  simp only [fq]
                  exact h_fbc2_gt_fx
                exact (h_ord_cons_strict_q bc.2 d).mpr h_fbc2_gt_fqd
              exact ⟨h_b2_ge_d, h_d_ge_b1⟩
            exact ⟨d, h_d_in_A, h_d_in_bc⟩
          exact h_no_a_in_A h_d_in_A

        -- Show that then these intervals (f(b), f(c)) are disjoint
        let s : IndiffQuot rs × IndiffQuot rs → Set ℝ := fun bc => Set.Ioo (fq bc.1) (fq bc.2)
        have h_fbfc_disjoint : K.PairwiseDisjoint s := by
          intro bc1 h_bc1_in_K bc2 h_bc2_in_K h_bc1_ne_bc2
          rw [Function.onFun, Disjoint]
          simp only [s, Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff]
          -- If x is in the intersection it has to be empty
          intro x h_x_in_Ioo1 h_x_in_Ioo2
          -- If its not empty, we can get an element and get a contradiction
          by_contra h_notempty
          have h_exists_a_in_x : ∃ a, a ∈ x := by
            exact Set.nonempty_def.mp (Set.nonempty_iff_ne_empty.mpr h_notempty)
          let a := Classical.choose h_exists_a_in_x
          have h_a_in_x : a ∈ x := Classical.choose_spec h_exists_a_in_x
          have h_a_in_Ioo1 : a ∈ Set.Ioo (fq bc1.1) (fq bc1.2) := by
            exact h_x_in_Ioo1 h_a_in_x
          have h_a_in_Ioo2 : a ∈ Set.Ioo (fq bc2.1) (fq bc2.2) := by
            exact h_x_in_Ioo2 h_a_in_x

          -- From this we get that one of the extremes is in one of the intervals
          -- First, both ends cannot be equal
          have h_proof_oneeq_otherneq :
            (bc1.1 = bc2.1 → bc1.2 ≠ bc2.2) ∧
            (bc1.2 = bc2.2 → bc1.1 ≠ bc2.1) := by
              constructor
              · intro h_eq1
                by_contra h_eq2
                have h_bc1_eq_bc2 : bc1 = bc2 := by
                  apply Prod.ext
                  · exact h_eq1
                  · exact h_eq2
                exact h_bc1_ne_bc2 h_bc1_eq_bc2
              · intro h_eq2
                by_contra h_eq1
                have h_bc1_eq_bc2 : bc1 = bc2 := by
                  apply Prod.ext
                  · exact h_eq1
                  · exact h_eq2
                exact h_bc1_ne_bc2 h_bc1_eq_bc2

          -- Second, both ends cannot be equal in f either
          have h_proof_oneeq_otherneq_f :
            (fq bc1.1 = fq bc2.1 → fq bc1.2 ≠ fq bc2.2) ∧
            (fq bc1.2 = fq bc2.2 → fq bc1.1 ≠ fq bc2.1) := by
            constructor
            · intro h_eq1
              by_contra h_eq2
              have h_bc1_eq_bc2 : bc1 = bc2 := by
                apply Prod.ext
                · exact (h_id_cons_strict_q bc1.1 bc2.1).mpr h_eq1
                · exact (h_id_cons_strict_q bc1.2 bc2.2).mpr h_eq2
              exact h_bc1_ne_bc2 h_bc1_eq_bc2
            · intro h_eq2
              by_contra h_eq1
              have h_bc1_eq_bc2 : bc1 = bc2 := by
                apply Prod.ext
                · exact (h_id_cons_strict_q bc1.1 bc2.1).mpr h_eq1
                · exact (h_id_cons_strict_q bc1.2 bc2.2).mpr h_eq2
              exact h_bc1_ne_bc2 h_bc1_eq_bc2

          -- Therefore, one of the endpoints is in the other's interval
          have h_one_is_in_f :
            (fq bc1.1 < fq bc2.1 ∧ fq bc2.1 < fq bc1.2) ∨
            (fq bc1.1 < fq bc2.2 ∧ fq bc2.2 < fq bc1.2) ∨
            (fq bc2.1 < fq bc1.1 ∧ fq bc1.1 < fq bc2.2) ∨
            (fq bc2.1 < fq bc1.2 ∧ fq bc1.2 < fq bc2.2) := by
              have ha1 := Set.mem_Ioo.mp h_a_in_Ioo1
              have ha2 := Set.mem_Ioo.mp h_a_in_Ioo2
              exact interval_endpoint_inside_of_intersection ha1 ha2 h_proof_oneeq_otherneq_f

          -- Therefore, there is an element of A in the interval
          have h_one_is_in :
            (bc2.1 ≽[rq] bc1.1 ∧ bc1.2 ≽[rq] bc2.1) ∨
            (bc2.2 ≽[rq] bc1.1 ∧ bc1.2 ≽[rq] bc2.2) ∨
            (bc1.1 ≽[rq] bc2.1 ∧ bc2.2 ≽[rq] bc1.1) ∨
            (bc1.2 ≽[rq] bc2.1 ∧ bc2.2 ≽[rq] bc1.2) := by
              simpa [h_ord_cons_strict_q] using h_one_is_in_f

          -- This contradicts the proprty of (b,c) ∈ K that they are empty of other f(a)
          have cont_fbc_empty {bc a} (hK : bc ∈ K)
            (h_in : a ∈ QuotSet) (h_rq : rq a bc.1 ∧ rq bc.2 a)
            (h_fbc_empty : ∀ bc ∈ K, ¬∃ a ∈ QuotSet, rq bc.2 a ∧ rq a bc.1) :
            False :=
            (h_fbc_empty bc hK) ⟨a, h_in, h_rq.right, h_rq.left⟩

          cases h_one_is_in with
          | inl h_bc2a1_bc1a1 =>
              exact cont_fbc_empty h_bc1_in_K (by trivial) h_bc2a1_bc1a1 h_fbc_empty_fa
          | inr h_rest =>
              cases h_rest with
              | inl h_bc2a2_bc1a1 =>
                  exact cont_fbc_empty h_bc1_in_K (by trivial) h_bc2a2_bc1a1 h_fbc_empty_fa
              | inr h_rest2 =>
                  cases h_rest2 with
                  | inl h_bc1a1_bc2a1 =>
                      exact cont_fbc_empty h_bc2_in_K (by trivial) h_bc1a1_bc2a1 h_fbc_empty_fa
                  | inr h_bc1a2_bc2a1 =>
                      exact cont_fbc_empty h_bc2_in_K (by trivial) h_bc1a2_bc2a1 h_fbc_empty_fa

        -- Show that since each (b,c) ∈ K defines (f(b),f(c)) as
        -- an open, non-empty, disjoint intervals in ℝ,
        -- then K is countable
        let s : IndiffQuot rs × IndiffQuot rs → Set ℝ := fun bc => Set.Ioo (fq bc.1) (fq bc.2)
        have h_fbfc_open: ∀ bc ∈ K, IsOpen (s bc) := by
          intro bc h_bc
          exact isOpen_Ioo
        have h_fbfc_nonempty : ∀ bc ∈ K, (s bc).Nonempty := by
          intro bc h_bc
          rcases h_bc with ⟨h_b1_notin_A, h_b2_notin_A, h_b2_ge_b1, h_no_a_in_A⟩
          have h_fbc2_gt_fbc1 : fq bc.2 > fq bc.1 := by
            exact (h_ord_cons_strict_q bc.2 bc.1).mp h_b2_ge_b1
          exact Set.nonempty_Ioo.2 h_fbc2_gt_fbc1
        exact Set.PairwiseDisjoint.countable_of_isOpen h_fbfc_disjoint h_fbfc_open h_fbfc_nonempty

      -- Define B
      let B : Set (IndiffQuot rs) :=
        { b | ∃ c ∈ QuotSet, ((b, c) ∈ K ∨ (c, b) ∈ K) }

      -- Show that B is countable
      have h_B_countable : Countable B := by
        -- Define subsets of B
        let Bl : Set (IndiffQuot rs) :=
          { b | ∃ c ∈ QuotSet, (b, c) ∈ K }
        let Br : Set (IndiffQuot rs) :=
          { b | ∃ c ∈ QuotSet, (c, b) ∈ K }
        -- Show they are countable as images of K
        have h_Bl_countable : Countable Bl := by
          let f_Bl : IndiffQuot rs × IndiffQuot rs → IndiffQuot rs := fun bc => bc.1
          have h_img_fbl_count := Set.Countable.image h_K_countable f_Bl
          have h_Bl_img : Bl = f_Bl '' K := by
            ext b
            constructor
            · rintro ⟨c, h_c_in_QuotSet, h_bc_in_K⟩
              exact ⟨(b, c), h_bc_in_K, rfl⟩
            · rintro ⟨⟨b, c⟩, h_bc_in_K, rfl⟩
              exact ⟨c,Set.mem_of_mem_diff h_bc_in_K.2.1, h_bc_in_K⟩
          rw [←h_Bl_img] at h_img_fbl_count
          exact h_img_fbl_count
        have h_Br_countable : Countable Br := by
          let f_Br : IndiffQuot rs × IndiffQuot rs → IndiffQuot rs := fun bc => bc.2
          have h_img_fbr_count := Set.Countable.image h_K_countable f_Br
          have h_Br_img : Br = f_Br '' K := by
            ext b
            constructor
            · rintro ⟨c, h_c_in_QuotSet, h_cb_in_K⟩
              exact ⟨(c, b), h_cb_in_K, rfl⟩
            · rintro ⟨⟨c, b⟩, h_cb_in_K, rfl⟩
              exact ⟨c, Set.mem_of_mem_diff h_cb_in_K.1, h_cb_in_K⟩
          rw [←h_Br_img] at h_img_fbr_count
          exact h_img_fbr_count
        -- Finally, B is the union of both
        have h_B_union : B = Bl ∪ Br := by
          ext b
          constructor
          · rintro ⟨c, h_c_in_QuotSet, h_bc_in_K_or_cb_in_K⟩
            cases h_bc_in_K_or_cb_in_K with
            | inl h_bc_in_K => exact Or.inl ⟨c, h_c_in_QuotSet, h_bc_in_K⟩
            | inr h_cb_in_K => exact Or.inr ⟨c, h_c_in_QuotSet, h_cb_in_K⟩
          · rintro h_b_in_Bl_or_Br
            cases h_b_in_Bl_or_Br with
            | inl h_b_in_Bl =>
                rcases h_b_in_Bl with ⟨c, h_c_in_QuotSet, h_bc_in_K⟩
                exact ⟨c, h_c_in_QuotSet, Or.inl h_bc_in_K⟩
            | inr h_b_in_Br =>
                rcases h_b_in_Br with ⟨c, h_c_in_QuotSet, h_cb_in_K⟩
                exact ⟨c, h_c_in_QuotSet, Or.inr h_cb_in_K⟩
        rw [h_B_union]
        exact Set.Countable.union h_Bl_countable h_Br_countable

      -- Define our final dense set D
      let D : Set (IndiffQuot rs) := A ∪ B

      -- Show that D is countable
      have h_D_countable : Countable D := by
        exact Set.Countable.union h_A_countable h_B_countable

      -- Show that D is dense
      have h_D_dense : order_dense D rq := by
        intro c b h_cb
        rcases h_cb with ⟨h_rcb, h_c_notin_D, h_b_notin_D⟩
        -- b, c ∉ D implies b, c ∉ A and ∉ B
        have h_b_notin_A : b ∉ A := by
          intro h_b_in_A
          exact h_b_notin_D (Set.mem_union_left B h_b_in_A)
        have h_c_notin_A : c ∉ A := by
          intro h_c_in_A
          exact h_c_notin_D (Set.mem_union_left B h_c_in_A)
        have h_b_notin_B : b ∉ B := by
          intro h_b_in_B
          exact h_b_notin_D (Set.mem_union_right A h_b_in_B)
        have h_c_notin_B : c ∉ B := by
          intro h_c_in_B
          exact h_c_notin_D (Set.mem_union_right A h_c_in_B)
        -- From b, c ∉ A we have that b, c ∈ QuotSet \ A
        have h_b_in_QuotSet_diff_A : b ∈ QuotSet \ A := by
          exact ⟨by trivial, h_b_notin_A⟩
        have h_c_in_QuotSet_diff_A : c ∈ QuotSet \ A := by
          exact ⟨by trivial, h_c_notin_A⟩
        -- From b, c ∉ B we have that (b, c) ∉ K
        have h_bc_notin_K : (b, c) ∉ K := by
          intro h_bc_in_K
          exact h_b_notin_B ⟨c, Set.mem_of_mem_diff h_bc_in_K.2.1, Or.inl h_bc_in_K⟩
        -- Therefore, there is d ∈ D such that c ≽[rq] d ≽[rq] b
        -- If there was no such d, then there would be no a ∈ A such that c ≽[rq] a ≽[rq] b
        -- and then (b, c) ∈ K contradicting previous
        by_contra h_no_d_in_D
        have h_no_a_in_A : ∀ a ∈ A, ¬ (c ≽[rq] a ∧ a ≽[rq] b) := by
          intro a h_a_in_A ⟨h_c_ge_a, h_a_ge_b⟩
          exact h_no_d_in_D ⟨a, (Set.mem_union_left B h_a_in_A), ⟨h_c_ge_a, h_a_ge_b⟩⟩
        have h_bc_in_K : (b, c) ∈ K := by
          exact ⟨h_b_in_QuotSet_diff_A, h_c_in_QuotSet_diff_A, h_rcb, by simpa using h_no_a_in_A⟩
        exact h_bc_notin_K h_bc_in_K

      -- So D is the required dense countable set, and it is order separable
      exact ⟨D, h_D_countable, h_D_dense⟩

    -- Finally, we have that is weak order and order separable,
    -- and we are done with the backward direction
    exact ⟨h_weak_order, h_order_separable⟩

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
