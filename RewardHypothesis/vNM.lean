/-
Copyright (c) 2026 Guillermo Martín-Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guillermo Martín-Sánchez
-/
import RewardHypothesis.Fishburn

/-!
# The vNM theorem

Define a mixture space and the vNM axioms.
Then, state and prove the vNM theorem: the vNM axioms are equivalent to
the existence of a utility function.
-/

namespace Utility

open OrdinalRep

variable {α : Type} {p q k : ℝ}

section MixtureSpaces

/-! ## Mixture spaces -/

/-! ### Lemmas for the mixture space (on [0, 1]) -/

/-- p ∈ [0, 1] ⇒ 1 − p ∈ [0, 1]: `p ∈ Set.Icc (0 : ℝ) 1 → 1 - p ∈ Set.Icc (0 : ℝ) 1`. -/
lemma comm_mem_Icc (hp : p ∈ Set.Icc (0 : ℝ) 1) : 1 - p ∈ Set.Icc (0 : ℝ) 1 := by
  rcases hp with ⟨hp0, hp1⟩
  constructor
  · -- 0 ≤ 1 - p
    linarith
  · -- 1 - p ≤ 1
    linarith

/-- p, q ∈ [0, 1] ⇒ p q ∈ [0, 1]:
`p ∈ Set.Icc (0 : ℝ) 1 → q ∈ Set.Icc (0 : ℝ) 1 → p * q ∈ Set.Icc (0 : ℝ) 1`. -/
lemma assoc_mem_Icc (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    p * q ∈ Set.Icc (0 : ℝ) 1 := by
  have hprod0 : 0 ≤ p * q := mul_nonneg hp.left hq.left
  have hprod1 : p * q ≤ 1 := by
    calc
      p * q ≤ p * 1 := mul_le_mul_of_nonneg_left hq.right hp.left
      _ = p := by ring
      _ ≤ 1 := hp.right
  exact ⟨hprod0, hprod1⟩

/-- p, q, k ∈ [0, 1] ⇒ k p + (1 − k) q ∈ [0, 1]:
`k * p + (1 - k) * q ∈ Set.Icc (0 : ℝ) 1`. -/
lemma assoc_of_mix_mem_Icc (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hk : k ∈ Set.Icc (0 : ℝ) 1) : k * p + (1 - k) * q ∈ Set.Icc (0 : ℝ) 1 := by
  have hlin0 : 0 ≤ k * p + (1 - k) * q := by
    apply add_nonneg
    · exact mul_nonneg hk.left hp.left
    · exact mul_nonneg (comm_mem_Icc hk).left hq.left
  have hlin1 : k * p + (1 - k) * q ≤ 1 := by
    calc
      k * p + (1 - k) * q ≤ k * 1 + (1 - k) * 1 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hp.right hk.left
        · exact mul_le_mul_of_nonneg_left hq.right (comm_mem_Icc hk).left
      _ = 1 := by ring
  exact ⟨hlin0, hlin1⟩

/-! ### Mixture spaces and the p-mixture operation -/

/-- The interval [0, 1] as a type (p ∈ [0, 1]): `IntervalType := {p : ℝ // p ∈ Set.Icc 0 1}`. -/
def IntervalType : Type :=
  {p : ℝ // p ∈ Set.Icc 0 1}

/-- Mixture space, with the p-mixture operation and its axioms
(x +[1] y = x, x +[p] y = y +[1 − p] x, (x +[q] y) +[p] y = x +[p q] y):
`mix : IntervalType → α → α → α` with `mix_one`, `mix_comm`, `mix_assoc`. -/
class MixSpace (α : Type) where
  mix : IntervalType → α → α → α
  mix_one : ∀ (p) (x y : α) (_ : p.1 = 1), mix p x y = x
  mix_comm : ∀ (p) (x y : α), mix p x y = mix ⟨1 - p.1, comm_mem_Icc p.2⟩ y x
  mix_assoc : ∀ (p q) (x y : α), mix p (mix q x y) y = mix ⟨p.1 * q.1, assoc_mem_Icc p.2 q.2⟩ x y

notation lhs " +[" p "] " rhs:50 => MixSpace.mix p lhs rhs

/-! ### Derived properties of the mixture operation -/

/-- p = 0 ⇒ x +[p] y = y: `p.1 = 0 → (x +[p] y) = y`. -/
lemma mix_zero [MixSpace α] (p : IntervalType) (x y : α) (h : p.1 = 0) :
    (x +[p] y) = y := by
  -- Use mix_comm to swap x and y
  have hcomm := MixSpace.mix_comm p x y
  rw [hcomm]
  -- Use mix_one on the swapped version
  have h1p : (⟨1 - p.1, comm_mem_Icc p.2⟩ : IntervalType).1 = 1 := by
    simp [h]
  have hone := MixSpace.mix_one ⟨1 - p.1, comm_mem_Icc p.2⟩ y x h1p
  rw [hone]

/-- Idempotence (x +[p] x = x): `(x +[p] x) = x`. -/
lemma mix_idem [MixSpace α] (p : IntervalType) (x : α) :
    (x +[p] x) = x := by
  -- By mix_zero x+[0]x = x
  have hzero : (x +[⟨0, by simp⟩] x) = x := mix_zero ⟨0, by simp⟩ x x rfl
  -- Then x +[p] x = (x +[0] x) +[p] x
  have hxx : (x +[p] x) = (x +[⟨0, by simp⟩] x) +[p] x := by
    rw [hzero]
  -- By associativity, we have (x +[0] x) +[p] x = x +[0] x
  have hassoc := MixSpace.mix_assoc p ⟨0, by simp⟩ x x
  rw [hassoc] at hxx
  have hp0 : (⟨p.1 * 0, assoc_mem_Icc p.2 (by simp)⟩ : IntervalType) = ⟨0, by simp⟩ := by
    apply Subtype.ext
    simp
  rw [hp0] at hxx
  -- Finally, by mix_zero again, we have x +[0] x = x
  rw [hzero] at hxx
  exact hxx

/-- Associativity of mixtures ((x +[p] y) +[k] (x +[q] y) = x +[k p + (1 − k) q] y):
`((x +[p] y) +[k] (x +[q] y)) = (x +[⟨k.1 * p.1 + (1 - k.1) * q.1, _⟩] y)`. -/
lemma associativity_of_mixtures [MixSpace α] :
    ∀ x y : α, ∀ p q k : IntervalType,
    ((x +[p] y) +[k] (x +[q] y)) =
    (x +[⟨k.1 * p.1 + (1 - k.1) * q.1, assoc_of_mix_mem_Icc p.2 q.2 k.2⟩] y) := by
  intro x y p q k
  by_cases hp0 : p.1 = 0
  · -- ===== Case 1: p = 0 =====
    -- Then k * p + (1-k) * q = (1-k) * q
    have hlin : k.1 * p.1 + (1 - k.1) * q.1 = (1 - k.1) * q.1 := by
      rw [hp0]
      simp
    have hlinsub : (⟨k.1 * p.1 + (1 - k.1) * q.1,
        assoc_of_mix_mem_Icc p.2 q.2 k.2⟩ : IntervalType) =
        ⟨(1 - k.1) * q.1, assoc_mem_Icc (comm_mem_Icc k.2) q.2⟩ := Subtype.ext hlin
    rw [hlinsub]
    -- Also (x +[p] y) = y
    have hmix : (x +[p] y) = y := mix_zero p x y hp0
    rw [hmix]
    -- So we have to prove (y +[k] (x +[q] y)) = (x +[(1-k)q] y)
    -- First by commutativity we have (y +[k] (x +[q] y)) = ((x +[q] y) +[1-k] y)
    have hcomm := MixSpace.mix_comm k y (x +[q] y)
    rw [hcomm]
    -- Then by associativity we have ((x +[q] y) +[1-k] y) = (x +[(1-k)q] y)
    have hassoc := MixSpace.mix_assoc ⟨1 - k.1, comm_mem_Icc k.2⟩ q x y
    rw [hassoc]
  · -- ===== Case 2: p ≠ 0 =====
    by_cases hq0 : q.1 = 0
    · -- Subcase 2.1: q = 0
      -- Then k * p + (1-k) * q = k * p
      have hlin : k.1 * p.1 + (1 - k.1) * q.1 = k.1 * p.1 := by
        rw [hq0]
        simp
      have hlinsub : (⟨k.1 * p.1 + (1 - k.1) * q.1,
          assoc_of_mix_mem_Icc p.2 q.2 k.2⟩ : IntervalType) =
          ⟨k.1 * p.1, assoc_mem_Icc k.2 p.2⟩ := Subtype.ext hlin
      rw [hlinsub]
      -- Also (x +[q] y) = y
      have hmix : (x +[q] y) = y := mix_zero q x y hq0
      rw [hmix]
      -- So we have to prove ((x +[p] y) +[k] y) = (x +[kp] y)
      -- This is just associativity
      have hassoc := MixSpace.mix_assoc k p x y
      rw [hassoc]
    · -- Subcase 2.2: q ≠ 0
      -- Then both p,q ≠ 0
      by_cases hpq : p.1 ≤ q.1
      · -- Subsubcase 2.2.1: p ≤ q
        -- Then d = p/q is in [0,1]
        let dval : ℝ := p.1 / q.1
        have hdin : dval ∈ Set.Icc 0 1 := by
          have hdnonneg : 0 ≤ p.1 / q.1 := div_nonneg p.2.left q.2.left
          have hdle1 : p.1 / q.1 ≤ 1 :=
            (div_le_one (lt_iff_le_and_ne.mpr ⟨q.2.left, ne_comm.mp hq0⟩)).mpr hpq
          exact ⟨hdnonneg, hdle1⟩
        let d : IntervalType := ⟨dval, hdin⟩
        -- By associativity we have
        -- x+[p]y = (x +[q]y) +[p/q] y
        have hassoc := MixSpace.mix_assoc d q x y
        have hpeq : p.1 = d.1 * q.1 := by
          simp [d, dval]
          field_simp
        have hpeqsub : p = ⟨d.1 * q.1, assoc_mem_Icc d.2 q.2⟩ := Subtype.ext hpeq
        have hmix : (x +[p] y) = ((x +[q] y) +[d] y) := by
          rw [hassoc, hpeqsub]
        rw [hmix]
        -- And by commutativity we have
        -- x+[p]y = y +[1 - p/q] (x +[q]y)
        have hcomm := MixSpace.mix_comm d (x +[q] y) y
        rw [hcomm]
        -- So we have now to prove
        -- (y +[1 - p/q] (x +[q]y)) +[k] (x +[q]y) = (x +[k * p + (1 - k) * q] y)
        -- By associativity we have
        -- (y +[1 - p/q] (x +[q]y)) +[k] (x +[q]y) = y +[k(1-p/q)] (x +[q]y)
        have hassoc₂ := MixSpace.mix_assoc k ⟨1 - d.1, comm_mem_Icc d.2⟩ y (x +[q] y)
        rw [hassoc₂]
        -- By commutativity we have
        -- y +[k(1-p/q)] (x +[q]y) = (x +[q]y) +[1 - k(1-p/q)] y
        have hcomm₂ := MixSpace.mix_comm ⟨k.1 * (1 - d.1),
          assoc_mem_Icc k.2 (comm_mem_Icc d.2)⟩ y (x +[q] y)
        rw [hcomm₂]
        -- By associativity we have
        -- (x +[q]y) +[1 - k(1-p/q)] y = x +[(1 - k(1-p/q)) * q] y
        have hassoc₃ := MixSpace.mix_assoc ⟨1 - k.1 * (1 - d.1),
          comm_mem_Icc (assoc_mem_Icc k.2 (comm_mem_Icc d.2))⟩ q x y
        rw [hassoc₃]
        -- Now we just need to show that
        -- (1 - k(1-p/q)) * q = k * p + (1 - k) * q
        have hfinal : (1 - k.1 * (1 - d.1)) * q.1 = k.1 * p.1 + (1 - k.1) * q.1 := by
          rw [hpeq]
          ring
        have hfinalsub : (⟨(1 - k.1 * (1 - d.1)) * q.1,
            assoc_mem_Icc (comm_mem_Icc (assoc_mem_Icc k.2 (comm_mem_Icc d.2))) q.2⟩ :
            IntervalType) =
            ⟨k.1 * p.1 + (1 - k.1) * q.1, assoc_of_mix_mem_Icc p.2 q.2 k.2⟩ := Subtype.ext hfinal
        rw [hfinalsub]
      · -- Subsubcase 2.2.2: p > q
        -- Similarly as before
        -- Then d = q/p is in [0,1]
        let dval : ℝ := q.1 / p.1
        have hdin : dval ∈ Set.Icc 0 1 := by
          have hdnonneg : 0 ≤ q.1 / p.1 := div_nonneg q.2.left p.2.left
          have hdle1 : q.1 / p.1 ≤ 1 :=
            (div_le_one (lt_iff_le_and_ne.mpr ⟨p.2.left, ne_comm.mp hp0⟩)).mpr
              (le_of_lt (lt_of_not_ge hpq))
          exact ⟨hdnonneg, hdle1⟩
        let d : IntervalType := ⟨dval, hdin⟩
        -- By associativity we have
        -- x+[q]y = (x +[p]y) +[q/p] y
        have hassoc := MixSpace.mix_assoc d p x y
        have hqeq : q.1 = d.1 * p.1 := by
          simp [d, dval]
          field_simp
        have hqeqsub : q = ⟨d.1 * p.1, assoc_mem_Icc d.2 p.2⟩ := Subtype.ext hqeq
        have hmix : (x +[q] y) = ((x +[p] y) +[d] y) := by
          rw [hassoc, hqeqsub]
        rw [hmix]
        -- And by commutativity we have
        -- x+[q]y = y +[1 - q/p] (x +[p]y)
        have hcomm := MixSpace.mix_comm d (x +[p] y) y
        rw [hcomm]
        -- So we have now to prove
        -- (x +[p]y) +[k] (y +[1 - q/p] (x +[p]y)) = (x +[k * p + (1 - k) * q] y)
        -- By commutativity we have
        -- (x +[p]y) +[k] (y +[1 - q/p] (x +[p]y)) = (y +[1 - q/p] (x +[p]y)) +[1-k] (x +[p]y)
        have hcomm₂ :=
          MixSpace.mix_comm k (x +[p] y) (y +[⟨1 - d.1, comm_mem_Icc d.2⟩] (x +[p] y))
        rw [hcomm₂]
        -- By associativity we have
        -- (y +[1 - q/p] (x +[p]y)) +[1-k] (x +[p]y) = y +[(1-k)(1-q/p)] (x +[p]y)
        have hassoc₂ := MixSpace.mix_assoc ⟨1 - k.1, comm_mem_Icc k.2⟩
          ⟨1 - d.1, comm_mem_Icc d.2⟩ y (x +[p] y)
        rw [hassoc₂]
        -- By commutativity we have
        -- y +[(1-k)(1-q/p)] (x +[p]y) = (x +[p]y) +[1 - (1-k)(1-q/p)] y
        have hcomm₃ := MixSpace.mix_comm ⟨(1 - k.1) * (1 - d.1),
          assoc_mem_Icc (comm_mem_Icc k.2) (comm_mem_Icc d.2)⟩ y (x +[p] y)
        rw [hcomm₃]
        -- By associativity we have
        -- (x +[p]y) +[1 - (1-k)(1-q/p)] y = x +[(1 - (1-k)(1-q/p)) * p] y
        have hassoc₃ := MixSpace.mix_assoc ⟨1 - (1 - k.1) * (1 - d.1),
          comm_mem_Icc (assoc_mem_Icc (comm_mem_Icc k.2) (comm_mem_Icc d.2))⟩ p x y
        rw [hassoc₃]
        -- Now we just need to show that
        -- (1 - (1-k)(1-q/p)) * p = k * p + (1 - k) * q
        have hfinal : (1 - (1 - k.1) * (1 - d.1)) * p.1 = k.1 * p.1 + (1 - k.1) * q.1 := by
          rw [hqeq]
          ring
        have hfinalsub : (⟨(1 - (1 - k.1) * (1 - d.1)) * p.1,
            assoc_mem_Icc
              (comm_mem_Icc (assoc_mem_Icc (comm_mem_Icc k.2) (comm_mem_Icc d.2))) p.2⟩ :
            IntervalType) =
            ⟨k.1 * p.1 + (1 - k.1) * q.1, assoc_of_mix_mem_Icc p.2 q.2 k.2⟩ := Subtype.ext hfinal
        rw [hfinalsub]

end MixtureSpaces

section ExpectedUtility

/-! ## Expected utility and the vNM axioms -/

/-! ### Expected utility functions -/

/-- u p-linear (u(x +[p] y) = p u(x) + (1 − p) u(y)):
`∀ x y p, u (x +[p] y) = p.1 * u x + (1 - p.1) * u y`. -/
def PLinear [MixSpace α] (u : α → ℝ) : Prop :=
  ∀ x y : α, ∀ p : IntervalType, u (x +[p] y) = p.1 * u x + (1 - p.1) * u y

/-- What it means for a function to be an expected utility function
(u ordinal consistent ∧ p-linear): `OrdinalConsistent u r ∧ PLinear u`. -/
def UtilityFunction [MixSpace α] (u : α → ℝ) (r : Relation α) : Prop :=
  OrdinalConsistent u r ∧ PLinear u

/-! ### The vNM axioms

Define the vNM axioms for expected utility on a preference relation.
-/

/-- Independence (p ∈ (0, 1] ⇒ (x ≽ y ⇔ x +[p] z ≽ y +[p] z)):
`∀ x y z p, p.1 ∈ Set.Ioc 0 1 → ((x ≽[r] y) ↔ (x +[p] z) ≽[r] (y +[p] z))`. -/
def Independence [MixSpace α] (r : Relation α) : Prop :=
  ∀ (x y z : α) (p : IntervalType), p.1 ∈ Set.Ioc 0 1 →
    ((x ≽[r] y) ↔ (x +[p] z) ≽[r] (y +[p] z))

/-- Continuity (x ≽ y ≽ z ⇒ ∃ p, x +[p] z ∼ y):
`∀ x y z, (x ≽[r] y ∧ y ≽[r] z) → ∃ p, (x +[p] z) ∼[r] y`. -/
def Continuity [MixSpace α] (r : Relation α) : Prop :=
  ∀ x y z : α, (x ≽[r] y ∧ y ≽[r] z) → ∃ p : IntervalType, (x +[p] z) ∼[r] y

/-- vNM axioms (≽ complete ∧ transitive ∧ independent ∧ continuous):
`Completeness r ∧ Transitivity r ∧ Independence r ∧ Continuity r`. -/
def VNMAxioms [MixSpace α] (r : Relation α) : Prop :=
  Completeness r ∧ Transitivity r ∧ Independence r ∧ Continuity r

end ExpectedUtility

section VNM

/-! ## The vNM theorem -/

/-! ### Lemmas for the proof of the vNM theorem -/

/-! #### Consequences of independence -/

/-- ≽ complete ∧ independent ⇒ (x ≽ y ⇒ x +[p] z ≽ y +[p] z for every p ∈ [0, 1]):
`Completeness r ∧ Independence r → x ≽[r] y → (x +[p] z) ≽[r] (y +[p] z)`. -/
lemma full_indep_of_indep_of_comp [MixSpace α] (r : Relation α) :
    Completeness r ∧ Independence r → ∀ x y : α, (x ≽[r] y) →
    ∀ z : α, ∀ p : IntervalType, (x +[p] z) ≽[r] (y +[p] z) := by
  intro h x y hxy z p
  rcases h with ⟨hcompl, hindep⟩
  by_cases hppos : p.1 > 0
  · -- ===== Case 1: p > 0 therefore p ∈ (0,1] =====
    have hpIoc : p.1 ∈ Set.Ioc 0 1 := ⟨hppos, p.2.right⟩
    -- Then this is just independence
    exact (hindep x y z p hpIoc).mp hxy
  · -- ===== Case 2: ¬(p > 0) therefore p = 0 =====
    have hp0 : p.1 = 0 := le_antisymm (not_lt.mp hppos) p.2.left
    -- Then (x +[p] z) = z and (y +[p] z) = z, so we have z ≽ z
    have hmixx : (x +[p] z) = z := mix_zero p x z hp0
    have hmixy : (y +[p] z) = z := mix_zero p y z hp0
    rw [hmixx, hmixy]
    -- This is where we need the completeness to get z ≽ z
    have hzz : z ≽[r] z := (hcompl z z).elim id id
    exact hzz

/-- ≽ complete ∧ independent ⇒ (x ∼ y ⇒ x +[p] z ∼ y +[p] z):
`Completeness r ∧ Independence r → x ∼[r] y → (x +[p] z) ∼[r] (y +[p] z)`. -/
lemma full_indiff_indep [MixSpace α] (r : Relation α) :
    Completeness r ∧ Independence r →
    ∀ x y : α, (x ∼[r] y) → ∀ z : α, ∀ p : IntervalType, (x +[p] z) ∼[r] (y +[p] z) := by
  intro h x y
  have hfull := full_indep_of_indep_of_comp r h
  intro hxiy z p
  have hxy : x ≽[r] y := hxiy.left
  have hyx : y ≽[r] x := hxiy.right
  have h1 := hfull x y hxy z p
  have h2 := hfull y x hyx z p
  exact ⟨h1, h2⟩

/-- ≽ complete ∧ independent ⇒ (x ∼ y ⇒ x ∼ x +[p] y ∼ y):
`Completeness r ∧ Independence r → x ∼[r] y → (x ∼[r] (x +[p] y)) ∧ ((x +[p] y) ∼[r] y)`. -/
lemma full_indiff_interior [MixSpace α] (r : Relation α) :
    Completeness r ∧ Independence r →
    ∀ x y : α, (x ∼[r] y) → ∀ p : IntervalType, (x ∼[r] (x +[p] y)) ∧ ((x +[p] y) ∼[r] y) := by
  intro h x y hxiy p
  -- Apply independence x ~ y with y and p
  -- We get (x +[p] y) ∼ (y +[p] y)
  have h1 := full_indiff_indep r h x y hxiy y p
  -- But (y +[p] y) = y by mix_idem
  have hidem := mix_idem p y
  rw [hidem] at h1
  -- So we have (x +[p] y) ∼ y
  -- Similarly for the other direction
  have h2 := full_indiff_indep r h x y hxiy x ⟨1 - p.1, comm_mem_Icc p.2⟩
  have hidem' := mix_idem ⟨1 - p.1, comm_mem_Icc p.2⟩ x
  rw [hidem'] at h2
  have hcomm := MixSpace.mix_comm p x y
  rw [← hcomm] at h2
  exact ⟨h2, h1⟩

/-- ≽ complete ∧ independent ⇒ (x ≽ y ⇒ x ≽ x +[p] y ≽ y):
`Completeness r ∧ Independence r → x ≽[r] y → (x ≽[r] (x +[p] y)) ∧ ((x +[p] y) ≽[r] y)`. -/
lemma full_partial_interior [MixSpace α] (r : Relation α) :
    Completeness r ∧ Independence r → ∀ x y : α, (x ≽[r] y) →
    ∀ p : IntervalType, (x ≽[r] (x +[p] y)) ∧ ((x +[p] y) ≽[r] y) := by
  intro h x y hxy p
  have hfull := full_indep_of_indep_of_comp r h
  -- Mix x ≽ y with y and p to get (x +[p] y) ≽ (y +[p] y)
  have h1 := hfull x y hxy y p
  -- But (y +[p] y) = y by mix_idem
  have hidem := mix_idem p y
  rw [hidem] at h1
  -- Similarly for the other direction,
  -- x ≽ y with x and 1-p to get (x +[1-p] x) ≽ (y +[1-p] x)
  have h2 := hfull x y hxy x ⟨1 - p.1, comm_mem_Icc p.2⟩
  -- But (x +[1-p] x) = x by mix_idem
  have hidem₂ := mix_idem ⟨1 - p.1, comm_mem_Icc p.2⟩ x
  rw [hidem₂] at h2
  -- By commutativity we have (y +[1-p] x) = (x +[p] y)
  have hcomm := MixSpace.mix_comm p x y
  rw [← hcomm] at h2
  exact ⟨h2, h1⟩

/-- independent ⇒ (x ≽ y ∧ p ∈ (0, 1) ⇒ x ≽ x +[p] y ≽ y):
`Independence r → x ≽[r] y → p.1 ∈ Set.Ioo 0 1 → (x ≽[r] (x +[p] y)) ∧ ((x +[p] y) ≽[r] y)`. -/
lemma partial_interior [MixSpace α] (r : Relation α) :
    Independence r → ∀ x y : α, (x ≽[r] y) →
    ∀ p : IntervalType, p.1 ∈ Set.Ioo 0 1 → (x ≽[r] (x +[p] y)) ∧ ((x +[p] y) ≽[r] y) := by
  intro hindep x y hxy p hpin
  have hpIoc : p.1 ∈ Set.Ioc 0 1 := ⟨hpin.left, le_of_lt hpin.right⟩
  -- Mix x ≽ y with y and p to get (x +[p] y) ≽ (y +[p] y)
  have h1 := (hindep x y y p hpIoc).mp hxy
  -- But (y +[p] y) = y by mix_idem
  have hidem := mix_idem p y
  rw [hidem] at h1
  -- Similarly for the other direction,
  -- x ≽ y with x and 1-p to get (x +[1-p] x) ≽ (y +[1-p] x)
  have h1pIoc : (1 - p.1) ∈ Set.Ioc 0 1 := by
    have h1ppos : 0 < 1 - p.1 := by
      have hplt1 := hpin.right
      linarith
    have h1ple1 : 1 - p.1 ≤ 1 := by
      have hppos := hpin.left
      linarith
    exact ⟨h1ppos, h1ple1⟩
  have h2 := (hindep x y x ⟨1 - p.1, comm_mem_Icc p.2⟩ h1pIoc).mp hxy
  -- But (x +[1-p] x) = x by mix_idem
  have hidem₂ := mix_idem ⟨1 - p.1, comm_mem_Icc p.2⟩ x
  rw [hidem₂] at h2
  -- By commutativity we have (y +[1-p] x) = (x +[p] y)
  have hcomm := MixSpace.mix_comm p x y
  rw [← hcomm] at h2
  exact ⟨h2, h1⟩

/-- independent ⇒ (x ≻ y ∧ p ∈ (0, 1) ⇒ x ≻ x +[p] y ≻ y):
`Independence r → x ≻[r] y → p.1 ∈ Set.Ioo 0 1 → x ≻[r] (x +[p] y) ∧ (x +[p] y) ≻[r] y`. -/
lemma strict_interior [MixSpace α] (r : Relation α) :
    Independence r → ∀ x y : α, (x ≻[r] y) →
    ∀ p : IntervalType, p.1 ∈ Set.Ioo 0 1 → x ≻[r] (x +[p] y) ∧ (x +[p] y) ≻[r] y := by
  intro hindep x y hxsy p hpin
  have hpartial : (x ≽[r] (x +[p] y)) ∧ ((x +[p] y) ≽[r] y) :=
    partial_interior r hindep x y hxsy.left p hpin
  have hnpartialx : ¬((x +[p] y) ≽[r] x) := by
    intro hcontra
    -- By commmutativity we have (x +[p] y) = (y +[1-p] x) ≽ x
    have hcomm := MixSpace.mix_comm p x y
    rw [hcomm] at hcontra
    -- By idem we have (y +[1-p] x) ≽ (x +[1-p] x) = x
    let oneMinusP : IntervalType := ⟨1 - p.1, comm_mem_Icc p.2⟩
    have haux : (y +[oneMinusP] x) ≽[r] (x +[oneMinusP] x) := by
      have hxx : (x +[oneMinusP] x) = x := mix_idem oneMinusP x
      nth_rewrite 2 [← hxx] at hcontra
      exact hcontra
    -- Therefore by independence we have y ≽ x, contradiction
    have h1pIoc : oneMinusP.1 ∈ Set.Ioc 0 1 := by
      have h1ppos : 0 < oneMinusP.1 := by
        have hplt1 := hpin.right
        linarith
      have h1ple1 : oneMinusP.1 ≤ 1 := by
        have hppos := hpin.left
        linarith
      exact ⟨h1ppos, h1ple1⟩
    have hyx : y ≽[r] x := (hindep y x x oneMinusP h1pIoc).mpr haux
    exact absurd hyx hxsy.right
  have hnpartialy : ¬(y ≽[r] (x +[p] y)) := by
    intro hcontra
    -- By idem we have (y +[p] y) ≽ (x +[p] y)
    have haux : (y +[p] y) ≽[r] (x +[p] y) := by
      have hyy : (y +[p] y) = y := mix_idem p y
      nth_rewrite 1 [← hyy] at hcontra
      exact hcontra
    -- Therefore by independence we have y ≽ x, contradiction
    have hyx : y ≽[r] x := (hindep y x y p ⟨hpin.left, le_of_lt hpin.right⟩).mpr haux
    exact absurd hyx hxsy.right
  exact ⟨⟨hpartial.left, hnpartialx⟩, ⟨hpartial.right, hnpartialy⟩⟩

/-- ≽ complete ∧ independent ⇒ (x ≻ y ⇒ (x +[p] y ≻ x +[q] y ⇔ p > q)):
`Completeness r ∧ Independence r → x ≻[r] y → (((x +[p] y) ≻[r] (x +[q] y)) ↔ p.1 > q.1)`. -/
lemma strict_p_consistency [MixSpace α] (r : Relation α) :
    Completeness r ∧ Independence r →
    ∀ x y : α, (x ≻[r] y) →
    (∀ p q : IntervalType, ((x +[p] y) ≻[r] (x +[q] y)) ↔ p.1 > q.1) := by
  intro h x y hxsy p q
  rcases h with ⟨hcompl, hindep⟩
  have hsi := strict_interior r hindep
  constructor
  · -- ===== Forward direction: (x +[p] y) ≻ (x +[q] y) → p > q =====
    -- Assume (x +[p] y) ≻ (x +[q] y) and show p.1 > q.1
    intro hpsq
    -- Then let's assume that p ≤ q and reach a contradiction
    by_contra hnpgtq
    have hpleq : p.1 ≤ q.1 := not_lt.mp hnpgtq
    by_cases hpeq : p.1 = q.1
    · -- Case 1: p = q
      -- Then (x +[p] y) = (x +[q] y), and we get (x +[p] y) ≻ (x +[p] y), contradiction
      have hmix : (x +[p] y) = (x +[q] y) := by
        have hpeqq : p = q := Subtype.ext hpeq
        rw [hpeqq]
      rw [← hmix] at hpsq
      exact absurd ((hcompl (x +[p] y) (x +[p] y)).elim id id) hpsq.right
    · -- Case 2: p ≠ q
      -- Then p < q
      have hpltq : p.1 < q.1 := lt_iff_le_and_ne.mpr ⟨hpleq, hpeq⟩
      by_cases hq0 : q.1 = 0
      · -- Subcase 2.1: q = 0, (p,q) = (>0,0)
        -- Impossible cause p ≥ 0 and p < q = 0
        have hpnonneg : p.1 ≥ 0 := p.2.left
        linarith
      · -- Subcase 2.2: q ≠ 0
        -- Then q > 0, (p,q) = (>0, >0)
        have hqpos : q.1 > 0 := lt_iff_le_and_ne.mpr ⟨q.2.left, ne_comm.mp hq0⟩
        by_cases hq1 : q.1 = 1
        · -- Subsubcase 2.1.1: q = 1, (p,q) = (<1,1)
          -- Then (x +[q] y) = x
          have hmix' : (x +[q] y) = x := MixSpace.mix_one q x y hq1
          rw [hmix'] at hpsq
          -- Since (x +[p] y) ≻ x, by strict_interior we have p ∉ (0,1)
          have hnpin : ¬(p.1 ∈ Set.Ioo 0 1) := by
            -- Since x ≻ y, if p ∈ (0,1) then x ≻ (x +[p] y), contradiction
            intro hpin
            have hstrict := hsi x y hxsy p hpin
            have hxp : x ≽[r] (x +[p] y) := hstrict.left.left
            exact absurd hxp hpsq.right
          -- Then since p ∉ (0,1) and p < 1, we have p = 0, (p,q) = (0,1)
          have hplt1 : p.1 < 1 := by
            simpa [hq1] using hpltq
          have hp0 : p.1 = 0 := by
            have hor : p.1 ≤ 0 ∨ p.1 ≥ 1 := by
              by_contra hcontra
              push_neg at hcontra
              exact hnpin hcontra
            cases hor with
            | inl hle0 =>
              exact le_antisymm hle0 p.2.left
            | inr hge1 =>
              exact absurd hplt1 (not_lt_of_ge hge1)
          -- Then (x +[p] y) = y, and we get y ≻ x, contradiction
          have hmix : (x +[p] y) = y := mix_zero p x y hp0
          rw [hmix] at hpsq
          exact absurd hpsq.left hxsy.right
        · -- Subsubcase 2.2.2: q ≠ 1, (p,q) = (<1, (0,1))
          -- Since q ∉ {0,1} then q ∈ (0,1) and by strict_interior we have
          -- (x +[q] y) ≻ y
          have hqin : q.1 ∈ Set.Ioo 0 1 := ⟨hqpos, lt_iff_le_and_ne.mpr ⟨q.2.right, hq1⟩⟩
          have hsip := hsi x y hxsy q hqin
          have hqsy : (x +[q] y) ≻[r] y := hsip.right
          by_cases hp0 : p.1 = 0
          · -- Subsubsubcase 2.2.2.1: p = 0
            -- Then (x +[p] y) = y, and y ≻ (x +[q] y)
            have hmix : (x +[p] y) = y := mix_zero p x y hp0
            rw [hmix] at hpsq
            -- Since q ∈ (0,1), by strict_interior we have (x +[q] y) ≻ y
            exact absurd hqsy.left hpsq.right
          · -- Subsubsubcase 2.2.2.2: p ≠ 0
            -- Then p > 0, and p ∈ (0,1), (p,q) = ((0,1), (0,1))
            have hppos : p.1 > 0 := lt_iff_le_and_ne.mpr ⟨p.2.left, ne_comm.mp hp0⟩
            have hpin : p.1 ∈ Set.Ioo 0 1 := ⟨hppos, lt_trans hpltq hqin.right⟩
            -- Then k = p/q ∈ (0,1)
            let kval : ℝ := p.1 / q.1
            have hkin : kval ∈ Set.Ioo 0 1 := by
              have hkpos : 0 < p.1 / q.1 := div_pos hppos hqpos
              have hklt1 : p.1 / q.1 < 1 := (div_lt_one hqin.left).mpr hpltq
              exact ⟨hkpos, hklt1⟩
            let k : IntervalType := ⟨kval, ⟨le_of_lt hkin.left, le_of_lt hkin.right⟩⟩
            -- By strict interior, we have (x +[q] y) ≻ (x +[q] y) +[k] y
            have hsik := hsi (x +[q] y) y hqsy k hkin
            have hqsk := hsik.left
            -- By associativity, we have (x +[q] y) +[k] y = x +[p] y
            -- since k = p / q
            have hassoc := MixSpace.mix_assoc k q x y
            have hpeqk : p.1 = k.1 * q.1 := by
              simp [k, kval]
              field_simp
            have hpeqsub : p = ⟨k.1 * q.1, assoc_mem_Icc k.2 q.2⟩ := Subtype.ext hpeqk
            have hmixeq : ((x +[q] y) +[k] y) = x +[p] y := by
              rw [hassoc, hpeqsub]
            -- Then we have (x +[q] y) ≻ (x +[p] y), contradiction
            rw [hmixeq] at hqsk
            exact absurd hqsk.left hpsq.right
  · -- ===== Backward direction: p > q → (x +[p] y) ≻ (x +[q] y) =====
    -- Assume p.1 > q.1 and show (x +[p] y) ≻ (x +[q] y)
    intro hpgtq
    have hppos : p.1 > 0 := lt_of_le_of_lt q.2.left hpgtq
    -- By cases on q = 0
    by_cases hq0 : q.1 = 0
    · -- Case 1: q = 0
      -- Then (x +[q] y) = y
      have hmix : (x +[q] y) = y := mix_zero q x y hq0
      rw [hmix]
      by_cases hp1 : p.1 = 1
      · -- Subcase 1.1: p = 1, (p,q) = (1,0)
        -- Then (x +[p] y) = x, and we have x ≻ y
        have hmix' : (x +[p] y) = x := MixSpace.mix_one p x y hp1
        rw [hmix']
        exact hxsy
      · -- Subcase 1.2: p ≠ 1, (p,q) = ((0,1),0)
        -- Then p ∈ (0,1), and by strict_interior we have (x +[p] y) ≻ y
        have hpin : p.1 ∈ Set.Ioo 0 1 := ⟨hppos, lt_iff_le_and_ne.mpr ⟨p.2.right, hp1⟩⟩
        have hstrict := hsi x y hxsy p hpin
        exact hstrict.right
    · -- Case 2: q ≠ 0
      -- Then q > 0, (p,q) = (>0, >0)
      have hqpos : q.1 > 0 := lt_iff_le_and_ne.mpr ⟨q.2.left, ne_comm.mp hq0⟩
      by_cases hp1 : p.1 = 1
      · -- Subcase 2.1: p = 1, (p,q) = (1, (0,1))
        -- Then (x +[p] y) = x
        have hmix' : (x +[p] y) = x := MixSpace.mix_one p x y hp1
        rw [hmix']
        -- Since p > q and p = 1, we have q ∈ (0,1),
        -- and by strict_interior we have x ≻ (x +[q] y)
        have hqin : q.1 ∈ Set.Ioo 0 1 := by
          have hqne1 : q.1 ≠ 1 := by
            intro hqe1
            rw [hqe1] at hpgtq
            linarith
          exact ⟨hqpos, lt_iff_le_and_ne.mpr ⟨q.2.right, hqne1⟩⟩
        have hstrict := hsi x y hxsy q hqin
        exact hstrict.left
      · -- Subcase 2.2: p ≠ 1, (p,q) = ((0,1), (0,1))
        -- Then p ∈ (0,1), and by strict_interior we have
        -- (x +[p] y) ≻ y
        have hpin : p.1 ∈ Set.Ioo 0 1 := ⟨hppos, lt_iff_le_and_ne.mpr ⟨p.2.right, hp1⟩⟩
        have hsip := hsi x y hxsy p hpin
        have hpsy : (x +[p] y) ≻[r] y := hsip.right
        -- Then k = q/p ∈ (0,1)
        let kval : ℝ := q.1 / p.1
        have hkin : kval ∈ Set.Ioo 0 1 := by
          have hkpos : 0 < q.1 / p.1 := div_pos hqpos hppos
          have hklt1 : q.1 / p.1 < 1 := (div_lt_one hppos).mpr hpgtq
          exact ⟨hkpos, hklt1⟩
        let k : IntervalType := ⟨kval, ⟨le_of_lt hkin.left, le_of_lt hkin.right⟩⟩
        -- By strict interior, we have (x +[p] y) ≻ (x +[p] y) +[k] y
        have hsik := hsi (x +[p] y) y hpsy k hkin
        have hpsk := hsik.left
        -- By associativity, we have (x +[p] y) +[k] y = x +[q] y
        -- since k = q / p
        have hassoc := MixSpace.mix_assoc k p x y
        have hqeqk : q.1 = k.1 * p.1 := by
          simp [k, kval]
          field_simp
        have hqeqsub : q = ⟨k.1 * p.1, assoc_mem_Icc k.2 p.2⟩ := Subtype.ext hqeqk
        have hmixeq : ((x +[p] y) +[k] y) = x +[q] y := by
          rw [hassoc, hqeqsub]
        -- Then we have (x +[p] y) ≻ (x +[q] y)
        rw [hmixeq] at hpsk
        exact hpsk

/-! #### Consequences of continuity -/

/-- vNM ⇒ (x ≻ y ≻ z ⇒ ∃! p, x +[p] z ∼ y):
`VNMAxioms r → (x ≻[r] y ∧ y ≻[r] z) → ∃! p : IntervalType, ((x +[p] z) ∼[r] y)`. -/
lemma unique_continuity_strict [MixSpace α] (r : Relation α) :
    VNMAxioms r →
    ∀ x y z : α, (x ≻[r] y ∧ y ≻[r] z) → ∃! p : IntervalType, ((x +[p] z) ∼[r] y) := by
  intro hvNM x y z hxyz
  rcases hvNM with ⟨hcompl, htrans, hindep, hcont⟩
  rcases hxyz with ⟨hxsy, hysz⟩
  have hxsz : x ≻[r] z := by
    have hxy : x ≽[r] y := hxsy.left
    have hyz : y ≽[r] z := hysz.left
    have hxz : x ≽[r] z := htrans x y z ⟨hxy, hyz⟩
    have hnzx : ¬(z ≽[r] x) := by
      intro hzx
      have hyx : y ≽[r] x := htrans y z x ⟨hyz, hzx⟩
      exact hxsy.right hyx
    exact ⟨hxz, hnzx⟩
  -- ===== Existence =====
  -- First, show existence, this is just from continuity
  have hexists := hcont x y z ⟨hxsy.left, hysz.left⟩
  rcases hexists with ⟨p, hpiy⟩
  -- ===== Uniqueness =====
  -- Now show uniqueness
  have huniq : ∀ q : IntervalType, ((x +[q] z) ∼[r] y) → q = p := by
    intro q hqiy
    -- Since both (x +[p] z) ∼ y and (x +[q] z) ∼ y, we have
    -- (x +[p] z) ∼ (x +[q] z)
    have hpiq := indiff_transitivity r htrans (x +[p] z) y (x +[q] z)
      ⟨hpiy, ⟨hqiy.right, hqiy.left⟩⟩
    -- Assume p ≠ q and reach a contradiction
    by_contra hpneq
    by_cases hpltq : p.1 < q.1
    · -- Case 1: p < q
      -- Then by strict p-consistency we have (x +[p] z) ≻ (x +[q] z), contradiction
      have hspc := strict_p_consistency r ⟨hcompl, hindep⟩ x z hxsz
      have hqsp := (hspc q p).mpr hpltq
      exact absurd hpiq.left hqsp.right
    · -- Case 2: p ≥ q
      have hqltp : q.1 < p.1 := by
        have hqnep : q.1 ≠ p.1 := by
          intro hqep
          exact hpneq (Subtype.ext hqep)
        exact lt_iff_le_and_ne.mpr ⟨le_of_not_gt hpltq, hqnep⟩
      -- Then by strict p-consistency we have (x +[q] z) ≻ (x +[p] z), contradiction
      have hspc := strict_p_consistency r ⟨hcompl, hindep⟩ x z hxsz
      have hpsq := (hspc p q).mpr hqltp
      exact absurd hpiq.right hpsq.right
  exact ⟨p, hpiy, huniq⟩

/-- vNM ⇒ (x ≻ z ∧ x ≽ y ≽ z ⇒ ∃! p, x +[p] z ∼ y):
`VNMAxioms r → (x ≻[r] z ∧ x ≽[r] y ∧ y ≽[r] z) → ∃! p : IntervalType, ((x +[p] z) ∼[r] y)`. -/
lemma unique_continuity [MixSpace α] (r : Relation α) :
    VNMAxioms r →
    ∀ x y z : α, (x ≻[r] z ∧ x ≽[r] y ∧ y ≽[r] z) →
    ∃! p : IntervalType, ((x +[p] z) ∼[r] y) := by
  intro hvNM x y z hxyz
  rcases hvNM with ⟨hcompl, htrans, hindep, hcont⟩
  have hsi := strict_interior r hindep
  rcases hxyz with ⟨hxsz, hxy, hyz⟩
  by_cases hxiy : x ∼[r] y
  · -- ===== Case 1: x ∼ y =====
    -- Then ∃ p = 1 such that (x +[p] z) ∼ y
    have hexists : ∃ p : IntervalType, ((x +[p] z) ∼[r] y) ∧ p.1 = 1 := by
      let p : IntervalType := ⟨1, by simp⟩
      refine ⟨p, ?_⟩
      have hmix : (x +[p] z) = x := MixSpace.mix_one p x z rfl
      rw [hmix]
      exact ⟨hxiy, rfl⟩
    -- Uniqueness: if (x +[q] z) ∼ y, then q = 1
    have huniq : ∀ q : IntervalType, ((x +[q] z) ∼[r] y) → q.1 = 1 := by
      intro q hqiy
      -- First we get (x +[q] z) ∼ x
      have hqix := indiff_transitivity r htrans (x +[q] z) y x
        ⟨hqiy, ⟨hxiy.right, hxiy.left⟩⟩
      by_contra hqne1
      have hqlt1 : q.1 < 1 := lt_iff_le_and_ne.mpr ⟨q.2.right, hqne1⟩
      by_cases hq0 : q.1 = 0
      · -- Subcase 1.1: q = 0
        -- Then (x +[q] z) = z, and we have z ∼ x, contradiction
        have hmix : (x +[q] z) = z := mix_zero q x z hq0
        rw [hmix] at hqix
        exact absurd hqix.left hxsz.right
      · -- Subcase 1.2: q ≠ 0
        -- Then q ∈ (0,1), and by strict_interior we have x ≻ (x +[q] z), contradiction
        have hqpos : q.1 > 0 := lt_iff_le_and_ne.mpr ⟨q.2.left, ne_comm.mp hq0⟩
        have hqin : q.1 ∈ Set.Ioo 0 1 := ⟨hqpos, hqlt1⟩
        have hstrict := hsi x z hxsz q hqin
        exact absurd hqix.left hstrict.left.right
    rcases hexists with ⟨p, hp⟩
    rcases hp with ⟨hpiy, hp1⟩
    have hpuniq : ∀ q : IntervalType, ((x +[q] z) ∼[r] y) → q = p := by
      intro q hqiy
      have hq1 : q.1 = 1 := huniq q hqiy
      have hqep : q.1 = p.1 := by
        rw [hq1]
        exact hp1.symm
      exact Subtype.ext hqep
    exact ⟨p, hpiy, hpuniq⟩
  · -- ===== Case 2: x ≁ y =====
    have hxsy : x ≻[r] y := ⟨hxy, (not_and_or.mp hxiy).resolve_left (not_not.mpr hxy)⟩
    by_cases hyiz : y ∼[r] z
    · -- Subcase 2.1: y ∼ z
      -- Then ∃ p = 0 such that (x +[p] z) ∼ y
      have hexists : ∃ p : IntervalType, ((x +[p] z) ∼[r] y) ∧ p.1 = 0 := by
        let p : IntervalType := ⟨0, by simp⟩
        refine ⟨p, ?_⟩
        have hmix : (x +[p] z) = z := mix_zero p x z rfl
        rw [hmix]
        exact ⟨⟨hyiz.right, hyiz.left⟩, rfl⟩
      -- Uniqueness: if (x +[q] z) ∼ y, then q = 0
      have huniq : ∀ q : IntervalType, ((x +[q] z) ∼[r] y) → q.1 = 0 := by
        intro q hqiy
        -- First we get (x +[q] z) ∼ z
        have hqiz := indiff_transitivity r htrans (x +[q] z) y z
          ⟨hqiy, hyiz⟩
        by_contra hqne0
        have hqpos : q.1 > 0 := lt_iff_le_and_ne.mpr ⟨q.2.left, ne_comm.mp hqne0⟩
        by_cases hq1 : q.1 = 1
        · -- Subsubcase 2.1.1: q = 1
          -- Then (x +[q] z) = x, and we have x ∼ z, contradiction
          have hmix : (x +[q] z) = x := MixSpace.mix_one q x z hq1
          rw [hmix] at hqiz
          exact absurd hqiz.right hxsz.right
        · -- Subsubcase 2.1.2: q ≠ 1
          -- Then q ∈ (0,1), and by strict_interior we have (x +[q] z) ≻ z, contradiction
          have hqlt1 : q.1 < 1 := lt_iff_le_and_ne.mpr ⟨q.2.right, hq1⟩
          have hqin : q.1 ∈ Set.Ioo 0 1 := ⟨hqpos, hqlt1⟩
          have hstrict := hsi x z hxsz q hqin
          exact absurd hqiz.right hstrict.right.right
      rcases hexists with ⟨p, hp⟩
      rcases hp with ⟨hpiy, hp0⟩
      have hpuniq : ∀ q : IntervalType, ((x +[q] z) ∼[r] y) → q = p := by
        intro q hqiy
        have hq0 : q.1 = 0 := huniq q hqiy
        have hqep : q.1 = p.1 := by
          rw [hq0]
          exact hp0.symm
        exact Subtype.ext hqep
      exact ⟨p, hpiy, hpuniq⟩
    · -- Subcase 2.2: y ≁ z
      have hysz : y ≻[r] z := ⟨hyz, (not_and_or.mp hyiz).resolve_left (not_not.mpr hyz)⟩
      -- Now we can use the strict version of unique continuity
      exact unique_continuity_strict r ⟨hcompl, htrans, hindep, hcont⟩
        x y z ⟨hxsy, hysz⟩

/-! #### Substitution -/

/-- ≽ transitive ⇒ (u ∼ x ∧ v ∼ y ⇒ (x ≻ y ⇔ u ≻ v)):
`Transitivity r → (u ∼[r] x ∧ v ∼[r] y) → ((x ≻[r] y) ↔ u ≻[r] v)`. -/
lemma strict_substitution {α : Type*} (r : Relation α) :
    Transitivity r → ∀ x y u v : α, (u ∼[r] x ∧ v ∼[r] y) → ((x ≻[r] y) ↔ u ≻[r] v) := by
  intro htrans x y u v huixviy
  have honedir : ∀ (x y u v : α), (u ∼[r] x ∧ v ∼[r] y) → ((x ≻[r] y) → u ≻[r] v) := by
    intro x y u v huixviy hxsy
    rcases huixviy with ⟨huix, hviy⟩
    have huv : u ≽[r] v := by
      have huy : u ≽[r] y := htrans u x y ⟨huix.left, hxsy.left⟩
      exact htrans u y v ⟨huy, hviy.right⟩
    have hnvu : ¬(v ≽[r] u) := by
      intro hvu
      have hyu : y ≽[r] u := htrans y v u ⟨hviy.right, hvu⟩
      have hyx : y ≽[r] x := htrans y u x ⟨hyu, huix.left⟩
      exact hxsy.right hyx
    exact ⟨huv, hnvu⟩
  constructor
  · -- ===== Forward direction =====
    intro hxsy
    exact honedir x y u v huixviy hxsy
  · -- ===== Backward direction =====
    intro husv
    exact honedir u v x y
      ⟨⟨huixviy.left.right, huixviy.left.left⟩, ⟨huixviy.right.right, huixviy.right.left⟩⟩ husv

/-- ≽ complete ∧ transitive ∧ independent ⇒
(x ∼ u +[p] v ∧ y ∼ u +[q] v ⇒ x +[k] y ∼ u +[k p + (1 − k) q] v):
`(x ∼[r] u +[p] v) ∧ (y ∼[r] u +[q] v) →
(x +[k] y) ∼[r] (u +[⟨k.1 * p.1 + (1 - k.1) * q.1, _⟩] v)`. -/
lemma linear_substitution [MixSpace α] (r : Relation α) :
    Completeness r ∧ Transitivity r ∧ Independence r → ∀ x y u v : α, ∀ p q k : IntervalType,
    (x ∼[r] u +[p] v) ∧ (y ∼[r] u +[q] v) →
    (x +[k] y) ∼[r] (u +[⟨k.1 * p.1 + (1 - k.1) * q.1, assoc_of_mix_mem_Icc p.2 q.2 k.2⟩] v) := by
  intro h x y u v p q k hxy
  rcases h with ⟨hcompl, htrans, hindep⟩
  rcases hxy with ⟨hxip, hyiq⟩
  -- From independence on x ∼ (u+[p]v) mixing with k and (u +[q]v) we get
  -- (x +[k] (u +[q] v)) ∼ ((u +[p] v) +[k] (u +[q] v))
  have hmixx : (x +[k] (u +[q] v)) ∼[r] ((u +[p] v) +[k] (u +[q] v)) :=
    full_indiff_indep r ⟨hcompl, hindep⟩ x (u +[p] v) hxip (u +[q] v) k
  -- From independence on y ∼ (u+[q]v) mixing with 1-k and x we get
  -- (y +[1-k] x) ∼ ((u +[q] v) +[1-k] x)
  have hmixy : (y +[⟨1 - k.1, comm_mem_Icc k.2⟩] x) ∼[r]
      ((u +[q] v) +[⟨1 - k.1, comm_mem_Icc k.2⟩] x) :=
    full_indiff_indep r ⟨hcompl, hindep⟩ y (u +[q] v) hyiq x ⟨1 - k.1, comm_mem_Icc k.2⟩
  -- By commutativity, the rhs ((u +[q] v) +[1-k] x) = (x +[k] (u +[q] v))
  have hcomm := MixSpace.mix_comm k x (u +[q] v)
  rw [← hcomm] at hmixy
  -- By commutativity, the lhs (y +[1-k] x) = (x +[k] y)
  have hcomm₂ := MixSpace.mix_comm k x y
  rw [← hcomm₂] at hmixy
  -- So we get (x +[k] y) ∼ (x +[k] (u +[q] v))
  -- By transitivity we have
  -- (x +[k] y) ∼ ((u +[p] v) +[k] (u +[q] v))
  have hres : (x +[k] y) ∼[r] ((u +[p] v) +[k] (u +[q] v)) :=
    indiff_transitivity r htrans (x +[k] y) (x +[k] (u +[q] v)) ((u +[p] v) +[k] (u +[q] v))
      ⟨hmixy, hmixx⟩
  -- Now we just need to show that
  -- (u +[p] v) +[k] (u +[q] v) = (u +[k * p + (1 - k) * q] v)
  -- This is just associativity of mixtures
  have hassoc := associativity_of_mixtures u v p q k
  rw [hassoc] at hres
  exact hres

/-! #### Structures needed for the proof of the vNM theorem -/

/-- The elements between b and a (S(a, b) = {x : a ≽ x ≽ b}):
`S r a b := {x : α | a ≽[r] x ∧ x ≽[r] b}`. -/
def S (r : Relation α) (a b : α) [MixSpace α] : Set α :=
  {x : α | a ≽[r] x ∧ x ≽[r] b}

/-- μ(a, b, x): the unique p with a +[p] b ∼ x, carrying its proof of uniqueness:
`p : IntervalType`, `spec : (a +[p] b) ∼[r] x`, `unique : ∀ k, (a +[k] b) ∼[r] x → k = p`. -/
structure μType (r : Relation α) (a b x : α) [MixSpace α] where
  p : IntervalType
  spec : ((a +[p] b) ∼[r] x)
  unique : ∀ (k : IntervalType), ((a +[k] b) ∼[r] x) → k = p

/-- M(a, b, x) = (μ(x) − μ(n)) / (μ(m) − μ(n)), with μ(m) ≠ μ(n):
`eval = (μx.p.val - μn.p.val) / (μm.p.val - μn.p.val)`,
`defined : μm.p.val - μn.p.val ≠ 0`. -/
structure MType (r : Relation α) (a b x m n : α) [MixSpace α] where
  eval : ℝ
  μx : μType r a b x
  μm : μType r a b m
  μn : μType r a b n
  spec : eval = (μx.p.val - μn.p.val) / (μm.p.val - μn.p.val)
  defined : μm.p.val - μn.p.val ≠ 0

/-- u(x): a pair a ≻ b with x, m, n ∈ S(a, b), and the value M(a, b, x):
`eval : MType r a b x m n`, `hab : a ≻[r] b`, `hx : x ∈ S r a b`, `hm`, `hn`. -/
structure uType (r : Relation α) (x m n : α) [MixSpace α] where
  a : α
  b : α
  eval : MType r a b x m n
  hab : a ≻[r] b
  hx : x ∈ S r a b
  hm : m ∈ S r a b
  hn : n ∈ S r a b

/-! ### Proof -/

/-! #### Forward direction -/

/-- vNM theorem, forward direction (≽ satisfies the vNM axioms ⇒ ∃ utility function u):
`VNMAxioms r → ∃ u : α → ℝ, UtilityFunction u r`. -/
lemma exists_utility_of_vNMAxioms [MixSpace α] (r : Relation α) :
    VNMAxioms r → ∃ u : α → ℝ, UtilityFunction u r := by
  -- ===== Setup: unpack the vNM axioms =====
  intro hvNM
  rcases hvNM with ⟨hcompl, htrans, hindep, hcont⟩
  have hspc := strict_p_consistency r ⟨hcompl, hindep⟩
  -- By cases: ∃ m, n : α, m ≻ n or ∀ x y : α, x ∼ y
  by_cases hsame : ∀ x y : α, x ∼[r] y
  · -- ===== Case 1: all elements are indifferent, u = 0 =====
    -- Then u(x) = 0 for all x is a valid utility function
    have hexists : ∃ u : α → ℝ, UtilityFunction u r := by
      let u := fun x : α ↦ (0 : ℝ)
      have huoc : OrdinalConsistent u r := by
        intro x y
        constructor
        · -- x ≽ y → u x ≥ u y
          intro hxy
          simp [u]
        · -- u x ≥ u y → x ≽ y
          intro huxy
          exact (hsame x y).left
      have huplin : PLinear u := by
        intro x y p
        simp [u]
      exact ⟨u, ⟨huoc, huplin⟩⟩
    exact hexists
  · -- ===== Case 2: there exist m ≻ n =====
    -- ===== Find m ≻ n =====
    have hexmn : ∃ m n : α, m ≻[r] n := by
      rcases Classical.not_forall.mp hsame with ⟨m, hnall⟩
      rcases Classical.not_forall.mp hnall with ⟨n, hnmin⟩
      -- From hnmin : ¬(m ∼ n), we have m ≻ n or n ≻ m
      have hor : m ≻[r] n ∨ n ≻[r] m := by
        have hnor := not_and_or.mp hnmin
        cases hnor with
        | inl hnmn => exact Or.inr ⟨(hcompl m n).resolve_left hnmn, hnmn⟩
        | inr hnnm => exact Or.inl ⟨(hcompl m n).resolve_right hnnm, hnnm⟩
      cases hor with
      | inl hmsn => exact ⟨m, n, hmsn⟩
      | inr hnsm => exact ⟨n, m, hnsm⟩
    rcases hexmn with ⟨m, n, hmsn⟩
    -- ===== Define μ(a, b, x), the unique p with a +[p] b ∼ x =====
    -- Define then the function μ : S(a, b) → ℝ
    -- with μ(a, b, x) = p where a +[p] b ∼ x
    -- Since the definition of μ involves choice, annoyingly we
    -- have to carry the proof of uniqueness around
    have huc := unique_continuity r ⟨hcompl, htrans, hindep, hcont⟩
    let μ (a b : α) (hasb : a ≻[r] b) (x : α) (hx : x ∈ S r a b) : μType r a b x :=
      have hp : ∃! p : IntervalType, (a +[p] b) ∼[r] x := huc a x b ⟨hasb, hx.left, hx.right⟩
      have hspec := Classical.choose_spec hp
      ⟨Classical.choose hp, hspec.left, hspec.right⟩
    -- ===== Two values of μ for the same x are equal =====
    -- Show that if we have two μ of the same type, then they are equal
    have hμunique : ∀ (a b : α) (x : α)
        (q1 q2 : μType r a b x), q1.p = q2.p := by
      intro a b x q1 q2
      have hq1spec : (a +[q1.p] b) ∼[r] x := q1.spec
      have hq2unique : ∀ (k : IntervalType), (a +[k] b) ∼[r] x → k = q2.p := q2.unique
      exact hq2unique q1.p hq1spec
    -- ===== μ is strictly ordinal consistent =====
    -- Show that μ is strict ordinal consistent
    have hμord : ∀ (a b : α) (hasb : a ≻[r] b),
        (∀ (x y : α) (hx : x ∈ S r a b) (hy : y ∈ S r a b),
        ∀ (μ_x : μType r a b x) (μ_y : μType r a b y),
        (x ≻[r] y) ↔ (μ_x.p.1 > μ_y.p.1)) := by
      intro a b hasb x y hx hy μ_x μ_y
      set hμx := μ_x.spec
      set hμy := μ_y.spec
      -- From x ≻ y ↔ (a +[μ x] b) ≻ (a +[μ y] b)
      have hiff : x ≻[r] y ↔ (a +[μ_x.p] b) ≻[r] (a +[μ_y.p] b) :=
        strict_substitution r htrans x y (a +[μ_x.p] b) (a +[μ_y.p] b) ⟨hμx, hμy⟩
      -- By strict p-consistency, we have
      -- (a +[μ x] b) ≻ (a +[μ y] b) ↔ (μ x > μ y)
      have hspcab := hspc a b hasb
      have hiff₂ := hspcab μ_x.p μ_y.p
      -- Combine these two
      exact Iff.trans hiff hiff₂
    -- ===== S(a, b) is closed under mixtures =====
    -- Show that μ is p-linear
    -- First show that if x, y ∈ S(a, b), then x +[p] y ∈ S(a, b)
    have hmixinS : ∀ (a b : α) (x y : α) (hx : x ∈ S r a b) (hy : y ∈ S r a b)
        (p : IntervalType), (x +[p] y) ∈ S r a b := by
      intro a b x y hx hy p
      have hcxy := hcompl x y
      cases hcxy with
      | inl hxy =>
        -- By partial_interior we have x ≽ x +[p] y ≽ y
        have hfpi := full_partial_interior r ⟨hcompl, hindep⟩
        have hxmix := hfpi x y hxy p
        -- By transitivity we have a ≽ x +[p] y ≽ b
        have hamix : a ≽[r] (x +[p] y) := htrans a x (x +[p] y) ⟨hx.left, hxmix.left⟩
        have hmixb : (x +[p] y) ≽[r] b := htrans (x +[p] y) y b ⟨hxmix.right, hy.right⟩
        exact ⟨hamix, hmixb⟩
      | inr hyx =>
        -- By partial_interior we have y ≽ x +[p] y ≽ x
        have hfpi := full_partial_interior r ⟨hcompl, hindep⟩
        have hymix := hfpi y x hyx ⟨1 - p.1, comm_mem_Icc p.2⟩
        have hcomm := MixSpace.mix_comm p x y
        rw [← hcomm] at hymix
        -- By transitivity we have a ≽ x +[p] y ≽ b
        have hamix : a ≽[r] (x +[p] y) := htrans a y (x +[p] y) ⟨hy.left, hymix.left⟩
        have hmixb : (x +[p] y) ≽[r] b := htrans (x +[p] y) x b ⟨hymix.right, hx.right⟩
        exact ⟨hamix, hmixb⟩
    -- ===== μ is p-linear =====
    -- Now we can show p-linearity
    have hμplin : ∀ (a b : α) (x y : α) (hx : x ∈ S r a b) (hy : y ∈ S r a b)
        (p : IntervalType) (μ_x : μType r a b x) (μ_y : μType r a b y)
        (μ_mix : μType r a b (x +[p] y)),
        ∃ (hmixin : (x +[p] y) ∈ S r a b),
        μ_mix.p.1 = p.1 * μ_x.p.1 + (1 - p.1) * μ_y.p.1 := by
      intro a b x y hx hy p μ_x μ_y μ_mix
      -- By hmixinS we have (x +[p] y) ∈ S(a, b)
      have hmixin : (x +[p] y) ∈ S r a b := hmixinS a b x y hx hy p
      -- We want to show that μ_mix = p * μ_x + (1-p) * μ_y
      -- By linear_substitution, we have (x +[p] y) ∼ (a +[p * μ_x + (1-p) * μ_y] b)
      have hxiμ : x ∼[r] (a +[μ_x.p] b) := (indiff_symm r (a +[μ_x.p] b) x) μ_x.spec
      have hyiμ : y ∼[r] (a +[μ_y.p] b) := (indiff_symm r (a +[μ_y.p] b) y) μ_y.spec
      have hmixi := linear_substitution r ⟨hcompl, htrans, hindep⟩ x y a b
        μ_x.p μ_y.p p ⟨hxiμ, hyiμ⟩
      have hmixi' := (indiff_symm r (x +[p] y) (a +[⟨p.1 * μ_x.p.1 + (1 - p.1) * μ_y.p.1,
        assoc_of_mix_mem_Icc μ_x.p.2 μ_y.p.2 p.2⟩] b)) hmixi
      -- By uniqueness of μ, we have μ_mix = p * μ_x + (1-p) * μ_y
      have hunique := μ_mix.unique
      have heqp := hunique (⟨p.1 * μ_x.p.1 + (1 - p.1) * μ_y.p.1,
        assoc_of_mix_mem_Icc μ_x.p.2 μ_y.p.2 p.2⟩ : IntervalType) hmixi'
      have hval : μ_mix.1.1 = p.1 * μ_x.p.1 + (1 - p.1) * μ_y.p.1 :=
        (congrArg Subtype.val heqp).symm
      exact ⟨hmixin, hval⟩
    -- ===== Define M(a, b, x) = (μ(x) − μ(n)) / (μ(m) − μ(n)) =====
    -- Finally define M : S(a, b) → ℝ with
    -- M(a, b, x) = μ(a, b, x) - μ(a, b, n) / μ(a, b, m) - μ(a, b, n)
    let M (a b : α) (hasb : a ≻[r] b) (x : α) (hx : x ∈ S r a b)
        (hm : m ∈ S r a b) (hn : n ∈ S r a b) : MType r a b x m n :=
      let μ_x := μ a b hasb x hx
      let μ_m := μ a b hasb m hm
      let μ_n := μ a b hasb n hn
      let eval := (μ_x.p.val - μ_n.p.val) / (μ_m.p.val - μ_n.p.val)
      let spec : eval =
          (μ_x.p.val - μ_n.p.val) / (μ_m.p.val - μ_n.p.val) := by rfl
      let defined : μ_m.p.val - μ_n.p.val ≠ 0 := by
        have hμmsμn := (hμord a b hasb m n hm hn μ_m μ_n).mp hmsn
        linarith
      ⟨eval, μ_x, μ_m, μ_n, spec, defined⟩
    -- ===== M is strictly ordinal consistent =====
    -- Show that M is strict ordinal consistent
    have hMord : ∀ (a b : α) (hasb : a ≻[r] b),
        (∀ (x y : α) (hx : x ∈ S r a b) (hy : y ∈ S r a b)
        (hm : m ∈ S r a b) (hn : n ∈ S r a b) (M_x : MType r a b x m n)
        (M_y : MType r a b y m n),
        (x ≻[r] y) ↔ (M_x.eval > M_y.eval)) := by
      intro a b hasb x y hx hy hm hn M_x M_y
      rw [M_x.spec, M_y.spec]
      -- Unfold the definition of M
      set μ_x_data := M_x.μx
      set μ_x := μ_x_data.p
      set μ_m_data := M_x.μm
      set μ_m := μ_m_data.p
      set μ_n_data := M_x.μn
      set μ_n := μ_n_data.p
      set μ_y_data := M_y.μx
      set μ_y := μ_y_data.p
      set μ_m_y_data := M_y.μm
      set μ_m_y := μ_m_y_data.p
      set μ_n_y_data := M_y.μn
      set μ_n_y := μ_n_y_data.p
      -- First μ_m = μ_m_y and μ_n = μ_n_y since μ is unique
      have hμm : μ_m = μ_m_y := hμunique a b m μ_m_data μ_m_y_data
      have hμn : μ_n = μ_n_y := hμunique a b n μ_n_data μ_n_y_data
      rw [← hμm, ← hμn]
      -- Since m ≻ n, we have μ_m > μ_n
      have hμmsμn := (hμord a b hasb m n hm hn μ_m_data μ_n_data).mp hmsn
      -- We have to show that x ≻ y ↔ M_x > M_y
      constructor
      · -- Forward direction: x ≻ y → M_x > M_y
        intro hxsy
        -- By hμord we have μ_x > μ_y
        have hμxsμy := (hμord a b hasb x y hx hy μ_x_data μ_y_data).mp hxsy
        -- Therefore, M_x = (μ_x - μ_n)/((μ_m - μ_n)) > M_y = (μ_y - μ_n_y)/((μ_m_y - μ_n_y))
        have hMxsMy := by
          have hnum : (μ_x.1 - μ_n.1) > (μ_y.1 - μ_n.1) := by
            linarith
          have hden : (μ_m.1 - μ_n.1) > 0 := by
            linarith
          have hinvden : (μ_m.1 - μ_n.1)⁻¹ > 0 := inv_pos.mpr hden
          exact mul_lt_mul_of_pos_right hnum hinvden
        exact hMxsMy
      · -- Backward direction: M_x > M_y → x ≻ y
        intro hMxsMy
        -- We have (μ_x - μ_n)/(μ_m - μ_n) > (μ_y - μ_n)/(μ_m - μ_n)
        -- From this we can conclude that μ_x > μ_y
        have hμxsμy : μ_x.1 > μ_y.1 := by
          have hnum : (μ_x.1 - μ_n.1) > (μ_y.1 - μ_n.1) := by
            have hden : (μ_m.1 - μ_n.1) > 0 := by
              linarith
            have hinvden : (μ_m.1 - μ_n.1)⁻¹ > 0 := inv_pos.mpr hden
            have h := mul_lt_mul_of_pos_right hMxsMy hinvden
            field_simp at h
            exact h
          linarith
        -- By hμord we have x ≻ y
        exact (hμord a b hasb x y hx hy μ_x_data μ_y_data).mpr hμxsμy
    -- ===== M is p-linear =====
    -- Show that M is p-linear
    have hMplin : ∀ (a b : α) (x y : α) (hx : x ∈ S r a b) (hy : y ∈ S r a b)
        (p : IntervalType) (hm : m ∈ S r a b) (hn : n ∈ S r a b)
        (M_x : MType r a b x m n) (M_y : MType r a b y m n)
        (M_mix : MType r a b (x +[p] y) m n),
        M_mix.eval = p.1 * M_x.eval + (1 - p.1) * M_y.eval := by
      intro a b x y hx hy p hm hn M_x M_y M_mix
      rw [M_mix.spec, M_x.spec, M_y.spec]
      -- Unfold the definition of M
      set hμmneμn := M_x.defined
      set μ_x_data := M_x.μx
      set μ_x := μ_x_data.1
      set μ_m_data := M_x.μm
      set μ_m := μ_m_data.1
      set μ_n_data := M_x.μn
      set μ_n := μ_n_data.1
      set μ_y_data := M_y.μx
      set μ_y := μ_y_data.1
      set μ_m_y_data := M_y.μm
      set μ_m_y := μ_m_y_data.1
      set μ_n_y_data := M_y.μn
      set μ_n_y := μ_n_y_data.1
      set μ_mix_data := M_mix.μx
      set μ_mix := μ_mix_data.1
      set μ_m_mix_data := M_mix.μm
      set μ_m_mix := μ_m_mix_data.1
      set μ_n_mix_data := M_mix.μn
      set μ_n_mix := μ_n_mix_data.1
      -- First, μ_m = μ_m_y = μ_m_mix and μ_n = μ_n_y = μ_n_mix since μ is unique
      have hμm : μ_m = μ_m_y := hμunique a b m μ_m_data μ_m_y_data
      have hμn : μ_n = μ_n_y := hμunique a b n μ_n_data μ_n_y_data
      have hμmmix : μ_m = μ_m_mix := hμunique a b m μ_m_data μ_m_mix_data
      have hμnmix : μ_n = μ_n_mix := hμunique a b n μ_n_data μ_n_mix_data
      rw [← hμm, ← hμn, ← hμmmix, ← hμnmix]
      -- By μ being p-linear we have μ_mix.1 = p.1 * μ_x.1 + (1 - p.1) * μ_y.1
      have hμmixplin := hμplin a b x y hx hy p μ_x_data μ_y_data μ_mix_data
      have hμmixeq : μ_mix.1 = p.1 * μ_x.1 + (1 - p.1) * μ_y.1 := by
        rcases hμmixplin with ⟨_, heq⟩
        exact heq
      rw [hμmixeq]
      -- Therefore, M_mix = p * M_x + (1-p) * M_y
      field_simp [M_x.defined]
      ring_nf
    -- ===== M is constant on indifference classes =====
    -- Since it is ordinal consistent, it is equal for indifference
    have hMindiff : ∀ (a b : α) (hasb : a ≻[r] b),
        (∀ (x y : α) (hx : x ∈ S r a b) (hy : y ∈ S r a b)
        (hm : m ∈ S r a b) (hn : n ∈ S r a b) (M_x : MType r a b x m n)
        (M_y : MType r a b y m n),
        (x ∼[r] y) ↔ (M_x.eval = M_y.eval)) := by
      intro a b hasb x y hx hy hm hn M_x M_y
      constructor
      · -- Forward direction: x ∼ y → M_x = M_y
        intro hxiy
        have hnxsy : ¬(x ≻[r] y) := by
          intro hxsy
          exact absurd hxiy.right hxsy.right
        have hnysx : ¬(y ≻[r] x) := by
          intro hysx
          exact absurd hxiy.left hysx.right
        have hnMxsMy : ¬(M_x.1 > M_y.1) := by
          intro hMxsMy
          exact absurd ((hMord a b hasb x y hx hy hm hn M_x M_y).mpr hMxsMy) hnxsy
        have hnMysMx : ¬(M_y.1 > M_x.1) := by
          intro hMysMx
          exact absurd ((hMord a b hasb y x hy hx hm hn M_y M_x).mpr hMysMx) hnysx
        linarith
      · -- Backward direction: M_x = M_y → x ∼ y
        intro hMxeMy
        have hnMxsMy : ¬(M_x.1 > M_y.1) := by
          intro hMxsMy
          exact absurd hMxeMy (ne_of_gt hMxsMy)
        have hnMysMx : ¬(M_y.1 > M_x.1) := by
          intro hMysMx
          exact absurd hMxeMy.symm (ne_of_gt hMysMx)
        have hnxsy : ¬(x ≻[r] y) := by
          intro hxsy
          exact absurd ((hMord a b hasb x y hx hy hm hn M_x M_y).mp hxsy) hnMxsMy
        have hnysx : ¬(y ≻[r] x) := by
          intro hysx
          exact absurd ((hMord a b hasb y x hy hx hm hn M_y M_x).mp hysx) hnMysMx
        have hxy : x ≽[r] y := by
          have hcxy := hcompl x y
          cases hcxy with
          | inl hxy => exact hxy
          | inr hyx =>
            by_contra hnxy
            exact hnysx ⟨hyx, hnxy⟩
        have hyx : y ≽[r] x := by
          have hcyx := hcompl y x
          cases hcyx with
          | inl hyx => exact hyx
          | inr hxy =>
            by_contra hnyx
            exact hnxsy ⟨hxy, hnyx⟩
        exact ⟨hxy, hyx⟩
    -- ===== M(m) = 1 =====
    -- M_ab(m) = 1
    have hMm : ∀ (a b : α)
        (hm : m ∈ S r a b) (hn : n ∈ S r a b) (M_m : MType r a b m m n),
        M_m.eval = 1 := by
      intro a b hm hn M_m
      rw [M_m.spec]
      set hμmneμn := M_m.defined
      set μ_m_data := M_m.μx
      set μ_m := μ_m_data.1
      set μ_m_m_data := M_m.μm
      set μ_m_m := μ_m_m_data.1
      set μ_n_data := M_m.μn
      set μ_n := μ_n_data.1
      -- By uniqueness of μ, we have μ_m = μ_m_m
      have hμm : μ_m = μ_m_m := hμunique a b m μ_m_data μ_m_m_data
      rw [← hμm]
      rw [← hμm] at hμmneμn
      -- So M(m) = (μ_m - μ_n)/(μ_m - μ_n) = 1
      exact div_self hμmneμn
    -- ===== M(n) = 0 =====
    -- M_ab(n) = 0
    have hMn : ∀ (a b : α)
        (hm : m ∈ S r a b) (hn : n ∈ S r a b) (M_n : MType r a b n m n),
        M_n.eval = 0 := by
      intro a b hm hn M_n
      rw [M_n.spec]
      set μ_n_data := M_n.μx
      set μ_n := μ_n_data.1
      set μ_m_data := M_n.μm
      set μ_m := μ_m_data.1
      set μ_n_n_data := M_n.μn
      set μ_n_n := μ_n_n_data.1
      -- By uniqueness of μ, we have μ_n = μ_n_n
      have hμn : μ_n = μ_n_n := hμunique a b n μ_n_data μ_n_n_data
      rw [← hμn]
      -- So M(n) = (μ_n - μ_n)/(μ_m - μ_n) = 0
      rw [sub_self, zero_div]
    -- ===== M does not depend on the choice of a, b =====
    -- With this we can also show that M does not depend on the choice of a, b
    have hMindep : ∀ (a1 b1 a2 b2) (ha1sb1 : a1 ≻[r] b1) (ha2sb2 : a2 ≻[r] b2),
        ∀ (x : α) (hx1 : x ∈ S r a1 b1) (hx2 : x ∈ S r a2 b2)
        (hm1 : m ∈ S r a1 b1) (hm2 : m ∈ S r a2 b2)
        (hn1 : n ∈ S r a1 b1) (hn2 : n ∈ S r a2 b2)
        (M1 : MType r a1 b1 x m n) (M2 : MType r a2 b2 x m n),
        M1.eval = M2.eval := by
      intro a1 b1 a2 b2 ha1sb1 ha2sb2 x hx1 hx2 hm1 hm2 hn1 hn2 M1 M2
      -- ===== M1(m) = M2(m) = 1 and M1(n) = M2(n) = 0 =====
      let M1_m := M a1 b1 ha1sb1 m hm1 hm1 hn1
      let M1_n := M a1 b1 ha1sb1 n hn1 hm1 hn1
      have hM1m : M1_m.eval = 1 := hMm a1 b1 hm1 hn1 M1_m
      have hM1n : M1_n.eval = 0 := hMn a1 b1 hm1 hn1 M1_n
      let M2_m := M a2 b2 ha2sb2 m hm2 hm2 hn2
      let M2_n := M a2 b2 ha2sb2 n hn2 hm2 hn2
      have hM2m : M2_m.eval = 1 := hMm a2 b2 hm2 hn2 M2_m
      have hM2n : M2_n.eval = 0 := hMn a2 b2 hm2 hn2 M2_n
      by_cases hxm : x ≽[r] m
      · -- ===== Case 1: x ≽ m =====
        -- ===== By continuity, x +[k] n ∼ m for some k ≠ 0 =====
        -- Then since m ≻ n, we have x ≻ n
        have hxsn : x ≻[r] n := by
          have hxn : x ≽[r] n := htrans x m n ⟨hxm, hmsn.left⟩
          have hnnx : ¬(n ≽[r] x) := by
            intro hnx
            exact hmsn.right (htrans n x m ⟨hnx, hxm⟩)
          exact ⟨hxn, hnnx⟩
        -- By continuity x ≽ m ≻ n, ∃ k, m ~ x +[k] n
        have hcontk := hcont x m n ⟨hxm, hmsn.left⟩
        rcases hcontk with ⟨k, hkim⟩
        -- Also k ≠ 0
        have hkne0 : k.1 ≠ 0 := by
          intro hk0
          rw [mix_zero k x n hk0] at hkim
          exact absurd hkim.left hmsn.right
        -- ===== M1 and M2 are defined at x +[k] n =====
        -- (x +[k] n) ∈ S(a1, b1) and S(a2, b2)
        have hxknS1 : (x +[k] n) ∈ S r a1 b1 := hmixinS a1 b1 x n hx1 hn1 k
        have hxknS2 : (x +[k] n) ∈ S r a2 b2 := hmixinS a2 b2 x n hx2 hn2 k
        -- M1(x +[k] n) and M2(x +[k] n) are well defined
        let M1_xkn := M a1 b1 ha1sb1 (x +[k] n) hxknS1 hm1 hn1
        let M2_xkn := M a2 b2 ha2sb2 (x +[k] n) hxknS2 hm2 hn2
        -- ===== k M1(x) = 1 = k M2(x), so M1(x) = M2(x) =====
        -- Then by indiff consistent M1(m) = M1(x +[k] n) and M2(m) = M2(x +[k] n)
        have hM1km := (hMindiff a1 b1 ha1sb1 (x +[k] n)
          m hxknS1 hm1 hm1 hn1 M1_xkn M1_m).mp hkim
        have hM2km := (hMindiff a2 b2 ha2sb2 (x +[k] n)
          m hxknS2 hm2 hm2 hn2 M2_xkn M2_m).mp hkim
        -- Then by p-linearity M1(x +[k] n) = k * M1(x) + (1-k) * M1(n)
        -- and M2(x +[k] n) = k * M2(x) + (1-k) * M2(n)
        have hM1plin := hMplin a1 b1 x n hx1 hn1 k hm1 hn1 M1 M1_n M1_xkn
        rw [hM1km] at hM1plin
        have hM2plin := hMplin a2 b2 x n hx2 hn2 k hm2 hn2 M2 M2_n M2_xkn
        rw [hM2km] at hM2plin
        -- Since M1(m) = M2(m) = 1 and M1(n) = M2(n) = 0,
        -- we have M1(x) * k = 1 and M2(x) * k = 1
        have hM1k : 1 = k.1 * M1.eval := by
          rw [hM1m, hM1n] at hM1plin
          simp only [mul_zero, add_zero] at hM1plin
          exact hM1plin
        have hM2k : 1 = k.1 * M2.eval := by
          rw [hM2m, hM2n] at hM2plin
          simp only [mul_zero, add_zero] at hM2plin
          exact hM2plin
        -- Since k ≠ 0, we can conclude that M1(x) = M2(x)
        have hM1eM2 : M1.eval = M2.eval := by
          have hkM1eM2 : k.1 * M1.eval = k.1 * M2.eval := by
            set kval := (k.1 : ℝ)
            rw [hM1k] at hM2k
            exact hM2k
          exact mul_left_cancel₀ hkne0 hkM1eM2
        exact hM1eM2
      · -- ===== Case 2: ¬(x ≽ m) =====
        by_cases hnx : n ≽[r] x
        · -- ===== Subcase 2.1: n ≽ x =====
          -- ===== By continuity, m +[k] x ∼ n for some k ≠ 1 =====
          -- Then since m ≻ n, we have m ≻ x
          have hmsx : m ≻[r] x := by
            have hmx : m ≽[r] x := htrans m n x ⟨hmsn.left, hnx⟩
            have hnxm : ¬(x ≽[r] m) := by
              intro hxm'
              exact hmsn.right (htrans n x m ⟨hnx, hxm'⟩)
            exact ⟨hmx, hnxm⟩
          -- By continuity m ≻ n ≽ x, ∃ k, n ~ m +[k] x
          have hcontk := hcont m n x ⟨hmsn.left, hnx⟩
          rcases hcontk with ⟨k, hkin⟩
          -- Also k ≠ 1
          have hkne1 : k.1 ≠ 1 := by
            intro hk1
            rw [MixSpace.mix_one k m x hk1] at hkin
            exact absurd hkin.right hmsn.right
          -- ===== M1 and M2 are defined at m +[k] x =====
          -- (m +[k] x) ∈ S(a1, b1) and S(a2, b2)
          have hmkxS1 : (m +[k] x) ∈ S r a1 b1 := hmixinS a1 b1 m x hm1 hx1 k
          have hmkxS2 : (m +[k] x) ∈ S r a2 b2 := hmixinS a2 b2 m x hm2 hx2 k
          -- M1(m +[k] x) and M2(m +[k] x) are well defined
          let M1_mkx := M a1 b1 ha1sb1 (m +[k] x) hmkxS1 hm1 hn1
          let M2_mkx := M a2 b2 ha2sb2 (m +[k] x) hmkxS2 hm2 hn2
          -- ===== k + (1 - k) M1(x) = 0 = k + (1 - k) M2(x), so M1(x) = M2(x) =====
          -- Then by indiff consistent M1(n) = M1(m +[k] x) and M2(m) = M2(m +[k] x)
          have hM1kn := (hMindiff a1 b1 ha1sb1 (m +[k] x) n
            hmkxS1 hn1 hm1 hn1 M1_mkx M1_n).mp hkin
          have hM2kn := (hMindiff a2 b2 ha2sb2 (m +[k] x) n
            hmkxS2 hn2 hm2 hn2 M2_mkx M2_n).mp hkin
          -- Then by p-linearity M1(m +[k] x) = k * M1(m) + (1-k) * M1(x)
          -- and M2(m +[k] x) = k * M2(m) + (1-k) * M2(x)
          have hM1plin := hMplin a1 b1 m x hm1 hx1 k hm1 hn1 M1_m M1 M1_mkx
          rw [hM1kn] at hM1plin
          have hM2plin := hMplin a2 b2 m x hm2 hx2 k hm2 hn2 M2_m M2 M2_mkx
          rw [hM2kn] at hM2plin
          -- Since M1(m) = M2(m) = 1 and M1(n) = M2(n) = 0,
          -- we have k + (1-k) M1(x) = 0 and k + (1-k) M1(x) = 0
          have hM1k : 0 = k.1 + (1 - k.1) * M1.eval := by
            rw [hM1m, hM1n] at hM1plin
            simp only [mul_one] at hM1plin
            exact hM1plin
          have hM2k : 0 = k.1 + (1 - k.1) * M2.eval := by
            rw [hM2m, hM2n] at hM2plin
            simp only [mul_one] at hM2plin
            exact hM2plin
          -- Since k ≠ 1, we can conclude that M1(x) = M2(x)
          have hM1eM2 : M1.eval = M2.eval := by
            have hkM1eM2 : (1 - k.1) * M1.eval = (1 - k.1) * M2.eval := by
              set kval := (k.1 : ℝ)
              rw [hM1k] at hM2k
              exact add_left_cancel hM2k
            have h1kne0 : (1 - k.1) ≠ 0 := by
              set kval := (k.1 : ℝ)
              intro h1k0
              have hk1 : k.1 = 1 := by
                linarith
              exact absurd hk1 hkne1
            exact mul_left_cancel₀ h1kne0 hkM1eM2
          exact hM1eM2
        · -- ===== Subcase 2.2: ¬(n ≽ x) =====
          -- ===== By completeness m ≽ x ≽ n, and by continuity m +[k] n ∼ x =====
          -- Then since x ≽ m is false and n ≽ x is false,
          -- by completeness we have m ≽ x ≽ n
          have hmx : m ≽[r] x := (hcompl x m).resolve_left hxm
          have hxn : x ≽[r] n := (hcompl x n).resolve_right hnx
          -- By continuity m ≽ x ≽ n,  ∃ k, x ~ m +[k] n
          have hcontk := hcont m x n ⟨hmx, hxn⟩
          rcases hcontk with ⟨k, hkix⟩
          -- ===== M1 and M2 are defined at m +[k] n =====
          -- (m +[k] n) ∈ S(a1, b1) and S(a2, b2)
          have hmknS1 : (m +[k] n) ∈ S r a1 b1 := hmixinS a1 b1 m n hm1 hn1 k
          have hmknS2 : (m +[k] n) ∈ S r a2 b2 := hmixinS a2 b2 m n hm2 hn2 k
          -- M1(m +[k] n) and M2(m +[k] n) are well defined
          let M1_mkn := M a1 b1 ha1sb1 (m +[k] n) hmknS1 hm1 hn1
          let M2_mkn := M a2 b2 ha2sb2 (m +[k] n) hmknS2 hm2 hn2
          -- ===== M1(x) = k M1(m) + (1 − k) M1(n) = M2(x) =====
          -- Then by indiff consistent M1(x) = M1(m +[k] n) and M2(x) = M2(m +[k] n)
          have hM1kx := (hMindiff a1 b1 ha1sb1 (m +[k] n) x
            hmknS1 hx1 hm1 hn1 M1_mkn M1).mp hkix
          have hM2kx := (hMindiff a2 b2 ha2sb2 (m +[k] n) x
            hmknS2 hx2 hm2 hn2 M2_mkn M2).mp hkix
          -- Then by p-linearity M1(m +[k] n) = k * M1(m) + (1-k) * M1(n)
          -- and M2(m +[k] n) = k * M2(m) + (1-k) * M2(n)
          have hM1plin := hMplin a1 b1 m n hm1 hn1 k hm1 hn1 M1_m M1_n M1_mkn
          rw [hM1kx] at hM1plin
          have hM2plin := hMplin a2 b2 m n hm2 hn2 k hm2 hn2 M2_m M2_n M2_mkn
          rw [hM2kx] at hM2plin
          -- Since M1(m) = M2(m) and M1(n) = M2(n),
          -- we have M1(x) = M2(x)
          have hM1eM2 : M1.eval = M2.eval := by
            have hM1meM2m : M1_m.eval = M2_m.eval := by
              rw [hM1m, hM2m]
            have hM1neM2n : M1_n.eval = M2_n.eval := by
              rw [hM1n, hM2n]
            rw [← hM1meM2m, ← hM1neM2n, ← hM1plin] at hM2plin
            exact hM2plin.symm
          exact hM1eM2
    -- ===== For every x there are a ≽ x, m, n ≽ b with a ≻ b =====
    -- Then, show that for any x, there exist a, b with a ≽ x, m, n ≽ b and a ≻ b
    have hbounds : ∀ x : α, ∃ a b : α, a ≽[r] x ∧ a ≽[r] m ∧ a ≽[r] n ∧
        x ≽[r] b ∧ m ≽[r] b ∧ n ≽[r] b ∧ a ≻[r] b := by
      intro x
      -- First, there is a highest a and lowest element b between these three
      have hlargest : ∃ w, w ≽[r] x ∧ w ≽[r] m ∧ w ≽[r] n :=
        highest_element r ⟨hcompl, htrans⟩ x m n
      have hsmallest : ∃ w, x ≽[r] w ∧ m ≽[r] w ∧ n ≽[r] w :=
        lowest_element r ⟨hcompl, htrans⟩ x m n
      rcases hlargest with ⟨a, hax, ham, han⟩
      rcases hsmallest with ⟨b, hxb, hmb, hnb⟩
      -- a ≽ m ≻ n ≽ b, so a ≻ b
      have hasb : a ≻[r] b := by
        have hab : a ≽[r] b := htrans a n b ⟨han, hnb⟩
        have hnba : ¬(b ≽[r] a) := by
          intro hba
          have hna : n ≽[r] a := htrans n b a ⟨hnb, hba⟩
          exact hmsn.right (htrans n a m ⟨hna, ham⟩)
        exact ⟨hab, hnba⟩
      exact ⟨a, b, hax, ham, han, hxb, hmb, hnb, hasb⟩
    -- ===== Choose such a pair (a, b) for every x =====
    -- This needs to be defined this way for lean to understand the choose
    have hpair : ∀ x : α, ∃ ab : α × α,
        ab.1 ≽[r] x ∧ ab.1 ≽[r] m ∧ ab.1 ≽[r] n ∧
        x ≽[r] ab.2 ∧ m ≽[r] ab.2 ∧ n ≽[r] ab.2 ∧ ab.1 ≻[r] ab.2 := by
      intro x
      rcases hbounds x with ⟨a, b, hax, ham, han, hxb, hmb, hnb, hasb⟩
      exact ⟨(a, b), hax, ham, han, hxb, hmb, hnb, hasb⟩
    let abType (x : α) := {ab : α × α //
      ab.1 ≽[r] x ∧ ab.1 ≽[r] m ∧ ab.1 ≽[r] n ∧
      x ≽[r] ab.2 ∧ m ≽[r] ab.2 ∧ n ≽[r] ab.2 ∧ ab.1 ≻[r] ab.2}
    let ab (r : Relation α) (x : α) : abType x :=
      let hex := hpair x
      ⟨Classical.choose hex, Classical.choose_spec hex⟩
    -- ===== Define u(x) = M(a, b, x) for the chosen pair (a, b) =====
    -- Choose then a and b s.t. a ≽ x, m, n ≽ b and a ≽ b
    let uConst (x : α) : uType r x m n :=
      let abPair := ab r x
      let a := abPair.1.1
      let b := abPair.1.2
      let ⟨hax, ham, han, hxb, hmb, hnb, hasb⟩ := abPair.2
      let hxS : x ∈ S r a b := ⟨hax, hxb⟩
      let hmS : m ∈ S r a b := ⟨ham, hmb⟩
      let hnS : n ∈ S r a b := ⟨han, hnb⟩
      ⟨a, b, M a b hasb x ⟨hax, hxb⟩ hmS hnS, hasb, hxS, hmS, hnS⟩
    let u (x : α) : ℝ := (uConst x).eval.eval
    -- ===== u is ordinal consistent =====
    -- Show that u is ordinal consistent
    have huoc : OrdinalConsistent u r := by
      -- First gonna show it is strict ordinal consistent
      have huocs : OrdinalConsistentStrict u (Strict r) := by
        intro x y
        -- The biggest challenge is that each u x and u y are picking different a and b
        -- so we need to get a3 and b3 to compute M3(x) and M3(y) and compare it there
        set ux := uConst x
        set uy := uConst y
        set a1 := ux.a
        set b1 := ux.b
        set a2 := uy.a
        set b2 := uy.b
        set ha1sb1 := ux.hab
        set ha2sb2 := uy.hab
        set hx1 := ux.hx
        set hy1 := uy.hx
        set hm1 := ux.hm
        set hn1 := ux.hn
        set hm2 := uy.hm
        set hn2 := uy.hn
        -- ===== A common pair a3 ≻ b3 with a3 ≽ a1, a2 and b1, b2 ≽ b3 =====
        -- Either a1 ≽ a2 or a2 ≽ a1
        have hamax : ∃ w, w ≽[r] a1 ∧ w ≽[r] a2 := by
          by_cases ha1a2 : a1 ≽[r] a2
          · exact ⟨a1, ⟨(hcompl a1 a1).elim id id, ha1a2⟩⟩
          · have ha2a1 : a2 ≽[r] a1 := (hcompl a2 a1).resolve_right ha1a2
            exact ⟨a2, ⟨ha2a1, (hcompl a2 a2).elim id id⟩⟩
        -- Either b1 ≽ b2 or b2 ≽ b1
        have hbmin : ∃ w, b1 ≽[r] w ∧ b2 ≽[r] w := by
          by_cases hb1b2 : b1 ≽[r] b2
          · exact ⟨b2, ⟨hb1b2, (hcompl b2 b2).elim id id⟩⟩
          · have hb2b1 : b2 ≽[r] b1 := (hcompl b2 b1).resolve_right hb1b2
            exact ⟨b1, ⟨(hcompl b1 b1).elim id id, hb2b1⟩⟩
        rcases hamax with ⟨a3, ha3a1, ha3a2⟩
        rcases hbmin with ⟨b3, hb1b3, hb2b3⟩
        -- Now a3 ≽ a1, a2 and b1, b2 ≽ b3
        -- So a3 ≻ b3
        have ha3sb3 : a3 ≻[r] b3 := by
          have ha3b3 : a3 ≽[r] b3 := by
            have ha3b2 : a3 ≽[r] b2 := htrans a3 a2 b2 ⟨ha3a2, ha2sb2.left⟩
            exact htrans a3 b2 b3 ⟨ha3b2, hb2b3⟩
          have hnb3a3 : ¬(b3 ≽[r] a3) := by
            intro hb3a3
            have hb1a3 : b1 ≽[r] a3 := htrans b1 b3 a3 ⟨hb1b3, hb3a3⟩
            exact ha1sb1.right (htrans b1 a3 a1 ⟨hb1a3, ha3a1⟩)
          exact ⟨ha3b3, hnb3a3⟩
        -- ===== x, y, m, n ∈ S(a3, b3), so M3 is defined at x and y =====
        -- So x, y ∈ S(a3, b3)
        have hx3 : x ∈ S r a3 b3 :=
          ⟨htrans a3 a1 x ⟨ha3a1, hx1.left⟩, htrans x b1 b3 ⟨hx1.right, hb1b3⟩⟩
        have hy3 : y ∈ S r a3 b3 :=
          ⟨htrans a3 a2 y ⟨ha3a2, hy1.left⟩, htrans y b2 b3 ⟨hy1.right, hb2b3⟩⟩
        -- And m, n ∈ S(a3, b3)
        have hm3 : m ∈ S r a3 b3 :=
          ⟨htrans a3 a1 m ⟨ha3a1, hm1.left⟩, htrans m b1 b3 ⟨hm1.right, hb1b3⟩⟩
        have hn3 : n ∈ S r a3 b3 :=
          ⟨htrans a3 a1 n ⟨ha3a1, hn1.left⟩, htrans n b1 b3 ⟨hn1.right, hb1b3⟩⟩
        -- So M3(x) and M3(y) are defined
        let M3_x := M a3 b3 ha3sb3 x hx3 hm3 hn3
        let M3_y := M a3 b3 ha3sb3 y hy3 hm3 hn3
        -- ===== x ≻ y ⇔ M3(x) > M3(y), and u = M3 at x and y =====
        -- Now we have x ≻ y ↔ M3(x) > M3(y)
        have hiff : (x ≻[r] y) ↔ (M3_x.eval > M3_y.eval) :=
          hMord a3 b3 ha3sb3 x y hx3 hy3 hm3 hn3 M3_x M3_y
        -- Finally, u x = M3(x) and u y = M3(y)
        have huxeM3x : u x = M3_x.eval := by
          -- Unfold u x
          dsimp [u]
          -- Unfold uConst x
          dsimp [uConst]
          -- Need to show that M1(x) = M3(x)
          have hM13x := hMindep a1 b1 a3 b3 ha1sb1 ha3sb3 x hx1 hx3 hm1 hm3 hn1 hn3 ux.eval M3_x
          rw [hM13x]
        have huyeM3y : u y = M3_y.eval := by
          -- Unfold u y
          dsimp [u]
          -- Unfold uConst y
          dsimp [uConst]
          -- Need to show that M1(y) = M3(y)
          have hM13y := hMindep a2 b2 a3 b3 ha2sb2 ha3sb3 y hy1 hy3 hm2 hm3 hn2 hn3 uy.eval M3_y
          rw [hM13y]
        -- Combine all together
        rw [← huxeM3x, ← huyeM3y] at hiff
        exact hiff
      -- Now show ordinal consistency from strict ordinal consistency
      exact (ordinalConsistent_iff_ordinalConsistentStrict_of_completeness hcompl).mpr
        huocs
    -- ===== u is p-linear =====
    -- Show that u is p-linear
    have huplin : PLinear u := by
      intro x y k
      -- Similar to the ordinal consistency proof, we need to get a4 and b4 to
      -- compute M4(x +[k] y), M4(x) and M4(y) and compare it there
      set ux := uConst x
      set uy := uConst y
      set uk := uConst (x +[k] y)
      set a1 := ux.a
      set b1 := ux.b
      set ha1sb1 := ux.hab
      set hx1 := ux.hx
      set hm1 := ux.hm
      set hn1 := ux.hn
      set a2 := uy.a
      set b2 := uy.b
      set ha2sb2 := uy.hab
      set hy2 := uy.hx
      set hm2 := uy.hm
      set hn2 := uy.hn
      set a3 := uk.a
      set b3 := uk.b
      set ha3sb3 := uk.hab
      set hk3 := uk.hx
      set hm3 := uk.hm
      set hn3 := uk.hn
      -- ===== A common pair a4 ≻ b4 with a4 ≽ a1, a2, a3 and b1, b2, b3 ≽ b4 =====
      -- First, pick up the highest a and lowest b among these three pairs
      have ha4ex : ∃ w, w ≽[r] a1 ∧ w ≽[r] a2 ∧ w ≽[r] a3 :=
        highest_element r ⟨hcompl, htrans⟩ a1 a2 a3
      have hb4ex : ∃ w, b1 ≽[r] w ∧ b2 ≽[r] w ∧ b3 ≽[r] w :=
        lowest_element r ⟨hcompl, htrans⟩ b1 b2 b3
      rcases ha4ex with ⟨a4, ha4a1, ha4a2, ha4a3⟩
      rcases hb4ex with ⟨b4, hb1b4, hb2b4, hb3b4⟩
      -- Now a4 ≽ a1, a2, a3 and b1, b2, b3 ≽ b4
      -- So a4 ≻ b4
      have ha4sb4 : a4 ≻[r] b4 := by
        have ha4b4 : a4 ≽[r] b4 := by
          have ha4b3 : a4 ≽[r] b3 := htrans a4 a3 b3 ⟨ha4a3, uk.hab.left⟩
          exact htrans a4 b3 b4 ⟨ha4b3, hb3b4⟩
        have hnb4a4 : ¬(b4 ≽[r] a4) := by
          intro hb4a4
          have hb1a4 : b1 ≽[r] a4 := htrans b1 b4 a4 ⟨hb1b4, hb4a4⟩
          exact ha1sb1.right (htrans b1 a4 a1 ⟨hb1a4, ha4a1⟩)
        exact ⟨ha4b4, hnb4a4⟩
      -- ===== x, y, x +[k] y, m, n ∈ S(a4, b4), so M4 is defined there =====
      -- So x, y, x +[k] y ∈ S(a4, b4)
      have hx4 : x ∈ S r a4 b4 :=
        ⟨htrans a4 a1 x ⟨ha4a1, ux.hx.left⟩, htrans x b1 b4 ⟨ux.hx.right, hb1b4⟩⟩
      have hy4 : y ∈ S r a4 b4 :=
        ⟨htrans a4 a2 y ⟨ha4a2, uy.hx.left⟩, htrans y b2 b4 ⟨uy.hx.right, hb2b4⟩⟩
      have hk4 : (x +[k] y) ∈ S r a4 b4 :=
        ⟨htrans a4 a3 (x +[k] y) ⟨ha4a3, uk.hx.left⟩,
          htrans (x +[k] y) b3 b4 ⟨uk.hx.right, hb3b4⟩⟩
      -- So m, n ∈ S(a4, b4)
      have hm4 : m ∈ S r a4 b4 :=
        ⟨htrans a4 a1 m ⟨ha4a1, ux.hm.left⟩, htrans m b1 b4 ⟨ux.hm.right, hb1b4⟩⟩
      have hn4 : n ∈ S r a4 b4 :=
        ⟨htrans a4 a1 n ⟨ha4a1, ux.hn.left⟩, htrans n b1 b4 ⟨ux.hn.right, hb1b4⟩⟩
      -- So M4(x), M4(y) and M4(x +[k] y) are defined
      let M4_x := M a4 b4 ha4sb4 x hx4 hm4 hn4
      let M4_y := M a4 b4 ha4sb4 y hy4 hm4 hn4
      let M4_k := M a4 b4 ha4sb4 (x +[k] y) hk4 hm4 hn4
      -- ===== M4 is p-linear, and u = M4 at x, y and x +[k] y =====
      -- Now we have M4(x +[k] y) = k * M4(x) + (1-k) * M4(y)
      have hM4plin : M4_k.eval = k.1 * M4_x.eval + (1 - k.1) * M4_y.eval :=
        hMplin a4 b4 x y hx4 hy4 k hm4 hn4 M4_x M4_y M4_k
      -- Finally, u x = M4(x), u y = M4(y) and u (x +[k] y) = M4(x +[k] y)
      have huxeM4x : u x = M4_x.eval := by
        -- Unfold u x
        dsimp [u]
        -- Unfold uConst x
        dsimp [uConst]
        -- Need to show that M1(x) = M4(x)
        have hM14x := hMindep a1 b1 a4 b4 ha1sb1 ha4sb4 x hx1 hx4 hm1 hm4 hn1 hn4 ux.eval M4_x
        rw [hM14x]
      have huyeM4y : u y = M4_y.eval := by
        -- Unfold u y
        dsimp [u]
        -- Unfold uConst y
        dsimp [uConst]
        -- Need to show that M1(y) = M4(y)
        have hM14y := hMindep a2 b2 a4 b4 ha2sb2 ha4sb4 y hy2 hy4 hm2 hm4 hn2 hn4 uy.eval M4_y
        rw [hM14y]
      have hukeM4k : u (x +[k] y) = M4_k.eval := by
        -- Unfold u (x +[k] y)
        dsimp [u]
        -- Unfold uConst (x +[k] y)
        dsimp [uConst]
        -- Need to show that M1(x +[k] y) = M4(x +[k] y)
        have hM14k := hMindep a3 b3 a4 b4 ha3sb3 ha4sb4 (x +[k] y)
          hk3 hk4 hm3 hm4 hn3 hn4 uk.eval M4_k
        rw [hM14k]
      -- Combine all together
      rw [← huxeM4x, ← huyeM4y, ← hukeM4k] at hM4plin
      exact hM4plin
    -- ===== Conclude: u is a utility function =====
    -- Finally, conclude that u is a utility function
    exact ⟨u, huoc, huplin⟩

/-! #### Backward direction -/

/-- vNM theorem, backward direction (∃ utility function u ⇒ ≽ satisfies the vNM axioms):
`(∃ u : α → ℝ, UtilityFunction u r) → VNMAxioms r`. -/
lemma vNMAxioms_of_utility [MixSpace α] (r : Relation α) :
    (∃ u : α → ℝ, UtilityFunction u r) → VNMAxioms r := by
  intro hex
  rcases hex with ⟨u, huoc, huplin⟩
  -- Show vNM axioms
  have hvNM : VNMAxioms r := by
    -- ===== Completeness =====
    have hcompl : Completeness r := by
      intro x y
      have hcuxy : u x ≥ u y ∨ u y ≥ u x := le_total (u y) (u x)
      cases hcuxy with
      | inl huxy => exact Or.inl ((huoc x y).mpr huxy)
      | inr huyx => exact Or.inr ((huoc y x).mpr huyx)
    -- ===== Transitivity =====
    have htrans : Transitivity r := by
      intro x y z hxyz
      rcases hxyz with ⟨hxy, hyz⟩
      have huxy : u x ≥ u y := (huoc x y).mp hxy
      have huyz : u y ≥ u z := (huoc y z).mp hyz
      have huxz : u x ≥ u z := by linarith
      exact (huoc x z).mpr huxz
    -- ===== Independence =====
    have hindep : Independence r := by
      intro x y z k hkin
      constructor
      · -- x ≽ y → x +[k] z ≽ y +[k] z
        intro hxy
        have huxy : u x ≥ u y := (huoc x y).mp hxy
        have hukx : u (x +[k] z) = k.1 * u x + (1 - k.1) * u z := huplin x z k
        have huky : u (y +[k] z) = k.1 * u y + (1 - k.1) * u z := huplin y z k
        have humix : u (x +[k] z) ≥ u (y +[k] z) := by
          have hkuxy : k.1 * u x ≥ k.1 * u y := by
            have hk0 : 0 ≤ k.1 := k.2.left
            exact mul_le_mul_of_nonneg_left huxy hk0
          linarith
        exact (huoc (x +[k] z) (y +[k] z)).mpr humix
      · -- x +[k] z ≽ y +[k] z → x ≽ y
        intro hmixxy
        have hukx : u (x +[k] z) = k.1 * u x + (1 - k.1) * u z := huplin x z k
        have huky : u (y +[k] z) = k.1 * u y + (1 - k.1) * u z := huplin y z k
        have humix : u (x +[k] z) ≥ u (y +[k] z) := (huoc (x +[k] z) (y +[k] z)).mp hmixxy
        have hkpos : 0 < k.1 := hkin.left
        have hkuxy : k.1 * u x ≥ k.1 * u y := by
          linarith
        have huxy : u x ≥ u y := by
          have hinvk : 0 ≤ 1/k.1 := by
            apply div_nonneg
            · linarith
            · linarith
          have h := mul_le_mul_of_nonneg_left hkuxy hinvk
          field_simp [hkpos] at h
          exact h
        exact (huoc x y).mpr huxy
    -- ===== Continuity =====
    have hcont : Continuity r := by
      intro x y z hxyz
      rcases hxyz with ⟨hxy, hyz⟩
      have huxy : u x ≥ u y := (huoc x y).mp hxy
      have huyz : u y ≥ u z := (huoc y z).mp hyz
      have huxz : u x ≥ u z := by linarith
      by_cases huxsz : u x > u z
      · -- k = (u y - u z) / (u x - u z) is the right choice to make u(x +[k] z) = u y
        have hden : u x - u z > 0 := by
          linarith
        let kval := (u y - u z) / (u x - u z)
        have hk0 : 0 ≤ kval := by
          apply div_nonneg
          · linarith
          · linarith
        have hkle1 : kval ≤ 1 := by
          have huxy' : u y ≤ u x := huxy
          have hnum : u y - u z ≤ u x - u z := by
            linarith
          exact (div_le_one hden).mpr hnum
        have hkin : kval ∈ Set.Icc 0 1 := ⟨hk0, hkle1⟩
        let k : IntervalType := ⟨kval, hkin⟩
        have hukx : u (x +[k] z) = kval * u x + (1 - kval) * u z := huplin x z k
        have hrhs : kval * u x + (1 - kval) * u z = u y := by
          simp [kval]
          field_simp [hden]
          ring_nf
        rw [hrhs] at hukx
        have hmixy : (x +[k] z) ≽[r] y := (huoc (x +[k] z) y).mpr (ge_of_eq hukx)
        have hymix : y ≽[r] (x +[k] z) := (huoc y (x +[k] z)).mpr (le_of_eq hukx)
        exact ⟨k, ⟨hmixy, hymix⟩⟩
      · -- If ¬(u x > u z), then u x = u y = u z
        have huxez : u x = u z := by
          linarith
        have huxey : u x = u y := by
          linarith
        -- Then any k works, k = 1 for simplicity
        let k : IntervalType := ⟨1, by simp⟩
        have hukx : u (x +[k] z) = 1 * u x + (1 - 1) * u z := huplin x z k
        have hrhs : 1 * u x + (1 - 1) * u z = u y := by
          rw [← huxez, huxey]
          simp
        rw [hrhs] at hukx
        have hmixy : (x +[k] z) ≽[r] y := (huoc (x +[k] z) y).mpr (ge_of_eq hukx)
        have hymix : y ≽[r] (x +[k] z) := (huoc y (x +[k] z)).mpr (le_of_eq hukx)
        exact ⟨k, ⟨hmixy, hymix⟩⟩
    exact ⟨hcompl, htrans, hindep, hcont⟩
  -- And therefore we have vNM
  exact hvNM

/-! #### The vNM theorem -/

/-- vNM theorem (≽ satisfies the vNM axioms ⇔ ∃ utility function u):
`VNMAxioms r ↔ ∃ u : α → ℝ, UtilityFunction u r`.

A preference relation on a mixture space satisfies completeness, transitivity, independence,
and continuity ⇔ there exists a utility function u : α → ℝ.
Adapted from Herstein and Milnor (1953) "An Axiomatic Approach to Measurable Utility"
Theorem 8. -/
theorem vNM_theorem [MixSpace α] (r : Relation α) :
    VNMAxioms r ↔ ∃ u : α → ℝ, UtilityFunction u r := by
  constructor
  · -- ===== Forward direction =====
    exact exists_utility_of_vNMAxioms r
  · -- ===== Backward direction: ∃ u, UtilityFunction u r → VNMAxioms r =====
    exact vNMAxioms_of_utility r

end VNM

section Uniqueness

/-! ## Uniqueness of the utility function -/

/-- Utility generator (u₁ utility function ∧ a > 0 ⇒ u₂ = a u₁ + b utility function):
`UtilityFunction u1 r → a > 0 ∧ (∀ x, u2 x = a * u1 x + b) → UtilityFunction u2 r`.

If u1 is a utility function representing r, then any positive affine transformation of u1
is also a utility function representing r. -/
theorem utility_gen [MixSpace α] (r : Relation α) {u1 : α → ℝ}
    (h1 : UtilityFunction u1 r) :
    ∀ a b : ℝ, ∀ u2 : α → ℝ, a > 0 ∧ (∀ x : α, u2 x = a * u1 x + b) →
    UtilityFunction u2 r := by
  intro a b u2 h
  rcases h with ⟨hapos, hu2def⟩
  -- ===== u2 is ordinal consistent =====
  -- Show that u2 is ordinal consistent
  have hu2oc : OrdinalConsistent u2 r := by
    intro x y
    have hu1oc := h1.left
    have hu1xy : u1 x ≥ u1 y ↔ x ≽[r] y := (hu1oc x y).symm
    have hu2xy : u2 x ≥ u2 y ↔ x ≽[r] y := by
      calc
        u2 x ≥ u2 y ↔ a * u1 x + b ≥ a * u1 y + b := by simp [hu2def]
        _ ↔ a * u1 x ≥ a * u1 y := add_le_add_iff_right b
        _ ↔ u1 x ≥ u1 y := mul_le_mul_iff_of_pos_left hapos
      rw [hu1xy]
    exact hu2xy.symm
  -- ===== u2 is p-linear =====
  -- Show that u2 is p-linear
  have hu2plin : PLinear u2 := by
    intro x y k
    have hu1plin := h1.right
    have hu1k : u1 (x +[k] y) = k.1 * u1 x + (1 - k.1) * u1 y := hu1plin x y k
    have hu2k : u2 (x +[k] y) = a * u1 (x +[k] y) + b := by simp [hu2def]
    rw [hu2k, hu1k]
    have hu2aff : a * u1 x + b = u2 x ∧ a * u1 y + b = u2 y := by
      simp [hu2def]
    rw [← hu2aff.1, ← hu2aff.2]
    ring_nf
  -- ===== Conclude: u2 is a utility function =====
  -- Finally, conclude that u2 is a utility function
  exact ⟨hu2oc, hu2plin⟩

/-- Utility uniqueness (u₁, u₂ utility functions ⇒ ∃ a > 0, b with u₂ = a u₁ + b):
`VNMAxioms r → ∃ a b : ℝ, a > 0 ∧ (∀ x : α, u2 x = a * u1 x + b)`.

If u1 and u2 are both utility functions representing r, then there exist a > 0 and b
such that ∀ x, u2 x = a * u1 x + b. -/
theorem utility_unique [MixSpace α] (r : Relation α) {u1 u2 : α → ℝ}
    (h1 : UtilityFunction u1 r) (h2 : UtilityFunction u2 r) :
    VNMAxioms r → ∃ a b : ℝ, a > 0 ∧ (∀ x : α, u2 x = a * u1 x + b) := by
  -- ===== Setup =====
  -- have hvNM := (vNM_theorem r).mpr ⟨u1, h1⟩
  intro hvNM
  rcases hvNM with ⟨hcompl, htrans, _, hcont⟩
  have hu1oc := h1.left
  have hu2oc := h2.left
  have hu1plin := h1.right
  have hu2plin := h2.right
  -- By cases, α is not empty
  by_cases hempty : ¬(∃ x : α, True)
  · -- ===== Case 1: α is empty, then any a > 0 and b works =====
    exact ⟨1, 0, by simp, by intro x; exfalso; exact hempty ⟨x, trivial⟩⟩
  · -- ===== Case 2: α is not empty =====
    have hne : ∃ x : α, True := not_not.mp hempty
    -- By cases, ∀ x y, x ∼ y
    by_cases hallindiff : ∀ x y : α, x ∼[r] y
    · -- ===== Subcase 2.1: all elements are indifferent, a = 1 and b = u2 − u1 =====
      -- Then u1(x) = u1(y) and u2(x) = u2(y) for all x, y
      have hu1const : ∀ x y : α, u1 x = u1 y := by
        intro x y
        have hu1xy : u1 x ≥ u1 y := (hu1oc x y).mp (hallindiff x y).left
        have hu1yx : u1 y ≥ u1 x := (hu1oc y x).mp (hallindiff y x).left
        exact le_antisymm hu1yx hu1xy
      have hu2const : ∀ x y : α, u2 x = u2 y := by
        intro x y
        have hu2xy : u2 x ≥ u2 y := (hu2oc x y).mp (hallindiff x y).left
        have hu2yx : u2 y ≥ u2 x := (hu2oc y x).mp (hallindiff y x).left
        exact le_antisymm hu2yx hu2xy
      -- Then a = 1 and b = u2 - u1 works
      let x0 := Classical.choose hne
      let a := (1 : ℝ)
      have hapos : a > 0 := zero_lt_one
      let b := u2 x0 - u1 x0
      have hu2def : ∀ x : α, u2 x = a * u1 x + b := by
        intro x
        simp only [a, b]
        have hu1x0x : u1 x0 = u1 x := hu1const x0 x
        have hu2x0x : u2 x0 = u2 x := hu2const x0 x
        rw [hu1x0x, hu2x0x]
        ring_nf
      exact ⟨a, b, hapos, hu2def⟩
    · -- ===== Subcase 2.2: there exist x0 ≻ y0 =====
      -- ===== Find x0 ≻ y0 =====
      -- Then there exists x0, y0 such that ¬(x0 ∼[r] y0)
      have hexni : ∃ x0 y0 : α, ¬(x0 ∼[r] y0) := by
        rw [not_forall] at hallindiff
        rcases hallindiff with ⟨x, hnx⟩
        rw [not_forall] at hnx
        rcases hnx with ⟨y, hnxiy⟩
        exact ⟨x, y, hnxiy⟩
      -- Then there exists x0, y0 such that x0 ≻[r] y0
      have hexs : ∃ x0 y0 : α, x0 ≻[r] y0 := by
        rcases hexni with ⟨x0, y0, hnx0iy0⟩
        have hnor : ¬(x0 ≽[r] y0) ∨ ¬(y0 ≽[r] x0) := not_and_or.mp hnx0iy0
        have hcx0y0 : x0 ≽[r] y0 ∨ y0 ≽[r] x0 := hcompl x0 y0
        cases hcx0y0 with
        | inl hx0y0 => exact ⟨x0, y0, ⟨hx0y0,
          hnor.resolve_left (not_not.mpr hx0y0)⟩⟩
        | inr hy0x0 => exact ⟨y0, x0, ⟨hy0x0,
          hnor.resolve_right (not_not.mpr hy0x0)⟩⟩
      rcases hexs with ⟨x0, y0, hx0sy0⟩
      -- ===== u1 x0 > u1 y0 and u2 x0 > u2 y0 =====
      -- Then u1 x0 > u1 y0 and u2 x0 > u2 y0
      have hu1x0sy0 : u1 x0 > u1 y0 := by
        have hu1x0y0 : u1 x0 ≥ u1 y0 := (hu1oc x0 y0).mp hx0sy0.left
        have hnu1y0x0 : ¬(u1 y0 ≥ u1 x0) := by
          intro hu1y0x0
          have h := (hu1oc y0 x0).mpr hu1y0x0
          exact absurd h hx0sy0.right
        linarith
      have hu2x0sy0 : u2 x0 > u2 y0 := by
        have hu2x0y0 : u2 x0 ≥ u2 y0 := (hu2oc x0 y0).mp hx0sy0.left
        have hnu2y0x0 : ¬(u2 y0 ≥ u2 x0) := by
          intro hu2y0x0
          have h := (hu2oc y0 x0).mpr hu2y0x0
          exact absurd h hx0sy0.right
        linarith
      -- ===== Define a = (u2 x0 − u2 y0) / (u1 x0 − u1 y0) > 0 and b = u2 x0 − a u1 x0 =====
      -- Then we can define a = (u2 x0 - u2 y0) / (u1 x0 - u1 y0) and b = u2 x0 - a * u1 x0
      let a := (u2 x0 - u2 y0) / (u1 x0 - u1 y0)
      have hapos : a > 0 := by
        apply div_pos
        · linarith
        · linarith
      have hden : u1 x0 - u1 y0 ≠ 0 := by
        linarith
      let b := u2 x0 - a * u1 x0
      -- ===== u2 x = a u1 x + b for every x =====
      have hu2def : ∀ x : α, u2 x = a * u1 x + b := by
        intro x
        -- By cases
        by_cases hxx0 : x ≽[r] x0
        · -- ===== Case x ≽ x0: x0 ∼ x +[k] y0 =====
          -- If x ≽ x0, then x ≽ x0 ≻ y0
          -- And therefore x0 = x +[k] y0 for some k > 0
          have hexk : ∃ (k : IntervalType), ((x +[k] y0) ∼[r] x0) :=
            hcont x x0 y0 ⟨hxx0, hx0sy0.left⟩
          rcases hexk with ⟨k, hkix0⟩
          have hkne0 : k.1 ≠ 0 := by
            intro hk0
            have hy0x0 : y0 ≽[r] x0 := by
              have hkx0 := hkix0.left
              have hmix := mix_zero k x y0 hk0
              rw [hmix] at hkx0
              exact hkx0
            exact absurd hy0x0 hx0sy0.right
          -- ===== u1 x0 and u2 x0 by p-linearity =====
          -- Then u1 x0 = u1 (x +[k] y0) = k * u1 x + (1-k) * u1 y0
          -- and u2 x0 = u2 (x +[k] y0) = k * u2 x + (1-k) * u2 y0
          have hu1x0ge : u1 x0 ≥ k.1 * u1 x + (1 - k.1) * u1 y0 := by
            have hord := (hu1oc x0 (x +[k] y0)).mp hkix0.right
            rw [hu1plin x y0 k] at hord
            exact hord
          have hu1x0le : k.1 * u1 x + (1 - k.1) * u1 y0 ≥ u1 x0 := by
            have hord := (hu1oc (x +[k] y0) x0).mp hkix0.left
            rw [hu1plin x y0 k] at hord
            exact hord
          have hu1x0e : u1 x0 = k.1 * u1 x + (1 - k.1) * u1 y0 := by
            linarith
          have hu2x0ge : u2 x0 ≥ k.1 * u2 x + (1 - k.1) * u2 y0 := by
            have hord := (hu2oc x0 (x +[k] y0)).mp hkix0.right
            rw [hu2plin x y0 k] at hord
            exact hord
          have hu2x0le : k.1 * u2 x + (1 - k.1) * u2 y0 ≥ u2 x0 := by
            have hord := (hu2oc (x +[k] y0) x0).mp hkix0.left
            rw [hu2plin x y0 k] at hord
            exact hord
          have hu2x0e : u2 x0 = k.1 * u2 x + (1 - k.1) * u2 y0 := by
            linarith
          -- ===== Solve for u1 x and u2 x, and combine =====
          -- Then u1 x = (u1 x0 - (1-k) * u1 y0)/k
          -- and u2 x = (u2 x0 - (1-k) * u2 y0)/k
          have hu1x : u1 x = (u1 x0 - (1 - k.1) * u1 y0)/k.1 := by
            rw [hu1x0e]
            ring_nf
            field_simp [hkne0]
          have hu2x : u2 x = (u2 x0 - (1 - k.1) * u2 y0)/k.1 := by
            rw [hu2x0e]
            ring_nf
            field_simp [hkne0]
          -- Combine all together to show u2 x = a * u1 x + b
          have hu2xab : u2 x = a * u1 x + b := by
            rw [hu1x, hu2x]
            simp [a, b]
            field_simp [hden]
            ring_nf
          exact hu2xab
        · -- If ¬(x ≽ x0), then x0 ≻ x
          have hx0sx : x0 ≻[r] x := ⟨(hcompl x x0).resolve_left hxx0, hxx0⟩
          by_cases hy0x : y0 ≽[r] x
          · -- ===== Case x0 ≻ y0 ≽ x: y0 ∼ x0 +[k] x =====
            -- If y0 ≽ x, then x0 ≻ y0 ≽ x
            -- And therefore y0 = x0 +[k] x for some k > 0
            have hexk : ∃ (k : IntervalType), ((x0 +[k] x) ∼[r] y0) :=
              hcont x0 y0 x ⟨hx0sy0.left, hy0x⟩
            rcases hexk with ⟨k, hkiy0⟩
            have hkne1 : k.1 ≠ 1 := by
              intro hk1
              have hy0x0 : y0 ≽[r] x0 := by
                have hy0k := hkiy0.right
                have hmix := MixSpace.mix_one k x0 x hk1
                rw [hmix] at hy0k
                exact hy0k
              exact absurd hy0x0 hx0sy0.right
            have h1kne0 : (1 - k.1) ≠ 0 := sub_ne_zero_of_ne hkne1.symm
            -- ===== u1 y0 and u2 y0 by p-linearity =====
            -- Then u1 y0 = u1 (x0 +[k] x) = k * u1 x0 + (1-k) * u1 x
            -- and u2 y0 = u2 (x0 +[k] x) = k * u2 x0 + (1-k) * u2 x
            have hu1y0ge : u1 y0 ≥ k.1 * u1 x0 + (1 - k.1) * u1 x := by
              have hord := (hu1oc y0 (x0 +[k] x)).mp hkiy0.right
              rw [hu1plin x0 x k] at hord
              exact hord
            have hu1y0le : k.1 * u1 x0 + (1 - k.1) * u1 x ≥ u1 y0 := by
              have hord := (hu1oc (x0 +[k] x) y0).mp hkiy0.left
              rw [hu1plin x0 x k] at hord
              exact hord
            have hu1y0e : u1 y0 = k.1 * u1 x0 + (1 - k.1) * u1 x := by
              linarith
            have hu2y0ge : u2 y0 ≥ k.1 * u2 x0 + (1 - k.1) * u2 x := by
              have hord := (hu2oc y0 (x0 +[k] x)).mp hkiy0.right
              rw [hu2plin x0 x k] at hord
              exact hord
            have hu2y0le : k.1 * u2 x0 + (1 - k.1) * u2 x ≥ u2 y0 := by
              have hord := (hu2oc (x0 +[k] x) y0).mp hkiy0.left
              rw [hu2plin x0 x k] at hord
              exact hord
            have hu2y0e : u2 y0 = k.1 * u2 x0 + (1 - k.1) * u2 x := by
              linarith
            -- ===== Solve for u1 x and u2 x, and combine =====
            -- Then u1 x = (u1 y0 - k * u1 x0)/(1 - k)
            -- and u2 x = (u2 y0 - k * u2 x0)/(1 - k)
            have hu1x : u1 x = (u1 y0 - k.1 * u1 x0)/(1 - k.1) := by
              rw [hu1y0e]
              field_simp [h1kne0]
              ring_nf
            have hu2x : u2 x = (u2 y0 - k.1 * u2 x0)/(1 - k.1) := by
              rw [hu2y0e]
              field_simp [h1kne0]
              ring_nf
            -- Combine all together to show u2 x = a * u1 x + b
            have hu2xab : u2 x = a * u1 x + b := by
              rw [hu1x, hu2x]
              simp [a, b]
              field_simp [hden]
              ring_nf
            exact hu2xab
          · -- ===== Case x0 ≻ x ≻ y0: x ∼ x0 +[k] y0 =====
            -- If ¬(y0 ≽ x), then x ≻ y0
            have hxsy0 : x ≻[r] y0 := ⟨(hcompl x y0).resolve_right hy0x, hy0x⟩
            -- Then x = x0 +[k] y0 for some k > 0
            have hexk : ∃ (k : IntervalType), ((x0 +[k] y0) ∼[r] x) :=
              hcont x0 x y0 ⟨hx0sx.left, hxsy0.left⟩
            rcases hexk with ⟨k, hkix⟩
            -- ===== u1 x and u2 x by p-linearity, and combine =====
            -- Then u1 x = u1 (x0 +[k] y0) = k * u1 x0 + (1-k) * u1 y0
            -- and u2 x = u2 (x0 +[k] y0) = k * u2 x0 + (1-k) * u2 y0
            have hu1xge : u1 x ≥ k.1 * u1 x0 + (1 - k.1) * u1 y0 := by
              have hord := (hu1oc x (x0 +[k] y0)).mp hkix.right
              rw [hu1plin x0 y0 k] at hord
              exact hord
            have hu1xle : k.1 * u1 x0 + (1 - k.1) * u1 y0 ≥ u1 x := by
              have hord := (hu1oc (x0 +[k] y0) x).mp hkix.left
              rw [hu1plin x0 y0 k] at hord
              exact hord
            have hu1xe : u1 x = k.1 * u1 x0 + (1 - k.1) * u1 y0 := by
              linarith
            have hu2xge : u2 x ≥ k.1 * u2 x0 + (1 - k.1) * u2 y0 := by
              have hord := (hu2oc x (x0 +[k] y0)).mp hkix.right
              rw [hu2plin x0 y0 k] at hord
              exact hord
            have hu2xle : k.1 * u2 x0 + (1 - k.1) * u2 y0 ≥ u2 x := by
              have hord := (hu2oc (x0 +[k] y0) x).mp hkix.left
              rw [hu2plin x0 y0 k] at hord
              exact hord
            have hu2xe : u2 x = k.1 * u2 x0 + (1 - k.1) * u2 y0 := by
              linarith
            -- Combine all together to show u2 x = a * u1 x + b
            have hu2xab : u2 x = a * u1 x + b := by
              rw [hu1xe, hu2xe]
              simp [a, b]
              field_simp [hden]
              ring_nf
            exact hu2xab
      exact ⟨a, b, hapos, hu2def⟩

/-- Corollary (∃ utility function ⇒ ∀ c, x, ∃ utility function u' with u'(x) = c):
`(∃ u, UtilityFunction u r) → ∀ c x, ∃ u', UtilityFunction u' r ∧ u' x = c`.

Given a utility function, we can construct another utility function that gives any
desired value to a particular element. -/
lemma utility_offset [MixSpace α] (r : Relation α)
    (hexists : ∃ u : α → ℝ, UtilityFunction u r) :
    ∀ c : ℝ, ∀ x : α, ∃ u' : α → ℝ, UtilityFunction u' r ∧ u' x = c := by
  rcases hexists with ⟨u, hu⟩
  intro c x
  let a := (1 : ℝ)
  let b := c - u x
  let u' := fun y : α ↦ a * u y + b
  have hau' : UtilityFunction u' r :=
    utility_gen r hu a b u' ⟨by linarith, by intro y; rfl⟩
  refine ⟨u', hau', ?_⟩
  calc
    u' x = a * u x + b := by rfl
    _ = (1 : ℝ) * u x + (c - u x) := by rfl
    _ = c := by ring

end Uniqueness

end Utility
