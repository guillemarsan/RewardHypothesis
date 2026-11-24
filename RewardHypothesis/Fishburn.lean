/-
Copyright (c) 2026 Guillermo Martín-Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guillermo Martín-Sánchez
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Data.Rat.Encodable
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Ordinal representation theorem

Define a preference relation on a set and the axioms for ordinal representation.
Then, state and prove the ordinal theorem: ordinal representation and order separability
on the quotient are equivalent to the existence of an ordinal consistent function.
-/

namespace OrdinalRep

variable {α : Type*}

section Preferences

/-! ## Preference relations -/

/-! ### Definitions relating to ≽ -/

/-- Preference relation ≽ on a set: `x ≽[r] y := r x y`. -/
def Relation (α : Type*) := α → α → Prop
notation lhs " ≽[" r "] " rhs:50 => r lhs rhs

/-- Strict preference (x ≻ y ⇔ x ≽ y ∧ y ⋡ x): `x ≻[r] y := x ≽[r] y ∧ ¬(y ≽[r] x)`. -/
def Strict (r : Relation α) : Relation α :=
  fun x y ↦ (x ≽[r] y) ∧ ¬(y ≽[r] x)
notation lhs " ≻[" r "] " rhs:50 => Strict r lhs rhs

/-- Indifference (x ∼ y ⇔ x ≽ y ∧ y ≽ x): `x ∼[r] y := x ≽[r] y ∧ y ≽[r] x`. -/
def Indiff (r : Relation α) : Relation α :=
  fun x y ↦ (x ≽[r] y) ∧ (y ≽[r] x)
notation lhs " ∼[" r "] " rhs:50 => Indiff r lhs rhs

/-- Indifference of a strict preference (x ∼ y ⇔ x ⊁ y ∧ y ⊁ x):
`x ∼ₛ[r] y := ¬(x ≽[r] y) ∧ ¬(y ≽[r] x)`. -/
def IndiffStrict (r : Relation α) : Relation α :=
  fun x y ↦ ¬(x ≽[r] y) ∧ ¬(y ≽[r] x)
notation lhs " ∼ₛ[" r "] " rhs:50 => IndiffStrict r lhs rhs

/-- ∼ is symmetric (x ∼ y ⇒ y ∼ x): `x ∼[r] y → y ∼[r] x`. -/
lemma indiff_symm (r : Relation α) :
    ∀ x y : α, (x ∼[r] y) → (y ∼[r] x) := by
  intro x y hxy
  exact ⟨hxy.right, hxy.left⟩

/-! ### Representing ≽ by a function -/

/-- u ordinal consistent with ≽ (x ≽ y ⇔ u(x) ≥ u(y)): `x ≽[r] y ↔ u x ≥ u y`. -/
def OrdinalConsistent (u : α → ℝ) (r : Relation α) : Prop :=
  ∀ x y : α, (x ≽[r] y) ↔ (u x ≥ u y)

/-- u strictly ordinal consistent with ≻ (x ≻ y ⇔ u(x) > u(y)): `x ≽[rs] y ↔ u x > u y`. -/
def OrdinalConsistentStrict (u : α → ℝ) (rs : Relation α) : Prop :=
  ∀ x y : α, (x ≽[rs] y) ↔ (u x > u y)

/-! ### Ordinal axioms -/

/-- Completeness (x ≽ y ∨ y ≽ x): `x ≽[r] y ∨ y ≽[r] x`. -/
def Completeness (r : Relation α) : Prop :=
  ∀ x y : α, x ≽[r] y ∨ y ≽[r] x

/-- Transitivity (x ≽ y ∧ y ≽ z ⇒ x ≽ z): `x ≽[r] y ∧ y ≽[r] z → x ≽[r] z`. -/
def Transitivity (r : Relation α) : Prop :=
  ∀ x y z : α, (x ≽[r] y ∧ y ≽[r] z) → x ≽[r] z

/-- Ordinal (≽ complete ∧ transitive): `Completeness r ∧ Transitivity r`. -/
def Ordinal (r : Relation α) : Prop :=
  Completeness r ∧ Transitivity r

/-! ### Lemmas from the ordinal axioms -/

/-- ≽ transitive ⇒ ∼ transitive (x ∼ y ∧ y ∼ z ⇒ x ∼ z):
`Transitivity r → (x ∼[r] y ∧ y ∼[r] z → x ∼[r] z)`. -/
lemma indiff_transitivity (r : Relation α) :
    Transitivity r → ∀ x y z : α, (x ∼[r] y ∧ y ∼[r] z) → (x ∼[r] z) := by
  intro htrans x y z hxyz
  rcases hxyz with ⟨hxiy, hyiz⟩
  exact ⟨htrans x y z ⟨hxiy.left, hyiz.left⟩, htrans z y x ⟨hyiz.right, hxiy.right⟩⟩

/-- ≽ ordinal ⇒ x, y, z have an upper bound w (w ≽ x ∧ w ≽ y ∧ w ≽ z):
`Ordinal r → ∃ w, w ≽[r] x ∧ w ≽[r] y ∧ w ≽[r] z`. -/
lemma highest_element (r : Relation α) :
    Ordinal r → ∀ x y z : α, ∃ w : α, w ≽[r] x ∧ w ≽[r] y ∧ w ≽[r] z := by
  intro hord
  rcases hord with ⟨hcompl, _⟩
  intro x y z
  have hcxy := hcompl x y
  have hcxz := hcompl x z
  have hcyz := hcompl y z
  have hlargest : (x ≽[r] y ∧ x ≽[r] z) ∨
      (y ≽[r] x ∧ y ≽[r] z) ∨ (z ≽[r] x ∧ z ≽[r] y) := by
    cases hcxy <;> cases hcxz <;> cases hcyz <;> aesop
  cases hlargest with
  | inl hx =>
    exact ⟨x, (hcompl x x).elim id id, hx⟩
  | inr hrest =>
    cases hrest with
    | inl hy =>
      exact ⟨y, hy.left, (hcompl y y).elim id id, hy.right⟩
    | inr hz =>
      exact ⟨z, hz.left, hz.right, (hcompl z z).elim id id⟩

/-- ≽ ordinal ⇒ x, y, z have a lower bound w (x ≽ w ∧ y ≽ w ∧ z ≽ w):
`Ordinal r → ∃ w, x ≽[r] w ∧ y ≽[r] w ∧ z ≽[r] w`. -/
lemma lowest_element (r : Relation α) :
    Ordinal r → ∀ x y z : α, ∃ w : α, x ≽[r] w ∧ y ≽[r] w ∧ z ≽[r] w := by
  intro hord
  rcases hord with ⟨hcompl, _⟩
  intro x y z
  have hcxy := hcompl x y
  have hcxz := hcompl x z
  have hcyz := hcompl y z
  have hsmallest : (y ≽[r] x ∧ z ≽[r] x) ∨
      (x ≽[r] y ∧ z ≽[r] y) ∨ (x ≽[r] z ∧ y ≽[r] z) := by
    cases hcxy <;> cases hcxz <;> cases hcyz <;> aesop
  cases hsmallest with
  | inl hx =>
    exact ⟨x, (hcompl x x).elim id id, hx⟩
  | inr hrest =>
    cases hrest with
    | inl hy =>
      exact ⟨y, hy.left, (hcompl y y).elim id id, hy.right⟩
    | inr hz =>
      exact ⟨z, hz.left, hz.right, (hcompl z z).elim id id⟩

end Preferences

section StrictPreferences

/-! ## Strict preferences -/

/-! ### Axioms for ≻ -/

/-- Asymmetry (x ≻ y ⇒ y ⊁ x): `x ≽[rs] y → ¬(y ≽[rs] x)`. -/
def Asymmetry (rs : Relation α) : Prop :=
  ∀ x y : α, (x ≽[rs] y) → ¬(y ≽[rs] x)

/-- Negative transitivity (x ⊁ y ∧ y ⊁ z ⇒ x ⊁ z):
`¬(x ≽[rs] y) ∧ ¬(y ≽[rs] z) → ¬(x ≽[rs] z)`. -/
def NegativeTransitivity (rs : Relation α) : Prop :=
  ∀ x y z : α, ¬(x ≽[rs] y) ∧ ¬(y ≽[rs] z) → ¬(x ≽[rs] z)

/-- Weak order (≻ asymmetric ∧ negatively transitive):
`Asymmetry rs ∧ NegativeTransitivity rs`. -/
def WeakOrder (rs : Relation α) : Prop :=
  Asymmetry rs ∧ NegativeTransitivity rs

/-! ### Relating ≽ and ≻ (used for the ordinal theorem) -/

/-- ≽ ordinal ⇒ (x ∼ y ⇔ x ⊁ y ∧ y ⊁ x):
`Ordinal r → (x ∼[r] y ↔ x ∼ₛ[Strict r] y)`. -/
lemma indiff_iff_indiffStrict {r : Relation α} :
    Ordinal r → ∀ x y : α, (x ∼[r] y) ↔ (x ∼ₛ[Strict r] y) := by
  intro hord x y
  constructor
  · -- ===== Forward direction: x ∼[r] y → x ∼ₛ[strict r] y =====
    intro hxiy
    rcases hxiy with ⟨hxy, hyx⟩
    constructor
    · -- ¬(x ≽[strict r] y)
      intro hxsy
      rcases hxsy with ⟨_, hnyx⟩
      exact hnyx hyx
    · -- ¬(y ≽[strict r] x)
      intro hysx
      rcases hysx with ⟨_, hnxy⟩
      exact hnxy hxy
  · -- ===== Backward direction: x ∼ₛ[strict r] y → x ∼[r] y =====
    intro hxisy
    rcases hxisy with ⟨hnxsy, hnysx⟩
    constructor
    · -- x ≽[r] y
      by_contra hnxy
      have hyx := Or.resolve_left (hord.left x y) hnxy
      exact hnysx ⟨hyx, hnxy⟩
    · -- y ≽[r] x
      by_contra hnyx
      have hxy := Or.resolve_right (hord.left x y) hnyx
      exact hnxsy ⟨hxy, hnyx⟩

/-- ≽ ordinal ⇒ ≻ weak order: `Ordinal r → WeakOrder (Strict r)`. -/
lemma weakOrder_of_ordinal {r : Relation α} :
    Ordinal r → WeakOrder (Strict r) := by
  intro hord
  -- Show that rs is a weak order from r being ordinal
  have hcompl := hord.left
  have htrans := hord.right
  have hwo : WeakOrder (Strict r) := by
    constructor
    · -- ===== Asymmetry =====
      intro x y hxsy hysx
      exact hysx.right hxsy.left
    · -- ===== Negative transitivity =====
      -- We get y ≽ x and z ≽ y from the negations
      intro x y z hn hxsz
      rcases hn with ⟨hnxsy, hnysz⟩
      have hyx : y ≽[r] x := by
        rcases not_and_or.mp hnxsy with hnxy | hnnyx
        · exact Or.resolve_left (hcompl x y) hnxy
        · exact not_not.mp hnnyx
      have hzy : z ≽[r] y := by
        rcases not_and_or.mp hnysz with hnyz | hnnzy
        · exact Or.resolve_left (hcompl y z) hnyz
        · exact not_not.mp hnnzy
      -- Apply transitivity to get z ≽ x and contradiction with x > z
      exact hxsz.right (htrans z y x ⟨hzy, hyx⟩)
  exact hwo

/-- ≽ complete ⇒ (≽ ordinal ⇔ ≻ weak order):
`Completeness r → (Ordinal r ↔ WeakOrder (Strict r))`. -/
lemma ordinal_iff_weakOrder_of_completeness {r : Relation α} :
    Completeness r → (Ordinal r ↔ WeakOrder (Strict r)) := by
  intro hcompl
  constructor
  · -- ===== Forward direction: Ordinal r → WeakOrder (Strict r) =====
    -- Always true, without completeness
    intro hord
    exact weakOrder_of_ordinal hord
  · -- ===== Backward direction: WeakOrder (Strict r) → Ordinal r =====
    intro hwo
    rcases hwo with ⟨_, hnegtrans⟩
    constructor
    · -- ===== Completeness =====
      exact hcompl
    · -- ===== Transitivity =====
      intro x y z hxyz
      rcases hxyz with ⟨hxy, hyz⟩
      have hnzsx : ¬(z ≻[r] x) := by
        have hnysx : ¬(y ≻[r] x) := by
          intro hysx
          exact hysx.right hxy
        have hnzsy : ¬(z ≻[r] y) := by
          intro hzsy
          exact hzsy.right hyz
        exact hnegtrans z y x ⟨hnzsy, hnysx⟩
      cases not_and_or.mp hnzsx with
      | inl hnzx => exact Or.resolve_left (hcompl z x) hnzx
      | inr hnnxz => exact not_not.mp hnnxz

/-- f consistent with ≽ ⇒ f strictly consistent with ≻:
`OrdinalConsistent f r → OrdinalConsistentStrict f (Strict r)`. -/
lemma ordinalConsistentStrict_of_ordinalConsistent {r : Relation α} {f : α → ℝ} :
    OrdinalConsistent f r → OrdinalConsistentStrict f (Strict r) := by
  intro hoc x y
  constructor
  · -- ===== x ≻[r] y → f x > f y =====
    intro hxsy
    have hnfyx : ¬(f y ≥ f x) := by
      intro hfyx
      have hyx : y ≽[r] x := (hoc y x).mpr hfyx
      exact hxsy.right hyx
    exact lt_of_not_ge hnfyx
  · -- ===== f x > f y → x ≻[r] y =====
    intro hfxsy
    have hnyx : ¬(y ≽[r] x) := by
      intro hyx
      have hfyx := (hoc y x).mp hyx
      exact not_lt.mpr hfyx hfxsy
    have hxy : x ≽[r] y := (hoc x y).mpr (le_of_lt hfxsy)
    exact ⟨hxy, hnyx⟩

/-- ≽ complete ⇒ (f consistent with ≽ ⇔ f strictly consistent with ≻):
`Completeness r → (OrdinalConsistent f r ↔ OrdinalConsistentStrict f (Strict r))`. -/
lemma ordinalConsistent_iff_ordinalConsistentStrict_of_completeness {r : Relation α} {f : α → ℝ} :
    Completeness r → (OrdinalConsistent f r ↔ OrdinalConsistentStrict f (Strict r)) := by
  intro hcompl
  constructor
  · -- ===== Forward direction =====
    -- OrdinalConsistent f r → OrdinalConsistentStrict f (Strict r)
    -- Always true, without completeness
    intro hoc
    exact ordinalConsistentStrict_of_ordinalConsistent hoc
  · -- ===== Backward direction =====
    -- OrdinalConsistentStrict f (Strict r) → OrdinalConsistent f r
    intro hocs x y
    constructor
    · -- ===== x ≽[r] y → f x ≥ f y =====
      intro hxy
      have hnysx : ¬(y ≻[r] x) := by
        intro hysx
        exact hysx.right hxy
      have hnfysx : ¬(f y > f x) := by
        intro hfysx
        exact hnysx ((hocs y x).mpr hfysx)
      exact le_of_not_gt hnfysx
    · -- ===== f x ≥ f y → x ≽[r] y =====
      intro hfxy
      have hnysx : ¬(y ≻[r] x) := by
        intro hysx
        have hfysx := (hocs y x).mp hysx
        exact not_le.mpr hfysx hfxy
      cases not_and_or.mp hnysx with
      | inl hnyx => exact Or.resolve_right (hcompl x y) hnyx
      | inr hnnxy => exact not_not.mp hnnxy

end StrictPreferences

section Quotient

/-! ## The quotient X/∼ -/

/-! ### Quotient, relation and lifted function -/

/-- Quotient X/∼ by indifference (X/∼ = {[x] : x ∈ X}, [x] = {y ∈ X : y ∼ x}):
`IndiffQuot rs := Quot (fun x y ↦ x ∼ₛ[rs] y)`. -/
def IndiffQuot (rs : Relation α) : Type _ :=
  Quot (fun x y ↦ x ∼ₛ[rs] y)

/-- Relation on the quotient ([x] ≻ [y] ⇔ x ≻ y):
`Quot.mk _ x ≽[IndiffQuotRel rs h] Quot.mk _ y ↔ x ≽[rs] y`. -/
def IndiffQuotRel (rs : Relation α) (h : WeakOrder rs) :
    IndiffQuot rs → IndiffQuot rs → Prop :=
  Quot.lift₂ (r := fun x y ↦ x ∼ₛ[rs] y) (s := fun x y ↦ x ∼ₛ[rs] y) (fun x y ↦ x ≽[rs] y)
    (by
      intro a b₁ b₂ hb₁isb₂
      rcases hb₁isb₂ with ⟨hnb₁sb₂, hnb₂sb₁⟩
      apply propext
      constructor
      · -- a ≽[rs] b₁ → a ≽[rs] b₂
        intro hasb₁
        by_contra hnasb₂
        have hnasb₁ := h.right a b₂ b₁ ⟨hnasb₂, hnb₂sb₁⟩
        exact hnasb₁ hasb₁
      · -- a ≽[rs] b₂ → a ≽[rs] b₁
        intro hasb₂
        by_contra hnasb₁
        have hnasb₂ := h.right a b₁ b₂ ⟨hnasb₁, hnb₁sb₂⟩
        exact hnasb₂ hasb₂)
    (by
      intro a₁ a₂ b ha₁isa₂
      rcases ha₁isa₂ with ⟨hna₁sa₂, hna₂sa₁⟩
      apply propext
      constructor
      · -- a₁ ≽[rs] b → a₂ ≽[rs] b
        intro ha₁sb
        by_contra hna₂sb
        have hna₁sb := h.right a₁ a₂ b ⟨hna₁sa₂, hna₂sb⟩
        exact hna₁sb ha₁sb
      · -- a₂ ≽[rs] b → a₁ ≽[rs] b
        intro ha₂sb
        by_contra hna₁sb
        have hna₂sb := h.right a₂ a₁ b ⟨hna₂sa₁, hna₁sb⟩
        exact hna₂sb ha₂sb)

/-- Function induced on X/∼ by f strictly consistent with ≻ (f̄([x]) = f(x)):
`liftQuot f hocs (Quot.mk _ x) = f x`. -/
def liftQuot {rs : Relation α} (f : α → ℝ)
    (hocs : OrdinalConsistentStrict f rs) : IndiffQuot rs → ℝ :=
  Quot.lift (r := fun x y ↦ x ∼ₛ[rs] y) f
    (by
      -- a ∼ₛ[rs] b → f a = f b
      intro a b haisb
      rcases haisb with ⟨hnasb, hnbsa⟩
      have hfaeb : f a = f b := by
        have hfab : f a ≥ f b := by
          by_contra hnfab
          have hfasb := lt_of_not_ge hnfab
          exact hnbsa ((hocs b a).mpr hfasb)
        have hfba : f b ≥ f a := by
          by_contra hnfba
          have hfbsa := lt_of_not_ge hnfba
          exact hnasb ((hocs a b).mpr hfbsa)
        exact le_antisymm hfba hfab
      exact hfaeb)

/-! ### Order separability -/

/-- D order dense (x ≻ y ∧ x, y ∉ D ⇒ ∃ z ∈ D, x ≻ z ≻ y):
`(x ≽[rs] y) ∧ x ∉ D ∧ y ∉ D → ∃ z ∈ D, (x ≽[rs] z ∧ z ≽[rs] y)`. -/
def OrderDense (D : Set α) (rs : Relation α) : Prop :=
  ∀ x y : α, (x ≽[rs] y) ∧ x ∉ D ∧ y ∉ D → ∃ z ∈ D, (x ≽[rs] z ∧ z ≽[rs] y)

/-- Order separable (∃ D countable ∧ order dense): `∃ D : Set α, Countable D ∧ OrderDense D rs`. -/
def OrderSeparable (rs : Relation α) : Prop :=
  ∃ D : Set α, Countable D ∧ OrderDense D rs

end Quotient

section Fishburn

/-! ## Fishburn's theorem -/

/-! ### Lemmas -/

/-! #### Lemmas on the quotient -/

/-- Two distinct elements of the quotient are strictly comparable (p ≠ q ⇒ p ≻ q ∨ q ≻ p):
`p ≠ q → (p ≽[IndiffQuotRel rs h] q) ∨ (q ≽[IndiffQuotRel rs h] p)`. -/
lemma indiffQuotRel_total {rs : Relation α} (h : WeakOrder rs) :
    ∀ p q : IndiffQuot rs, p ≠ q →
    (p ≽[IndiffQuotRel rs h] q) ∨ (q ≽[IndiffQuotRel rs h] p) := by
  intro p q
  refine Quot.induction_on₂ p q ?_
  intro x y hxney
  by_contra hn
  rcases not_or.mp hn with ⟨hnxsy, hnysx⟩
  exact hxney (Quot.sound ⟨hnxsy, hnysx⟩)

/-- The strict order on the quotient is transitive (p ≻ q ∧ q ≻ r ⇒ p ≻ r):
`p ≽[IndiffQuotRel rs h] q → q ≽[IndiffQuotRel rs h] r → p ≽[IndiffQuotRel rs h] r`. -/
lemma indiffQuotRel_trans {rs : Relation α} (h : WeakOrder rs) :
    ∀ p q r : IndiffQuot rs, p ≽[IndiffQuotRel rs h] q → q ≽[IndiffQuotRel rs h] r →
    p ≽[IndiffQuotRel rs h] r := by
  intro p q r
  refine Quot.induction_on₃ p q r ?_
  intro x y z hxsy hysz
  by_contra hnxsz
  exact h.right y x z ⟨h.left x y hxsy, hnxsz⟩ hysz

/-- The relation on the quotient is again a weak order (≻ weak order ⇒ ≻ on X/∼ weak order):
`WeakOrder (IndiffQuotRel rs h)`. -/
lemma indiffQuotRel_weakOrder {rs : Relation α} (h : WeakOrder rs) :
    WeakOrder (IndiffQuotRel rs h) := by
  constructor
  · -- ===== Asymmetry =====
    intro p q
    refine Quot.induction_on₂ p q ?_
    intro x y hxsy
    exact h.left x y hxsy
  · -- ===== Negative transitivity =====
    intro p q r
    refine Quot.induction_on₃ p q r ?_
    intro x y z hn
    exact h.right x y z hn

/-! #### Lemmas on the lifted function -/

/-- The lifted function strictly represents the relation on the quotient
([x] ≻ [y] ⇔ f̄([x]) > f̄([y])):
`OrdinalConsistentStrict (liftQuot f hocs) (IndiffQuotRel rs hwo)`. -/
lemma liftQuot_ordinalConsistentStrict {rs : Relation α} {f : α → ℝ}
    (hocs : OrdinalConsistentStrict f rs) (hwo : WeakOrder rs) :
    OrdinalConsistentStrict (liftQuot f hocs) (IndiffQuotRel rs hwo) := by
  let rq := IndiffQuotRel rs hwo
  let fq := liftQuot f hocs
  change ∀ (a b : IndiffQuot rs), (a ≽[rq] b) ↔ (fq a > fq b)
  intro a b
  constructor
  · -- ===== Forward direction: a ≽[rq] b → fq a > fq b =====
    refine Quot.induction_on₂ a b ?_
    intro x y hasb
    have hxsy : x ≽[rs] y := by
      simp only [rq, IndiffQuotRel] at hasb
      exact hasb
    have hfxsy : f x > f y := (hocs x y).mp hxsy
    exact hfxsy
  · -- ===== Backward direction: fq a > fq b → a ≽[rq] b =====
    refine Quot.induction_on₂ a b ?_
    intro x y hfasb
    have hfxsy : f x > f y := hfasb
    have hxsy : x ≽[rs] y := (hocs x y).mpr hfxsy
    simp only [rq, IndiffQuotRel]
    exact hxsy

/-- Two classes are equal ⇔ the lifted function takes the same value on them
([x] = [y] ⇔ f̄([x]) = f̄([y])):
`(a = b) ↔ (liftQuot f hocs a = liftQuot f hocs b)`. -/
lemma liftQuot_eq_iff {rs : Relation α} {f : α → ℝ}
    (hocs : OrdinalConsistentStrict f rs) (hwo : WeakOrder rs) :
    ∀ (a b : IndiffQuot rs), (a = b) ↔ (liftQuot f hocs a = liftQuot f hocs b) := by
  let rq := IndiffQuotRel rs hwo
  let fq := liftQuot f hocs
  have hocsq : ∀ (a b : IndiffQuot rs), (a ≽[rq] b) ↔ (fq a > fq b) :=
    liftQuot_ordinalConsistentStrict hocs hwo
  intro a b
  constructor
  · -- ===== Forward direction: a = b → fq a = fq b =====
    intro haeb
    rw [haeb]
  · -- ===== Backward direction: fq a = fq b → a = b =====
    intro hfaeb
    have hnfasb : ¬(fq a > fq b) := by
      have hor₁ : (fq b = fq a) ∨ (fq a < fq b) := Or.inl hfaeb.symm
      exact not_lt_iff_eq_or_lt.mpr hor₁
    have hnfbsa : ¬(fq b > fq a) := by
      have hor₂ : (fq a = fq b) ∨ (fq b < fq a) := Or.inl hfaeb
      exact not_lt_iff_eq_or_lt.mpr hor₂
    have hnasb : ¬(a ≽[rq] b) := by
      intro hasb
      have hfasb := (hocsq a b).mp hasb
      exact hnfasb hfasb
    have hnbsa : ¬(b ≽[rq] a) := by
      intro hbsa
      have hfbsa := (hocsq b a).mp hbsa
      exact hnfbsa hfbsa
    have haeb : a = b := by
      revert hnasb hnbsa
      refine Quot.induction_on₂ a b ?_
      intro x y hnasb hnbsa
      have hnxsy : ¬(x ≽[rs] y) := by
        intro hxsy
        simp only [rq, IndiffQuotRel] at hnasb
        exact hnasb hxsy
      have hnysx : ¬(y ≽[rs] x) := by
        intro hysx
        simp only [rq, IndiffQuotRel] at hnbsa
        exact hnbsa hysx
      have hxisy : x ∼ₛ[rs] y := ⟨hnxsy, hnysx⟩
      exact Quot.sound hxisy
    exact haeb

/-! #### Interval lemma -/

/-- If a ∈ (l₁, u₁) ∩ (l₂, u₂) and the intervals differ, an endpoint of one interval lies
inside the other:
`(l₁ < l₂ ∧ l₂ < u₁) ∨ (l₁ < u₂ ∧ u₂ < u₁) ∨ (l₂ < l₁ ∧ l₁ < u₂) ∨ (l₂ < u₁ ∧ u₁ < u₂)`. -/
lemma interval_endpoint_inside_of_intersection {a l₁ u₁ l₂ u₂ : ℝ}
    (h₁ : l₁ < a ∧ a < u₁) (h₂ : l₂ < a ∧ a < u₂)
    (hneq : (l₁ = l₂ → u₁ ≠ u₂) ∧ (u₁ = u₂ → l₁ ≠ l₂)) :
    (l₁ < l₂ ∧ l₂ < u₁) ∨ (l₁ < u₂ ∧ u₂ < u₁) ∨ (l₂ < l₁ ∧ l₁ < u₂) ∨ (l₂ < u₁ ∧ u₁ < u₂) := by
  rcases h₁ with ⟨h₁l, h₁u⟩
  rcases h₂ with ⟨h₂l, h₂u⟩
  have hoverlap₁ : l₁ < u₂ := by linarith
  have hoverlap₂ : l₂ < u₁ := by linarith
  -- Split on whether lower endpoints are equal
  by_cases hll : l₁ = l₂
  · -- ===== Lower endpoints equal → upper endpoints differ =====
    have huu : u₁ ≠ u₂ := hneq.1 hll
    have hu : u₂ < u₁ ∨ u₁ < u₂ := lt_or_gt_of_ne huu.symm
    cases hu with
    | inl h =>
      -- u₂ < u₁
      right; left
      exact ⟨hoverlap₁, h⟩
    | inr h =>
      -- u₁ < u₂
      right; right; right
      exact ⟨hoverlap₂, h⟩
  · -- ===== Lower endpoints differ =====
    have hl : l₁ < l₂ ∨ l₂ < l₁ := lt_or_gt_of_ne hll
    cases hl with
    | inl h =>
      -- l₁ < l₂
      left
      exact ⟨h, hoverlap₂⟩
    | inr h =>
      -- l₂ < l₁
      right; right; left
      exact ⟨h, hoverlap₁⟩

/-! #### Countable representation theorem -/

/-- Countable representation theorem (≻ weak order ∧ X/∼ countable ⇒ ∃ f : X → ℝ with
x ≻ y ⇔ f(x) > f(y)):
`WeakOrder rs → Countable (IndiffQuot rs) → ∃ f : α → ℝ, OrdinalConsistentStrict f rs`.

Used in the main Fishburn theorem as a key step to construct the representing function.
Statement from: Fishburn (1970) "Utility Theory for Decision Making" Theorem 2.2.
Proof: non-inductive construction of Voorneveld & Weibull, "An Elementary Proof That
Well-Behaved Utility Functions Exist", pre Theorem 1, which is more natural in Lean than
Fishburn's: the utility of a class is the total weight of the classes below it,
u([x]) = ∑_{[y] ≺ [x]} (1/2)^{n([y])}. -/
theorem countable_representation_theorem (rs : Relation α) :
    WeakOrder rs → Countable (IndiffQuot rs) →
    ∃ f : α → ℝ, OrdinalConsistentStrict f rs := by
  intro hwo hcountable
  -- ===== Weights: enumerate the classes and give class y the weight (1/2)^(n y) =====
  -- Enumerate the quotient: each indifference class gets a distinct natural number
  have henum : ∃ n : IndiffQuot rs → ℕ, Function.Injective n :=
    Countable.exists_injective_nat (IndiffQuot rs)
  rcases henum with ⟨n, hn⟩
  -- Weight of each class: w y = (1/2)^(n y)
  let w : IndiffQuot rs → ℝ := fun y ↦ (1 / 2 : ℝ) ^ n y
  -- Every weight is positive
  have hwpos : ∀ y : IndiffQuot rs, 0 < w y := fun y ↦ pow_pos (by norm_num) (n y)
  -- The weights are summable, since n is injective
  have hwsum : Summable w := summable_geometric_two.comp_injective hn
  -- ===== Utility of a class: the total weight of the classes below it =====
  -- Utility of a class q: the total weight of the classes strictly below q
  -- u q = ∑ w y over all y strictly below q
  let uq : IndiffQuot rs → ℝ := fun q ↦
    ∑' y : IndiffQuot rs, Set.indicator {y | q ≽[IndiffQuotRel rs hwo] y} w y
  -- ===== p ≻ q ⇒ uq p > uq q =====
  -- If p ≻ q then uq p > uq q: p has everything below q, plus q itself
  have huqgt : ∀ p q : IndiffQuot rs,
      p ≽[IndiffQuotRel rs hwo] q → uq p > uq q := by
    intro p q hpsq
    -- Everything below q is below p, by transitivity
    have hsub : ∀ y : IndiffQuot rs, y ∈ {y | q ≽[IndiffQuotRel rs hwo] y} →
        y ∈ {y | p ≽[IndiffQuotRel rs hwo] y} :=
      fun y hqsy ↦ indiffQuotRel_trans hwo p q y hpsq hqsy
    -- q itself is not below q, by asymmetry
    have hnqsq : q ∉ {y | q ≽[IndiffQuotRel rs hwo] y} := by
      refine Quot.induction_on q ?_
      intro x hxsx
      exact hwo.left x x hxsx hxsx
    -- Termwise ≤, and strictly < at the term q
    refine Summable.tsum_lt_tsum (i := q) (fun y ↦ ?_) ?_
      (hwsum.indicator _) (hwsum.indicator _)
    · -- Termwise ≤
      by_cases hy : y ∈ {y | q ≽[IndiffQuotRel rs hwo] y}
      · -- y below q: the same weight on both sides
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hsub y hy)]
      · -- y not below q: 0 on the left
        rw [Set.indicator_of_notMem hy]
        unfold Set.indicator
        split_ifs
        exacts [(hwpos y).le, le_rfl]
    · -- Strictly < at the term q
      -- q is below p, so its weight counts for p but not for q
      have hpsq' : q ∈ {y | p ≽[IndiffQuotRel rs hwo] y} := hpsq
      rw [Set.indicator_of_notMem hnqsq, Set.indicator_of_mem hpsq']
      exact hwpos q
  -- ===== ¬(p ≻ q) ⇒ uq p ≤ uq q =====
  -- If not p ≻ q then uq p ≤ uq q: everything below p is below q
  have huqle : ∀ p q : IndiffQuot rs,
      ¬(p ≽[IndiffQuotRel rs hwo] q) → uq p ≤ uq q := by
    intro p q hnpsq
    -- Everything below p is below q, by negative transitivity
    have hsub : ∀ y : IndiffQuot rs, y ∈ {y | p ≽[IndiffQuotRel rs hwo] y} →
        y ∈ {y | q ≽[IndiffQuotRel rs hwo] y} := by
      intro y hpsy
      by_contra hnqsy
      revert hnpsq hpsy hnqsy
      refine Quot.induction_on₃ p q y ?_
      intro a b c hnasb hasc hnbsc
      exact hwo.right a b c ⟨hnasb, hnbsc⟩ hasc
    -- So the sum for p is termwise ≤ the sum for q
    refine Summable.tsum_le_tsum (fun y ↦ ?_) (hwsum.indicator _) (hwsum.indicator _)
    by_cases hy : y ∈ {y | p ≽[IndiffQuotRel rs hwo] y}
    · -- y below p: the same weight on both sides
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hsub y hy)]
    · -- y not below p: 0 on the left
      rw [Set.indicator_of_notMem hy]
      unfold Set.indicator
      split_ifs
      exacts [(hwpos y).le, le_rfl]
  -- ===== Lift uq to α and conclude =====
  -- The representing function: the utility of an element is that of its class
  refine ⟨fun x ↦ uq (Quot.mk _ x), ?_⟩
  intro x y
  constructor
  · -- ===== Forward direction: x ≻ y → f x > f y =====
    intro hxsy
    exact huqgt (Quot.mk _ x) (Quot.mk _ y) hxsy
  · -- ===== Backward direction: f x > f y → x ≻ y =====
    intro hfxsy
    by_contra hnxsy
    exact not_le.mpr hfxsy (huqle (Quot.mk _ x) (Quot.mk _ y) hnxsy)

/-! ### Proof -/

/-! #### Forward direction -/

/-- Fishburn's theorem, forward direction (≻ weak order ∧ X/∼ order separable ⇒
∃ f : X → ℝ with x ≻ y ⇔ f(x) > f(y)):
`OrderSeparable (IndiffQuotRel rs hwo) → ∃ f : α → ℝ, OrdinalConsistentStrict f rs`. -/
lemma exists_ordinalConsistentStrict_of_orderSeparable {rs : Relation α}
    (hwo : WeakOrder rs) :
    OrderSeparable (IndiffQuotRel rs hwo) →
    ∃ f : α → ℝ, OrdinalConsistentStrict f rs := by
  intro hsep
  -- ===== Define A = D ∪ {extreme elements} and show it is countable and order dense =====
  let rq := IndiffQuotRel rs hwo
  -- Extract the order dense set from the order separable property
  rcases hsep with ⟨D, hcountable, hdense⟩
  -- Define the set A as the order dense set D with the least and
  -- greatest elements included
  let A := D ∪ {q : IndiffQuot rs | ∀ p : IndiffQuot rs, ¬(p ≽[rq] q)}
    ∪ {q : IndiffQuot rs | ∀ p : IndiffQuot rs, ¬(q ≽[rq] p)}
  -- Show A is countable
  have hcountableA : Countable A := by
    -- D is countable
    have hD : D.Countable := Set.countable_coe_iff.mp hcountable
    -- There is at most one greatest element: two greatest elements are
    -- indifferent, hence equal in the quotient
    have hmax : {q : IndiffQuot rs | ∀ p : IndiffQuot rs, ¬(p ≽[rq] q)}.Subsingleton := by
      intro q₁ hq₁ q₂ hq₂
      revert hq₁ hq₂
      refine Quot.induction_on₂ q₁ q₂ ?_
      intro x y hx hy
      exact Quot.sound ⟨hy (Quot.mk _ x), hx (Quot.mk _ y)⟩
    -- Likewise, there is at most one least element
    have hmin : {q : IndiffQuot rs | ∀ p : IndiffQuot rs, ¬(q ≽[rq] p)}.Subsingleton := by
      intro q₁ hq₁ q₂ hq₂
      revert hq₁ hq₂
      refine Quot.induction_on₂ q₁ q₂ ?_
      intro x y hx hy
      exact Quot.sound ⟨hx (Quot.mk _ y), hy (Quot.mk _ x)⟩
    -- A is a union of three countable sets
    exact Set.countable_coe_iff.mpr ((hD.union hmax.countable).union hmin.countable)
  -- Show A is order dense in the quotient set
  have hdenseA : OrderDense A rq := by
    intro x y h
    rcases h with ⟨hxsy, hnxA, hnyA⟩
    -- x and y are not in D either, since D ⊆ A
    have hnxD : x ∉ D := fun hx ↦ hnxA (Or.inl (Or.inl hx))
    have hnyD : y ∉ D := fun hy ↦ hnyA (Or.inl (Or.inl hy))
    -- So D gives an element z strictly between x and y, and z ∈ D ⊆ A
    rcases hdense x y ⟨hxsy, hnxD, hnyD⟩ with ⟨z, hzD, hxsz, hzsy⟩
    exact ⟨z, Or.inl (Or.inl hzD), hxsz, hzsy⟩
  -- ===== Define B, the elements outside A next to a gap of A, and show it is countable =====
  -- Define above S b as the set of elements in S bigger than b
  let above (S : Set (IndiffQuot rs)) (b : IndiffQuot rs) : Set (IndiffQuot rs) :=
    {q : IndiffQuot rs | q ∈ S ∧ q ≽[rq] b}
  -- Define below S b as the set of elements in S smaller than b
  let below (S : Set (IndiffQuot rs)) (b : IndiffQuot rs) : Set (IndiffQuot rs) :=
    {q : IndiffQuot rs | q ∈ S ∧ b ≽[rq] q}
  -- a is a least element of above S b
  let leastAbove (S : Set (IndiffQuot rs)) (b a : IndiffQuot rs) : Prop :=
    a ∈ above S b ∧ ∀ a' ∈ above S b, ¬(a ≽[rq] a')
  -- c is a greatest element of below S b
  let greatestBelow (S : Set (IndiffQuot rs)) (b c : IndiffQuot rs) : Prop :=
    c ∈ below S b ∧ ∀ c' ∈ below S b, ¬(c' ≽[rq] c)
  -- Define B as the elements outside A such that above A b has a least element
  -- or below A b has a greatest element
  let B : Set (IndiffQuot rs) :=
    {b : IndiffQuot rs | b ∉ A ∧ ((∃ a, leastAbove A b a) ∨ (∃ c, greatestBelow A b c))}
  -- A given a can be the least element of above A b for at most one b ∉ A
  have hleastAboveUniq : ∀ a : IndiffQuot rs,
      {b : IndiffQuot rs | b ∉ A ∧ leastAbove A b a}.Subsingleton := by
    intro a b₁ hb₁ b₂ hb₂
    rcases hb₁ with ⟨hnb₁A, ha₁, hmin₁⟩
    rcases hb₂ with ⟨hnb₂A, ha₂, hmin₂⟩
    by_contra hb₁neb₂
    rcases indiffQuotRel_total hwo b₁ b₂ hb₁neb₂ with hb₁sb₂ | hb₂sb₁
    · -- b₁ ≻ b₂: some z ∈ A lies strictly between, so z ∈ above A b₂ and a ≻ z
      rcases hdenseA b₁ b₂ ⟨hb₁sb₂, hnb₁A, hnb₂A⟩ with ⟨z, hzA, hb₁sz, hzsb₂⟩
      exact hmin₂ z ⟨hzA, hzsb₂⟩ (indiffQuotRel_trans hwo a b₁ z ha₁.2 hb₁sz)
    · -- b₂ ≻ b₁: symmetric
      rcases hdenseA b₂ b₁ ⟨hb₂sb₁, hnb₂A, hnb₁A⟩ with ⟨z, hzA, hb₂sz, hzsb₁⟩
      exact hmin₁ z ⟨hzA, hzsb₁⟩ (indiffQuotRel_trans hwo a b₂ z ha₂.2 hb₂sz)
  -- A given c can be the greatest element of below A b for at most one b ∉ A
  have hgreatestBelowUniq : ∀ c : IndiffQuot rs,
      {b : IndiffQuot rs | b ∉ A ∧ greatestBelow A b c}.Subsingleton := by
    intro c b₁ hb₁ b₂ hb₂
    rcases hb₁ with ⟨hnb₁A, hc₁, hmax₁⟩
    rcases hb₂ with ⟨hnb₂A, hc₂, hmax₂⟩
    by_contra hb₁neb₂
    rcases indiffQuotRel_total hwo b₁ b₂ hb₁neb₂ with hb₁sb₂ | hb₂sb₁
    · -- b₁ ≻ b₂: some z ∈ A lies strictly between, so z ∈ below A b₁ and z ≻ c
      rcases hdenseA b₁ b₂ ⟨hb₁sb₂, hnb₁A, hnb₂A⟩ with ⟨z, hzA, hb₁sz, hzsb₂⟩
      exact hmax₁ z ⟨hzA, hb₁sz⟩ (indiffQuotRel_trans hwo z b₂ c hzsb₂ hc₂.2)
    · -- b₂ ≻ b₁: symmetric
      rcases hdenseA b₂ b₁ ⟨hb₂sb₁, hnb₂A, hnb₁A⟩ with ⟨z, hzA, hb₂sz, hzsb₁⟩
      exact hmax₂ z ⟨hzA, hb₂sz⟩ (indiffQuotRel_trans hwo z b₁ c hzsb₁ hc₁.2)
  -- B is countable: each part injects into the countable set A
  have hcountableB : Countable B := by
    have hA : A.Countable := Set.countable_coe_iff.mp hcountableA
    -- b's whose above A b has a least element: at most one b for each a ∈ A
    have hB₁ : (⋃ a ∈ A, {b : IndiffQuot rs | b ∉ A ∧ leastAbove A b a}).Countable :=
      hA.biUnion fun a _ ↦ (hleastAboveUniq a).countable
    -- b's whose below A b has a greatest element: at most one b for each c ∈ A
    have hB₂ : (⋃ c ∈ A, {b : IndiffQuot rs | b ∉ A ∧ greatestBelow A b c}).Countable :=
      hA.biUnion fun c _ ↦ (hgreatestBelowUniq c).countable
    -- B is contained in the union of both
    have hBsub : B ⊆ (⋃ a ∈ A, {b : IndiffQuot rs | b ∉ A ∧ leastAbove A b a}) ∪
        (⋃ c ∈ A, {b : IndiffQuot rs | b ∉ A ∧ greatestBelow A b c}) := by
      intro b hb
      rcases hb with ⟨hnbA, ⟨a, ha⟩ | ⟨c, hc⟩⟩
      · -- above A b has least element a ∈ A
        exact Or.inl (Set.mem_biUnion ha.1.1 ⟨hnbA, ha⟩)
      · -- below A b has greatest element c ∈ A
        exact Or.inr (Set.mem_biUnion hc.1.1 ⟨hnbA, hc⟩)
    exact Set.countable_coe_iff.mpr ((hB₁.union hB₂).mono hBsub)
  -- ===== C = A ∪ B is countable and has no gaps next to the elements outside it =====
  -- Define C as A ∪ B, which is countable as a union of countable sets
  let C : Set (IndiffQuot rs) := A ∪ B
  have hcountableC : Countable C :=
    Set.countable_coe_iff.mpr ((Set.countable_coe_iff.mp hcountableA).union
      (Set.countable_coe_iff.mp hcountableB))
  -- (1) For b ∉ C, above C b has no least element
  have hnoLeastAbove : ∀ b : IndiffQuot rs, b ∉ C → ¬∃ a, leastAbove C b a := by
    intro b hnbC hex
    rcases hex with ⟨a, ⟨haC, hasb⟩, hmin⟩
    -- b ∉ A, since A ⊆ C
    have hnbA : b ∉ A := fun hb ↦ hnbC (Or.inl hb)
    -- a ∉ A: otherwise a is also least in above A b, so b ∈ B ⊆ C
    have hnaA : a ∉ A := by
      intro haA
      apply hnbC
      exact Or.inr ⟨hnbA, Or.inl ⟨a, ⟨haA, hasb⟩, fun a' ha' ↦ hmin a' ⟨Or.inl ha'.1, ha'.2⟩⟩⟩
    -- By order denseness, some z ∈ A ⊆ C lies strictly between a and b,
    -- so z ∈ above C b and a ≻ z, contradicting that a is least
    rcases hdenseA a b ⟨hasb, hnaA, hnbA⟩ with ⟨z, hzA, hasz, hzsb⟩
    exact hmin z ⟨Or.inl hzA, hzsb⟩ hasz
  -- (2) For b ∉ C, below C b has no greatest element
  have hnoGreatestBelow : ∀ b : IndiffQuot rs, b ∉ C → ¬∃ c, greatestBelow C b c := by
    intro b hnbC hex
    rcases hex with ⟨c, ⟨hcC, hbsc⟩, hmax⟩
    -- b ∉ A, since A ⊆ C
    have hnbA : b ∉ A := fun hb ↦ hnbC (Or.inl hb)
    -- c ∉ A: otherwise c is also greatest in below A b, so b ∈ B ⊆ C
    have hncA : c ∉ A := by
      intro hcA
      apply hnbC
      exact Or.inr ⟨hnbA, Or.inr ⟨c, ⟨hcA, hbsc⟩, fun c' hc' ↦ hmax c' ⟨Or.inl hc'.1, hc'.2⟩⟩⟩
    -- By order denseness, some z ∈ A ⊆ C lies strictly between b and c,
    -- so z ∈ below C b and z ≻ c, contradicting that c is greatest
    rcases hdenseA b c ⟨hbsc, hnbA, hncA⟩ with ⟨z, hzA, hbsz, hzsc⟩
    exact hmax z ⟨Or.inl hzA, hbsz⟩ hzsc
  -- ===== By Theorem 2.2, represent ≻ on C by a function uC =====
  -- The preference restricted to C
  let rC : Relation C := fun a c ↦ a.1 ≽[rq] c.1
  -- rC is a weak order, since rq is
  have hwoC : WeakOrder rC := by
    have hwoq := indiffQuotRel_weakOrder hwo
    exact ⟨fun a c ↦ hwoq.left a.1 c.1, fun a b c ↦ hwoq.right a.1 b.1 c.1⟩
  -- The quotient of C is countable, since C is
  have hcountableQuotC : Countable (IndiffQuot rC) := by
    have : Countable C := hcountableC
    unfold IndiffQuot
    infer_instance
  -- By Theorem 2.2, there is a utility uC on C representing rC
  rcases countable_representation_theorem rC hwoC hcountableQuotC with ⟨uC, huC⟩
  -- ===== u_b and u^b: the values of uC below and above b =====
  -- u_b: the values of uC on the elements of C below b
  let uBelow (b : IndiffQuot rs) : Set ℝ := {r : ℝ | ∃ c : C, b ≽[rq] c.1 ∧ uC c = r}
  -- u^b: the values of uC on the elements of C above b
  let uAbove (b : IndiffQuot rs) : Set ℝ := {r : ℝ | ∃ a : C, a.1 ≽[rq] b ∧ uC a = r}
  -- For b ∉ C, both sets are nonempty
  have huBelowNonempty : ∀ b : IndiffQuot rs, b ∉ C → (uBelow b).Nonempty := by
    intro b hnbC
    have hnbA : b ∉ A := fun hb ↦ hnbC (Or.inl hb)
    -- b is not a least element, since those are in A; so some p is below b
    have hnmin : ¬∀ p : IndiffQuot rs, ¬(b ≽[rq] p) := fun h ↦ hnbA (Or.inr h)
    rcases not_forall.mp hnmin with ⟨p, hnnbsp⟩
    have hbsp : b ≽[rq] p := not_not.mp hnnbsp
    by_cases hpC : p ∈ C
    · -- p itself is in C
      exact ⟨uC ⟨p, hpC⟩, ⟨p, hpC⟩, hbsp, rfl⟩
    · -- Otherwise, by order denseness some z ∈ A ⊆ C lies between b and p
      have hnpA : p ∉ A := fun h ↦ hpC (Or.inl h)
      rcases hdenseA b p ⟨hbsp, hnbA, hnpA⟩ with ⟨z, hzA, hbsz, _⟩
      exact ⟨uC ⟨z, Or.inl hzA⟩, ⟨z, Or.inl hzA⟩, hbsz, rfl⟩
  have huAboveNonempty : ∀ b : IndiffQuot rs, b ∉ C → (uAbove b).Nonempty := by
    intro b hnbC
    have hnbA : b ∉ A := fun hb ↦ hnbC (Or.inl hb)
    -- b is not a greatest element, since those are in A; so some p is above b
    have hnmax : ¬∀ p : IndiffQuot rs, ¬(p ≽[rq] b) := fun h ↦ hnbA (Or.inl (Or.inr h))
    rcases not_forall.mp hnmax with ⟨p, hnnpsb⟩
    have hpsb : p ≽[rq] b := not_not.mp hnnpsb
    by_cases hpC : p ∈ C
    · -- p itself is in C
      exact ⟨uC ⟨p, hpC⟩, ⟨p, hpC⟩, hpsb, rfl⟩
    · -- Otherwise, by order denseness some z ∈ A ⊆ C lies between p and b
      have hnpA : p ∉ A := fun h ↦ hpC (Or.inl h)
      rcases hdenseA p b ⟨hpsb, hnpA, hnbA⟩ with ⟨z, hzA, _, hzsb⟩
      exact ⟨uC ⟨z, Or.inl hzA⟩, ⟨z, Or.inl hzA⟩, hzsb, rfl⟩
  -- Every value in u_b is smaller than every value in u^b
  have huBelowLtAbove : ∀ b : IndiffQuot rs, ∀ r ∈ uBelow b, ∀ s ∈ uAbove b, r < s := by
    intro b r hr s hs
    rcases hr with ⟨c, hbsc, hcr⟩
    rcases hs with ⟨a, hasb, has⟩
    -- a ≻ b ≻ c, so a ≻ c, and hence uC a > uC c
    have hasc : rC a c := indiffQuotRel_trans hwo a.1 b c.1 hasb hbsc
    rw [← hcr, ← has]
    exact (huC a c).mp hasc
  -- ===== (3.2): extend uC to the whole quotient =====
  -- Membership in C is decided classically
  classical
  let u (q : IndiffQuot rs) : ℝ :=
    if h : q ∈ C then uC ⟨q, h⟩ else (sSup (uBelow q) + sInf (uAbove q)) / 2
  -- From (2): every value in u_b is strictly below sup u_b
  have hltsSup : ∀ b : IndiffQuot rs, b ∉ C → ∀ r ∈ uBelow b, r < sSup (uBelow b) := by
    intro b hnbC r hr
    rcases hr with ⟨c, hbsc, hcr⟩
    -- u_b is bounded above by any value in u^b
    rcases huAboveNonempty b hnbC with ⟨s, hs⟩
    have hbdd : BddAbove (uBelow b) :=
      ⟨s, fun r' hr' ↦ (huBelowLtAbove b r' hr' s hs).le⟩
    -- By (2), c is not greatest in below C b: some c' ∈ below C b has c' ≻ c
    have hc' : ∃ c' ∈ below C b, c' ≽[rq] c.1 := by
      by_contra hn
      exact hnoGreatestBelow b hnbC ⟨c.1, ⟨c.2, hbsc⟩, fun c' hc' hc'sc ↦ hn ⟨c', hc', hc'sc⟩⟩
    rcases hc' with ⟨c', hc'b, hc'sc⟩
    rcases hc'b with ⟨hc'C, hbsc'⟩
    -- So uC c < uC c' ≤ sup u_b
    have hlt : uC c < uC ⟨c', hc'C⟩ := (huC ⟨c', hc'C⟩ c).mp hc'sc
    have hle : uC ⟨c', hc'C⟩ ≤ sSup (uBelow b) := le_csSup hbdd ⟨⟨c', hc'C⟩, hbsc', rfl⟩
    rw [← hcr]
    exact lt_of_lt_of_le hlt hle
  -- From (1): every value in u^b is strictly above inf u^b
  have hsInflt : ∀ b : IndiffQuot rs, b ∉ C → ∀ s ∈ uAbove b, sInf (uAbove b) < s := by
    intro b hnbC s hs
    rcases hs with ⟨a, hasb, has⟩
    -- u^b is bounded below by any value in u_b
    rcases huBelowNonempty b hnbC with ⟨r, hr⟩
    have hbdd : BddBelow (uAbove b) :=
      ⟨r, fun s' hs' ↦ (huBelowLtAbove b r hr s' hs').le⟩
    -- By (1), a is not least in above C b: some a' ∈ above C b has a ≻ a'
    have ha' : ∃ a' ∈ above C b, a.1 ≽[rq] a' := by
      by_contra hn
      exact hnoLeastAbove b hnbC ⟨a.1, ⟨a.2, hasb⟩, fun a' ha' hasa' ↦ hn ⟨a', ha', hasa'⟩⟩
    rcases ha' with ⟨a', ha'b, hasa'⟩
    rcases ha'b with ⟨ha'C, ha'sb⟩
    -- So inf u^b ≤ uC a' < uC a
    have hlt : uC ⟨a', ha'C⟩ < uC a := (huC a ⟨a', ha'C⟩).mp hasa'
    have hle : sInf (uAbove b) ≤ uC ⟨a', ha'C⟩ := csInf_le hbdd ⟨⟨a', ha'C⟩, ha'sb, rfl⟩
    rw [← has]
    exact lt_of_le_of_lt hle hlt
  -- ===== u represents ≻ on the quotient =====
  -- On C, u agrees with uC
  have huOnC : ∀ q : IndiffQuot rs, ∀ hq : q ∈ C, u q = uC ⟨q, hq⟩ :=
    fun q hq ↦ dif_pos hq
  -- For b ∉ C: u(c) < u(b) < u(a) for all values u(c) ∈ u_b and u(a) ∈ u^b
  have hubetween : ∀ b : IndiffQuot rs, b ∉ C →
      (∀ r ∈ uBelow b, r < u b) ∧ (∀ s ∈ uAbove b, u b < s) := by
    intro b hnbC
    have hu : u b = (sSup (uBelow b) + sInf (uAbove b)) / 2 := dif_neg hnbC
    -- sup u_b ≤ inf u^b, since every value below is smaller than every value above
    have hsuple : sSup (uBelow b) ≤ sInf (uAbove b) :=
      csSup_le (huBelowNonempty b hnbC) (fun r hr ↦
        le_csInf (huAboveNonempty b hnbC) (fun s hs ↦ (huBelowLtAbove b r hr s hs).le))
    constructor
    · -- r < sup u_b ≤ u b
      intro r hr
      have hrlt := hltsSup b hnbC r hr
      rw [hu]
      linarith
    · -- u b ≤ inf u^b < s
      intro s hs
      have hsgt := hsInflt b hnbC s hs
      rw [hu]
      linarith
  -- u preserves the strict order: p ≻ q → u p > u q
  have hugt : ∀ p q : IndiffQuot rs, p ≽[rq] q → u p > u q := by
    intro p q hpsq
    by_cases hpC : p ∈ C <;> by_cases hqC : q ∈ C
    · -- p, q ∈ C: u is uC, which represents rC
      rw [huOnC p hpC, huOnC q hqC]
      exact (huC ⟨p, hpC⟩ ⟨q, hqC⟩).mp hpsq
    · -- p ∈ C, q ∉ C: u p is a value in u^q
      rw [huOnC p hpC]
      exact (hubetween q hqC).2 _ ⟨⟨p, hpC⟩, hpsq, rfl⟩
    · -- p ∉ C, q ∈ C: u q is a value in u_p
      rw [huOnC q hqC]
      exact (hubetween p hpC).1 _ ⟨⟨q, hqC⟩, hpsq, rfl⟩
    · -- p, q ∉ C
      -- By order denseness some z ∈ A ⊆ C lies between, so u q < u z < u p
      have hnpA : p ∉ A := fun h ↦ hpC (Or.inl h)
      have hnqA : q ∉ A := fun h ↦ hqC (Or.inl h)
      rcases hdenseA p q ⟨hpsq, hnpA, hnqA⟩ with ⟨z, hzA, hpsz, hzsq⟩
      have huzsq := (hubetween q hqC).2 _ ⟨⟨z, Or.inl hzA⟩, hzsq, rfl⟩
      have hupsz := (hubetween p hpC).1 _ ⟨⟨z, Or.inl hzA⟩, hpsz, rfl⟩
      exact lt_trans huzsq hupsz
  -- u represents the order on the quotient
  have hurep : ∀ p q : IndiffQuot rs, p ≽[rq] q ↔ u p > u q := by
    intro p q
    constructor
    · -- Forward direction: p ≻ q → u p > u q
      exact hugt p q
    · -- Backward direction: u p > u q → p ≻ q, by totality
      intro hupsq
      by_contra hnpsq
      by_cases hpeq : p = q
      · -- p = q: contradicts irreflexivity of <
        rw [hpeq] at hupsq
        exact lt_irrefl _ hupsq
      · -- p ≠ q: p ≻ q or q ≻ p
        rcases indiffQuotRel_total hwo p q hpeq with hpsq | hqsp
        · -- p ≻ q
          exact hnpsq hpsq
        · -- q ≻ p
          exact lt_asymm hupsq (hugt q p hqsp)
  -- ===== (3.1): lift u to α =====
  exact ⟨fun x ↦ u (Quot.mk _ x), fun x y ↦ hurep (Quot.mk _ x) (Quot.mk _ y)⟩

/-! #### Backward direction -/

/-- Fishburn's theorem, backward direction, weak order part
(f strictly consistent with ≻ ⇒ ≻ weak order):
`OrdinalConsistentStrict f rs → WeakOrder rs`. -/
lemma weakOrder_of_ordinalConsistentStrict {rs : Relation α} {f : α → ℝ} :
    OrdinalConsistentStrict f rs → WeakOrder rs := by
  intro hocs
  -- ===== rs is asymmetric =====
  have hasym : Asymmetry rs := by
    intro x y hxsy hysx
    have hfxsy := (hocs x y).mp hxsy
    have hfysx := (hocs y x).mp hysx
    exact not_le.mpr hfysx (le_of_lt hfxsy)
  -- ===== rs is negatively transitive =====
  have hnegtrans : NegativeTransitivity rs := by
    intro x y z hn
    rcases hn with ⟨hnxsy, hnysz⟩
    have hnfxsy : ¬(f x > f y) := by
      intro hfxsy
      exact hnxsy ((hocs x y).mpr hfxsy)
    have hnfysz : ¬(f y > f z) := by
      intro hfysz
      exact hnysz ((hocs y z).mpr hfysz)
    have hnfxsz : ¬(f x > f z) := by
      intro hfxsz
      have hfzy := le_of_not_gt hnfysz
      have hfyx := le_of_not_gt hnfxsy
      exact not_lt.mpr (le_trans hfyx hfzy) hfxsz
    intro hxsz
    exact hnfxsz ((hocs x z).mp hxsz)
  exact ⟨hasym, hnegtrans⟩

/-- Fishburn's theorem, backward direction, order separability part
(f strictly consistent with ≻ ∧ ≻ weak order ⇒ X/∼ order separable):
`OrderSeparable (IndiffQuotRel rs hwo)`. -/
lemma orderSeparable_of_ordinalConsistentStrict {rs : Relation α} {f : α → ℝ}
    (hocs : OrdinalConsistentStrict f rs) (hwo : WeakOrder rs) :
    OrderSeparable (IndiffQuotRel rs hwo) := by
  -- ===== Setup: the quotient, its relation and the lifted function =====
  -- Since it is a weak order, we can define the quotient space
  -- and lift most of the operations to the quotient
  let QuotSet := {q : IndiffQuot rs | True}
  let rq := IndiffQuotRel rs hwo
  let fq := liftQuot f hocs
  have hocsq : ∀ (a b : IndiffQuot rs), (a ≽[rq] b) ↔ (fq a > fq b) :=
    liftQuot_ordinalConsistentStrict hocs hwo
  have hidq : ∀ (a b : IndiffQuot rs), (a = b) ↔ (fq a = fq b) :=
    liftQuot_eq_iff hocs hwo
  -- ===== Define A: one element of the quotient for each rational interval =====
  -- Define a countable set A as one element of the quotient
  -- for each rational interval (a, b)
  -- Set of closed intervals with rational endpoints
  let Cs : Set (Set ℝ) :=
    {C | ∃ (p q : ℚ) (hpq : p < q), C = {x : ℝ | p ≤ x ∧ x ≤ q}}
  -- Subset of intervals that contain at least one image of f
  let Is : Set (Set ℝ) :=
    {I | ∃ (C : Set ℝ) (hc : C ∈ Cs) (x : α), f x ∈ C ∧ I = C}
  -- Set of images per interval
  let pAs : Set (Set (IndiffQuot rs)) :=
    {S | ∃ (I : Set ℝ) (hI : I ∈ Is), S = (Quot.mk _ '' {x : α | f x ∈ I})}
  have hpAsNonempty : ∀ S ∈ pAs, ∃ a, a ∈ S := by
    intro S hS
    rcases hS with ⟨I, hIinIs, rfl⟩
    rcases hIinIs with ⟨C, _, x, hfxinC, hIeC⟩
    have hsetNonempty : ∃ x : α, x ∈ {x : α | f x ∈ I} := by
      rw [← hIeC] at hfxinC
      exact ⟨x, hfxinC⟩
    rcases hsetNonempty with ⟨x0, hx0⟩
    exact ⟨Quot.mk _ x0, ⟨x0, hx0, rfl⟩⟩
  -- Random choice of one element per image set
  let A : Set (IndiffQuot rs) :=
    {a | ∃ (S : Set (IndiffQuot rs)) (hS : S ∈ pAs),
      a = Classical.choose (hpAsNonempty S hS)}
  -- ===== A is countable =====
  -- Show that A is countable by chaining countability results
  have hcountableA : Countable A := by
    -- Show that Cs is countable
    have hcountableCs : Countable Cs := by
      let P := {pq : ℚ × ℚ | pq.1 < pq.2}
      have hcountableP : Countable P := by
        let QxQ := {pq : ℚ × ℚ | True}
        have hcountableQxQ : Countable QxQ := inferInstance
        have hPsub : P ⊆ QxQ := by
          intro pq _
          trivial
        exact Set.Countable.mono hPsub hcountableQxQ
      let fCs : (ℚ × ℚ) → Set ℝ := fun pq ↦ {x : ℝ | pq.1 ≤ x ∧ x ≤ pq.2}
      have h := Set.Countable.image hcountableP fCs
      have hCsimg : Cs = fCs '' P := by
        ext C
        constructor
        · intro hC
          rcases hC with ⟨p, q, hpq, rfl⟩
          have hpqP : (p, q) ∈ P := hpq
          exact ⟨(p, q), hpqP, rfl⟩
        · intro hC
          rcases hC with ⟨⟨p, q⟩, hpq, rfl⟩
          exact ⟨p, q, hpq, rfl⟩
      rw [← hCsimg] at h
      exact h
    -- Show that Is is countable
    have hcountableIs : Countable Is := by
      have hIssub : Is ⊆ Cs := by
        intro I hI
        rcases hI with ⟨C, hCinCs, _, _, hIeC⟩
        rw [hIeC]
        exact hCinCs
      exact Set.Countable.mono hIssub hcountableCs
    -- Show that pAs is countable
    have hcountablepAs : Countable pAs := by
      let fpAs : Set ℝ → Set (IndiffQuot rs) := fun I ↦
        Set.image (Quot.mk _) {x : α | f x ∈ I}
      have h := Set.Countable.image hcountableIs fpAs
      have hpAsimg : pAs = fpAs '' Is := by
        ext S
        constructor
        · intro hS
          rcases hS with ⟨I, hIinIs, rfl⟩
          exact ⟨I, hIinIs, rfl⟩
        · intro hS
          rcases hS with ⟨I, hIinIs, rfl⟩
          exact ⟨I, hIinIs, rfl⟩
      rw [← hpAsimg] at h
      exact h
    -- Finally, show that A is countable
    -- This requires subtypes for the axiom of choice
    let pAsSubtype := {S // S ∈ pAs}
    let pAsSet := {S : {S // S ∈ pAs} | True}
    let fA : pAsSubtype → IndiffQuot rs := fun S ↦
      Classical.choose (hpAsNonempty S.val S.property)
    have hcountablepAsSubtype : Countable pAsSubtype :=
      Set.Countable.to_subtype hcountablepAs
    have hcountablepAsSet : Countable pAsSet :=
      Set.countable_univ_iff.mpr hcountablepAsSubtype
    have h := Set.Countable.image hcountablepAsSet fA
    have hAimg : A = fA '' pAsSet := by
      ext a
      constructor
      · intro ha
        rcases ha with ⟨S, hSinpAs, rfl⟩
        exact ⟨⟨S, hSinpAs⟩, trivial, rfl⟩
      · intro ha
        rcases ha with ⟨⟨S, hSinpAs⟩, _, rfl⟩
        exact ⟨S, hSinpAs, rfl⟩
    rw [← hAimg] at h
    exact h
  -- ===== Define K, the pairs (b, c) outside A with no element of A between them =====
  -- Define K
  let K : Set (IndiffQuot rs × IndiffQuot rs) :=
    {bc | bc.1 ∈ QuotSet \ A ∧ bc.2 ∈ QuotSet \ A
      ∧ bc.2 ≽[rq] bc.1 ∧ ¬∃ a ∈ A, bc.2 ≽[rq] a ∧ a ≽[rq] bc.1}
  -- ===== K is countable =====
  -- Show that K is countable
  have hcountableK : Countable K := by
    -- ===== The intervals (f(b), f(c)) contain no other f(a) =====
    -- Show that intervals are empty of other f(a)
    have hfbcEmpty : ∀ bc ∈ K, ¬∃ a ∈ QuotSet, bc.2 ≽[rq] a ∧ a ≽[rq] bc.1 := by
      intro bc hbc
      rcases hbc with ⟨_, _, _, hnoA⟩
      intro ha
      rcases ha with ⟨a, _, hcsa, hasb⟩
      -- Assume that there is such a, then there is d in A with f(bc.1) < f(d) < f(bc.2)
      -- which leads to contradiction of (b,c) ∈ K
      have hexd : ∃ d ∈ A, bc.2 ≽[rq] d ∧ d ≽[rq] bc.1 := by
        -- f(c) > f(a) > f(b)
        have hfasb : fq a > fq bc.1 := (hocsq a bc.1).mp hasb
        have hfcsa : fq bc.2 > fq a := (hocsq bc.2 a).mp hcsa
        -- Find an interval (p, q) with rational endpoints such that
        -- f(a) ∈ (p, q)
        rcases exists_rat_btwn hfasb with ⟨prat, hprat₁, hprat₂⟩
        rcases exists_rat_btwn hfcsa with ⟨qrat, hqrat₁, hqrat₂⟩
        have hpq : prat < qrat := Rat.cast_lt.1 (lt_trans hprat₂ hqrat₁)
        -- Define the interval and show it is in Is
        let C := {x : ℝ | prat ≤ x ∧ x ≤ qrat}
        have hCinCs : C ∈ Cs := ⟨prat, qrat, hpq, rfl⟩
        let I := C
        have hfqainI : fq a ∈ I := ⟨le_of_lt hprat₂, le_of_lt hqrat₁⟩
        have hIinIs : I ∈ Is := by
          cases a using Quot.inductionOn with
          | _ x =>
            have hfxinC : f x ∈ C := by
              simp only [fq] at hfqainI
              exact hfqainI
            exact ⟨C, hCinCs, x, hfxinC, rfl⟩
        -- Consider the set S in pAs
        let S := Quot.mk (fun x y ↦ x ∼ₛ[rs] y) '' {x : α | f x ∈ I}
        have hSinpAs : S ∈ pAs := ⟨I, hIinIs, rfl⟩
        -- The chosen element d in A
        let d := Classical.choose (hpAsNonempty S hSinpAs)
        have hdA : d ∈ A := ⟨S, hSinpAs, rfl⟩
        -- Show that d satisfies the inequalities
        have hdbetween : bc.2 ≽[rq] d ∧ d ≽[rq] bc.1 := by
          have hdS : d ∈ S := Classical.choose_spec (hpAsNonempty S hSinpAs)
          rcases hdS with ⟨x, hfxinI, hxed⟩
          have hfxinC : f x ∈ C := by
            simp only [I] at hfxinI
            exact hfxinI
          have hdsb : d ≽[rq] bc.1 := by
            have hfxsb : f x > fq bc.1 := lt_of_lt_of_le hprat₁ hfxinC.left
            have hfdsb : fq d > fq bc.1 := by
              rw [← hxed]
              simp only [fq]
              exact hfxsb
            exact (hocsq d bc.1).mpr hfdsb
          have hcsd : bc.2 ≽[rq] d := by
            have hfcsx : fq bc.2 > f x := lt_of_le_of_lt hfxinC.right hqrat₂
            have hfcsd : fq bc.2 > fq d := by
              rw [← hxed]
              simp only [fq]
              exact hfcsx
            exact (hocsq bc.2 d).mpr hfcsd
          exact ⟨hcsd, hdsb⟩
        exact ⟨d, hdA, hdbetween⟩
      exact hnoA hexd
    -- ===== The intervals (f(b), f(c)) are pairwise disjoint =====
    -- Show that then these intervals (f(b), f(c)) are disjoint
    let s : IndiffQuot rs × IndiffQuot rs → Set ℝ := fun bc ↦ Set.Ioo (fq bc.1) (fq bc.2)
    have hdisjoint : K.PairwiseDisjoint s := by
      intro bc1 hbc1K bc2 hbc2K hbc1nebc2
      rw [Function.onFun, Disjoint]
      simp only [s, Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff]
      -- If x is in the intersection it has to be empty
      intro x hxIoo1 hxIoo2
      -- If its not empty, we can get an element and get a contradiction
      by_contra hne
      have hexa : ∃ a, a ∈ x := Set.nonempty_def.mp (Set.nonempty_iff_ne_empty.mpr hne)
      let a := Classical.choose hexa
      have hax : a ∈ x := Classical.choose_spec hexa
      have haIoo1 : a ∈ Set.Ioo (fq bc1.1) (fq bc1.2) := hxIoo1 hax
      have haIoo2 : a ∈ Set.Ioo (fq bc2.1) (fq bc2.2) := hxIoo2 hax
      -- From this we get that one of the extremes is in one of the intervals
      -- First, both ends cannot be equal in f, since then the two pairs would be equal
      have hendsne :
          (fq bc1.1 = fq bc2.1 → fq bc1.2 ≠ fq bc2.2) ∧
          (fq bc1.2 = fq bc2.2 → fq bc1.1 ≠ fq bc2.1) := by
        constructor
        · intro he₁
          by_contra he₂
          have hbc1ebc2 : bc1 = bc2 := by
            apply Prod.ext
            · exact (hidq bc1.1 bc2.1).mpr he₁
            · exact (hidq bc1.2 bc2.2).mpr he₂
          exact hbc1nebc2 hbc1ebc2
        · intro he₂
          by_contra he₁
          have hbc1ebc2 : bc1 = bc2 := by
            apply Prod.ext
            · exact (hidq bc1.1 bc2.1).mpr he₁
            · exact (hidq bc1.2 bc2.2).mpr he₂
          exact hbc1nebc2 hbc1ebc2
      -- Therefore, one of the endpoints is in the other's interval
      have honeinf :
          (fq bc1.1 < fq bc2.1 ∧ fq bc2.1 < fq bc1.2) ∨
          (fq bc1.1 < fq bc2.2 ∧ fq bc2.2 < fq bc1.2) ∨
          (fq bc2.1 < fq bc1.1 ∧ fq bc1.1 < fq bc2.2) ∨
          (fq bc2.1 < fq bc1.2 ∧ fq bc1.2 < fq bc2.2) := by
        have ha1 := Set.mem_Ioo.mp haIoo1
        have ha2 := Set.mem_Ioo.mp haIoo2
        exact interval_endpoint_inside_of_intersection ha1 ha2 hendsne
      -- Therefore, there is an element of A in the interval
      have honein :
          (bc2.1 ≽[rq] bc1.1 ∧ bc1.2 ≽[rq] bc2.1) ∨
          (bc2.2 ≽[rq] bc1.1 ∧ bc1.2 ≽[rq] bc2.2) ∨
          (bc1.1 ≽[rq] bc2.1 ∧ bc2.2 ≽[rq] bc1.1) ∨
          (bc1.2 ≽[rq] bc2.1 ∧ bc2.2 ≽[rq] bc1.2) := by
        simpa [hocsq] using honeinf
      -- This contradicts the property of (b,c) ∈ K that they are empty of other f(a)
      have hcont {bc a} (hK : bc ∈ K)
          (hin : a ∈ QuotSet) (hrq : rq a bc.1 ∧ rq bc.2 a)
          (hempty : ∀ bc ∈ K, ¬∃ a ∈ QuotSet, rq bc.2 a ∧ rq a bc.1) :
          False :=
        (hempty bc hK) ⟨a, hin, hrq.right, hrq.left⟩
      cases honein with
      | inl h₁ =>
        exact hcont hbc1K (by trivial) h₁ hfbcEmpty
      | inr hrest =>
        cases hrest with
        | inl h₂ =>
          exact hcont hbc1K (by trivial) h₂ hfbcEmpty
        | inr hrest₂ =>
          cases hrest₂ with
          | inl h₃ =>
            exact hcont hbc2K (by trivial) h₃ hfbcEmpty
          | inr h₄ =>
            exact hcont hbc2K (by trivial) h₄ hfbcEmpty
    -- ===== Disjoint nonempty open intervals in ℝ: K is countable =====
    -- Show that since each (b,c) ∈ K defines (f(b),f(c)) as
    -- an open, non-empty, disjoint intervals in ℝ,
    -- then K is countable
    have hopen : ∀ bc ∈ K, IsOpen (s bc) := by
      intro bc _
      exact isOpen_Ioo
    have hnonempty : ∀ bc ∈ K, (s bc).Nonempty := by
      intro bc hbc
      rcases hbc with ⟨_, _, hcsb, _⟩
      have hfcsb : fq bc.2 > fq bc.1 := (hocsq bc.2 bc.1).mp hcsb
      exact Set.nonempty_Ioo.2 hfcsb
    exact Set.PairwiseDisjoint.countable_of_isOpen hdisjoint hopen hnonempty
  -- ===== Define B, the endpoints of the pairs in K, and show it is countable =====
  -- Define B
  let B : Set (IndiffQuot rs) :=
    {b | ∃ c ∈ QuotSet, ((b, c) ∈ K ∨ (c, b) ∈ K)}
  -- Show that B is countable
  have hcountableB : Countable B := by
    -- Define subsets of B
    let Bl : Set (IndiffQuot rs) :=
      {b | ∃ c ∈ QuotSet, (b, c) ∈ K}
    let Br : Set (IndiffQuot rs) :=
      {b | ∃ c ∈ QuotSet, (c, b) ∈ K}
    -- Show they are countable as images of K
    have hcountableBl : Countable Bl := by
      let fBl : IndiffQuot rs × IndiffQuot rs → IndiffQuot rs := fun bc ↦ bc.1
      have himg := Set.Countable.image hcountableK fBl
      have hBlimg : Bl = fBl '' K := by
        ext b
        constructor
        · intro hb
          rcases hb with ⟨c, _, hbcK⟩
          exact ⟨(b, c), hbcK, rfl⟩
        · intro hb
          rcases hb with ⟨⟨b, c⟩, hbcK, rfl⟩
          exact ⟨c, Set.mem_of_mem_diff hbcK.2.1, hbcK⟩
      rw [← hBlimg] at himg
      exact himg
    have hcountableBr : Countable Br := by
      let fBr : IndiffQuot rs × IndiffQuot rs → IndiffQuot rs := fun bc ↦ bc.2
      have himg := Set.Countable.image hcountableK fBr
      have hBrimg : Br = fBr '' K := by
        ext b
        constructor
        · intro hb
          rcases hb with ⟨c, _, hcbK⟩
          exact ⟨(c, b), hcbK, rfl⟩
        · intro hb
          rcases hb with ⟨⟨c, b⟩, hcbK, rfl⟩
          exact ⟨c, Set.mem_of_mem_diff hcbK.1, hcbK⟩
      rw [← hBrimg] at himg
      exact himg
    -- Finally, B is the union of both
    have hBunion : B = Bl ∪ Br := by
      ext b
      constructor
      · intro hb
        rcases hb with ⟨c, hcQ, hor⟩
        cases hor with
        | inl hbcK => exact Or.inl ⟨c, hcQ, hbcK⟩
        | inr hcbK => exact Or.inr ⟨c, hcQ, hcbK⟩
      · intro hb
        cases hb with
        | inl hbBl =>
          rcases hbBl with ⟨c, hcQ, hbcK⟩
          exact ⟨c, hcQ, Or.inl hbcK⟩
        | inr hbBr =>
          rcases hbBr with ⟨c, hcQ, hcbK⟩
          exact ⟨c, hcQ, Or.inr hcbK⟩
    rw [hBunion]
    exact Set.Countable.union hcountableBl hcountableBr
  -- ===== D = A ∪ B is countable and order dense =====
  -- Define our final dense set D
  let D : Set (IndiffQuot rs) := A ∪ B
  -- Show that D is countable
  have hcountableD : Countable D := Set.Countable.union hcountableA hcountableB
  -- Show that D is dense
  have hdenseD : OrderDense D rq := by
    intro c b hcb
    rcases hcb with ⟨hcsb, hncD, hnbD⟩
    -- b, c ∉ D implies b, c ∉ A and ∉ B
    have hnbA : b ∉ A := by
      intro hbA
      exact hnbD (Set.mem_union_left B hbA)
    have hncA : c ∉ A := by
      intro hcA
      exact hncD (Set.mem_union_left B hcA)
    have hnbB : b ∉ B := by
      intro hbB
      exact hnbD (Set.mem_union_right A hbB)
    -- From b, c ∉ A we have that b, c ∈ QuotSet \ A
    have hbQA : b ∈ QuotSet \ A := ⟨by trivial, hnbA⟩
    have hcQA : c ∈ QuotSet \ A := ⟨by trivial, hncA⟩
    -- From b, c ∉ B we have that (b, c) ∉ K
    have hnbcK : (b, c) ∉ K := by
      intro hbcK
      exact hnbB ⟨c, Set.mem_of_mem_diff hbcK.2.1, Or.inl hbcK⟩
    -- Therefore, there is d ∈ D such that c ≽[rq] d ≽[rq] b
    -- If there was no such d, then there would be no a ∈ A such that c ≽[rq] a ≽[rq] b
    -- and then (b, c) ∈ K contradicting previous
    by_contra hnod
    have hnoa : ∀ a ∈ A, ¬(c ≽[rq] a ∧ a ≽[rq] b) := by
      intro a haA hcab
      rcases hcab with ⟨hcsa, hasb⟩
      exact hnod ⟨a, Set.mem_union_left B haA, ⟨hcsa, hasb⟩⟩
    have hbcK : (b, c) ∈ K := ⟨hbQA, hcQA, hcsb, by simpa using hnoa⟩
    exact hnbcK hbcK
  -- So D is the required dense countable set, and it is order separable
  exact ⟨D, hcountableD, hdenseD⟩

/-! #### Fishburn's theorem -/

/-- Fishburn's theorem (≻ weak order ∧ X/∼ order separable ⇔ ∃ f : X → ℝ with
x ≻ y ⇔ f(x) > f(y)):
`(∃ h : WeakOrder rs, OrderSeparable (IndiffQuotRel rs h)) ↔
∃ f : α → ℝ, OrdinalConsistentStrict f rs`.

Proof from: Fishburn (1970) "Utility Theory for Decision Making" Theorem 3.1. -/
theorem fishburn_theorem (rs : Relation α) :
    (∃ h : WeakOrder rs, OrderSeparable (IndiffQuotRel rs h))
    ↔ ∃ f : α → ℝ, OrdinalConsistentStrict f rs := by
  constructor
  · -- ===== Forward direction: weak order ∧ OrderSeparable → ∃ function =====
    intro hex
    rcases hex with ⟨hwo, hsep⟩
    exact exists_ordinalConsistentStrict_of_orderSeparable hwo hsep
  · -- ===== Backward direction: ∃ function → weak order ∧ OrderSeparable =====
    intro hex
    rcases hex with ⟨f, hocs⟩
    have hwo := weakOrder_of_ordinalConsistentStrict hocs
    have hsep := orderSeparable_of_ordinalConsistentStrict hocs hwo
    -- Finally, we have that is weak order and order separable,
    -- and we are done with the backward direction
    exact ⟨hwo, hsep⟩

end Fishburn

section Ordinal

/-! ## The ordinal theorem -/

/-- Main ordinal theorem (≽ complete ∧ transitive ∧ X/∼ order separable ⇔
∃ f : X → ℝ with x ≽ y ⇔ f(x) ≥ f(y)):
`(∃ h : Ordinal r, OrderSeparable (IndiffQuotRel (Strict r) (weakOrder_of_ordinal h))) ↔
∃ f : α → ℝ, OrdinalConsistent f r`. -/
theorem ordinal_theorem (r : Relation α) :
    (∃ h : Ordinal r, OrderSeparable (IndiffQuotRel (Strict r) (weakOrder_of_ordinal h)))
    ↔ ∃ f : α → ℝ, OrdinalConsistent f r := by
  constructor
  · -- ===== Forward direction: ordinal axioms ∧ OrderSeparable → ∃ function =====
    intro hex
    rcases hex with ⟨hord, hsep⟩
    have hcompl := hord.left
    -- r is ordinal → strict r is weak order
    have hwo := weakOrder_of_ordinal hord
    -- Apply Fishburn theorem to strict r
    have hexf : ∃ f : α → ℝ, OrdinalConsistentStrict f (Strict r) :=
      (fishburn_theorem (Strict r)).mp ⟨hwo, hsep⟩
    -- Strict ordinal consistency ↔ ordinal consistency
    rcases hexf with ⟨f, hocs⟩
    have hoc : OrdinalConsistent f r :=
      (ordinalConsistent_iff_ordinalConsistentStrict_of_completeness hcompl).mpr hocs
    exact ⟨f, hoc⟩
  · -- ===== Backward direction: ∃ function → ordinal axioms ∧ OrderSeparable =====
    intro hex
    rcases hex with ⟨f, hoc⟩
    -- ∃ f → r is complete
    have hcompl : Completeness r := by
      intro x y
      by_cases hfxy : f x ≥ f y
      · -- f x ≥ f y
        exact Or.inl ((hoc x y).mpr hfxy)
      · -- ¬(f x ≥ f y) → f y > f x
        exact Or.inr ((hoc y x).mpr (le_of_not_ge hfxy))
    -- r complete → (f ordinal consistent → f strict r ordinal consistent)
    have hocs : OrdinalConsistentStrict f (Strict r) :=
      ordinalConsistentStrict_of_ordinalConsistent hoc
    -- Apply Fishburn theorem to get weak order and order separable
    have hfishburn : ∃ h : WeakOrder (Strict r), OrderSeparable (IndiffQuotRel (Strict r) h) :=
      (fishburn_theorem (Strict r)).mpr ⟨f, hocs⟩
    rcases hfishburn with ⟨hwo, hsep⟩
    -- r complete → (strict r weak order → r ordinal)
    have hord : Ordinal r := (ordinal_iff_weakOrder_of_completeness hcompl).mpr hwo
    exact ⟨hord, hsep⟩

end Ordinal

end OrdinalRep
