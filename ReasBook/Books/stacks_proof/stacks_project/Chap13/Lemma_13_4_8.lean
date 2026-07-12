import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe v u

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.4.8:
- primary domain: morphisms between distinguished triangles in a pretriangulated category, together
  with the exact Hom sequences attached to a distinguished triangle;
- sampled owner declarations:
  `Triangle.hom_ext`,
  `Triangle.coyoneda_exact₂`,
  `Triangle.yoneda_exact₂`,
  `Triangle.coyoneda_exact₁`;
- best owner abstraction: the category `Triangle D`, so parallel triangle morphisms should use the
  canonical hom type `T ⟶ T'`; the five vanishing alternatives remain source-facing hypotheses on
  the theorem surface rather than a separate packaged owner;
- primitive data: two distinguished triangles `T` and `T'`, together with parallel morphisms
  `φ ψ : T ⟶ T'`;
- derived API: the uniqueness of the middle component under one of the five textbook
  Hom-vanishing alternatives.

Source/core/bridge triage:
- `source-facing`: the five textbook Hom-vanishing alternatives ensuring uniqueness of the middle
  component;
- `core/canonical`: the triangle category owner `Triangle D` and the exactness lemmas for the
  represented Hom functors of a distinguished triangle;
- `bridge/view`: the comparison of two parallel morphisms with fixed outer components, together
  with the owner-level corollary `φ = ψ` obtained from `Triangle.hom_ext`. -/

variable {T T' : Triangle D} {φ ψ : T ⟶ T'}

-- Proof sketch: subtract `ψ` from `φ`, use the equality of third components and the exactness of
-- `Hom(T.obj₂,-)` on `T'` to factor the difference of the middle components through `T'.mor₁`,
-- and then use the subsingleton hypothesis on `T.obj₂ ⟶ T'.obj₁` to force that factor to vanish.
/-- Companion to Lemma 13.4.8, case `(1)`: if `Hom(T.obj₂,T'.obj₁)` is subsingleton, then two
parallel morphisms of distinguished triangles with the same third component have the same middle
component. -/
theorem triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₂_obj₁
    (hT' : T' ∈ distTriang D) (h₃ : φ.hom₃ = ψ.hom₃)
    (h21 : Subsingleton (T.obj₂ ⟶ T'.obj₁)) :
    φ.hom₂ = ψ.hom₂ := by
  -- Proof comment: factor the middle-component difference through `T'.mor₁`.
  have hsub : φ.hom₂ - ψ.hom₂ = 0 := by
    have hzero : (φ.hom₂ - ψ.hom₂) ≫ T'.mor₂ = 0 := by
      rw [Preadditive.sub_comp, ← φ.comm₂, ← ψ.comm₂, h₃, sub_self]
    obtain ⟨a, ha⟩ := T'.coyoneda_exact₂ hT' (φ.hom₂ - ψ.hom₂) hzero
    -- Proof comment: the factor belongs to a subsingleton Hom group, so it must vanish.
    have ha_zero : a = 0 := h21.elim a 0
    simpa [ha_zero] using ha
  exact sub_eq_zero.mp hsub

-- Proof sketch: subtract `ψ` from `φ` and use the equality of first components together with the
-- exactness of `Hom(-,T'.obj₂)` on `T` to factor the difference of the middle components through
-- `T.mor₂`; the vanishing of `T.obj₃ ⟶ T'.obj₂` forces that factor to be zero.
/-- Companion to Lemma 13.4.8, case `(2)`: if `Hom(T.obj₃,T'.obj₂)` is subsingleton, then the
middle component of a morphism of distinguished triangles is determined by the first component. -/
theorem triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₃_obj₂
    (hT : T ∈ distTriang D) (h₁ : φ.hom₁ = ψ.hom₁)
    (h32 : Subsingleton (T.obj₃ ⟶ T'.obj₂)) :
    φ.hom₂ = ψ.hom₂ := by
  -- Proof comment: factor the middle-component difference through `T.mor₂`.
  have hsub : φ.hom₂ - ψ.hom₂ = 0 := by
    have hzero : T.mor₁ ≫ (φ.hom₂ - ψ.hom₂) = 0 := by
      rw [Preadditive.comp_sub, φ.comm₁, ψ.comm₁, h₁, sub_self]
    obtain ⟨a, ha⟩ := T.yoneda_exact₂ hT (φ.hom₂ - ψ.hom₂) hzero
    -- Proof comment: the factor lands in a subsingleton Hom group, forcing the difference to be
    -- zero.
    have ha_zero : a = 0 := h32.elim a 0
    simpa [ha_zero] using ha
  exact sub_eq_zero.mp hsub

-- Proof sketch: from the difference morphism `(0,b,0)`, exactness gives a factorization through
-- both `T.mor₁` and `T'.mor₁`; the subsingleton hypotheses on
-- `Hom(T.obj₁,T'.obj₁)` and `Hom(T.obj₃,T'.obj₁)` force the factor maps, hence `b`, to vanish.
/-- Companion to Lemma 13.4.8, case `(3)`: if both `Hom(T.obj₁,T'.obj₁)` and `Hom(T.obj₃,T'.obj₁)`
are subsingleton, then the middle component is determined by the third component. -/
theorem triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₁_obj₁_and_obj₃_obj₁
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₃ : φ.hom₃ = ψ.hom₃)
    (h11 : Subsingleton (T.obj₁ ⟶ T'.obj₁)) (h31 : Subsingleton (T.obj₃ ⟶ T'.obj₁)) :
    φ.hom₂ = ψ.hom₂ := by
  -- Proof comment: first derive `Hom(T.obj₂,T'.obj₁)` vanishing from exactness on `T`.
  have h21 : Subsingleton (T.obj₂ ⟶ T'.obj₁) := by
    refine ⟨?_⟩
    intro u v
    have hsub : u - v = 0 := by
      have hzero : T.mor₁ ≫ (u - v) = 0 := by
        rw [Preadditive.comp_sub]
        have hu_zero : T.mor₁ ≫ u = 0 := h11.elim (T.mor₁ ≫ u) 0
        have hv_zero : T.mor₁ ≫ v = 0 := h11.elim (T.mor₁ ≫ v) 0
        rw [hu_zero, hv_zero, sub_self]
      obtain ⟨a, ha⟩ := T.yoneda_exact₂ hT (u - v) hzero
      -- Proof comment: exactness moves the difference to `T.obj₃`, where the second
      -- subsingleton hypothesis kills it.
      have ha_zero : a = 0 := h31.elim a 0
      simpa [ha_zero] using ha
    exact sub_eq_zero.mp hsub
  exact triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₂_obj₁ hT' h₃ h21

-- Proof sketch: this is dual to case `(3)`, now using the exactness segment around the third
-- components together with the subsingleton hypotheses on `Hom(T.obj₃,T'.obj₁)` and
-- `Hom(T.obj₃,T'.obj₃)`.
/-- Companion to Lemma 13.4.8, case `(4)`: if both `Hom(T.obj₃,T'.obj₁)` and
`Hom(T.obj₃,T'.obj₃)` are subsingleton, then the middle component is determined by the first
component. -/
theorem triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₃_obj₁_and_obj₃_obj₃
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₁ : φ.hom₁ = ψ.hom₁)
    (h31 : Subsingleton (T.obj₃ ⟶ T'.obj₁)) (h33 : Subsingleton (T.obj₃ ⟶ T'.obj₃)) :
    φ.hom₂ = ψ.hom₂ := by
  -- Proof comment: dual to case `(3)`, derive `Hom(T.obj₃,T'.obj₂)` vanishing from exactness on
  -- `T'`.
  have h32 : Subsingleton (T.obj₃ ⟶ T'.obj₂) := by
    refine ⟨?_⟩
    intro u v
    have hsub : u - v = 0 := by
      have hzero : (u - v) ≫ T'.mor₂ = 0 := by
        rw [Preadditive.sub_comp]
        have hu_zero : u ≫ T'.mor₂ = 0 := h33.elim (u ≫ T'.mor₂) 0
        have hv_zero : v ≫ T'.mor₂ = 0 := h33.elim (v ≫ T'.mor₂) 0
        rw [hu_zero, hv_zero, sub_self]
      obtain ⟨a, ha⟩ := T'.coyoneda_exact₂ hT' (u - v) hzero
      -- Proof comment: the factorization lands in `Hom(T.obj₃,T'.obj₁)`, which is also
      -- subsingleton.
      have ha_zero : a = 0 := h31.elim a 0
      simpa [ha_zero] using ha
    exact sub_eq_zero.mp hsub
  exact triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₃_obj₂ hT h₁ h32

-- Proof sketch: use the shifted exactness segment ending in `T'.obj₁⟦1⟧` together with the
-- unshifted exactness through `T'.obj₁`; the subsingleton hypotheses on
-- `Hom(T.obj₁⟦1⟧,T'.obj₃)` and `Hom(T.obj₃,T'.obj₁)` force the relevant factors to vanish.
/-- Companion to Lemma 13.4.8, case `(5)`: if both `Hom(T.obj₁⟦1⟧,T'.obj₃)` and
`Hom(T.obj₃,T'.obj₁)` are subsingleton, then the middle component is unique. -/
theorem triangleMorphism_hom₂_eq_of_subsingleton_hom_shift_obj₁_obj₃_and_obj₃_obj₁
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₁ : φ.hom₁ = ψ.hom₁) (h₃ : φ.hom₃ = ψ.hom₃)
    (h13 : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃))
    (h31 : Subsingleton (T.obj₃ ⟶ T'.obj₁)) :
    φ.hom₂ = ψ.hom₂ := by
  -- Proof comment: follow the source proof and successively factor the middle-component
  -- difference through `T.mor₂`, `T.mor₃`, and `T'.mor₁`.
  have hsub : φ.hom₂ - ψ.hom₂ = 0 := by
    have hleft_zero : T.mor₁ ≫ (φ.hom₂ - ψ.hom₂) = 0 := by
      rw [Preadditive.comp_sub, φ.comm₁, ψ.comm₁, h₁, sub_self]
    obtain ⟨ε, hε⟩ := T.yoneda_exact₂ hT (φ.hom₂ - ψ.hom₂) hleft_zero
    have hright_zero : (φ.hom₂ - ψ.hom₂) ≫ T'.mor₂ = 0 := by
      rw [Preadditive.sub_comp, ← φ.comm₂, ← ψ.comm₂, h₃, sub_self]
    have hε_right_zero : T.mor₂ ≫ (ε ≫ T'.mor₂) = 0 := by
      rw [← Category.assoc, ← hε]
      exact hright_zero
    obtain ⟨δ, hδ⟩ := T.yoneda_exact₃ hT (ε ≫ T'.mor₂) hε_right_zero
    -- Proof comment: the shifted-Hom subsingleton kills the factor through `T.mor₃`.
    have hδ_zero : δ = 0 := h13.elim δ 0
    have hε_mor₂_zero : ε ≫ T'.mor₂ = 0 := by
      simpa [hδ_zero] using hδ
    obtain ⟨γ, hγ⟩ := T'.coyoneda_exact₂ hT' ε hε_mor₂_zero
    -- Proof comment: the remaining factor through `T'.mor₁` also vanishes.
    have hγ_zero : γ = 0 := h31.elim γ 0
    have hε_zero : ε = 0 := by
      simpa [hγ_zero] using hγ
    simpa [hε_zero] using hε
  exact sub_eq_zero.mp hsub

/-- Lemma 13.4.8: for a morphism between distinguished triangles in a pretriangulated category,
the middle component is uniquely determined by the outer components whenever one of the five
listed Hom-vanishing conditions holds. -/
-- Proof sketch: subtract two triangle morphisms with the same first and third components to
-- reduce to a triangle morphism `(0,b,0)`. Then use the exactness statements of Lemma 13.4.2 for
-- the covariant or contravariant Hom functors, together with the stated vanishing hypotheses, to
-- force `b = 0` in each of the five cases.
theorem triangleMorphism_hom₂_eq_of_hom_vanishing
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₁ : φ.hom₁ = ψ.hom₁) (h₃ : φ.hom₃ = ψ.hom₃)
    (hvan :
      Subsingleton (T.obj₂ ⟶ T'.obj₁) ∨
        Subsingleton (T.obj₃ ⟶ T'.obj₂) ∨
          (Subsingleton (T.obj₁ ⟶ T'.obj₁) ∧ Subsingleton (T.obj₃ ⟶ T'.obj₁)) ∨
            (Subsingleton (T.obj₃ ⟶ T'.obj₁) ∧ Subsingleton (T.obj₃ ⟶ T'.obj₃)) ∨
              (Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃) ∧
                Subsingleton (T.obj₃ ⟶ T'.obj₁))) :
    φ.hom₂ = ψ.hom₂ := by
  rcases hvan with h21 | hvan
  · exact triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₂_obj₁ hT' h₃ h21
  rcases hvan with h32 | hvan
  · exact triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₃_obj₂ hT h₁ h32
  rcases hvan with h11 | hvan
  · exact triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₁_obj₁_and_obj₃_obj₁
      hT hT' h₃ h11.1 h11.2
  rcases hvan with h33 | hvan
  · exact triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₃_obj₁_and_obj₃_obj₃
      hT hT' h₁ h33.1 h33.2
  exact triangleMorphism_hom₂_eq_of_subsingleton_hom_shift_obj₁_obj₃_and_obj₃_obj₁
    hT hT' h₁ h₃ hvan.1 hvan.2

/-- Owner-level corollary of Lemma 13.4.8: under any of the five Hom-vanishing alternatives, a
parallel morphism of distinguished triangles is determined by its first and third components. -/
theorem triangleMorphism_eq_of_outer_eq_of_hom_vanishing
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₁ : φ.hom₁ = ψ.hom₁) (h₃ : φ.hom₃ = ψ.hom₃)
    (hvan :
      Subsingleton (T.obj₂ ⟶ T'.obj₁) ∨
        Subsingleton (T.obj₃ ⟶ T'.obj₂) ∨
          (Subsingleton (T.obj₁ ⟶ T'.obj₁) ∧ Subsingleton (T.obj₃ ⟶ T'.obj₁)) ∨
            (Subsingleton (T.obj₃ ⟶ T'.obj₁) ∧ Subsingleton (T.obj₃ ⟶ T'.obj₃)) ∨
              (Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃) ∧
                Subsingleton (T.obj₃ ⟶ T'.obj₁))) :
    φ = ψ :=
  Triangle.hom_ext φ ψ h₁
    (triangleMorphism_hom₂_eq_of_hom_vanishing hT hT' h₁ h₃ hvan) h₃

end
