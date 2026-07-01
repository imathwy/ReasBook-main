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
    φ.hom₂ = ψ.hom₂ := sorry

-- Proof sketch: subtract `ψ` from `φ` and use the equality of first components together with the
-- exactness of `Hom(-,T'.obj₂)` on `T` to factor the difference of the middle components through
-- `T.mor₂`; the vanishing of `T.obj₃ ⟶ T'.obj₂` forces that factor to be zero.
/-- Companion to Lemma 13.4.8, case `(2)`: if `Hom(T.obj₃,T'.obj₂)` is subsingleton, then the
middle component of a morphism of distinguished triangles is determined by the first component. -/
theorem triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₃_obj₂
    (hT : T ∈ distTriang D) (h₁ : φ.hom₁ = ψ.hom₁)
    (h32 : Subsingleton (T.obj₃ ⟶ T'.obj₂)) :
    φ.hom₂ = ψ.hom₂ := sorry

-- Proof sketch: from the difference morphism `(0,b,0)`, exactness gives a factorization through
-- both `T.mor₁` and `T'.mor₁`; the subsingleton hypotheses on
-- `Hom(T.obj₁,T'.obj₁)` and `Hom(T.obj₃,T'.obj₁)` force the factor maps, hence `b`, to vanish.
/-- Companion to Lemma 13.4.8, case `(3)`: if both `Hom(T.obj₁,T'.obj₁)` and `Hom(T.obj₃,T'.obj₁)`
are subsingleton, then the middle component is determined by the third component. -/
theorem triangleMorphism_hom₂_eq_of_subsingleton_hom_obj₁_obj₁_and_obj₃_obj₁
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₃ : φ.hom₃ = ψ.hom₃)
    (h11 : Subsingleton (T.obj₁ ⟶ T'.obj₁)) (h31 : Subsingleton (T.obj₃ ⟶ T'.obj₁)) :
    φ.hom₂ = ψ.hom₂ := sorry

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
    φ.hom₂ = ψ.hom₂ := sorry

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
    φ.hom₂ = ψ.hom₂ := sorry

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
