import StacksProject_2024.Chap08.Lemma_8_4_3_RestrictedDescent

open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C)
variable (P : ObjectProperty X)

variable [IsStackOnSite J p]

section RestrictedFibered

variable [(P.ι ⋙ p).IsFibered]

/-- Helper for Lemma 8.4.3: for a fixed source object in the restricted fiber, the componentwise
pullback-comparison isomorphisms satisfy the descent square relating the restricted and ambient
canonical fixed-cover descent data. -/
private theorem restricted_cover_toDescentData_transport_iso_app_comm
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U)
    {Y : C} (q : Y ⟶ U) {I₁ I₂ : S.Arrow}
    (f₁ : Y ⟶ I₁.Y) (f₂ : Y ⟶ I₂.Y)
    (hf₁ : f₁ ≫ I₁.f = q := by cat_disch) (hf₂ : f₂ ≫ I₂.f = q := by cat_disch) :
    (((canonicalFiberPseudofunctor p).map f₁.op.toLoc).toFunctor.map
        (restricted_pullback_vs_ambient_pullback_comparison
          (J := J) (p := p) (P := P) hpullback I₁.f x).hom) ≫
      (((ambient_cover_toDescentData_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          ((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor.obj x)).obj).hom q f₁ f₂ hf₁ hf₂ =
    (((restricted_cover_descent_to_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
              (fun I : S.Arrow ↦ I.f)).obj x)).obj).hom q f₁ f₂ hf₁ hf₂ ≫
        (((canonicalFiberPseudofunctor p).map f₂.op.toLoc).toFunctor.map
          (restricted_pullback_vs_ambient_pullback_comparison
            (J := J) (p := p) (P := P) hpullback I₂.f x).hom) := by
  -- TODO: normalize the ambient canonical descent overlap to the comparison-conjugated shell
  -- `restricted_cover_descent_isoClosure_obj_hom_via_pullbackComparison`, then finish by the
  -- same fixed-cover transport identity used in the target file.
  sorry

/-- Helper for Lemma 8.4.3: for a fixed source object in the restricted fiber, the legwise
pullback-comparison isomorphisms package to an isomorphism between the restricted and ambient
fixed-cover descent data. -/
private noncomputable def restricted_cover_toDescentData_transport_component_iso
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) (x : (P.ι ⋙ p).Fiber U) :
    ((restricted_cover_descent_to_isoClosure
          (J := J) (p := p) (P := P) hpullback S).obj
        (((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
            (fun I : S.Arrow ↦ I.f)).obj x)) ≅
      ((ambient_cover_toDescentData_isoClosure
            (J := J) (p := p) (P := P) hpullback S).obj
          ((fullSubcategory_fiber_equiv_inverseImage
              (p := p) (P := P) U).functor.obj x)) := by
  -- Package the legwise pullback-comparison maps into an isomorphism of the two fixed-cover
  -- descent data attached to `x`.
  refine ObjectProperty.isoMk (P := cover_componentwise_isoClosure_property
    (J := J) (p := p) (P := P) S) <|
    Pseudofunctor.DescentData.isoMk
      (fun I ↦ restricted_pullback_vs_ambient_pullback_comparison
        (J := J) (p := p) (P := P) hpullback I.f x) ?_
  intro Y q I₁ I₂ f₁ f₂ hf₁ hf₂
  -- The componentwise commutativity is exactly the unfolded transport square proved above.
  exact
    restricted_cover_toDescentData_transport_iso_app_comm
      (J := J) (p := p) (P := P) (hpullback := hpullback) S x q f₁ f₂ hf₁ hf₂

/-- Helper for Lemma 8.4.3: compare the restricted canonical descent functor composed with the
forward bridge to the ambient canonical descent functor on the inverse-image full subcategory. -/
noncomputable def restricted_cover_toDescentData_transport_iso
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {U : C} (S : J.Cover U) :
    ((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData (fun I : S.Arrow ↦ I.f)) ⋙
        restricted_cover_descent_to_isoClosure (J := J) (p := p) (P := P) hpullback S ≅
      (fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor ⋙
        ambient_cover_toDescentData_isoClosure (J := J) (p := p) (P := P) hpullback S := by
  let η :
      (fullSubcategory_fiber_equiv_inverseImage (p := p) (P := P) U).functor ⋙
          ambient_cover_toDescentData_isoClosure
            (J := J) (p := p) (P := P) hpullback S ≅
        ((canonicalFiberPseudofunctor (P.ι ⋙ p)).toDescentData
          (fun I : S.Arrow ↦ I.f)) ⋙
          restricted_cover_descent_to_isoClosure
            (J := J) (p := p) (P := P) hpullback S :=
    NatIso.ofComponents
      (fun x ↦
        (restricted_cover_toDescentData_transport_component_iso
          (J := J) (p := p) (P := P) hpullback S x).symm)
      (fun φ ↦ by
        -- TODO: rewrite the objectwise components of the owner comparison to the actual legwise
        -- pullback-comparison maps and close naturality by the specialized inverse-side
        -- pullback-comparison square.
        sorry)
  -- The previous comparison is oriented ambient-to-restricted; invert it to match the theorem.
  exact η.symm

end RestrictedFibered

end
