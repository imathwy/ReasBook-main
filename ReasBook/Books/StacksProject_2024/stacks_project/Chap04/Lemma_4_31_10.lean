import StacksProject_2024.stacks_project.Chap04.Lemma_4_31_7
import StacksProject_2024.stacks_project.Chap04.Lemma_4_31_8

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory.Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

noncomputable section

open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]

variable (F : A ⥤ B) (G : C ⥤ B) (H : D ⥤ C)

local notation "LeftAssoc" => (π₂ F G) ⊡ H
local notation "RightAssoc" => F ⊡ (H ⋙ G)

/- Domain-style sampling for Lemma 4.31.10:
- primary domain: categorical pullbacks of functors and canonical comparison functors between
  pullback models;
- sampled owner abstractions:
  `CategoricalPullback`,
  `CategoricalPullback.CatCommSqOver`,
  `CatCommSqOver.toFunctorToCategoricalPullback`,
  `two_fibre_product_map`,
  `two_fibre_product_map_isEquivalence`,
  `two_fibre_product_assoc`;
- best owner abstraction: the source-facing main entry is the reassociation equivalence itself,
  assembled from the chapter's canonical pullback comparison equivalences;
- primitive data: the identity-square object of `CatCommSqOver (𝟭 C) H D`;
- derived API: the induced section
  `D ⥤ (𝟭 C) ⊡ H`, the projection equivalence
  `π₂ (𝟭 C) H : (𝟭 C) ⊡ H ⥤ D`, and the right-leg comparison functor built by
  `two_fibre_product_map`;
  that equivalence is upgraded by `two_fibre_product_map_isEquivalence`.

Source/core/bridge triage:
- `source-facing`: the canonical equivalence `((π₂ F G) ⊡ H) ≌ (F ⊡ (H ⋙ G))`;
- `core/canonical`: `two_fibre_product_assoc` from Lemma `4.31.8` and the chapter owner
  `two_fibre_product_map`;
- `bridge/view`: the canonical identity square in `CatCommSqOver (𝟭 C) H D`, the induced section
  `D ⥤ (𝟭 C) ⊡ H`, and the induced right-leg transport functor on pullbacks. -/

local notation "IdPullback" => (𝟭 C) ⊡ H
local notation "TransportSource" => F ⊡ ((π₁ (𝟭 C) H) ⋙ G)

/-- The identity square over `(𝟭 C, H)` with cone point `D`. -/
private abbrev identityPullbackSquare : CatCommSqOver (𝟭 C) H D where
  fst := H
  snd := 𝟭 D
  iso := Functor.rightUnitor H ≪≫ (Functor.leftUnitor H).symm

/-- The canonical section of the identity pullback `(𝟭 C) ⊡ H`. -/
private abbrev identityPullbackSection : D ⥤ IdPullback :=
  (toFunctorToCategoricalPullback (𝟭 C) H D).obj (identityPullbackSquare H)

/-- The second projection from the identity pullback `(𝟭 C) ⊡ H` is an equivalence, with inverse
given by the canonical section. -/
private theorem identityPullbackProj₂_isEquivalence :
    (π₂ (𝟭 C) H).IsEquivalence := by
  sorry

/-- The canonical right-leg comparison induced by the equivalence `(𝟭 C) ⊡ H ≌ D`. -/
private def rightLegTransportIso :
    (π₂ (𝟭 C) H) ⋙ (H ⋙ G) ≅ ((π₁ (𝟭 C) H) ⋙ G) ⋙ 𝟭 B :=
  Functor.associator (π₂ (𝟭 C) H) H G ≪≫
    Functor.isoWhiskerRight (catCommSq (𝟭 C) H).iso.symm G ≪≫
    Functor.associator (π₁ (𝟭 C) H) (𝟭 C) G ≪≫
    Functor.isoWhiskerLeft (π₁ (𝟭 C) H) (Functor.leftUnitor G) ≪≫
    (Functor.rightUnitor ((π₁ (𝟭 C) H) ⋙ G)).symm

/-- Lemma 4.31.10: for a diagram `A ⥤ B ← C ← D`, the textbook's canonical isomorphism
`(A ×_B C) ×_C D ≅ A ×_B D` is formalized by the canonical equivalence of categories
`((π₂ F G) ⊡ H) ≌ (F ⊡ (H ⋙ G))`. -/
def categorical_pullback_assoc : LeftAssoc ≌ RightAssoc :=
  let _ : (π₂ (𝟭 C) H).IsEquivalence :=
    identityPullbackProj₂_isEquivalence H
  let transport : TransportSource ⥤ RightAssoc :=
    two_fibre_product_map
      (rightLegTransportIso G H)
      (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm)
  let _ : transport.IsEquivalence := by
    simpa [transport, rightLegTransportIso] using
      (two_fibre_product_map_isEquivalence
        (rightLegTransportIso G H)
        (Functor.rightUnitor F ≪≫ (Functor.leftUnitor F).symm))
  (two_fibre_product_assoc F G (𝟭 C) H).trans transport.asEquivalence

/-- The forward functor of `categorical_pullback_assoc` preserves the outer-left component. -/
-- Proof sketch: unfold `categorical_pullback_assoc` as the composite of
-- `two_fibre_product_assoc F G (𝟭 C) H` with the transport equivalence induced by
-- `two_fibre_product_map`; the transport functor acts only on the right leg, so the first
-- component remains `X.fst.fst`.
theorem categorical_pullback_assoc_functor_obj_fst
    (X : LeftAssoc) :
    ((categorical_pullback_assoc F G H).functor.obj X).fst = X.fst.fst := sorry

end

end CategoryTheory.Limits
