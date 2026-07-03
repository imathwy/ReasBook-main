import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_34_1 (from Chap07) -/
universe w u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for Lemma 7.34.1:
- primary domain: set-valued presheaf fibers, presheaf costalks, and left Kan extension along
  `u.op`;
- sampled owner API:
  `Functor.lanAdjunction`,
  `presheafCostalkAdjunction`,
  `Functor.whiskeringLeftObjCompIso`,
  `Adjunction.leftAdjointUniq`;
- source/core/bridge triage:
  `source-facing`: the comparison from the `v`-fiber of the pushforward `uₚ F` to the
  `(u ⋙ v)`-fiber of `F`;
  `core/canonical`: the owners `u.op.lan`, `Functor.presheafFiber`, and the right-adjoint
  description by presheaf costalks;
  `bridge/view`: the canonical identification of right adjoints
  `(u ⋙ v)^p ≅ v^p ⋙ (whiskeringLeft _ _ _).obj u.op`, obtained by combining
  `Functor.associator` with `Functor.whiskeringLeftObjCompIso u.op v.op`.

Primitive data are only the functors `u` and `v`, with `v` valued in a sufficiently large `Type`
so that the canonical left Kan extension and presheaf-fiber owners exist without extra public
smallness assumptions. The comparison isomorphism is derived API from the canonical adjunctions
`u.op.lan ⊣ u^p` and `v.presheafFiber ⊣ v^p`, together with the composition formula for
pullback/costalk. The refinement therefore removes the private generator-level comparison maps and
defines the source-facing isomorphism directly as the canonical uniqueness isomorphism between two
left adjoints to the same right adjoint.
-/

/-- Lemma 7.34.1: for a functor `u : \mathcal C \to \mathcal D`, a set-valued functor
`v : \mathcal D \to \mathrm{Sets}`, and `w = v \circ u`, the canonical natural transformation from
the `v`-fiber of the pushforward presheaf, realized canonically as the left Kan extension of `F`
along `u.op`, to the `w`-fiber of `F` is an isomorphism.
This is the functorial form of `(uₚ F)_q = F_p`. -/
@[simps!]
noncomputable def presheafPushforwardFiberIso
    (u : C ⥤ D) (v : D ⥤ Type (max u₁ u₂ v₁ v₂ w)) :
    u.op.lan ⋙ v.presheafFiber ≅ (u ⋙ v).presheafFiber :=
  (((u.op.lanAdjunction (Type (max u₁ u₂ v₁ v₂ w))).comp (presheafCostalkAdjunction v)).ofNatIsoRight
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (whiskeringLeftObjCompIso u.op v.op).symm)).leftAdjointUniq
    (presheafCostalkAdjunction (u ⋙ v))

/-- Proposition-level companion to `presheafPushforwardFiberIso`: pushing a presheaf forward
along `u` and then taking the `v`-fiber is canonically isomorphic to taking the `(u ⋙ v)`-fiber
directly. -/
theorem presheafPushforwardFiber_isomorphic
    (u : C ⥤ D) (v : D ⥤ Type (max u₁ u₂ v₁ v₂ w)) :
    IsIsomorphic (u.op.lan ⋙ v.presheafFiber) ((u ⋙ v).presheafFiber) :=
  ⟨presheafPushforwardFiberIso u v⟩

-- Proof sketch: the hom component of any natural isomorphism is an isomorphism objectwise, so
-- this follows by applying the canonical instance to the component of
-- `presheafPushforwardFiberIso`.
/-- The canonical comparison map from the `v`-fiber of the pushforward presheaf to the
`(u ⋙ v)`-fiber is objectwise an isomorphism. -/
theorem presheafPushforwardFiberIso_hom_app_isIso
    (u : C ⥤ D) (v : D ⥤ Type (max u₁ u₂ v₁ v₂ w))
    (F : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w)) :
    IsIso ((presheafPushforwardFiberIso u v).hom.app F) := by
  -- The comparison is a natural isomorphism, so each component map is an isomorphism.
  simpa using (show IsIso (((presheafPushforwardFiberIso u v).app F).hom) by infer_instance)

end Functor

end CategoryTheory

/-! ### Lemma_7_34_2 (from Chap07) -/
open CategoryTheory.Limits

universe w v u₁ u₂ u₃ v₁ v₂

namespace CategoryTheory.GrothendieckTopology

/- Domain-style sampling for Lemma 7.34.2:
- primary domain: points of Grothendieck sites and inverse image along a morphism of sites;
- sampled owner declarations:
  `GrothendieckTopology.Point`,
  `GrothendieckTopology.Point.comap`,
  `GrothendieckTopology.Point.sheafFiberComapIso`;
- best owner abstraction: the site-point owner `GrothendieckTopology.Point`, with the pullback
  point and its stalk comparison as derived API;
- source/core/bridge triage:
  `source-facing`: pulling back a site point along a morphism of sites and identifying the stalk
    of a pulled-back sheaf at the original point;
  `core/canonical`: the mathlib owners `Point.comap` and `Point.sheafFiberComapIso`;
  `bridge/view`: this file is recall-only, restating the textbook content directly on that
    canonical owner surface.

Primitive data are only the point `q`, the functor `u`, and the cover-preserving hypothesis `h`.
The induced point on `(C, J)` and the stalk comparison are derived API from the owner
`GrothendieckTopology.Point`, so this file should keep direct recall/use of the canonical mathlib
declarations rather than reintroducing any local wrapper.
-/

section

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable {K : GrothendieckTopology D}
variable (q : K.Point) (u : C ⥤ D) [RepresentablyFlat u]
variable {J : GrothendieckTopology C} (h : CoverPreserving J K u)
variable [InitiallySmall (u ⋙ q.fiber).Elements]

/-
Lemma 7.34.2: a morphism of sites `(D, K) → (C, J)` given by `u : C ⥤ D` pulls a point `q` of
`(D, K)` back to a point of `(C, J)`. Mathlib states the canonical construction slightly more
generally, for a representably flat cover-preserving functor `u`, as `q.comap u h`.
-/
#check (q.comap u h : J.Point)

variable (A : Type u₃) [Category.{v} A] [HasProducts A] [u.IsContinuous J K]
variable [(u.sheafPushforwardContinuous A J K).IsRightAdjoint]
variable [HasColimitsOfSize.{w, w} A]

/-
Lemma 7.34.2: for the same data, the stalk of the pullback of a sheaf along `u` at `q` is
canonically identified with the stalk at the pulled-back point `q.comap u h`. Mathlib states
this as the canonical isomorphism `q.sheafFiberComapIso u h A`; specializing to set-valued
sheaves takes `A` to a suitable universe of types.
-/
#check
  (q.sheafFiberComapIso u h A :
    (q.comap u h).sheafFiber ≅ u.sheafPullback A J K ⋙ q.sheafFiber)

end

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_7_34_3 (from Chap07) -/
universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (f : MorphismOfTopoiIn J K)
variable (q : MorphismOfTopoiIn K typesGrothendieckTopology.{w})
variable (ℱ : Sheaf J (Type w))

/- Domain-style sampling for Lemma 7.34.3:
- primary domain: points of topoi and their inverse-image/stalk functors;
- sampled owner API:
  `MorphismOfTopoiIn.typeInverseImage`,
  `MorphismOfTopoiIn.comp`,
  `typeEquiv`;
- owner abstraction: `MorphismOfTopoiIn.comp`;
- layer: bridge/view, since the stalk statement is the objectwise computation of the inverse-image
  functor of the composite point, viewed in `Type` through `typeEquiv` via `typeInverseImage`.

Primitive data are just the morphism of topoi `f`, the point `q`, and the sheaf `ℱ`. The stalk
comparison is derived API from the owner `MorphismOfTopoiIn.comp`, so this item should be a direct
recall of that canonical computation rather than a parallel theorem wrapper.
-/

/- Lemma 7.34.3: for a morphism of topoi `f : Sh(𝒟) ⟶ Sh(𝒞)`, a point `q` of `Sh(𝒟)`, and a
sheaf `ℱ` on `𝒞`, the stalk `(f⁻¹ ℱ)_q` is canonically identified with the stalk of `ℱ` at the
composite point `f.comp q`. -/
#check
  (rfl :
    q.typeInverseImage.obj ((f⁻¹).obj ℱ) =
      (f.comp q).typeInverseImage.obj ℱ)

end CategoryTheory
