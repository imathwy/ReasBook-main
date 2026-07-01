import Mathlib
import stacks_project.Chap07.Lemma_7_12_4
import stacks_project.Chap07.Definition_7_14_1
import stacks_project.Chap07.Lemma_7_25_2
import stacks_project.Chap07.Lemma_7_25_9
import stacks_project.Chap07.Lemma_7_25_8
import stacks_project.Chap07.Remark_7_25_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe w u₁ u₂ v₁ v₂ v₃

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.28.1:
- primary domain: the slice functor `Over.post u : D/V ⥤ C/u(V)` attached to a morphism of sites
  and the induced comparison on direct images;
- sampled owner API:
  `Over.post`,
  `Functor.IsContinuous`,
  `RepresentablyFlat`,
  `IsMorphismOfSites`,
  `Functor.sheafPushforwardContinuousComp'`;
- source/core/bridge triage:
  `source-facing`: the localized morphism of sites `(D/V, JD.over V) ⟶ (C/u(V), JC.over u(V))`
  induced by `u`;
  `core/canonical`: the owner predicates `Functor.IsContinuous`, `RepresentablyFlat`,
  `IsMorphismOfSites`, and the pushforward comparison
  `Functor.sheafPushforwardContinuousComp'`;
  `bridge/view`: the slice specialization of those owner declarations.

Primitive data are only the functor `u`, the object `V`, and the site structures. The remaining
source-faithful blocker is the localization proof that `Over.post u` is continuous; once that is
supplied, the site-morphism and pushforward-comparison statements are owner-level corollaries.
-/

/- The flatness proof follows the source route: identify the slice structured-arrow category of
`Over.post u` with an over-category in the ambient structured-arrow category of `u`, then transport
cofilteredness across that equivalence. -/
/-- Helper for Lemma 7.28.1: send an object of `StructuredArrow Y (Over.post u)` to the
corresponding object of `Over (StructuredArrow.mk Y.hom)`. -/
private abbrev structuredArrow_overPost_to_over_obj
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V))
    (A : StructuredArrow Y (show Over V ⥤ Over (u.obj V) from Over.post u)) :
    Over (StructuredArrow.mk Y.hom : StructuredArrow Y.left u) := by
  -- The map `Y ⟶ u(A.right.left)/u(V)` is exactly a map into the ambient structured arrow
  -- `StructuredArrow.mk Y.hom`.
  let Z : StructuredArrow Y.left u := StructuredArrow.mk A.hom.left
  exact CostructuredArrow.mk
    (StructuredArrow.homMk (f := Z) (f' := StructuredArrow.mk Y.hom) A.right.hom (by
      simpa using A.hom.w))

/-- Helper for Lemma 7.28.1: send a morphism in `StructuredArrow Y (Over.post u)` to the
corresponding morphism in `Over (StructuredArrow.mk Y.hom)`. -/
private abbrev structuredArrow_overPost_to_over_hom
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V))
    {A B : StructuredArrow Y (show Over V ⥤ Over (u.obj V) from Over.post u)}
    (f : A ⟶ B) :
    structuredArrow_overPost_to_over_obj u V Y A ⟶
      structuredArrow_overPost_to_over_obj u V Y B := by
  -- The underlying map in `Over V` already satisfies the required compatibility over `u`.
  exact Over.homMk
    (StructuredArrow.homMk f.right.left (by
      simpa using (congrArg CommaMorphism.left f.w).symm))
    (by
      simpa using Over.w f.right)

/-- Helper for Lemma 7.28.1: recover an object of `StructuredArrow Y (Over.post u)` from an
object of `Over (StructuredArrow.mk Y.hom)`. -/
private abbrev over_to_structuredArrow_overPost_obj
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V))
    (A : Over (StructuredArrow.mk Y.hom : StructuredArrow Y.left u)) :
    StructuredArrow Y (show Over V ⥤ Over (u.obj V) from Over.post u) := by
  -- The right leg of the over-object is the corresponding object of `Over V`.
  let Z : Over V := CostructuredArrow.mk A.hom.right
  exact StructuredArrow.mk
    (Over.homMk (U := Y) (V := (Over.post u).obj Z) A.left.hom (by
      simpa using A.hom.w.symm))

/-- Helper for Lemma 7.28.1: recover a morphism in `StructuredArrow Y (Over.post u)` from a
morphism in `Over (StructuredArrow.mk Y.hom)`. -/
private abbrev over_to_structuredArrow_overPost_hom
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V))
    {A B : Over (StructuredArrow.mk Y.hom : StructuredArrow Y.left u)}
    (f : A ⟶ B) :
    over_to_structuredArrow_overPost_obj u V Y A ⟶
      over_to_structuredArrow_overPost_obj u V Y B := by
  -- The left component gives the structured-arrow compatibility, and the right component is the
  -- desired map in `Over V`.
  refine StructuredArrow.homMk ?_ ?_
  · exact Over.homMk f.left.right (by
      simpa using congrArg CommaMorphism.right (Over.w f))
  · ext
    simpa using f.left.w.symm

/-- Helper for Lemma 7.28.1: translating a structured-arrow morphism to the over-side and back
recovers the original morphism. -/
private theorem over_to_structuredArrow_overPost_hom_structuredArrow_overPost_to_over_hom
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V))
    {A B : StructuredArrow Y (show Over V ⥤ Over (u.obj V) from Over.post u)}
    (f : A ⟶ B) :
    over_to_structuredArrow_overPost_hom u V Y
        (structuredArrow_overPost_to_over_hom u V Y f) = f := by
  -- Both comma morphisms have the same right component in `Over V`.
  ext
  rfl

/-- Helper for Lemma 7.28.1: translating an over-side morphism to the structured-arrow side and
back recovers the original morphism. -/
private theorem structuredArrow_overPost_to_over_hom_over_to_structuredArrow_overPost_hom
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V))
    {A B : Over (StructuredArrow.mk Y.hom : StructuredArrow Y.left u)}
    (f : A ⟶ B) :
    structuredArrow_overPost_to_over_hom u V Y
        (over_to_structuredArrow_overPost_hom u V Y f) = f := by
  -- Both over-morphisms have the same left component in `StructuredArrow Y.left u`.
  ext
  rfl

/-- Helper for Lemma 7.28.1: the structured-arrow category governing slice flatness is
equivalent to the over-category on the corresponding ambient structured arrow. -/
private noncomputable def structuredArrow_overPost_equiv_over_structuredArrow
    (u : D ⥤ C) (V : D) (Y : Over (u.obj V)) :
    StructuredArrow Y (show Over V ⥤ Over (u.obj V) from Over.post u) ≌
      Over (StructuredArrow.mk Y.hom : StructuredArrow Y.left u) where
  functor :=
    { obj := structuredArrow_overPost_to_over_obj u V Y
      map := fun f ↦ structuredArrow_overPost_to_over_hom u V Y f }
  inverse :=
    { obj := over_to_structuredArrow_overPost_obj u V Y
      map := fun f ↦ over_to_structuredArrow_overPost_hom u V Y f }
  unitIso := NatIso.ofComponents
    (fun A ↦
      -- The round-trip only repackages the same object of `Over V`.
      StructuredArrow.isoMk (Over.isoMk (Iso.refl _)))
    (by
      intro A B f
      ext
      simp)
  counitIso := NatIso.ofComponents
    (fun A ↦
      -- The reverse round-trip only repackages the same object of the ambient over-category.
      Over.isoMk (StructuredArrow.isoMk (Iso.refl _)))
    (by
      intro A B f
      ext
      simp)

/-- Helper for Lemma 7.28.1: forgetting the target slice after `Over.post u` recovers the base
functor `u`. -/
private theorem overPost_comp_forget_eq
    (u : D ⥤ C) (V : D) :
    Over.post u ⋙ Over.forget (u.obj V) = Over.forget V ⋙ u := by
  -- This is the strict specialization of the definition of `Over.post`.
  rfl

/-- Helper for Lemma 7.28.1: after transporting a slice sieve back to the base category, pushing
it forward along `Over.post u` is the same as pushing the transported sieve forward along `u`. -/
private theorem overEquiv_functorPushforward_post
    (u : D ⥤ C) {V : D} {Y : Over V} (S : Sieve Y) :
    Sieve.overEquiv ((Over.post u).obj Y) (S.functorPushforward (Over.post u)) =
      (Sieve.overEquiv Y S).functorPushforward u := by
  -- Both sides are the pushforward of `S` along the same composite
  -- `Over.forget V ⋙ u = Over.post u ⋙ Over.forget (u.obj V)`.
  change
      Sieve.functorPushforward (Over.forget (u.obj V))
          (S.functorPushforward (Over.post u)) =
        Sieve.functorPushforward u (Sieve.functorPushforward (Over.forget V) S)
  rw [← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp]
  rfl

/-- Helper for Lemma 7.28.1: any ambient sheaf on `(C, JC)` remains a sheaf after first pulling
back along `u` and then restricting to the slice over `V`. -/
private theorem overPost_ambient_restriction_isSheaf
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (F : Sheaf JC (Type (max u₁ u₂ v₁ v₂))) :
    Presieve.IsSheaf (JD.over V) (((Over.forget V).op ⋙ u.op) ⋙ F.obj) := by
  -- First use continuity of `u`, then continuity of the localized forgetful functor.
  exact
    (Over.forget V).op_comp_isSheaf_of_types (JD.over V) JD
      ⟨u.op ⋙ F.obj, (isSheaf_iff_isSheaf_of_type JD (u.op ⋙ F.obj)).2
        (u.op_comp_isSheaf_of_types JD JC F)⟩

/-- Helper for Lemma 7.28.1: the ambient lower-shriek sheaf `j_{u(V)!} ℋ` attached to a localized
sheaf `ℋ` on `(C/u(V), JC.over u(V))`. -/
private abbrev overPost_lowerShriek_obj
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    Sheaf JC (Type (max u₁ u₂ v₁ v₂)) :=
  ((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
    (JC.over (u.obj V)) JC).obj ℋ

/-- Helper for Lemma 7.28.1: after localizing `ℋ` to the ambient site by `j_{u(V)!}`, the
restriction of the resulting sheaf along `Over.forget V ⋙ u` is already a sheaf on `(D/V,
JD.over V)`. -/
private theorem overPost_lowerShriek_isSheaf_on_slice
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    Presieve.IsSheaf (JD.over V)
      (((Over.forget V).op ⋙ u.op) ⋙ (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj) := by
  -- This is exactly the ambient sheaf argument applied to `j_{u(V)!} ℋ`.
  exact overPost_ambient_restriction_isSheaf
    (u := u) (V := V) (F := overPost_lowerShriek_obj (u := u) (V := V) ℋ)

/-- Helper for Lemma 7.28.1: the ambient lower shriek `j_{u(V)!} ℋ` is computed by sheafifying
the raw left Kan extension of the underlying slice presheaf. -/
private noncomputable def overPost_lowerShriek_associatedSheafIso
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    overPost_lowerShriek_obj (u := u) (V := V) ℋ ≅
      (presheafToSheaf JC (Type (max u₁ u₂ v₁ v₂))).obj
        ((Over.forget (u.obj V)).op.lan.obj ℋ.obj) :=
  (((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
      (JC.over (u.obj V)) JC).mapIso (sheafificationIso ℋ)) ≪≫
    localization_lowerShriek_associatedSheafIso JC (u.obj V) ℋ.obj

/-- Helper for Lemma 7.28.1: the canonical section of `h[u(V)]^#` on `u(X)` determined by the
slice structure map `u(X) ⟶ u(V)`. -/
private noncomputable def overPost_basepoint_section
    (u : D ⥤ C) (V : D) (X : Over V) :
    (GrothendieckTopology.sheafifiedRepresentable JC (u.obj V)).obj.obj
      (op (u.obj X.left)) :=
  JC.uliftSheafifiedRepresentableHomEquiv
      (GrothendieckTopology.sheafifiedRepresentable JC (u.obj V))
      (u.obj X.left)
    (JC.sheafifiedRepresentableMap (u.map X.hom))

/-- Helper for Lemma 7.28.1: restricting the canonical basepoint section along a morphism in the
slice `D/V` gives the canonical basepoint section on the source. -/
private theorem overPost_basepoint_section_naturality
    (u : D ⥤ C) (V : D) {X Y : Over V} (g : Y ⟶ X) :
    (GrothendieckTopology.sheafifiedRepresentable JC (u.obj V)).obj.map (u.map g.left).op
        (overPost_basepoint_section (JC := JC) (u := u) (V := V) X) =
      overPost_basepoint_section (JC := JC) (u := u) (V := V) Y := by
  have hnat :=
    (JC.uliftSheafifiedRepresentableHomEquiv_naturality (u.map g.left)
      (GrothendieckTopology.sheafifiedRepresentable JC (u.obj V))
      (JC.sheafifiedRepresentableMap (u.map X.hom))).symm
  have hcomp :
      JC.sheafifiedRepresentableMap (u.map g.left) ≫
          JC.sheafifiedRepresentableMap (u.map X.hom) =
        JC.sheafifiedRepresentableMap (u.map Y.hom) := by
    -- The composite of representable maps is indexed by the composite
    -- `u(g) ≫ u(X ⟶ V) = u(Y ⟶ V)`.
    simpa [GrothendieckTopology.sheafifiedRepresentableMap, Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ JC.sheafifiedRepresentableMap (u.map k)) (Over.w g)
  calc
    (GrothendieckTopology.sheafifiedRepresentable JC (u.obj V)).obj.map (u.map g.left).op
        (overPost_basepoint_section (JC := JC) (u := u) (V := V) X) =
      JC.uliftSheafifiedRepresentableHomEquiv
        (GrothendieckTopology.sheafifiedRepresentable JC (u.obj V))
        (u.obj Y.left)
        (JC.sheafifiedRepresentableMap (u.map g.left) ≫
          JC.sheafifiedRepresentableMap (u.map X.hom)) := by
            simpa [overPost_basepoint_section] using hnat
    _ =
      JC.uliftSheafifiedRepresentableHomEquiv
        (GrothendieckTopology.sheafifiedRepresentable JC (u.obj V))
        (u.obj Y.left)
        (JC.sheafifiedRepresentableMap (u.map Y.hom)) := by
            exact congrArg
              (JC.uliftSheafifiedRepresentableHomEquiv
                (GrothendieckTopology.sheafifiedRepresentable JC (u.obj V))
                (u.obj Y.left))
              hcomp
    _ = overPost_basepoint_section (JC := JC) (u := u) (V := V) Y := by
          rfl

/-- Helper for Lemma 7.28.1: the canonical family of sections of `h[u(V)]^#` over a slice sieve.
-/
private noncomputable def overPost_basepoint_family
    (u : D ⥤ C) (V : D) {X : Over V} (S : Sieve X) :
    S.arrows.FamilyOfElements
      (((Over.forget V).op ⋙ u.op) ⋙
        (GrothendieckTopology.sheafifiedRepresentable JC (u.obj V)).obj) :=
  fun Y _f _hf ↦ overPost_basepoint_section (JC := JC) (u := u) (V := V) Y

/-- Helper for Lemma 7.28.1: the canonical basepoint sections form a compatible family on every
covering sieve of `X` in `D/V`. -/
private theorem overPost_basepoint_family_compatible
    (u : D ⥤ C) (V : D) {X : Over V} {S : Sieve X} :
    (overPost_basepoint_family (JC := JC) (u := u) (V := V) S).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hfg
  -- Both restrictions are the same canonical basepoint section on `u(Z)`.
  dsimp [overPost_basepoint_family]
  rw [overPost_basepoint_section_naturality (JC := JC) (u := u) (V := V) (g := g₁)]
  rw [overPost_basepoint_section_naturality (JC := JC) (u := u) (V := V) (g := g₂)]

/-- Helper for Lemma 7.28.1: the global basepoint section on `u(X)` is an amalgamation of the
canonical basepoint family on any sieve of `X`. -/
private theorem overPost_basepoint_isAmalgamation
    (u : D ⥤ C) (V : D) {X : Over V} {S : Sieve X} :
    (overPost_basepoint_family (JC := JC) (u := u) (V := V) S).IsAmalgamation
      (overPost_basepoint_section (JC := JC) (u := u) (V := V) X) := by
  intro Y f hf
  -- Restrict the global basepoint section along `f : Y ⟶ X` and use the previous naturality
  -- formula to identify the result with the local basepoint section on `Y`.
  simpa [overPost_basepoint_family] using
    overPost_basepoint_section_naturality (JC := JC) (u := u) (V := V) (g := f)

/-- Helper for Lemma 7.28.1: the large-universe basepoint section of the sheafified representable
of `u(V)` on the object `u(X)`. -/
private noncomputable def overPost_ulift_basepoint_section
    (u : D ⥤ C) (V : D) (X : Over V) :
    (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂}
        JC (u.obj V)).obj.obj (op (u.obj X.left)) :=
  (((sheafificationAdjunction JC (Type (max u₁ u₂ v₁ v₂))).unit.app
      ((CategoryTheory.uliftYoneda.{max u₁ u₂ v₁ v₂}.obj (u.obj V)) :
        Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂))).app
    (op (u.obj X.left))
    (ULift.up (u.map X.hom)))

/-- Helper for Lemma 7.28.1: restricting the large-universe basepoint section along a morphism in
`D/V` gives the large-universe basepoint section on the source. -/
private theorem overPost_ulift_basepoint_section_naturality
    (u : D ⥤ C) (V : D) {X Y : Over V} (g : Y ⟶ X) :
    (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂}
        JC (u.obj V)).obj.map (u.map g.left).op
        (overPost_ulift_basepoint_section (JC := JC) (u := u) (V := V) X) =
      overPost_ulift_basepoint_section (JC := JC) (u := u) (V := V) Y := by
  -- The sheafification unit is natural, and the underlying representable section is indexed by
  -- the composite map `u(g) ≫ u(X ⟶ V) = u(Y ⟶ V)`.
  let rawRep :
      Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂) :=
    (CategoryTheory.uliftYoneda.{max u₁ u₂ v₁ v₂}.obj (u.obj V))
  let η := (sheafificationAdjunction JC (Type (max u₁ u₂ v₁ v₂))).unit.app rawRep
  have hunit :
      (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂}
          JC (u.obj V)).obj.map (u.map g.left).op
          (η.app (op (u.obj X.left)) (ULift.up (u.map X.hom))) =
        η.app (op (u.obj Y.left))
          (rawRep.map (u.map g.left).op (ULift.up (u.map X.hom))) := by
    simpa [rawRep, η] using
      (congrFun (η.naturality (u.map g.left).op) (ULift.up (u.map X.hom))).symm
  have hcomp : u.map g.left ≫ u.map X.hom = u.map Y.hom := by
    simpa [Functor.map_comp] using congrArg (fun k ↦ u.map k) (Over.w g)
  have h₁ :
      (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂}
          JC (u.obj V)).obj.map (u.map g.left).op
          (overPost_ulift_basepoint_section (JC := JC) (u := u) (V := V) X) =
        η.app (op (u.obj Y.left)) (ULift.up (u.map g.left ≫ u.map X.hom)) := by
    simpa [overPost_ulift_basepoint_section, rawRep, η, CategoryTheory.uliftYoneda] using
      hunit
  have h₂ :
      η.app (op (u.obj Y.left)) (ULift.up (u.map g.left ≫ u.map X.hom)) =
        η.app (op (u.obj Y.left)) (ULift.up (u.map Y.hom)) := by
    exact congrArg (fun k ↦ η.app (op (u.obj Y.left)) (ULift.up k)) hcomp
  have h₃ :
      η.app (op (u.obj Y.left)) (ULift.up (u.map Y.hom)) =
        overPost_ulift_basepoint_section (JC := JC) (u := u) (V := V) Y := by
    rfl
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Lemma 7.28.1: the large-universe canonical family of sections of the sheafified
representable of `u(V)` over a slice sieve. -/
private noncomputable def overPost_ulift_basepoint_family
    (u : D ⥤ C) (V : D) {X : Over V} (S : Sieve X) :
    S.arrows.FamilyOfElements
      (((Over.forget V).op ⋙ u.op) ⋙
        (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂}
          JC (u.obj V)).obj) :=
  fun Y _f _hf ↦ overPost_ulift_basepoint_section (JC := JC) (u := u) (V := V) Y

/-- Helper for Lemma 7.28.1: the large-universe basepoint sections form a compatible family on
every covering sieve of `X` in `D/V`. -/
private theorem overPost_ulift_basepoint_family_compatible
    (u : D ⥤ C) (V : D) {X : Over V} {S : Sieve X} :
    (overPost_ulift_basepoint_family (JC := JC) (u := u) (V := V) S).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hfg
  -- Both restrictions are the same large-universe basepoint section on `u(Z)`.
  dsimp [overPost_ulift_basepoint_family]
  simpa [Functor.comp_map] using
    (overPost_ulift_basepoint_section_naturality (JC := JC) (u := u) (V := V) (g := g₁)).trans
      (overPost_ulift_basepoint_section_naturality (JC := JC) (u := u) (V := V) (g := g₂)).symm

/-- Helper for Lemma 7.28.1: the global large-universe basepoint section on `u(X)` is an
amalgamation of the large-universe canonical basepoint family on any sieve of `X`. -/
private theorem overPost_ulift_basepoint_isAmalgamation
    (u : D ⥤ C) (V : D) {X : Over V} {S : Sieve X} :
    (overPost_ulift_basepoint_family (JC := JC) (u := u) (V := V) S).IsAmalgamation
      (overPost_ulift_basepoint_section (JC := JC) (u := u) (V := V) X) := by
  intro Y f hf
  -- Restrict the global large-universe basepoint section along `f : Y ⟶ X` and use the previous
  -- naturality formula to identify the result with the local large-universe basepoint section.
  simpa [overPost_ulift_basepoint_family, Functor.comp_map] using
    overPost_ulift_basepoint_section_naturality (JC := JC) (u := u) (V := V) (g := f)

/-- Helper for Lemma 7.28.1: a section on the slice object `u(X)/u(V)` gives a section of the
ambient lower shriek `j_{u(V)!} ℋ` on the underlying object `u(X)`. -/
private noncomputable def overPost_local_section_to_lowerShriek
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    (X : Over V) :
    ℋ.obj.obj (op ((Over.post u).obj X)) →
      (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj.obj (op (u.obj X.left)) :=
  fun s ↦
    (overPost_lowerShriek_associatedSheafIso (u := u) (V := V) ℋ).inv.1.app
      (op (u.obj X.left))
      (((sheafificationAdjunction JC (Type (max u₁ u₂ v₁ v₂))).unit.app
          ((Over.forget (u.obj V)).op.lan.obj ℋ.obj)).app
        (op (u.obj X.left))
        ((((Over.forget (u.obj V)).op.leftKanExtensionUnit ℋ.obj).app
            (op ((Over.post u).obj X))) s))

/-- Helper for Lemma 7.28.1: the inclusion of slice sections into the ambient lower shriek is
natural with respect to morphisms in `D/V`. -/
private theorem overPost_local_section_to_lowerShriek_naturality
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    {X Y : Over V} (f : Y ⟶ X)
    (s : ℋ.obj.obj (op ((Over.post u).obj X))) :
    (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj.map (u.map f.left).op
        (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s) =
      overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y
        (ℋ.obj.map ((Over.post u).map f).op s) := by
  -- Route correction: the subcanonical sigma-model from Lemma 7.27.1 is not available under the
  -- current hypotheses, so this direct naturality statement must be proved from the ambient
  -- associated-sheaf/unit description already used in the definition above.
  let e := overPost_lowerShriek_associatedSheafIso (u := u) (V := V) ℋ
  let F := ((Over.forget (u.obj V)).op.lan.obj ℋ.obj)
  let SF := ((presheafToSheaf JC (Type (max u₁ u₂ v₁ v₂))).obj F).obj
  let η := (sheafificationAdjunction JC (Type (max u₁ u₂ v₁ v₂))).unit.app F
  let t :=
    ((((Over.forget (u.obj V)).op.leftKanExtensionUnit ℋ.obj).app
      (op ((Over.post u).obj X))) s)
  -- First move the ambient restriction across the comparison isomorphism `e`.
  have hIso :
      (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj.map (u.map f.left).op
          ((e.inv.hom.app (op (u.obj X.left))) (η.app (op (u.obj X.left)) t)) =
        (e.inv.hom.app (op (u.obj Y.left)))
          (SF.map (u.map f.left).op (η.app (op (u.obj X.left)) t)) := by
    simpa [e, F, SF, η, t] using
      (congrFun (e.inv.hom.naturality (u.map f.left).op) (η.app (op (u.obj X.left)) t)).symm
  -- Next rewrite the sheafification unit along `u.map f.left`.
  have hUnit :
      SF.map (u.map f.left).op (η.app (op (u.obj X.left)) t) =
        η.app (op (u.obj Y.left)) (F.map (u.map f.left).op t) := by
    simpa [F, SF, η] using
      (congrFun (η.naturality (u.map f.left).op) t).symm
  -- Finally transport the generator through the raw left Kan extension unit.
  have hLan :
      F.map (u.map f.left).op t =
        (((Over.forget (u.obj V)).op.leftKanExtensionUnit ℋ.obj).app
          (op ((Over.post u).obj Y)))
          (ℋ.obj.map ((Over.post u).map f).op s) := by
    simpa [F, t, Functor.comp_map] using
      (congrFun (((Over.forget (u.obj V)).op.leftKanExtensionUnit ℋ.obj).naturality
        ((Over.post u).map f).op) s).symm
  calc
    (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj.map (u.map f.left).op
        (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s) =
      (e.inv.hom.app (op (u.obj Y.left)))
        (SF.map (u.map f.left).op (η.app (op (u.obj X.left)) t)) := by
          simpa [overPost_local_section_to_lowerShriek, e, F, SF, η, t] using hIso
    _ =
      (e.inv.hom.app (op (u.obj Y.left)))
        (η.app (op (u.obj Y.left)) (F.map (u.map f.left).op t)) := by
          rw [hUnit]
    _ =
      (e.inv.hom.app (op (u.obj Y.left)))
        (η.app (op (u.obj Y.left))
          ((((Over.forget (u.obj V)).op.leftKanExtensionUnit ℋ.obj).app
            (op ((Over.post u).obj Y)))
            (ℋ.obj.map ((Over.post u).map f).op s))) := by
              rw [hLan]
    _ =
      overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y
        (ℋ.obj.map ((Over.post u).map f).op s) := by
          rfl

/-- Helper for Lemma 7.28.1: the transported compatible family in `j_{u(V)!} ℋ` is now recorded
explicitly, arrow by arrow, over the original slice covering sieve. -/
private noncomputable def overPost_family_to_lowerShriek
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    {X : Over V} {S : Sieve X}
    (x : S.arrows.FamilyOfElements ((Over.post u).op ⋙ ℋ.obj)) :
    S.arrows.FamilyOfElements
      (((Over.forget V).op ⋙ u.op) ⋙ (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj) :=
  fun Y f hf ↦
    -- Each slice section is included into the ambient lower shriek on the same covering arrow.
    overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y (x f hf)

/-- Helper for Lemma 7.28.1: source-faithful remaining bridge. A compatible family on the slice
presheaf `((Over.post u).op ⋙ ℋ.obj)` should first be embedded into the ambient lower-shriek
`j_{u(V)!} ℋ`, still over the same covering sieve in `D/V`. -/
private theorem overPost_family_transport_to_lowerShriek
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    {X : Over V} {S : Sieve X}
    (x : S.arrows.FamilyOfElements ((Over.post u).op ⋙ ℋ.obj))
    (hx : x.Compatible) :
    ∃ y : S.arrows.FamilyOfElements
        (((Over.forget V).op ⋙ u.op) ⋙ (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj),
      y.Compatible := by
  refine ⟨overPost_family_to_lowerShriek (u := u) (V := V) ℋ x, ?_⟩
  -- Route correction: the family is now explicit. Compatibility should be proved by rewriting the
  -- two ambient restrictions with `overPost_local_section_to_lowerShriek_naturality` and then
  -- invoking the original slice compatibility `hx`.
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hfg
  dsimp [overPost_family_to_lowerShriek]
  rw [overPost_local_section_to_lowerShriek_naturality
    (u := u) (V := V) (ℋ := ℋ) (f := g₁) (s := x f₁ hf₁)]
  rw [overPost_local_section_to_lowerShriek_naturality
    (u := u) (V := V) (ℋ := ℋ) (f := g₂) (s := x f₂ hf₂)]
  -- The remaining equality is exactly the original compatibility, now pushed through the same
  -- inclusion into the ambient lower shriek on `u.obj Z.left`.
  have hx' :
      ℋ.obj.map ((Over.post u).map g₁).op (x f₁ hf₁) =
        ℋ.obj.map ((Over.post u).map g₂).op (x f₂ hf₂) := by
    simpa [Functor.comp_map] using hx g₁ g₂ hf₁ hf₂ hfg
  exact congrArg (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Z) hx'

/-- Helper for Lemma 7.28.1: applying `Over.map f` to the terminal object of `Over V`
recovers the object indexed by `f`. -/
private theorem over_map_obj_terminal_eq
    {U V : C} (f : V ⟶ U) :
    (Over.map f).obj (Over.mk (𝟙 V)) = Over.mk f := by
  -- The terminal slice object carries the identity arrow, so postcomposition gives `f`.
  change Over.mk ((𝟙 V) ≫ f) = Over.mk f
  simp

/-- Helper for Lemma 7.28.1: evaluating the relocalized sheaf along `u.map X.hom` at the
terminal object of `Over (u(X))` recovers the original section type on `u(X)/u(V)`. -/
private theorem overPost_overMapPullback_obj_terminal
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    (X : Over V) :
    (((JC.overMapPullback (Type (max u₁ u₂ v₁ v₂)) (u.map X.hom)).obj ℋ).obj.obj
      (op (Over.mk (𝟙 (u.obj X.left))))) =
      ℋ.obj.obj (op ((Over.post u).obj X)) := by
  -- Unfold the slice pullback once and rewrite the terminal object to the arrow `u.map X.hom`.
  simp [GrothendieckTopology.overMapPullback, Over.post, over_map_obj_terminal_eq]

/-- Helper for Lemma 7.28.1: after transporting a slice section into the ambient lower shriek and
then across the associated-sheaf comparison, we recover the sheafification unit applied to the raw
left-Kan-extension generator. -/
private theorem overPost_local_section_to_lowerShriek_associatedSheafIso_hom
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    (X : Over V)
    (s : ℋ.obj.obj (op ((Over.post u).obj X))) :
    (overPost_lowerShriek_associatedSheafIso (u := u) (V := V) ℋ).hom.hom.app
        (op (u.obj X.left))
        (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s) =
      (((sheafificationAdjunction JC (Type (max u₁ u₂ v₁ v₂))).unit.app
          ((Over.forget (u.obj V)).op.lan.obj ℋ.obj)).app
        (op (u.obj X.left))
        ((((Over.forget (u.obj V)).op.leftKanExtensionUnit ℋ.obj).app
          (op ((Over.post u).obj X))) s)) := by
  -- This is just the cancellation of `overPost_lowerShriek_associatedSheafIso.hom` with the
  -- inverse used in the definition of `overPost_local_section_to_lowerShriek`.
  let e := (sheafToPresheaf JC (Type (max u₁ u₂ v₁ v₂))).mapIso
    (overPost_lowerShriek_associatedSheafIso (u := u) (V := V) ℋ)
  let z :=
    (((sheafificationAdjunction JC (Type (max u₁ u₂ v₁ v₂))).unit.app
        ((Over.forget (u.obj V)).op.lan.obj ℋ.obj)).app
      (op (u.obj X.left))
      ((((Over.forget (u.obj V)).op.leftKanExtensionUnit ℋ.obj).app
        (op ((Over.post u).obj X))) s))
  have hcomp :
      e.hom.app (op (u.obj X.left)) (e.inv.app (op (u.obj X.left)) z) = z := by
    simpa [z] using
      CategoryTheory.FunctorToTypes.inv_hom_id_app_apply
        ((overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj)
        (((presheafToSheaf JC (Type (max u₁ u₂ v₁ v₂))).obj
          ((Over.forget (u.obj V)).op.lan.obj ℋ.obj)).obj)
        e (op (u.obj X.left)) z
  simpa [overPost_local_section_to_lowerShriek, e, z] using hcomp

/-- Helper for Lemma 7.28.1: the ambient lower-shriek functor preserves identity morphisms. -/
private theorem overPost_lowerShriek_map_id
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    ((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
      (JC.over (u.obj V)) JC).map (𝟙 ℋ) = 𝟙 _ := by
  -- This is the identity law for the ambient sheaf-pullback functor defining `j_{u(V)!}`.
  simp

/-- Helper for Lemma 7.28.1: the associated-sheaf comparison for `j_{u(V)!}` is natural in the
sheaf argument. -/
private theorem overPost_lowerShriek_associatedSheafIso_naturality
    (u : D ⥤ C) (V : D)
    {ℋ ℋ' : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))}
    (η : ℋ ⟶ ℋ') :
    (((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
        (JC.over (u.obj V)) JC).map η) ≫
      (overPost_lowerShriek_associatedSheafIso (u := u) (V := V) ℋ').hom =
    (overPost_lowerShriek_associatedSheafIso (u := u) (V := V) ℋ).hom ≫
      (presheafToSheaf JC (Type (max u₁ u₂ v₁ v₂))).map
        (((Over.forget (u.obj V)).op.lan).map η.hom) := by
  -- Route correction: this is the same cancellation pattern as in Lemma 7.25.4. After moving to
  -- the sheafification/unit model, the only content is cancelling the two isomorphisms coming
  -- from sheafifying `((Over.forget (u.obj V)).op.lan).map (toSheafify ...)`.
  let F := presheafToSheaf JC (Type (max u₁ u₂ v₁ v₂))
  let L :=
    Functor.sheafPullbackConstruction.sheafPullback
      (Over.forget (u.obj V)) (Type (max u₁ u₂ v₁ v₂))
      (JC.over (u.obj V)) JC
  have hsimpl :
      L.map η ≫
          (asIso (F.map (((Over.forget (u.obj V)).op.lan).map
            (CategoryTheory.toSheafify (JC.over (u.obj V)) ℋ'.obj)))).inv =
        (asIso (F.map (((Over.forget (u.obj V)).op.lan).map
          (CategoryTheory.toSheafify (JC.over (u.obj V)) ℋ.obj)))).inv ≫
          F.map (((Over.forget (u.obj V)).op.lan).map η.hom) := by
    have hnat :
        F.map (((Over.forget (u.obj V)).op.lan).map η.hom) ≫
            F.map (((Over.forget (u.obj V)).op.lan).map
              (CategoryTheory.toSheafify (JC.over (u.obj V)) ℋ'.obj)) =
          F.map (((Over.forget (u.obj V)).op.lan).map
              (CategoryTheory.toSheafify (JC.over (u.obj V)) ℋ.obj)) ≫
            L.map η := by
      -- The constructed lower shriek is `sheafToPresheaf ⋙ lan ⋙ presheafToSheaf`, so this is
      -- exactly the transported naturality of `toSheafify`.
      dsimp [F, L]
      simp [Functor.sheafPullbackConstruction.sheafPullback, ← Functor.map_comp]
    let i := asIso (F.map (((Over.forget (u.obj V)).op.lan).map
      (CategoryTheory.toSheafify (JC.over (u.obj V)) ℋ.obj)))
    let i' := asIso (F.map (((Over.forget (u.obj V)).op.lan).map
      (CategoryTheory.toSheafify (JC.over (u.obj V)) ℋ'.obj)))
    have hrew :
        i.hom ≫ L.map η =
          F.map (((Over.forget (u.obj V)).op.lan).map η.hom) ≫ i'.hom := by
      simpa [i, i', Category.assoc] using hnat.symm
    have hrew' :
        L.map η = i.inv ≫ F.map (((Over.forget (u.obj V)).op.lan).map η.hom) ≫ i'.hom := by
      simpa [Category.assoc] using congrArg (fun k ↦ i.inv ≫ k) hrew
    rw [hrew']
    change
      (((i.inv ≫ F.map (((Over.forget (u.obj V)).op.lan).map η.hom)) ≫ i'.hom) ≫ i'.inv =
        i.inv ≫ F.map (((Over.forget (u.obj V)).op.lan).map η.hom))
    simp [Category.assoc]
  -- After unfolding `overPost_lowerShriek_associatedSheafIso`, the formal `mapIso` layer and the
  -- intermediate `eqToIso rfl` cancel, leaving exactly `hsimpl`.
  simpa [overPost_lowerShriek_associatedSheafIso, Category.assoc] using hsimpl

/-- Helper for Lemma 7.28.1: embedding a local slice section into `j_{u(V)!}` is natural in the
source sheaf. -/
private theorem overPost_local_section_to_lowerShriek_map
    (u : D ⥤ C) (V : D)
    {ℋ ℋ' : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))}
    (η : ℋ ⟶ ℋ')
    (X : Over V)
    (s : ℋ.obj.obj (op ((Over.post u).obj X))) :
    ((((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
          (JC.over (u.obj V)) JC).map η).hom.app (op (u.obj X.left)))
        (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s) =
      overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ' X
        (η.hom.app (op ((Over.post u).obj X)) s) := by
  -- Push both sides across the associated-sheaf comparison for `j_{u(V)!}` and then rewrite the
  -- resulting section identity using the naturality square proved just above.
  let e := overPost_lowerShriek_associatedSheafIso (u := u) (V := V) ℋ
  let e' := overPost_lowerShriek_associatedSheafIso (u := u) (V := V) ℋ'
  let F := ((Over.forget (u.obj V)).op.lan.obj ℋ.obj)
  let F' := ((Over.forget (u.obj V)).op.lan.obj ℋ'.obj)
  let ηF := (sheafificationAdjunction JC (Type (max u₁ u₂ v₁ v₂))).unit.app F
  let ηF' := (sheafificationAdjunction JC (Type (max u₁ u₂ v₁ v₂))).unit.app F'
  let t :=
    (((Over.forget (u.obj V)).op.leftKanExtensionUnit ℋ.obj).app
      (op ((Over.post u).obj X))) s
  have hIso :
      (e'.hom.hom.app (op (u.obj X.left)))
          ((((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
              (JC.over (u.obj V)) JC).map η).hom.app (op (u.obj X.left))
            (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s)) =
        (((presheafToSheaf JC (Type (max u₁ u₂ v₁ v₂))).map
            (((Over.forget (u.obj V)).op.lan).map η.hom)).hom.app
          (op (u.obj X.left)))
          ((e.hom.hom.app (op (u.obj X.left)))
            (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s)) := by
    -- Evaluate the morphism equality from the naturality square on the chosen local section.
    simpa [Category.assoc] using
      congrFun
        (congrArg (fun k ↦ k.hom.app (op (u.obj X.left)))
          (overPost_lowerShriek_associatedSheafIso_naturality
            (JC := JC) (u := u) (V := V) η))
        (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s)
  have hUnit :
      (((presheafToSheaf JC (Type (max u₁ u₂ v₁ v₂))).map
          (((Over.forget (u.obj V)).op.lan).map η.hom)).hom.app
        (op (u.obj X.left)))
        (ηF.app (op (u.obj X.left)) t) =
      ηF'.app (op (u.obj X.left))
        ((((Over.forget (u.obj V)).op.lan).map η.hom).app (op (u.obj X.left)) t) := by
    -- Rewrite the objectwise statement back to the owner theorem `toSheafify_naturality`.
    change
      (((CategoryTheory.toSheafify JC F ≫
          CategoryTheory.sheafifyMap JC
            (((Over.forget (u.obj V)).op.lan).map η.hom)).app
          (op (u.obj X.left))) t) =
        ((((Over.forget (u.obj V)).op.lan).map η.hom ≫
            CategoryTheory.toSheafify JC F').app
          (op (u.obj X.left))) t)
    rw [← CategoryTheory.toSheafify_naturality
      (J := JC) (((Over.forget (u.obj V)).op.lan).map η.hom)]
  have hLan :
      (((Over.forget (u.obj V)).op.lan).map η.hom).app (op (u.obj X.left)) t =
        (((Over.forget (u.obj V)).op.leftKanExtensionUnit ℋ'.obj).app
          (op ((Over.post u).obj X)))
          (η.hom.app (op ((Over.post u).obj X)) s) := by
    -- This is the defining comparison identity for `((Over.forget (u.obj V)).op.lan).map η.hom`
    -- obtained from the universal property of the chosen left Kan extension.
    simpa [t, Functor.comp_map] using
      congrArg (fun k ↦ k s)
        (Functor.descOfIsLeftKanExtension_fac_app
          (F' := (Over.forget (u.obj V)).op.leftKanExtension ℋ.obj)
          (α := (Over.forget (u.obj V)).op.leftKanExtensionUnit ℋ.obj)
          (G := (Over.forget (u.obj V)).op.leftKanExtension ℋ'.obj)
          (β := η.hom ≫ (Over.forget (u.obj V)).op.leftKanExtensionUnit ℋ'.obj)
          (op ((Over.post u).obj X)))
  have hImage :
      (e'.hom.hom.app (op (u.obj X.left)))
          ((((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
              (JC.over (u.obj V)) JC).map η).hom.app (op (u.obj X.left))
            (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s)) =
        (e'.hom.hom.app (op (u.obj X.left)))
          (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ' X
            (η.hom.app (op ((Over.post u).obj X)) s)) := by
    -- Rewrite the image of the left-hand side through the proved naturality square, then identify
    -- both sides by the explicit section formula after crossing `e'`.
    calc
      (e'.hom.hom.app (op (u.obj X.left)))
          ((((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
              (JC.over (u.obj V)) JC).map η).hom.app (op (u.obj X.left))
            (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s)) =
        (((presheafToSheaf JC (Type (max u₁ u₂ v₁ v₂))).map
            (((Over.forget (u.obj V)).op.lan).map η.hom)).hom.app
          (op (u.obj X.left)))
          ((e.hom.hom.app (op (u.obj X.left)))
            (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s)) := hIso
      _ =
        (((presheafToSheaf JC (Type (max u₁ u₂ v₁ v₂))).map
            (((Over.forget (u.obj V)).op.lan).map η.hom)).hom.app
          (op (u.obj X.left)))
          (ηF.app (op (u.obj X.left)) t) := by
            rw [overPost_local_section_to_lowerShriek_associatedSheafIso_hom
              (JC := JC) (u := u) (V := V) (ℋ := ℋ) (X := X) (s := s)]
      _ =
        ηF'.app (op (u.obj X.left))
          ((((Over.forget (u.obj V)).op.lan).map η.hom).app (op (u.obj X.left)) t) := hUnit
      _ =
        ηF'.app (op (u.obj X.left))
          ((((Over.forget (u.obj V)).op.leftKanExtensionUnit ℋ'.obj).app
            (op ((Over.post u).obj X)))
            (η.hom.app (op ((Over.post u).obj X)) s)) := by
              rw [hLan]
      _ =
        (e'.hom.hom.app (op (u.obj X.left)))
          (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ' X
            (η.hom.app (op ((Over.post u).obj X)) s)) := by
              rw [overPost_local_section_to_lowerShriek_associatedSheafIso_hom
                (JC := JC) (u := u) (V := V) (ℋ := ℋ') (X := X)
                (s := η.hom.app (op ((Over.post u).obj X)) s)]
  -- Apply the inverse component of `e'` to cancel the comparison isomorphism and recover the
  -- desired equality in `j_{u(V)!}` itself.
  have hCancel :=
    congrArg ((e'.inv.hom.app (op (u.obj X.left)))) hImage
  simpa [e'] using hCancel


/-- Helper for Lemma 7.28.1: composing type-valued sheaves with the ambient `ULift` functor
preserves the sheaf condition on any site appearing in this proof. -/
private instance uliftFunctor_hasSheafCompose_type
    {E : Type u₁} [Category.{v₁} E] (L : GrothendieckTopology E) :
    L.HasSheafCompose
      (CategoryTheory.uliftFunctor :
        Type (max u₁ u₂ v₁ v₂) ⥤ Type (max w (max u₁ u₂ v₁ v₂))) where
  isSheaf P hP := by
    -- Reduce to the concrete type-valued sheaf condition where `ULift` is stable.
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_comp_uliftFunctor (J := L)
      ((isSheaf_iff_isSheaf_of_type L P).1 hP)

/-- Helper for Lemma 7.28.1: the slice sheafness goal is unchanged after whiskering by the ambient
`ULift` functor. -/
private theorem overPost_op_comp_isSheaf_iff_ulift
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    Presieve.IsSheaf (JD.over V)
        (((Over.post u).op ⋙ ℋ.obj) ⋙
          (CategoryTheory.uliftFunctor :
            Type (max u₁ u₂ v₁ v₂) ⥤ Type (max w (max u₁ u₂ v₁ v₂)))) ↔
      Presieve.IsSheaf (JD.over V) ((Over.post u).op ⋙ ℋ.obj) := by
  -- This is exactly the standard `ULift`-invariance of the type-valued sheaf condition.
  exact
    (Presieve.isSheaf_comp_uliftFunctor_iff
      (J := JD.over V) (P := (Over.post u).op ⋙ ℋ.obj))


/-- Helper for Lemma 7.28.1: the source identity
`j_{u(V)!} ∘ u'^* ≅ u^* ∘ j_{V!}` is the canonical pullback-composition comparison for the strict
equality `Over.post u ⋙ Over.forget (u.obj V) = Over.forget V ⋙ u`. -/
private noncomputable def overPost_composite_sheafPullback_iso
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    [Functor.IsContinuous (Over.post u) (JD.over V) (JC.over (u.obj V))]
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), (Over.post u).op.HasLeftKanExtension P]
    [∀ P : (Over (u.obj V))ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂),
      (Over.forget (u.obj V)).op.HasLeftKanExtension P]
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), (Over.forget V).op.HasLeftKanExtension P]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), u.op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify JD (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify JC (Type (max u₁ u₂ v₁ v₂))] :
    (Over.post u).sheafPullback (Type (max u₁ u₂ v₁ v₂)) (JD.over V) (JC.over (u.obj V)) ⋙
        (Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
          (JC.over (u.obj V)) JC ≅
      (Over.forget V).sheafPullback (Type (max u₁ u₂ v₁ v₂)) (JD.over V) JD ⋙
        u.sheafPullback (Type (max u₁ u₂ v₁ v₂)) JD JC := by
  let A := Type (max u₁ u₂ v₁ v₂)
  letI : Functor.IsContinuous (Over.forget V ⋙ u) (JD.over V) JC :=
    Functor.isContinuous_comp (Over.forget V) u (JD.over V) JD JC
  let leftIso :
      (Over.post u).sheafPullback A (JD.over V) (JC.over (u.obj V)) ⋙
          (Over.forget (u.obj V)).sheafPullback A (JC.over (u.obj V)) JC ≅
        (Over.forget V ⋙ u).sheafPullback A (JD.over V) JC :=
    -- First collapse the slice lower-shriek with the ambient localization functor.
    Functor.sheafPullbackComp'
      (JD.over V) (JC.over (u.obj V)) JC (Over.post u) (Over.forget (u.obj V))
      (eqToIso (overPost_comp_forget_eq u V))
  let rightIso :
      (Over.forget V).sheafPullback A (JD.over V) JD ⋙ u.sheafPullback A JD JC ≅
        (Over.forget V ⋙ u).sheafPullback A (JD.over V) JC :=
    -- Then identify the ambient composite with `u^* ∘ j_{V!}`.
    Functor.sheafPullbackComp'
      (JD.over V) JD JC (Over.forget V) u (Iso.refl _)
  exact leftIso ≪≫ rightIso.symm

/-- Helper for Lemma 7.28.1: objectwise form of
`overPost_composite_sheafPullback_iso`, evaluated at a sheaf on `(C/u(V), JC.over u(V))`. -/
private noncomputable def overPost_composite_sheafPullback_iso_app
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    [Functor.IsContinuous (Over.post u) (JD.over V) (JC.over (u.obj V))]
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), (Over.post u).op.HasLeftKanExtension P]
    [∀ P : (Over (u.obj V))ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂),
      (Over.forget (u.obj V)).op.HasLeftKanExtension P]
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), (Over.forget V).op.HasLeftKanExtension P]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂), u.op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify JD (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify JC (Type (max u₁ u₂ v₁ v₂))]
    (ℋ : Sheaf (JD.over V) (Type (max u₁ u₂ v₁ v₂))) :
    (((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
          (JC.over (u.obj V)) JC).obj
        (((Over.post u).sheafPullback (Type (max u₁ u₂ v₁ v₂))
            (JD.over V) (JC.over (u.obj V))).obj ℋ)) ≅
      ((u.sheafPullback (Type (max u₁ u₂ v₁ v₂)) JD JC).obj
        (((Over.forget V).sheafPullback (Type (max u₁ u₂ v₁ v₂))
            (JD.over V) JD).obj ℋ)) := by
  -- Evaluate the functor-level comparison at `ℋ`.
  simpa using (overPost_composite_sheafPullback_iso (u := u) (V := V)).app ℋ

/-- Helper for Lemma 7.28.1: in the default localization universe, the sheafified representable
of the identity object is terminal on `(C/U, JC.over U)`. -/
private noncomputable def localized_identity_uliftSheafifiedRepresentable_iso_terminal
    (U : C)
    [HasWeakSheafify (JC.over U) (Type (max u₁ v₁))] :
    (JC.over U).uliftSheafifiedRepresentable (Over.mk (𝟙 U)) ≅
      Sheaf.terminal (JC.over U) Types.isTerminalPUnit := by
  let yonedaOver : Over U ⥤ (Over U)ᵒᵖ ⥤ Type (max u₁ v₁) :=
    CategoryTheory.uliftYoneda.{max u₁ v₁}
  let hRep :
      IsTerminal
        ((yonedaOver.obj (Over.mk (𝟙 U))) :
          (Over U)ᵒᵖ ⥤ Type (max u₁ v₁)) :=
    -- The identity object is terminal in the slice, so its representable presheaf is terminal.
    IsTerminal.isTerminalObj yonedaOver (Over.mk (𝟙 U)) Over.mkIdTerminal
  let e :
      ((CategoryTheory.uliftYoneda.{max u₁ v₁}.obj (Over.mk (𝟙 U))) :
        (Over U)ᵒᵖ ⥤ Type (max u₁ v₁)) ≅
        (Functor.const (Over U)ᵒᵖ).obj (PUnit : Type (max u₁ v₁)) :=
    IsTerminal.uniqueUpToIso hRep <|
      Functor.isTerminalConst (Over U)ᵒᵖ Types.isTerminalPUnit
  -- Sheafifying the terminal representable gives the terminal sheaf on the localized site.
  simpa [GrothendieckTopology.uliftSheafifiedRepresentable] using
    (Functor.mapIso (presheafToSheaf (JC.over U) (Type (max u₁ v₁))) e ≪≫
      (sheafificationIso
        (Sheaf.terminal (JC.over U) Types.isTerminalPUnit)).symm)

/-- Helper for Lemma 7.28.1: the sheafified representable of the identity arrow is terminal on the
localized site in the default universe. -/
private noncomputable instance localized_identity_uliftSheafifiedRepresentable_isTerminal
    (U : C)
    [HasWeakSheafify (JC.over U) (Type (max u₁ v₁))] :
    IsTerminal ((JC.over U).uliftSheafifiedRepresentable (Over.mk (𝟙 U))) := by
  -- Transport terminality across the explicit terminal-object comparison above.
  exact IsTerminal.ofIso
    (Sheaf.isTerminalTerminal (JC.over U) Types.isTerminalPUnit)
    (localized_identity_uliftSheafifiedRepresentable_iso_terminal
      (JC := JC) U).symm

/-- Helper for Lemma 7.28.1: the default-universe terminal arrow from a localized sheaf to the
identity representable. This is the small-universe fragment that still needs a large-universe
`ULift` transport in the main proof. -/
private noncomputable def localized_identity_uliftSheafifiedRepresentable_terminal_hom
    (U : C)
    [HasWeakSheafify (JC.over U) (Type (max u₁ v₁))]
    (ℋ : Sheaf (JC.over U) (Type (max u₁ v₁))) :
    ℋ ⟶ (JC.over U).uliftSheafifiedRepresentable (Over.mk (𝟙 U)) :=
  -- The unique map into a terminal object is the source-faithful structure morphism.
  (localized_identity_uliftSheafifiedRepresentable_isTerminal
    (JC := JC) U).from ℋ

/-- Helper for Lemma 7.28.1: in any extra universe `w`, the sheafified representable of the
identity object is terminal on `(C/U, JC.over U)`. -/
private noncomputable def localized_identity_uliftSheafifiedRepresentable_iso_terminal_ulift
    (U : C)
    [HasWeakSheafify (JC.over U) (Type (max w u₁ v₁))] :
    GrothendieckTopology.uliftSheafifiedRepresentable.{w, max u₁ v₁, v₁}
        (JC.over U) (Over.mk (𝟙 U)) ≅
      Sheaf.terminal (JC.over U) Types.isTerminalPUnit := by
  let yonedaOver : Over U ⥤ (Over U)ᵒᵖ ⥤ Type (max w u₁ v₁) :=
    CategoryTheory.uliftYoneda.{max w u₁ v₁}
  let hRep :
      IsTerminal
        ((yonedaOver.obj (Over.mk (𝟙 U))) :
          (Over U)ᵒᵖ ⥤ Type (max w u₁ v₁)) :=
    -- The identity object is terminal in the slice, so its representable presheaf is terminal.
    IsTerminal.isTerminalObj yonedaOver (Over.mk (𝟙 U)) Over.mkIdTerminal
  let e :
      ((CategoryTheory.uliftYoneda.{max w u₁ v₁}.obj (Over.mk (𝟙 U))) :
        (Over U)ᵒᵖ ⥤ Type (max w u₁ v₁)) ≅
        (Functor.const (Over U)ᵒᵖ).obj (PUnit : Type (max w u₁ v₁)) :=
    IsTerminal.uniqueUpToIso hRep <|
      Functor.isTerminalConst (Over U)ᵒᵖ Types.isTerminalPUnit
  -- Sheafifying the terminal representable in the chosen universe still gives the terminal sheaf.
  simpa [GrothendieckTopology.uliftSheafifiedRepresentable] using
    (Functor.mapIso (presheafToSheaf (JC.over U) (Type (max w u₁ v₁))) e ≪≫
      (sheafificationIso
        (Sheaf.terminal (JC.over U) Types.isTerminalPUnit)).symm)

/-- Helper for Lemma 7.28.1: the universe-polymorphic sheafified identity representable is
terminal on the localized site. -/
private noncomputable instance localized_identity_uliftSheafifiedRepresentable_isTerminal_ulift
    (U : C)
    [HasWeakSheafify (JC.over U) (Type (max w u₁ v₁))] :
    IsTerminal
      (GrothendieckTopology.uliftSheafifiedRepresentable.{w, max u₁ v₁, v₁}
        (JC.over U) (Over.mk (𝟙 U))) := by
  -- Transport terminality across the explicit universe-polymorphic comparison.
  exact IsTerminal.ofIso
    (Sheaf.isTerminalTerminal (JC.over U) Types.isTerminalPUnit)
    (localized_identity_uliftSheafifiedRepresentable_iso_terminal_ulift
      (JC := JC) U).symm

/-- Helper for Lemma 7.28.1: the unique morphism from a localized sheaf to the identity
representable in any extra universe `w`. -/
private noncomputable def localized_identity_uliftSheafifiedRepresentable_terminal_hom_ulift
    (U : C)
    [HasWeakSheafify (JC.over U) (Type (max w u₁ v₁))]
    (ℋ : Sheaf (JC.over U) (Type (max w u₁ v₁))) :
    ℋ ⟶ GrothendieckTopology.uliftSheafifiedRepresentable.{w, max u₁ v₁, v₁}
      (JC.over U) (Over.mk (𝟙 U)) :=
  -- The unique map into the terminal localized representable is the source-faithful structure map.
  (localized_identity_uliftSheafifiedRepresentable_isTerminal_ulift
    (JC := JC) U).from ℋ

/-- Helper for Lemma 7.28.1: in the large target universe, the localized identity representable
maps to itself by the identity terminal morphism. -/
private theorem localized_identity_uliftSheafifiedRepresentable_terminal_from_self
    (U : C)
    [HasWeakSheafify (JC.over U) (Type (max w u₁ v₁))] :
    localized_identity_uliftSheafifiedRepresentable_terminal_hom_ulift
        (JC := JC) U
        (GrothendieckTopology.uliftSheafifiedRepresentable.{w, max u₁ v₁, v₁}
          (JC.over U) (Over.mk (𝟙 U))) =
      𝟙 _ := by
  -- Both endomorphisms of a terminal object coincide.
  exact
    (localized_identity_uliftSheafifiedRepresentable_isTerminal_ulift
      (JC := JC) U).hom_ext _ _

/-- Helper for Lemma 7.28.1: in the large target universe, the canonical map from a localized
representable to the terminal localized representable is the map induced by its structure arrow.
-/
private theorem localized_identity_uliftSheafifiedRepresentable_terminal_map
    (U : C)
    [HasWeakSheafify (JC.over U) (Type (max w u₁ v₁))]
    (X : Over U) :
    localized_identity_uliftSheafifiedRepresentable_terminal_hom_ulift
        (JC := JC) U
        (GrothendieckTopology.uliftSheafifiedRepresentable.{w, max u₁ v₁, v₁}
          (JC.over U) X) =
      (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, max u₁ v₁, v₁}
          (JC.over U)).map
        (show X ⟶ Over.mk (𝟙 U) from Over.homMk X.hom) := by
  -- The terminal localized representable receives a unique morphism from every object.
  exact
    (localized_identity_uliftSheafifiedRepresentable_isTerminal_ulift
      (JC := JC) U).hom_ext _ _

/-- Helper for Lemma 7.28.1: applying `j_{u(V)!}` to the terminal arrow on the localized site
produces the source-level structure morphism into the localized identity representable. The
remaining blocker is the large-universe comparison from this localized target to the ambient
representable `h[u(V)]^#`. -/
private noncomputable def overPost_localized_terminal_hom
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    overPost_lowerShriek_obj (u := u) (V := V) ℋ ⟶
      ((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
        (JC.over (u.obj V)) JC).obj
        (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
          (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V)))) :=
  let τ :
      ℋ ⟶
        GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
          (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V))) :=
    localized_identity_uliftSheafifiedRepresentable_terminal_hom_ulift.{max u₂ v₂, u₁, v₁}
      (JC := JC) (u.obj V) ℋ
  ((Over.forget (u.obj V)).sheafPullback (Type (max u₁ u₂ v₁ v₂))
      (JC.over (u.obj V)) JC).map τ

/-- Helper for Lemma 7.28.1: the localized terminal morphism sends each embedded local slice
section to the corresponding embedded section of the localized identity representable. -/
private theorem overPost_localized_terminal_hom_on_local_section
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    (X : Over V)
    (s : ℋ.obj.obj (op ((Over.post u).obj X))) :
    (overPost_localized_terminal_hom (JC := JC) (u := u) (V := V) ℋ).hom.app
        (op (u.obj X.left))
        (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s) =
      overPost_local_section_to_lowerShriek (u := u) (V := V)
        (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
          (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V))))
        X
        ((localized_identity_uliftSheafifiedRepresentable_terminal_hom_ulift
          (JC := JC) (u.obj V) ℋ).hom.app (op ((Over.post u).obj X)) s) := by
  -- Specialize the naturality of the lower-shriek inclusion to the unique map into the terminal
  -- localized representable.
  simpa [overPost_localized_terminal_hom] using
    overPost_local_section_to_lowerShriek_map
      (JC := JC) (u := u) (V := V)
      (η := localized_identity_uliftSheafifiedRepresentable_terminal_hom_ulift
        (JC := JC) (u.obj V) ℋ)
      X s

/-- Helper for Lemma 7.28.1: every section of the localized identity representable on
`u(X)/u(V)` is the canonical section induced by `Over.homMk (u.map X.hom)`. -/
private theorem overPost_localized_identity_section_eq_homMk_section
    (u : D ⥤ C) (V : D)
    (X : Over V)
    (z :
      (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
        (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V)))).obj.obj
          (op ((Over.post u).obj X))) :
    z =
      (JC.over (u.obj V)).uliftSheafifiedRepresentableHomEquiv
        (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
          (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V))))
        ((Over.post u).obj X)
        ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₂ v₂, max u₁ v₁, v₁}
          (JC.over (u.obj V))).map
            (show (Over.post u).obj X ⟶ Over.mk (𝟙 (u.obj V)) from
              Over.homMk (u.map X.hom))) := by
  -- Route correction: normalize the section by moving it across
  -- `uliftSheafifiedRepresentableHomEquiv`, where terminality gives a unique morphism.
  let e := (JC.over (u.obj V)).uliftSheafifiedRepresentableHomEquiv
    (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
      (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V))))
    ((Over.post u).obj X)
  have huniq :
      e.symm z =
        localized_identity_uliftSheafifiedRepresentable_terminal_hom_ulift
          (JC := JC) (u.obj V)
          (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
            (JC.over (u.obj V)) ((Over.post u).obj X)) := by
    -- Both morphisms land in the terminal localized identity representable.
    exact
      (localized_identity_uliftSheafifiedRepresentable_isTerminal_ulift
        (JC := JC) (u.obj V)).hom_ext _ _
  have hz :
      e (e.symm z) =
        e
          (localized_identity_uliftSheafifiedRepresentable_terminal_hom_ulift
            (JC := JC) (u.obj V)
            (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
              (JC.over (u.obj V)) ((Over.post u).obj X))) := by
    exact congrArg e huniq
  -- Rewrite the unique morphism from the localized representable by the explicit terminal map.
  simpa [e, localized_identity_uliftSheafifiedRepresentable_terminal_map]
    using hz

/-- Helper for Lemma 7.28.1: after applying the localized terminal morphism, every embedded local
slice section becomes the same canonical `Over.homMk` section of the localized identity
representable. -/
private theorem overPost_localized_terminal_hom_on_local_section_eq_homMk_section
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    (X : Over V)
    (s : ℋ.obj.obj (op ((Over.post u).obj X))) :
    (overPost_localized_terminal_hom (JC := JC) (u := u) (V := V) ℋ).hom.app
        (op (u.obj X.left))
        (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s) =
      overPost_local_section_to_lowerShriek (u := u) (V := V)
        (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
          (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V))))
        X
        ((JC.over (u.obj V)).uliftSheafifiedRepresentableHomEquiv
          (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
            (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V))))
          ((Over.post u).obj X)
          ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₂ v₂, max u₁ v₁, v₁}
            (JC.over (u.obj V))).map
              (show (Over.post u).obj X ⟶ Over.mk (𝟙 (u.obj V)) from
                Over.homMk (u.map X.hom)))) := by
  -- First compute the localized terminal morphism on the embedded slice section, then normalize
  -- the resulting section of the terminal localized representable.
  calc
    (overPost_localized_terminal_hom (JC := JC) (u := u) (V := V) ℋ).hom.app
        (op (u.obj X.left))
        (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s) =
      overPost_local_section_to_lowerShriek (u := u) (V := V)
        (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
          (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V))))
        X
        ((localized_identity_uliftSheafifiedRepresentable_terminal_hom_ulift
          (JC := JC) (u.obj V) ℋ).hom.app (op ((Over.post u).obj X)) s) := by
            exact overPost_localized_terminal_hom_on_local_section
              (JC := JC) (u := u) (V := V) (ℋ := ℋ) X s
    _ =
      overPost_local_section_to_lowerShriek (u := u) (V := V)
        (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
          (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V))))
        X
        ((JC.over (u.obj V)).uliftSheafifiedRepresentableHomEquiv
          (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
            (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V))))
          ((Over.post u).obj X)
          ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₂ v₂, max u₁ v₁, v₁}
            (JC.over (u.obj V))).map
              (show (Over.post u).obj X ⟶ Over.mk (𝟙 (u.obj V)) from
                Over.homMk (u.map X.hom)))) := by
            -- The previous lemma identifies the objectwise section of the terminal representable.
            exact congrArg
              (overPost_local_section_to_lowerShriek (u := u) (V := V)
                (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
                  (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V)))) X)
              (overPost_localized_identity_section_eq_homMk_section
                (JC := JC) (u := u) (V := V) X
                ((localized_identity_uliftSheafifiedRepresentable_terminal_hom_ulift
                  (JC := JC) (u.obj V) ℋ).hom.app (op ((Over.post u).obj X)) s))

/-- Helper for Lemma 7.28.1: the explicit transported family
`overPost_family_to_lowerShriek ... x` is compatible in the ambient lower shriek. -/
private theorem overPost_family_to_lowerShriek_compatible
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    {X : Over V} {S : Sieve X}
    (x : S.arrows.FamilyOfElements ((Over.post u).op ⋙ ℋ.obj))
    (hx : x.Compatible) :
    (overPost_family_to_lowerShriek (u := u) (V := V) ℋ x).Compatible := by
  -- Route correction: keep the transported family explicit, so the only remaining blocker is the
  -- final fibre extraction from the ambient glued section.
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hfg
  dsimp [overPost_family_to_lowerShriek]
  rw [overPost_local_section_to_lowerShriek_naturality
    (u := u) (V := V) (ℋ := ℋ) (f := g₁) (s := x f₁ hf₁)]
  rw [overPost_local_section_to_lowerShriek_naturality
    (u := u) (V := V) (ℋ := ℋ) (f := g₂) (s := x f₂ hf₂)]
  exact congrArg (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Z)
    (by simpa [Functor.comp_map] using hx g₁ g₂ hf₁ hf₂ hfg)

/-- Helper for Lemma 7.28.1: a slice amalgamation maps to an amalgamation of the transported
ambient family in `j_{u(V)!} ℋ`. -/
private theorem overPost_family_to_lowerShriek_isAmalgamation
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    {X : Over V} {S : Sieve X}
    (x : S.arrows.FamilyOfElements ((Over.post u).op ⋙ ℋ.obj))
    {s : ℋ.obj.obj (op ((Over.post u).obj X))}
    (hs : x.IsAmalgamation s) :
    (overPost_family_to_lowerShriek (u := u) (V := V) ℋ x).IsAmalgamation
      (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s) := by
  intro Y f hf
  -- Restrict the ambient image of `s` along `f`, then rewrite it using the naturality of the
  -- lower-shriek inclusion and the slice amalgamation identity for `s`.
  calc
    (((Over.forget V).op ⋙ u.op) ⋙ (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj).map f.op
        (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s) =
      overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y
        (ℋ.obj.map ((Over.post u).map f).op s) := by
          simpa [Functor.comp_map] using
            overPost_local_section_to_lowerShriek_naturality
              (u := u) (V := V) (ℋ := ℋ) (f := f) (s := s)
    _ =
      overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y (x f hf) := by
        exact congrArg (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y) (hs f hf)

/-- Helper for Lemma 7.28.1: once the ambient gluing is fixed, every slice amalgamation has the
same image in `j_{u(V)!} ℋ`. -/
private theorem overPost_slice_amalgamation_eq_glued_lowerShriek
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    {X : Over V} {S : Sieve X}
    (hGS : Presieve.IsSheafFor
      (((Over.forget V).op ⋙ u.op) ⋙ (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj) S)
    (x : S.arrows.FamilyOfElements ((Over.post u).op ⋙ ℋ.obj))
    (hy : (overPost_family_to_lowerShriek (u := u) (V := V) ℋ x).Compatible)
    {s : ℋ.obj.obj (op ((Over.post u).obj X))}
    (hs : x.IsAmalgamation s) :
    overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s =
      hGS.amalgamate (overPost_family_to_lowerShriek (u := u) (V := V) ℋ x) hy := by
  let y := overPost_family_to_lowerShriek (u := u) (V := V) ℋ x
  have hs' : y.IsAmalgamation
      (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ X s) := by
    -- Map the slice amalgamation through the explicit lower-shriek inclusion.
    simpa [y] using overPost_family_to_lowerShriek_isAmalgamation
      (u := u) (V := V) (ℋ := ℋ) (x := x) hs
  have ht : y.IsAmalgamation (hGS.amalgamate y hy) := hGS.isAmalgamation hy
  -- The ambient sheaf is separated on `S`, so two ambient amalgamations must coincide.
  exact (Presieve.IsSheafFor.isSeparatedFor hGS) y _ _ hs' ht

/-- Helper for Lemma 7.28.1: apply an ambient sheaf morphism to the explicitly transported slice
family in `j_{u(V)!} ℋ`. -/
private noncomputable def overPost_map_family_to_ambient
    (u : D ⥤ C) (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    (𝒢 : Sheaf JC (Type (max u₁ u₂ v₁ v₂)))
    {X : Over V} {S : Sieve X}
    (φ : overPost_lowerShriek_obj (u := u) (V := V) ℋ ⟶ 𝒢)
    (x : S.arrows.FamilyOfElements ((Over.post u).op ⋙ ℋ.obj)) :
    S.arrows.FamilyOfElements (((Over.forget V).op ⋙ u.op) ⋙ 𝒢.obj) :=
  fun Y f hf ↦
    φ.hom.app (op (u.obj Y.left))
      (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y (x f hf))

/-- Helper for Lemma 7.28.1: an ambient sheaf morphism preserves compatibility of the transported
slice family. -/
private theorem overPost_map_family_to_ambient_compatible
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    (𝒢 : Sheaf JC (Type (max u₁ u₂ v₁ v₂)))
    {X : Over V} {S : Sieve X}
    (φ : overPost_lowerShriek_obj (u := u) (V := V) ℋ ⟶ 𝒢)
    (x : S.arrows.FamilyOfElements ((Over.post u).op ⋙ ℋ.obj))
    (hx : x.Compatible) :
    (overPost_map_family_to_ambient (u := u) (V := V) (ℋ := ℋ) (𝒢 := 𝒢) φ x).Compatible := by
  -- First transport the slice family into `j_{u(V)!} ℋ`, then apply naturality of `φ`.
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hfg
  dsimp [overPost_map_family_to_ambient]
  have hφ₁ :
      𝒢.obj.map (u.map g₁.left).op
          (φ.hom.app (op (u.obj Y₁.left))
            (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y₁ (x f₁ hf₁))) =
        φ.hom.app (op (u.obj Z.left))
          ((overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj.map (u.map g₁.left).op
            (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y₁ (x f₁ hf₁))) := by
    simpa using
      (congr_fun (φ.hom.naturality (u.map g₁.left).op)
        (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y₁ (x f₁ hf₁))).symm
  have hφ₂ :
      𝒢.obj.map (u.map g₂.left).op
          (φ.hom.app (op (u.obj Y₂.left))
            (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y₂ (x f₂ hf₂))) =
        φ.hom.app (op (u.obj Z.left))
          ((overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj.map (u.map g₂.left).op
            (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y₂ (x f₂ hf₂))) := by
    simpa using
      (congr_fun (φ.hom.naturality (u.map g₂.left).op)
        (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y₂ (x f₂ hf₂))).symm
  rw [hφ₁, hφ₂]
  rw [overPost_local_section_to_lowerShriek_naturality
    (u := u) (V := V) (ℋ := ℋ) (f := g₁) (s := x f₁ hf₁)]
  rw [overPost_local_section_to_lowerShriek_naturality
    (u := u) (V := V) (ℋ := ℋ) (f := g₂) (s := x f₂ hf₂)]
  refine congrArg (φ.hom.app (op (u.obj Z.left))) ?_
  refine congrArg (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Z) ?_
  simpa [Functor.comp_map] using hx g₁ g₂ hf₁ hf₂ hfg

/-- Helper for Lemma 7.28.1: if `t` is the glued ambient section in `j_{u(V)!} ℋ`, then any
ambient sheaf morphism sends `t` to an amalgamation of the image family. -/
private theorem overPost_map_glued_lowerShriek_isAmalgamation
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    (𝒢 : Sheaf JC (Type (max u₁ u₂ v₁ v₂)))
    {X : Over V} {S : Sieve X}
    (hG : Presieve.IsSheaf (JD.over V)
      (((Over.forget V).op ⋙ u.op) ⋙ (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj))
    (hS : S ∈ (JD.over V) X)
    (φ : overPost_lowerShriek_obj (u := u) (V := V) ℋ ⟶ 𝒢)
    (x : S.arrows.FamilyOfElements ((Over.post u).op ⋙ ℋ.obj))
    (hx : x.Compatible) :
    let y := overPost_family_to_lowerShriek (u := u) (V := V) ℋ x
    let hy := overPost_family_to_lowerShriek_compatible
      (JD := JD) (JC := JC) (u := u) (V := V) (ℋ := ℋ) (x := x) hx
    let hGS := hG S hS
    let t := hGS.amalgamate y hy
    (overPost_map_family_to_ambient (u := u) (V := V) (ℋ := ℋ) (𝒢 := 𝒢) φ x).IsAmalgamation
      (φ.hom.app (op (u.obj X.left)) t) := by
  -- The glued section `t` already amalgamates the transported family in `j_{u(V)!} ℋ`; apply
  -- naturality of `φ` to transport that amalgamation identity to `𝒢`.
  intro y hy hGS t Y f hf
  dsimp [overPost_map_family_to_ambient]
  have hφ :
      𝒢.obj.map (u.map f.left).op (φ.hom.app (op (u.obj X.left)) t) =
        φ.hom.app (op (u.obj Y.left))
          ((overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj.map (u.map f.left).op t) := by
    simpa using (congr_fun (φ.hom.naturality (u.map f.left).op) t).symm
  rw [hφ]
  exact congrArg (φ.hom.app (op (u.obj Y.left))) ((hGS.isAmalgamation hy) f hf)

/-- Helper for Lemma 7.28.1: once an ambient morphism sends every local embedded slice section to
the canonical basepoint section, separatedness forces the glued ambient section to land over that
same basepoint. -/
private theorem overPost_glued_lowerShriek_eq_basepoint_of_local_sections
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    {X : Over V} {S : Sieve X}
    (hG : Presieve.IsSheaf (JD.over V)
      (((Over.forget V).op ⋙ u.op) ⋙ (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj))
    (hS : S ∈ (JD.over V) X)
    (x : S.arrows.FamilyOfElements ((Over.post u).op ⋙ ℋ.obj))
    (hx : x.Compatible)
    (φ : overPost_lowerShriek_obj (u := u) (V := V) ℋ ⟶
      GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂} JC (u.obj V))
    (hlocal :
      ∀ ⦃Y : Over V⦄ (f : Y ⟶ X) (hf : S.arrows f),
        φ.hom.app (op (u.obj Y.left))
            (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y (x f hf)) =
          overPost_ulift_basepoint_section (JC := JC) (u := u) (V := V) Y) :
    let y := overPost_family_to_lowerShriek (u := u) (V := V) ℋ x
    let hy := overPost_family_to_lowerShriek_compatible
      (JD := JD) (JC := JC) (u := u) (V := V) (ℋ := ℋ) (x := x) hx
    let hGS := hG S hS
    let t := hGS.amalgamate y hy
    φ.hom.app (op (u.obj X.left)) t =
      overPost_ulift_basepoint_section (JC := JC) (u := u) (V := V) X := by
  -- Route correction: separate the universal sheaf argument from the missing comparison map. Once
  -- `φ` is available, the conclusion is a formal separatedness argument on the ambient site.
  intro y hy hGS t
  let z := overPost_map_family_to_ambient (u := u) (V := V) (ℋ := ℋ)
    (𝒢 := GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂} JC (u.obj V)) φ x
  have hz : z.Compatible := by
    -- The mapped family stays compatible because `φ` is a sheaf morphism.
    simpa [z] using overPost_map_family_to_ambient_compatible
      (JD := JD) (JC := JC) (u := u) (V := V) (ℋ := ℋ)
      (𝒢 := GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂} JC (u.obj V))
      (φ := φ) (x := x) hx
  have hzt : z.IsAmalgamation (φ.hom.app (op (u.obj X.left)) t) := by
    -- Apply the previous image-of-amalgamation lemma to the actual glued section `t`.
    simpa [z, t, y, hy, hGS] using overPost_map_glued_lowerShriek_isAmalgamation
      (JD := JD) (JC := JC) (u := u) (V := V) (ℋ := ℋ)
      (𝒢 := GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂} JC (u.obj V))
      (hG := hG) (hS := hS) (φ := φ) (x := x) (hx := hx)
  have hzbase :
      z =
        overPost_ulift_basepoint_family (JC := JC) (u := u) (V := V) S := by
    -- The local hypothesis identifies each component of the image family with the canonical
    -- basepoint section on the same covering arrow.
    funext Y
    funext f
    funext hf
    exact hlocal f hf
  have hSheaf :
      Presieve.IsSheafFor
        ((((Over.forget V).op ⋙ u.op) ⋙
          (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂}
            JC (u.obj V)).obj)) S.arrows := by
    -- The ambient sheafified representable is a sheaf on `(C, JC)`, hence also on the localized
    -- site after restricting along `u`.
    exact (overPost_ambient_restriction_isSheaf
      (JD := JD) (JC := JC) (u := u) (V := V)
      (F := GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂}
        JC (u.obj V))) S hS
  have hbase :
      z.IsAmalgamation
        (overPost_ulift_basepoint_section (JC := JC) (u := u) (V := V) X) := by
    -- Rewrite the canonical basepoint amalgamation along the explicit identification of families.
    simpa [hzbase] using overPost_ulift_basepoint_isAmalgamation
      (JC := JC) (u := u) (V := V) (S := S)
  -- The ambient sheaf is separated on `S`, so the two amalgamations of the same family coincide.
  exact (Presieve.IsSheafFor.isSeparatedFor hSheaf) z _ _ hzt hbase

/-- Helper for Lemma 7.28.1: the glued ambient section already lifts through the localized
terminal morphism to the canonical `Over.homMk (u.map X.hom)` section of the localized identity
representable. -/
private theorem overPost_glued_lowerShriek_lifts_to_localized_identity
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    {X : Over V} {S : Sieve X}
    (hG : Presieve.IsSheaf (JD.over V)
      (((Over.forget V).op ⋙ u.op) ⋙ (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj))
    (hS : S ∈ (JD.over V) X)
    (x : S.arrows.FamilyOfElements ((Over.post u).op ⋙ ℋ.obj))
    (hx : x.Compatible) :
    let y := overPost_family_to_lowerShriek (u := u) (V := V) ℋ x
    let hy := overPost_family_to_lowerShriek_compatible
      (JD := JD) (JC := JC) (u := u) (V := V) (ℋ := ℋ) (x := x) hx
    let hGS := hG S hS
    let t := hGS.amalgamate y hy
    (overPost_localized_terminal_hom (JC := JC) (u := u) (V := V) ℋ).hom.app
        (op (u.obj X.left)) t =
      overPost_local_section_to_lowerShriek (u := u) (V := V)
        (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
          (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V))))
        X
        ((JC.over (u.obj V)).uliftSheafifiedRepresentableHomEquiv
          (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, max u₁ v₁, v₁}
            (JC.over (u.obj V)) (Over.mk (𝟙 (u.obj V))))
          ((Over.post u).obj X)
          ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₂ v₂, max u₁ v₁, v₁}
            (JC.over (u.obj V))).map
              (show (Over.post u).obj X ⟶ Over.mk (𝟙 (u.obj V)) from
                Over.homMk (u.map X.hom)))) := by
  -- Route correction: first land in the localized identity representable using the terminal map.
  -- The remaining missing comparison to `h[u(V)]^#` is now isolated from the gluing argument.
  intro y hy hGS t
  exact overPost_glued_lowerShriek_eq_basepoint_of_local_sections
    (JD := JD) (JC := JC) (u := u) (V := V) (ℋ := ℋ)
    (hG := hG) (hS := hS) (x := x) (hx := hx)
    (φ := overPost_localized_terminal_hom (JC := JC) (u := u) (V := V) ℋ)
    (hlocal := by
      intro Y f hf
      -- Every embedded local section is already identified by the localized terminality formula.
      simpa using overPost_localized_terminal_hom_on_local_section_eq_homMk_section
        (JC := JC) (u := u) (V := V) (ℋ := ℋ) Y (x f hf))

/-- Helper for Lemma 7.28.1: once the canonical localization morphism
`representableLocalizationHom` is known to send each embedded local slice section to the ambient
basepoint, the glued ambient section lies over that same basepoint. -/
private theorem overPost_glued_lowerShriek_representableLocalizationHom_eq_basepoint
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    {X : Over V} {S : Sieve X}
    (hG : Presieve.IsSheaf (JD.over V)
      (((Over.forget V).op ⋙ u.op) ⋙ (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj))
    (hS : S ∈ (JD.over V) X)
    (x : S.arrows.FamilyOfElements ((Over.post u).op ⋙ ℋ.obj))
    (hx : x.Compatible)
    (hlocal :
      ∀ ⦃Y : Over V⦄ (f : Y ⟶ X) (hf : S.arrows f),
        (JC.representableLocalizationHom (u.obj V) ℋ).hom.app (op (u.obj Y.left))
            (overPost_local_section_to_lowerShriek (u := u) (V := V) ℋ Y (x f hf)) =
          overPost_ulift_basepoint_section (JC := JC) (u := u) (V := V) Y) :
    let y := overPost_family_to_lowerShriek (u := u) (V := V) ℋ x
    let hy := overPost_family_to_lowerShriek_compatible
      (JD := JD) (JC := JC) (u := u) (V := V) (ℋ := ℋ) (x := x) hx
    let hGS := hG S hS
    let t := hGS.amalgamate y hy
    (JC.representableLocalizationHom (u.obj V) ℋ).hom.app (op (u.obj X.left)) t =
      overPost_ulift_basepoint_section (JC := JC) (u := u) (V := V) X := by
  -- This is Step 2 of the source route: once the local formula is available for the canonical
  -- map `j_{u(V)!} ℋ ⟶ h[u(V)]^#`, the ambient sheaf argument from the previous lemma applies
  -- without any further transport work.
  intro y hy hGS t
  exact overPost_glued_lowerShriek_eq_basepoint_of_local_sections
    (JD := JD) (JC := JC) (u := u) (V := V) (ℋ := ℋ)
    (hG := hG) (hS := hS) (x := x) (hx := hx)
    (φ := JC.representableLocalizationHom (u.obj V) ℋ)
    (hlocal := hlocal)

/-- Helper for Lemma 7.28.1: the canonical basepoint morphism
`h[V]^# ⟶ u_* h[u(V)]^#`, obtained by evaluating `u_* h[u(V)]^#` at the identity of `u(V)`. -/
private noncomputable abbrev overPost_pushforward_basepoint_hom
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D) :
    h[V]^#[JD] ⟶
      (u.sheafPushforwardContinuous (Type (max u₁ u₂ v₁ v₂)) JD JC).obj
        h[u.obj V]^#[JC] :=
  (JD.uliftSheafifiedRepresentableHomEquiv
    ((u.sheafPushforwardContinuous (Type (max u₁ u₂ v₁ v₂)) JD JC).obj
      h[u.obj V]^#[JC]) V).symm
    ((((u.sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (max u₁ u₂ v₁ v₂)) JD JC).inv.app h[u.obj V]^#[JC]).app (op V))
      (JC.uliftSheafifiedRepresentableHomEquiv h[u.obj V]^#[JC] (u.obj V) (𝟙 _)))

/-- Helper for Lemma 7.28.1: the localization comparison at any target slice is an equivalence of
categories. -/
private noncomputable instance overPost_representableLocalizationComparison_isEquivalence
    (W : D) :
    Functor.IsEquivalence (JD.representableLocalizationComparison W) :=
  JD.representableLocalizationComparison_isEquivalence W

/-- Helper for Lemma 7.28.1: source-faithful structural pivot. We first localize a slice sheaf on
`C/u(V)` to an over-object over `h[u(V)]^#`, push it forward along `u`, then pull it back along
the canonical map `h[V]^# ⟶ u_* h[u(V)]^#`, and finally return to `Sh(D/V)` via the localization
equivalence of Lemma 7.25.4. -/
private noncomputable abbrev overPost_slice_pushforward_via_localization
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D) :
    Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)) ⥤
      Sheaf (JD.over V) (Type (max u₁ u₂ v₁ v₂)) :=
  JC.representableLocalizationComparison (u.obj V) ⋙
    Over.post (u.sheafPushforwardContinuous (Type (max u₁ u₂ v₁ v₂)) JD JC) ⋙
    Over.pullback (overPost_pushforward_basepoint_hom (JD := JD) (JC := JC) (u := u) (V := V)) ⋙
    (JD.representableLocalizationComparison V).asEquivalence.inverse

/-- Helper for Lemma 7.28.1: after passing through the localized ambient pushforward object, the
remaining task is to identify the recovered slice sheaf with the raw presheaf
`((Over.post u).op ⋙ ℋ.obj)`. -/
private noncomputable def overPost_slice_pushforward_localization_counit
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    (JD.representableLocalizationComparison V).obj
        ((overPost_slice_pushforward_via_localization
            (JD := JD) (JC := JC) (u := u) (V := V)).obj ℋ) ≅
      (Over.pullback
          (overPost_pushforward_basepoint_hom (JD := JD) (JC := JC) (u := u) (V := V))).obj
        ((Over.post
            (u.sheafPushforwardContinuous (Type (max u₁ u₂ v₁ v₂)) JD JC)).obj
          ((JC.representableLocalizationComparison (u.obj V)).obj ℋ)) := by
  let comparison := (JD.representableLocalizationComparison V).asEquivalence
  -- The inverse in `overPost_slice_pushforward_via_localization` was chosen from the localization
  -- equivalence, so reapplying the forward comparison is exactly the counit isomorphism.
  simpa [overPost_slice_pushforward_via_localization, comparison] using
    comparison.counitIso.app
      ((Over.pullback
          (overPost_pushforward_basepoint_hom (JD := JD) (JC := JC) (u := u) (V := V))).obj
        ((Over.post
            (u.sheafPushforwardContinuous (Type (max u₁ u₂ v₁ v₂)) JD JC)).obj
          ((JC.representableLocalizationComparison (u.obj V)).obj ℋ)))

/-- Helper for Lemma 7.28.1: after passing through the localized ambient pushforward object, the
remaining task is to identify the recovered slice sheaf with the raw presheaf
`((Over.post u).op ⋙ ℋ.obj)`. -/
private theorem overPost_slice_pushforward_pullback_obj_hom
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (A : Over
      ((u.sheafPushforwardContinuous (Type (max u₁ u₂ v₁ v₂)) JD JC).obj
        h[u.obj V]^#[JC])) :
    ((Over.pullback
        (overPost_pushforward_basepoint_hom (JD := JD) (JC := JC) (u := u) (V := V))).obj
      A).hom =
      Limits.pullback.snd A.hom
        (overPost_pushforward_basepoint_hom (JD := JD) (JC := JC) (u := u) (V := V)) := by
  -- Normalize the `Over.pullback` target once, so later proofs can work with the owner-level
  -- pullback projection instead of unfolding the over-object transport repeatedly.
  simpa using Over.pullback_obj_hom
    (overPost_pushforward_basepoint_hom (JD := JD) (JC := JC) (u := u) (V := V)) A

/-- Helper for Lemma 7.28.1: after fixing the left-object comparison
`overPost_composite_sheafPullback_iso_app`, the remaining source-faithful step is the single
structure-map identity needed by `Over.isoMk`. -/
private theorem overPost_slice_pushforward_structure_map
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    let G :=
      ((Over.post u).sheafPushforwardContinuous
        (Type (max u₁ u₂ v₁ v₂)) (JD.over V) (JC.over (u.obj V))).obj ℋ
    let T :=
      (Over.pullback
          (overPost_pushforward_basepoint_hom (JD := JD) (JC := JC) (u := u) (V := V))).obj
        ((Over.post
            (u.sheafPushforwardContinuous (Type (max u₁ u₂ v₁ v₂)) JD JC)).obj
          ((JC.representableLocalizationComparison (u.obj V)).obj ℋ))
    (overPost_composite_sheafPullback_iso_app (u := u) (V := V) G).hom ≫ T.hom =
      JD.representableLocalizationHom V G := by
  -- Route correction: the object comparison is no longer the blocker. After normalizing the
  -- `Over.pullback` target, only the structure-map computation over `h[V]^#` remains.
  intro G T
  -- TODO: first rewrite `T.hom` with `overPost_slice_pushforward_pullback_obj_hom`, then prove
  -- the terminal/basepoint case and lift it to arbitrary `ℋ` by naturality, following
  -- `relocalization_lower_shriek_over_map_square`.
  sorry

/-- Helper for Lemma 7.28.1: after passing through the localized ambient pushforward object, the
remaining task is to identify the recovered slice sheaf with the raw presheaf
`((Over.post u).op ⋙ ℋ.obj)`. -/
private theorem overPost_slice_pushforward_forward_localization_iso
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    (JD.representableLocalizationComparison V).obj
        (((Over.post u).sheafPushforwardContinuous
            (Type (max u₁ u₂ v₁ v₂)) (JD.over V) (JC.over (u.obj V))).obj ℋ) ≅
      (Over.pullback
          (overPost_pushforward_basepoint_hom (JD := JD) (JC := JC) (u := u) (V := V))).obj
        ((Over.post
            (u.sheafPushforwardContinuous (Type (max u₁ u₂ v₁ v₂)) JD JC)).obj
          ((JC.representableLocalizationComparison (u.obj V)).obj ℋ)) := by
  let G :=
    ((Over.post u).sheafPushforwardContinuous
      (Type (max u₁ u₂ v₁ v₂)) (JD.over V) (JC.over (u.obj V))).obj ℋ
  let e := overPost_composite_sheafPullback_iso_app (u := u) (V := V) G
  let T :=
    (Over.pullback
        (overPost_pushforward_basepoint_hom (JD := JD) (JC := JC) (u := u) (V := V))).obj
      ((Over.post
          (u.sheafPushforwardContinuous (Type (max u₁ u₂ v₁ v₂)) JD JC)).obj
        ((JC.representableLocalizationComparison (u.obj V)).obj ℋ))
  -- Build the over-object isomorphism from the fixed left-object comparison `e`; the preceding
  -- helper isolates the remaining source-faithful structure-map computation.
  refine Over.isoMk e ?_
  simpa [G, e, T] using
    overPost_slice_pushforward_structure_map
      (JD := JD) (JC := JC) (u := u) (V := V) ℋ

/-- Helper for Lemma 7.28.1: after passing through the localized ambient pushforward object, the
remaining task is to identify the recovered slice sheaf with the raw presheaf
`((Over.post u).op ⋙ ℋ.obj)`. -/
private theorem overPost_slice_pushforward_via_localization_obj_iso
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    ((overPost_slice_pushforward_via_localization (JD := JD) (JC := JC) (u := u) (V := V)).obj
        ℋ).obj ≅
      ((Over.post u).op ⋙ ℋ.obj) := by
  -- Route correction: the old proof tried to recover a slice section by comparing a glued ambient
  -- section with a terminal basepoint section inside `j_{u(V)!} ℋ`. The new route first packages
  -- the ambient pushforward over `h[V]^#`; the only remaining blocker is the owner-level
  -- identification of the resulting localized slice object with the raw presheaf
  -- `((Over.post u).op ⋙ ℋ.obj)`.
  let T : Over h[V]^#[JD] :=
    (Over.pullback
        (overPost_pushforward_basepoint_hom (JD := JD) (JC := JC) (u := u) (V := V))).obj
      ((Over.post
          (u.sheafPushforwardContinuous (Type (max u₁ u₂ v₁ v₂)) JD JC)).obj
        ((JC.representableLocalizationComparison (u.obj V)).obj ℋ))
  have hCounit :
      (JD.representableLocalizationComparison V).obj
          ((overPost_slice_pushforward_via_localization
              (JD := JD) (JC := JC) (u := u) (V := V)).obj ℋ) ≅
        T :=
    overPost_slice_pushforward_localization_counit
      (JD := JD) (JC := JC) (u := u) (V := V) ℋ
  let G : Sheaf (JD.over V) (Type (max u₁ u₂ v₁ v₂)) :=
    ((Over.post u).sheafPushforwardContinuous
      (Type (max u₁ u₂ v₁ v₂)) (JD.over V) (JC.over (u.obj V))).obj ℋ
  have hLocalized :
      (JD.representableLocalizationComparison V).obj G ≅ T :=
    overPost_slice_pushforward_forward_localization_iso
      (JD := JD) (JC := JC) (u := u) (V := V) ℋ
  let comparison := (JD.representableLocalizationComparison V).asEquivalence
  have hRecovered :
      ((overPost_slice_pushforward_via_localization
          (JD := JD) (JC := JC) (u := u) (V := V)).obj ℋ) ≅ G := by
    -- Once both candidates have the same forward localization, recover the slice sheaf by
    -- transporting that equality back through the equivalence of Lemma 7.25.4.
    refine (comparison.unitIso.app
        ((overPost_slice_pushforward_via_localization
          (JD := JD) (JC := JC) (u := u) (V := V)).obj ℋ)).symm ≪≫ ?_ ≪≫
      comparison.unitIso.app G
    exact Functor.mapIso comparison.inverse (hCounit ≪≫ hLocalized.symm)
  -- Forget the recovered sheaf comparison and rewrite the right-hand side by the standard
  -- presheaf formula for the inverse-image functor attached to `Over.post u`.
  exact
    (Functor.mapIso (sheafToPresheaf (JD.over V) (Type (max u₁ u₂ v₁ v₂))) hRecovered) ≪≫
      ((Over.post u).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type (max u₁ u₂ v₁ v₂)) (JD.over V) (JC.over (u.obj V))).app ℋ

/-- Helper for Lemma 7.28.1: once the compatible family on the slice cover has been embedded into
the ambient lower shriek `j_{u(V)!} ℋ`, the remaining source-faithful step is to extract the
unique slice amalgamation from the glued ambient section. -/
private theorem overPost_extract_unique_amalgamation_from_lowerShriek
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂)))
    {X : Over V} {S : Sieve X}
    (hG : Presieve.IsSheaf (JD.over V)
      (((Over.forget V).op ⋙ u.op) ⋙ (overPost_lowerShriek_obj (u := u) (V := V) ℋ).obj))
    (hS : S ∈ (JD.over V) X)
    (x : S.arrows.FamilyOfElements ((Over.post u).op ⋙ ℋ.obj))
    (hx : x.Compatible) :
    ∃! s : ℋ.obj.obj (op ((Over.post u).obj X)), x.IsAmalgamation s := by
  -- Route correction: after localizing the ambient pushforward object, uniqueness is now reduced
  -- to the sheaf axiom for the recovered slice sheaf. The old fibre-extraction endpoint is no
  -- longer part of the main skeleton.
  let G :=
    (overPost_slice_pushforward_via_localization (JD := JD) (JC := JC) (u := u) (V := V)).obj ℋ
  have hIso :
      G.obj ≅ ((Over.post u).op ⋙ ℋ.obj) :=
    overPost_slice_pushforward_via_localization_obj_iso
      (JD := JD) (JC := JC) (u := u) (V := V) ℋ
  have hSheaf : Presieve.IsSheaf (JD.over V) ((Over.post u).op ⋙ ℋ.obj) :=
    (Presheaf.isSheaf_of_iso_iff hIso).1 G.property
  exact hSheaf X S hS x hx

/-- Helper for Lemma 7.28.1: the localization step proving continuity of `Over.post u` remains
the only structural blocker. -/
private theorem overPost_op_comp_isSheaf_of_types
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    Presieve.IsSheaf (JD.over V) ((Over.post u).op ⋙ ℋ.obj) := by
  -- Route correction: instead of gluing inside `j_{u(V)!} ℋ` and then extracting a fibre point,
  -- we now transport `ℋ` through the localized ambient pushforward object and only need its
  -- underlying-presheaf identification.
  let G :=
    (overPost_slice_pushforward_via_localization (JD := JD) (JC := JC) (u := u) (V := V)).obj ℋ
  have hIso :
      G.obj ≅ ((Over.post u).op ⋙ ℋ.obj) :=
    overPost_slice_pushforward_via_localization_obj_iso
      (JD := JD) (JC := JC) (u := u) (V := V) ℋ
  exact (Presheaf.isSheaf_of_iso_iff hIso).1 G.property

-- Proof sketch: once the localized sheafness statement above is proved, continuity is exactly the
-- owner constructor `Functor.IsContinuous.mk`.
/-- The induced slice functor of a continuous site functor is again continuous. -/
instance overPost_isContinuous
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D) :
    (Over.post u).IsContinuous (JD.over V) (JC.over (u.obj V)) := by
  constructor
  intro ℋ
  -- The source-faithful localization proof is isolated in the previous helper.
  exact overPost_op_comp_isSheaf_of_types (u := u) (V := V) ℋ

-- Proof sketch: representable flatness descends to the slice by identifying the relevant
-- structured-arrow category with an over-category in the ambient structured-arrow category.
/-- If `u` is representably flat, then the induced slice functor `Over.post u` is representably
flat. -/
instance overPost_representablyFlat
    (u : D ⥤ C) [RepresentablyFlat u] (V : D) :
    RepresentablyFlat (show Over V ⥤ Over (u.obj V) from Over.post u) := by
  constructor
  intro Y
  -- The ambient structured-arrow category is cofiltered by flatness of `u`.
  haveI : IsCofiltered (StructuredArrow Y.left u) :=
    RepresentablyFlat.cofiltered (F := u) Y.left
  -- Passing to an over-category preserves cofilteredness.
  haveI : IsCofiltered (Over (StructuredArrow.mk Y.hom : StructuredArrow Y.left u)) :=
    CategoryTheory.IsCofiltered.over _
  -- Transport cofilteredness back across the explicit slice equivalence.
  exact IsCofiltered.of_equivalence
    (structuredArrow_overPost_equiv_over_structuredArrow u V Y).symm

-- Proof sketch: the chapter owner `IsMorphismOfSites` is by definition continuity together with
-- representable flatness, both already provided above for `Over.post u`.
/-- The slice functor induced by a morphism of sites is again a morphism of sites on the localized
sites. -/
instance overPost_isMorphismOfSites
    (u : D ⥤ C) [IsMorphismOfSites JD JC u] (V : D) :
    IsMorphismOfSites (JD.over V) (JC.over (u.obj V))
      (show Over V ⥤ Over (u.obj V) from Over.post u) :=
  inferInstance

-- Proof sketch: once `Over.post u` is continuous, the commutative square of direct images is the
-- canonical owner comparison for the strict equality
-- `Over.post u ⋙ Over.forget (u.obj V) = Over.forget V ⋙ u`.
/-- Lemma 7.28.1: the localized direct-image square is the owner-level comparison
`f'_* j_U^{-1} ≅ j_V^{-1} f_*`. -/
noncomputable def slice_pushforward_comp_iso
    (u : D ⥤ C) [u.IsContinuous JD JC]
    (V : D) (A : Type w) [Category.{v₃} A] :
    JC.overPullback A (u.obj V) ⋙
        (Over.post u).sheafPushforwardContinuous A (JD.over V) (JC.over (u.obj V)) ≅
      u.sheafPushforwardContinuous A JD JC ⋙ JD.overPullback A V := by
  letI : Functor.IsContinuous (Over.forget V ⋙ u) (JD.over V) JC :=
    Functor.isContinuous_comp (Over.forget V) u (JD.over V) JD JC
  -- Apply the owner comparison to the strict commutative triangle on slice forgetful functors.
  exact
    Functor.sheafPushforwardContinuousComp'
      (eqToIso (overPost_comp_forget_eq u V) :
        Over.post u ⋙ Over.forget (u.obj V) ≅ Over.forget V ⋙ u)
      A (JD.over V) (JC.over (u.obj V)) JC

end

end CategoryTheory
