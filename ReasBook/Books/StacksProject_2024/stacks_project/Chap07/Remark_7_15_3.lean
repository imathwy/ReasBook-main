import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite CategoryTheory.Limits
open CategoryTheory.Types

universe u

noncomputable section

namespace CategoryTheory.ObjectProperty

/-
Domain-style sampling for Remark 7.15.3:
- primary domain: sheaves on full subcategories of `Type` equipped with the pulled-back jointly
  surjective topology;
- sampled owner API:
  `typesGrothendieckTopology`,
  `Functor.inducedTopology`,
  `typeEquiv`,
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafInducedTopologyEquivOfIsCoverDense`;
- source/core/bridge triage:
  `source-facing`: the jointly surjective site on `S.FullSubcategory`;
  `core/canonical`: the induced-topology owner `S.ι.inducedTopology typesGrothendieckTopology`,
  together with `typeEquiv` and the dense-subsite comparison for
  `S.ι.sheafPushforwardContinuous`;
  `bridge/view`: the source-facing topology
  `(jointlySurjectivePrecoverage.comap S.ι).toGrothendieck` and the resulting set-to-sheaf
  functor.

Primitive data are the inclusion `S.ι` and the source-facing jointly surjective precoverage on the
full subcategory. The canonical comparison machinery is organized around
`S.ι.inducedTopology typesGrothendieckTopology`, so the local topology/functor names should be
thin bridges to that owner rather than parallel replacements for it.
-/

section

variable (S : ObjectProperty (Type u))

/-- The pulled-back jointly surjective topology on `S.FullSubcategory`. -/
abbrev fullSubcategoryJointlySurjectiveTopology : GrothendieckTopology S.FullSubcategory :=
  (jointlySurjectivePrecoverage.comap S.ι).toGrothendieck

/-- If `S` contains a singleton object, the inclusion `S.FullSubcategory ⥤ Type` is cover-dense
for the jointly surjective topology on `Type`. -/
theorem fullSubcategoryInclusion_isCoverDense_of_singleton_object
    (e : S.FullSubcategory) (he : Unique e.obj) :
    S.ι.IsCoverDense typesGrothendieckTopology := by
  refine ⟨fun X x ↦ ?_⟩
  refine ⟨⟨e, (↾fun _ ↦ he.default), (↾fun _ ↦ x), ?_⟩⟩
  funext y
  simp

/-- Under cover density, the source-facing jointly surjective topology on `S.FullSubcategory`
agrees with the canonical induced topology coming from the inclusion into `Type`. -/
theorem fullSubcategoryJointlySurjectiveTopology_eq_inducedTopology
    [HasPullbacks S.FullSubcategory]
    [S.ι.IsCoverDense typesGrothendieckTopology] :
    fullSubcategoryJointlySurjectiveTopology S = S.ι.inducedTopology typesGrothendieckTopology := by
  sorry

section

variable [HasPullbacks S.FullSubcategory]

/-- The canonical direct-image functor `E ↦ (U ↦ (U → E))` from sets to sheaves on the surjective
site attached to a full subcategory of `Type`. -/
abbrev fullSubcategorySetDirectImage :
    Type u ⥤ Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u) :=
  ObjectProperty.lift (Presheaf.IsSheaf (fullSubcategoryJointlySurjectiveTopology S))
    (typeEquiv.functor ⋙ sheafToPresheaf _ _ ⋙
      (Functor.whiskeringLeft _ _ _).obj S.ι.op)
    (fun _ ↦ by
      sorry)

omit [HasPullbacks S.FullSubcategory] in
/-- On an object `U` of the full subcategory, the direct image of `E` is the set of maps
`U ⟶ E`, i.e. functions `U.obj → E`. -/
theorem fullSubcategorySetDirectImage_obj_obj
    (E : Type u) (U : S.FullSubcategory) :
    ((fullSubcategorySetDirectImage S).obj E).obj.obj (op U) = (U.obj ⟶ E) := by
  exact typeEquiv_functor_obj_obj_obj E (op U.obj)

attribute [simp] fullSubcategorySetDirectImage_obj_obj

end

section

variable [HasPullbacks S.FullSubcategory]

-- Proof sketch: if `e` is singleton, then the inclusion `S.ι` is cover-dense for
-- `typesGrothendieckTopology`, the pulled-back topology on `S.FullSubcategory` agrees with the
-- induced topology, and the canonical comparison equivalence
-- `S.ι.sheafInducedTopologyEquivOfIsCoverDense` identifies sheaves on `S.FullSubcategory` with
-- sheaves on `Type`. Composing that owner equivalence with `typeEquiv` recovers the source
-- functor `E ↦ (U ↦ (U → E))`.
/-- If the full subcategory contains a singleton object, the canonical functor from sets to sheaves
is an equivalence, with quasi-inverse the evaluation functor
`(sheafSections (fullSubcategoryJointlySurjectiveTopology S) (Type u)).obj (op e)`.
-/
theorem fullSubcategorySetDirectImage_isEquivalence_of_singleton_object
    (e : S.FullSubcategory) (he : Unique e.obj) :
    Functor.IsEquivalence (fullSubcategorySetDirectImage S) := by
  letI : S.ι.IsCoverDense typesGrothendieckTopology :=
    fullSubcategoryInclusion_isCoverDense_of_singleton_object S e he
  letI :
      Functor.IsContinuous S.ι
        (fullSubcategoryJointlySurjectiveTopology S) typesGrothendieckTopology := by
    simpa [fullSubcategoryJointlySurjectiveTopology_eq_inducedTopology S] using
      (inferInstance :
        Functor.IsContinuous S.ι
          (S.ι.inducedTopology typesGrothendieckTopology) typesGrothendieckTopology)
  letI :
      Functor.IsEquivalence
        (typeEquiv.functor ⋙
          S.ι.sheafPushforwardContinuous (Type u)
            (fullSubcategoryJointlySurjectiveTopology S) typesGrothendieckTopology) := by
    sorry
  let eIso :
      fullSubcategorySetDirectImage S ≅
        typeEquiv.functor ⋙
          S.ι.sheafPushforwardContinuous (Type u)
            (fullSubcategoryJointlySurjectiveTopology S) typesGrothendieckTopology :=
    NatIso.ofComponents
      (fun E ↦
        ObjectProperty.isoMk (Presheaf.IsSheaf (fullSubcategoryJointlySurjectiveTopology S))
          (Iso.refl _))
      (fun _ ↦ by
        ext U x
        rfl)
  exact Functor.isEquivalence_of_iso eIso.symm

end

section

private theorem fullSubcategorySetInverseImageOfEndomorphism_map_mem
    {e : S.FullSubcategory} (φ : e ⟶ e)
    {F G : Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u)} (η : F ⟶ G)
    {x : F.obj.obj (op e)}
    (hx : x ∈ Set.range (F.obj.map φ.op)) :
    η.hom.app (op e) x ∈ Set.range (G.obj.map φ.op) := by
  rcases hx with ⟨y, rfl⟩
  refine ⟨η.hom.app (op e) y, ?_⟩
  simpa using (congrFun (η.hom.naturality φ.op) y).symm

/-- For an endomorphism `φ : e ⟶ e`, this inverse-image functor sends a sheaf `F` to the image
`Im(F(φ))`, represented in Lean as the subtype `Set.range (F.obj.map φ.op)`. -/
def fullSubcategorySetInverseImageOfEndomorphism
    {e : S.FullSubcategory} (φ : e ⟶ e) :
    Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u) ⥤ Type u where
  obj F := ↥(Set.range (F.obj.map φ.op))
  map η :=
    Subtype.map (η.hom.app (op e))
      (fun a ha ↦ fullSubcategorySetInverseImageOfEndomorphism_map_mem S φ η ha)
  map_id F := by
    ext x
    rfl
  map_comp η θ := by
    ext x
    rfl

/-- Objectwise, the endomorphism-image inverse-image functor is the image `Im(F(φ))`. -/
@[simp] theorem fullSubcategorySetInverseImageOfEndomorphism_obj
    {e : S.FullSubcategory} (φ : e ⟶ e)
    (F : Sheaf (fullSubcategoryJointlySurjectiveTopology S) (Type u)) :
    (fullSubcategorySetInverseImageOfEndomorphism S φ).obj F = ↥(Set.range (F.obj.map φ.op)) := rfl

section

variable [HasPullbacks S.FullSubcategory]

/-- Remark 7.15.3: if the full subcategory contains a nonempty object, then the canonical functor
`E ↦ (U ↦ (U → E))` gives an equivalence between sets and sheaves for the jointly surjective site
on that full subcategory. -/
theorem fullSubcategorySetDirectImage_isEquivalence_of_nonempty_object
    (e : S.FullSubcategory) (he : Nonempty e.obj) :
    Functor.IsEquivalence (fullSubcategorySetDirectImage S) := sorry

-- Proof sketch: a constant endomorphism of the nonempty object `e` has singleton image. The
-- preceding singleton-object comparison can then be applied through the source-facing inverse
-- image functor `F ↦ Im(F(φ))`.
/-- If a nonempty object admits an endomorphism with singleton image, then Remark 7.15.3 applies.
The quasi-inverse is `fullSubcategorySetInverseImageOfEndomorphism S φ`, whose value on a sheaf is
`Im(F(φ))`. -/
theorem fullSubcategorySetDirectImage_isEquivalence_of_nonempty_endomorphism_with_singleton_range
    (e : S.FullSubcategory) (he : Nonempty e.obj) (φ : e ⟶ e)
    (hφ : (Set.range φ).Subsingleton) :
    Functor.IsEquivalence (fullSubcategorySetDirectImage S) := sorry

end

end

end

end CategoryTheory.ObjectProperty
