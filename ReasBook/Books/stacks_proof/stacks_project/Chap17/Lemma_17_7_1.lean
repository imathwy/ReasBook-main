import Mathlib
import Mathlib.Topology.Sheaves.Abelian
import StacksProject_2024.Chap06.Lemma_6_16_1
import StacksProject_2024.Chap06.Lemma_6_31_6
import StacksProject_2024.Chap06.Lemma_6_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open TopCat.Sheaf
open OpenSubsetExtensionByInitial

noncomputable section

universe u

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

local instance : Preadditive (X.Sheaf AddCommGrpCat.{u}) :=
  inferInstanceAs
    (Preadditive
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

/-- Helper for Lemma 17.7.1: abelian sheaves have the induced zero morphisms. -/
local instance : HasZeroMorphisms (X.Sheaf AddCommGrpCat.{u}) :=
  Preadditive.preadditiveHasZeroMorphisms

local notation "i[" U "]" => X.closedSubsetInclusion ((U : Set X)ᶜ)
local notation "i⁻¹[" U "]" => Sheaf.pullback AddCommGrpCat i[U]
local notation "i_*[" U "]" => Sheaf.pushforward AddCommGrpCat i[U]
local notation "iAdj[" U "]" => Sheaf.pullbackPushforwardAdjunction AddCommGrpCat i[U]
local notation "jAdj[" U "]" => sheafExtensionByInitialAdjunction U

/-
Domain-style sampling for Lemma 17.7.1:
- primary domain: sheaves of abelian groups on an open/closed decomposition of a topological
  space;
- sampled owner declarations:
  `sheafExtensionByInitialAdjunction`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkDescription`,
  `closedSubsetAbelianSheaf_pushforward_stalk_isZero_of_not_mem`,
  `exact_iff_stalkFunctor_map_exact`;
- owner abstraction: the canonical adjunction maps
  `j_! j^{-1} ℱ ⟶ ℱ` and `ℱ ⟶ i_* i^{-1} ℱ`, organized by
  `ShortComplex` / `ShortComplex.ShortExact` in `X.Sheaf AddCommGrpCat`;
- primitive data: the open subset `U`, the sheaf `ℱ`, and those two owner maps;
- derived API: the zero-composite relation and the resulting short-exactness statement.

Source/core/bridge triage:
- `source-facing`: the short exact sequence
  `j_! j^{-1} ℱ ⟶ ℱ ⟶ i_* i^{-1} ℱ`;
- `core/canonical`: the owner adjunction maps and `ShortComplex.ShortExact`;
- `bridge/view`: the stalkwise identifications on points of `U` and of `X \ U`.

The packaged short complex is therefore only one-off derived data in this file, so the public API
should keep the source-facing short-exact theorem rather than a parallel named wrapper object.
-/

-- Proof sketch: these are the built-in naturality squares of the counit for `j! U ⊣ j^{-1}` and
-- of the unit for `i^{-1} ⊣ i_*`.
/-- The counit map `j_! j^{-1} ℱ ⟶ ℱ` is natural in the sheaf. -/
theorem openClosedComplementAbelianSheaf_left_naturality
    (U : Opens X) {ℱ 𝒢 : X.Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢) :
    CommSq
      ((j! U).map
        ((Sheaf.pullback AddCommGrpCat (extensionByZeroOpenSubsetInclusion U)).map φ))
      ((jAdj[U]).counit.app ℱ)
      ((jAdj[U]).counit.app 𝒢)
      φ := by
  exact CommSq.mk ((jAdj[U]).counit.naturality φ)

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- The unit map `ℱ ⟶ i_* i^{-1} ℱ` for the closed complement of `U` is natural in the sheaf. -/
theorem openClosedComplementAbelianSheaf_right_naturality
    (U : Opens X) {ℱ 𝒢 : X.Sheaf AddCommGrpCat.{u}} (φ : ℱ ⟶ 𝒢) :
    CommSq
      φ
      ((iAdj[U]).unit.app ℱ)
      ((iAdj[U]).unit.app 𝒢)
      ((i_*[U]).map ((i⁻¹[U]).map φ)) := by
  exact CommSq.mk ((iAdj[U]).unit.naturality φ)

/-- Helper for Lemma 17.7.1: in `AddCommGrpCat`, every two maps into a zero object agree. -/
private theorem addCommGrpHom_eq_of_isZero
    {A B : AddCommGrpCat.{u}} (hB : IsZero B) (f g : A ⟶ B) :
    f = g :=
  hB.eq_of_tgt _ _

-- Proof comment: this is the owner naturality theorem for the sheaf-level stalk pullback
-- comparison, specialized to abelian sheaves.
/-- Helper for Lemma 17.7.1: the sheaf stalk pullback comparison is natural in the sheaf
argument. -/
private theorem sheaf_stalkPullbackIso_hom_naturality
    {Y : TopCat.{u}} (f : X ⟶ Y) {ℱ 𝒢 : Y.Sheaf AddCommGrpCat.{u}} (η : ℱ ⟶ 𝒢) (x : X) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map η.hom) ≫
        (TopCat.Sheaf.stalkPullbackIso f 𝒢 x).hom =
      (TopCat.Sheaf.stalkPullbackIso f ℱ x).hom ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (((TopCat.Sheaf.pullback AddCommGrpCat.{u} f).map η).hom)) := by
  simpa using
    (TopCat.Sheaf.stalkPullbackIso_hom_naturality
      (A := AddCommGrpCat.{u}) (f := f) (x := x) η.hom)

-- Proof comment: the stalk functor on abelian sheaves is the sheaf forgetful functor followed by
-- the usual presheaf stalk functor.
/-- Helper for Lemma 17.7.1: the stalk functor on abelian sheaves at a point of `X`. -/
private noncomputable abbrev abelianSheafStalkFunctor (x : X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

omit [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
-- Proof comment: the closed complement appearing in the statement is the ordinary complement of
-- an open subset, so its closedness is immediate from the topology API.
/-- Helper for Lemma 17.7.1: the complement of `U` is a closed subset of `X`. -/
private theorem openSubsetComplement_isClosed (U : Opens X) :
    IsClosed ((U : Set X)ᶜ) := by
  simpa using U.2.isClosed_compl

-- Proof comment: on the branch `x ∉ U`, the Chapter 6 stalk description for extension by zero
-- identifies the stalk with the zero abelian group.
/-- Helper for Lemma 17.7.1: outside `U`, the stalk of `j_! 𝒢` is zero. -/
private theorem openSubsetExtensionByInitial_stalk_isZero_of_not_mem
    (U : Opens X) (𝒢 : (extensionByZeroOpenSubsetSpace U).Sheaf AddCommGrpCat.{u})
    (x : X) (hx : x ∉ (U : Set X)) :
    IsZero (((j! U).obj 𝒢).presheaf.stalk x) := by
  let e : (((j! U).obj 𝒢).presheaf.stalk x) ≅ (⊥_ AddCommGrpCat.{u}) := by
    simpa [hx] using
      (OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkIso
        (C := AddCommGrpCat.{u}) U 𝒢 x)
  exact IsZero.of_iso (Limits.initialIsInitial.isZero : IsZero (⊥_ AddCommGrpCat.{u})) e

-- Proof comment: on the branch `x ∈ U`, the point lies outside the closed complement `X \ U`, so
-- the Chapter 6 closed-subset pushforward theorem forces the stalk to vanish.
/-- Helper for Lemma 17.7.1: at a point of `U`, the stalk of `i_* i^{-1} ℱ` is zero. -/
private theorem closedComplementPushforward_stalk_isZero_of_mem
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∈ (U : Set X)) :
    IsZero (((i_*[U]).obj ((i⁻¹[U]).obj ℱ)).presheaf.stalk x) := by
  have hxCompl : x ∉ ((U : Set X)ᶜ) := by
    simpa using hx
  simpa using
    (closedSubsetAbelianSheaf_pushforward_stalk_isZero_of_not_mem
      (Z := ((U : Set X)ᶜ))
      (openSubsetComplement_isClosed (X := X) U)
      ((i⁻¹[U]).obj ℱ)
      (x := x)
      hxCompl)

-- Proof comment: the right triangle identity for `j! U ⊣ j⁻¹[U]` makes the pullback of the
-- counit a split inverse to the unit, and the unit is already an isomorphism on the open
-- subspace.
/-- Helper for Lemma 17.7.1: after pulling back along the open inclusion, the counit
`j_! j^{-1} ℱ ⟶ ℱ` becomes an isomorphism. -/
private theorem openSubsetPulledBackCounit_isIso
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    IsIso
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
        (extensionByZeroOpenSubsetInclusion U)).map ((jAdj[U]).counit.app ℱ)) := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let R := TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)
  let η := h.unit.app (R.obj ℱ)
  let ε := h.counit.app ℱ
  have hη : IsIso η := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
      (R.obj ℱ))
    infer_instance
  have hright : η ≫ R.map ε = 𝟙 (R.obj ℱ) := by
    simpa [R, η, ε] using h.right_triangle_components_assoc ℱ (𝟙 (R.obj ℱ))
  have hleft : R.map ε ≫ η = 𝟙 (R.obj ((j! U).obj (R.obj ℱ))) := by
    -- The counit pullback is the inverse of the unit by the right triangle identity.
    apply (CategoryTheory.cancel_epi η).1
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ η) hright
  exact ⟨⟨η, hleft, hright⟩⟩

-- Proof comment: the left triangle identity for `i⁻¹[U] ⊣ i_*[U]` makes the pullback of the
-- unit a split mono whose retraction is the closed-subset counit, and that counit is already an
-- isomorphism by the Chapter 6 owner theorem.
/-- Helper for Lemma 17.7.1: after pulling back to the closed complement, the unit
`ℱ ⟶ i_* i^{-1} ℱ` becomes an isomorphism. -/
private theorem closedComplementPulledBackUnit_isIso
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    IsIso ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i[U]).map ((iAdj[U]).unit.app ℱ)) := by
  let L := TopCat.Sheaf.pullback AddCommGrpCat.{u} i[U]
  let ε := (iAdj[U]).counit.app (L.obj ℱ)
  have hε : IsIso ε := by
    simpa [L] using
      (subsetSheaf_pullback_pushforward_counit_isIso
        (X := X) (C := AddCommGrpCat.{u}) (Z := ((U : Set X)ᶜ)) (ℱ := L.obj ℱ))
  letI : IsIso ε := hε
  have htriangle : L.map ((iAdj[U]).unit.app ℱ) ≫ ε = 𝟙 (L.obj ℱ) := by
    simpa [L] using (iAdj[U]).left_triangle_components ℱ
  have hback : ε ≫ L.map ((iAdj[U]).unit.app ℱ) = 𝟙 (L.obj ((i_*[U]).obj (L.obj ℱ))) := by
    simpa [L] using (iAdj[U]).right_triangle_components (L.obj ℱ)
  exact ⟨⟨ε, htriangle, hback⟩⟩

-- Proof comment: pull the counit map back to the open subspace, identify that pullback with the
-- pulled-back counit as an isomorphism via stalk-pullback naturality, and package the transport
-- into a separate comparison lemma before cancelling the pullback stalk isomorphism.
/-- Helper for Lemma 17.7.1: on the inside branch `x ∈ U`, the stalk map of the counit composed
with the stalk pullback comparison is the canonical stalk identification coming from the unit
isomorphism of the open-subset adjunction. -/
private theorem openSubsetCounitCompStalkPullbackIso_eq_of_mem
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∈ (U : Set X)) :
    let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
    let h : (j! U) ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) :=
      OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
    let R := TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)
    let explicit :
        (((j! U).obj (R.obj ℱ)).presheaf.stalk x) ≅ (R.obj ℱ).presheaf.stalk xU :=
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj ℱ))
          xU) ≪≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso
          ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso
            (asIso (h.unit.app (R.obj ℱ))))).symm
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (h.counit.app ℱ).hom) ≫
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ℱ xU).hom =
      explicit.hom := by
  -- Route correction: isolate the inside-`U` transport once, then reuse it in the final `IsIso`
  -- proof instead of rewriting the same stalk-pullback naturality square inline.
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  let h : (j! U) ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let R := TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)
  have hunit : IsIso (h.unit.app (R.obj ℱ)) := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
      (R.obj ℱ))
    infer_instance
  letI : IsIso (h.unit.app (R.obj ℱ)) := hunit
  let explicit :
      (((j! U).obj (R.obj ℱ)).presheaf.stalk x) ≅ (R.obj ℱ).presheaf.stalk xU :=
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj ℱ))
        xU) ≪≫
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso
          (asIso (h.unit.app (R.obj ℱ))))).symm
  let e : R.obj ℱ ≅ R.obj ((j! U).obj (R.obj ℱ)) :=
    (OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).app (R.obj ℱ)
  let eStalk :
      (((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
          ((j! U).obj (R.obj ℱ))).presheaf.stalk xU) ≅
        (R.obj ℱ).presheaf.stalk xU :=
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso
      ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso
        (asIso (h.unit.app (R.obj ℱ))))).symm
  have hright :
      R.map (h.counit.app ℱ) = inv (h.unit.app (R.obj ℱ)) := by
    -- The adjunction right triangle identifies the pulled-back counit with the inverse unit.
    apply (CategoryTheory.cancel_mono e.hom).1
    simpa [e, R] using h.right_triangle_components ℱ
  have hnat :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (h.counit.app ℱ).hom) ≫
          (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ℱ xU).hom =
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
            ((j! U).obj (R.obj ℱ)) xU).hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
            (R.map (h.counit.app ℱ)).hom) := by
    -- Move the counit through the stalk pullback comparison.
    simpa [R] using
      sheaf_stalkPullbackIso_hom_naturality
        (f := extensionByZeroOpenSubsetInclusion U) (η := h.counit.app ℱ) (x := xU)
  rw [hnat]
  have hforget :
      (R.map (h.counit.app ℱ)).hom =
        (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
          (inv (h.unit.app (R.obj ℱ))) := by
    -- Forgetting to presheaves turns the adjunction-level identity into an equality of morphisms
    -- in `AddCommGrpCat`.
    simpa [hright] using congrArg
      (fun k ↦ (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map k)
      hright
  letI :
      IsIso
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
          (h.unit.app (R.obj ℱ))) := by
    infer_instance
  letI :
      IsIso
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
          ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
            (h.unit.app (R.obj ℱ)))) := by
    infer_instance
  have hstalk :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map (R.map (h.counit.app ℱ)).hom) =
        eStalk.hom := by
    -- The stalk image of the pulled-back counit is the inverse of the stalk image of the unit.
    rw [hforget]
    have hforgetInv :
        (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
            (inv (h.unit.app (R.obj ℱ))) =
          inv
            ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
              (h.unit.app (R.obj ℱ))) := by
      exact Functor.map_inv
        (TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U))
        (h.unit.app (R.obj ℱ))
    rw [hforgetInv]
    have heStalk :
        eStalk.hom =
          inv
            ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
              ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
                (h.unit.app (R.obj ℱ)))) := by
      simp [eStalk]
    exact
      (Functor.map_inv (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU)
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).map
          (h.unit.app (R.obj ℱ)))).trans heStalk.symm
  have hcomp :
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
          ((j! U).obj (R.obj ℱ)) xU).hom ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).map
          (R.map (h.counit.app ℱ)).hom) =
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
          ((j! U).obj (R.obj ℱ)) xU).hom ≫
        eStalk.hom := by
    -- Replace the pulled-back counit by the explicit inverse of the unit on stalks.
    simpa using congrArg
      (fun k ↦
        (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
          ((j! U).obj (R.obj ℱ)) xU).hom ≫ k)
      hstalk
  have hfinal :
      (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
          ((j! U).obj (R.obj ℱ)) xU).hom ≫
        eStalk.hom =
      explicit.hom := by
    simp [explicit, eStalk, Category.assoc]
  exact hcomp.trans hfinal

-- Proof comment: after the previous comparison lemma, the final `IsIso` proof is just cancellation
-- of the stalk pullback isomorphism on the right.
/-- Helper for Lemma 17.7.1: at a point of `U`, the stalk map of the counit
`j_! j^{-1} ℱ ⟶ ℱ` is an isomorphism. -/
private theorem openSubsetCounitStalkIsoOfMem
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∈ (U : Set X)) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (((jAdj[U]).counit.app ℱ).hom)) := by
  let h : (j! U) ⊣ TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) :=
    OpenSubsetExtensionByInitial.sheafExtensionByInitialAdjunction U
  let xU : extensionByZeroOpenSubsetSpace U := ⟨x, hx⟩
  let R := TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)
  have hunit : IsIso (h.unit.app (R.obj ℱ)) := by
    change IsIso ((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso U).hom.app
      (R.obj ℱ))
    infer_instance
  let explicit :
      (((j! U).obj (R.obj ℱ)).presheaf.stalk x) ≅ (R.obj ℱ).presheaf.stalk xU :=
    (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ((j! U).obj (R.obj ℱ))
        xU) ≪≫
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xU).mapIso
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso
          (asIso (h.unit.app (R.obj ℱ))))).symm
  have hComp :
      IsIso
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (h.counit.app ℱ).hom) ≫
          (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ℱ xU).hom) := by
    rw [openSubsetCounitCompStalkPullbackIso_eq_of_mem U ℱ x hx]
    infer_instance
  have :
      IsIso
        ((((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
              (h.counit.app ℱ).hom) ≫
            (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ℱ xU).hom) ≫
          inv (TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U) ℱ xU).hom) := by
    exact inferInstance
  simpa [Category.assoc] using this

-- Proof comment: pull the unit map back to the closed complement, identify that pullback with the
-- inverse of the closed-subset counit isomorphism, and transport the result back to the ambient
-- point.
/-- Helper for Lemma 17.7.1: at a point outside `U`, the stalk map of the unit
`ℱ ⟶ i_* i^{-1} ℱ` is an isomorphism. -/
private theorem closedComplementUnitStalkIsoOfNotMem
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∉ (U : Set X)) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (((iAdj[U]).unit.app ℱ).hom)) := by
  let xZ : TopCat.of ((U : Set X)ᶜ) := ⟨x, hx⟩
  let α := TopCat.Sheaf.stalkPullbackIso i[U] ℱ xZ
  let β := TopCat.Sheaf.stalkPullbackIso i[U] ((i_*[U]).obj ((i⁻¹[U]).obj ℱ)) xZ
  have hpull :
      IsIso ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i[U]).map ((iAdj[U]).unit.app ℱ)) :=
    closedComplementPulledBackUnit_isIso U ℱ
  letI :
      IsIso ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i[U]).map ((iAdj[U]).unit.app ℱ)) := hpull
  have hnat :
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (((iAdj[U]).unit.app ℱ).hom)) ≫
          β.hom =
        α.hom ≫
          ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} xZ).map
            (((TopCat.Sheaf.pullback AddCommGrpCat.{u} i[U]).map ((iAdj[U]).unit.app ℱ)).hom)) := by
    simpa [α, β] using
      (sheaf_stalkPullbackIso_hom_naturality (f := i[U]) (η := (iAdj[U]).unit.app ℱ) (x := xZ))
  have hComp :
      IsIso
        (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (((iAdj[U]).unit.app ℱ).hom)) ≫
          β.hom) := by
    rw [hnat]
    infer_instance
  have :
      IsIso
        ((((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (((iAdj[U]).unit.app ℱ).hom)) ≫
            β.hom) ≫ inv β.hom) := by
    exact inferInstance
  simpa [Category.assoc] using this

-- Proof comment: reduce equality of sheaf morphisms to equality of presheaf morphisms, then
-- check sections by the standard "all germs vanish" criterion.
/-- Helper for Chap17 Lemma 17 7 1: a morphism of abelian sheaves is zero if all of its stalk
maps vanish. -/
private theorem abelianSheafHom_eq_zero_of_stalkZero
    {𝒜 ℬ : X.Sheaf AddCommGrpCat.{u}} (φ : 𝒜 ⟶ ℬ)
    (hφ : ∀ x : X,
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.hom = 0) :
    φ = 0 := by
  apply TopCat.Sheaf.hom_ext
  apply NatTrans.ext
  intro V
  ext s x hx
  -- The germ detects the value of a section after applying a presheaf morphism.
  have hgerm :=
    congrArg (fun k ↦ k (𝒜.presheaf.germ V.unop x hx s)) (hφ x)
  simpa [TopCat.Presheaf.stalkFunctor_map_germ_apply] using hgerm

-- Proof comment: the stalk composite vanishes branchwise because one of the two stalk objects is
-- zero on each branch of `x ∈ U`.
/-- Helper for Chap17 Lemma 17 7 1: the stalk map of the open/closed composite is zero. -/
private theorem openClosedComplementAbelianSheaf_stalkComp_zero
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((((jAdj[U]).counit.app ℱ) ≫ ((iAdj[U]).unit.app ℱ)).hom) = 0 := by
  rw [Functor.map_comp]
  by_cases hx : x ∈ (U : Set X)
  · -- Inside `U`, the target stalk is zero, so every map into it is zero.
    exact addCommGrpHom_eq_of_isZero
      (closedComplementPushforward_stalk_isZero_of_mem U ℱ x hx)
      _ _
  · -- Outside `U`, the source stalk is zero, so every map out of it is zero.
    exact addCommGrpHom_eq_of_isZero
      (openSubsetExtensionByInitial_stalk_isZero_of_not_mem U ((i⁻¹[U]).obj ℱ) x hx)
      _ _

-- Proof comment: exactness of the stalk complex is checked by the same open/closed branch split,
-- using the stalk isomorphism on the nonzero side and the zero stalk on the complementary side.
/-- Helper for Chap17 Lemma 17 7 1: the two stalk maps form an exact sequence of functions. -/
private theorem openClosedComplementAbelianSheaf_stalkFunctionExact
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) (x : X) :
    Function.Exact
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (((jAdj[U]).counit.app ℱ).hom))
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (((iAdj[U]).unit.app ℱ).hom)) := by
  let f :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (((jAdj[U]).counit.app ℱ).hom)
  let g :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (((iAdj[U]).unit.app ℱ).hom)
  by_cases hx : x ∈ (U : Set X)
  · -- Proof comment: on `U`, the counit stalk map is an isomorphism, so every element of the
    -- middle stalk already lies in its range.
    refine Function.Exact.of_comp_of_mem_range ?_ ?_
    · -- Proof comment: the stalk composite is already known to be zero.
      simpa [f, g] using
        congrArg DFunLike.coe (openClosedComplementAbelianSheaf_stalkComp_zero U ℱ x)
    · intro y _hy
      have hsurj : Function.Surjective f := by
        letI : IsIso f := by
          simpa [f] using openSubsetCounitStalkIsoOfMem U ℱ x hx
        exact (ConcreteCategory.bijective_of_isIso f).2
      obtain ⟨z, rfl⟩ := hsurj y
      exact ⟨z, rfl⟩
  · -- Proof comment: outside `U`, the unit stalk map is an isomorphism, so its kernel is zero.
    refine Function.Exact.of_comp_of_mem_range ?_ ?_
    · -- Proof comment: the stalk composite is already known to be zero.
      simpa [f, g] using
        congrArg DFunLike.coe (openClosedComplementAbelianSheaf_stalkComp_zero U ℱ x)
    · intro y hy
      have hinj : Function.Injective g := by
        letI : IsIso g := by
          simpa [g] using closedComplementUnitStalkIsoOfNotMem U ℱ x hx
        exact (ConcreteCategory.bijective_of_isIso g).1
      have hy0 : y = 0 := hinj <| by simpa using hy
      refine ⟨0, ?_⟩
      change f 0 = y
      rw [hy0]
      exact map_zero f

-- Proof comment: injectivity of the counit on stalks is checked by the same open/closed branch
-- split used for exactness.
/-- Helper for Chap17 Lemma 17 7 1: every stalk map of the counit `j_! j^{-1} ℱ ⟶ ℱ` is
injective. -/
private theorem openClosedComplementAbelianSheaf_stalkCounitInjective
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) (x : X) :
    Function.Injective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (((jAdj[U]).counit.app ℱ).hom)) := by
  let f :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (((jAdj[U]).counit.app ℱ).hom)
  by_cases hx : x ∈ (U : Set X)
  · -- Proof comment: on `U`, the counit stalk map is an isomorphism.
    letI : IsIso f := by
      simpa [f] using openSubsetCounitStalkIsoOfMem U ℱ x hx
    simpa [f] using (ConcreteCategory.bijective_of_isIso f).1
  · -- Proof comment: outside `U`, the source stalk is zero, hence every two source elements
    -- coincide.
    let hsub :
        Subsingleton (((j! U).obj ((i⁻¹[U]).obj ℱ)).presheaf.stalk x) :=
      (AddCommGrpCat.isZero_iff_subsingleton).1
        (openSubsetExtensionByInitial_stalk_isZero_of_not_mem U ((i⁻¹[U]).obj ℱ) x hx)
    intro a b _hab
    exact hsub.elim _ _

-- Proof comment: surjectivity of the unit on stalks is again branchwise: on `U` the target stalk
-- is zero, and outside `U` the unit stalk map is an isomorphism.
/-- Helper for Chap17 Lemma 17 7 1: every stalk map of the unit `ℱ ⟶ i_* i^{-1} ℱ` is
surjective. -/
private theorem openClosedComplementAbelianSheaf_stalkUnitSurjective
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) (x : X) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (((iAdj[U]).unit.app ℱ).hom)) := by
  let g :=
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (((iAdj[U]).unit.app ℱ).hom)
  by_cases hx : x ∈ (U : Set X)
  · -- Proof comment: on `U`, the target stalk is zero, so every element equals the image of `0`.
    let hsub :
        Subsingleton (((i_*[U]).obj ((i⁻¹[U]).obj ℱ)).presheaf.stalk x) :=
      (AddCommGrpCat.isZero_iff_subsingleton).1
        (closedComplementPushforward_stalk_isZero_of_mem U ℱ x hx)
    intro y
    refine ⟨0, ?_⟩
    exact hsub.elim _ _
  · -- Proof comment: outside `U`, the unit stalk map is an isomorphism.
    letI : IsIso g := by
      simpa [g] using closedComplementUnitStalkIsoOfNotMem U ℱ x hx
    simpa [g] using (ConcreteCategory.bijective_of_isIso g).2

-- Proof comment: stalkwise surjectivity is exactly the locally-surjective criterion for sheaf
-- epimorphisms in this concrete abelian setting.
/-- Helper for Chap17 Lemma 17 7 1: a morphism of abelian sheaves is epi iff its stalk maps are
surjective. -/
private theorem addCommGrpSheafEpiIffStalkSurjective
    {𝒜 ℬ : X.Sheaf AddCommGrpCat.{u}} (φ : 𝒜 ⟶ ℬ) :
    Epi φ ↔ ∀ x : X,
      Function.Surjective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map φ.hom) := by
  -- Proof comment: for additive sheaves, epimorphy is equivalent to local surjectivity, and local
  -- surjectivity is detected on all stalks.
  rw [← Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} φ]
  simpa using TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks φ.hom

-- Proof sketch: check the composite on stalks. At points of `U`, the first map is the identity on
-- stalks and the second map vanishes because the closed-complement pushforward has zero stalk
-- there; at points of `X \ U`, the first map vanishes because extension by zero has zero stalk.
/-- The two adjunction maps for an open subset and its closed complement compose to zero. -/
theorem openClosedComplementAbelianSheaf_comp_zero
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    ((jAdj[U]).counit.app ℱ) ≫ ((iAdj[U]).unit.app ℱ) =
      0 := by
  -- The composite is determined by its stalk maps, so it suffices to show each stalk map is zero.
  apply abelianSheafHom_eq_zero_of_stalkZero
  intro x
  simpa using openClosedComplementAbelianSheaf_stalkComp_zero U ℱ x

-- Proof sketch: use the stalkwise exactness criterion for sheaves of abelian groups. For `x ∈ U`,
-- identify the stalk of `j_! j^{-1} ℱ` with the stalk of `ℱ` and the stalk of `i_* i^{-1} ℱ`
-- with zero; for `x ∉ U`, identify the stalk of `j_! j^{-1} ℱ` with zero and the stalk of
-- `i_* i^{-1} ℱ` with the stalk over the closed complement. The resulting stalk complex is the
-- evident short exact sequence `0 → F_x → F_x → 0` or `0 → 0 → F_x → F_x`.
/-- Lemma 17.7.1: for an open subset `U ⊆ X` with closed complement `X \ U`, the adjunction maps
`j_! j^{-1} ℱ ⟶ ℱ` and `ℱ ⟶ i_* i^{-1} ℱ` form a short exact sequence of sheaves of abelian
groups on `X`. -/
@[stacks 02UT]
theorem openClosedComplementAbelianSheaf_shortExact
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (ShortComplex.mk
      ((jAdj[U]).counit.app ℱ)
      ((iAdj[U]).unit.app ℱ)
      (openClosedComplementAbelianSheaf_comp_zero U ℱ)).ShortExact := by
  let S : ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
    ShortComplex.mk
      ((jAdj[U]).counit.app ℱ)
      ((iAdj[U]).unit.app ℱ)
      (openClosedComplementAbelianSheaf_comp_zero U ℱ)
  change S.ShortExact
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Proof comment: exactness of a short complex of abelian sheaves is detected stalkwise.
    rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S := S)]
    intro x
    rw [ShortComplex.ab_exact_iff_function_exact]
    simpa [S, abelianSheafStalkFunctor] using
      openClosedComplementAbelianSheaf_stalkFunctionExact U ℱ x
  · -- Proof comment: monomorphy of the counit is detected on stalks by injectivity.
    rw [TopCat.Presheaf.mono_iff_stalk_mono]
    intro x
    rw [AddCommGrpCat.mono_iff_injective]
    simpa using openClosedComplementAbelianSheaf_stalkCounitInjective U ℱ x
  · -- Proof comment: epimorphy of the unit is detected on stalks by surjectivity.
    rw [addCommGrpSheafEpiIffStalkSurjective]
    intro x
    simpa using openClosedComplementAbelianSheaf_stalkUnitSurjective U ℱ x

end
