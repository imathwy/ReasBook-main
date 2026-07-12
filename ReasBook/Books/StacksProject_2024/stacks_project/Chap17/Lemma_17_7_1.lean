import Mathlib
import Mathlib.Topology.Sheaves.Abelian
import StacksProject_2024.Chap06.Lemma_6_31_6
import StacksProject_2024.Chap06.Lemma_6_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
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
  simpa using
    (closedSubsetAbelianSheaf_pushforward_stalk_isZero_of_not_mem
      (Z := ((U : Set X)ᶜ))
      (openSubsetComplement_isClosed (X := X) U)
      ((i⁻¹[U]).obj ℱ)
      (x := x)
      (by simpa using hx))

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
  let G := TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)
  haveI : IsIso ((jAdj[U]).unit.app (G.obj ℱ)) := by
    simpa [G] using
      (show IsIso
        (((OpenSubsetExtensionByInitial.sheafExtensionByInitialUnitIso
          (C := AddCommGrpCat.{u}) U).app (G.obj ℱ)).hom) from inferInstance)
  exact isIso_of_hom_comp_eq_id
    ((jAdj[U]).unit.app (G.obj ℱ))
    ((jAdj[U]).right_triangle_components ℱ)

-- Proof comment: the left triangle identity for `i⁻¹[U] ⊣ i_*[U]` makes the pullback of the
-- unit a split mono whose retraction is the closed-subset counit, and that counit is already an
-- isomorphism by the Chapter 6 owner theorem.
/-- Helper for Lemma 17.7.1: after pulling back to the closed complement, the unit
`ℱ ⟶ i_* i^{-1} ℱ` becomes an isomorphism. -/
private theorem closedComplementPulledBackUnit_isIso
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    IsIso ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i[U]).map ((iAdj[U]).unit.app ℱ)) := by
  let F := TopCat.Sheaf.pullback AddCommGrpCat.{u} i[U]
  haveI : IsIso ((iAdj[U]).counit.app (F.obj ℱ)) := by
    simpa [F] using subsetSheaf_pullback_pushforward_counit_isIso (F.obj ℱ)
  exact isIso_of_hom_comp_eq_id
    ((iAdj[U]).counit.app (F.obj ℱ))
    ((iAdj[U]).left_triangle_components ℱ)

-- Proof comment: pull the counit map back to the open subspace, identify that pullback with the
-- inverse of the unit isomorphism via the adjunction triangle identity, and then transport the
-- resulting stalk isomorphism back to the ambient point.
/-- Helper for Lemma 17.7.1: at a point of `U`, the stalk map of the counit
`j_! j^{-1} ℱ ⟶ ℱ` is an isomorphism. -/
private theorem openSubsetCounitStalkIsoOfMem
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) (x : X) (hx : x ∈ (U : Set X)) :
    IsIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (((jAdj[U]).counit.app ℱ).hom)) := by
  -- TODO: transport `openSubsetPulledBackCounit_isIso` to the ambient stalk map using
  -- `TopCat.Sheaf.stalkPullbackIso_hom_naturality` at the point `⟨x, hx⟩`.
  sorry

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
  -- TODO: transport `closedComplementPulledBackUnit_isIso` to the ambient stalk map using
  -- `TopCat.Sheaf.stalkPullbackIso_hom_naturality` at the complementary point `⟨x, hx⟩`.
  sorry

-- Proof sketch: check the composite on stalks. At points of `U`, the first map is the identity on
-- stalks and the second map vanishes because the closed-complement pushforward has zero stalk
-- there; at points of `X \ U`, the first map vanishes because extension by zero has zero stalk.
/-- The two adjunction maps for an open subset and its closed complement compose to zero. -/
theorem openClosedComplementAbelianSheaf_comp_zero
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    ((jAdj[U]).counit.app ℱ) ≫ ((iAdj[U]).unit.app ℱ) =
      0 := by
  -- TODO: compare sections via `CategoryTheory.Sheaf.hom_ext`, then use
  -- `TopCat.Presheaf.section_ext` and the inside/outside zero-stalk descriptions above.
  sorry

-- Proof sketch: use the stalkwise exactness criterion for sheaves of abelian groups. For `x ∈ U`,
-- identify the stalk of `j_! j^{-1} ℱ` with the stalk of `ℱ` and the stalk of `i_* i^{-1} ℱ`
-- with zero; for `x ∉ U`, identify the stalk of `j_! j^{-1} ℱ` with zero and the stalk of
-- `i_* i^{-1} ℱ` with the stalk over the closed complement. The resulting stalk complex is the
-- evident short exact sequence `0 → F_x → F_x → 0` or `0 → 0 → F_x → F_x`.
/-- Lemma 17.7.1: for an open subset `U ⊆ X` with closed complement `X \ U`, the adjunction maps
`j_! j^{-1} ℱ ⟶ ℱ` and `ℱ ⟶ i_* i^{-1} ℱ` form a short exact sequence of sheaves of abelian
groups on `X`. -/
theorem openClosedComplementAbelianSheaf_shortExact
    (U : Opens X) (ℱ : X.Sheaf AddCommGrpCat.{u}) :
    (ShortComplex.mk
      ((jAdj[U]).counit.app ℱ)
      ((iAdj[U]).unit.app ℱ)
      (openClosedComplementAbelianSheaf_comp_zero U ℱ)).ShortExact := by
  -- TODO: once the two ambient stalk isomorphism lemmas are proved, combine them with
  -- `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`, `TopCat.Presheaf.mono_iff_stalk_mono`,
  -- and stalkwise surjectivity of the unit map to obtain the short exact sequence.
  sorry

end
