import Mathlib.Data.List.TFAE
import Mathlib.Algebra.Category.Ring.Limits
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap20.Global_sections_module_owners_core
import StacksProject_2024.Chap20.Open_subspace_module_core
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped RingedSpace.Hom

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [∀ U : Opens X.carrier,
  HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
variable [∀ U : Opens X.carrier,
  ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : Opens X.carrier,
  ((Opens.grothendieckTopology X).over U).HasSheafCompose
    (forget₂ RingCat AddCommGrpCat.{u})]
variable [∀ U : Opens X.carrier,
  HasWeakSheafify (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}]
variable [∀ U : Opens X.carrier,
  (Opens.grothendieckTopology (TopCat.of U)).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [∀ U : Opens X.carrier,
  (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier).HasSheafCompose
    (forget₂ RingCat AddCommGrpCat.{u})]

/-
Domain-style sampling for Lemma 20.49.3:
- primary domain: perfect derived `𝒪_X`-modules and local finite locally free / finite
  free representatives on open covers;
- sampled owner declarations:
  `TopologicalSpace.IsOpenCover`,
  `ModuleDerived`,
  `restrictedModuleDerivedOnOpen`,
  `openSubspaceModuleCategory`,
  `SheafOfModules.IsFiniteLocallyFree`,
  `DerivedCategory.IsPerfect`,
  `DerivedCategory.isPerfect_iff_exists_openCover`;
- best owner abstraction:
  `source-facing`: the two local representative criteria in this lemma;
  `core/canonical`: `TopologicalSpace.IsOpenCover`, `ModuleDerived X`,
    `restrictedModuleDerivedOnOpen`, `openSubspaceModuleCategory X U`, and
    `DerivedCategory.IsPerfect`;
  `bridge/view`: the TFAE theorem below, relating perfectness to the two source-facing local
    representative conditions via the Chapter 20 perfect-open-cover owner
    `DerivedCategory.isPerfect_iff_exists_openCover`.

Primitive data are an indexed open cover and bounded local complexes on the intrinsic restricted
ringed spaces `X|_{U_i}`. The local representative criteria should therefore be stated directly
through the Chapter 20 open-subspace owners `openSubspaceModuleCategory`,
`restrictedModuleDerivedOnOpen`, and the ringed-space owner
`SheafOfModules.IsFiniteLocallyFree` on each restricted ringed space, rather than by expanding
those owners or by introducing an extra global representative of `E`.
-/
local notation "DModX" => ModuleDerived X
local notation "OpenComplex" U => CochainComplex (openSubspaceModuleCategory X U) ℤ

local instance restrictRingedSpace_hasWeakSheafify (U : Opens X.carrier) :
    HasWeakSheafify
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      AddCommGrpCat.{u} := by
  change HasWeakSheafify (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}
  infer_instance

local instance restrictRingedSpace_sheafToPresheaf_isRightAdjoint (U : Opens X.carrier) :
    (sheafToPresheaf
      (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier)
      AddCommGrpCat.{u}).IsRightAdjoint := by
  change (sheafToPresheaf (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}).IsRightAdjoint
  exact (sheafificationAdjunction
      (Opens.grothendieckTopology (TopCat.of U))
      AddCommGrpCat.{u}).isRightAdjoint

local instance restrictRingedSpace_wEqualsLocallyBijective (U : Opens X.carrier) :
    (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u} := by
  change (Opens.grothendieckTopology (TopCat.of U)).WEqualsLocallyBijective AddCommGrpCat.{u}
  infer_instance

namespace DerivedCategory

/-- An object of `D(𝒪_X)` admits a finite-locally-free representative on an open cover
if, after restricting to each member of some open cover, it is represented by a bounded complex
whose terms are finite locally free `𝒪`-modules on that open subspace. -/
def HasFiniteLocallyFreeRepresentativeOnOpenCover (E : DModX) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X.carrier),
    IsOpenCover U ∧
      ∀ i : ι, ∃ Ei : OpenComplex (U i),
        ∃ _ : DerivedCategory.Q.obj Ei ≅ E↾[U i],
          ∃ a b : ℤ, Ei.IsStrictlyGE a ∧ Ei.IsStrictlyLE b ∧
            ∀ j : ℤ, SheafOfModules.IsFiniteLocallyFree (Ei.X j)

/-- An object of `D(𝒪_X)` admits a finite-free representative on an open cover if,
after restricting to each member of some open cover, it is represented by a bounded complex whose
terms are finite free `𝒪`-modules on that open subspace. -/
def HasFiniteFreeRepresentativeOnOpenCover (E : DModX) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X.carrier),
    IsOpenCover U ∧
      ∀ i : ι, ∃ Ei : OpenComplex (U i),
        ∃ _ : DerivedCategory.Q.obj Ei ≅ E↾[U i],
          ∃ a b : ℤ, Ei.IsStrictlyGE a ∧ Ei.IsStrictlyLE b ∧
            ∀ j : ℤ, SheafOfModules.IsFiniteFree (Ei.X j)

omit [∀ U : Opens X.carrier,
  HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
  [∀ U : Opens X.carrier,
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Opens X.carrier,
    ((Opens.grothendieckTopology X).over U).HasSheafCompose
      (forget₂ RingCat AddCommGrpCat.{u})] in
omit [∀ U : Opens X.carrier,
  HasWeakSheafify (Opens.grothendieckTopology (TopCat.of U)) AddCommGrpCat.{u}]
  [∀ U : Opens X.carrier,
    (Opens.grothendieckTopology (TopCat.of U)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
omit [∀ U : Opens X.carrier,
  (Opens.grothendieckTopology (X.restrict U.isOpenEmbedding).carrier).HasSheafCompose
    (forget₂ RingCat AddCommGrpCat.{u})] in
/-- Unfolding `HasFiniteLocallyFreeRepresentativeOnOpenCover` gives the open-cover criterion by
bounded complexes whose terms are finite locally free on each member of the cover. -/
theorem hasFiniteLocallyFreeRepresentativeOnOpenCover_iff (E : DModX) :
    HasFiniteLocallyFreeRepresentativeOnOpenCover E ↔
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        IsOpenCover U ∧
          ∀ i : ι, ∃ Ei : OpenComplex (U i),
            ∃ _ : DerivedCategory.Q.obj Ei ≅ E↾[U i],
              ∃ a b : ℤ, Ei.IsStrictlyGE a ∧ Ei.IsStrictlyLE b ∧
                ∀ j : ℤ, SheafOfModules.IsFiniteLocallyFree (Ei.X j) :=
  Iff.rfl

omit [∀ U : Opens X.carrier,
  HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
  [∀ U : Opens X.carrier,
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Opens X.carrier,
    ((Opens.grothendieckTopology X).over U).HasSheafCompose
      (forget₂ RingCat AddCommGrpCat.{u})] in
/-- Unfolding `HasFiniteFreeRepresentativeOnOpenCover` gives the open-cover criterion by bounded
complexes whose terms are finite free on each member of the cover. -/
theorem hasFiniteFreeRepresentativeOnOpenCover_iff (E : DModX) :
    HasFiniteFreeRepresentativeOnOpenCover E ↔
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        IsOpenCover U ∧
          ∀ i : ι, ∃ Ei : OpenComplex (U i),
            ∃ _ : DerivedCategory.Q.obj Ei ≅ E↾[U i],
              ∃ a b : ℤ, Ei.IsStrictlyGE a ∧ Ei.IsStrictlyLE b ∧
                ∀ j : ℤ, SheafOfModules.IsFiniteFree (Ei.X j) :=
  Iff.rfl

omit [∀ U : Opens X.carrier,
  HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}]
  [∀ U : Opens X.carrier,
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Opens X.carrier,
    ((Opens.grothendieckTopology X).over U).HasSheafCompose
      (forget₂ RingCat AddCommGrpCat.{u})] in
/-- A finite-free local representative is, termwise, a finite-locally-free local representative. -/
theorem hasFiniteLocallyFreeRepresentativeOnOpenCover_of_hasFiniteFreeRepresentativeOnOpenCover
    {E : DModX} (hE : HasFiniteFreeRepresentativeOnOpenCover E) :
    HasFiniteLocallyFreeRepresentativeOnOpenCover E := by
  rcases (hasFiniteFreeRepresentativeOnOpenCover_iff E).1 hE with ⟨ι, U, hU, hrep⟩
  refine (hasFiniteLocallyFreeRepresentativeOnOpenCover_iff E).2 ?_
  refine ⟨ι, U, hU, ?_⟩
  intro i
  rcases hrep i with ⟨Ei, eEi, a, b, hge, hle, hterms⟩
  refine ⟨Ei, eEi, a, b, hge, hle, ?_⟩
  intro j
  letI : SheafOfModules.IsFiniteFree (Ei.X j) := hterms j
  exact SheafOfModules.isFiniteLocallyFree_of_isFiniteFree (Ei.X j)

-- Proof sketch: `(1) → (2)` uses Lemma `20.49.2` to choose a perfect representative and then
-- applies Lemma `17.14.6` termwise on the open subspaces, using the local-ring hypothesis on
-- stalks. `(2) → (3)` refines the cover so that each finite locally free term becomes finite free
-- on smaller opens. `(3) → (1)` applies Lemma `20.49.2` again, since a bounded complex of finite
-- free modules is in particular strictly perfect on each member of the chosen cover.
/-- Lemma 20.49.3: for an object `E` of `D(𝒪_X)` on a ringed space whose stalk rings are
local, the following are equivalent: `E` is perfect, `E` is locally represented by bounded
complexes of finite locally free modules, and `E` is locally represented by bounded complexes of
finite free modules. -/
@[stacks 0BCJ]
theorem perfect_tfae_exists_cover_termwise_finiteLocallyFree_exists_cover_termwise_finiteFree
    (E : DModX) (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    ([ IsPerfect E
      , HasFiniteLocallyFreeRepresentativeOnOpenCover E
      , HasFiniteFreeRepresentativeOnOpenCover E
      ] : List Prop).TFAE := sorry

/-- On a ringed space with local stalk rings, a derived `𝒪_X`-module is perfect if and only if
it admits a bounded local representative whose terms are finite locally free on some open cover. -/
theorem isPerfect_iff_hasFiniteLocallyFreeRepresentativeOnOpenCover
    (E : DModX) (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    IsPerfect E ↔ HasFiniteLocallyFreeRepresentativeOnOpenCover E := by
  have hTFAE :
      ([ IsPerfect E
        , HasFiniteLocallyFreeRepresentativeOnOpenCover E
        , HasFiniteFreeRepresentativeOnOpenCover E
        ] : List Prop).TFAE :=
    perfect_tfae_exists_cover_termwise_finiteLocallyFree_exists_cover_termwise_finiteFree E hlocal
  exact hTFAE.out 0 1 (by simp) (by simp)

/-- On a ringed space with local stalk rings, a derived `𝒪_X`-module is perfect if and only if
it admits a bounded local representative whose terms are finite free on some open cover. -/
theorem isPerfect_iff_hasFiniteFreeRepresentativeOnOpenCover
    (E : DModX) (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    IsPerfect E ↔ HasFiniteFreeRepresentativeOnOpenCover E := by
  have hTFAE :
      ([ IsPerfect E
        , HasFiniteLocallyFreeRepresentativeOnOpenCover E
        , HasFiniteFreeRepresentativeOnOpenCover E
        ] : List Prop).TFAE :=
    perfect_tfae_exists_cover_termwise_finiteLocallyFree_exists_cover_termwise_finiteFree E hlocal
  exact hTFAE.out 0 2 (by simp) (by simp)

/-- On a ringed space with local stalk rings, the finite-locally-free and finite-free open-cover
representative criteria for `E` are equivalent. -/
theorem hasFiniteLocallyFreeRepresentativeOnOpenCover_iff_hasFiniteFreeRepresentativeOnOpenCover
    (E : DModX) (hlocal : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    HasFiniteLocallyFreeRepresentativeOnOpenCover E ↔
      HasFiniteFreeRepresentativeOnOpenCover E := by
  have hTFAE :
      ([ IsPerfect E
        , HasFiniteLocallyFreeRepresentativeOnOpenCover E
        , HasFiniteFreeRepresentativeOnOpenCover E
        ] : List Prop).TFAE :=
    perfect_tfae_exists_cover_termwise_finiteLocallyFree_exists_cover_termwise_finiteFree E hlocal
  exact hTFAE.out 1 2 (by simp) (by simp)

end DerivedCategory
end AlgebraicGeometry.RingedSpace
