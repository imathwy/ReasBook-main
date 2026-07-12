import StacksProject_2024.Chap21.Definition_21_44_1
import StacksProject_2024.Chap21.Lemma_21_44_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

/-
Domain-style sampling for Lemma 21.44.8:
- primary domain: localized derived restrictions of morphisms from strictly perfect complexes on
  the slice ringed site `(C/U, 𝒪_U)`;
- sampled owner declarations:
  `ringedSiteLocalizedRestriction`,
  `ringedSiteLocalizedRestriction_exact`,
  `ringedSiteLocalizedRestriction_additive`,
  `Functor.mapDerivedCategoryFactors`,
  `IsLocallyNullHomotopic`;
- best owner abstraction: the Chapter 18 localized restriction owner
  `ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) V` on the already localized ringed site,
  together with the Chapter 18 exact/additive instance API for its derived functor
  `res.mapDerivedCategory`; `mapDerivedCategoryFactors` remains only the bridge from owner-level
  derived restrictions to restricted chain maps;
- primitive data: localized complexes `E`, `F`, a derived morphism
  `α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F`, and a covering family of `U`;
- derived API: the direct cover-wise representation theorem in part `(1)`, together with the
  local null-homotopy consequence in part `(2)`.

Source/core/bridge triage:
- `source-facing`: the direct cover-wise representation statement in part `(1)` and the local
  null-homotopy statement in part `(2)`;
- `core/canonical`: `ringedSiteLocalizedRestriction`, `mapDerivedCategoryFactors`,
  and `CochainComplex.IsStrictlyPerfect`;
- `bridge/view`: the comparison of the owner-level restricted derived morphism
  `(res.mapDerivedCategory).map α` with `DerivedCategory.Q.map αi` through
  `res.mapDerivedCategoryFactors`.
-/
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasBinaryProducts C]
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {U : C}

local notation "ModLoc" => ringedSiteModuleCategory (J.over U) (𝒪.over U)

section Representation

variable [HasSheafify (J.over U) AddCommGrpCat]
variable [(J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ V : Over U, HasSheafify ((J.over U).over V) AddCommGrpCat]
variable [∀ V : Over U, ((J.over U).over V).WEqualsLocallyBijective AddCommGrpCat]
variable [∀ V : Over U, (ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) V).Additive]
variable [∀ V : Over U,
  PreservesFiniteLimits (ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) V)]
variable [∀ V : Over U,
  PreservesFiniteColimits (ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) V)]

local instance : Abelian ModLoc :=
  SheafOfModules.instAbelian (ringSheaf (J.over U) (𝒪.over U))

local instance localizedOverAbelian (V : Over U) :
    Abelian (ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)) :=
  SheafOfModules.instAbelian
    (ringSheaf ((J.over U).over V) ((𝒪.over U).over V))

local notation "res[" V "]" =>
  ringedSiteLocalizedRestriction (J.over U) (𝒪.over U) V

/-- A morphism in the localized derived category is locally represented by chain maps if, after
restricting to a cover of `U`, each restricted derived morphism fits into the canonical
comparison square with a morphism of restricted complexes. -/
def HasLocalChainMapRepresentation
    (E F : CochainComplex ModLoc ℤ)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) : Prop :=
  ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
    ∀ i : ι,
      let j := (res[cover i]).mapHomologicalComplex (up ℤ)
      ∃ αi : j.obj E ⟶ j.obj F,
        CommSq
          ((res[cover i]).mapDerivedCategory.map α)
          ((res[cover i].mapDerivedCategoryFactors.app E).hom)
          ((res[cover i].mapDerivedCategoryFactors.app F).hom)
          (DerivedCategory.Q.map αi)

omit [HasBinaryProducts C] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Unfolding `HasLocalChainMapRepresentation` gives the explicit cover-wise chain-map
representation criterion. -/
theorem hasLocalChainMapRepresentation_iff
    (E F : CochainComplex ModLoc ℤ)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    HasLocalChainMapRepresentation E F α ↔
      ∃ (ι : Type (max u v)) (cover : ι → Over U), (J.over U).CoversTop cover ∧
        ∀ i : ι,
          let j := (res[cover i]).mapHomologicalComplex (up ℤ)
          ∃ αi : j.obj E ⟶ j.obj F,
            CommSq
              ((res[cover i]).mapDerivedCategory.map α)
              ((res[cover i].mapDerivedCategoryFactors.app E).hom)
              ((res[cover i].mapDerivedCategoryFactors.app F).hom)
              (DerivedCategory.Q.map αi) :=
  Iff.rfl

-- Proof sketch: prove the source-facing cover-wise representation statement directly, using the
-- owner-level restricted derived functor `res[V].mapDerivedCategory` and the canonical comparison
-- `res[V].mapDerivedCategoryFactors.app _` to normalize each restricted derived morphism against
-- a restricted chain map.
/-- Lemma 21.44.8 (1): a morphism in the localized derived category from a strictly perfect
complex is locally represented by a morphism of complexes after restricting to a cover of `U`. -/
@[stacks 08FR]
theorem exists_cover_restriction_eq_Q_map_of_isStrictlyPerfect
    (E F : CochainComplex ModLoc ℤ)
    (α : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)
    (hE : CochainComplex.IsStrictlyPerfect E) :
    HasLocalChainMapRepresentation E F α := sorry

end Representation

section NullHomotopy

local instance : Abelian ModLoc :=
  SheafOfModules.instAbelian (ringSheaf (J.over U) (𝒪.over U))

-- Proof sketch: part `(2)` should consume the refined owner theorem from part `(1)`, rather than
-- duplicating its quantified local data, and then turn vanishing of the restricted derived
-- morphisms into local null-homotopies.
/-- Lemma 21.44.8 (2): if a morphism of complexes from a strictly perfect complex becomes zero in
the localized derived category, then after restricting to a cover of `U` it is homotopic to
zero. -/
@[stacks 08FR]
theorem exists_cover_homotopicToZero_of_isStrictlyPerfect_of_Q_map_eq_zero
    {E F : CochainComplex ModLoc ℤ} (α : E ⟶ F)
    (hE : CochainComplex.IsStrictlyPerfect E)
    (hα : DerivedCategory.Q.map α =
      (0 : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F)) :
    IsLocallyNullHomotopic α := sorry

end NullHomotopy

end SheafOfModules.RingedSite
