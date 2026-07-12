import StacksProject_2024.Chap10.Definition_10_63_1
import StacksProject_2024.Chap17.Definition_17_12_1
import StacksProject_2024.Chap17.Definition_17_23_1
import StacksProject_2024.Chap18.IdealSectionIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry SheafOfModules.AnnihilatorSheaf

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme}
variable [MonoidalCategory (SheafOfModules (RingedSpace.ringCatSheaf X.toSheafedSpace))]
variable [MonoidalClosed (SheafOfModules (RingedSpace.ringCatSheaf X.toSheafedSpace))]

local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : X.Modules)

-- Semantic recall: `lean_leansearch` surfaced `IsLocallyNoetherian` and
-- `Scheme.IdealSheafData.subscheme`; local Chapter 17/31 precedent fixes the annihilator as
-- `SheafOfModules.annihilator`, no embedded associated points as `embeddedAssociatedPoints = ∅`,
-- and closed-subscheme pushforward as `Scheme.Modules.pushforward`.
-- The imported Chapter 17/31 support and associated-point owners are currently blocked by the
-- default stalk-module universe, so this item keeps equivalent stalkwise bridges locally.

/-- The support of a scheme module, expressed as nonvanishing of the underlying additive stalk. -/
def stalkModuleSupport (ℱ : X.Modules) : Set X :=
  {x : X | ¬ IsZero (TopCat.Presheaf.stalk ℱ.val.presheaf x)}

/-- Membership in `stalkModuleSupport` is nonvanishing of the underlying additive stalk. -/
theorem mem_stalkModuleSupport_iff (ℱ : X.Modules) (x : X) :
    x ∈ stalkModuleSupport ℱ ↔ ¬ IsZero (TopCat.Presheaf.stalk ℱ.val.presheaf x) := sorry

/-- The associated points of a scheme module via the usual stalkwise associated-prime condition. -/
def stalkAssociatedPoints (ℱ : X.Modules) : Set X :=
  {x : X | IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
    associatedPrimesOfModule (X.presheaf.stalk x)
      (RingedSpace.stalkModuleCat ℱ (x : X.toRingedSpace))}

/-- Membership in `stalkAssociatedPoints` is the stalkwise associated-prime condition. -/
theorem mem_stalkAssociatedPoints_iff (ℱ : X.Modules) (x : X) :
    x ∈ stalkAssociatedPoints ℱ ↔
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
        associatedPrimesOfModule (X.presheaf.stalk x)
          (RingedSpace.stalkModuleCat ℱ (x : X.toRingedSpace)) := sorry

/-- A point is embedded associated for a module when it is associated and is the specialization of
a distinct associated point. -/
def stalkEmbeddedAssociatedAt (ℱ : X.Modules) (x : X) : Prop :=
  x ∈ stalkAssociatedPoints ℱ ∧
    ∃ y : X, y ∈ stalkAssociatedPoints ℱ ∧ y ≠ x ∧ y ⤳ x

/-- Membership in `stalkEmbeddedAssociatedAt` unfolds to the associated-point specialization
condition. -/
theorem stalkEmbeddedAssociatedAt_iff (ℱ : X.Modules) (x : X) :
    stalkEmbeddedAssociatedAt ℱ x ↔
      x ∈ stalkAssociatedPoints ℱ ∧
        ∃ y : X, y ∈ stalkAssociatedPoints ℱ ∧ y ≠ x ∧ y ⤳ x := sorry

/-- The set of embedded associated points of a scheme module. -/
def stalkEmbeddedAssociatedPoints (ℱ : X.Modules) : Set X :=
  {x | stalkEmbeddedAssociatedAt ℱ x}

/-- Membership in `stalkEmbeddedAssociatedPoints` is the embedded-associated-point predicate. -/
theorem mem_stalkEmbeddedAssociatedPoints_iff (ℱ : X.Modules) (x : X) :
    x ∈ stalkEmbeddedAssociatedPoints ℱ ↔ stalkEmbeddedAssociatedAt ℱ x := sorry

/-- The embedded points of a scheme, defined as embedded associated points of its structure
sheaf. -/
abbrev stalkEmbeddedPoints (Y : Scheme) : Set Y :=
  stalkEmbeddedAssociatedPoints (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)

/-- Membership in `stalkEmbeddedPoints` means being embedded associated for the structure sheaf. -/
theorem mem_stalkEmbeddedPoints_iff (Y : Scheme) (y : Y) :
    y ∈ stalkEmbeddedPoints Y ↔
      stalkEmbeddedAssociatedAt (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) y := sorry

/-- The ideal subsheaf `Ker(𝒪_X → 𝓗om(ℱ, ℱ))`, viewed as a subobject of the structure sheaf. -/
@[stacks 02OM]
abbrev annihilatorIdealSubobject (ℱ : X.Modules) : Subobject 𝒪X :=
  Subobject.mk (SheafOfModules.annihilatorι ℱ)

/-- The affine-open ideal sheaf data attached to the annihilator subsheaf
`Ker(𝒪_X → 𝓗om(ℱ, ℱ))`. -/
@[stacks 02OM]
def annihilatorIdealSheaf (ℱ : X.Modules) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U : X.affineOpens ↦
    SheafOfModules.RingedSite.idealSectionIdeal
      (annihilatorIdealSubobject ℱ) (op (U : X.Opens))

/-- On each affine open, `annihilatorIdealSheaf` is the ideal of sections cut out by the
annihilator subsheaf. -/
theorem annihilatorIdealSheaf_ideal (ℱ : X.Modules) (U : X.affineOpens) :
    (annihilatorIdealSheaf ℱ).ideal U =
      SheafOfModules.RingedSite.idealSectionIdeal
        (annihilatorIdealSubobject ℱ) (op (U : X.Opens)) := sorry

variable [IsLocallyNoetherian X]

/-- Lemma 31.4.7 (1): for a coherent `𝒪_X`-module `ℱ` without embedded associated points, the
annihilator ideal sheaf `Ker(𝒪_X → 𝓗om(ℱ, ℱ))` is coherent. -/
@[stacks 02OM]
theorem annihilatorIdealSubobject_isCoherent
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hℱ : stalkEmbeddedAssociatedPoints ℱ = (∅ : Set X)) :
    (SheafOfModules.annihilator ℱ).IsCoherent := sorry

/-- Lemma 31.4.7 (2): the closed subscheme defined by
`Ker(𝒪_X → 𝓗om(ℱ, ℱ))` has no embedded points. -/
@[stacks 02OM]
theorem annihilatorSubscheme_embeddedPoints_eq_empty
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hℱ : stalkEmbeddedAssociatedPoints ℱ = (∅ : Set X)) :
    stalkEmbeddedPoints (annihilatorIdealSheaf ℱ).subscheme =
      (∅ : Set (annihilatorIdealSheaf ℱ).subscheme) := sorry

/-- Lemma 31.4.7 (3): if `ℱ` is coherent and has no embedded associated points, then on the
closed subscheme cut out by `Ker(𝒪_X → 𝓗om(ℱ, ℱ))` there is a coherent sheaf `𝒢` whose
pushforward is `ℱ`, which has no embedded associated points, and whose support is the whole
closed subscheme. -/
@[stacks 02OM]
theorem exists_coherent_module_on_annihilatorSubscheme
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hℱ : stalkEmbeddedAssociatedPoints ℱ = (∅ : Set X)) :
    ∃ 𝒢 : (annihilatorIdealSheaf ℱ).subscheme.Modules,
      ∃ hcoh : 𝒢.IsCoherent,
        ∃ e : (Scheme.Modules.pushforward (annihilatorIdealSheaf ℱ).subschemeι).obj 𝒢 ≅ ℱ,
          ∃ hEmbedded : stalkEmbeddedAssociatedPoints 𝒢 =
              (∅ : Set (annihilatorIdealSheaf ℱ).subscheme),
            stalkModuleSupport 𝒢 =
              (Set.univ : Set (annihilatorIdealSheaf ℱ).subscheme) := sorry

end AlgebraicGeometry.Scheme.Modules
