import Mathlib
import StacksProject_2024.Chap13.Definition_13_13_7
import StacksProject_2024.Chap13.Lemma_13_11_6
import StacksProject_2024.Chap13.Lemma_13_13_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/- Domain-style sampling for Lemma `13.13.9`.
- primary domain: bounded filtered homotopy categories, filtered acyclic complexes, filtered
  quasi-isomorphisms, and their localization in the filtered derived category;
- sampled owner declarations:
  `DF⁺(𝒜)`, `DF⁻(𝒜)`, `DFᵇ(𝒜)`,
  `FQis(𝒜)`,
  `FAc(𝒜)`,
  `MorphismProperty.Q`,
  `boundedBelowHomotopyProperty`,
  `boundedAboveHomotopyProperty`,
  `boundedHomotopyProperty`;
- best owner abstraction: the source-facing derived owners are already the chapter notations
  `DF⁺(𝒜)`, `DF⁻(𝒜)`, and `DFᵇ(𝒜)` from Definition `13.13.7`; this lemma should therefore live
  at the bridge/view layer, expressing the bounded filtered localizations of
  `K⁺(Fil^f(𝒜))`, `K⁻(Fil^f(𝒜))`, and `Kᵇ(Fil^f(𝒜))` into those existing owners rather than
  introducing a second bounded filtered derived-category owner;
- primitive data: the chapter owners `FQis(𝒜)`, `FAc(𝒜)`,
  `((FAc(𝒜) : ObjectProperty KFilt).trW).Q`,
  together with the bounded homotopy object properties on `K(Fil^f(𝒜))`;
- derived API: the bounded filtered quasi-isomorphism owners `FQis⁺/⁻/ᵇ`, the notation-only
  bounded filtered acyclic views `FAc⁺/⁻/ᵇ`, and the canonical bounded bridge functors
  `K⁺(Fil^f(𝒜)) ⥤ DF⁺(𝒜)`, `K⁻(Fil^f(𝒜)) ⥤ DF⁻(𝒜)`, `Kᵇ(Fil^f(𝒜)) ⥤ DFᵇ(𝒜)`.

Source/core/bridge triage:
- `source-facing`: the bounded filtered localization statements of Lemma `13.13.9`;
- `core/canonical`: `DF⁺(𝒜)`, `DF⁻(𝒜)`, `DFᵇ(𝒜)`, `FQis(𝒜)`, `FAc(𝒜)`,
  `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))`, and the bounded homotopy owners on
  `K(Fil^f(𝒜))`;
- `bridge/view`: the bounded filtered quasi-isomorphism owners, the notation-only restricted
  acyclic views, and the induced functors from bounded filtered homotopy categories into the
  existing bounded filtered derived categories. -/

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]
variable [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
variable [Pretriangulated (HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "KFilt" => HomotopyCategory FilF (up ℤ)

local instance finiteFiltered_hasFiniteBiproducts_13_13_9 : HasFiniteBiproducts FilF :=
  Limits.HasFiniteBiproducts.of_hasFiniteProducts

local instance pretriangulated_filtered_homotopy_13_13_9 : Pretriangulated KFilt := by
  exact finiteFilteredHomotopyPretriangulated

local instance isTriangulated_filtered_homotopy_13_13_9 : IsTriangulated KFilt := by
  exact finiteFilteredHomotopyIsTriangulated

private abbrev QFilt : KFilt ⥤ DF(𝒜) :=
  (((FAc(𝒜) : ObjectProperty KFilt).trW).Q : KFilt ⥤ DF(𝒜))

local instance qFilt_commShift :
    ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)).CommShift ℤ := by
  infer_instance

local instance qFilt_isTriangulated :
    ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)).IsTriangulated := by
  infer_instance

local instance :
    ((((HomotopyCategory.plus FilF).ι : K⁺(FilF) ⥤ KFilt) ⋙
      ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)))).CommShift ℤ := by
  infer_instance

local instance :
    ((((HomotopyCategory.plus FilF).ι : K⁺(FilF) ⥤ KFilt) ⋙
      ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)))).IsTriangulated := by
  infer_instance

local instance :
    ((((HomotopyCategory.minus FilF).ι : K⁻(FilF) ⥤ KFilt) ⋙
      ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)))).CommShift ℤ := by
  infer_instance

local instance :
    ((((HomotopyCategory.minus FilF).ι : K⁻(FilF) ⥤ KFilt) ⋙
      ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)))).IsTriangulated := by
  infer_instance

local instance :
    ((((HomotopyCategory.bounded FilF).ι : Kᵇ(FilF) ⥤ KFilt) ⋙
      ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)))).CommShift ℤ := by
  infer_instance

local instance :
    ((((HomotopyCategory.bounded FilF).ι : Kᵇ(FilF) ⥤ KFilt) ⋙
      ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)))).IsTriangulated := by
  infer_instance

/- The filtered quasi-isomorphisms in `K^+(\mathrm{Fil}^f(\mathcal A))` are the morphisms whose
images in `K(\mathrm{Fil}^f(\mathcal A))` are filtered quasi-isomorphisms. -/
variable (𝒜) in
abbrev boundedBelowFilteredQuasiIso :
    MorphismProperty (K⁺(FilF)) :=
  (FQis(𝒜) : MorphismProperty KFilt).inverseImage
    (HomotopyCategory.plus FilF).ι

/- The filtered quasi-isomorphisms in `K^-(\mathrm{Fil}^f(\mathcal A))` are the morphisms whose
images in `K(\mathrm{Fil}^f(\mathcal A))` are filtered quasi-isomorphisms. -/
variable (𝒜) in
abbrev boundedAboveFilteredQuasiIso :
    MorphismProperty (K⁻(FilF)) :=
  (FQis(𝒜) : MorphismProperty KFilt).inverseImage
    (HomotopyCategory.minus FilF).ι

/- The filtered quasi-isomorphisms in `K^b(\mathrm{Fil}^f(\mathcal A))` are the morphisms whose
images in `K(\mathrm{Fil}^f(\mathcal A))` are filtered quasi-isomorphisms. -/
variable (𝒜) in
abbrev boundedFilteredQuasiIso :
    MorphismProperty (Kᵇ(FilF)) :=
  (FQis(𝒜) : MorphismProperty KFilt).inverseImage
    (HomotopyCategory.bounded FilF).ι

scoped notation "FQis⁺(" A:arg ")" => boundedBelowFilteredQuasiIso A
scoped notation "FQis⁻(" A:arg ")" => boundedAboveFilteredQuasiIso A
scoped notation "FQisᵇ(" A:arg ")" => boundedFilteredQuasiIso A
scoped notation "FAc⁺(" A:arg ")" =>
  ObjectProperty.inverseImage
    (FAc(A))
    (ObjectProperty.ι (HomotopyCategory.plus (finiteFilteredObjectCat A)))
scoped notation "FAc⁻(" A:arg ")" =>
  ObjectProperty.inverseImage
    (FAc(A))
    (ObjectProperty.ι (HomotopyCategory.minus (finiteFilteredObjectCat A)))
scoped notation "FAcᵇ(" A:arg ")" =>
  ObjectProperty.inverseImage
    (FAc(A))
    (ObjectProperty.ι (HomotopyCategory.bounded (finiteFilteredObjectCat A)))

-- Proof sketch: the associated graded functor on filtered homotopy categories preserves
-- bounded-below complexes, and Lemma `13.11.6 (1)` shows that the derived image of a bounded-
-- below graded complex lies in `D⁺(Gr(\mathcal A))`.
variable (𝒜) in
/-- The canonical functor `K(Fil^f(\mathcal A)) ⟶ DF(\mathcal A)` sends bounded-below filtered
homotopy objects to `DF⁺(\mathcal A)`. -/
theorem filteredDerivedQuotientFunctor_obj_mem_boundedBelowFilteredDerivedCategory
    (X : K⁺(FilF)) :
    filteredDerivedPlusProperty 𝒜
      (QFilt.obj X.obj) := by
  sorry

-- Proof sketch: the same argument with bounded-above associated graded complexes lands in
-- `D⁻(Gr(\mathcal A))`.
variable (𝒜) in
/-- The canonical functor `K(Fil^f(\mathcal A)) ⟶ DF(\mathcal A)` sends bounded-above filtered
homotopy objects to `DF⁻(\mathcal A)`. -/
theorem filteredDerivedQuotientFunctor_obj_mem_boundedAboveFilteredDerivedCategory
    (X : K⁻(FilF)) :
    filteredDerivedMinusProperty 𝒜
      (QFilt.obj X.obj) := by
  sorry

-- Proof sketch: a bounded filtered homotopy object has bounded associated graded complex, so its
-- image in `DF(\mathcal A)` lies in `DFᵇ(\mathcal A)`.
variable (𝒜) in
/-- The canonical functor `K(Fil^f(\mathcal A)) ⟶ DF(\mathcal A)` sends bounded filtered homotopy
objects to `DFᵇ(\mathcal A)`. -/
theorem filteredDerivedQuotientFunctor_obj_mem_boundedFilteredDerivedCategory
    (X : Kᵇ(FilF)) :
    filteredDerivedBoundedProperty 𝒜
      (QFilt.obj X.obj) := by
  sorry

variable (𝒜) in
/-- The canonical functor `K^+(\mathrm{Fil}^f(\mathcal A)) ⟶ DF^+(\mathcal A)`. -/
abbrev mapBoundedBelowFilteredHomotopyToDerivedBelow :
    K⁺(FilF) ⥤ DF⁺(𝒜) :=
  (filteredDerivedPlusProperty 𝒜).lift
    ((HomotopyCategory.plus FilF).ι ⋙ QFilt)
    (fun X ↦ by
      simpa using filteredDerivedQuotientFunctor_obj_mem_boundedBelowFilteredDerivedCategory 𝒜 X)

variable (𝒜) in
/-- The canonical functor `K^-(\mathrm{Fil}^f(\mathcal A)) ⟶ DF^-(\mathcal A)`. -/
abbrev mapBoundedAboveFilteredHomotopyToDerivedAbove :
    K⁻(FilF) ⥤ DF⁻(𝒜) :=
  (filteredDerivedMinusProperty 𝒜).lift
    ((HomotopyCategory.minus FilF).ι ⋙ QFilt)
    (fun X ↦ by
      simpa using filteredDerivedQuotientFunctor_obj_mem_boundedAboveFilteredDerivedCategory 𝒜 X)

variable (𝒜) in
/-- The canonical functor `K^b(\mathrm{Fil}^f(\mathcal A)) ⟶ DF^b(\mathcal A)`. -/
abbrev mapBoundedFilteredHomotopyToDerivedBounded :
    Kᵇ(FilF) ⥤ DFᵇ(𝒜) :=
  (filteredDerivedBoundedProperty 𝒜).lift
    ((HomotopyCategory.bounded FilF).ι ⋙ QFilt)
    (fun X ↦ by
      simpa using filteredDerivedQuotientFunctor_obj_mem_boundedFilteredDerivedCategory 𝒜 X)

/- Companion recall: the acyclic bounded-below objects define a triangulated full subcategory
`FAc^{+}(\mathcal A) ⊆ K^{+}(Fil^{f}(\mathcal A))`. This is the generic inverse-image
triangulated instance applied to `FAc(𝒜)`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (FAc⁺(𝒜)))

/- Companion recall: the acyclic bounded-below subcategory `FAc^{+}(\mathcal A)` is saturated,
i.e. stable under retracts in `K^{+}(Fil^{f}(\mathcal A))`. This is the generic inverse-image
retract stability instance. -/
#check (show ObjectProperty.IsStableUnderRetracts (FAc⁺(𝒜)) from by
  dsimp [filteredAcyclic]
  infer_instance)

/- Companion recall: the acyclic bounded-above objects define a triangulated full subcategory
`FAc^{-}(\mathcal A) ⊆ K^{-}(Fil^{f}(\mathcal A))`. This is the generic inverse-image
triangulated instance applied to `FAc(𝒜)`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (FAc⁻(𝒜)))

/- Companion recall: the acyclic bounded-above subcategory `FAc^{-}(\mathcal A)` is saturated,
i.e. stable under retracts in `K^{-}(Fil^{f}(\mathcal A))`. This is the generic inverse-image
retract stability instance. -/
#check (show ObjectProperty.IsStableUnderRetracts (FAc⁻(𝒜)) from by
  dsimp [filteredAcyclic]
  infer_instance)

/- Companion recall: the acyclic bounded objects define a triangulated full subcategory
`FAc^{b}(\mathcal A) ⊆ K^{b}(Fil^{f}(\mathcal A))`. This is the generic inverse-image
triangulated instance applied to `FAc(𝒜)`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (FAcᵇ(𝒜)))

/- Companion recall: the acyclic bounded subcategory `FAc^{b}(\mathcal A)` is saturated, i.e.
stable under retracts in `K^{b}(Fil^{f}(\mathcal A))`. This is the generic inverse-image
retract stability instance. -/
#check (show ObjectProperty.IsStableUnderRetracts (FAcᵇ(𝒜)) from by
  dsimp [filteredAcyclic]
  infer_instance)

-- Proof sketch: restrict Lemma `13.13.4` from `K(Fil^f(\mathcal A))` to the bounded-below full
-- subcategory, exactly as in Lemma `13.11.6 (1)`.
/-- Lemma 13.13.9 (1): the saturated multiplicative system corresponding to
`FAc^{+}(\mathcal A)` is precisely `FQis^{+}(\mathcal A)`. -/
theorem boundedBelowFilteredAcyclicProperty_trW_eq_quasiIso :
    (FAc⁺(𝒜)).trW =
      FQis⁺(𝒜) := by
  sorry

-- Proof sketch: an object of `K^{+}(Fil^{f}(\mathcal A))` maps to zero in `DF^{+}(\mathcal A)`
-- exactly when its image in `DF(\mathcal A)` is filtered acyclic.
/-- Lemma 13.13.9 (2): the kernel of
`K^{+}(Fil^{f}(\mathcal A)) ⟶ DF^{+}(\mathcal A)` is `FAc^{+}(\mathcal A)`. -/
theorem kernel_mapBoundedBelowFilteredHomotopyToDerivedBelow_eq_acyclic :
    Functor.kernel (mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜) =
      FAc⁺(𝒜) := by
  sorry

-- Proof sketch: use Lemma `13.13.8 (1)` to obtain bounded-below filtered representatives and
-- then repeat the localization argument of Lemma `13.11.6 (3)`.
/-- Lemma 13.13.9 (3): the canonical functor
`K^{+}(Fil^{f}(\mathcal A)) ⟶ DF^{+}(\mathcal A)` realizes `DF^{+}(\mathcal A)` as the
localization of `K^{+}(Fil^{f}(\mathcal A))` at `FQis^{+}(\mathcal A)`. -/
theorem mapBoundedBelowFilteredHomotopyToDerivedBelow_isLocalization :
    Functor.IsLocalization
      (mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜)
      (FQis⁺(𝒜)) := by
  sorry

-- Proof sketch: restrict Lemma `13.13.4` to the bounded-above full subcategory, as in
-- Lemma `13.11.6 (4)`.
/-- Lemma 13.13.9 (4): the saturated multiplicative system corresponding to
`FAc^{-}(\mathcal A)` is precisely `FQis^{-}(\mathcal A)`. -/
theorem boundedAboveFilteredAcyclicProperty_trW_eq_quasiIso :
    (FAc⁻(𝒜)).trW =
      FQis⁻(𝒜) := by
  sorry

-- Proof sketch: bounded-above filtered objects die in `DF^{-}(\mathcal A)` exactly when their
-- ambient filtered derived objects are filtered acyclic.
/-- Lemma 13.13.9 (5): the kernel of
`K^{-}(Fil^{f}(\mathcal A)) ⟶ DF^{-}(\mathcal A)` is `FAc^{-}(\mathcal A)`. -/
theorem kernel_mapBoundedAboveFilteredHomotopyToDerivedAbove_eq_acyclic :
    Functor.kernel (mapBoundedAboveFilteredHomotopyToDerivedAbove 𝒜) =
      FAc⁻(𝒜) := by
  sorry

-- Proof sketch: use Lemma `13.13.8 (2)` to obtain bounded-above filtered representatives and
-- then repeat the localization argument of Lemma `13.11.6 (6)`.
/-- Lemma 13.13.9 (6): the canonical functor
`K^{-}(Fil^{f}(\mathcal A)) ⟶ DF^{-}(\mathcal A)` realizes `DF^{-}(\mathcal A)` as the
localization of `K^{-}(Fil^{f}(\mathcal A))` at `FQis^{-}(\mathcal A)`. -/
theorem mapBoundedAboveFilteredHomotopyToDerivedAbove_isLocalization :
    Functor.IsLocalization
      (mapBoundedAboveFilteredHomotopyToDerivedAbove 𝒜)
      (FQis⁻(𝒜)) := by
  sorry

-- Proof sketch: restrict Lemma `13.13.4` to the bounded full subcategory, as in
-- Lemma `13.11.6 (7)`.
/-- Lemma 13.13.9 (7): the saturated multiplicative system corresponding to
`FAc^{b}(\mathcal A)` is precisely `FQis^{b}(\mathcal A)`. -/
theorem boundedFilteredAcyclicProperty_trW_eq_quasiIso :
    (FAcᵇ(𝒜)).trW =
      FQisᵇ(𝒜) := by
  sorry

-- Proof sketch: a bounded filtered homotopy object becomes zero in `DF^{b}(\mathcal A)` exactly
-- when it is filtered acyclic.
/-- Lemma 13.13.9 (8): the kernel of
`K^{b}(Fil^{f}(\mathcal A)) ⟶ DF^{b}(\mathcal A)` is `FAc^{b}(\mathcal A)`. -/
theorem kernel_mapBoundedFilteredHomotopyToDerivedBounded_eq_acyclic :
    Functor.kernel (mapBoundedFilteredHomotopyToDerivedBounded 𝒜) =
      FAcᵇ(𝒜) := by
  sorry

-- Proof sketch: use Lemma `13.13.8 (3)` to choose bounded filtered representatives and then
-- repeat the bounded localization argument of Lemma `13.11.6 (9)`.
/-- Lemma 13.13.9 (9): the canonical functor
`K^{b}(Fil^{f}(\mathcal A)) ⟶ DF^{b}(\mathcal A)` realizes `DF^{b}(\mathcal A)` as the
localization of `K^{b}(Fil^{f}(\mathcal A))` at `FQis^{b}(\mathcal A)`. -/
theorem mapBoundedFilteredHomotopyToDerivedBounded_isLocalization :
    Functor.IsLocalization
      (mapBoundedFilteredHomotopyToDerivedBounded 𝒜)
      (FQisᵇ(𝒜)) := by
  sorry

end CategoryTheory
