import Mathlib
import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap13.Lemma_13_6_2
import StacksProject_2024.Chap13.Lemma_13_6_11
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_10_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

/- Domain-style sampling for Lemma 13.11.6:
- primary domain: derived-category localization of bounded homotopy categories by
  quasi-isomorphisms;
- sampled owner declarations:
  `HomotopyCategory.quasiIso`,
  `HomotopyCategory.subcategoryAcyclic`,
  `ObjectProperty.inverseImage`,
  `ObjectProperty.lift`,
  `DerivedCategory.Qh`,
  `Functor.kernel`;
- best owner abstraction: the ambient owners are the unbounded quasi-isomorphism morphism
  property `HomotopyCategory.quasiIso 𝒜 (up ℤ)` and the acyclic triangulated subcategory
  `HomotopyCategory.subcategoryAcyclic 𝒜`; on the bounded categories, the source-facing objects
  are their inverse-image/restricted views along the inclusion `ObjectProperty.ι`.
- primitive vs. derived API: the primitive data are the bounded homotopy object properties from
  `Definition_13_8_1`, the canonical quotient functor `DerivedCategory.Qh`, and the ambient
  quasi-isomorphism / acyclic owners. The bounded localization functors and their kernel /
  localization statements are the derived bridge/view layer.
- source/core/bridge triage:
  `source-facing`: `Qis⁺(𝒜)`, `Qis⁻(𝒜)`, `Qisᵇ(𝒜)`, the bounded derived functors, and the nine
    localization statements of Lemma 13.11.6;
  `core/canonical`: `HomotopyCategory.quasiIso 𝒜 (up ℤ)`,
    `HomotopyCategory.subcategoryAcyclic 𝒜`, `DerivedCategory.Qh`, and `Functor.kernel`;
  `bridge/view`: inverse images to `K⁺(𝒜)`, `K⁻(𝒜)`, `Kᵇ(𝒜)` and the induced functors
    `K^*(𝒜) ⥤ D^*(𝒜)`.

The bounded quasi-isomorphism morphism properties are high-frequency bridge owners used downstream,
so they remain named here. The bounded acyclic object properties are only the direct inverse-image
views of `HomotopyCategory.subcategoryAcyclic 𝒜`, so this file uses source-facing notation for
them rather than introducing a second public owner layer. -/

/- Reuse the Chapter 13 boundedness owners on cochain complexes and their homotopy categories from
`Definition_13_8_1` and the bounded derived-category owners from `Definition_13_11_3`; this file
adds localization results on top of that canonical API rather than redeclaring parallel
bounded-derived notions. -/

/-- The quasi-isomorphisms in `K^+(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedBelowHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (K⁺(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (ObjectProperty.ι (boundedBelowHomotopyProperty 𝒜))

/-- The quasi-isomorphisms in `K^-(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedAboveHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (K⁻(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (ObjectProperty.ι (boundedAboveHomotopyProperty 𝒜))

/-- The quasi-isomorphisms in `K^b(\mathcal A)` are the morphisms whose images in
`K(\mathcal A)` are quasi-isomorphisms. -/
abbrev boundedHomotopyQuasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    MorphismProperty (Kᵇ(𝒜)) :=
  (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
    (ObjectProperty.ι (boundedHomotopyProperty 𝒜))

scoped notation "Qis⁺(" A:arg ")" => boundedBelowHomotopyQuasiIso A
scoped notation "Qis⁻(" A:arg ")" => boundedAboveHomotopyQuasiIso A
scoped notation "Qisᵇ(" A:arg ")" => boundedHomotopyQuasiIso A

scoped notation "Ac⁺(" A:arg ")" =>
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (boundedBelowHomotopyProperty A))
scoped notation "Ac⁻(" A:arg ")" =>
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (boundedAboveHomotopyProperty A))
scoped notation "Acᵇ(" A:arg ")" =>
  ObjectProperty.inverseImage
    (HomotopyCategory.subcategoryAcyclic A)
    (ObjectProperty.ι (boundedHomotopyProperty A))

/-- The canonical functor `K(\mathcal A) ⟶ D(\mathcal A)` sends bounded-below homotopy objects
to bounded-below derived objects. -/
theorem qh_obj_mem_t_plus
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    (X : K⁺(𝒜)) :
    (t.plus : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := sorry

/-- The canonical functor `K(\mathcal A) ⟶ D(\mathcal A)` sends bounded-above homotopy objects
to bounded-above derived objects. -/
theorem qh_obj_mem_t_minus
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    (X : K⁻(𝒜)) :
    (t.minus : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := sorry

-- Proof sketch: a bounded complex has cohomology vanishing outside a finite interval, and the
-- identity functor sends bounded complexes to the same derived objects, so both the bounded-below
-- and bounded-above vanishing conditions hold in the image.
/-- The canonical functor `K(\mathcal A) ⟶ D(\mathcal A)` sends bounded homotopy objects to
bounded derived objects. -/
theorem qh_obj_mem_t_bounded
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
    (X : Kᵇ(𝒜)) :
    (t.bounded : ObjectProperty (D(𝒜)))
      (DerivedCategory.Qh.obj X.obj) := sorry

/-- The canonical functor `K^+(\mathcal A) ⟶ D^+(\mathcal A)`. -/
abbrev mapBoundedBelowHomotopyToDerivedBelow
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    K⁺(𝒜) ⥤ D⁺(𝒜) :=
  ObjectProperty.lift
    (t.plus : ObjectProperty (D(𝒜)))
    (ObjectProperty.ι (boundedBelowHomotopyProperty 𝒜) ⋙ DerivedCategory.Qh)
    (qh_obj_mem_t_plus 𝒜)

/-- The canonical functor `K^-(\mathcal A) ⟶ D^-(\mathcal A)`. -/
abbrev mapBoundedAboveHomotopyToDerivedAbove
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    K⁻(𝒜) ⥤ D⁻(𝒜) :=
  ObjectProperty.lift
    (t.minus : ObjectProperty (D(𝒜)))
    (ObjectProperty.ι (boundedAboveHomotopyProperty 𝒜) ⋙ DerivedCategory.Qh)
    (qh_obj_mem_t_minus 𝒜)

/-- The canonical functor `K^b(\mathcal A) ⟶ D^b(\mathcal A)`. -/
abbrev mapBoundedHomotopyToDerivedBounded
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Kᵇ(𝒜) ⥤ Dᵇ(𝒜) :=
  ObjectProperty.lift
    (t.bounded : ObjectProperty (D(𝒜)))
    (ObjectProperty.ι (boundedHomotopyProperty 𝒜) ⋙ DerivedCategory.Qh)
    (qh_obj_mem_t_bounded 𝒜)

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Companion recall: the acyclic bounded-below objects define a triangulated full subcategory
`Ac^{+}(\mathcal A) ⊆ K^{+}(\mathcal A)`. This is the generic inverse-image triangulated
instance applied to `HomotopyCategory.subcategoryAcyclic 𝒜`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (Ac⁺(𝒜)))

/- Companion recall: the acyclic bounded-below subcategory `Ac^{+}(\mathcal A)` is saturated,
i.e. stable under retracts in `K^{+}(\mathcal A)`. This is the generic inverse-image retract
stability instance. -/
#check (show ObjectProperty.IsStableUnderRetracts (Ac⁺(𝒜)) from by
  dsimp [HomotopyCategory.subcategoryAcyclic]
  infer_instance)

-- Proof sketch: identify quasi-isomorphisms in the ambient homotopy category with the Verdier
-- morphism property of the acyclic subcategory, then restrict along the inclusion
-- `K^{+}(\mathcal A) ⥤ K(\mathcal A)`.
/-- Lemma 13.11.6 (1): the saturated multiplicative system corresponding to
`Ac^{+}(\mathcal A)` is precisely `Qis^{+}(\mathcal A)`. -/
theorem boundedBelowAcyclicHomotopyProperty_trW_eq_quasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    (Ac⁺(𝒜)).trW =
      Qis⁺(𝒜) := sorry

-- Proof sketch: an object of `K^{+}(\mathcal A)` maps to zero in `D^{+}(\mathcal A)` exactly
-- when its image in the unbounded derived category is acyclic, which is the defining condition of
-- `Ac^{+}(\mathcal A)`.
/-- Lemma 13.11.6 (2): the kernel of `K^{+}(\mathcal A) ⟶ D^{+}(\mathcal A)` is
`Ac^{+}(\mathcal A)`. -/
theorem kernel_mapBoundedBelowHomotopyToDerivedBelow_eq_acyclic
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Functor.kernel (mapBoundedBelowHomotopyToDerivedBelow 𝒜) =
      Ac⁺(𝒜) := sorry

-- Proof sketch: Lemma 13.11.5 makes the bounded-below quasi-isomorphisms cofinal in the ambient
-- derived-category localization, so the canonical functor `K^{+}(\mathcal A) ⟶ D^{+}(\mathcal A)`
-- satisfies the universal property of localization at `Qis^{+}(\mathcal A)`.
/-- Lemma 13.11.6 (3): the canonical functor `K^{+}(\mathcal A) ⟶ D^{+}(\mathcal A)` realizes
`D^{+}(\mathcal A)` as the localization of `K^{+}(\mathcal A)` at `Qis^{+}(\mathcal A)`. -/
theorem mapBoundedBelowHomotopyToDerivedBelow_isLocalization
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Functor.IsLocalization
      (mapBoundedBelowHomotopyToDerivedBelow 𝒜)
      (Qis⁺(𝒜)) := sorry

/- Companion recall: the acyclic bounded-above objects define a triangulated full subcategory
`Ac^{-}(\mathcal A) ⊆ K^{-}(\mathcal A)`. This is the generic inverse-image triangulated
instance applied to `HomotopyCategory.subcategoryAcyclic 𝒜`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (Ac⁻(𝒜)))

/- Companion recall: the acyclic bounded-above subcategory `Ac^{-}(\mathcal A)` is saturated,
i.e. stable under retracts in `K^{-}(\mathcal A)`. This is the generic inverse-image retract
stability instance. -/
#check (show ObjectProperty.IsStableUnderRetracts (Ac⁻(𝒜)) from by
  dsimp [HomotopyCategory.subcategoryAcyclic]
  infer_instance)

-- Proof sketch: use the unbounded identification between quasi-isomorphisms and the Verdier
-- morphism property of acyclic complexes, then restrict it to the bounded-above full subcategory.
/-- Lemma 13.11.6 (4): the saturated multiplicative system corresponding to
`Ac^{-}(\mathcal A)` is precisely `Qis^{-}(\mathcal A)`. -/
theorem boundedAboveAcyclicHomotopyProperty_trW_eq_quasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    (Ac⁻(𝒜)).trW =
      Qis⁻(𝒜) := sorry

-- Proof sketch: bounded-above objects die in `D^{-}(\mathcal A)` exactly when their image in the
-- unbounded derived category is acyclic, giving the same kernel criterion as in the bounded-below
-- case.
/-- Lemma 13.11.6 (5): the kernel of `K^{-}(\mathcal A) ⟶ D^{-}(\mathcal A)` is
`Ac^{-}(\mathcal A)`. -/
theorem kernel_mapBoundedAboveHomotopyToDerivedAbove_eq_acyclic
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Functor.kernel (mapBoundedAboveHomotopyToDerivedAbove 𝒜) =
      Ac⁻(𝒜) := sorry

-- Proof sketch: Lemma 13.11.5 yields bounded-above representatives for the denominators in the
-- ambient localization, so the bounded-above functor has the universal property of localization at
-- `Qis^{-}(\mathcal A)`.
/-- Lemma 13.11.6 (6): the canonical functor `K^{-}(\mathcal A) ⟶ D^{-}(\mathcal A)` realizes
`D^{-}(\mathcal A)` as the localization of `K^{-}(\mathcal A)` at `Qis^{-}(\mathcal A)`. -/
theorem mapBoundedAboveHomotopyToDerivedAbove_isLocalization
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Functor.IsLocalization
      (mapBoundedAboveHomotopyToDerivedAbove 𝒜)
      (Qis⁻(𝒜)) := sorry

/- Companion recall: the acyclic bounded objects define a triangulated full subcategory
`Ac^{b}(\mathcal A) ⊆ K^{b}(\mathcal A)`. This is the generic inverse-image triangulated
instance applied to `HomotopyCategory.subcategoryAcyclic 𝒜`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (Acᵇ(𝒜)))

/- Companion recall: the acyclic bounded subcategory `Ac^{b}(\mathcal A)` is saturated, i.e.
stable under retracts in `K^{b}(\mathcal A)`. This is the generic inverse-image retract
stability instance. -/
#check (show ObjectProperty.IsStableUnderRetracts (Acᵇ(𝒜)) from by
  dsimp [HomotopyCategory.subcategoryAcyclic]
  infer_instance)

-- Proof sketch: identify quasi-isomorphisms with the Verdier morphism property of acyclic
-- complexes in the ambient homotopy category and restrict to the bounded full subcategory.
/-- Lemma 13.11.6 (7): the saturated multiplicative system corresponding to
`Ac^{b}(\mathcal A)` is precisely `Qis^{b}(\mathcal A)`. -/
theorem boundedAcyclicHomotopyProperty_trW_eq_quasiIso
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    (Acᵇ(𝒜)).trW =
      Qisᵇ(𝒜) := sorry

-- Proof sketch: a bounded homotopy object becomes zero in `D^{b}(\mathcal A)` exactly when its
-- image in `D(\mathcal A)` is acyclic, so the kernel is the bounded acyclic subcategory.
/-- Lemma 13.11.6 (8): the kernel of `K^{b}(\mathcal A) ⟶ D^{b}(\mathcal A)` is
`Ac^{b}(\mathcal A)`. -/
theorem kernel_mapBoundedHomotopyToDerivedBounded_eq_acyclic
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Functor.kernel (mapBoundedHomotopyToDerivedBounded 𝒜) =
      Acᵇ(𝒜) := sorry

-- Proof sketch: combine the bounded-above localization argument with the fact that bounded
-- denominators can be chosen inside `K^{b}(\mathcal A)`, again using the bounded replacement
-- statement from Lemma 13.11.5.
/-- Lemma 13.11.6 (9): the canonical functor `K^{b}(\mathcal A) ⟶ D^{b}(\mathcal A)` realizes
`D^{b}(\mathcal A)` as the localization of `K^{b}(\mathcal A)` at `Qis^{b}(\mathcal A)`. -/
theorem mapBoundedHomotopyToDerivedBounded_isLocalization
    (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    Functor.IsLocalization
      (mapBoundedHomotopyToDerivedBounded 𝒜)
      (Qisᵇ(𝒜)) := sorry

end

end CategoryTheory
