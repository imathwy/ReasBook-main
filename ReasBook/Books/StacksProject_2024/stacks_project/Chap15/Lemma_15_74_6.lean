import Mathlib
import StacksProject_2024.Chap15.«15_74_0_2»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

open scoped DerivedTensorProduct
open scoped DerivedInternalHom

/-- Helper for Lemma 15.74.6: the map on a chosen derived internal Hom induced contravariantly
by a morphism in the source and covariantly by a morphism in the target. -/
noncomputable def derivedInternalHomMap
    (H : RHomPkg)
    {K₁ K₂ L₁ L₂ : DMod}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    RHom[H](K₁, L₁) ⟶ RHom[H](K₂, L₂) :=
  letI := H
  (MonoidalClosed.pre fK).app L₁ ≫ (ihom K₂).map fL

/-- Helper for Lemma 15.74.6: the natural transformation on derived tensor functors induced by a
map of right tensor factors, defined as the mate of `MonoidalClosed.pre`. -/
noncomputable def derivedTensorProductMap
    (H : RHomPkg)
    {L₁ L₂ : DMod} (f : L₁ ⟶ L₂) :
    derivedTensorProduct L₁ ⟶ derivedTensorProduct L₂ :=
  letI := H
  (conjugateEquiv (H.derivedTensorAdj L₂) (H.derivedTensorAdj L₁)).symm
    (MonoidalClosed.pre f)

/- Domain-style sampling for Lemma 15.74.6:
- primary domain: adjunction units and mate naturality for the chosen derived internal Hom on
  `D(R)`;
- sampled owner declarations:
  `CategoryTheory.MonoidalClosed.derivedTensorAdj`,
  `CategoryTheory.Adjunction.unit`,
  `CategoryTheory.NatTrans.naturality`,
  `CategoryTheory.unit_conjugateEquiv_symm`;
- best owner abstraction:
  `source-facing`: the canonical morphism
  `K ⟶ R\mathrm{Hom}_R(L, K \otimes_R^{\mathbf L} L)`;
  `core/canonical`: the adjunction
  `H.derivedTensorAdj L`;
  `bridge/view`: rewriting the generic unit and mate naturality identities through
  `derivedInternalHomMap` and `derivedTensorProductMap`;
- primitive data: only the canonical owner `H : MonoidalClosed DMod`;
- derived API: the specialized naturality formulas below.

This file is therefore a recall/view layer. The canonical map itself is exactly the adjunction unit
of `H.derivedTensorAdj L`, so the file should reuse that owner directly rather than keeping a parallel
local wrapper.

Source/core/bridge triage:
- `source-facing`: the canonical unit morphism and its functoriality in `K` and `L`;
- `core/canonical`: `H.derivedTensorAdj L`;
- `bridge/view`: the specialization of `NatTrans.naturality` and `unit_conjugateEquiv_symm` to the
  derived tensor/internal-Hom notation. -/

/-- Lemma 15.74.6: for derived `R`-complexes `K` and `L`, the canonical morphism
`K ⟶ R\mathrm{Hom}_R(L, K \otimes_R^{\mathbf L} L)` in `D(R)` is the unit of the adjunction
`- \otimes_R^{\mathbf L} L ⊣ R\mathrm{Hom}_R(L,-)`. -/
noncomputable def derivedInternalHom_unit
    (H : RHomPkg)
    (K L : DMod) :
    K ⟶ RHom[H](L, K ⊗[R]^L L) :=
  (H.derivedTensorAdj L).unit.app K

/-- Helper for Lemma 15.74.6: the source-facing canonical morphism is definitionally the
adjunction unit of `H.derivedTensorAdj L`. -/
theorem derivedInternalHom_unit_eq_adjunction_unit
    (H : RHomPkg)
    (K L : DMod) :
    derivedInternalHom_unit H K L = (H.derivedTensorAdj L).unit.app K := by
  -- The wrapper is defined directly from the adjunction unit.
  rfl

/-- Helper for Lemma 15.74.6: the canonical unit morphism is functorial in the left variable
`K`. -/
theorem derivedInternalHom_unit_natural_left
    (H : RHomPkg)
    {K₁ K₂ L : DMod} (fK : K₁ ⟶ K₂) :
    CommSq
      fK
      (derivedInternalHom_unit H K₁ L)
      (derivedInternalHom_unit H K₂ L)
      (derivedInternalHomMap H (𝟙 L) ((derivedTensorProduct L).map fK)) := by
  -- This is exactly the naturality square of the unit for the fixed adjunction
  -- `H.derivedTensorAdj L`, rewritten into the source-facing `derivedInternalHomMap` notation.
  refine ⟨?_⟩
  rw [derivedInternalHom_unit_eq_adjunction_unit, derivedInternalHom_unit_eq_adjunction_unit]
  rw [derivedInternalHomMap]
  simpa using (H.derivedTensorAdj L).unit.naturality fK

/-- Helper for Lemma 15.74.6: the canonical unit morphism is functorial in the right variable
`L`. -/
theorem derivedInternalHom_unit_natural_right
    (H : RHomPkg)
    (K : DMod) {L₁ L₂ : DMod} (fL : L₁ ⟶ L₂) :
    CommSq
      (derivedInternalHom_unit H K L₂)
      (derivedInternalHom_unit H K L₁)
      (derivedInternalHomMap H fL (𝟙 (K ⊗[R]^L L₂)))
      (derivedInternalHomMap H (𝟙 L₁) ((derivedTensorProductMap H fL).app K)) := by
  -- The change in `L` compares the units of two different adjunctions, so we use the
  -- unit-side conjugate naturality identity and rewrite the comparison maps into the
  -- derived tensor/internal-Hom API.
  refine ⟨?_⟩
  rw [derivedInternalHom_unit_eq_adjunction_unit, derivedInternalHom_unit_eq_adjunction_unit]
  convert unit_conjugateEquiv_symm
      (H.derivedTensorAdj L₂)
      (H.derivedTensorAdj L₁)
      (MonoidalClosed.pre fL)
      K using 1 <;>
    simp [derivedInternalHomMap, derivedTensorProductMap]

end

end CategoryTheory
