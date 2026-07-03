import Mathlib
import StacksProject_2024.Chap15.«15_74_0_1»

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

/- Lemma 15.74.6: for derived `R`-complexes `K` and `L`, the canonical morphism
`K ⟶ R\mathrm{Hom}_R(L, K \otimes_R^{\mathbf L} L)` is exactly the adjunction unit of
`derivedTensorProduct L ⊣ ihom L`. -/
set_option linter.hashCommand false in
#check fun (H : RHomPkg) (K L : DMod) ↦
  ((H.derivedTensorAdj L).unit.app K :
    K ⟶ RHom[H](L, K ⊗[R]^L L))

/- Naturality in the left variable `K` is the canonical unit naturality square, with top edge
`fK`, vertical edges the two unit components, and bottom edge the induced `derivedInternalHomMap`.
-/
set_option linter.hashCommand false in
#check fun (H : RHomPkg) {K₁ K₂ L : DMod} (fK : K₁ ⟶ K₂) ↦
  let η₁ : K₁ ⟶ RHom[H](L, K₁ ⊗[R]^L L) := (H.derivedTensorAdj L).unit.app K₁
  let η₂ : K₂ ⟶ RHom[H](L, K₂ ⊗[R]^L L) := (H.derivedTensorAdj L).unit.app K₂
  let β :
      RHom[H](L, K₁ ⊗[R]^L L) ⟶ RHom[H](L, K₂ ⊗[R]^L L) :=
    derivedInternalHomMap H (𝟙 L) ((derivedTensorProduct L).map fK)
  show CommSq fK η₁ η₂ β from by
    refine ⟨?_⟩
    dsimp [η₁, η₂, β]
    rw [derivedInternalHomMap]
    simpa using (H.derivedTensorAdj L).unit.naturality fK

/- Naturality in the right variable `L` is the unit-side mate naturality square for the conjugate
map `derivedTensorProductMap H fL`, specialized via `unit_conjugateEquiv_symm`. -/
set_option linter.hashCommand false in
#check
  fun (H : RHomPkg) (K : DMod) {L₁ L₂ : DMod} (fL : L₁ ⟶ L₂) ↦
    let η₁ : K ⟶ RHom[H](L₁, K ⊗[R]^L L₁) := (H.derivedTensorAdj L₁).unit.app K
    let η₂ : K ⟶ RHom[H](L₂, K ⊗[R]^L L₂) := (H.derivedTensorAdj L₂).unit.app K
    let α :
        RHom[H](L₂, K ⊗[R]^L L₂) ⟶ RHom[H](L₁, K ⊗[R]^L L₂) :=
      derivedInternalHomMap H fL (𝟙 (K ⊗[R]^L L₂))
    let β :
        RHom[H](L₁, K ⊗[R]^L L₁) ⟶ RHom[H](L₁, K ⊗[R]^L L₂) :=
      derivedInternalHomMap H (𝟙 L₁) ((derivedTensorProductMap H fL).app K)
    show CommSq η₂ η₁ α β from by
      refine ⟨?_⟩
      dsimp [η₁, η₂, α, β]
      convert unit_conjugateEquiv_symm
          (H.derivedTensorAdj L₂)
          (H.derivedTensorAdj L₁)
          (MonoidalClosed.pre fL)
          K using 1 <;>
        simp [derivedInternalHomMap, derivedTensorProductMap]

end

end CategoryTheory
