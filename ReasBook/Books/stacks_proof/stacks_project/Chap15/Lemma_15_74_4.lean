import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import stacks_proof.stacks_project.Chap13.Remark_13_10_9
import stacks_proof.stacks_project.Chap15.Lemma_15_59_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open Opposite
open ComplexShape
open CategoryTheory.MonoidalCategory
open BraidedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "KMod" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "DMod" => DerivedCategory (ModuleCat R)

open scoped DerivedTensorProduct

/- 
Domain-style sampling for derived internal-Hom composition on `D(R)`:
- primary domain: closed symmetric monoidal structure on the derived category `D(R)`;
- sampled owner declarations:
  `CategoryTheory.derivedTensorProduct`,
  `CategoryTheory.MonoidalClosed.internalHom`,
  `CategoryTheory.MonoidalClosed.internalHomAdjunction₂`,
  `CategoryTheory.MonoidalClosed.comp`;
- best owner abstraction:
  `core/canonical`: the monoidal-closed owner `H : MonoidalClosed DMod`, together with
  `ihom`, `MonoidalClosed.pre`, and `MonoidalClosed.comp`;
  `source-facing`: the notation `RHom[H](K, L)` and the source-facing right-tensor adjunction
  `derivedTensorProduct L ⊣ RHom[H](L,-)`;
  `bridge/view`: the transported adjunction `H.derivedTensorAdj`, the tensor map
  `derivedTensorProductMap`, and the composition map `derivedInternalHom_comp`;
- primitive data: only the canonical owner `H : MonoidalClosed DMod`;
- derived API: the `RHom` notation and the bridge morphisms below.

This file therefore keeps the public API centered on `MonoidalClosed DMod` and reuses the
canonical tensor-localization owner from `Lemma_15_59_14`. The notation itself is defined directly
over the canonical internal-Hom owner `(ihom K).obj L`, not through a parallel wrapper
declaration.
-/

-- Route correction: `Lemma_15_59_14` is the canonical owner of the localized tensor structure and
-- the bridge `derivedCategory_tensorObj_iso_derivedTensorProduct`; this file now only adds the
-- internal-Hom comparison API built on top of that owner.

namespace DerivedInternalHom

/- Textbook notation for the derived internal-Hom object `RHom_R(K, L)` in `D(R)`. -/
set_option quotPrecheck false in
scoped notation:70 "RHom[" H:70 "](" K:70 ", " L:70 ")" =>
  (letI := H
   (ihom K).obj L)

end DerivedInternalHom

open scoped DerivedInternalHom

namespace MonoidalClosed

/-- Helper for Lemma 15.74.4: the source-facing adjunction
`- \otimes_R^{\mathbf L} L ⊣ R\mathrm{Hom}_R(L,-)`,
transported from the canonical left-tensor adjunction by the braiding on `D(R)` and the standard
comparison between the owner tensor and `⊗[R]^L`. -/
noncomputable def derivedTensorAdj
    (H : MonoidalClosed DMod)
    (L : DMod) :
    derivedTensorProduct L ⊣
      (let _ := H
       ihom L) :=
  letI := H
  -- Transport the owner tensor-left adjunction first through the braiding, then through the
  -- tensor/derived-tensor comparison.
  ((ihom.adjunction L).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight L)).ofNatIsoLeft
    (tensoringRightIsoDerivedTensorProduct L)

end MonoidalClosed

/-- Helper for Lemma 15.74.4: the morphism on a chosen derived internal Hom induced
contravariantly by a map on the source object and covariantly by a map on the target object. -/
noncomputable def derivedInternalHomMap
    (H : MonoidalClosed DMod)
    {K₁ K₂ L₁ L₂ : DMod}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    RHom[H](K₁, L₁) ⟶ RHom[H](K₂, L₂) :=
  letI := H
  -- This is the standard contravariance in the first variable followed by covariance in the
  -- second variable for the internal-Hom owner.
  (MonoidalClosed.pre fK).app L₁ ≫ (ihom K₂).map fL

/-- Helper for Lemma 15.74.4: the natural transformation on derived tensor functors induced by a
morphism of right tensor factors, obtained as the adjoint mate of the corresponding map on
derived internal-Hom functors. -/
noncomputable def derivedTensorProductMap
    (H : MonoidalClosed DMod)
    {L₁ L₂ : DMod} (f : L₁ ⟶ L₂) :
    derivedTensorProduct L₁ ⟶ derivedTensorProduct L₂ :=
  letI := H
  -- Take the mate of `MonoidalClosed.pre f` under the transported right-tensor adjunctions.
  (conjugateEquiv (H.derivedTensorAdj L₂) (H.derivedTensorAdj L₁)).symm
    (MonoidalClosed.pre f)

/-- Lemma 15.74.4: for a chosen monoidal-closed owner on `D(R)`, the canonical composition
morphism
`R\mathrm{Hom}_R(L, M) \otimes_R^{\mathbf L} R\mathrm{Hom}_R(K, L) \to
R\mathrm{Hom}_R(K, M)` is the canonical closed-monoidal composition map
`MonoidalClosed.comp`, transported to the source-facing derived tensor notation by the standard
tensor/derived-tensor comparison and the braiding on `D(R)`. -/
@[stacks 0A8J]
noncomputable def derivedInternalHom_comp
    (H : MonoidalClosed DMod)
    (K L M : DMod) :
    ((RHom[H](L, M)) ⊗[R]^L (RHom[H](K, L))) ⟶ RHom[H](K, M) :=
  letI := H
  -- Convert the source-facing derived tensor to the owner tensor, swap the two factors into the
  -- order expected by `MonoidalClosed.comp`, and then apply the owner composition morphism.
  (derivedCategory_tensorObj_iso_derivedTensorProduct
      (RHom[H](L, M))
      (RHom[H](K, L))).inv ≫
    (β_ (RHom[H](L, M)) (RHom[H](K, L))).hom ≫
      (MonoidalClosed.comp K L M)

-- Proof sketch: both sides are the mates, under the adjunction
-- `- \otimes_R^{\mathbf L} RHom_R(K₂, L) ⊣ RHom_R(RHom_R(K₂, L), -)`, of the same morphism
-- obtained from functoriality of `RHom_R(-, M)` in the first variable together with the canonical
-- closed-monoidal composition map.
end

end CategoryTheory
