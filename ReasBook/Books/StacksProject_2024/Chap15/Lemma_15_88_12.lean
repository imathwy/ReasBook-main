import Mathlib
import StacksProject_2024.Chap04.Example_4_22_6
import StacksProject_2024.Chap15.Lemma_15_88_3
import StacksProject_2024.Chap15.Lemma_15_88_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open SequentialProObjectMorphismRep

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod

/- Domain-style sampling for Lemma 15.88.12:
- primary domain: fixed-base derived inverse limits of sequential inverse systems of `A`-modules,
  together with the exact tensor-induced functors on `D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)`;
- sampled owner declarations:
  `stagewiseModuleDerivedLimitTower`,
  `stagewiseModuleDerivedLimitTowerFunctor`,
  `derivedInverseLimitTensorOnInverseSystemFunctor`,
  `SequentialProObjectMorphismRep.toProObjectHom`;
- best owner abstraction: the source-facing theorem should use the Chapter 15 exact functor
  `derivedInverseLimitTensorOnInverseSystemFunctor K : D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)
    ⥤ D(A)`, while the stagewise comparison should be expressed as the canonical stagewise tower
  in `D(A)` obtained from the upstream bridge owner `stagewiseModuleDerivedLimitTowerFunctor`;
- primitive data: a morphism `φ : E ⟶ D` in `D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)` and
  its image under the canonical stagewise tower functor in `D(A)`;
- derived API: the induced map of the stagewise tower functor and the induced map of the exact owner functor
  `derivedInverseLimitTensorOnInverseSystemFunctor K`.

Source/core/bridge triage:
- `source-facing`: the isomorphism statement for
  `R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} E) ⟶
    R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} D)`;
- `core/canonical`: `derivedInverseLimitTensorOnInverseSystemFunctor`,
  `stagewiseModuleDerivedLimitTowerFunctor`, and
  `SequentialProObjectMorphismRep.toProObjectHom`;
- `bridge/view`: the canonical stagewise tower functor
  `stagewiseModuleDerivedLimitTowerFunctor`. -/

-- Proof sketch: the exact owner functor
-- `derivedInverseLimitTensorOnInverseSystemFunctor K` first tensors the inverse system by the
-- fixed factor `K` and then applies `R lim`. Tensoring stagewise preserves the assumed
-- pro-isomorphism of the towers, so Lemma `15.87.13` applied to the tensorized stagewise map
-- yields an isomorphism on the resulting derived inverse limits.
/-- Lemma 15.88.12: let `A` be a ring and let `φ : E ⟶ D` be a morphism in
`D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)`. If the induced stagewise morphism
`(E_n^\bullet) \to (D_n^\bullet)` is an isomorphism of pro-objects in `D(A)`, then for every
`K ∈ D(A)` the corresponding map
`R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} E) ⟶
  R \!\varprojlim (\Delta(K) \otimes_A^{\mathbf L} D)`
is an isomorphism. This is the fixed-base owner-level form of the textbook map
`R \!\varprojlim_n (K \otimes_A^{\mathbf L} E_n) ⟶
  R \!\varprojlim_n (K \otimes_A^{\mathbf L} D_n)`. -/
theorem isIso_map_derivedInverseLimitTensorOnInverseSystemFunctor_of_stagewise_proIsomorphism
    {E D : DSeq} (φ : E ⟶ D)
    (hφ : IsIso (ofNatTrans ((stagewiseModuleDerivedLimitTowerFunctor A).map φ)).toProObjectHom)
    (K : DMod) :
    IsIso ((derivedInverseLimitTensorOnInverseSystemFunctor K).map φ) := by
  sorry

end
