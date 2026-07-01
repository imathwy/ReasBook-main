import Mathlib
import stacks_project.Chap13.Definition_13_34_1
import stacks_project.Chap15.Definition_15_59_13
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Lemma_15_88_1_FixedBase
import stacks_project.Chap19.Lemma_19_13_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod

private abbrev stageSingle : ModuleCat A ⥤ DMod :=
  ModuleCat.single0Functor

private abbrev systemSingle : SeqMod ⥤ DSeq :=
  show SeqMod ⥤ DSeq from
    DerivedCategory.singleFunctor SeqMod 0

/- Domain-style sampling for Lemma 15.103.3:
- primary domain: sequential derived inverse limits in `D(A)` and their compatibility with the
  exact tensor functor `- ⊗[A]^L K`;
- sampled owner declarations:
  * `moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation`
  * the fixed-base bridge owner notation `R lim(_)` from `Lemma_15_88_1_FixedBase`
  * `CategoryTheory.IsDerivedLimit`
  * `ModuleCat.single0Functor`
  * `DerivedCategory.singleFunctor`
  * `CategoryTheory.derivedTensorProduct`
- best owner abstraction: the source-facing statement remains an `IsDerivedLimit` claim for the
  tensor tower, while the chosen derived-limit object is the canonical fixed-base Chapter 15 owner
  `R lim(systemSingle.obj M)` from `Lemma_15_88_1_FixedBase`; the bridge data are the stagewise
  degree-zero embedding `stageSingle` and the system-level degree-zero embedding `systemSingle`;
- primitive vs. derived:
  primitive data are only the pseudo-coherent object `K : D(A)` and the sequential inverse system
  `M : ℕᵒᵖ ⥤ Mod_A`;
  derived API is the tower `M ⋙ stageSingle ⋙ derivedTensorProduct K` and the tensorized chosen
  derived inverse limit `(R lim(systemSingle.obj M)) ⊗[A]^L K`.

Source/core/bridge triage:
- `source-facing`: the tensor compatibility statement that
  `(R lim(systemSingle.obj M)) ⊗[A]^L K` is a derived limit of the tensor tower;
- `core/canonical`: `R lim(_)`, `IsDerivedLimit`, and `derivedTensorProduct`;
- `bridge/view`: the degree-zero embeddings `stageSingle` and `systemSingle`, and the tower
  `M ⋙ stageSingle`.
-/

-- Proof sketch: apply the Milnor distinguished triangle defining the chosen derived inverse limit
-- of `M`, then apply the exact functor `derivedTensorProduct K`. Lemma `15.66.5` identifies the
-- images of the two product terms with the corresponding products of the stagewise derived tensor
-- products because `K` is pseudo-coherent, so the resulting triangle is exactly the Milnor
-- triangle for the tensor tower.
/-- Lemma 15.103.3: if `K ∈ D(A)` is pseudo-coherent and `(M_n)` is a sequential inverse system
of `A`-modules, then tensoring the chosen derived inverse limit of `(M_n[0])` with `K` gives a
derived limit of the stagewise tensor tower `((M_n[0]) \otimes_A^{\mathbf L} K)_n`. By symmetry
of the derived tensor product, this is the statement form of the textbook identity
`R\!\varprojlim_n (K \otimes_A^{\mathbf L} M_n) = K \otimes_A^{\mathbf L} R\!\varprojlim_n M_n`.
-/
lemma moduleDerivedInverseLimit_tensor_isDerivedLimit_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) (M : SeqMod) :
    IsDerivedLimit
      ((M ⋙ stageSingle) ⋙ derivedTensorProduct K)
      ((R lim(systemSingle.obj M)) ⊗[A]^L K) := sorry

end

end CategoryTheory
