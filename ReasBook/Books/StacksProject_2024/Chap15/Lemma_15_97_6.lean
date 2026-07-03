import Mathlib.LinearAlgebra.TensorProduct.Tower
import StacksProject_2024.Chap15.Lemma_15_96_10
import StacksProject_2024.Chap15.Lemma_15_97_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open BerthelotOgusEtaReduction.Nat
open scoped nonZeroDivisors
open scoped TensorProduct

noncomputable section

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "CpxA" => NatModuleCochainComplex A
local notation "baseChange" =>
  Functor.mapHomologicalComplex (ModuleCat.extendScalars (algebraMap A B)) (up ℕ)

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
  { __ := AddEquiv.refl B
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

private noncomputable def extendScalarsTermLinearEquiv
    (K : CpxA) (i : ℕ) :
    ((((baseChange).obj K).X i : ModuleCat B)) ≃ₗ[B] (B ⊗[A] (K.X i)) := by
  simpa [Functor.mapHomologicalComplex_obj_X, ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl A (K.X i)))

private theorem etaFDegreeSubmodule_toBaseChange_bijective
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    Function.Bijective ((etaFDegreeSubmodule f M i).toBaseChange B) := by
  sorry

private theorem etaFDegreeSubmodule_baseChange_map_eq
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    ((etaFDegreeSubmodule f M i).baseChange B).map
        ((extendScalarsTermLinearEquiv M i).symm.toLinearMap) =
      etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) i := by
  sorry

private noncomputable def etaFDegreeTensorBaseChangeIso
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    (B ⊗[A] (((η[f] M).X i : ModuleCat A))) ≃ₗ[B] (etaFDegreeSubmodule f M i).baseChange B := by
  simpa using
    (LinearEquiv.ofBijective
      ((etaFDegreeSubmodule f M i).toBaseChange B)
      (etaFDegreeSubmodule_toBaseChange_bijective f M hf hg hI i) :
        (B ⊗[A] etaFDegreeSubmodule f M i) ≃ₗ[B] (etaFDegreeSubmodule f M i).baseChange B)

private noncomputable def etaFDegreeBaseChangeIso
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    (((baseChange).obj (η[f] M)).X i) ≅
      (η[algebraMap A B f] ((baseChange).obj M)).X i := by
  let eLeft :
      ((((baseChange).obj (η[f] M)).X i : ModuleCat B)) ≃ₗ[B]
        (B ⊗[A] (((η[f] M).X i : ModuleCat A))) :=
    extendScalarsTermLinearEquiv (η[f] M) i
  let eRight :
      (etaFDegreeSubmodule f M i).baseChange B ≃ₗ[B]
        etaFDegreeSubmodule (algebraMap A B f) ((baseChange).obj M) i :=
    ((extendScalarsTermLinearEquiv M i).symm).ofSubmodules _ _
      (etaFDegreeSubmodule_baseChange_map_eq f M hf hg hI i)
  exact ((eLeft.trans (etaFDegreeTensorBaseChangeIso f M hf hg hI i)).trans
    eRight).toModuleIso

private theorem etaFDegreeBaseChangeIso_comm_succ
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i : ℕ) :
    (etaFDegreeBaseChangeIso f M hf hg hI i).hom ≫
        (η[algebraMap A B f] ((baseChange).obj M)).d i (i + 1) =
      ((baseChange).obj (η[f] M)).d i (i + 1) ≫
        (etaFDegreeBaseChangeIso f M hf hg hI (i + 1)).hom := by
  sorry

private theorem etaFDegreeBaseChangeIso_comm
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)
    (i j : ℕ) (hij : (up ℕ).Rel i j) :
    (etaFDegreeBaseChangeIso f M hf hg hI i).hom ≫
        (η[algebraMap A B f] ((baseChange).obj M)).d i j =
      ((baseChange).obj (η[f] M)).d i j ≫
        (etaFDegreeBaseChangeIso f M hf hg hI j).hom := by
  cases hij
  simpa using etaFDegreeBaseChangeIso_comm_succ f M hf hg hI i

/-
Domain-style sampling:
- primary domain: scalar extension of the source-facing Berthelot-Ogus complex `η[f] M` on
  `ℕ`-indexed cochain complexes of finite free modules;
- sampled owner declarations:
  `η[_] _`,
  `NatModuleCochainComplex.etaDeterminantalIdeal`,
  `etaDeterminantalIdeal_baseChange`,
  `etaFDegreePairMap_isSplitMono_of_determinantalIdeal_isPrincipal`,
  `Functor.mapHomologicalComplex`;
- best owner abstraction:
  `source-facing`: the canonical base-change isomorphism for `η[f] M`;
  `core/canonical`: the owners `η[_] _`, `NatModuleCochainComplex.etaDeterminantalIdeal`, and
    scalar extension by `baseChange`;
  `bridge/view`: the comparison between `baseChange.obj (η[f] M)` and
    `η[algebraMap A B f] (baseChange.obj M)`;
- primitive data vs derived API: the primitive data are the finite-free complex `M`, the
  nonzerodivisor hypotheses on `f` and its image, and principality of the source
  determinantal ideals. The comparison isomorphism is derived bridge data and should stay a direct
  named isomorphism rather than a wrapper around auxiliary comparison packages. -/

/-- Lemma 15.97.6: let `A → B` be a ring map, let `f ∈ A` be a nonzerodivisor, and let `M^\bullet`
be a complex of finite free `A`-modules. If the image of `f` in `B` is a nonzerodivisor and every
determinantal ideal `I_i(M^\bullet, f)` is principal, then the base change of `η_f M^\bullet` is
canonically isomorphic to `η_g(M^\bullet ⊗_A B)` for `g = algebraMap A B f`. No bounded-above
hypothesis is needed for this comparison. -/
noncomputable def etaFComplex_baseChangeIso_of_determinantalIdeal_isPrincipal
    (f : A) (M : CpxA)
    [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
    (hf : f ∈ nonZeroDivisors A)
    (hg : algebraMap A B f ∈ nonZeroDivisors B)
    (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal) :
    ((baseChange).obj (η[f] M)) ≅ η[algebraMap A B f] ((baseChange).obj M) :=
  HomologicalComplex.Hom.isoOfComponents
    (etaFDegreeBaseChangeIso f M hf hg hI)
    (etaFDegreeBaseChangeIso_comm f M hf hg hI)

end
