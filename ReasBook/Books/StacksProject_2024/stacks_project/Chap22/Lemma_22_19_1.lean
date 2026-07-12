import StacksProject_2024.Chap22.Lemma_22_7_3

open CategoryTheory

noncomputable section

universe u

namespace CochainComplex

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ

/-- Companion instance for Lemma 22.19.1: if the underlying graded morphism of a differential
graded `A`-module map `ι : I ⟶ M` is a monomorphism and the underlying graded module of `I` is
injective, then `ι` is split after forgetting the differential. -/
instance forget_isSplitMono_of_forgetMono_of_gradedInjective
    {I M : DGMod} (ι : I ⟶ M) [Mono (dgModuleUnderlyingGradedHomSystem.map ι)]
    [Injective (dgModuleUnderlyingGradedHomSystem.obj I)] :
    IsSplitMono (dgModuleUnderlyingGradedHomSystem.map ι) :=
  let retraction :
      dgModuleUnderlyingGradedHomSystem.obj M ⟶ dgModuleUnderlyingGradedHomSystem.obj I := by
    letI : Mono (dgModuleUnderlyingGradedHomSystem.map ι) := inferInstance
    exact Injective.factorThru
      (𝟙 (dgModuleUnderlyingGradedHomSystem.obj I))
      (dgModuleUnderlyingGradedHomSystem.map ι)
  IsSplitMono.mk' ⟨retraction, by
    letI : Mono (dgModuleUnderlyingGradedHomSystem.map ι) := inferInstance
    funext n
    simpa [retraction, dgModuleUnderlyingGradedHomSystem] using
      congr_fun
        (Injective.comp_factorThru
          (𝟙 (dgModuleUnderlyingGradedHomSystem.obj I))
          (dgModuleUnderlyingGradedHomSystem.map ι)) n⟩

/-- Lemma 22.19.1: in the canonical cochain-complex model for differential graded `A`-modules, a
monomorphism on the underlying graded `A`-modules with graded-injective source is an admissible
monomorphism after forgetting the differential. -/
@[stacks 09K2]
theorem isAdmissibleMono_of_forgetMono_of_gradedInjective
    {I M : DGMod} (ι : I ⟶ M) [Mono (dgModuleUnderlyingGradedHomSystem.map ι)]
    [Injective (dgModuleUnderlyingGradedHomSystem.obj I)] :
    IsAdmissibleMono dgModuleUnderlyingGradedHomSystem ι := by
  change IsSplitMono (dgModuleUnderlyingGradedHomSystem.map ι)
  infer_instance

/-- Companion view of Lemma 22.19.1: the admissible-monomorphism criterion yields the degreewise
split-monomorphism conclusion used by the Chapter 13 strictification results. -/
theorem degreewiseSplitMono_of_forgetMono_of_gradedInjective
    {I M : DGMod} (ι : I ⟶ M) [Mono (dgModuleUnderlyingGradedHomSystem.map ι)]
    [Injective (dgModuleUnderlyingGradedHomSystem.obj I)] :
    ∀ n : ℤ, IsSplitMono (ι.f n) := by
  exact
    termwiseSplitMono_of_admissibleMono
      (isAdmissibleMono_of_forgetMono_of_gradedInjective ι)

end

end CochainComplex
