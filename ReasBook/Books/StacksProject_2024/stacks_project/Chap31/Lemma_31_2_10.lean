import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap10.Lemma_10_63_7
import StacksProject_2024.Chap31.Definition_31_2_1
import StacksProject_2024.Chap31.Lemma_31_2_4
import StacksProject_2024.Chap31.Lemma_31_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

private theorem stalkModuleInjective_of_mono {𝒜 ℬ : X.Modules} (φ : 𝒜 ⟶ ℬ) [Mono φ] (x : X) :
    Function.Injective (moduleStalkHom x φ) := by
  have hmono : Mono ((RingedSpace.stalkModuleFunctor (X := X) x).map φ) :=
    Functor.map_mono (RingedSpace.stalkModuleFunctor (X := X) x) φ
  simpa using (ModuleCat.mono_iff_injective (moduleStalkHom x φ)).1 hmono

private theorem isZero_stalkKernel_of_moduleStalkHom_injective (φ : ℱ ⟶ 𝒢) (x : X)
    (hφx : Function.Injective (moduleStalkHom x φ)) :
    IsZero (RingedSpace.stalkModuleCat (kernel φ) x) := by
  have hιx : Function.Injective (moduleStalkHom x (kernel.ι φ)) :=
    stalkModuleInjective_of_mono (kernel.ι φ) x
  have hkernel_map_eq_zero (m : RingedSpace.stalkModuleCat (kernel φ) x) :
      moduleStalkHom x φ (moduleStalkHom x (kernel.ι φ) m) = 0 := by
    let ι : kernel φ ⟶ ℱ := kernel.ι φ
    have hcomp :
        moduleStalkHom x ι ≫ moduleStalkHom x φ = moduleStalkHom x (ι ≫ φ) := by
      simpa using ((RingedSpace.stalkModuleFunctor (X := X) x).map_comp ι φ).symm
    have hzero : moduleStalkHom x (ι ≫ φ) = 0 := by
      rw [show ι ≫ φ = 0 by simpa [ι] using kernel.condition φ]
      simpa using
        (Functor.map_zero (RingedSpace.stalkModuleFunctor (X := X) x)
          (kernel φ) 𝒢)
    have hm :
        (moduleStalkHom x ι ≫ moduleStalkHom x φ) m = 0 := by
      rw [hcomp, hzero]
      rfl
    simpa [ι, ConcreteCategory.comp_apply] using hm
  letI : Subsingleton (RingedSpace.stalkModuleCat (kernel φ) x) := ⟨fun m n ↦ by
    apply hιx
    apply hφx
    rw [hkernel_map_eq_zero m, hkernel_map_eq_zero n]⟩
  exact ModuleCat.isZero_of_subsingleton (RingedSpace.stalkModuleCat (kernel φ) x)

-- Semantic recall: the source-facing owner here is the associated-points injectivity criterion
-- itself. The public API stays on `associatedPoints ℱ`, `RingedSpace.moduleStalkHom x φ`, and
-- `Mono φ`, while proof work is deferred.

/-- Lemma 31.2.10: let `X` be a locally Noetherian scheme and let `φ : ℱ ⟶ 𝒢` be a morphism of
quasi-coherent `\mathcal O_X`-modules. Assume that for every point `x : X`, either the stalk map
`φ_x : ℱ_x ⟶ 𝒢_x` is injective, or `x` is not an associated point of `ℱ`. Then `φ` is injective.
-/
@[stacks 0AVL]
theorem mono_of_stalkwise_injective_or_not_mem_associatedPoints
    (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X,
      Function.Injective (moduleStalkHom x φ) ∨ x ∉ associatedPoints ℱ) :
    Mono φ := by
  let S : ShortComplex X.Modules := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.ShortExact := by
    exact ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact φ) inferInstance
      inferInstance
  have hkernel_empty : associatedPoints (kernel φ) = (∅ : Set X) := by
    apply Set.eq_empty_iff_forall_not_mem.2
    intro x hx
    have hxℱ : x ∈ associatedPoints ℱ :=
      associatedPoints_left_subset_of_shortExact hS hx
    rcases hφ x with hφx | hxnot
    · have hzero :
          IsZero (RingedSpace.stalkModuleCat (kernel φ) x) :=
        isZero_stalkKernel_of_moduleStalkHom_injective φ x hφx
      letI : Subsingleton (RingedSpace.stalkModuleCat (kernel φ) x) :=
        ModuleCat.subsingleton_of_isZero hzero
      have hEmpty :
          associatedPrimesOfModule (X.presheaf.stalk x)
            (RingedSpace.stalkModuleCat (kernel φ) x) = ∅ := by
        rw [subsingleton_iff_associatedPrimesOfModule_eq_empty]
        infer_instance
      rw [mem_associatedPoints_iff] at hx
      simpa [hEmpty] using hx
    · exact hxnot hxℱ
  have hkernel_zero : IsZero (kernel φ) := by
    exact (isZero_iff_associatedPoints_eq_empty (kernel φ)).2 hkernel_empty
  exact CategoryTheory.Preadditive.mono_of_isZero_kernel φ hkernel_zero

/-- Companion bridge for Lemma 31.2.10: it is enough to check injectivity of the stalk map `φ_x`
at the associated points of `ℱ`. -/
theorem mono_of_stalkwise_injective_on_associatedPoints
    (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X, x ∈ associatedPoints ℱ → Function.Injective (moduleStalkHom x φ)) :
    Mono φ := by
  refine mono_of_stalkwise_injective_or_not_mem_associatedPoints φ ?_
  intro x
  by_cases hx : x ∈ associatedPoints ℱ
  · exact Or.inl (hφ x hx)
  · exact Or.inr hx

end AlgebraicGeometry.Scheme.Modules
