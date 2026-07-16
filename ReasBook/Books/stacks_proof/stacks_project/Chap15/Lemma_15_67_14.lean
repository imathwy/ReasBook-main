import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_67_1
import stacks_proof.stacks_project.Chap15.Lemma_15_67_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Helper for Lemma 15.67.14: extension of scalars along `A → B` is the usual tensor product
with `B`. -/
private noncomputable def extendScalars_tensor_linearEquiv (M : ModuleCat A) :
    ((ModuleCat.extendScalars (algebraMap A B)).obj M : Type u) ≃ₗ[B] TensorProduct A B M := by
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
    { __ := AddEquiv.refl B
      map_smul' := fun _ _ ↦ rfl }
  let _ : IsScalarTower A B
      ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
    IsScalarTower.of_algebraMap_smul fun a b ↦ rfl
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl A ↑M))

/-- Helper for Lemma 15.67.14: a flat extension of scalars carries a finite flat
resolution over `A` to a finite flat resolution over `B` of the same length. -/
private theorem hasFiniteFlatResolutionLengthLE_extendScalars
    [Module.Flat A B] {M : ModuleCat A} {d : ℕ}
    (hM : ModuleCat.HasFiniteFlatResolutionLengthLE M d) :
    ModuleCat.HasFiniteFlatResolutionLengthLE
      ((ModuleCat.extendScalars (algebraMap A B)).obj M) d := by
  cases d with
  | zero =>
      let _ : Module.Flat A M := hM
      have hflatTensor : Module.Flat B (TensorProduct A B M) := by
        simpa using (Module.Flat.baseChange (R := A) (S := B) (M := M))
      simpa [ModuleCat.HasFiniteFlatResolutionLengthLE] using
        (Module.Flat.of_linearEquiv
          (extendScalars_tensor_linearEquiv (A := A) (B := B) M) : Module.Flat B
            ((ModuleCat.extendScalars (algebraMap A B)).obj M))
  | succ n =>
      rcases hM with ⟨F, hFflat, δ, π, hπsurj, hδπ, hδ, hδinj⟩
      let G : Fin (n + 2) → ModuleCat B := fun i ↦ ModuleCat.of B (TensorProduct A B (F i))
      let δB : (i : Fin (n + 1)) → G i.succ ⟶ G i.castSucc :=
        fun i ↦ ModuleCat.ofHom (LinearMap.lTensor B (δ i).hom)
      let πBase : G 0 ⟶ ModuleCat.of B (TensorProduct A B M) :=
        ModuleCat.ofHom (LinearMap.lTensor B π.hom)
      let e := extendScalars_tensor_linearEquiv (A := A) (B := B) M
      let eHom := e.symm.toLinearMap
      let πB : G 0 ⟶ (ModuleCat.extendScalars (algebraMap A B)).obj M :=
        ModuleCat.ofHom (eHom.comp πBase.hom)
      refine ⟨G, ?_⟩
      constructor
      · intro i
        let _ : Module.Flat A (F i) := hFflat i
        have hflatTensor : Module.Flat B (TensorProduct A B (F i)) := by
          simpa using (Module.Flat.baseChange (R := A) (S := B) (M := F i))
        simpa [G] using hflatTensor
      · refine ⟨δB, πB, ?_, ?_, ?_, ?_⟩
        · -- Proof comment: tensoring with `B` preserves surjections.
          have hπBase :
              Function.Surjective πBase := by
            simpa [πBase] using
              (LinearMap.lTensor_surjective (R := A) (Q := B) hπsurj)
          intro x
          rcases eHom.surjective x with ⟨x', rfl⟩
          rcases hπBase x' with ⟨y, rfl⟩
          rfl
        · -- Proof comment: flatness of `B` makes extension of scalars exact on the resolution.
          have hδπBase :
              Function.Exact (δB 0) πBase := by
            simpa [δB, πBase] using
              (Module.Flat.lTensor_exact (R := A) (M := B) hδπ)
          intro x
          constructor
          · intro hx
            have hx' : πBase x = 0 := by
              apply eHom.injective
              simpa [πB] using hx
            exact (hδπBase x).1 hx'
          · rintro ⟨y, rfl⟩
            have hy : πBase ((δB 0) y) = 0 := by
              exact congrArg (fun f ↦ f y) (Function.Exact.comp_eq_zero hδπBase)
            apply eHom.injective
            simpa [πB] using hy
        · intro i
          simpa [δB] using
            (Module.Flat.lTensor_exact (R := A) (M := B) (hδ i))
        · simpa [δB] using
            (Module.Flat.lTensor_preserves_injective_linearMap
              (R := A) (M := B) (δ (Fin.last n)) hδinj)

/-- Lemma 15.67.14: for a flat ring map `A → B`, if an `A`-module `M` has tor dimension at most
`d`, then its scalar extension `M ⊗_A B` has tor dimension at most `d` as a `B`-module. -/
@[stacks 066M]
theorem moduleHasTorDimensionLE_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A) (d : ℕ)
    (hM : ModuleHasTorDimensionLE M d) :
    ModuleHasTorDimensionLE ((ModuleCat.extendScalars (algebraMap A B)).obj M) d := by
  let _ : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hflat
  have hResolution : ModuleCat.HasFiniteFlatResolutionLengthLE M d :=
    ModuleCat.ModuleHasTorDimensionLE.hasFiniteFlatResolutionLengthLE (M := M) hM
  -- Proof comment: transport a finite flat `A`-resolution of `M` across the flat map
  -- `A → B`, then convert the resulting finite flat `B`-resolution back to tor dimension.
  exact
    ModuleCat.HasFiniteFlatResolutionLengthLE.hasTorDimensionLE
      (M := ((ModuleCat.extendScalars (algebraMap A B)).obj M))
      (hasFiniteFlatResolutionLengthLE_extendScalars (A := A) (B := B) hResolution)

end

end CategoryTheory
