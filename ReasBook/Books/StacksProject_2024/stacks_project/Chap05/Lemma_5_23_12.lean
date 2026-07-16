import StacksProject_2024.stacks_project.Chap05.Lemma_5_24_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/- Domain-style sampling for finite sober inverse limits:
- primary domain: spectral topological spaces and cofiltered limits in `TopCat`;
- sampled owner declarations:
  `SpectralSpace`,
  `IsSpectralMap`,
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`,
  `TopologicalSpace.NoetherianSpace.isCompact`;
- best owner abstraction: the chapter owner theorem
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`;
- primitive data: a directed inverse system of finite `T₀` quasi-sober spaces;
- derived API: each stage is spectral by finiteness plus quasi-sobriety, and each transition map is
  spectral because preimages of compact opens in finite spaces are compact.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma about inverse limits of finite sober spaces;
- `core/canonical`: `SpectralSpace`, `IsSpectralMap`, and the cofiltered-limit owner theorem from
  Lemma `5.24.5`;
- `bridge/view`: the local passage from finite `T₀` quasi-sober stages to the spectral-space
  hypotheses required by the owner theorem.
-/

-- Proof sketch: a finite `T₀` space with a generic point for every irreducible closed subset is
-- spectral, and the cofiltered limit topology has the compact-open basis, quasi-separatedness,
-- and sobriety described in the Stacks proof via Lemmas `5.14.1` and `5.14.2`.
/-- Lemma 5.23.12: the inverse limit of a directed inverse system of finite sober topological
spaces is a spectral topological space. -/
theorem spectralSpace_of_limit_finite_sober_inverse_system
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : Iᵒᵖ ⥤ TopCat.{u}) [∀ i : Iᵒᵖ, Finite (F.obj i)]
    [∀ i : Iᵒᵖ, T0Space (F.obj i)] [∀ i : Iᵒᵖ, QuasiSober (F.obj i)] :
    SpectralSpace ↥(limit F) := by
  letI : ∀ i : Iᵒᵖ, SpectralSpace ↥(F.obj i) := fun i ↦
    { toT0Space := inferInstance
      toCompactSpace := inferInstance
      toQuasiSober := inferInstance
      toQuasiSeparatedSpace := inferInstance
      toPrespectralSpace := inferInstance }
  have hF : ∀ ⦃j k : Iᵒᵖ⦄ (a : j ⟶ k), IsSpectralMap (F.map a) := by
    intro j k a
    refine ⟨(F.map a).hom.continuous, ?_⟩
    intro s _ _
    exact NoetherianSpace.isCompact ((F.map a) ⁻¹' s)
  exact spectralSpace_of_isLimit_of_cofiltered_spectral_diagram (limit.isLimit F) hF
