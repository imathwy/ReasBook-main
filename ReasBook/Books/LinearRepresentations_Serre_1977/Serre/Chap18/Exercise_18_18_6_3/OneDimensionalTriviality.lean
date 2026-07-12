import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_3.API
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_6_3.Shared

noncomputable section

open Representation

namespace Representation

local notation "A5" => alternatingGroup (Fin 5)

/-- Helper for Exercise 18-18.6-3: every one-dimensional `A₅`-representation is equivalent to the
trivial representation, because its associated unit character must be trivial. -/
theorem alternatingGroup_fin5_equiv_trivial_of_finrank_one
    {k : Type*} [Field k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k A5 V) (hV : Module.finrank k V = 1) :
    Nonempty (ρ.Equiv (Representation.trivial k A5 k)) := by
  let scalarEquiv : k ≃ₗ[k] (V →ₗ[k] V) := LinearEquiv.smul_id_of_finrank_eq_one hV
  have hscalar (c : k) : scalarEquiv c = c • LinearMap.id := by
    exact LinearEquiv.smul_id_of_finrank_eq_one_apply hV c
  let α₀ : A5 → k := fun g ↦ scalarEquiv.symm (ρ g)
  have hα₀_eq (g : A5) : ρ g = α₀ g • LinearMap.id := by
    calc
      ρ g = scalarEquiv (α₀ g) := by
        simp [α₀]
      _ = α₀ g • LinearMap.id := hscalar _
  have hα₀_one : α₀ 1 = 1 := by
    have hscalar1 : scalarEquiv (1 : k) = (1 : V →ₗ[k] V) := by
      simpa using hscalar (1 : k)
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ 1) = ρ 1 := by
        simp [α₀]
      _ = (1 : V →ₗ[k] V) := by
        simp
      _ = scalarEquiv 1 := hscalar1.symm
  have hα₀_mul (g h : A5) : α₀ (g * h) = α₀ g * α₀ h := by
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ (g * h)) = ρ (g * h) := by
        simp [α₀]
      _ = ρ g * ρ h := by
        simp
      _ = (α₀ g * α₀ h) • LinearMap.id := by
        rw [hα₀_eq, hα₀_eq]
        ext v
        simp [smul_smul, mul_comm]
      _ = scalarEquiv (α₀ g * α₀ h) := (hscalar _).symm
  have hα₀_ne_zero (g : A5) : α₀ g ≠ 0 := by
    have hpos : 0 < Module.finrank k V := by
      simpa [hV]
    letI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
    intro hzero
    have hzeroMap : ρ g = 0 := by
      simp [hα₀_eq, hzero]
    have hmul : ρ g * ρ g⁻¹ = (1 : V →ₗ[k] V) := by
      simpa using (ρ.map_mul g g⁻¹).symm
    have hidzero : (1 : V →ₗ[k] V) = 0 := by
      calc
        (1 : V →ₗ[k] V) = ρ g * ρ g⁻¹ := hmul.symm
        _ = 0 := by
              rw [hzeroMap]
              simp
    exact one_ne_zero hidzero
  let α : A5 →* kˣ :=
    { toFun := fun g ↦ Units.mk0 (α₀ g) (hα₀_ne_zero g)
      map_one' := by
        ext
        simpa using hα₀_one
      map_mul' := by
        intro g h
        ext
        simpa using hα₀_mul g h }
  have hρ_one_dimensional : Nonempty (ρ.Equiv (oneDimensionalRepresentation α)) := by
    let e : V ≃ₗ[k] k := (Module.nonempty_linearEquiv_of_finrank_eq_one hV).some.symm
    refine ⟨Representation.Equiv.mk e ?_⟩
    intro g
    ext v
    have hv := LinearMap.congr_fun (by simpa [α] using hα₀_eq g) v
    simpa [oneDimensionalRepresentation, LinearMap.lsmul_apply] using congrArg e hv
  have hα : α = 1 :=
    Representation.alternatingGroup_fin5_units_hom_eq_one_over_any_field α
  have hone_dimensional_trivial :
      Nonempty ((oneDimensionalRepresentation α).Equiv (Representation.trivial k A5 k)) := by
    rw [hα]
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl k k) ?_⟩
    intro g
    ext x
    simp [oneDimensionalRepresentation, Representation.trivial, LinearMap.lsmul_apply]
  rcases hρ_one_dimensional with ⟨e⟩
  rcases hone_dimensional_trivial with ⟨e'⟩
  exact ⟨e.trans e'⟩

end Representation
