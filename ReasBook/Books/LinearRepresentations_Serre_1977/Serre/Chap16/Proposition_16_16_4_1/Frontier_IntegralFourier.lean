import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Index
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.CanonicalPacketFrontier
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_PacketReindex
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_CharZeroSupportedFamily
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_AsAlgebraHomTransport
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_FiberInternalCoordinate
import LinearRepresentations_Serre_1977.Chap16.Proposition_16_16_4_1.Frontier_FourierOrthogonality

noncomputable section

open scoped MonoidAlgebra
open Representation
open CategoryTheory

universe u v w x y

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type v} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type w} [Group G]
variable {E : Type x} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

local notation "k" => IsLocalRing.ResidueField A

namespace StableLattice

section DefectZero

variable [Finite G] [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
variable {ρ : Representation K G E} [FiniteDimensional K E]
variable (L : StableLattice A ρ)

/-- Helper for Proposition 16-16.4-1: for a single basis matrix unit on the stable lattice, the
ambient action of Serre's integral Fourier element is exactly the scalar-extended matrix unit.
This is the unreduced source Proposition `11` specialization that still has to be formalized in
the equal-characteristic branch. -/
lemma integral_fourier_matrix_unit_action_local
    [CharP K p] [CharZero K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A L.toSubmodule) (i j : ι)
    (hdefect : ρ.HasDefectZero p) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K)
          (L.serre_fourier_element hdefect ((b.coord i).smulRight (b j)))) =
      (L.toSubmodule_subtype_isBaseChange).endHom ((b.coord i).smulRight (b j)) := by
  -- Reuse the stronger basis-unit owner so downstream consumers still keep the original name.
  exact
    L.defect_zero_basis_unit_fourier_action_eq_baseChange_local
      (p := p) (ρ := ρ) (b := b) i j hdefect

/-- Helper for Proposition 16-16.4-1: once the equal-characteristic Fourier identity is proved on
the basis matrix units of the stable lattice, additivity and `A`-linearity of Serre's integral
Fourier section extend it to every lattice endomorphism. -/
lemma integral_fourier_self_action_local
    [CharP K p] [CharZero K]
    (hdefect : ρ.HasDefectZero p) (φ : Module.End A L.toSubmodule) :
    ρ.asAlgebraHom
        (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect φ)) =
      (L.toSubmodule_subtype_isBaseChange).endHom φ := by
  classical
  let ι := Module.Free.ChooseBasisIndex A L.toSubmodule
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  let b : Module.Basis ι A L.toSubmodule := Module.Free.chooseBasis A L.toSubmodule
  let hf : IsBaseChange K (L.toSubmodule.subtype : L.toSubmodule →ₗ[A] E) :=
    L.toSubmodule_subtype_isBaseChange
  let fourierAction : Module.End A L.toSubmodule →ₗ[A] Module.End K E :=
    { toFun := fun ψ ↦
        ρ.asAlgebraHom
          (MonoidAlgebra.mapRingHom G (algebraMap A K) (L.serre_fourier_element hdefect ψ))
      map_add' := by
        intro ψ χ
        rw [L.serre_fourier_add_pre_local (p := p) (ρ := ρ) hdefect ψ χ]
        simp
      map_smul' := by
        intro a ψ
        rw [L.serre_fourier_smul_pre_local (p := p) (ρ := ρ) hdefect a ψ]
        have hmap :
            MonoidAlgebra.mapRingHom G (algebraMap A K)
                (a • L.serre_fourier_element hdefect ψ) =
              (algebraMap A K a) •
                MonoidAlgebra.mapRingHom G (algebraMap A K)
                  (L.serre_fourier_element hdefect ψ) := by
          ext s
          simp [MonoidAlgebra.mapRingHom_apply, Algebra.smul_def]
        rw [hmap, AlgHom.map_smul_of_tower]
        exact
          (IsScalarTower.algebraMap_smul
            (R := A) (A := K) a
            (ρ.asAlgebraHom
              (MonoidAlgebra.mapRingHom G (algebraMap A K)
                (L.serre_fourier_element hdefect ψ)) : Module.End K E)) }
  let baseChangeAction : Module.End A L.toSubmodule →ₗ[A] Module.End K E :=
    { toFun := hf.endHom
      map_add' := by
        intro ψ χ
        apply (b.extendOfIsLattice K).ext
        intro i
        simp [hf.endHom_comp_apply, Module.Basis.extendOfIsLattice_apply]
      map_smul' := by
        intro a ψ
        apply (b.extendOfIsLattice K).ext
        intro i
        simp [hf.endHom_comp_apply, Module.Basis.extendOfIsLattice_apply] }
  have hdecomp :
      φ =
        ∑ i : ι, ∑ j : ι,
          (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j)) :=
    L.endHom_eq_sum_matrix_units_local (ρ := ρ) (b := b) φ
  have hfourier_decomp :
      fourierAction φ =
      ∑ i : ι, ∑ j : ι,
        (LinearMap.toMatrix b b φ j i) •
          fourierAction ((b.coord i).smulRight (b j)) := by
    calc
      fourierAction φ =
        fourierAction
          (∑ i : ι, ∑ j : ι,
            (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) := by
              exact congrArg fourierAction hdecomp
      _ =
        ∑ i : ι,
          fourierAction
            (∑ j : ι, (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) := by
              exact _root_.map_sum fourierAction
                (fun i : ι ↦
                  ∑ j : ι, (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j)))
                (Finset.univ : Finset ι)
      _ =
        ∑ i : ι, ∑ j : ι,
          (LinearMap.toMatrix b b φ j i) •
            fourierAction ((b.coord i).smulRight (b j)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              calc
                fourierAction (∑ j : ι, (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) =
                    ∑ j : ι,
                      fourierAction
                        ((LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) := by
                          exact _root_.map_sum fourierAction
                            (fun j : ι ↦
                              (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j)))
                            (Finset.univ : Finset ι)
                _ = ∑ j : ι,
                      (LinearMap.toMatrix b b φ j i) •
                        fourierAction ((b.coord i).smulRight (b j)) := by
                          simp [fourierAction]
  have hbaseChange_decomp :
      baseChangeAction φ =
      ∑ i : ι, ∑ j : ι,
        (LinearMap.toMatrix b b φ j i) •
          baseChangeAction ((b.coord i).smulRight (b j)) := by
    calc
      baseChangeAction φ =
        baseChangeAction
          (∑ i : ι, ∑ j : ι,
            (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) := by
              exact congrArg baseChangeAction hdecomp
      _ =
        ∑ i : ι,
          baseChangeAction
            (∑ j : ι, (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) := by
              exact _root_.map_sum baseChangeAction
                (fun i : ι ↦
                  ∑ j : ι, (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j)))
                (Finset.univ : Finset ι)
      _ =
        ∑ i : ι, ∑ j : ι,
          (LinearMap.toMatrix b b φ j i) •
            baseChangeAction ((b.coord i).smulRight (b j)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              calc
                baseChangeAction
                    (∑ j : ι, (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) =
                  ∑ j : ι,
                    baseChangeAction
                      ((LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j))) := by
                        exact _root_.map_sum baseChangeAction
                          (fun j : ι ↦
                            (LinearMap.toMatrix b b φ j i) • ((b.coord i).smulRight (b j)))
                          (Finset.univ : Finset ι)
                _ = ∑ j : ι,
                      (LinearMap.toMatrix b b φ j i) •
                        baseChangeAction ((b.coord i).smulRight (b j)) := by
                          simp [baseChangeAction]
  -- Expand `φ` in basis units and compare the two `A`-linear maps termwise.
  change fourierAction φ = baseChangeAction φ
  rw [hfourier_decomp, hbaseChange_decomp]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  congr 1
  exact
    L.basis_unit_fourier_action_eq_baseChange_direct_local
      (p := p) (ρ := ρ) (b := b) i j hdefect


end DefectZero

end StableLattice

end
