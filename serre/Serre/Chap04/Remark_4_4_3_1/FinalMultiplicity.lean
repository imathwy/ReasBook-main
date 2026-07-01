import Serre.Chap04.Remark_4_4_3_1.CopyLocalWitness

open MeasureTheory
open DomMulAct
open scoped ENNReal MonoidAlgebra
open scoped ComplexStarModule
open scoped Representation.ExplicitDecomposition

noncomputable section

universe u v

namespace Representation

open Remark_4_4_3_1
local notation "L²(" G ")" => G →₂[(Measure.haar : Measure G)] ℂ

section PeterWeyl

variable {G : Type u} [MeasurableSpace G] [Group G] [TopologicalSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [Finite G]
variable {W : Type v} [TopologicalSpace W] [AddCommGroup W] [Module ℂ W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]

theorem
    matrixCoefficient_codRestrict_fixedVector_mem_evalRange_of_firstCoordinate_orthogonal_zero
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (hfirst_zero :
      ∀ y :
          (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule,
        y ∈ V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex →
        (∀ z ∈ LinearMap.range
            (matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ),
          inner ℂ z y = 0) →
        y = 0)
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    D (chosen_irreducible_vector (G := G) σ) ∈
      LinearMap.range
        (matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ) := by
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  let E := matrixCoefficient_codRestrict_evalAtChosenLinear (G := G) σ hσ
  have hcoord :
      D x₀ ∈
        V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex :=
    matrixCoefficient_codRestrict_fixedVector_mem_coordinateSubspace
      (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex) hbasis D
  by_cases hDx₀ : D x₀ = 0
  · refine ⟨0, ?_⟩
    simpa [E, x₀, hDx₀]
  · rcases
      matrixCoefficient_codRestrict_exists_range_preimage_of_firstCoordinate_orthogonal_zero
        (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex)
        hbasis (y := D x₀) (hy := hcoord) (hy0 := hDx₀) hfirst_zero with
      ⟨T, hT_range, hTx₀⟩
    rcases hT_range with ⟨ℓ, rfl⟩
    refine ⟨ℓ, ?_⟩
    simpa [E, x₀] using hTx₀

/-- Helper for Remark 4-4.3-1: the remaining source-faithful Proposition 8 input is that the
fixed-vector value of any intertwiner in the `σ`-isotypic summand already lies in the evaluated
coefficient range. The existential preimage statement is equivalent to this first-coordinate
membership formulation. -/
theorem matrixCoefficient_codRestrict_exists_range_preimage_of_fixedVector
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    ∃ T : σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),
      T ∈ LinearMap.range
          (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
            (G := G) σ hσ) ∧
        T (chosen_irreducible_vector (G := G) σ) =
          D (chosen_irreducible_vector (G := G) σ) := by
  let x₀ : W := chosen_irreducible_vector (G := G) σ
  let s : Set W := {x₀}
  have hs : LinearIndepOn ℂ id s := by
    simpa [s, x₀] using
      (linearIndepOn_singleton_iff (R := ℂ) (v := id) (i := x₀)).2
        (by simpa [x₀] using chosen_irreducible_vector_ne_zero (G := G) σ)
  let ι : Type v := hs.extend (Set.subset_univ s)
  letI : Fintype ι := Set.Finite.fintype (show Set.Finite (hs.extend (Set.subset_univ s)) by
    exact Set.toFinite _)
  let basis : Module.Basis ι ℂ W := Module.Basis.extend hs
  have hx₀_mem : x₀ ∈ hs.extend (Set.subset_univ s) := by
    exact hs.subset_extend (Set.subset_univ s) (by simp [s])
  let oneIndex : ι := ⟨x₀, hx₀_mem⟩
  have hbasis : basis oneIndex = x₀ := by
    simpa [basis, oneIndex] using Module.Basis.extend_apply_self hs oneIndex
  rw [matrixCoefficient_codRestrict_exists_range_preimage_of_fixedVector_iff_mem_evalRange]
  -- Route correction: the analytic projection/recovery work is complete. The main theorem now
  -- delegates only the final compact Proposition 8 vanishing step to the isolated helper above.
  exact
    matrixCoefficient_codRestrict_fixedVector_mem_evalRange_of_firstCoordinate_orthogonal_zero
      (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex)
      hbasis
      (matrixCoefficient_codRestrict_firstCoordinate_orthogonal_zero
        (G := G) (σ := σ) (hσ := hσ) (basis := basis) (oneIndex := oneIndex) hbasis)
      D

/-- Helper for Remark 4-4.3-1: the remaining source-faithful kernel bridge says that an
intertwiner in the `σ`-isotypic summand with vanishing recovered dual already vanishes on the
chosen irreducible source vector. -/
theorem matrixCoefficient_codRestrict_kernel_bridge
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ))
    (D : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (hΨD :
      (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) D = 0) :
    D (chosen_irreducible_vector (G := G) σ) = 0 := by
  -- Route correction: the analytic kernel step is complete. The bridge now reduces to the single
  -- compact Proposition 8 statement that `D x₀` lies in the evaluated coefficient-image range.
  exact
    matrixCoefficient_codRestrict_fixedVector_zero_of_exists_range_preimage
      (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
      (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
      (D := D) hΨD
      (matrixCoefficient_codRestrict_exists_range_preimage_of_fixedVector
        (G := G) (σ := σ) (hσ := hσ) (D := D))

/-- Helper for Remark 4-4.3-1: once the source-faithful kernel bridge is available, the analytic
recovery map `Ψ` is injective on the `σ`-isotypic intertwining space. -/
theorem matrixCoefficient_codRestrict_dualRecovery_injective
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (hJ_pos : ∀ x : W, x ≠ 0 → ∃ r : ℝ, 0 < r ∧ J x x = (r : ℂ)) :
    Function.Injective
      (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) := by
  intro D₁ D₂ hEq
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  let D :
      σ.IntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) :=
    D₁ - D₂
  have hΨD : Ψ D = 0 := by
    -- Route correction: reduce injectivity to the kernel case handled by the source bridge.
    rw [show D = D₁ - D₂ by rfl, LinearMap.map_sub, hEq, sub_self]
  have hDx₀ : D (chosen_irreducible_vector (G := G) σ) = 0 := by
    -- The bridge identifies the kernel of `Ψ` with vanishing on the chosen source vector.
    exact
      matrixCoefficient_codRestrict_kernel_bridge
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos) D hΨD
  have hDzero : D = 0 := by
    -- Once the chosen source vector vanishes, irreducibility forces the whole intertwiner to be
    -- zero.
    exact
      matrixCoefficient_codRestrict_zero_of_apply_chosen_irreducible_vector_zero
        (G := G) (σ := σ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
        (D := D) hDx₀
  exact sub_eq_zero.mp (by simpa [D] using hDzero)

/-- Helper for Remark 4-4.3-1: after corestricting to the canonical `σ`-isotypic summand of
`L²(G)`, the intertwining space is squeezed between the injective coefficient map `Φ : Wᵛ → H`
and the injective recovery map `Ψ : H → Wᵛ`. This reduces the multiplicity computation to the
single remaining source-faithful kernel bridge for `Ψ`. -/
theorem finrank_intertwiningMap_l2Regular_corestricted
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible] :
    Module.finrank ℂ
      (σ.IntertwiningMap ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) =
        Module.finrank ℂ W := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  have hΦ_inj : Function.Injective Φ :=
    matrixCoefficientIntertwining_l2Regular_codRestrictLinear_injective (G := G) σ hσ
  rcases averaged_invariant_toDual (G := G) σ hσ with ⟨J, hJ, hJ_herm, hJ_pos⟩
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  have hΨ_inj : Function.Injective Ψ := by
    -- The only remaining Peter-Weyl input is the kernel bridge packaged above.
    exact
      matrixCoefficient_codRestrict_dualRecovery_injective
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (hJ_pos := hJ_pos)
  letI :
      FiniteDimensional ℂ
        (σ.IntertwiningMap ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :=
    FiniteDimensional.of_injective Ψ hΨ_inj
  have hlower :
      Module.finrank ℂ (Module.Dual ℂ W) ≤
        Module.finrank ℂ
          (σ.IntertwiningMap ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :=
    LinearMap.finrank_le_finrank_of_injective (f := Φ) hΦ_inj
  have hupper :
      Module.finrank ℂ
          (σ.IntertwiningMap ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) ≤
        Module.finrank ℂ (Module.Dual ℂ W) :=
    LinearMap.finrank_le_finrank_of_injective (f := Ψ) hΨ_inj
  have hdual :
      Module.finrank ℂ (Module.Dual ℂ W) = Module.finrank ℂ W := by
    classical
    exact LinearEquiv.finrank_eq (Module.Free.chooseBasis ℂ W).toDualEquiv.symm
  -- Compare the lower and upper bounds after identifying `Wᵛ` with `W`.
  apply le_antisymm
  · exact hupper.trans hdual.le
  · exact hdual.symm.le.trans hlower

end PeterWeyl

end Representation
