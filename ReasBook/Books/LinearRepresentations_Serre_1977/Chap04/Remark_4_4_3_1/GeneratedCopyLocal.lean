import Serre.Chap04.Remark_4_4_3_1.GeneratedCopyAmbient
import Serre.Chap04.Remark_4_4_3_1.EvalSymmApply

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

theorem matrixCoefficient_codRestrict_evalSymm_mem_generated_copy
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hy : y ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hy0 : y ≠ 0) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
    let D : σ.IntertwiningMap τ :=
      (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
    ∀ x : W, D x ∈ (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
  let e :=
    ExplicitDecomposition.generatedSubrepresentationEquiv τ σ basis oneIndex x₁
      (by simpa [x₁] using hy0)
  let inclLin :
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule →ₗ[ℂ]
        (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
    (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule.subtype
  let incl :
      ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation).IntertwiningMap τ :=
    inclLin.intertwiningMap_of_isIntertwiningMap
      ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation) τ
      (fun g x ↦ by
        apply Subtype.ext
        rfl)
  let Dambient : σ.IntertwiningMap τ := incl.comp e.toIntertwiningMap
  let D : σ.IntertwiningMap τ :=
    (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
  have hD_eq : Dambient = D := by
    -- The canonical Exercise 2-2.7-2 inverse is exactly the ambient inclusion of the single
    -- generated copy `W(y)`.
    simpa [τ, x₁, e, inclLin, incl, Dambient, D] using
      matrixCoefficient_codRestrict_generated_copy_ambient_intertwiner_eq_evalSymm
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (y := y) (hy := hy) (hy0 := hy0)
  intro x
  have hmem :
      Dambient x ∈ (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule := by
    -- By construction the ambient comparison map factors through the generated copy `W(y)`.
    simpa [Dambient, incl, inclLin] using (e.toIntertwiningMap x).2
  -- Route correction: the unresolved step is no longer ambient transport. The canonical inverse
  -- already lands in `W(y)`, so only the copy-local coefficient realization remains.
  simpa [D] using (hD_eq ▸ hmem)

/-- Helper for Remark 4-4.3-1: source Proposition 8(c)/(d) should upgrade a nonzero
first-coordinate vector to an actual coefficient-image witness on the chosen source vector. This
isolates the single remaining copy-local bridge needed by the compact Peter-Weyl argument. -/
theorem
    matrixCoefficient_codRestrict_evalSymm_codRestrict_eq_generatedSubrepresentationHom
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hy : y ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hy0 : y ≠ 0) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
    let D : σ.IntertwiningMap τ :=
      (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
    let DcopyLin :
        W →ₗ[ℂ] (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule :=
      D.toLinearMap.codRestrict
        (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule
        (matrixCoefficient_codRestrict_evalSymm_mem_generated_copy
          (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
          (y := y) (hy := hy) (hy0 := hy0))
    let Dcopy :
        σ.IntertwiningMap (W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation :=
      DcopyLin.intertwiningMap_of_isIntertwiningMap σ
        (W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation
        (fun g x ↦ by
          apply Subtype.ext
          simpa [DcopyLin] using congr($(D.isIntertwining' g) x))
    Dcopy = ExplicitDecomposition.generatedSubrepresentationHom τ σ basis oneIndex x₁ := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
  let D : σ.IntertwiningMap τ :=
    (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
  let DcopyLin :
      W →ₗ[ℂ] (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule :=
    D.toLinearMap.codRestrict
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule
      (matrixCoefficient_codRestrict_evalSymm_mem_generated_copy
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (y := y) (hy := hy) (hy0 := hy0))
  let Dcopy :
      σ.IntertwiningMap (W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation :=
    DcopyLin.intertwiningMap_of_isIntertwiningMap σ
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation
      (fun g x ↦ by
        apply Subtype.ext
        simpa [DcopyLin] using congr($(D.isIntertwining' g) x))
  let inclLin :
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule →ₗ[ℂ]
        (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule :=
    (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule.subtype
  let incl :
      ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation).IntertwiningMap τ :=
    inclLin.intertwiningMap_of_isIntertwiningMap
      ((W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation) τ
      (fun g x ↦ by
        apply Subtype.ext
        rfl)
  have hcomp_left : incl.comp Dcopy = D := by
    -- Codomain restriction followed by the inclusion recovers the original canonical inverse.
    apply Representation.IntertwiningMap.ext
    intro x
    apply Subtype.ext
    rfl
  have hcomp_right :
      incl.comp (ExplicitDecomposition.generatedSubrepresentationHom τ σ basis oneIndex x₁) = D := by
    -- The ambient generated-copy inclusion is already the canonical Exercise 2-2.7-2 inverse.
    simpa [D, incl, inclLin, x₁,
      ExplicitDecomposition.generatedSubrepresentationEquiv,
      ExplicitDecomposition.generatedSubrepresentationHom] using
      matrixCoefficient_codRestrict_generated_copy_ambient_intertwiner_eq_evalSymm
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (y := y) (hy := hy) (hy0 := hy0)
  -- Compare the two maps after re-including them into the ambient isotypic summand.
  apply Representation.IntertwiningMap.ext
  intro x
  apply Subtype.ext
  exact congrArg Subtype.val <|
    congrArg (fun f : σ.IntertwiningMap τ ↦ f x) (hcomp_left.trans hcomp_right.symm)

/-- Helper for Remark 4-4.3-1: if `y` already lies in the distinguished first-coordinate copy
`V_{i,1}`, then the cyclic subrepresentation generated by `y` is exactly the single source copy
`W(y)`. This is the Exercise 2-2.7.4 collapse specialized to the compact `L²` setting. -/
theorem
    matrixCoefficient_codRestrict_first_coordinate_cyclicSubrepresentation_eq_generated_copy
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (hbasis : basis oneIndex = chosen_irreducible_vector (G := G) σ)
    (y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hy : y ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (hy0 : y ≠ 0) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
    V⟮τ⟯ y = W⟮τ,σ,basis,oneIndex⟯ x₁ := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
  let D : σ.IntertwiningMap τ :=
    (ExplicitDecomposition.intertwiningMapEvaluationEquiv τ σ basis oneIndex).symm x₁
  let DcopyLin :
      W →ₗ[ℂ] (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule :=
    D.toLinearMap.codRestrict
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule
      (matrixCoefficient_codRestrict_evalSymm_mem_generated_copy
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (y := y) (hy := hy) (hy0 := hy0))
  let Dcopy :
      σ.IntertwiningMap (W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation :=
    DcopyLin.intertwiningMap_of_isIntertwiningMap σ
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toRepresentation
      (fun g x ↦ by
        apply Subtype.ext
        simpa [DcopyLin] using congr($(D.isIntertwining' g) x))
  have hDx₀ :
      D (chosen_irreducible_vector (G := G) σ) = y := by
    -- The canonical inverse recovers the original first-coordinate vector on the chosen source
    -- generator.
    simpa [D, τ, x₁] using
      matrixCoefficient_codRestrict_evalSymm_apply_chosen
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (hbasis := hbasis) (y := y) (hy := hy)
  have hDcopy_eq :
      Dcopy = ExplicitDecomposition.generatedSubrepresentationHom τ σ basis oneIndex x₁ := by
    -- Reuse the codomain-restricted identification of the canonical inverse with the source map.
    simpa [D] using
      matrixCoefficient_codRestrict_evalSymm_codRestrict_eq_generatedSubrepresentationHom
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (y := y) (hy := hy) (hy0 := hy0)
  have hy_range : y ∈ D.range.toSubmodule := by
    -- The canonical inverse evaluates to `y` on the chosen irreducible source vector.
    refine LinearMap.mem_range.mpr ?_
    exact ⟨chosen_irreducible_vector (G := G) σ, hDx₀⟩
  have hcyc_le_range :
      (V⟮τ⟯ y).toSubmodule ≤ D.range.toSubmodule := by
    -- Any stable subrepresentation containing `y` contains the cyclic representation `V(y)`.
    exact cyclicSubrepresentation_le_of_mem τ D.range hy_range
  have hrange_le_copy :
      D.range.toSubmodule ≤ (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule := by
    intro z hz
    rcases LinearMap.mem_range.mp hz with ⟨w, rfl⟩
    -- The canonical inverse already lands in the single generated copy `W(y)`.
    simpa [D, τ, x₁] using
      matrixCoefficient_codRestrict_evalSymm_mem_generated_copy
        (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
        (y := y) (hy := hy) (hy0 := hy0) w
  have hcopy_le_cyc :
      (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule ≤ (V⟮τ⟯ y).toSubmodule := by
    intro z hz
    let zz : (W⟮τ,σ,basis,oneIndex⟯ x₁).toSubmodule := ⟨z, hz⟩
    have hsurj :
        Function.Surjective
          (ExplicitDecomposition.generatedSubrepresentationHom τ σ basis oneIndex x₁) := by
      -- The source owner map is just the canonical range restriction of the coordinate family.
      simpa [ExplicitDecomposition.generatedSubrepresentationHom] using
        (LinearMap.surjective_rangeRestrict
          (ExplicitDecomposition.coordinateFamilyHom τ σ basis oneIndex x₁).toLinearMap)
    rcases hsurj zz with ⟨w, hw⟩
    have hDw_mem :
        D w ∈ (V⟮τ⟯ y).toSubmodule := by
      -- The chosen source vector generates all of `σ`, so the whole range of `D` lies in `V(y)`.
      simpa [hDx₀] using
        intertwiningMap_range_le_cyclicSubrepresentation_of_apply_chosen
          (G := G) (τ := τ) (σ := σ) D
          (LinearMap.mem_range.mpr ⟨w, rfl⟩)
    have hDw_eq : Dcopy w = zz := by
      -- Rewrite the surjective source map as the codomain-restricted canonical inverse.
      simpa [hDcopy_eq] using hw
    have hz_eq : D w = z := by
      simpa [Dcopy, DcopyLin] using congrArg Subtype.val hDw_eq
    exact hz_eq ▸ hDw_mem
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · exact le_trans hcyc_le_range hrange_le_copy
  · exact hcopy_le_cyc

/-- Helper for Remark 4-4.3-1: on the single generated copy `W(y)`, applying the reverse
matrix-unit `p_{1η}` to a vector from the coordinate family extracts the `η`-th source-basis
coefficient times the generating vector `y`. This is the copy-local source computation from
Exercise 2-2.7-4 specialized to the compact `L²` model. -/
theorem
    matrixCoefficient_codRestrict_reverse_matrixUnit_apply_generated_copy
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex η : ι)
    (y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hy : y ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (w : W) :
    let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
    p⟮τ,σ,basis⟯ oneIndex η
        (ExplicitDecomposition.coordinateFamilyMap τ σ basis oneIndex x₁ w) =
      (basis.repr w η) • y := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
  have hx₁_fix : p⟮τ,σ,basis⟯ oneIndex oneIndex (x₁ : τ.asModule) = x₁ := by
    -- Because `x₁` already lies in the first-coordinate copy, the diagonal matrix unit fixes it.
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp x₁.2
    calc
      p⟮τ,σ,basis⟯ oneIndex oneIndex (x₁ : τ.asModule)
          = p⟮τ,σ,basis⟯ oneIndex oneIndex (p⟮τ,σ,basis⟯ oneIndex oneIndex u) := by
              rw [hu]
      _ = p⟮τ,σ,basis⟯ oneIndex oneIndex u := by
            simpa [LinearMap.comp_apply] using
              congrArg (fun f : Module.End ℂ τ.asModule ↦ f u)
                (ExplicitDecomposition.matrixUnit_comp τ σ basis
                  oneIndex oneIndex oneIndex oneIndex rfl)
      _ = x₁ := hu
  have hw_expand :
      ExplicitDecomposition.coordinateFamilyMap τ σ basis oneIndex x₁ w =
        ∑ α : ι,
          (basis.repr w α) •
            ExplicitDecomposition.coordinateVector τ σ basis oneIndex x₁ α := by
    -- Expand the source vector `w` in the fixed basis so the reverse matrix unit can isolate
    -- one coefficient at a time.
    simpa [ExplicitDecomposition.coordinateFamilyMap] using
      (basis.constr_apply_fintype ℂ
        (ExplicitDecomposition.coordinateVector τ σ basis oneIndex x₁) w)
  rw [hw_expand]
  calc
    p⟮τ,σ,basis⟯ oneIndex η
        (∑ α : ι,
          (basis.repr w α) •
            ExplicitDecomposition.coordinateVector τ σ basis oneIndex x₁ α)
        = ∑ α : ι,
            (basis.repr w α) •
              p⟮τ,σ,basis⟯ oneIndex η
                (ExplicitDecomposition.coordinateVector τ σ basis oneIndex x₁ α) := by
                  simp [map_sum, map_smul]
    _ = ∑ α : ι,
          (basis.repr w α) • ↑(if η = α then x₁ else 0) := by
            apply Finset.sum_congr rfl
            intro α hα
            by_cases hηα : η = α
            · subst α
              calc
                p⟮τ,σ,basis⟯ oneIndex η
                    (ExplicitDecomposition.coordinateVector τ σ basis oneIndex x₁ η)
                    = p⟮τ,σ,basis⟯ oneIndex oneIndex (x₁ : τ.asModule) := by
                        simpa [ExplicitDecomposition.coordinateVector, LinearMap.comp_apply] using
                          congrArg (fun f : Module.End ℂ τ.asModule ↦ f x₁)
                            (ExplicitDecomposition.matrixUnit_comp τ σ basis
                              oneIndex η η oneIndex rfl)
                _ = x₁ := hx₁_fix
                _ = if η = η then x₁ else 0 := by simp
            · simpa [ExplicitDecomposition.coordinateVector, hηα, LinearMap.comp_apply] using
                congrArg (fun f : Module.End ℂ τ.asModule ↦ f x₁)
                  (ExplicitDecomposition.matrixUnit_comp_eq_zero_of_ne
                    τ σ basis oneIndex η α oneIndex hηα)
    _ = ∑ α : ι,
          if η = α then (basis.repr w α) • y else 0 := by
            apply Finset.sum_congr rfl
            intro α hα
            by_cases hηα : η = α <;> simp [hηα, x₁]
    _ = (basis.repr w η) • y := by
          simp

/-- Helper for Remark 4-4.3-1: inside the single generated copy `W(y)`, the distinguished
first-coordinate slice is the line spanned by `y`. This packages the source fact that once the
cyclic representation has collapsed to one copy, there is only one surviving first-coordinate
generator. -/
theorem matrixCoefficient_codRestrict_first_coordinate_mem_smul_generated_vector
    {ι : Type v} [Fintype ι]
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (basis : Module.Basis ι ℂ W) (oneIndex : ι)
    (y : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hy : y ∈
      V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex)
    (z : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (hzW :
      z ∈
        (W⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis,
          oneIndex⟯ ⟨y, hy⟩).toSubmodule)
    (hz1 :
      z ∈
        V⟮((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation),σ,basis⟯ oneIndex) :
    ∃ c : ℂ, z = c • y := by
  let τ := ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
  let x₁ : V⟮τ,σ,basis⟯ oneIndex := ⟨y, hy⟩
  rcases LinearMap.mem_range.mp hzW with ⟨w, rfl⟩
  have hz_fix :
      ExplicitDecomposition.coordinateFamilyMap τ σ basis oneIndex x₁ w =
        p⟮τ,σ,basis⟯ oneIndex oneIndex
          (ExplicitDecomposition.coordinateFamilyMap τ σ basis oneIndex x₁ w) := by
    -- Membership in the first-coordinate copy means the diagonal matrix unit acts as the identity.
    rcases LinearMap.mem_range.mp hz1 with ⟨u, hu⟩
    calc
      ExplicitDecomposition.coordinateFamilyMap τ σ basis oneIndex x₁ w
          = p⟮τ,σ,basis⟯ oneIndex oneIndex u := hu.symm
      _ = p⟮τ,σ,basis⟯ oneIndex oneIndex
            (p⟮τ,σ,basis⟯ oneIndex oneIndex u) := by
              symm
              simpa [LinearMap.comp_apply] using
                congrArg (fun f : Module.End ℂ τ.asModule ↦ f u)
                  (ExplicitDecomposition.matrixUnit_comp τ σ basis
                    oneIndex oneIndex oneIndex oneIndex rfl)
      _ = p⟮τ,σ,basis⟯ oneIndex oneIndex
            (ExplicitDecomposition.coordinateFamilyMap τ σ basis oneIndex x₁ w) := by
              rw [hu]
  refine ⟨basis.repr w oneIndex, ?_⟩
  calc
    ExplicitDecomposition.coordinateFamilyMap τ σ basis oneIndex x₁ w
        = p⟮τ,σ,basis⟯ oneIndex oneIndex
            (ExplicitDecomposition.coordinateFamilyMap τ σ basis oneIndex x₁ w) := hz_fix
    _ = (basis.repr w oneIndex) • y := by
          simpa [τ, x₁] using
            matrixCoefficient_codRestrict_reverse_matrixUnit_apply_generated_copy
              (G := G) (σ := σ) (basis := basis) (oneIndex := oneIndex)
              (η := oneIndex) (y := y) (hy := hy) (w := w)

/-- Helper for Remark 4-4.3-1: once an ambient intertwiner factors through the single generated
copy `W(y)`, its evaluation at the chosen irreducible vector already determines it up to scalar.
This packages the uniqueness half of the source copy argument, so the only missing step is to
produce one nonzero coefficient intertwiner whose image lies in `W(y)`. -/

end PeterWeyl

end Representation
