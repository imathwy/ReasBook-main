import Mathlib
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Manifold.Instances.Sphere
import SmoothManifolds_Lee_2012.Chap01.Sec01.Example_1_8
import SmoothManifolds_Lee_2012.Chap02.Sec02_08.Proposition_2_12
import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Example_4_35
import SmoothManifolds_Lee_2012.Chap07.Sec07_46.Proposition_7_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Definition_7_49_extra_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_51.Example_7_32
import SmoothManifolds_Lee_2012.Chap07.Sec07_52.Definition_7_52_extra_1

open scoped Matrix Torus Manifold ContDiff
open Matrix.GeneralLinearGroup

noncomputable section

private def linearEndRestrictScalars
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    Module.End K (ι → K) →* Module.End ℝ (ι → K) where
  toFun f := f.restrictScalars ℝ
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def matrixToLinearEndUnits
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    GL ι K →* LinearMap.GeneralLinearGroup ℝ (ι → K) :=
  (Units.map linearEndRestrictScalars).comp toLin.toMonoidHom

private theorem matrixToLinearEndUnits_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    Function.Injective (fun A : GL ι K ↦ matrixToLinearEndUnits A) := by
  intro A B hAB
  apply toLin.injective
  apply Units.ext
  exact LinearMap.restrictScalars_injective ℝ <|
    congrArg (fun f : LinearMap.GeneralLinearGroup ℝ (ι → K) ↦ (f : Module.End ℝ (ι → K))) hAB

private noncomputable def linearEndToContinuousEndUnits
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    LinearMap.GeneralLinearGroup ℝ (ι → K) →* ((ι → K) →L[ℝ] (ι → K))ˣ :=
  (Units.mapEquiv (Module.End.toContinuousLinearMap (ι → K)).toMulEquiv).toMonoidHom

private noncomputable def matrixToContinuousEndUnits
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    GL ι K →* ((ι → K) →L[ℝ] (ι → K))ˣ :=
  linearEndToContinuousEndUnits.comp matrixToLinearEndUnits

private theorem matrixToContinuousEndUnits_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    Function.Injective (fun A : GL ι K ↦ matrixToContinuousEndUnits A) := by
  intro A B hAB
  exact matrixToLinearEndUnits_injective <|
    (Units.mapEquiv (Module.End.toContinuousLinearMap (ι → K)).toMulEquiv).injective hAB

private noncomputable def matrixLieGroupRepresentation
    {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    {I : ModelWithCorners ℝ E H} [LieGroup I ∞ G]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K]
    (ρ : G →* GL ι K) :
    LieGroupRepresentation I G (ι → K) where
  toMonoidHom := matrixToContinuousEndUnits.comp ρ
  contMDiff_toFun := by
    sorry

private theorem matrixLieGroupRepresentation_isFaithful
    {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    {I : ModelWithCorners ℝ E H} [LieGroup I ∞ G]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K]
    {ρ : G →* GL ι K} (hρ : Function.Injective ρ) :
    LieGroupRepresentation.IsFaithful
      ((matrixLieGroupRepresentation ρ : LieGroupRepresentation I G (ι → K))) := by
  rw [LieGroupRepresentation.isFaithful_iff_injective]
  intro g h hgh
  exact hρ <| matrixToContinuousEndUnits_injective hgh

private abbrev RealSubgroup (n : ℕ)
    [ChartedSpace (Fin n → Fin n → ℝ) (GL (Fin n) ℝ)]
    [LieGroup (𝓘(ℝ, Fin n → Fin n → ℝ)) ∞ (GL (Fin n) ℝ)] :=
  @LieSubgroup ℝ _ (Fin n → Fin n → ℝ) _ _ (Fin n → Fin n → ℝ) _ (GL (Fin n) ℝ) _ _ _
    (𝓘(ℝ, Fin n → Fin n → ℝ))

private abbrev ComplexSubgroup (n : ℕ)
    [ChartedSpace (Fin n → Fin n → ℂ) (GL (Fin n) ℂ)]
    [LieGroup (𝓘(ℝ, Fin n → Fin n → ℂ)) ∞ (GL (Fin n) ℂ)] :=
  @LieSubgroup ℝ _ (Fin n → Fin n → ℂ) _ _ (Fin n → Fin n → ℂ) _ (GL (Fin n) ℂ) _ _ _
    (𝓘(ℝ, Fin n → Fin n → ℂ))

private instance multiplicativeChartedSpace
    {H : Type*} {E : Type*} [TopologicalSpace H] [TopologicalSpace E] [ChartedSpace H E] :
    ChartedSpace H (Multiplicative E) := by
  simpa [Multiplicative] using (inferInstance : ChartedSpace H E)

private instance multiplicativeIsManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsManifold (𝓘(ℝ, E)) ∞ (Multiplicative E) := by
  simpa [Multiplicative] using (inferInstance : IsManifold (𝓘(ℝ, E)) ∞ E)

private instance multiplicativeLieGroup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    LieGroup (𝓘(ℝ, E)) ∞ (Multiplicative E) :=
  lieGroup_of_contMDiff_mul_inv <| by
    simpa [Multiplicative, div_eq_mul_inv, sub_eq_add_neg] using
      (contMDiff_fst.sub contMDiff_snd :
        ContMDiff ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) ∞
          fun p : E × E ↦ p.1 - p.2)

section SubgroupExamples

/-- Example 7.36 (1): for a Lie subgroup of `GL(n, ℝ)`, the inclusion map is a faithful defining
representation. -/
noncomputable def real_subgroup_defining_representation (n : ℕ)
    [ChartedSpace (Fin n → Fin n → ℝ) (GL (Fin n) ℝ)]
    [LieGroup (𝓘(ℝ, Fin n → Fin n → ℝ)) ∞ (GL (Fin n) ℝ)]
    (G : RealSubgroup n) :
    LieGroupRepresentation (modelWithCornersSelf ℝ G.ModelSpace) G (Fin n → ℝ) :=
  matrixLieGroupRepresentation G.carrier.subtype

/-- Example 7.36 (1): the defining representation of a Lie subgroup of `GL(n, ℝ)` is faithful. -/
theorem real_subgroup_defining_representation_faithful (n : ℕ)
    [ChartedSpace (Fin n → Fin n → ℝ) (GL (Fin n) ℝ)]
    [LieGroup (𝓘(ℝ, Fin n → Fin n → ℝ)) ∞ (GL (Fin n) ℝ)]
    (G : RealSubgroup n) :
    LieGroupRepresentation.IsFaithful (real_subgroup_defining_representation n G) :=
  matrixLieGroupRepresentation_isFaithful G.carrier.subtype_injective

/-- Example 7.36 (2): for a Lie subgroup of `GL(n, ℂ)`, the inclusion map is a faithful defining
representation. Here the representation is viewed on `ℂⁿ` as a real vector space. -/
noncomputable def complex_subgroup_defining_representation (n : ℕ)
    [ChartedSpace (Fin n → Fin n → ℂ) (GL (Fin n) ℂ)]
    [LieGroup (𝓘(ℝ, Fin n → Fin n → ℂ)) ∞ (GL (Fin n) ℂ)]
    (G : ComplexSubgroup n) :
    LieGroupRepresentation (modelWithCornersSelf ℝ G.ModelSpace) G (Fin n → ℂ) :=
  matrixLieGroupRepresentation G.carrier.subtype

/-- Example 7.36 (2): the defining representation of a Lie subgroup of `GL(n, ℂ)` is faithful. -/
theorem complex_subgroup_defining_representation_faithful (n : ℕ)
    [ChartedSpace (Fin n → Fin n → ℂ) (GL (Fin n) ℂ)]
    [LieGroup (𝓘(ℝ, Fin n → Fin n → ℂ)) ∞ (GL (Fin n) ℂ)]
    (G : ComplexSubgroup n) :
    LieGroupRepresentation.IsFaithful (complex_subgroup_defining_representation n G) :=
  matrixLieGroupRepresentation_isFaithful G.carrier.subtype_injective

end SubgroupExamples

section CircleExample

private noncomputable def circle_defining_matrix_hom : Circle →* GL (Fin 1) ℂ :=
  (scalar (Fin 1)).comp Circle.toUnits

/-- The circle group's defining representation, viewed on `ℂ` as a real vector space. -/
noncomputable def circle_defining_representation :
    LieGroupRepresentation (𝓡 1) Circle (Fin 1 → ℂ) :=
  matrixLieGroupRepresentation circle_defining_matrix_hom

/-- Example 7.36 (3): the inclusion `S¹ ↪ ℂˣ ≃ GL(1, ℂ)` gives a faithful smooth representation. -/
theorem circle_defining_representation_faithful :
    LieGroupRepresentation.IsFaithful circle_defining_representation := by
  exact matrixLieGroupRepresentation_isFaithful (by
    intro z w hzw
    sorry)

end CircleExample

section TorusExample

variable (n : ℕ)

private abbrev TnModel (n : ℕ) := ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1)
private abbrev TnProdModel (n : ℕ) := (TnModel n).prod (TnModel n)

local instance torusIsManifold : IsManifold (TnModel n) ∞ (𝕋^{n}) := by
  infer_instance
local instance torusLieGroup : LieGroup (TnModel n) ∞ (𝕋^{n}) := by
  change LieGroup (TnModel n) ∞ (Fin n → Circle)
  exact lieGroup_of_contMDiff_mul_inv <| by
    rw [contMDiff_pi_iff]
    intro i
    have hfstPi :
        ContMDiff (TnProdModel n) (TnModel n) ∞
          (Prod.fst : (Fin n → Circle) × (Fin n → Circle) → Fin n → Circle) :=
      contMDiff_fst
    have hsndPi :
        ContMDiff (TnProdModel n) (TnModel n) ∞
          (Prod.snd : (Fin n → Circle) × (Fin n → Circle) → Fin n → Circle) :=
      contMDiff_snd
    have hfst : ContMDiff (TnProdModel n) (𝓡 1) ∞
        (fun p : (Fin n → Circle) × (Fin n → Circle) ↦ p.1 i) :=
      (contMDiff_pi_iff.mp hfstPi) i
    have hsnd : ContMDiff (TnProdModel n) (𝓡 1) ∞
        (fun p : (Fin n → Circle) × (Fin n → Circle) ↦ p.2 i) :=
      (contMDiff_pi_iff.mp hsndPi) i
    simpa [div_eq_mul_inv] using hfst.div hsnd

/-- The diagonal complex matrix determined by an `n`-torus point. -/
def torus_diagonal_matrix (z : 𝕋^{n}) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i ↦ (z i : ℂ)

/-- The diagonal torus matrix as an element of `GL(n, ℂ)`. -/
noncomputable def torus_diagonal_gl (z : 𝕋^{n}) : GL (Fin n) ℂ :=
  mkOfDetNeZero (torus_diagonal_matrix n z) (by
    sorry)

private noncomputable def torus_diagonal_matrix_hom : 𝕋^{n} →* GL (Fin n) ℂ where
  toFun := torus_diagonal_gl n
  map_one' := by
    sorry
  map_mul' := by
    intro z w
    sorry

/-- The standard diagonal representation of the complex `n`-torus, viewed on `ℂⁿ` as a real
vector space. -/
noncomputable def torus_diagonal_representation :
    LieGroupRepresentation (TnModel n) (𝕋^{n}) (Fin n → ℂ) :=
  matrixLieGroupRepresentation (torus_diagonal_matrix_hom n)

/-- Example 7.36 (4): the diagonal map `𝕋ⁿ → GL(n, ℂ)` is faithful. -/
theorem torus_diagonal_representation_faithful :
    LieGroupRepresentation.IsFaithful (torus_diagonal_representation n) := by
  exact matrixLieGroupRepresentation_isFaithful (by
    intro z w hzw
    sorry)

end TorusExample

section AdditiveExamples

variable (n : ℕ)

/-- The upper-triangular affine matrix used to represent the additive group `ℝ^n`. -/
def additive_upper_triangular_matrix (x : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (fun i _ ↦ x i) 0 1

/-- The upper-triangular affine matrix as an element of `GL(n+1, ℝ)`. -/
noncomputable def additive_upper_triangular_gl
    (x : Multiplicative (Fin n → ℝ)) : GL (Fin n ⊕ Fin 1) ℝ :=
  mkOfDetNeZero (additive_upper_triangular_matrix n (Multiplicative.toAdd x)) (by
    sorry)

private noncomputable def additive_upper_triangular_matrix_hom :
    Multiplicative (Fin n → ℝ) →* GL (Fin n ⊕ Fin 1) ℝ where
  toFun := additive_upper_triangular_gl n
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    sorry

/-- The affine upper-triangular block map, viewed as a smooth representation of `ℝⁿ`. -/
noncomputable def additive_upper_triangular_representation :
    LieGroupRepresentation (𝓘(ℝ, Fin n → ℝ)) (Multiplicative (Fin n → ℝ))
      (Fin n ⊕ Fin 1 → ℝ) :=
  matrixLieGroupRepresentation (additive_upper_triangular_matrix_hom n)

/-- Example 7.36 (5): the affine upper-triangular block map gives a faithful representation of the
additive group `ℝ^n`. -/
theorem additive_upper_triangular_representation_faithful :
    LieGroupRepresentation.IsFaithful (additive_upper_triangular_representation n) := by
  exact matrixLieGroupRepresentation_isFaithful (by
    intro x y hxy
    sorry)

/-- The positive diagonal matrix with entries `exp xᵢ`. -/
def additive_exp_diagonal_matrix (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i ↦ Real.exp (x i)

/-- The positive diagonal matrix as an element of `GL(n, ℝ)`. -/
noncomputable def additive_exp_diagonal_gl
    (x : Multiplicative (Fin n → ℝ)) : GL (Fin n) ℝ :=
  mkOfDetNeZero (additive_exp_diagonal_matrix n (Multiplicative.toAdd x)) (by
    sorry)

private noncomputable def additive_exp_diagonal_matrix_hom :
    Multiplicative (Fin n → ℝ) →* GL (Fin n) ℝ where
  toFun := additive_exp_diagonal_gl n
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    sorry

/-- The faithful exponential diagonal representation of the additive group `ℝ^n`. -/
noncomputable def additive_exp_diagonal_representation :
    LieGroupRepresentation (𝓘(ℝ, Fin n → ℝ)) (Multiplicative (Fin n → ℝ)) (Fin n → ℝ) :=
  matrixLieGroupRepresentation (additive_exp_diagonal_matrix_hom n)

/-- Example 7.36 (6): the diagonal matrix with entries `exp xᵢ` gives a faithful representation of
the additive group `ℝ^n`. -/
theorem additive_exp_diagonal_representation_faithful :
    LieGroupRepresentation.IsFaithful (additive_exp_diagonal_representation n) := by
  exact matrixLieGroupRepresentation_isFaithful (by
    intro x y hxy
    sorry)

/-- The diagonal unitary matrix with entries `exp (2π i xᵢ)`. -/
def unitary_character_diagonal_matrix (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i ↦ Complex.exp ((x i : ℂ) * (2 * Real.pi * Complex.I))

/-- The diagonal unitary matrix as an element of `GL(n, ℂ)`. -/
noncomputable def unitary_character_diagonal_gl
    (x : Multiplicative (Fin n → ℝ)) : GL (Fin n) ℂ :=
  mkOfDetNeZero (unitary_character_diagonal_matrix n (Multiplicative.toAdd x)) (by
    sorry)

private noncomputable def unitary_character_diagonal_matrix_hom :
    Multiplicative (Fin n → ℝ) →* GL (Fin n) ℂ where
  toFun := unitary_character_diagonal_gl n
  map_one' := by
    sorry
  map_mul' := by
    intro x y
    sorry

/-- The diagonal unitary representation of the additive group `ℝ^n`, viewed on `ℂⁿ` as a real
vector space. -/
noncomputable def unitary_character_diagonal_representation :
    LieGroupRepresentation (𝓘(ℝ, Fin n → ℝ)) (Multiplicative (Fin n → ℝ)) (Fin n → ℂ) :=
  matrixLieGroupRepresentation (unitary_character_diagonal_matrix_hom n)

/-- Example 7.36 (7): the diagonal map with entries `exp (2π i xᵢ)` is not faithful; its kernel is
the integer lattice `ℤ^n`, encoded as coordinatewise integrality. -/
theorem unitary_character_diagonal_representation_eq_one_iff
    (x : Multiplicative (Fin n → ℝ)) :
    unitary_character_diagonal_representation n x = 1 ↔
      ∀ i : Fin n, ∃ m : ℤ, Multiplicative.toAdd x i = (m : ℝ) := by
  sorry

end AdditiveExamples

section EuclideanGroupExample

variable (n : ℕ)
variable {H : Type*} [TopologicalSpace H]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace (euclidean_group n)] [ChartedSpace H (euclidean_group n)]
variable [LieGroup I ∞ (euclidean_group n)]

/-- The block matrix representing an element of the Euclidean group. -/
def euclidean_group_block_matrix (g : euclidean_group n) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks (g.2 : Matrix (Fin n) (Fin n) ℝ)
    (fun i _ ↦ g.1 i) 0 1

/-- The Euclidean-group block matrix as an element of `GL(n+1, ℝ)`. -/
noncomputable def euclidean_group_block_gl (g : euclidean_group n) :
    GL (Fin n ⊕ Fin 1) ℝ :=
  mkOfDetNeZero (euclidean_group_block_matrix n g) (by
    sorry)

private noncomputable def euclidean_group_block_matrix_hom :
    euclidean_group n →* GL (Fin n ⊕ Fin 1) ℝ where
  toFun := euclidean_group_block_gl n
  map_one' := by
    sorry
  map_mul' := by
    intro g h
    sorry

/-- The affine block representation of the Euclidean group. -/
noncomputable def euclidean_group_block_representation :
    LieGroupRepresentation I (euclidean_group n) (Fin n ⊕ Fin 1 → ℝ) :=
  matrixLieGroupRepresentation (euclidean_group_block_matrix_hom n)

/-- Example 7.36 (8): the Euclidean group admits a faithful block-matrix representation. -/
theorem euclidean_group_block_representation_faithful :
    LieGroupRepresentation.IsFaithful
      (show LieGroupRepresentation I (euclidean_group n) (Fin n ⊕ Fin 1 → ℝ) from
        euclidean_group_block_representation n) := by
  exact matrixLieGroupRepresentation_isFaithful (by
    intro g h hgh
    sorry)

end EuclideanGroupExample
