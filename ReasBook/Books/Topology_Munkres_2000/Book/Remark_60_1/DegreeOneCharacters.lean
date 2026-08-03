module

public import Topology_Munkres_2000.Book.Remark_60_1.CoefficientBockstein

public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory

/-- Helper for Remark 60.1: degree zero is the predecessor of degree one in a
cochain complex indexed by the natural numbers. -/
lemma singularCochain_prev_one :
    (ComplexShape.up ℕ).prev 1 = 0 := by
  -- Normalize the predecessor used by the degree-one short-complex projection.
  simp

/-- Helper for Remark 60.1: degree two is the successor of degree one in a
cochain complex indexed by the natural numbers. -/
lemma singularCochain_next_one :
    (ComplexShape.up ℕ).next 1 = 2 := by
  -- Normalize the successor used by the degree-one short-complex projection.
  simp

/-- Helper for Remark 60.1: the degree-one short-complex projection of the
coefficient-valued singular cochain complex. -/
abbrev degreeOneSingularCochainShortComplex
    (X : TopCat) (M : ModuleCat ℤ) : ShortComplex (ModuleCat ℤ) :=
  (singularCochainComplexWithCoefficients X M).sc' 0 1 2

/-- Helper for Remark 60.1: normalize abstract degree-one cohomology to the
explicit quotient of cocycles by coboundaries. -/
noncomputable def cohomologyOneNormalization
    (X : TopCat) (M : ModuleCat ℤ) :
    SingularCohomologyWithCoefficients X M 1 ≃ₗ[ℤ]
      (degreeOneSingularCochainShortComplex X M).moduleCatLeftHomologyData.H :=
  ((singularCochainComplexWithCoefficients X M).homologyIsoSc' 0 1 2
      singularCochain_prev_one singularCochain_next_one).toLinearEquiv.trans
    (degreeOneSingularCochainShortComplex X M).moduleCatHomologyIso.toLinearEquiv

/-- Helper for Remark 60.1: evaluation of coefficient-valued cochains at a
fixed chain preserves addition. -/
lemma singularCochainEvaluation_map_add
    (X : TopCat) (M : ModuleCat ℤ)
    (z : (integralSingularChainComplex X).X 1)
    (φ ψ : singularCochainGroupWithCoefficients X M 1) :
    (φ + ψ) z = φ z + ψ z := by
  -- Addition of linear maps is evaluated pointwise.
  exact LinearMap.add_apply φ ψ z

/-- Helper for Remark 60.1: evaluation at a fixed singular one-chain as an
additive homomorphism on coefficient-valued one-cochains. -/
def singularCochainEvaluationAddHom
    (X : TopCat) (M : ModuleCat ℤ)
    (z : (integralSingularChainComplex X).X 1) :
    singularCochainGroupWithCoefficients X M 1 →+ M :=
  { toFun := fun φ ↦ φ z
    map_zero' := rfl
    map_add' := singularCochainEvaluation_map_add X M z }

/-- Helper for Remark 60.1: evaluation respects the stored integral module
structures on a cochain group and its coefficient module. -/
lemma singularCochainEvaluation_map_smul
    (X : TopCat) (M : ModuleCat ℤ)
    (z : (integralSingularChainComplex X).X 1)
    (c : ℤ) (φ : singularCochainGroupWithCoefficients X M 1) :
    (singularCochainGroupWithCoefficients X M 1).isModule.smul c φ z =
      M.isModule.smul c (φ z) := by
  -- Every integral module action is the canonical repeated-addition action.
  rw [int_smul_eq_zsmul (singularCochainGroupWithCoefficients X M 1).isModule,
    int_smul_eq_zsmul M.isModule]
  exact (singularCochainEvaluationAddHom X M z).map_zsmul c φ

/-- Helper for Remark 60.1: evaluation at a fixed singular one-chain as a
linear map on coefficient-valued one-cochains. -/
def singularCochainEvaluation
    (X : TopCat) (M : ModuleCat ℤ)
    (z : (integralSingularChainComplex X).X 1) :
    singularCochainGroupWithCoefficients X M 1 →ₗ[ℤ] M :=
  { toFun := fun φ ↦ φ z
    map_add' := singularCochainEvaluation_map_add X M z
    map_smul' := singularCochainEvaluation_map_smul X M z }

/-- Helper for Remark 60.1: evaluation on a cycle kills every degree-one
coboundary. -/
lemma cochainEvaluationOnCycle_vanishesOnCoboundaries
    (X : TopCat) (M : ModuleCat ℤ)
    (z : (integralSingularChainComplex X).X 1)
    (hz : ((integralSingularChainComplex X).d 1 0).hom z = 0) :
    LinearMap.range
        ((singularCochainComplexWithCoefficients X M).sc' 0 1 2).moduleCatToCycles ≤
      LinearMap.ker
        ((singularCochainEvaluation X M z).comp
          ((LinearMap.ker
            ((singularCochainComplexWithCoefficients X M).sc' 0 1 2).g.hom).subtype :
              LinearMap.ker
                  ((singularCochainComplexWithCoefficients X M).sc' 0 1 2).g.hom →ₗ[ℤ]
                singularCochainGroupWithCoefficients X M 1)) := by
  -- A coboundary evaluates on `z` by first applying the chain boundary to `z`.
  intro ψ hψ
  obtain ⟨(φ : singularCochainGroupWithCoefficients X M 0), rfl⟩ := hψ
  rw [LinearMap.mem_ker]
  change singularCochainEvaluation X M z
    (((singularCochainComplexWithCoefficients X M).d 0 1).hom φ) = 0
  rw [singularCochainComplexWithCoefficients_d_apply]
  change φ (((integralSingularChainComplex X).d 1 0).hom z) = 0
  rw [hz, map_zero]

/-- Helper for Remark 60.1: a degree-one singular cohomology class can be
evaluated on a fixed singular one-cycle. -/
noncomputable def cohomologyOneEvaluationOnCycle
    (X : TopCat) (M : ModuleCat ℤ)
    (z : (integralSingularChainComplex X).X 1)
    (hz : ((integralSingularChainComplex X).d 1 0).hom z = 0) :
    SingularCohomologyWithCoefficients X M 1 →ₗ[ℤ] M :=
  let C := singularCochainComplexWithCoefficients X M
  let S := C.sc' 0 1 2
  let evaluationOnCycles : LinearMap.ker S.g.hom →ₗ[ℤ] M :=
    (singularCochainEvaluation X M z).comp
      ((LinearMap.ker S.g.hom).subtype :
        LinearMap.ker S.g.hom →ₗ[ℤ] singularCochainGroupWithCoefficients X M 1)
  let evaluationOnHomology :
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) →ₗ[ℤ] M :=
    Submodule.liftQ (LinearMap.range S.moduleCatToCycles) evaluationOnCycles
      (cochainEvaluationOnCycle_vanishesOnCoboundaries X M z hz)
  let normalize := cohomologyOneNormalization X M
  evaluationOnHomology.comp normalize.toLinearMap

/-- Helper for Remark 60.1: a concrete degree-one cocycle determines a class
in coefficient-valued singular cohomology. -/
noncomputable def cohomologyOneClassOfCocycle
    (X : TopCat) (M : ModuleCat ℤ)
    (φ : singularCochainGroupWithCoefficients X M 1)
    (hφ : ((singularCochainComplexWithCoefficients X M).d 1 2).hom φ = 0) :
    SingularCohomologyWithCoefficients X M 1 :=
  (cohomologyOneNormalization X M).symm (Submodule.Quotient.mk ⟨φ, hφ⟩)

/-- Helper for Remark 60.1: normalizing a class built from a cocycle returns
the concrete quotient class of that cocycle. -/
lemma cohomologyOneClassOfCocycle_normalize
    (X : TopCat) (M : ModuleCat ℤ)
    (φ : singularCochainGroupWithCoefficients X M 1)
    (hφ : ((singularCochainComplexWithCoefficients X M).d 1 2).hom φ = 0) :
    cohomologyOneNormalization X M
        (cohomologyOneClassOfCocycle X M φ hφ) =
      Submodule.Quotient.mk ⟨φ, hφ⟩ := by
  -- This is the cancellation rule for the normalization used in the constructor.
  exact (cohomologyOneNormalization X M).apply_symm_apply _

/-- Helper for Remark 60.1: fixed-cycle evaluation of a class represented by a
cocycle is ordinary cochain evaluation. -/
lemma cohomologyOneEvaluationOnCycle_classOfCocycle
    (X : TopCat) (M : ModuleCat ℤ)
    (z : (integralSingularChainComplex X).X 1)
    (hz : ((integralSingularChainComplex X).d 1 0).hom z = 0)
    (φ : singularCochainGroupWithCoefficients X M 1)
    (hφ : ((singularCochainComplexWithCoefficients X M).d 1 2).hom φ = 0) :
    cohomologyOneEvaluationOnCycle X M z hz
        (cohomologyOneClassOfCocycle X M φ hφ) = φ z := by
  -- The two normalization equivalences cancel, and quotient evaluation returns
  -- the value of the chosen cocycle representative.
  let C := singularCochainComplexWithCoefficients X M
  let S := C.sc' 0 1 2
  let evaluationOnCycles : LinearMap.ker S.g.hom →ₗ[ℤ] M :=
    (singularCochainEvaluation X M z).comp
      ((LinearMap.ker S.g.hom).subtype :
        LinearMap.ker S.g.hom →ₗ[ℤ] singularCochainGroupWithCoefficients X M 1)
  let evaluationOnHomology :
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) →ₗ[ℤ] M :=
    Submodule.liftQ (LinearMap.range S.moduleCatToCycles) evaluationOnCycles
      (cochainEvaluationOnCycle_vanishesOnCoboundaries X M z hz)
  let normalize := cohomologyOneNormalization X M
  let q : LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles :=
    Submodule.Quotient.mk ⟨φ, hφ⟩
  have hnormalize : normalize (normalize.symm q) = q :=
    normalize.apply_symm_apply q
  calc
    cohomologyOneEvaluationOnCycle X M z hz
        (cohomologyOneClassOfCocycle X M φ hφ) =
        evaluationOnHomology (normalize (normalize.symm q)) := rfl
    _ = evaluationOnHomology q := congrArg evaluationOnHomology hnormalize
    _ = φ z := by
      dsimp only [q, evaluationOnHomology, evaluationOnCycles,
        singularCochainEvaluation]
      rfl

/-- Helper for Remark 60.1: every degree-one coefficient-valued singular
cohomology class has a concrete cocycle representative. -/
lemma cohomologyOneClassOfCocycle_surjective
    (X : TopCat) (M : ModuleCat ℤ)
    (a : SingularCohomologyWithCoefficients X M 1) :
    ∃ (φ : singularCochainGroupWithCoefficients X M 1)
        (hφ : ((singularCochainComplexWithCoefficients X M).d 1 2).hom φ = 0),
      cohomologyOneClassOfCocycle X M φ hφ = a := by
  let C := singularCochainComplexWithCoefficients X M
  let S := C.sc' 0 1 2
  let normalize := cohomologyOneNormalization X M
  -- Choose a cycle representing the normalized quotient class.
  obtain ⟨φ, hφ⟩ :=
    Submodule.Quotient.mk_surjective
      (LinearMap.range S.moduleCatToCycles) (normalize a)
  refine ⟨φ.1, φ.2, ?_⟩
  -- Applying the inverse normalization to the chosen quotient equality
  -- recovers the original abstract cohomology class.
  calc
    cohomologyOneClassOfCocycle X M φ.1 φ.2 =
        normalize.symm (Submodule.Quotient.mk ⟨φ.1, φ.2⟩) := rfl
    _ = normalize.symm (Submodule.Quotient.mk φ) :=
      congrArg normalize.symm
        (congrArg Submodule.Quotient.mk (Subtype.coe_eta φ φ.2))
    _ = normalize.symm (normalize a) := congrArg normalize.symm hφ
    _ = a := normalize.symm_apply_apply a

/-- Helper for Remark 60.1: postcomposing a degree-one cocycle with a
coefficient homomorphism again gives a cocycle. -/
lemma singularCoefficientCocycle_isCocycle
    (X : TopCat) {M N : ModuleCat ℤ} (f : M ⟶ N)
    (φ : singularCochainGroupWithCoefficients X M 1)
    (hφ : ((singularCochainComplexWithCoefficients X M).d 1 2).hom φ = 0) :
    ((singularCochainComplexWithCoefficients X N).d 1 2).hom
        (f.hom.comp φ) = 0 := by
  -- Evaluate the mapped coboundary on a two-chain, then use the original
  -- cocycle equation before applying the coefficient homomorphism.
  apply LinearMap.ext
  intro x
  rw [singularCochainComplexWithCoefficients_d_apply]
  change f.hom (φ (((integralSingularChainComplex X).d 2 1).hom x)) = 0
  have hpoint := LinearMap.congr_fun hφ x
  rw [singularCochainComplexWithCoefficients_d_apply] at hpoint
  change φ (((integralSingularChainComplex X).d 2 1).hom x) = 0 at hpoint
  rw [hpoint, map_zero]

/-- Helper for Remark 60.1: evaluation of an explicitly represented
degree-one class commutes with a change of coefficients. -/
lemma cohomologyOneEvaluationOnCycle_classOfCocycle_coefficientMap
    (X : TopCat) {M N : ModuleCat ℤ} (f : M ⟶ N)
    (z : (integralSingularChainComplex X).X 1)
    (hz : ((integralSingularChainComplex X).d 1 0).hom z = 0)
    (φ : singularCochainGroupWithCoefficients X M 1)
    (hφ : ((singularCochainComplexWithCoefficients X M).d 1 2).hom φ = 0) :
    cohomologyOneEvaluationOnCycle X N z hz
        (cohomologyOneClassOfCocycle X N (f.hom.comp φ)
          (singularCoefficientCocycle_isCocycle X f φ hφ)) =
      f (cohomologyOneEvaluationOnCycle X M z hz
        (cohomologyOneClassOfCocycle X M φ hφ)) := by
  -- Reduce both classes to their cocycle representatives; postcomposition
  -- then computes coefficient transport pointwise.
  rw [cohomologyOneEvaluationOnCycle_classOfCocycle,
    cohomologyOneEvaluationOnCycle_classOfCocycle]
  rfl

end AlgebraicTopology
