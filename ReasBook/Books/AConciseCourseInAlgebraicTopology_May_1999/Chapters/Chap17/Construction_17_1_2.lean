import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap12.Definition_12_3_2
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.CommSq
import Mathlib.LinearAlgebra.TensorProduct.Quotient

noncomputable section

open CategoryTheory MonoidalCategory HomologicalComplex
open scoped TensorProduct

universe u

-- Semantic recall via `lean_leansearch`: the current environment exposes the tensor-product owner
-- `HomologicalComplex.tensorObj`, and Chapter 12 already fixes `homologyWithCoefficients` as the
-- target homology owner for `X ⊗ coefficientComplex R M`. This file therefore records the
-- source-facing cycle map and homology comparison, while the quotient-model descent helpers
-- remain internal to this file.

-- The next helper isolates the `(i, 0)` tensor summand normalization used in both the cycle and
-- boundary computations below.
/-- Helper for Construction 17.1.2: on the `(i, 0)` summand of
`X ⊗ coefficientComplex R M`, the tensor differential is induced entirely by the differential of
`X`. -/
private theorem tensorZeroSummand_d_eq
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (i : ℕ) :
    ιTensorObj X (coefficientComplex R M) i 0 i (by simp) ≫
        (X ⊗ coefficientComplex R M).d i ((ComplexShape.down ℕ).next i) =
      (X.d i ((ComplexShape.down ℕ).next i) ⊗ₘ 𝟙 M) ≫
        ιTensorObj X (coefficientComplex R M) ((ComplexShape.down ℕ).next i) 0
          ((ComplexShape.down ℕ).next i) (by simp) := by
  -- Split the tensor differential into its `X`- and coefficient-complex parts.
  change
    ιMapBifunctor X (coefficientComplex R M) (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
        i 0 i (by simp) ≫
      (HomologicalComplex.mapBifunctor X (coefficientComplex R M) (curriedTensor (ModuleCat R))
          (ComplexShape.down ℕ)).d i ((ComplexShape.down ℕ).next i) =
    _
  rw [HomologicalComplex.mapBifunctor.d_eq X (coefficientComplex R M)
    (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i ((ComplexShape.down ℕ).next i),
    Preadditive.comp_add]
  have hD₁ :
      ιMapBifunctor X (coefficientComplex R M) (curriedTensor (ModuleCat R))
          (ComplexShape.down ℕ) i 0 i (by simp) ≫
        HomologicalComplex.mapBifunctor.D₁ X (coefficientComplex R M)
          (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i
          ((ComplexShape.down ℕ).next i) =
      HomologicalComplex.mapBifunctor.d₁ X (coefficientComplex R M)
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i 0
        ((ComplexShape.down ℕ).next i) := by
    -- Expose the `D₁` branch on the visible `(i, 0)` summand.
    simpa using
      HomologicalComplex.mapBifunctor.ι_D₁ X (coefficientComplex R M)
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i
        ((ComplexShape.down ℕ).next i) i 0 (by simp)
  have hD₂ :
      ιMapBifunctor X (coefficientComplex R M) (curriedTensor (ModuleCat R))
          (ComplexShape.down ℕ) i 0 i (by simp) ≫
        HomologicalComplex.mapBifunctor.D₂ X (coefficientComplex R M)
          (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i
          ((ComplexShape.down ℕ).next i) =
      HomologicalComplex.mapBifunctor.d₂ X (coefficientComplex R M)
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i 0
        ((ComplexShape.down ℕ).next i) := by
    -- Expose the `D₂` branch on the visible `(i, 0)` summand.
    simpa using
      HomologicalComplex.mapBifunctor.ι_D₂ X (coefficientComplex R M)
        (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i
        ((ComplexShape.down ℕ).next i) i 0 (by simp)
  rw [hD₁, hD₂]
  by_cases hi : (ComplexShape.down ℕ).Rel i ((ComplexShape.down ℕ).next i)
  · -- The `X`-branch is the visible differential, while the coefficient branch vanishes.
    rw [HomologicalComplex.mapBifunctor.d₁_eq X (coefficientComplex R M)
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) hi 0
      ((ComplexShape.down ℕ).next i) (by simp)]
    rw [HomologicalComplex.mapBifunctor.d₂_eq_zero X (coefficientComplex R M)
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i 0
      ((ComplexShape.down ℕ).next i) (by simp [ComplexShape.down_Rel])]
    dsimp [ComplexShape.ε₁]
    have hleft :
        (1 : ℤˣ) •
            (X.d i ((ComplexShape.down ℕ).next i) ▷ M ≫
              ιMapBifunctor X (coefficientComplex R M) (curriedTensor (ModuleCat R))
                (ComplexShape.down ℕ) ((ComplexShape.down ℕ).next i) 0
                ((ComplexShape.down ℕ).next i) (by simp)) +
          0 =
        X.d i ((ComplexShape.down ℕ).next i) ▷ M ≫
          ιMapBifunctor X (coefficientComplex R M) (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).next i) 0
            ((ComplexShape.down ℕ).next i) (by simp) := by
      -- The sign is trivial in the first tensor differential and the extra summand is zero.
      simp
    rw [tensorHom_id]
    exact hleft
  · -- Off the shape relation both branches are zero, so the target side is also zero.
    rw [HomologicalComplex.mapBifunctor.d₁_eq_zero X (coefficientComplex R M)
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i 0
      ((ComplexShape.down ℕ).next i) hi]
    rw [HomologicalComplex.mapBifunctor.d₂_eq_zero X (coefficientComplex R M)
      (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) i 0
      ((ComplexShape.down ℕ).next i) (by simp [ComplexShape.down_Rel])]
    rw [X.shape _ _ hi, tensorHom_id]
    rw [zero_add]
    rw [← tensorHom_id]
    simp
    rfl

private theorem homologyTensorCycleMap_d_eq_zero
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) n] :
    ((X.iCycles n ⊗ₘ 𝟙 M) ≫
        ιTensorObj X (coefficientComplex R M) n 0 n rfl) ≫
      (X ⊗ coefficientComplex R M).d n ((ComplexShape.down ℕ).next n) =
    0 :=
  by
  -- First normalize the tensor differential on the `(n, 0)` summand.
  calc
    ((X.iCycles n ⊗ₘ 𝟙 M) ≫
          ιTensorObj X (coefficientComplex R M) n 0 n rfl) ≫
        (X ⊗ coefficientComplex R M).d n ((ComplexShape.down ℕ).next n) =
      (X.iCycles n ⊗ₘ 𝟙 M) ≫
        ((X.d n ((ComplexShape.down ℕ).next n) ⊗ₘ 𝟙 M) ≫
          ιTensorObj X (coefficientComplex R M) ((ComplexShape.down ℕ).next n) 0
            ((ComplexShape.down ℕ).next n) (by simp)) := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦ (X.iCycles n ⊗ₘ 𝟙 M) ≫ f)
              (tensorZeroSummand_d_eq R X M n)
    _ =
      ((X.iCycles n ≫ X.d n ((ComplexShape.down ℕ).next n)) ⊗ₘ 𝟙 M) ≫
        ιTensorObj X (coefficientComplex R M) ((ComplexShape.down ℕ).next n) 0
          ((ComplexShape.down ℕ).next n) (by simp) := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦ f ≫
                ιTensorObj X (coefficientComplex R M) ((ComplexShape.down ℕ).next n) 0
                  ((ComplexShape.down ℕ).next n) (by simp))
              (tensorHom_comp_tensorHom (X.iCycles n) (𝟙 M)
                (X.d n ((ComplexShape.down ℕ).next n)) (𝟙 M))
    _ = 0 := by
          rw [X.iCycles_d n ((ComplexShape.down ℕ).next n)]
          simp

/-- The cycle-level morphism underlying the homology comparison
`α : X.homology n ⊗ M ⟶ homologyWithCoefficients R X M n` is the canonical lift
`X.cycles n ⊗ M ⟶
  (X ⊗ coefficientComplex R M).cycles n`
of the evident tensor of `X.iCycles n` with `𝟙 M` followed by the `(n, 0)` summand inclusion into
the tensor complex.
-/
noncomputable def homologyTensorCycleMap
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) n] :
    X.cycles n ⊗ M ⟶ (X ⊗ coefficientComplex R M).cycles n :=
  (X ⊗ coefficientComplex R M).liftCycles
    ((X.iCycles n ⊗ₘ 𝟙 M) ≫
      ιTensorObj X (coefficientComplex R M) n 0 n rfl)
    ((ComplexShape.down ℕ).next n)
    rfl
    (homologyTensorCycleMap_d_eq_zero R X M n)

/-- The cycle-level map `homologyTensorCycleMap` fits into the canonical `iCycles` square of
Construction 17.1.2. -/
theorem homologyTensorCycleMap_iCycles
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) n] :
    CommSq (X.iCycles n ⊗ₘ 𝟙 M) (homologyTensorCycleMap R X M n)
      (ιTensorObj X (coefficientComplex R M) n 0 n rfl)
      ((X ⊗ coefficientComplex R M).iCycles n) :=
  by
    -- This is exactly the defining `liftCycles_i` computation for the lifted cycles map.
    refine ⟨?_⟩
    rw [homologyTensorCycleMap]
    exact
      (HomologicalComplex.liftCycles_i
        (K := X ⊗ coefficientComplex R M)
        (((X.iCycles n ⊗ₘ 𝟙 M) ≫
          ιTensorObj X (coefficientComplex R M) n 0 n rfl))
        ((ComplexShape.down ℕ).next n)
        rfl
        (homologyTensorCycleMap_d_eq_zero R X M n)).symm

/-- The concrete linear map on the explicit quotient model of `X.homology n ⊗ M` obtained from
`homologyTensorCycleMap` and the target homology quotient. -/
private noncomputable def homologyTensorKernelToHomologyLinear
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) n] :
    (X.sc n).moduleCatLeftHomologyData.K ⊗[R] M →ₗ[R]
      ((X ⊗ coefficientComplex R M).sc n).moduleCatLeftHomologyData.H :=
  ModuleCat.Hom.hom
    ((((X.sc n).moduleCatCyclesIso.inv ⊗ₘ 𝟙 M) ≫
        homologyTensorCycleMap R X M n ≫
        (X ⊗ coefficientComplex R M).homologyπ n ≫
        ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom))

/-- Helper for Construction 17.1.2: normalize `homologyTensorKernelToHomologyLinear` to the
concrete quotient projection on the target short complex. -/
private theorem homologyTensorKernelToHomologyLinear_eq_concreteProjection
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) n] :
    homologyTensorKernelToHomologyLinear R X M n =
      ((((X.sc n).moduleCatCyclesIso.inv ⊗ₘ 𝟙 M) ≫
          homologyTensorCycleMap R X M n ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatCyclesIso.hom ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatLeftHomologyData.π).hom) := by
  -- Rewrite the target homology quotient through the concrete cycles quotient model.
  rw [homologyTensorKernelToHomologyLinear]
  congr 1
  exact congrArg
    (fun f ↦
      (((X.sc n).moduleCatCyclesIso.inv ⊗ₘ 𝟙 M) ≫
        homologyTensorCycleMap R X M n) ≫ f)
    (CategoryTheory.ShortComplex.π_moduleCatCyclesIso_hom
      (S := (X ⊗ coefficientComplex R M).sc n))

/-- Helper for Construction 17.1.2: the concrete boundary map in degree `n`, followed by the
cycles identification on `(X.sc n)`, is `X.toCycles ((ComplexShape.down ℕ).prev n) n`. -/
private theorem moduleCatLeftHomologyData_f'_moduleCatCyclesIso_inv
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv =
      X.toCycles ((ComplexShape.down ℕ).prev n) n := by
  -- Compare both descriptions after postcomposing with the cycle inclusion.
  simpa [Category.assoc] using
    (congrArg (fun f => f ≫ (X.sc n).moduleCatCyclesIso.inv)
      (CategoryTheory.ShortComplex.toCycles_moduleCatCyclesIso_hom (S := X.sc n))).symm

/-- Helper for Construction 17.1.2: after returning from the concrete cycles model, the source
boundary map is the actual differential `X.d ((ComplexShape.down ℕ).prev n) n`. -/
private theorem leftBoundarySourceCyclesIso_inv_iCycles
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    (X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv ≫ X.iCycles n =
      X.d ((ComplexShape.down ℕ).prev n) n := by
  -- Rewrite the concrete quotient-model boundary map to `toCycles`, then recover the chain
  -- differential by composing with the cycle inclusion.
  simpa [Category.assoc] using
    congrArg
      (fun f ↦ f ≫ X.iCycles n)
      (moduleCatLeftHomologyData_f'_moduleCatCyclesIso_inv R X n)

/-- Helper for Construction 17.1.2: precomposing the visible cycle representative with the source
boundary map yields the actual tensor-complex boundary representative. -/
private theorem homologyTensorLeftBoundaryRepresentative_normalized
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ 𝟙 M) ≫
        ((X.iCycles n ⊗ₘ 𝟙 M) ≫
          ιTensorObj X (coefficientComplex R M) n 0 n rfl)) =
      ((X.d ((ComplexShape.down ℕ).prev n) n ⊗ₘ 𝟙 M) ≫
        ιTensorObj X (coefficientComplex R M) n 0 n rfl) := by
  -- Push the tensor composition across the visible `(n, 0)` summand.
  calc
    ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ 𝟙 M) ≫
          ((X.iCycles n ⊗ₘ 𝟙 M) ≫
            ιTensorObj X (coefficientComplex R M) n 0 n rfl)) =
      (((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ
            𝟙 M) ≫
          (X.iCycles n ⊗ₘ 𝟙 M)) ≫
        ιTensorObj X (coefficientComplex R M) n 0 n rfl) := by
          simp [Category.assoc]
    _ =
      ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ≫
            X.iCycles n) ⊗ₘ 𝟙 M) ≫
        ιTensorObj X (coefficientComplex R M) n 0 n rfl := by
          rw [tensorHom_comp_tensorHom]
          simp [Category.assoc]
    _ =
      ((X.d ((ComplexShape.down ℕ).prev n) n ⊗ₘ 𝟙 M) ≫
        ιTensorObj X (coefficientComplex R M) n 0 n rfl) := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦ (f ⊗ₘ 𝟙 M) ≫
                ιTensorObj X (coefficientComplex R M) n 0 n rfl)
              (leftBoundarySourceCyclesIso_inv_iCycles R X n)

/-- Helper for Construction 17.1.2: the normalized `(prev n, 0)` representative is a literal
boundary in `X ⊗ coefficientComplex R M`. -/
private theorem tensorBoundaryPrevZeroSummand
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    ((X.d ((ComplexShape.down ℕ).prev n)
          ((ComplexShape.down ℕ).next ((ComplexShape.down ℕ).prev n)) ⊗ₘ 𝟙 M) ≫
        ιTensorObj X (coefficientComplex R M)
          ((ComplexShape.down ℕ).next ((ComplexShape.down ℕ).prev n)) 0
          ((ComplexShape.down ℕ).next ((ComplexShape.down ℕ).prev n)) (by simp)) =
      ιTensorObj X (coefficientComplex R M) ((ComplexShape.down ℕ).prev n) 0
        ((ComplexShape.down ℕ).prev n) (by simp) ≫
          (X ⊗ coefficientComplex R M).d ((ComplexShape.down ℕ).prev n)
            ((ComplexShape.down ℕ).next ((ComplexShape.down ℕ).prev n)) := by
  -- Specialize the `(i, 0)` tensor-differential formula at `i = prev n` and reverse it.
  exact (tensorZeroSummand_d_eq R X M ((ComplexShape.down ℕ).prev n)).symm

/-- Helper for Construction 17.1.2: normalize the visible target index
`next (prev n)` to `n`. -/
private theorem tensorBoundaryVisibleTarget_eq (n : ℕ) :
    (ComplexShape.down ℕ).next ((ComplexShape.down ℕ).prev n) = n := by
  rw [ChainComplex.prev]
  exact ChainComplex.next_nat_succ n

/-- Helper for Construction 17.1.2: `tensorBoundaryPrevZeroSummand` with the target degree
spelled visibly as `n`. -/
private theorem tensorBoundaryPrevZeroSummandVisible
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    ((X.d ((ComplexShape.down ℕ).prev n) n ⊗ₘ 𝟙 M) ≫
        ιTensorObj X (coefficientComplex R M) n 0 n rfl) =
      ιTensorObj X (coefficientComplex R M) ((ComplexShape.down ℕ).prev n) 0
        ((ComplexShape.down ℕ).prev n) (by simp) ≫
          (X ⊗ coefficientComplex R M).d ((ComplexShape.down ℕ).prev n) n :=
  by
  -- Route correction: rewrite the literal boundary identity only at the visible target degree,
  -- so the dependent codomain transport is discharged by simplification rather than `convert`.
  have h := (tensorZeroSummand_d_eq R X M ((ComplexShape.down ℕ).prev n)).symm
  rw [tensorBoundaryVisibleTarget_eq n] at h
  simpa using h

/-- Helper for Construction 17.1.2: the source boundary relation maps to zero after the
cycle-level tensor map and the target homology quotient. -/
private theorem homologyTensorLeftBoundary_homology_zero
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) n] :
    ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ 𝟙 M) ≫
        homologyTensorCycleMap R X M n ≫
        (X ⊗ coefficientComplex R M).homologyπ n ≫
        ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom) =
      0 := by
  -- Route correction: normalize the precomposition before any reassociation, then rewrite the
  -- resulting representative to a literal boundary and kill it in homology.
  have hkprecomp :
      ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ 𝟙 M) ≫
            ((X.iCycles n ⊗ₘ 𝟙 M) ≫
              ιTensorObj X (coefficientComplex R M) n 0 n rfl)) ≫
          (X ⊗ coefficientComplex R M).d n ((ComplexShape.down ℕ).next n) =
        0 := by
    -- The source precomposition preserves the cycle relation needed to lift into target cycles.
    simpa [Category.assoc] using
      congrArg
        (fun f ↦
          (((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ
              𝟙 M) ≫
            f)
        (homologyTensorCycleMap_d_eq_zero R X M n)
  have hboundaryWitness :
      ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ 𝟙 M) ≫
            ((X.iCycles n ⊗ₘ 𝟙 M) ≫
              ιTensorObj X (coefficientComplex R M) n 0 n rfl)) =
        ιTensorObj X (coefficientComplex R M) ((ComplexShape.down ℕ).prev n) 0
            ((ComplexShape.down ℕ).prev n) (by simp) ≫
          (X ⊗ coefficientComplex R M).d ((ComplexShape.down ℕ).prev n) n := by
    -- Identify the precomposed representative with a literal tensor boundary.
    exact
      (homologyTensorLeftBoundaryRepresentative_normalized
        (R := R) (X := X) (M := M) (n := n)).trans
        (tensorBoundaryPrevZeroSummandVisible (R := R) (X := X) (M := M) (n := n))
  have hcomp :
      ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ 𝟙 M) ≫
          homologyTensorCycleMap R X M n) =
        (X ⊗ coefficientComplex R M).liftCycles
          ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ
              𝟙 M) ≫
            ((X.iCycles n ⊗ₘ 𝟙 M) ≫
              ιTensorObj X (coefficientComplex R M) n 0 n rfl))
          ((ComplexShape.down ℕ).next n)
          rfl
          hkprecomp := by
    -- Push the source boundary precomposition through the cycle lift.
    simpa [homologyTensorCycleMap] using
      HomologicalComplex.comp_liftCycles (K := X ⊗ coefficientComplex R M)
        (((X.iCycles n ⊗ₘ 𝟙 M) ≫
          ιTensorObj X (coefficientComplex R M) n 0 n rfl))
        ((ComplexShape.down ℕ).next n)
        rfl
        (homologyTensorCycleMap_d_eq_zero R X M n)
        (((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ
          𝟙 M)
  have hzero :
      (X ⊗ coefficientComplex R M).liftCycles
          ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ
                𝟙 M) ≫
              ((X.iCycles n ⊗ₘ 𝟙 M) ≫
                ιTensorObj X (coefficientComplex R M) n 0 n rfl))
          ((ComplexShape.down ℕ).next n)
          rfl
          hkprecomp ≫
        (X ⊗ coefficientComplex R M).homologyπ n =
      0 := by
    -- Once the representative is visibly a boundary, its homology class vanishes.
    exact HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
      (K := X ⊗ coefficientComplex R M)
      ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ 𝟙 M) ≫
        ((X.iCycles n ⊗ₘ 𝟙 M) ≫
          ιTensorObj X (coefficientComplex R M) n 0 n rfl))
      ((ComplexShape.down ℕ).next n)
      rfl
      (ιTensorObj X (coefficientComplex R M) ((ComplexShape.down ℕ).prev n) 0
        ((ComplexShape.down ℕ).prev n) (by simp))
      hboundaryWitness
  calc
    ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ 𝟙 M) ≫
          homologyTensorCycleMap R X M n ≫
          (X ⊗ coefficientComplex R M).homologyπ n ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom) =
        (X ⊗ coefficientComplex R M).liftCycles
            ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ
                𝟙 M) ≫
              ((X.iCycles n ⊗ₘ 𝟙 M) ≫
                ιTensorObj X (coefficientComplex R M) n 0 n rfl))
            ((ComplexShape.down ℕ).next n)
            rfl
            hkprecomp ≫
          (X ⊗ coefficientComplex R M).homologyπ n ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom := by
      simpa [Category.assoc] using
        congrArg
          (fun f ↦
            f ≫ (X ⊗ coefficientComplex R M).homologyπ n ≫
              ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom)
          hcomp
    _ =
        ((X ⊗ coefficientComplex R M).liftCycles
              ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ
                    𝟙 M) ≫
                  ((X.iCycles n ⊗ₘ 𝟙 M) ≫
                    ιTensorObj X (coefficientComplex R M) n 0 n rfl))
              ((ComplexShape.down ℕ).next n)
              rfl
              hkprecomp ≫
            (X ⊗ coefficientComplex R M).homologyπ n) ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom := by
      simp [Category.assoc]
    _ = 0 := by
      -- Postcompose the vanishing homology class with the concrete target homology isomorphism.
      rw [hzero]
      rw [CategoryTheory.Limits.zero_comp]

/-- The kernel-level tensor map kills the boundary summands, so it descends across the quotient
presentation of `X.homology n ⊗ M`. -/
private theorem homologyTensorKernelToHomologyLinear_range_le_ker
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) n] :
    LinearMap.range
        (TensorProduct.map
          (Submodule.subtype
            (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom)))
          (LinearMap.id : M →ₗ[R] M)) ≤
      LinearMap.ker (homologyTensorKernelToHomologyLinear R X M n) := by
  -- Evaluate the descent condition on pure tensors in the concrete quotient presentation.
  exact LinearMap.range_le_ker_iff.2 <| by
    apply TensorProduct.ext'
    intro x y
    rcases x with ⟨x, hx⟩
    rcases hx with ⟨x', rfl⟩
    have hzero :
        ModuleCat.Hom.hom
            ((((X.sc n).moduleCatLeftHomologyData.f' ≫ (X.sc n).moduleCatCyclesIso.inv) ⊗ₘ
                𝟙 M) ≫
              homologyTensorCycleMap R X M n ≫
              (X ⊗ coefficientComplex R M).homologyπ n ≫
              ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom)
            (x' ⊗ₜ y) =
          0 := by
      simpa using
        congrArg
          (fun f ↦ ModuleCat.Hom.hom f (x' ⊗ₜ y))
          (homologyTensorLeftBoundary_homology_zero R X M n)
    simpa [LinearMap.comp_apply, homologyTensorKernelToHomologyLinear,
      TensorProduct.map_tmul] using hzero

/-- The morphism `homologyTensorComparison` from Construction 17.1.2 sends
`X.homology n ⊗ M` to `homologyWithCoefficients R X M n` by tensoring cycle representatives
with `M` and descending to the homology quotient. -/
noncomputable def homologyTensorComparison
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) n] :
    X.homology n ⊗ M ⟶ homologyWithCoefficients R X M n :=
  ((X.sc n).moduleCatHomologyIso.hom ⊗ₘ 𝟙 M) ≫
    ModuleCat.ofHom
  ((Submodule.liftQ
          (LinearMap.range
            (TensorProduct.map
              (Submodule.subtype
                (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom)))
              (LinearMap.id : M →ₗ[R] M)))
          (homologyTensorKernelToHomologyLinear R X M n)
          (homologyTensorKernelToHomologyLinear_range_le_ker R X M n)).comp
        (TensorProduct.quotientTensorEquiv M
          (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom))).toLinearMap) ≫
    ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.inv

/-- Helper for Construction 17.1.2: tensoring the source homology quotient map with `M` matches
the concrete quotient map on the cycles model of `X.sc n`. -/
private theorem sourceHomologyPiTensorNormalized
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n] :
    ((X.homologyπ n ⊗ₘ 𝟙 M) ≫ ((X.sc n).moduleCatHomologyIso.hom ⊗ₘ 𝟙 M)) =
      ((X.sc n).moduleCatCyclesIso.hom ⊗ₘ 𝟙 M) ≫
        ((X.sc n).moduleCatLeftHomologyData.π ⊗ₘ 𝟙 M) := by
  -- Rewrite the source homology quotient into the concrete cycles quotient before tensoring.
  calc
    ((X.homologyπ n ⊗ₘ 𝟙 M) ≫ ((X.sc n).moduleCatHomologyIso.hom ⊗ₘ 𝟙 M)) =
      ((X.homologyπ n ≫ (X.sc n).moduleCatHomologyIso.hom) ⊗ₘ 𝟙 M) := by
        exact tensorHom_comp_tensorHom (X.homologyπ n) (𝟙 M)
          (X.sc n).moduleCatHomologyIso.hom (𝟙 M)
    _ =
      (((X.sc n).moduleCatCyclesIso.hom ≫ (X.sc n).moduleCatLeftHomologyData.π) ⊗ₘ 𝟙 M) := by
        simpa using
          congrArg
            (fun f ↦ f ⊗ₘ 𝟙 M)
            (CategoryTheory.ShortComplex.π_moduleCatCyclesIso_hom (S := X.sc n))
    _ =
      ((X.sc n).moduleCatCyclesIso.hom ⊗ₘ 𝟙 M) ≫
        ((X.sc n).moduleCatLeftHomologyData.π ⊗ₘ 𝟙 M) := by
        exact
          (tensorHom_comp_tensorHom
            (X.sc n).moduleCatCyclesIso.hom
            (𝟙 M)
            (X.sc n).moduleCatLeftHomologyData.π
            (𝟙 M)).symm

/-- Helper for Construction 17.1.2: after entering the concrete cycles model on the source,
the descended quotient formula uses the concrete quotient map
`(X.sc n).moduleCatLeftHomologyData.π ⊗ₘ 𝟙 M`. -/
private theorem homologyTensorComparison_sourceDescNormalized
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) n] :
    (((X.sc n).moduleCatCyclesIso.inv ⊗ₘ 𝟙 M) ≫
          (X.homologyπ n ⊗ₘ 𝟙 M) ≫
          ((X.sc n).moduleCatHomologyIso.hom ⊗ₘ 𝟙 M) ≫
          ModuleCat.ofHom
            ((Submodule.liftQ
                    (LinearMap.range
                      (TensorProduct.map
                        (Submodule.subtype
                          (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom)))
                        (LinearMap.id : M →ₗ[R] M)))
                    (homologyTensorKernelToHomologyLinear R X M n)
                    (homologyTensorKernelToHomologyLinear_range_le_ker R X M n)).comp
                  (TensorProduct.quotientTensorEquiv M
                    (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom))).toLinearMap) ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.inv ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom) =
      (((X.sc n).moduleCatLeftHomologyData.π ⊗ₘ 𝟙 M) ≫
          ModuleCat.ofHom
            ((Submodule.liftQ
                    (LinearMap.range
                      (TensorProduct.map
                        (Submodule.subtype
                          (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom)))
                        (LinearMap.id : M →ₗ[R] M)))
                    (homologyTensorKernelToHomologyLinear R X M n)
                    (homologyTensorKernelToHomologyLinear_range_le_ker R X M n)).comp
                  (TensorProduct.quotientTensorEquiv M
                    (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom))).toLinearMap) ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.inv ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom) := by
  -- First normalize the abstract source quotient to the concrete cycles quotient, then extend
  -- that equality across the descended quotient map.
  have hsourceBase :
      (((X.sc n).moduleCatCyclesIso.inv ⊗ₘ 𝟙 M) ≫
            ((X.homologyπ n ⊗ₘ 𝟙 M) ≫
              ((X.sc n).moduleCatHomologyIso.hom ⊗ₘ 𝟙 M))) =
        ((X.sc n).moduleCatLeftHomologyData.π ⊗ₘ 𝟙 M) := by
    calc
      (((X.sc n).moduleCatCyclesIso.inv ⊗ₘ 𝟙 M) ≫
              ((X.homologyπ n ⊗ₘ 𝟙 M) ≫
                ((X.sc n).moduleCatHomologyIso.hom ⊗ₘ 𝟙 M))) =
          (((X.sc n).moduleCatCyclesIso.inv ⊗ₘ 𝟙 M) ≫
            (((X.sc n).moduleCatCyclesIso.hom ⊗ₘ 𝟙 M) ≫
              ((X.sc n).moduleCatLeftHomologyData.π ⊗ₘ 𝟙 M))) := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦ ((X.sc n).moduleCatCyclesIso.inv ⊗ₘ 𝟙 M) ≫ f)
              (sourceHomologyPiTensorNormalized (R := R) (X := X) (M := M) (n := n))
      _ = ((X.sc n).moduleCatLeftHomologyData.π ⊗ₘ 𝟙 M) := by
          simp
  simpa [Category.assoc] using
    congrArg
      (fun f ↦
        f ≫
          ModuleCat.ofHom
            ((Submodule.liftQ
                    (LinearMap.range
                      (TensorProduct.map
                        (Submodule.subtype
                          (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom)))
                        (LinearMap.id : M →ₗ[R] M)))
                    (homologyTensorKernelToHomologyLinear R X M n)
                    (homologyTensorKernelToHomologyLinear_range_le_ker R X M n)).comp
                  (TensorProduct.quotientTensorEquiv M
                    (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom))).toLinearMap) ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.inv ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom)
      hsourceBase

/-- Helper for Construction 17.1.2: after postcomposing with the concrete target homology model,
the quotient-descended formula for `homologyTensorComparison` agrees with the cycle-level tensor
map. -/
private theorem sourceHomologyTensorDesc_comp_piTensor
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) n] :
    ((X.sc n).moduleCatLeftHomologyData.π ⊗ₘ 𝟙 M) ≫
        ModuleCat.ofHom
          ((Submodule.liftQ
                  (LinearMap.range
                    (TensorProduct.map
                      (Submodule.subtype
                        (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom)))
                      (LinearMap.id : M →ₗ[R] M)))
                  (homologyTensorKernelToHomologyLinear R X M n)
                  (homologyTensorKernelToHomologyLinear_range_le_ker R X M n)).comp
                (TensorProduct.quotientTensorEquiv M
                  (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom))).toLinearMap) =
      ModuleCat.ofHom (homologyTensorKernelToHomologyLinear R X M n) := by
  -- Evaluate both sides on pure tensors in the concrete quotient model.
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x m
  -- Route correction: move the quotient computation to pure tensors and let the concrete
  -- quotient-tensor formulas identify the descended map with the target linear map directly.
  change
      ((Submodule.liftQ
            (LinearMap.range
              (TensorProduct.map
                (Submodule.subtype
                  (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom)))
                (LinearMap.id : M →ₗ[R] M)))
            (homologyTensorKernelToHomologyLinear R X M n)
            (homologyTensorKernelToHomologyLinear_range_le_ker R X M n)).comp
          (TensorProduct.quotientTensorEquiv M
            (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom))).toLinearMap)
        (((X.sc n).moduleCatLeftHomologyData.π ⊗ₘ 𝟙 M) (x ⊗ₜ[R] m)) =
      homologyTensorKernelToHomologyLinear R X M n (x ⊗ₜ[R] m)
  -- First compute the tensor of the quotient map on a pure tensor.
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul]
  -- Then rewrite the quotient class to the standard `Submodule.Quotient.mk` spelling.
  change
      ((Submodule.liftQ
            (LinearMap.range
              (TensorProduct.map
                (Submodule.subtype
                  (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom)))
                (LinearMap.id : M →ₗ[R] M)))
            (homologyTensorKernelToHomologyLinear R X M n)
            (homologyTensorKernelToHomologyLinear_range_le_ker R X M n)).comp
          (TensorProduct.quotientTensorEquiv M
            (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom))).toLinearMap)
        (Submodule.Quotient.mk x ⊗ₜ[R] m) =
      homologyTensorKernelToHomologyLinear R X M n (x ⊗ₜ[R] m)
  -- The concrete quotient-tensor and quotient-descent formulas now match the target map exactly.
  rw [LinearMap.comp_apply]
  have hquot :
      (TensorProduct.quotientTensorEquiv M
          (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom)))
        (Submodule.Quotient.mk x ⊗ₜ[R] m) =
        Submodule.Quotient.mk (x ⊗ₜ[R] m) := by
    simpa using
      (TensorProduct.quotientTensorEquiv_apply_tmul_mk
        (N := M)
        (m := LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom))
        x m)
  -- Apply the descended quotient map to the quotient-tensor computation.
  simpa [Submodule.liftQ_apply] using
    congrArg
      ((LinearMap.range
            (TensorProduct.map
              (Submodule.subtype
                (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom)))
              (LinearMap.id : M →ₗ[R] M))).liftQ
        (homologyTensorKernelToHomologyLinear R X M n)
        (homologyTensorKernelToHomologyLinear_range_le_ker R X M n))
      hquot

/-- Helper for Construction 17.1.2: after postcomposing with the concrete target homology model,
the quotient-descended formula for `homologyTensorComparison` agrees with the cycle-level tensor
map. -/
private theorem homologyTensorComparison_spec_moduleCat
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) n] :
    ((X.homologyπ n ⊗ₘ 𝟙 M) ≫ homologyTensorComparison R X M n ≫
        ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom) =
      homologyTensorCycleMap R X M n ≫
        (X ⊗ coefficientComplex R M).homologyπ n ≫
        ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom :=
  by
  -- Route correction: pull the source side back to the concrete cycles model first, then replace
  -- the quotient constructor by the concrete linear map on pure tensors.
  apply (cancel_epi (((X.sc n).moduleCatCyclesIso.inv ⊗ₘ 𝟙 M))).1
  calc
    (((X.sc n).moduleCatCyclesIso.inv ⊗ₘ 𝟙 M) ≫
          ((X.homologyπ n ⊗ₘ 𝟙 M) ≫
            homologyTensorComparison R X M n ≫
              ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom)) =
        (((X.sc n).moduleCatLeftHomologyData.π ⊗ₘ 𝟙 M) ≫
            ModuleCat.ofHom
              ((Submodule.liftQ
                      (LinearMap.range
                        (TensorProduct.map
                          (Submodule.subtype
                            (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom)))
                          (LinearMap.id : M →ₗ[R] M)))
                    (homologyTensorKernelToHomologyLinear R X M n)
                    (homologyTensorKernelToHomologyLinear_range_le_ker R X M n)).comp
                    ((TensorProduct.quotientTensorEquiv M
                      (LinearMap.range
                        (((X.sc n).moduleCatLeftHomologyData.f').hom))).toLinearMap)) ≫
            ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.inv ≫
            ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom) := by
        simpa [homologyTensorComparison, Category.assoc] using
          homologyTensorComparison_sourceDescNormalized (R := R) (X := X) (M := M) (n := n)
    _ =
        ((((X.sc n).moduleCatLeftHomologyData.π ⊗ₘ 𝟙 M) ≫
            ModuleCat.ofHom
              ((Submodule.liftQ
                      (LinearMap.range
                        (TensorProduct.map
                          (Submodule.subtype
                            (LinearMap.range (((X.sc n).moduleCatLeftHomologyData.f').hom)))
                          (LinearMap.id : M →ₗ[R] M)))
                      (homologyTensorKernelToHomologyLinear R X M n)
                      (homologyTensorKernelToHomologyLinear_range_le_ker R X M n)).comp
                    ((TensorProduct.quotientTensorEquiv M
                      (LinearMap.range
                        (((X.sc n).moduleCatLeftHomologyData.f').hom))).toLinearMap))) ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.inv) ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom := by
        simp [Category.assoc]
    _ =
        (ModuleCat.ofHom (homologyTensorKernelToHomologyLinear R X M n) ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.inv) ≫
          ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom := by
        -- Replace the quotient constructor by the concrete tensor-to-homology linear map.
        rw [sourceHomologyTensorDesc_comp_piTensor (R := R) (X := X) (M := M) (n := n)]
    _ =
        ModuleCat.ofHom (homologyTensorKernelToHomologyLinear R X M n) ≫
          (((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.inv ≫
            ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom) := by
        simp [Category.assoc]
    _ = ModuleCat.ofHom (homologyTensorKernelToHomologyLinear R X M n) := by
        -- Cancel the target homology isomorphism pair after the concrete map is exposed.
        rw [CategoryTheory.Iso.inv_hom_id]
        rw [Category.comp_id]
    _ =
        ((X.sc n).moduleCatCyclesIso.inv ⊗ₘ 𝟙 M) ≫
          (homologyTensorCycleMap R X M n ≫
            (X ⊗ coefficientComplex R M).homologyπ n ≫
              ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom) := by
        rfl
    _ =
        (((X.sc n).moduleCatCyclesIso.inv ⊗ₘ 𝟙 M) ≫
          homologyTensorCycleMap R X M n ≫
            (X ⊗ coefficientComplex R M).homologyπ n ≫
              ((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom) := by
        simp

/-- Construction 17.1.2. The comparison morphism `homologyTensorComparison` is induced from
`homologyTensorCycleMap` by the quotient maps from cycles to homology. -/
theorem homologyTensorComparison_spec
    (R : Type u) [CommRing R]
    (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ)
    [HomologicalComplex.HasHomology X n]
    [HomologicalComplex.HasHomology (X ⊗ coefficientComplex R M) n] :
    CommSq (X.homologyπ n ⊗ₘ 𝟙 M) (homologyTensorCycleMap R X M n)
      (homologyTensorComparison R X M n)
      ((X ⊗ coefficientComplex R M).homologyπ n) :=
  by
  refine ⟨?_⟩
  -- Compare after postcomposing with the concrete target homology model, then cancel the
  -- target homology isomorphism.
  apply (cancel_mono (((X ⊗ coefficientComplex R M).sc n).moduleCatHomologyIso.hom)).1
  simpa [Category.assoc] using
    homologyTensorComparison_spec_moduleCat R X M n
