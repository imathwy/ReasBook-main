import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Definition_17_3_2
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

noncomputable section

open CategoryTheory MonoidalCategory

universe u

-- Semantic recall via `lean_leansearch`: no dedicated mathlib Kronecker-pairing owner surfaced
-- for this setting, so this file records the source-facing induced morphism directly.

/-- The cocycle-level map underlying `kroneckerPairing`, sending a cocycle in `Hom(X, M)` to the
induced morphism `H_n(X) ⟶ M`. -/
theorem kroneckerCocycleToHom_desc_zero
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ)
    (φ : ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.K) :
    (X.sc n).moduleCatLeftHomologyData.f' ≫
        ModuleCat.ofHom
          ((ModuleCat.Hom.hom φ.1).comp
            (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)) =
      0 := by
  -- Evaluate the composite on a boundary and rewrite it as the cocycle condition for `φ`.
  apply ModuleCat.hom_ext
  ext x
  simpa [homCochainComplex, CategoryTheory.Linear.leftComp_apply] using
    congrArg (fun f => ModuleCat.Hom.hom f x) φ.2

/-- Additivity of the cocycle-level Kronecker map in the cocycle representative. -/
theorem kroneckerCocycleToHom_map_add
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ)
    (φ ψ : ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.K) :
    (X.sc n).moduleCatHomologyIso.hom ≫
        (X.sc n).moduleCatLeftHomologyData.descH
          (ModuleCat.ofHom
            ((ModuleCat.Hom.hom (φ + ψ).1).comp
              (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)))
          (kroneckerCocycleToHom_desc_zero R X M n (φ + ψ)) =
      ((X.sc n).moduleCatHomologyIso.hom ≫
          (X.sc n).moduleCatLeftHomologyData.descH
            (ModuleCat.ofHom
              ((ModuleCat.Hom.hom φ.1).comp
                (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)))
            (kroneckerCocycleToHom_desc_zero R X M n φ)) +
        ((X.sc n).moduleCatHomologyIso.hom ≫
          (X.sc n).moduleCatLeftHomologyData.descH
            (ModuleCat.ofHom
              ((ModuleCat.Hom.hom ψ.1).comp
                (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)))
            (kroneckerCocycleToHom_desc_zero R X M n ψ)) := by
  -- Normalize the sum on the right so both sides share the homology isomorphism.
  rw [← Preadditive.comp_add]
  rw [cancel_epi (X.sc n).moduleCatHomologyIso.hom]
  -- Compare the descended maps after precomposing with the quotient map from cycles.
  apply (cancel_epi (X.sc n).moduleCatLeftHomologyData.π).1
  simp only [CategoryTheory.ShortComplex.LeftHomologyData.π_descH]
  -- On cycle representatives, additivity is definitionally the additivity of the cocycle value.
  apply ModuleCat.hom_ext
  ext β
  rfl

/-- Compatibility of the cocycle-level Kronecker map with integer scalar multiplication. -/
theorem kroneckerCocycleToHom_map_zsmul
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ)
    (m : ℤ) (φ : ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.K) :
    (X.sc n).moduleCatHomologyIso.hom ≫
        (X.sc n).moduleCatLeftHomologyData.descH
          (ModuleCat.ofHom
            ((ModuleCat.Hom.hom (m • φ).1).comp
              (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)))
          (kroneckerCocycleToHom_desc_zero R X M n (m • φ)) =
      m •
        ((X.sc n).moduleCatHomologyIso.hom ≫
          (X.sc n).moduleCatLeftHomologyData.descH
            (ModuleCat.ofHom
              ((ModuleCat.Hom.hom φ.1).comp
                (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)))
            (kroneckerCocycleToHom_desc_zero R X M n φ)) := by
  -- Normalize the scalar on the right so both sides share the homology isomorphism.
  rw [← Linear.comp_smul]
  rw [cancel_epi (X.sc n).moduleCatHomologyIso.hom]
  -- Compare the descended maps after precomposing with the quotient map from cycles.
  apply (cancel_epi (X.sc n).moduleCatLeftHomologyData.π).1
  simp only [CategoryTheory.ShortComplex.LeftHomologyData.π_descH]
  -- On cycle representatives, scalar compatibility is definitionally the scalar action on cocycles.
  apply ModuleCat.hom_ext
  ext β
  rfl

/-- The cocycle-level map sending a cocycle in `Hom(X, M)` to the induced morphism
`H_n(X) ⟶ M`. -/
noncomputable def kroneckerCocycleToHom
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.K ⟶
      ModuleCat.of ℤ (X.homology n ⟶ M) :=
  ModuleCat.ofHom
    { toFun := fun φ ↦
        (X.sc n).moduleCatHomologyIso.hom ≫
          (X.sc n).moduleCatLeftHomologyData.descH
            (ModuleCat.ofHom
              ((ModuleCat.Hom.hom φ.1).comp
                (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)))
            (kroneckerCocycleToHom_desc_zero R X M n φ)
      map_add' := kroneckerCocycleToHom_map_add R X M n
      map_smul' := kroneckerCocycleToHom_map_zsmul R X M n }

/-- Helper for Construction 17.3.3: composing `kroneckerCocycleToHom` with `X.homologyπ n`
recovers evaluation on cycle representatives. -/
theorem homologyπ_kroneckerCocycleToHom
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ)
    (φ : ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.K) :
    X.homologyπ n ≫ kroneckerCocycleToHom R X M n φ =
      (X.sc n).moduleCatCyclesIso.hom ≫
        ModuleCat.ofHom
          ((ModuleCat.Hom.hom φ.1).comp
            (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)) := by
  -- Route correction: rewrite the quotient comparison through the explicit cycles and descH maps.
  change
    (X.homologyπ n) ≫
        ((X.sc n).moduleCatHomologyIso.hom ≫
          (X.sc n).moduleCatLeftHomologyData.descH
            (ModuleCat.ofHom
              ((ModuleCat.Hom.hom φ.1).comp
                (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)))
            (kroneckerCocycleToHom_desc_zero R X M n φ)) =
      (X.sc n).moduleCatCyclesIso.hom ≫
        ModuleCat.ofHom
          ((ModuleCat.Hom.hom φ.1).comp
            (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i))
  -- First move from abstract homology to the concrete cycles quotient.
  have hquot :
      (X.homologyπ n) ≫
          ((X.sc n).moduleCatHomologyIso.hom ≫
            (X.sc n).moduleCatLeftHomologyData.descH
              (ModuleCat.ofHom
                ((ModuleCat.Hom.hom φ.1).comp
                  (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)))
              (kroneckerCocycleToHom_desc_zero R X M n φ)) =
        (X.sc n).moduleCatCyclesIso.hom ≫
          (X.sc n).moduleCatLeftHomologyData.π ≫
            (X.sc n).moduleCatLeftHomologyData.descH
              (ModuleCat.ofHom
                ((ModuleCat.Hom.hom φ.1).comp
                  (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)))
              (kroneckerCocycleToHom_desc_zero R X M n φ) := by
    simpa [Category.assoc] using
      congrArg
        (fun f => f ≫
          (X.sc n).moduleCatLeftHomologyData.descH
            (ModuleCat.ofHom
              ((ModuleCat.Hom.hom φ.1).comp
                (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)))
            (kroneckerCocycleToHom_desc_zero R X M n φ))
        (CategoryTheory.ShortComplex.π_moduleCatCyclesIso_hom (S := X.sc n))
  -- Then use the cokernel-descending property of `descH`.
  have hdesc :
      (X.sc n).moduleCatCyclesIso.hom ≫
          (X.sc n).moduleCatLeftHomologyData.π ≫
            (X.sc n).moduleCatLeftHomologyData.descH
              (ModuleCat.ofHom
                ((ModuleCat.Hom.hom φ.1).comp
                  (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)))
              (kroneckerCocycleToHom_desc_zero R X M n φ) =
        (X.sc n).moduleCatCyclesIso.hom ≫
          ModuleCat.ofHom
            ((ModuleCat.Hom.hom φ.1).comp
              (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)) := by
    simpa [Category.assoc] using
      congrArg
        (fun f => (X.sc n).moduleCatCyclesIso.hom ≫ f)
        (CategoryTheory.ShortComplex.LeftHomologyData.π_descH
          (h := (X.sc n).moduleCatLeftHomologyData)
          (k := ModuleCat.ofHom
            ((ModuleCat.Hom.hom φ.1).comp
              (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)))
          (hk := kroneckerCocycleToHom_desc_zero R X M n φ))
  exact hquot.trans hdesc

/-- The cocycle-level Kronecker map kills coboundaries, so it descends to cohomology. -/
theorem kroneckerCocycleToHom_boundary_zero
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.f' ≫
        kroneckerCocycleToHom R X M n =
      0 := by
  -- Evaluate a coboundary class on a homology class by choosing a cycle representative.
  apply ModuleCat.hom_ext
  ext ψ β
  obtain ⟨γ, rfl⟩ := (ModuleCat.epi_iff_surjective (X.homologyπ n)).mp inferInstance β
  -- Rewrite the chosen coboundary representative as precomposition by `X.d n (n - 1)`.
  have hboundary :
      ModuleCat.Hom.hom
          ((((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.f' ψ).1)
          ((X.iCycles n) γ) =
        ModuleCat.Hom.hom ψ (((X.sc n).g) ((X.iCycles n) γ)) := by
    have hcochain :=
      congrArg
        (fun f => ModuleCat.Hom.hom f ((X.iCycles n) γ))
        (congrArg
          (fun k => k ψ)
          (((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.f'_i))
    simpa [homCochainComplex, CategoryTheory.Linear.leftComp_apply] using hcochain
  -- Cycles are killed by the outgoing differential.
  have hcycle : ((X.sc n).g) ((X.iCycles n) γ) = 0 := by
    simpa using congrArg (fun f => ModuleCat.Hom.hom f γ) ((X.sc n).iCycles_g)
  -- Normalize evaluation on homology classes back to evaluation on cycle representatives.
  have hfirst :
      ModuleCat.Hom.hom
          (kroneckerCocycleToHom R X M n
            (((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.f' ψ))
          ((X.homologyπ n) γ) =
        ModuleCat.Hom.hom
          ((((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.f' ψ).1)
          ((X.iCycles n) γ) := by
    -- The new bridge theorem packages the quotient normalization needed for evaluation.
    have hcomp :
        (X.homologyπ n) ≫
            kroneckerCocycleToHom R X M n
              (((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.f' ψ) =
          (X.sc n).moduleCatCyclesIso.hom ≫
            ModuleCat.ofHom
              ((ModuleCat.Hom.hom
                  ((((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.f' ψ).1)).comp
                (ModuleCat.Hom.hom (X.sc n).moduleCatLeftHomologyData.i)) :=
      homologyπ_kroneckerCocycleToHom R X M n
        (((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.f' ψ)
    simpa using congrArg (fun f => ModuleCat.Hom.hom f γ) hcomp
  calc
    ModuleCat.Hom.hom
        (kroneckerCocycleToHom R X M n
          (((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.f' ψ))
        ((X.homologyπ n) γ) =
      ModuleCat.Hom.hom
        ((((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.f' ψ).1)
        ((X.iCycles n) γ) := hfirst
    _ = ModuleCat.Hom.hom ψ (((X.sc n).g) ((X.iCycles n) γ)) := hboundary
    _ = 0 := by
        rw [hcycle]
        exact (ModuleCat.Hom.hom ψ).map_zero

/-- The cohomology-level morphism underlying Construction 17.3.3, obtained by descending
`kroneckerCocycleToHom` along the quotient from cocycles to cohomology. -/
noncomputable def kroneckerPairingDesc
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.H ⟶
      ModuleCat.of ℤ (X.homology n ⟶ M) :=
  ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.descH
    (kroneckerCocycleToHom R X M n)
    (kroneckerCocycleToHom_boundary_zero R X M n)

/-- The curried morphism associated to Construction 17.3.3, landing in
`ModuleCat.of ℤ (X.homology n ⟶ M)`. -/
noncomputable def kroneckerPairing (R : Type u) [Ring R]
    (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    cohomologyWithCoefficients R X M n ⟶ ModuleCat.of ℤ (X.homology n ⟶ M) :=
  ((homCochainComplex R X M).sc n).moduleCatHomologyIso.hom ≫
    kroneckerPairingDesc R X M n

/-- Additivity of the linear map underlying `kroneckerPairingBilinear`. -/
theorem kroneckerPairingBilinear_map_add
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ)
    (α γ : cohomologyWithCoefficients R X M n) :
    ((kroneckerPairing R X M n).hom (α + γ)).hom.restrictScalars ℤ =
      (((kroneckerPairing R X M n).hom α).hom.restrictScalars ℤ) +
        (((kroneckerPairing R X M n).hom γ).hom.restrictScalars ℤ) := by
  -- This is the underlying additivity of the linear map `kroneckerPairing`.
  simpa using
    congrArg (fun f : X.homology n ⟶ M => f.hom.restrictScalars ℤ)
      ((kroneckerPairing R X M n).hom.map_add α γ)

/-- Integer-scalar compatibility of the linear map underlying `kroneckerPairingBilinear`. -/
theorem kroneckerPairingBilinear_map_zsmul
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ)
    (m : ℤ) (x : cohomologyWithCoefficients R X M n) :
    ((kroneckerPairing R X M n).hom
        ((cohomologyWithCoefficients R X M n).isModule.smul m x)).hom.restrictScalars ℤ =
      (RingHom.id ℤ) m • ((kroneckerPairing R X M n).hom x).hom.restrictScalars ℤ := by
  -- This is the underlying scalar compatibility of the linear map `kroneckerPairing`.
  simpa using
    congrArg (fun f : X.homology n ⟶ M => f.hom.restrictScalars ℤ)
      ((kroneckerPairing R X M n).hom.map_smul m x)

/-- The bilinear map whose tensor-product uncurry is the source-facing Kronecker pairing. -/
noncomputable def kroneckerPairingBilinear
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    cohomologyWithCoefficients R X M n →ₗ[ℤ]
      ModuleCat.of ℤ (X.homology n) →ₗ[ℤ] ModuleCat.of ℤ M :=
  { toFun := fun α ↦
      ((kroneckerPairing R X M n).hom α).hom.restrictScalars ℤ
    map_add' := kroneckerPairingBilinear_map_add R X M n
    map_smul' := kroneckerPairingBilinear_map_zsmul R X M n }

/-- Construction 17.3.3. The evaluation pairing `Hom(X, M) ⊗ X ⟶ M` induces a Kronecker pairing
`H^n(X; M) ⊗ H_n(X) ⟶ M`, formalized here on the tensor-product side over the underlying
`ℤ`-modules. -/
noncomputable def kroneckerTensorPairing
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    ModuleCat.of ℤ (TensorProduct ℤ (cohomologyWithCoefficients R X M n) (X.homology n)) ⟶
      ModuleCat.of ℤ M :=
  ModuleCat.ofHom <|
    TensorProduct.uncurry (.id ℤ)
      (cohomologyWithCoefficients R X M n)
      (ModuleCat.of ℤ (X.homology n))
      (ModuleCat.of ℤ M)
      (kroneckerPairingBilinear R X M n)

/-- Evaluating `kroneckerTensorPairing` on a pure tensor recovers the value of the curried
Kronecker map on the corresponding cohomology and homology classes. -/
theorem kroneckerTensorPairing_tmul
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ)
    (α : cohomologyWithCoefficients R X M n) (β : ModuleCat.of ℤ (X.homology n)) :
    kroneckerTensorPairing R X M n (α ⊗ₜ[ℤ] β) =
      (((kroneckerPairing R X M n).hom α).hom.restrictScalars ℤ) β := by
  -- Uncurry recovers the original bilinear map on pure tensors.
  rfl

/-- Composing the quotient map from cocycles to cohomology with `kroneckerPairing` recovers the
descended cocycle-level Kronecker map. -/
theorem homologyπ_kroneckerPairing
    (R : Type u) [Ring R] (X : ChainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    (homCochainComplex R X M).homologyπ n ≫ kroneckerPairing R X M n =
      ((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom ≫
        kroneckerCocycleToHom R X M n := by
  -- Rewrite the cohomology quotient through the concrete cycles/homology interface.
  calc
    (homCochainComplex R X M).homologyπ n ≫ kroneckerPairing R X M n =
        (homCochainComplex R X M).homologyπ n ≫
          ((homCochainComplex R X M).sc n).moduleCatHomologyIso.hom ≫
            kroneckerPairingDesc R X M n := by
      rfl
    _ =
        ((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom ≫
          ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData.π ≫
            kroneckerPairingDesc R X M n := by
      simpa [Category.assoc] using
        congrArg
          (fun f => f ≫ kroneckerPairingDesc R X M n)
          (CategoryTheory.ShortComplex.π_moduleCatCyclesIso_hom
            (S := (homCochainComplex R X M).sc n))
    _ =
        ((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom ≫
          kroneckerCocycleToHom R X M n := by
      -- Descend from cocycles to cohomology using the cokernel property of `descH`.
      simpa [kroneckerPairingDesc, Category.assoc] using
        congrArg
          (fun f => ((homCochainComplex R X M).sc n).moduleCatCyclesIso.hom ≫ f)
          (CategoryTheory.ShortComplex.LeftHomologyData.π_descH
            (h := ((homCochainComplex R X M).sc n).moduleCatLeftHomologyData)
            (k := kroneckerCocycleToHom R X M n)
            (hk := kroneckerCocycleToHom_boundary_zero R X M n))
