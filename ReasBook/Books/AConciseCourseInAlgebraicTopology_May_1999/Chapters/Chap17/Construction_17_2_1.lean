import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.CommSq
import Mathlib.LinearAlgebra.TensorProduct.Quotient

open CategoryTheory MonoidalCategory HomologicalComplex
open scoped TensorProduct

universe u

-- Semantic recall: `lean_leansearch` surfaced `HomologicalComplex.tensorObj` as the canonical
-- tensor-product owner for chain complexes. No verified mathlib owner for the induced homology
-- cross product was found in the current environment, so this file records the source-faithful
-- degreewise map together with its specification; the quotient-model descent helpers remain
-- internal to this file.

variable {R : Type u} [CommRing R]
variable {X Y : ChainComplex (ModuleCat R) ℕ}
variable {p q : ℕ}

noncomputable section

variable [HomologicalComplex.HasHomology X p]
variable [HomologicalComplex.HasHomology Y q]
variable [HomologicalComplex.HasHomology (X ⊗ Y) (p + q)]

/-- Helper for Construction 17.2.1: the explicit `(p, q)` summand of the tensor of cycle
representatives is killed by the differential of `tensorObj X Y`. -/
private theorem chainComplexCycleRepresentativeTensor_d_eq_zero_explicit :
    ((X.iCycles p ⊗ₘ Y.iCycles q) ≫
        X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) p q (p + q) rfl) ≫
        (HomologicalComplex.tensorObj X Y).d (p + q) ((ComplexShape.down ℕ).next (p + q)) =
      0 := by
  -- Expand the tensor differential into its two summands coming from `X` and `Y`.
  rw [HomologicalComplex.mapBifunctor.d_eq X Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
    (p + q) ((ComplexShape.down ℕ).next (p + q)), Preadditive.comp_add]
  have hD₁ :
      ((X.iCycles p ⊗ₘ Y.iCycles q) ≫
          X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) p q (p + q) rfl) ≫
        HomologicalComplex.mapBifunctor.D₁ X Y (curriedTensor (ModuleCat R))
          (ComplexShape.down ℕ) (p + q) ((ComplexShape.down ℕ).next (p + q)) =
      (X.iCycles p ⊗ₘ Y.iCycles q) ≫
        HomologicalComplex.mapBifunctor.d₁ X Y (curriedTensor (ModuleCat R))
          (ComplexShape.down ℕ) p q ((ComplexShape.down ℕ).next (p + q)) := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦ (X.iCycles p ⊗ₘ Y.iCycles q) ≫ f)
        (HomologicalComplex.mapBifunctor.ι_D₁ X Y (curriedTensor (ModuleCat R))
          (ComplexShape.down ℕ) (p + q) ((ComplexShape.down ℕ).next (p + q)) p q rfl)
  have hD₂ :
      ((X.iCycles p ⊗ₘ Y.iCycles q) ≫
          X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) p q (p + q) rfl) ≫
        HomologicalComplex.mapBifunctor.D₂ X Y (curriedTensor (ModuleCat R))
          (ComplexShape.down ℕ) (p + q) ((ComplexShape.down ℕ).next (p + q)) =
      (X.iCycles p ⊗ₘ Y.iCycles q) ≫
        HomologicalComplex.mapBifunctor.d₂ X Y (curriedTensor (ModuleCat R))
          (ComplexShape.down ℕ) p q ((ComplexShape.down ℕ).next (p + q)) := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦ (X.iCycles p ⊗ₘ Y.iCycles q) ≫ f)
        (HomologicalComplex.mapBifunctor.ι_D₂ X Y (curriedTensor (ModuleCat R))
          (ComplexShape.down ℕ) (p + q) ((ComplexShape.down ℕ).next (p + q)) p q rfl)
  rw [hD₁, hD₂]
  have hleft :
      (X.iCycles p ⊗ₘ Y.iCycles q) ≫
        HomologicalComplex.mapBifunctor.d₁ X Y (curriedTensor (ModuleCat R))
          (ComplexShape.down ℕ) p q ((ComplexShape.down ℕ).next (p + q)) = 0 := by
    by_cases hp : (ComplexShape.down ℕ).Rel p ((ComplexShape.down ℕ).next p)
    · have hp_eq : ((ComplexShape.down ℕ).next p) + 1 = p := by
        simpa [ComplexShape.down_Rel] using hp
      have hpq : (ComplexShape.down ℕ).Rel (p + q) ((ComplexShape.down ℕ).next p + q) := by
        simpa [ComplexShape.down_Rel, add_assoc, Nat.add_left_comm, Nat.add_comm] using
          congrArg (fun t ↦ t + q) hp_eq
      have hpq_eq : (ComplexShape.down ℕ).next p + q = (ComplexShape.down ℕ).next (p + q) := by
        symm
        exact ComplexShape.next_eq' (ComplexShape.down ℕ) hpq
      -- Rewrite the `X`-boundary contribution and absorb it into the cycle equation for `X`.
      rw [HomologicalComplex.mapBifunctor.d₁_eq X Y (curriedTensor (ModuleCat R))
        (ComplexShape.down ℕ) hp q ((ComplexShape.down ℕ).next (p + q)) hpq_eq]
      have hmap :
          ((curriedTensor (ModuleCat R)).map (X.d p ((ComplexShape.down ℕ).next p))).app
              (Y.X q) =
            X.d p ((ComplexShape.down ℕ).next p) ▷ Y.X q := rfl
      rw [hmap]
      have hcomp :
          (X.iCycles p ⊗ₘ Y.iCycles q) ≫ (X.d p ((ComplexShape.down ℕ).next p) ▷ Y.X q) =
            (X.iCycles p ≫ X.d p ((ComplexShape.down ℕ).next p)) ⊗ₘ Y.iCycles q := by
        simpa using tensorHom_comp_whiskerRight (f := X.iCycles p)
          (g := X.d p ((ComplexShape.down ℕ).next p)) (h := Y.iCycles q)
      have hcomp_assoc :
          (X.iCycles p ⊗ₘ Y.iCycles q) ≫ (X.d p ((ComplexShape.down ℕ).next p) ▷ Y.X q) ≫
              X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                ((ComplexShape.down ℕ).next p) q ((ComplexShape.down ℕ).next (p + q)) hpq_eq =
            ((X.iCycles p ≫ X.d p ((ComplexShape.down ℕ).next p)) ⊗ₘ Y.iCycles q) ≫
              X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                ((ComplexShape.down ℕ).next p) q ((ComplexShape.down ℕ).next (p + q)) hpq_eq := by
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ f ≫
              X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                ((ComplexShape.down ℕ).next p) q ((ComplexShape.down ℕ).next (p + q)) hpq_eq)
            hcomp
      have hinner :
          (X.iCycles p ⊗ₘ Y.iCycles q) ≫ (X.d p ((ComplexShape.down ℕ).next p) ▷ Y.X q) ≫
              X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                ((ComplexShape.down ℕ).next p) q ((ComplexShape.down ℕ).next (p + q)) hpq_eq =
            0 := by
        rw [hcomp_assoc]
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ (f ⊗ₘ Y.iCycles q) ≫
              X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                ((ComplexShape.down ℕ).next p) q ((ComplexShape.down ℕ).next (p + q)) hpq_eq)
            (X.iCycles_d p ((ComplexShape.down ℕ).next p))
      have hsmul :
          (X.iCycles p ⊗ₘ Y.iCycles q) ≫
            (ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, q) • ((X.d p ((ComplexShape.down ℕ).next p) ▷ Y.X q) ≫
                X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                  ((ComplexShape.down ℕ).next p) q ((ComplexShape.down ℕ).next (p + q))
                    hpq_eq)) =
            ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, q) •
              ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ (X.d p ((ComplexShape.down ℕ).next p) ▷ Y.X q) ≫
                X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                  ((ComplexShape.down ℕ).next p) q ((ComplexShape.down ℕ).next (p + q))
                    hpq_eq) := by
        apply ModuleCat.hom_ext
        ext x
        rfl
      calc
        (X.iCycles p ⊗ₘ Y.iCycles q) ≫
            (ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, q) • ((X.d p ((ComplexShape.down ℕ).next p) ▷ Y.X q) ≫
                X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                  ((ComplexShape.down ℕ).next p) q ((ComplexShape.down ℕ).next (p + q))
                    hpq_eq)) =
          ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (p, q) •
            ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ (X.d p ((ComplexShape.down ℕ).next p) ▷ Y.X q) ≫
              X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                ((ComplexShape.down ℕ).next p) q ((ComplexShape.down ℕ).next (p + q))
                  hpq_eq) := hsmul
        _ = 0 := by
            rw [hinner, smul_zero]
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero X Y (curriedTensor (ModuleCat R))
        (ComplexShape.down ℕ) p q ((ComplexShape.down ℕ).next (p + q)) hp]
      exact CategoryTheory.Limits.comp_zero
  have hright :
      (X.iCycles p ⊗ₘ Y.iCycles q) ≫
        HomologicalComplex.mapBifunctor.d₂ X Y (curriedTensor (ModuleCat R))
          (ComplexShape.down ℕ) p q ((ComplexShape.down ℕ).next (p + q)) = 0 := by
    by_cases hq : (ComplexShape.down ℕ).Rel q ((ComplexShape.down ℕ).next q)
    · have hq_eq : ((ComplexShape.down ℕ).next q) + 1 = q := by
        simpa [ComplexShape.down_Rel] using hq
      have hpq : (ComplexShape.down ℕ).Rel (p + q) (p + (ComplexShape.down ℕ).next q) := by
        simpa [ComplexShape.down_Rel, add_assoc, Nat.add_left_comm, Nat.add_comm] using
          congrArg (fun t ↦ p + t) hq_eq
      have hpq_eq : p + (ComplexShape.down ℕ).next q = (ComplexShape.down ℕ).next (p + q) := by
        symm
        exact ComplexShape.next_eq' (ComplexShape.down ℕ) hpq
      -- Rewrite the `Y`-boundary contribution and absorb it into the cycle equation for `Y`.
      rw [HomologicalComplex.mapBifunctor.d₂_eq X Y (curriedTensor (ModuleCat R))
        (ComplexShape.down ℕ) p hq ((ComplexShape.down ℕ).next (p + q)) hpq_eq]
      have hmap :
          ((curriedTensor (ModuleCat R)).obj (X.X p)).map (Y.d q ((ComplexShape.down ℕ).next q)) =
            X.X p ◁ Y.d q ((ComplexShape.down ℕ).next q) := rfl
      rw [hmap]
      have hcomp :
          (X.iCycles p ⊗ₘ Y.iCycles q) ≫ (X.X p ◁ Y.d q ((ComplexShape.down ℕ).next q)) =
            X.iCycles p ⊗ₘ (Y.iCycles q ≫ Y.d q ((ComplexShape.down ℕ).next q)) := by
        simpa using tensorHom_comp_whiskerLeft (f := X.iCycles p)
          (g := Y.iCycles q) (h := Y.d q ((ComplexShape.down ℕ).next q))
      have hcomp_assoc :
          (X.iCycles p ⊗ₘ Y.iCycles q) ≫ (X.X p ◁ Y.d q ((ComplexShape.down ℕ).next q)) ≫
              X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                p ((ComplexShape.down ℕ).next q) ((ComplexShape.down ℕ).next (p + q)) hpq_eq =
            (X.iCycles p ⊗ₘ (Y.iCycles q ≫ Y.d q ((ComplexShape.down ℕ).next q))) ≫
              X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                p ((ComplexShape.down ℕ).next q) ((ComplexShape.down ℕ).next (p + q)) hpq_eq := by
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ f ≫
              X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                p ((ComplexShape.down ℕ).next q) ((ComplexShape.down ℕ).next (p + q)) hpq_eq)
            hcomp
      have hinner :
          (X.iCycles p ⊗ₘ Y.iCycles q) ≫ (X.X p ◁ Y.d q ((ComplexShape.down ℕ).next q)) ≫
              X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                p ((ComplexShape.down ℕ).next q) ((ComplexShape.down ℕ).next (p + q)) hpq_eq =
            0 := by
        rw [hcomp_assoc]
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ (X.iCycles p ⊗ₘ f) ≫
              X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                p ((ComplexShape.down ℕ).next q) ((ComplexShape.down ℕ).next (p + q)) hpq_eq)
            (Y.iCycles_d q ((ComplexShape.down ℕ).next q))
      have hsmul :
          (X.iCycles p ⊗ₘ Y.iCycles q) ≫
            (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, q) • ((X.X p ◁ Y.d q ((ComplexShape.down ℕ).next q)) ≫
                X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                  p ((ComplexShape.down ℕ).next q) ((ComplexShape.down ℕ).next (p + q))
                    hpq_eq)) =
            ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, q) •
              ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ (X.X p ◁ Y.d q ((ComplexShape.down ℕ).next q)) ≫
                X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                  p ((ComplexShape.down ℕ).next q) ((ComplexShape.down ℕ).next (p + q))
                    hpq_eq) := by
        apply ModuleCat.hom_ext
        ext x
        rfl
      calc
        (X.iCycles p ⊗ₘ Y.iCycles q) ≫
            (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, q) • ((X.X p ◁ Y.d q ((ComplexShape.down ℕ).next q)) ≫
                X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                  p ((ComplexShape.down ℕ).next q) ((ComplexShape.down ℕ).next (p + q))
                    hpq_eq)) =
          ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (p, q) •
            ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ (X.X p ◁ Y.d q ((ComplexShape.down ℕ).next q)) ≫
              X.ιMapBifunctor Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                p ((ComplexShape.down ℕ).next q) ((ComplexShape.down ℕ).next (p + q))
                  hpq_eq) := hsmul
        _ = 0 := by
            rw [hinner, smul_zero]
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero X Y (curriedTensor (ModuleCat R))
        (ComplexShape.down ℕ) p q ((ComplexShape.down ℕ).next (p + q)) hq]
      exact CategoryTheory.Limits.comp_zero
  rw [hleft, hright, zero_add]

private theorem chainComplexCycleRepresentativeTensor_d_eq_zero :
    ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl) ≫
        (X ⊗ Y).d (p + q) ((ComplexShape.down ℕ).next (p + q)) =
      0 := by
  -- The explicit `ιMapBifunctor` statement above matches the tensor-differential API.
  simpa [HomologicalComplex.ιTensorObj] using
    chainComplexCycleRepresentativeTensor_d_eq_zero_explicit

/-- The cycles-level cross product obtained by tensoring cycle representatives. -/
noncomputable def chainComplexCycleCrossProduct
    : X.cycles p ⊗ Y.cycles q ⟶ (X ⊗ Y).cycles (p + q) :=
  (X ⊗ Y).liftCycles
    ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl)
    ((ComplexShape.down ℕ).next (p + q))
    rfl
    chainComplexCycleRepresentativeTensor_d_eq_zero

/-- The cycles-level cross product includes into `(X ⊗ Y).X (p + q)` as the evident tensor of
cycle inclusions followed by the `(p, q)` summand inclusion. -/
theorem chainComplexCycleCrossProduct_iCycles :
    CommSq (X.iCycles p ⊗ₘ Y.iCycles q) chainComplexCycleCrossProduct
      (ιTensorObj X Y p q (p + q) rfl) ((X ⊗ Y).iCycles (p + q)) := by
  -- The defining property of `liftCycles` recovers the chosen cycle representative map.
  refine ⟨?_⟩
  simpa [chainComplexCycleCrossProduct] using
    (HomologicalComplex.liftCycles_i (K := X ⊗ Y)
      ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl)
      ((ComplexShape.down ℕ).next (p + q))
      rfl
      chainComplexCycleRepresentativeTensor_d_eq_zero)

/-- The tensor of cycle representatives, viewed on the concrete kernel models for
`X.cycles p` and `Y.cycles q`, followed by the quotient map to `H_{p + q}(X ⊗ Y)`. -/
private noncomputable def chainComplexKernelCrossProductToHomologyLinear :
    (X.sc p).moduleCatLeftHomologyData.K ⊗[R] (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
      ((X ⊗ Y).sc (p + q)).moduleCatLeftHomologyData.H :=
  ((((X.sc p).moduleCatCyclesIso.inv ⊗ₘ (Y.sc q).moduleCatCyclesIso.inv) ≫
      chainComplexCycleCrossProduct ≫
      (X ⊗ Y).homologyπ (p + q) ≫
      ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom).hom)

/-- Helper for Construction 17.2.1: the concrete boundary map in degree `n`, followed by the
cycles identification on `K.sc n`, is the canonical `toCycles` map. -/
private theorem moduleCatLeftHomologyData_f'_moduleCatCyclesIso_inv
    (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology K n] :
    (K.sc n).moduleCatLeftHomologyData.f' ≫ (K.sc n).moduleCatCyclesIso.inv =
      K.toCycles ((ComplexShape.down ℕ).prev n) n := by
  -- Compare both descriptions after postcomposing with the cycle inclusion.
  simpa [Category.assoc] using
    (congrArg (fun f ↦ f ≫ (K.sc n).moduleCatCyclesIso.inv)
      (CategoryTheory.ShortComplex.toCycles_moduleCatCyclesIso_hom (S := K.sc n))).symm

/-- Helper for Construction 17.2.1: normalize the target quotient map in
`chainComplexKernelCrossProductToHomologyLinear` to the concrete `moduleCatLeftHomologyData.π`
presentation. -/
private theorem chainComplexKernelCrossProductToHomologyLinear_eq_concreteProjection :
    chainComplexKernelCrossProductToHomologyLinear =
      ((((X.sc p).moduleCatCyclesIso.inv ⊗ₘ (Y.sc q).moduleCatCyclesIso.inv) ≫
          chainComplexCycleCrossProduct ≫
          ((X ⊗ Y).sc (p + q)).moduleCatCyclesIso.hom ≫
          ((X ⊗ Y).sc (p + q)).moduleCatLeftHomologyData.π).hom) := by
  -- Rewrite the target homology quotient through the concrete cycles quotient model.
  rw [chainComplexKernelCrossProductToHomologyLinear]
  congr 1
  exact congrArg
    (fun f ↦
      (((X.sc p).moduleCatCyclesIso.inv ⊗ₘ (Y.sc q).moduleCatCyclesIso.inv) ≫
        chainComplexCycleCrossProduct) ≫ f)
    (CategoryTheory.ShortComplex.π_moduleCatCyclesIso_hom (S := (X ⊗ Y).sc (p + q)))

/-- Helper for Construction 17.2.1: the concrete left boundary input becomes the actual
differential `X.d ((ComplexShape.down ℕ).prev p) p` after returning from the cycles model. -/
private theorem leftBoundarySourceCyclesIso_inv_iCycles :
    (X.sc p).moduleCatLeftHomologyData.f' ≫ (X.sc p).moduleCatCyclesIso.inv ≫ X.iCycles p =
      X.d ((ComplexShape.down ℕ).prev p) p := by
  -- Rewrite the concrete quotient-model boundary map to `X.toCycles`, then recover the actual
  -- chain differential by composing with `X.iCycles p`.
  simpa [Category.assoc] using
    congrArg
      (fun f ↦ f ≫ X.iCycles p)
      (moduleCatLeftHomologyData_f'_moduleCatCyclesIso_inv (K := X) (n := p))

/-- Helper for Construction 17.2.1: the concrete right boundary input becomes the actual
differential `Y.d ((ComplexShape.down ℕ).prev q) q` after returning from the cycles model. -/
private theorem rightBoundarySourceCyclesIso_inv_iCycles :
    (Y.sc q).moduleCatLeftHomologyData.f' ≫ (Y.sc q).moduleCatCyclesIso.inv ≫ Y.iCycles q =
      Y.d ((ComplexShape.down ℕ).prev q) q := by
  -- The same cycles-model normalization on `Y` identifies the abstract boundary map with the
  -- chain differential landing in degree `q`.
  simpa [Category.assoc] using
    congrArg
      (fun f ↦ f ≫ Y.iCycles q)
      (moduleCatLeftHomologyData_f'_moduleCatCyclesIso_inv (K := Y) (n := q))

/-- Helper for Construction 17.2.1: normalize the left branch representative inside
`chainComplexCycleCrossProduct` before proving it is a boundary in `X ⊗ Y`. -/
private theorem leftBoundaryRepresentative_normalized :
    (((X.sc p).moduleCatLeftHomologyData.f' ≫ (X.sc p).moduleCatCyclesIso.inv) ⊗ₘ
        (Y.sc q).moduleCatCyclesIso.inv) ≫
      ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl) =
    (X.d ((ComplexShape.down ℕ).prev p) p ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
      ιTensorObj X Y p q (p + q) rfl := by
  -- Push the tensor composition across the pure tensor inclusion first.
  calc
    (((X.sc p).moduleCatLeftHomologyData.f' ≫ (X.sc p).moduleCatCyclesIso.inv) ⊗ₘ
        (Y.sc q).moduleCatCyclesIso.inv) ≫
        ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl) =
      ((((X.sc p).moduleCatLeftHomologyData.f' ≫ (X.sc p).moduleCatCyclesIso.inv) ⊗ₘ
          (Y.sc q).moduleCatCyclesIso.inv) ≫
          (X.iCycles p ⊗ₘ Y.iCycles q)) ≫
          ιTensorObj X Y p q (p + q) rfl := by
        simp [Category.assoc]
    -- Then identify both tensor factors with the concrete boundary/cycle inclusions.
    _ =
      (((X.sc p).moduleCatLeftHomologyData.f' ≫ (X.sc p).moduleCatCyclesIso.inv ≫
          X.iCycles p) ⊗ₘ
          ((Y.sc q).moduleCatCyclesIso.inv ≫ Y.iCycles q)) ≫
          ιTensorObj X Y p q (p + q) rfl := by
        simp [Category.assoc]
    _ =
      (X.d ((ComplexShape.down ℕ).prev p) p ⊗ₘ
          ((Y.sc q).moduleCatCyclesIso.inv ≫ Y.iCycles q)) ≫
          ιTensorObj X Y p q (p + q) rfl := by
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ (f ⊗ₘ ((Y.sc q).moduleCatCyclesIso.inv ≫ Y.iCycles q)) ≫
              ιTensorObj X Y p q (p + q) rfl)
            (leftBoundarySourceCyclesIso_inv_iCycles (X := X) (p := p))
    _ =
      (X.d ((ComplexShape.down ℕ).prev p) p ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
          ιTensorObj X Y p q (p + q) rfl := by
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ (X.d ((ComplexShape.down ℕ).prev p) p ⊗ₘ f) ≫
              ιTensorObj X Y p q (p + q) rfl)
            (CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_iCycles (S := Y.sc q))

/-- Helper for Construction 17.2.1: the concrete cycles inclusion on `K.sc n` is killed by the
outgoing differential in degree `n`. -/
private theorem moduleCatLeftHomologyData_i_d_eq_zero
    (K : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    [HomologicalComplex.HasHomology K n] :
    (K.sc n).moduleCatLeftHomologyData.i ≫
        K.d n ((ComplexShape.down ℕ).next n) =
      0 := by
  -- Rewrite the concrete cycles inclusion back to `K.iCycles`, where the standard cycle equation
  -- is available in the short-complex API.
  calc
    (K.sc n).moduleCatLeftHomologyData.i ≫ K.d n ((ComplexShape.down ℕ).next n) =
      (K.sc n).moduleCatCyclesIso.inv ≫ K.iCycles n ≫ K.d n ((ComplexShape.down ℕ).next n) := by
        simpa [Category.assoc] using
          (congrArg
            (fun f ↦ f ≫ K.d n ((ComplexShape.down ℕ).next n))
            (CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_iCycles (S := K.sc n))).symm
    _ = (K.sc n).moduleCatCyclesIso.inv ≫
          (K.iCycles n ≫ K.d n ((ComplexShape.down ℕ).next n)) := by
        simp
    _ = (K.sc n).moduleCatCyclesIso.inv ≫ 0 := by
        congr 1
        exact K.iCycles_d n ((ComplexShape.down ℕ).next n)
    _ = 0 := by
        rfl

/-- Helper for Construction 17.2.1: when `q` contributes a nonzero differential branch, the
`(prev p, next q)` summand lands in total degree `p + q`. -/
private theorem leftBoundaryPrevNext_eq
    (hq : (ComplexShape.down ℕ).Rel q ((ComplexShape.down ℕ).next q)) :
    (ComplexShape.down ℕ).prev p + (ComplexShape.down ℕ).next q = p + q := by
  -- Convert the shape relation on `q` to the arithmetic identity `next q + 1 = q`.
  have hq_eq : (ComplexShape.down ℕ).next q + 1 = q := by
    simpa [ComplexShape.down_Rel] using hq
  calc
    (ComplexShape.down ℕ).prev p + (ComplexShape.down ℕ).next q =
      (p + 1) + (ComplexShape.down ℕ).next q := by
        simp [ChainComplex.prev]
    _ = p + ((ComplexShape.down ℕ).next q + 1) := by omega
    _ = p + q := by rw [hq_eq]

/-- Helper for Construction 17.2.1: when `p` contributes a nonzero differential branch, the
`(next p, prev q)` summand lands in total degree `p + q`. -/
private theorem rightBoundaryNextPrev_eq
    (hp : (ComplexShape.down ℕ).Rel p ((ComplexShape.down ℕ).next p)) :
    (ComplexShape.down ℕ).next p + (ComplexShape.down ℕ).prev q = p + q := by
  -- Convert the shape relation on `p` to the arithmetic identity `next p + 1 = p`.
  have hp_eq : (ComplexShape.down ℕ).next p + 1 = p := by
    simpa [ComplexShape.down_Rel] using hp
  calc
    (ComplexShape.down ℕ).next p + (ComplexShape.down ℕ).prev q =
      (ComplexShape.down ℕ).next p + (q + 1) := by
        simp [ChainComplex.prev]
    _ = ((ComplexShape.down ℕ).next p + 1) + q := by omega
    _ = p + q := by rw [hp_eq]

/-- Helper for Construction 17.2.1: composing two `ℤ`-scaled morphisms multiplies the scalars. -/
private theorem zsmulCompZsmul {A B C : ModuleCat R} (n m : ℤ) (f : A ⟶ B) (g : B ⟶ C) :
    (n • f) ≫ (m • g) = (n * m) • (f ≫ g) := by
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul]

/-- Helper for Construction 17.2.1: the normalized left representative is the differential of the
explicit `(prev p, q)` summand map into `(X ⊗ Y).X ((ComplexShape.down ℕ).prev (p + q))`. -/
private theorem leftBoundaryRepresentative_eq_boundary
    (hprev : (ComplexShape.down ℕ).prev p + q = (ComplexShape.down ℕ).prev (p + q)) :
    (X.d ((ComplexShape.down ℕ).prev p) p ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
        ιTensorObj X Y p q (p + q) rfl =
      ((((𝟙 ((X.sc p).X₁)) ⊗ₘ
          (Y.sc q).moduleCatLeftHomologyData.i) ≫
          ιTensorObj X Y ((ComplexShape.down ℕ).prev p) q
            ((ComplexShape.down ℕ).prev (p + q)) hprev) ≫
        (X ⊗ Y).d ((ComplexShape.down ℕ).prev (p + q)) (p + q)) := by
  -- Expand the tensor differential at the `(prev p, q)` summand and keep only the `D₁` branch.
  change (X.d ((ComplexShape.down ℕ).prev p) p ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
        ιTensorObj X Y p q (p + q) rfl =
      ((((𝟙 ((X.sc p).X₁)) ⊗ₘ
            (Y.sc q).moduleCatLeftHomologyData.i) ≫
          ιTensorObj X Y ((ComplexShape.down ℕ).prev p) q
            ((ComplexShape.down ℕ).prev (p + q)) hprev) ≫
        (HomologicalComplex.tensorObj X Y).d ((ComplexShape.down ℕ).prev (p + q)) (p + q))
  simp_rw [Category.assoc]
  rw [HomologicalComplex.mapBifunctor.d_eq X Y (curriedTensor (ModuleCat R))
    (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q),
    Preadditive.comp_add, Preadditive.comp_add]
  have hp : (ComplexShape.down ℕ).Rel ((ComplexShape.down ℕ).prev p) p := by
    simp [ChainComplex.prev, ComplexShape.down_Rel]
  have hD₁ :
      ((((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
            ιTensorObj X Y ((ComplexShape.down ℕ).prev p) q
              ((ComplexShape.down ℕ).prev (p + q)) hprev) ≫
          HomologicalComplex.mapBifunctor.D₁ X Y (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q)) =
        (X.d ((ComplexShape.down ℕ).prev p) p ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
          ιTensorObj X Y p q (p + q) rfl := by
    have hι :
        ((((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
              ιTensorObj X Y ((ComplexShape.down ℕ).prev p) q
                ((ComplexShape.down ℕ).prev (p + q)) hprev) ≫
            HomologicalComplex.mapBifunctor.D₁ X Y (curriedTensor (ModuleCat R))
              (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q)) =
          (((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
            HomologicalComplex.mapBifunctor.d₁ X Y (curriedTensor (ModuleCat R))
              (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev p) q (p + q)) := by
      simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
        congrArg
          (fun f ↦ ((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫ f)
          (HomologicalComplex.mapBifunctor.ι_D₁ X Y (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q)
            ((ComplexShape.down ℕ).prev p) q hprev)
    rw [hι]
    rw [HomologicalComplex.mapBifunctor.d₁_eq X Y (curriedTensor (ModuleCat R))
      (ComplexShape.down ℕ) hp q (p + q) rfl]
    have hmap :
        ((curriedTensor (ModuleCat R)).map (X.d ((ComplexShape.down ℕ).prev p) p)).app (Y.X q) =
          X.d ((ComplexShape.down ℕ).prev p) p ▷ Y.X q := rfl
    rw [hmap]
    have hcomp :
        X.X ((ComplexShape.down ℕ).prev p) ◁ (Y.sc q).moduleCatLeftHomologyData.i ≫
            X.d ((ComplexShape.down ℕ).prev p) p ▷ Y.X q =
          X.d ((ComplexShape.down ℕ).prev p) p ⊗ₘ
            (Y.sc q).moduleCatLeftHomologyData.i := by
      simpa using tensorHom_comp_whiskerRight
        (f := 𝟙 ((X.sc p).X₁))
        (g := X.d ((ComplexShape.down ℕ).prev p) p)
        (h := (Y.sc q).moduleCatLeftHomologyData.i)
    calc
      ((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
          ((ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              ((ComplexShape.down ℕ).prev p, q) •
              (X.d ((ComplexShape.down ℕ).prev p) p ▷ Y.X q ≫
                ιMapBifunctor X Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) p q
                  (p + q) rfl))) =
        (((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
            X.d ((ComplexShape.down ℕ).prev p) p ▷ Y.X q) ≫
          ιMapBifunctor X Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) p q
            (p + q) rfl := by
          simp [Preadditive.comp_zsmul, Category.assoc]
      _ = ((X.d ((ComplexShape.down ℕ).prev p) p ⊗ₘ
            (Y.sc q).moduleCatLeftHomologyData.i)) ≫
          ιMapBifunctor X Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) p q
            (p + q) rfl := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦
                f ≫ ιMapBifunctor X Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ) p q
                  (p + q) rfl)
              hcomp
  have hD₂ :
      ((((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
            ιTensorObj X Y ((ComplexShape.down ℕ).prev p) q
              ((ComplexShape.down ℕ).prev (p + q)) hprev) ≫
          HomologicalComplex.mapBifunctor.D₂ X Y (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q)) =
        0 := by
    have hι :
        ((((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
              ιTensorObj X Y ((ComplexShape.down ℕ).prev p) q
                ((ComplexShape.down ℕ).prev (p + q)) hprev) ≫
            HomologicalComplex.mapBifunctor.D₂ X Y (curriedTensor (ModuleCat R))
              (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q)) =
          (((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
            HomologicalComplex.mapBifunctor.d₂ X Y (curriedTensor (ModuleCat R))
              (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev p) q (p + q)) := by
      simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
        congrArg
          (fun f ↦ ((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫ f)
          (HomologicalComplex.mapBifunctor.ι_D₂ X Y (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q)
            ((ComplexShape.down ℕ).prev p) q hprev)
    rw [hι]
    by_cases hq : (ComplexShape.down ℕ).Rel q ((ComplexShape.down ℕ).next q)
    · have hpq_eq : (ComplexShape.down ℕ).prev p + (ComplexShape.down ℕ).next q = p + q := by
        exact leftBoundaryPrevNext_eq (p := p) (q := q) hq
      rw [HomologicalComplex.mapBifunctor.d₂_eq X Y (curriedTensor (ModuleCat R))
        (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev p) hq (p + q) hpq_eq]
      have hmap :
          ((curriedTensor (ModuleCat R)).obj (X.X ((ComplexShape.down ℕ).prev p))).map
              (Y.d q ((ComplexShape.down ℕ).next q)) =
            X.X ((ComplexShape.down ℕ).prev p) ◁ Y.d q ((ComplexShape.down ℕ).next q) := rfl
      rw [hmap]
      have hcomp :
          ((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
              (X.X ((ComplexShape.down ℕ).prev p) ◁ Y.d q ((ComplexShape.down ℕ).next q)) =
            (𝟙 ((X.sc p).X₁)) ⊗ₘ
              ((Y.sc q).moduleCatLeftHomologyData.i ≫
                Y.d q ((ComplexShape.down ℕ).next q)) := by
        simpa using tensorHom_comp_whiskerLeft
          (f := 𝟙 ((X.sc p).X₁))
          (g := (Y.sc q).moduleCatLeftHomologyData.i)
          (h := Y.d q ((ComplexShape.down ℕ).next q))
      calc
        ((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
            ((ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                ((ComplexShape.down ℕ).prev p, q) •
                (X.X ((ComplexShape.down ℕ).prev p) ◁ Y.d q ((ComplexShape.down ℕ).next q) ≫
                  ιMapBifunctor X Y (curriedTensor (ModuleCat R)) (ComplexShape.down ℕ)
                    ((ComplexShape.down ℕ).prev p) ((ComplexShape.down ℕ).next q)
                    (p + q) hpq_eq))) =
          (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              ((ComplexShape.down ℕ).prev p, q)) •
            ((((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
                X.X ((ComplexShape.down ℕ).prev p) ◁ Y.d q ((ComplexShape.down ℕ).next q)) ≫
              ιTensorObj X Y ((ComplexShape.down ℕ).prev p) ((ComplexShape.down ℕ).next q)
                (p + q) hpq_eq) := by
            apply ModuleCat.hom_ext
            ext x
            rfl
        _ = (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              ((ComplexShape.down ℕ).prev p, q)) •
            (((𝟙 ((X.sc p).X₁)) ⊗ₘ
                ((Y.sc q).moduleCatLeftHomologyData.i ≫
                  Y.d q ((ComplexShape.down ℕ).next q))) ≫
              ιTensorObj X Y ((ComplexShape.down ℕ).prev p) ((ComplexShape.down ℕ).next q)
                (p + q) hpq_eq) := by
            congr 1
            simpa [Category.assoc] using
              congrArg
                (fun f ↦
                  f ≫ ιTensorObj X Y ((ComplexShape.down ℕ).prev p)
                    ((ComplexShape.down ℕ).next q) (p + q) hpq_eq)
                hcomp
        _ = (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              ((ComplexShape.down ℕ).prev p, q)) •
            (((𝟙 ((X.sc p).X₁)) ⊗ₘ 0) ≫
              ιTensorObj X Y ((ComplexShape.down ℕ).prev p) ((ComplexShape.down ℕ).next q)
                (p + q) hpq_eq) := by
            congr 1
            simpa [Category.assoc] using
              congrArg
                (fun f ↦
                  ((𝟙 ((X.sc p).X₁)) ⊗ₘ f) ≫
                    ιTensorObj X Y ((ComplexShape.down ℕ).prev p)
                      ((ComplexShape.down ℕ).next q) (p + q) hpq_eq)
                (moduleCatLeftHomologyData_i_d_eq_zero (K := Y) (n := q))
        _ = 0 := by
            rw [CategoryTheory.MonoidalPreadditive.tensor_zero, CategoryTheory.Limits.zero_comp,
              smul_zero]
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero X Y (curriedTensor (ModuleCat R))
        (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev p) q (p + q) hq]
      exact CategoryTheory.Limits.comp_zero
  have hD₁' :
      ((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
          ιTensorObj X Y ((ComplexShape.down ℕ).prev p) q
            ((ComplexShape.down ℕ).prev (p + q)) hprev ≫
          HomologicalComplex.mapBifunctor.D₁ X Y (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q) =
        (X.d ((ComplexShape.down ℕ).prev p) p ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
          ιTensorObj X Y p q (p + q) rfl := by
    simpa [Category.assoc] using hD₁
  have hD₂' :
      ((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
          ιTensorObj X Y ((ComplexShape.down ℕ).prev p) q
            ((ComplexShape.down ℕ).prev (p + q)) hprev ≫
          HomologicalComplex.mapBifunctor.D₂ X Y (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q) =
        0 := by
    simpa [Category.assoc] using hD₂
  rw [hD₁', hD₂']
  rw [add_zero]

private theorem leftBoundaryCrossProduct_homology_zero :
    (((X.sc p).moduleCatLeftHomologyData.f' ≫ (X.sc p).moduleCatCyclesIso.inv) ⊗ₘ
        (Y.sc q).moduleCatCyclesIso.inv) ≫
      chainComplexCycleCrossProduct ≫
      (X ⊗ Y).homologyπ (p + q) ≫
      ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom =
    0 := by
  -- Rewrite the precomposed cycle map as a lifted boundary, then apply the standard vanishing of
  -- boundaries in homology.
  have hprev : (ComplexShape.down ℕ).prev p + q = (ComplexShape.down ℕ).prev (p + q) := by
    simp [ChainComplex.prev]
    omega
  let α :=
    (((X.sc p).moduleCatLeftHomologyData.f' ≫ (X.sc p).moduleCatCyclesIso.inv) ⊗ₘ
      (Y.sc q).moduleCatCyclesIso.inv)
  let x :=
    ((((𝟙 ((X.sc p).X₁)) ⊗ₘ (Y.sc q).moduleCatLeftHomologyData.i) ≫
      ιTensorObj X Y ((ComplexShape.down ℕ).prev p) q
        ((ComplexShape.down ℕ).prev (p + q)) hprev))
  have hα :
      α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl) =
        x ≫ (X ⊗ Y).d ((ComplexShape.down ℕ).prev (p + q)) (p + q) := by
    rw [leftBoundaryRepresentative_normalized, leftBoundaryRepresentative_eq_boundary
      (X := X) (Y := Y) (p := p) (q := q) hprev]
  have hkprecomp :
      (α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl)) ≫
          (X ⊗ Y).d (p + q) ((ComplexShape.down ℕ).next (p + q)) =
        0 := by
    simpa [Category.assoc] using
      congrArg (fun f ↦ α ≫ f) chainComplexCycleRepresentativeTensor_d_eq_zero
  have hcomp :
      α ≫ chainComplexCycleCrossProduct =
        (X ⊗ Y).liftCycles
          (α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl))
          ((ComplexShape.down ℕ).next (p + q))
          rfl
          hkprecomp := by
    simpa [chainComplexCycleCrossProduct] using
      HomologicalComplex.comp_liftCycles (K := X ⊗ Y)
        (((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl))
        ((ComplexShape.down ℕ).next (p + q))
        rfl
        chainComplexCycleRepresentativeTensor_d_eq_zero
        α
  have hzero :
      (X ⊗ Y).liftCycles
          (α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl))
          ((ComplexShape.down ℕ).next (p + q))
          rfl
          hkprecomp ≫
        (X ⊗ Y).homologyπ (p + q) =
      0 := by
    exact HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary (K := X ⊗ Y)
      (α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl))
      ((ComplexShape.down ℕ).next (p + q))
      rfl
      x
      hα
  calc
    (((X.sc p).moduleCatLeftHomologyData.f' ≫ (X.sc p).moduleCatCyclesIso.inv) ⊗ₘ
        (Y.sc q).moduleCatCyclesIso.inv) ≫
      chainComplexCycleCrossProduct ≫
      (X ⊗ Y).homologyπ (p + q) ≫
      ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom =
        (X ⊗ Y).liftCycles
          (α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl))
          ((ComplexShape.down ℕ).next (p + q))
          rfl
          hkprecomp ≫
          (X ⊗ Y).homologyπ (p + q) ≫
          ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom := by
        simpa [Category.assoc, α] using
          congrArg
            (fun f ↦
              f ≫ (X ⊗ Y).homologyπ (p + q) ≫
                ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom)
            hcomp
    _ =
        ((X ⊗ Y).liftCycles
              (α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl))
              ((ComplexShape.down ℕ).next (p + q))
              rfl
              hkprecomp ≫
            (X ⊗ Y).homologyπ (p + q)) ≫
          ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom := by
        simp [Category.assoc]
    _ = 0 := by
        rw [hzero]
        exact CategoryTheory.Limits.zero_comp

private theorem chainComplexKernelCrossProductToHomologyLinear_leftBoundary_zero :
    chainComplexKernelCrossProductToHomologyLinear.comp
        (TensorProduct.map
          (Submodule.subtype
            (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom)))
          (LinearMap.id : (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
            (Y.sc q).moduleCatLeftHomologyData.K)) =
      0 := by
  -- Evaluate the quotient-model tensor map on pure tensors and reduce to the abstract
  -- homology-vanishing statement proved above.
  apply TensorProduct.ext'
  intro x y
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨x', rfl⟩
  have hzero :
      ModuleCat.Hom.hom
          ((((X.sc p).moduleCatLeftHomologyData.f' ≫ (X.sc p).moduleCatCyclesIso.inv) ⊗ₘ
              (Y.sc q).moduleCatCyclesIso.inv) ≫
            chainComplexCycleCrossProduct ≫
            (X ⊗ Y).homologyπ (p + q) ≫
            ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom)
          (x' ⊗ₜ y) =
        0 := by
    simpa using
      congrArg
        (fun f ↦ ModuleCat.Hom.hom f (x' ⊗ₜ y))
        (leftBoundaryCrossProduct_homology_zero (X := X) (Y := Y) (p := p) (q := q))
  simpa [LinearMap.comp_apply, chainComplexKernelCrossProductToHomologyLinear,
    TensorProduct.map_tmul]
    using hzero

/-- Helper for Construction 17.2.1: tensors of `X`-cycles with `Y`-boundaries map to zero in the
target homology quotient. -/
private theorem rightBoundaryRepresentative_normalized :
    ((X.sc p).moduleCatCyclesIso.inv ⊗ₘ
        ((Y.sc q).moduleCatLeftHomologyData.f' ≫ (Y.sc q).moduleCatCyclesIso.inv)) ≫
      ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl) =
    ((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ Y.d ((ComplexShape.down ℕ).prev q) q) ≫
      ιTensorObj X Y p q (p + q) rfl := by
  -- Push the tensor composition across the summand inclusion, then normalize each factor.
  calc
    ((X.sc p).moduleCatCyclesIso.inv ⊗ₘ
        ((Y.sc q).moduleCatLeftHomologyData.f' ≫ (Y.sc q).moduleCatCyclesIso.inv)) ≫
        ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl) =
      ((((X.sc p).moduleCatCyclesIso.inv) ⊗ₘ
          ((Y.sc q).moduleCatLeftHomologyData.f' ≫ (Y.sc q).moduleCatCyclesIso.inv)) ≫
          (X.iCycles p ⊗ₘ Y.iCycles q)) ≫
          ιTensorObj X Y p q (p + q) rfl := by
        simp [Category.assoc]
    _ =
      (((X.sc p).moduleCatCyclesIso.inv ≫ X.iCycles p) ⊗ₘ
          (((Y.sc q).moduleCatLeftHomologyData.f' ≫
              (Y.sc q).moduleCatCyclesIso.inv) ≫
            Y.iCycles q)) ≫
          ιTensorObj X Y p q (p + q) rfl := by
        simp [Category.assoc]
    _ =
      (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
          (((Y.sc q).moduleCatLeftHomologyData.f' ≫
              (Y.sc q).moduleCatCyclesIso.inv) ≫
            Y.iCycles q)) ≫
          ιTensorObj X Y p q (p + q) rfl := by
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ (f ⊗ₘ
              (((Y.sc q).moduleCatLeftHomologyData.f' ≫
                  (Y.sc q).moduleCatCyclesIso.inv) ≫
                Y.iCycles q)) ≫
              ιTensorObj X Y p q (p + q) rfl)
            (CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_iCycles (S := X.sc p))
    _ =
      ((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ Y.d ((ComplexShape.down ℕ).prev q) q) ≫
          ιTensorObj X Y p q (p + q) rfl := by
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ ((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ f) ≫
              ιTensorObj X Y p q (p + q) rfl)
            (rightBoundarySourceCyclesIso_inv_iCycles (Y := Y) (q := q))

/-- Helper for Construction 17.2.1: tensors of `X`-cycles with `Y`-boundaries map to zero in the
target homology quotient. -/
private theorem rightBoundaryRepresentative_eq_boundary
    (hprev : p + (ComplexShape.down ℕ).prev q = (ComplexShape.down ℕ).prev (p + q)) :
    ((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ Y.d ((ComplexShape.down ℕ).prev q) q) ≫
        ιTensorObj X Y p q (p + q) rfl =
      ((ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (p, (ComplexShape.down ℕ).prev q) •
          (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
            (𝟙 ((Y.sc q).X₁)))) ≫
          ιTensorObj X Y p ((ComplexShape.down ℕ).prev q)
            ((ComplexShape.down ℕ).prev (p + q)) hprev ≫
        (X ⊗ Y).d ((ComplexShape.down ℕ).prev (p + q)) (p + q)) := by
  -- Expand the tensor differential at the `(p, prev q)` summand and keep only the `D₂` branch.
  change ((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ Y.d ((ComplexShape.down ℕ).prev q) q) ≫
        ιTensorObj X Y p q (p + q) rfl =
      ((ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (p, (ComplexShape.down ℕ).prev q) •
            (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
              (𝟙 ((Y.sc q).X₁)))) ≫
          ιTensorObj X Y p ((ComplexShape.down ℕ).prev q)
            ((ComplexShape.down ℕ).prev (p + q)) hprev ≫
        (HomologicalComplex.tensorObj X Y).d ((ComplexShape.down ℕ).prev (p + q)) (p + q))
  rw [HomologicalComplex.mapBifunctor.d_eq X Y (curriedTensor (ModuleCat R))
    (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q),
    Preadditive.comp_add, Preadditive.comp_add]
  have hq : (ComplexShape.down ℕ).Rel ((ComplexShape.down ℕ).prev q) q := by
    simp [ChainComplex.prev, ComplexShape.down_Rel]
  have hD₁ :
      (((ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (p, (ComplexShape.down ℕ).prev q) •
            (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
              (𝟙 ((Y.sc q).X₁)))) ≫
          ιTensorObj X Y p ((ComplexShape.down ℕ).prev q)
            ((ComplexShape.down ℕ).prev (p + q)) hprev) ≫
          HomologicalComplex.mapBifunctor.D₁ X Y (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q)) =
        0 := by
    have hι :
        (((ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q) •
              (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                (𝟙 ((Y.sc q).X₁)))) ≫
            ιTensorObj X Y p ((ComplexShape.down ℕ).prev q)
              ((ComplexShape.down ℕ).prev (p + q)) hprev) ≫
            HomologicalComplex.mapBifunctor.D₁ X Y (curriedTensor (ModuleCat R))
              (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q)) =
          ((ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q) •
              (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                (𝟙 ((Y.sc q).X₁)))) ≫
            HomologicalComplex.mapBifunctor.d₁ X Y (curriedTensor (ModuleCat R))
              (ComplexShape.down ℕ) p ((ComplexShape.down ℕ).prev q) (p + q)) := by
      simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
        congrArg
          (fun f ↦
            (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q) •
              (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                (𝟙 ((Y.sc q).X₁)))) ≫ f)
          (HomologicalComplex.mapBifunctor.ι_D₁ X Y (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q)
            p ((ComplexShape.down ℕ).prev q) hprev)
    rw [hι]
    by_cases hp : (ComplexShape.down ℕ).Rel p ((ComplexShape.down ℕ).next p)
    · have hpq_eq : (ComplexShape.down ℕ).next p + (ComplexShape.down ℕ).prev q = p + q := by
        exact rightBoundaryNextPrev_eq (p := p) (q := q) hp
      rw [HomologicalComplex.mapBifunctor.d₁_eq X Y (curriedTensor (ModuleCat R))
        (ComplexShape.down ℕ) hp ((ComplexShape.down ℕ).prev q) (p + q) hpq_eq]
      have hmap :
          ((curriedTensor (ModuleCat R)).map (X.d p ((ComplexShape.down ℕ).next p))).app
              (Y.X ((ComplexShape.down ℕ).prev q)) =
            X.d p ((ComplexShape.down ℕ).next p) ▷ Y.X ((ComplexShape.down ℕ).prev q) := rfl
      rw [hmap]
      have hcomp :
          ((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ (𝟙 ((Y.sc q).X₁))) ≫
              (X.d p ((ComplexShape.down ℕ).next p) ▷ Y.X ((ComplexShape.down ℕ).prev q)) =
            (((X.sc p).moduleCatLeftHomologyData.i ≫ X.d p ((ComplexShape.down ℕ).next p)) ⊗ₘ
              (𝟙 ((Y.sc q).X₁))) := by
        simpa using tensorHom_comp_whiskerRight
          (f := (X.sc p).moduleCatLeftHomologyData.i)
          (g := X.d p ((ComplexShape.down ℕ).next p))
          (h := 𝟙 ((Y.sc q).X₁))
      calc
        (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (p, (ComplexShape.down ℕ).prev q) •
            (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
              (𝟙 ((Y.sc q).X₁)))) ≫
            (ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q) •
              (X.d p ((ComplexShape.down ℕ).next p) ▷ Y.X ((ComplexShape.down ℕ).prev q) ≫
              ιTensorObj X Y ((ComplexShape.down ℕ).next p) ((ComplexShape.down ℕ).prev q)
                (p + q) hpq_eq)) =
          (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q) *
            ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q)) •
            ((((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ
                (𝟙 ((Y.sc q).X₁))) ≫
              X.d p ((ComplexShape.down ℕ).next p) ▷ Y.X ((ComplexShape.down ℕ).prev q)) ≫
              ιTensorObj X Y ((ComplexShape.down ℕ).next p) ((ComplexShape.down ℕ).prev q)
                (p + q) hpq_eq) := by
            have hsmul :
                (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (p, (ComplexShape.down ℕ).prev q) •
                    (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                      (𝟙 ((Y.sc q).X₁)))) ≫
                  (ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) •
                    (X.d p ((ComplexShape.down ℕ).next p) ▷
                      Y.X ((ComplexShape.down ℕ).prev q) ≫
                      ιTensorObj X Y ((ComplexShape.down ℕ).next p)
                        ((ComplexShape.down ℕ).prev q) (p + q) hpq_eq)) =
                (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) *
                  ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q)) •
                  (((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ
                      (𝟙 ((Y.sc q).X₁))) ≫
                    (X.d p ((ComplexShape.down ℕ).next p) ▷
                      Y.X ((ComplexShape.down ℕ).prev q) ≫
                      ιTensorObj X Y ((ComplexShape.down ℕ).next p)
                        ((ComplexShape.down ℕ).prev q) (p + q) hpq_eq)) := by
              have hε₁ :
                  ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) = 1 := by
                rfl
              rw [hε₁]
              rw [← Category.assoc]
              have hscaled :
                  (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                      (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) •
                      (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                        (𝟙 ((Y.sc q).X₁)))) ≫
                    (X.d p ((ComplexShape.down ℕ).next p) ▷
                      Y.X ((ComplexShape.down ℕ).prev q)) =
                  ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) •
                    ((((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                        (𝟙 ((Y.sc q).X₁))) ≫
                      (X.d p ((ComplexShape.down ℕ).next p) ▷
                        Y.X ((ComplexShape.down ℕ).prev q))) := by
                simpa using
                  (Preadditive.zsmul_comp
                    (n := ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                      (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q))
                    (f := (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                      (𝟙 ((Y.sc q).X₁))))
                    (g := X.d p ((ComplexShape.down ℕ).next p) ▷
                      Y.X ((ComplexShape.down ℕ).prev q)))
              have hpost :
                  ((ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                        (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) •
                        (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                          (𝟙 ((Y.sc q).X₁)))) ≫
                      (X.d p ((ComplexShape.down ℕ).next p) ▷
                        Y.X ((ComplexShape.down ℕ).prev q))) ≫
                      ιTensorObj X Y ((ComplexShape.down ℕ).next p)
                        ((ComplexShape.down ℕ).prev q) (p + q) hpq_eq =
                    ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                        (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) •
                      ((((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                          (𝟙 ((Y.sc q).X₁))) ≫
                        (X.d p ((ComplexShape.down ℕ).next p) ▷
                          Y.X ((ComplexShape.down ℕ).prev q)) ≫
                        ιTensorObj X Y ((ComplexShape.down ℕ).next p)
                          ((ComplexShape.down ℕ).prev q) (p + q) hpq_eq) := by
                rw [hscaled]
                simpa [Category.assoc] using
                  (Preadditive.zsmul_comp
                    (n := ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                      (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q))
                    (f := (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                      (𝟙 ((Y.sc q).X₁))) ≫
                      (X.d p ((ComplexShape.down ℕ).next p) ▷
                        Y.X ((ComplexShape.down ℕ).prev q)))
                    (g := ιTensorObj X Y ((ComplexShape.down ℕ).next p)
                      ((ComplexShape.down ℕ).prev q) (p + q) hpq_eq))
              simpa [Category.assoc] using hpost
            calc
              (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                  (p, (ComplexShape.down ℕ).prev q) •
                  (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                    (𝟙 ((Y.sc q).X₁)))) ≫
                  (ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) •
                    (X.d p ((ComplexShape.down ℕ).next p) ▷
                      Y.X ((ComplexShape.down ℕ).prev q) ≫
                      ιTensorObj X Y ((ComplexShape.down ℕ).next p)
                        ((ComplexShape.down ℕ).prev q) (p + q) hpq_eq)) =
                (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) *
                  ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q)) •
                  (((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ
                      (𝟙 ((Y.sc q).X₁))) ≫
                    (X.d p ((ComplexShape.down ℕ).next p) ▷
                      Y.X ((ComplexShape.down ℕ).prev q) ≫
                      ιTensorObj X Y ((ComplexShape.down ℕ).next p)
                        ((ComplexShape.down ℕ).prev q) (p + q) hpq_eq)) := hsmul
              _ =
                (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) *
                  ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q)) •
                  ((((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ
                      (𝟙 ((Y.sc q).X₁))) ≫
                    X.d p ((ComplexShape.down ℕ).next p) ▷
                      Y.X ((ComplexShape.down ℕ).prev q)) ≫
                    ιTensorObj X Y ((ComplexShape.down ℕ).next p)
                      ((ComplexShape.down ℕ).prev q) (p + q) hpq_eq) := by
                rw [Category.assoc]
        _ =
          (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q) *
            ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q)) •
            ((((X.sc p).moduleCatLeftHomologyData.i ≫ X.d p ((ComplexShape.down ℕ).next p)) ⊗ₘ
                (𝟙 ((Y.sc q).X₁))) ≫
              ιTensorObj X Y ((ComplexShape.down ℕ).next p) ((ComplexShape.down ℕ).prev q)
                (p + q) hpq_eq) := by
            congr 1
            simpa [Category.assoc] using
              congrArg
                (fun f ↦
                  f ≫ ιTensorObj X Y ((ComplexShape.down ℕ).next p)
                    ((ComplexShape.down ℕ).prev q) (p + q) hpq_eq)
                hcomp
        _ =
          (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q) *
            ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q)) •
            ((0 ⊗ₘ (𝟙 ((Y.sc q).X₁))) ≫
              ιTensorObj X Y ((ComplexShape.down ℕ).next p) ((ComplexShape.down ℕ).prev q)
                (p + q) hpq_eq) := by
            congr 1
            simpa [Category.assoc] using
              congrArg
                (fun f ↦
                  (f ⊗ₘ (𝟙 ((Y.sc q).X₁))) ≫
                    ιTensorObj X Y ((ComplexShape.down ℕ).next p) ((ComplexShape.down ℕ).prev q)
                      (p + q) hpq_eq)
                (moduleCatLeftHomologyData_i_d_eq_zero (K := X) (n := p))
        _ = 0 := by
            rw [CategoryTheory.MonoidalPreadditive.zero_tensor, CategoryTheory.Limits.zero_comp,
              smul_zero]
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero X Y (curriedTensor (ModuleCat R))
        (ComplexShape.down ℕ) p ((ComplexShape.down ℕ).prev q) (p + q) hp]
      exact CategoryTheory.Limits.comp_zero
  have hD₂ :
      (((ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (p, (ComplexShape.down ℕ).prev q) •
            (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
              (𝟙 ((Y.sc q).X₁)))) ≫
          ιTensorObj X Y p ((ComplexShape.down ℕ).prev q)
            ((ComplexShape.down ℕ).prev (p + q)) hprev) ≫
          HomologicalComplex.mapBifunctor.D₂ X Y (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q)) =
        ((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ Y.d ((ComplexShape.down ℕ).prev q) q) ≫
          ιTensorObj X Y p q (p + q) rfl := by
    have hι :
        (((ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q) •
              (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                (𝟙 ((Y.sc q).X₁)))) ≫
            ιTensorObj X Y p ((ComplexShape.down ℕ).prev q)
              ((ComplexShape.down ℕ).prev (p + q)) hprev) ≫
            HomologicalComplex.mapBifunctor.D₂ X Y (curriedTensor (ModuleCat R))
              (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q)) =
          ((ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q) •
              (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                (𝟙 ((Y.sc q).X₁)))) ≫
            HomologicalComplex.mapBifunctor.d₂ X Y (curriedTensor (ModuleCat R))
              (ComplexShape.down ℕ) p ((ComplexShape.down ℕ).prev q) (p + q)) := by
      simpa [HomologicalComplex.ιTensorObj, Category.assoc] using
        congrArg
          (fun f ↦
            (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q) •
              (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                (𝟙 ((Y.sc q).X₁)))) ≫ f)
          (HomologicalComplex.mapBifunctor.ι_D₂ X Y (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q)
            p ((ComplexShape.down ℕ).prev q) hprev)
    rw [hι]
    rw [HomologicalComplex.mapBifunctor.d₂_eq X Y (curriedTensor (ModuleCat R))
      (ComplexShape.down ℕ) p hq (p + q) rfl]
    have hmap :
        ((curriedTensor (ModuleCat R)).obj (X.X p)).map (Y.d ((ComplexShape.down ℕ).prev q) q) =
          X.X p ◁ Y.d ((ComplexShape.down ℕ).prev q) q := rfl
    rw [hmap]
    have hcomp :
        ((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ (𝟙 ((Y.sc q).X₁))) ≫
            (X.X p ◁ Y.d ((ComplexShape.down ℕ).prev q) q) =
          ((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ
            ((𝟙 ((Y.sc q).X₁)) ≫ Y.d ((ComplexShape.down ℕ).prev q) q)) := by
      simpa using tensorHom_comp_whiskerLeft
        (f := (X.sc p).moduleCatLeftHomologyData.i)
        (g := 𝟙 ((Y.sc q).X₁))
        (h := Y.d ((ComplexShape.down ℕ).prev q) q)
    calc
      (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (p, (ComplexShape.down ℕ).prev q) •
        (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
          (𝟙 ((Y.sc q).X₁)))) ≫
        (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (p, (ComplexShape.down ℕ).prev q) •
          (X.X p ◁ Y.d ((ComplexShape.down ℕ).prev q) q ≫
            ιTensorObj X Y p q (p + q) rfl)) =
      ((ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (p, (ComplexShape.down ℕ).prev q)) *
          ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
            (p, (ComplexShape.down ℕ).prev q)) •
        ((((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
            (𝟙 ((Y.sc q).X₁))) ≫
          X.X p ◁ Y.d ((ComplexShape.down ℕ).prev q) q) ≫
          ιTensorObj X Y p q (p + q) rfl := by
        have hsmul :
            (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (p, (ComplexShape.down ℕ).prev q) •
                (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                  (𝟙 ((Y.sc q).X₁)))) ≫
              (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) •
                (X.X p ◁ Y.d ((ComplexShape.down ℕ).prev q) q ≫
                  ιTensorObj X Y p q (p + q) rfl)) =
            (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) *
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q)) •
              (((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ
                  (𝟙 ((Y.sc q).X₁))) ≫
                (X.X p ◁ Y.d ((ComplexShape.down ℕ).prev q) q ≫
                  ιTensorObj X Y p q (p + q) rfl)) := by
          simpa using
            zsmulCompZsmul
              (n := ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q))
              (m := ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q))
              (f := (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                (𝟙 ((Y.sc q).X₁))))
              (g := X.X p ◁ Y.d ((ComplexShape.down ℕ).prev q) q ≫
                ιTensorObj X Y p q (p + q) rfl)
        calc
          (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
              (p, (ComplexShape.down ℕ).prev q) •
              (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                (𝟙 ((Y.sc q).X₁)))) ≫
              (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) •
                (X.X p ◁ Y.d ((ComplexShape.down ℕ).prev q) q ≫
                  ιTensorObj X Y p q (p + q) rfl)) =
            (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) *
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q)) •
              (((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ
                  (𝟙 ((Y.sc q).X₁))) ≫
                (X.X p ◁ Y.d ((ComplexShape.down ℕ).prev q) q ≫
                  ιTensorObj X Y p q (p + q) rfl)) := hsmul
          _ =
            (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q) *
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, (ComplexShape.down ℕ).prev q)) •
              ((((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
                  (𝟙 ((Y.sc q).X₁))) ≫
                X.X p ◁ Y.d ((ComplexShape.down ℕ).prev q) q) ≫
                ιTensorObj X Y p q (p + q) rfl := by
              rw [Category.assoc]
      _ =
        ((((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
            (𝟙 ((Y.sc q).X₁))) ≫
          X.X p ◁ Y.d ((ComplexShape.down ℕ).prev q) q) ≫
          ιTensorObj X Y p q (p + q) rfl := by
        simpa using one_zsmul
          ((((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
              (𝟙 ((Y.sc q).X₁))) ≫
            X.X p ◁ Y.d ((ComplexShape.down ℕ).prev q) q ≫
            ιTensorObj X Y p q (p + q) rfl)
      _ =
        ((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ
          ((𝟙 ((Y.sc q).X₁)) ≫ Y.d ((ComplexShape.down ℕ).prev q) q)) ≫
          ιTensorObj X Y p q (p + q) rfl := by
        simpa [Category.assoc] using
          congrArg
            (fun f ↦ f ≫ ιTensorObj X Y p q (p + q) rfl)
            hcomp
      _ =
        ((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ Y.d ((ComplexShape.down ℕ).prev q) q) ≫
          ιTensorObj X Y p q (p + q) rfl := by
        simp [Category.assoc]
  have hD₁' :
      (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (p, (ComplexShape.down ℕ).prev q) •
          (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
            (𝟙 ((Y.sc q).X₁)))) ≫
          ιTensorObj X Y p ((ComplexShape.down ℕ).prev q)
            ((ComplexShape.down ℕ).prev (p + q)) hprev ≫
          HomologicalComplex.mapBifunctor.D₁ X Y (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q) =
        0 := by
    simpa [Category.assoc] using hD₁
  have hD₂' :
      (ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (p, (ComplexShape.down ℕ).prev q) •
          (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ
            (𝟙 ((Y.sc q).X₁)))) ≫
          ιTensorObj X Y p ((ComplexShape.down ℕ).prev q)
            ((ComplexShape.down ℕ).prev (p + q)) hprev ≫
          HomologicalComplex.mapBifunctor.D₂ X Y (curriedTensor (ModuleCat R))
            (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev (p + q)) (p + q) =
        ((X.sc p).moduleCatLeftHomologyData.i ⊗ₘ Y.d ((ComplexShape.down ℕ).prev q) q) ≫
          ιTensorObj X Y p q (p + q) rfl := by
    simpa [Category.assoc] using hD₂
  rw [hD₁', hD₂']
  rw [zero_add]

/-- Helper for Construction 17.2.1: tensors of `X`-cycles with `Y`-boundaries map to zero in the
target homology quotient. -/
private theorem rightBoundaryCrossProduct_homology_zero :
    ((X.sc p).moduleCatCyclesIso.inv ⊗ₘ
        ((Y.sc q).moduleCatLeftHomologyData.f' ≫ (Y.sc q).moduleCatCyclesIso.inv)) ≫
      chainComplexCycleCrossProduct ≫
      (X ⊗ Y).homologyπ (p + q) ≫
      ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom =
    0 := by
  -- Rewrite the precomposed cycle map as a lifted boundary, then use the standard vanishing of
  -- boundaries in homology.
  have hprev : p + (ComplexShape.down ℕ).prev q = (ComplexShape.down ℕ).prev (p + q) := by
    simp [ChainComplex.prev]
    omega
  let α :=
    ((X.sc p).moduleCatCyclesIso.inv ⊗ₘ
      ((Y.sc q).moduleCatLeftHomologyData.f' ≫ (Y.sc q).moduleCatCyclesIso.inv))
  let x :=
    ((ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (p, (ComplexShape.down ℕ).prev q) •
        (((X.sc p).moduleCatLeftHomologyData.i) ⊗ₘ (𝟙 ((Y.sc q).X₁)))) ≫
      ιTensorObj X Y p ((ComplexShape.down ℕ).prev q)
        ((ComplexShape.down ℕ).prev (p + q)) hprev)
  have hα :
      α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl) =
        x ≫ (X ⊗ Y).d ((ComplexShape.down ℕ).prev (p + q)) (p + q) := by
    rw [rightBoundaryRepresentative_normalized]
    unfold x
    simpa [Category.assoc] using
      rightBoundaryRepresentative_eq_boundary (X := X) (Y := Y) (p := p) (q := q) hprev
  have hkprecomp :
      (α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl)) ≫
          (X ⊗ Y).d (p + q) ((ComplexShape.down ℕ).next (p + q)) =
        0 := by
    simpa [Category.assoc] using
      congrArg (fun f ↦ α ≫ f) chainComplexCycleRepresentativeTensor_d_eq_zero
  have hcomp :
      α ≫ chainComplexCycleCrossProduct =
      (X ⊗ Y).liftCycles
        (α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl))
        ((ComplexShape.down ℕ).next (p + q))
        rfl
        hkprecomp := by
    simpa [chainComplexCycleCrossProduct] using
      HomologicalComplex.comp_liftCycles (K := X ⊗ Y)
        (((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl))
        ((ComplexShape.down ℕ).next (p + q))
        rfl
        chainComplexCycleRepresentativeTensor_d_eq_zero
        α
  have hzero :
      (X ⊗ Y).liftCycles
          (α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl))
          ((ComplexShape.down ℕ).next (p + q))
          rfl
          hkprecomp ≫
        (X ⊗ Y).homologyπ (p + q) =
      0 := by
    exact HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary (K := X ⊗ Y)
      (α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl))
      ((ComplexShape.down ℕ).next (p + q))
      rfl
      x
      hα
  calc
    ((X.sc p).moduleCatCyclesIso.inv ⊗ₘ
        ((Y.sc q).moduleCatLeftHomologyData.f' ≫ (Y.sc q).moduleCatCyclesIso.inv)) ≫
      chainComplexCycleCrossProduct ≫
      (X ⊗ Y).homologyπ (p + q) ≫
      ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom =
        (X ⊗ Y).liftCycles
          (α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl))
          ((ComplexShape.down ℕ).next (p + q))
          rfl
          hkprecomp ≫
          (X ⊗ Y).homologyπ (p + q) ≫
          ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom := by
        simpa [Category.assoc, α] using
          congrArg
            (fun f ↦
              f ≫ (X ⊗ Y).homologyπ (p + q) ≫
                ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom)
            hcomp
    _ =
        ((X ⊗ Y).liftCycles
              (α ≫ ((X.iCycles p ⊗ₘ Y.iCycles q) ≫ ιTensorObj X Y p q (p + q) rfl))
              ((ComplexShape.down ℕ).next (p + q))
              rfl
              hkprecomp ≫
            (X ⊗ Y).homologyπ (p + q)) ≫
          ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom := by
        simp [Category.assoc]
    _ = 0 := by
        rw [hzero]
        exact CategoryTheory.Limits.zero_comp

/-- Helper for Construction 17.2.1: tensors of `X`-cycles with `Y`-boundaries map to zero in the
target homology quotient. -/
private theorem chainComplexKernelCrossProductToHomologyLinear_rightBoundary_zero :
    chainComplexKernelCrossProductToHomologyLinear.comp
        (TensorProduct.map
          (LinearMap.id : (X.sc p).moduleCatLeftHomologyData.K →ₗ[R]
            (X.sc p).moduleCatLeftHomologyData.K)
          (Submodule.subtype
              (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom)))) =
      0 := by
  -- Evaluate the quotient-model tensor map on pure tensors and reduce to the symmetric abstract
  -- boundary-vanishing statement proved above.
  apply TensorProduct.ext'
  intro x y
  rcases y with ⟨y, hy⟩
  rcases hy with ⟨y', rfl⟩
  have hzero :
      ModuleCat.Hom.hom
          (((X.sc p).moduleCatCyclesIso.inv ⊗ₘ
              ((Y.sc q).moduleCatLeftHomologyData.f' ≫ (Y.sc q).moduleCatCyclesIso.inv)) ≫
            chainComplexCycleCrossProduct ≫
            (X ⊗ Y).homologyπ (p + q) ≫
            ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom)
          (x ⊗ₜ y') =
        0 := by
    simpa using
      congrArg
        (fun f ↦ ModuleCat.Hom.hom f (x ⊗ₜ y'))
        (rightBoundaryCrossProduct_homology_zero (X := X) (Y := Y) (p := p) (q := q))
  simpa [LinearMap.comp_apply, chainComplexKernelCrossProductToHomologyLinear,
    TensorProduct.map_tmul]
    using hzero

/-- The kernel-level tensor map kills the boundary summands, so it descends along the quotient
presentation of `X.homology p ⊗ Y.homology q`. -/
private theorem chainComplexKernelCrossProductToHomologyLinear_range_le_ker :
    LinearMap.range
          (TensorProduct.map
            (Submodule.subtype
              (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom)))
            (LinearMap.id : (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
              (Y.sc q).moduleCatLeftHomologyData.K)) ⊔
        LinearMap.range
          (TensorProduct.map
            (LinearMap.id : (X.sc p).moduleCatLeftHomologyData.K →ₗ[R]
              (X.sc p).moduleCatLeftHomologyData.K)
            (Submodule.subtype
              (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom)))) ≤
      LinearMap.ker
        chainComplexKernelCrossProductToHomologyLinear := by
  -- Once the two boundary branches vanish, the supremum of their ranges lies in the kernel.
  rw [sup_le_iff]
  constructor
  · exact LinearMap.range_le_ker_iff.2
      chainComplexKernelCrossProductToHomologyLinear_leftBoundary_zero
  · exact LinearMap.range_le_ker_iff.2
      chainComplexKernelCrossProductToHomologyLinear_rightBoundary_zero

/-- Construction 17.2.1: for chain complexes `X` and `Y`, in degrees `p` and `q`, the cross
product `H_p(X) ⊗ H_q(Y) ⟶ H_{p + q}(X ⊗ Y)` induced by tensoring cycle representatives. -/
noncomputable def chainComplexHomologyCrossProduct
    : X.homology p ⊗ Y.homology q ⟶ (X ⊗ Y).homology (p + q) :=
  ((X.sc p).moduleCatHomologyIso.hom ⊗ₘ (Y.sc q).moduleCatHomologyIso.hom) ≫
    ModuleCat.ofHom
      ((Submodule.liftQ
          (LinearMap.range
              (TensorProduct.map
                (Submodule.subtype
                  (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom)))
                (LinearMap.id : (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
                  (Y.sc q).moduleCatLeftHomologyData.K)) ⊔
            LinearMap.range
              (TensorProduct.map
                (LinearMap.id : (X.sc p).moduleCatLeftHomologyData.K →ₗ[R]
                  (X.sc p).moduleCatLeftHomologyData.K)
                (Submodule.subtype
                  (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom)))))
          chainComplexKernelCrossProductToHomologyLinear
          chainComplexKernelCrossProductToHomologyLinear_range_le_ker).comp
        (TensorProduct.quotientTensorQuotientEquiv
          (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom))
          (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom))).toLinearMap) ≫
    ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.inv

/-- Helper for Construction 17.2.1: bundling
`chainComplexKernelCrossProductToHomologyLinear` back into `ModuleCat` recovers the defining
cycles-to-homology composite. -/
private theorem chainComplexKernelCrossProductToHomologyLinear_hom :
    ModuleCat.ofHom chainComplexKernelCrossProductToHomologyLinear =
      ((X.sc p).moduleCatCyclesIso.inv ⊗ₘ (Y.sc q).moduleCatCyclesIso.inv) ≫
        chainComplexCycleCrossProduct ≫ (X ⊗ Y).homologyπ (p + q) ≫
          ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom := by
  -- The concrete linear map was defined as the underlying hom of this composite.
  apply ModuleCat.hom_ext
  rfl

/-- Helper for Construction 17.2.1: the quotient-tensor descent from the concrete homology models
computes on pure tensors as `chainComplexKernelCrossProductToHomologyLinear`. -/
private theorem quotientTensorDescent_hom :
    ((X.sc p).moduleCatLeftHomologyData.π ⊗ₘ
        (Y.sc q).moduleCatLeftHomologyData.π) ≫
      ModuleCat.ofHom
        ((Submodule.liftQ
            (LinearMap.range
                (TensorProduct.map
                  (Submodule.subtype
                    (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom)))
                  (LinearMap.id : (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
                    (Y.sc q).moduleCatLeftHomologyData.K)) ⊔
              LinearMap.range
                (TensorProduct.map
                  (LinearMap.id : (X.sc p).moduleCatLeftHomologyData.K →ₗ[R]
                    (X.sc p).moduleCatLeftHomologyData.K)
                  (Submodule.subtype
                    (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom)))))
            chainComplexKernelCrossProductToHomologyLinear
            chainComplexKernelCrossProductToHomologyLinear_range_le_ker).comp
          (TensorProduct.quotientTensorQuotientEquiv
            (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom))
            (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom))).toLinearMap) =
    ModuleCat.ofHom chainComplexKernelCrossProductToHomologyLinear := by
  -- Compare the two morphisms on pure tensors in the concrete quotient presentation.
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change
    (Submodule.liftQ
        (LinearMap.range
            (TensorProduct.map
              (Submodule.subtype
                (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom)))
              (LinearMap.id : (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
                (Y.sc q).moduleCatLeftHomologyData.K)) ⊔
          LinearMap.range
            (TensorProduct.map
              (LinearMap.id : (X.sc p).moduleCatLeftHomologyData.K →ₗ[R]
                (X.sc p).moduleCatLeftHomologyData.K)
              (Submodule.subtype
                (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom)))))
        chainComplexKernelCrossProductToHomologyLinear
        chainComplexKernelCrossProductToHomologyLinear_range_le_ker)
      ((TensorProduct.quotientTensorQuotientEquiv
          (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom))
          (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom))).toLinearMap
        (Submodule.Quotient.mk x ⊗ₜ[R] Submodule.Quotient.mk y)) =
    chainComplexKernelCrossProductToHomologyLinear (x ⊗ₜ[R] y)
  have hquot :
      (TensorProduct.quotientTensorQuotientEquiv
          (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom))
          (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom))).toLinearMap
        (Submodule.Quotient.mk x ⊗ₜ[R] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x ⊗ₜ[R] y) := by
    simpa using
      (TensorProduct.quotientTensorQuotientEquiv_apply_tmul_mk_tmul_mk
        (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom))
        (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom))
        x y)
  rw [hquot]
  simpa [chainComplexKernelCrossProductToHomologyLinear] using
    (Submodule.liftQ_apply
      (p := LinearMap.range
          (TensorProduct.map
            (Submodule.subtype
              (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom)))
            (LinearMap.id : (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
              (Y.sc q).moduleCatLeftHomologyData.K)) ⊔
        LinearMap.range
          (TensorProduct.map
            (LinearMap.id : (X.sc p).moduleCatLeftHomologyData.K →ₗ[R]
              (X.sc p).moduleCatLeftHomologyData.K)
            (Submodule.subtype
              (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom)))))
      (f := chainComplexKernelCrossProductToHomologyLinear)
      (h := chainComplexKernelCrossProductToHomologyLinear_range_le_ker)
      (x := x ⊗ₜ[R] y))

/-- Helper for Construction 17.2.1: after rewriting the source homology factors to the concrete
quotient maps, postcomposing with the target homology isomorphism inverse and hom cancels. -/
private theorem quotientTensorDescent_postcompose_homologyIso :
    ((X.sc p).moduleCatLeftHomologyData.π ⊗ₘ
        (Y.sc q).moduleCatLeftHomologyData.π) ≫
      ModuleCat.ofHom
        ((Submodule.liftQ
            (LinearMap.range
                (TensorProduct.map
                  (Submodule.subtype
                    (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom)))
                  (LinearMap.id : (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
                    (Y.sc q).moduleCatLeftHomologyData.K)) ⊔
              LinearMap.range
                (TensorProduct.map
                  (LinearMap.id : (X.sc p).moduleCatLeftHomologyData.K →ₗ[R]
                    (X.sc p).moduleCatLeftHomologyData.K)
                  (Submodule.subtype
                    (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom)))))
            chainComplexKernelCrossProductToHomologyLinear
            chainComplexKernelCrossProductToHomologyLinear_range_le_ker).comp
          (TensorProduct.quotientTensorQuotientEquiv
            (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom))
            (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom))).toLinearMap) ≫
      ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.inv ≫
      ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom =
    ((X.sc p).moduleCatLeftHomologyData.π ⊗ₘ
        (Y.sc q).moduleCatLeftHomologyData.π) ≫
      ModuleCat.ofHom
        ((Submodule.liftQ
            (LinearMap.range
                (TensorProduct.map
                  (Submodule.subtype
                    (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom)))
                  (LinearMap.id : (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
                    (Y.sc q).moduleCatLeftHomologyData.K)) ⊔
              LinearMap.range
                (TensorProduct.map
                  (LinearMap.id : (X.sc p).moduleCatLeftHomologyData.K →ₗ[R]
                    (X.sc p).moduleCatLeftHomologyData.K)
                  (Submodule.subtype
                    (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom)))))
            chainComplexKernelCrossProductToHomologyLinear
            chainComplexKernelCrossProductToHomologyLinear_range_le_ker).comp
          (TensorProduct.quotientTensorQuotientEquiv
            (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom))
            (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom))).toLinearMap) := by
  -- Cancel the target homology isomorphism pair after the quotient-model descent map.
  let g :=
    ((X.sc p).moduleCatLeftHomologyData.π ⊗ₘ
        (Y.sc q).moduleCatLeftHomologyData.π) ≫
      ModuleCat.ofHom
        ((Submodule.liftQ
            (LinearMap.range
                (TensorProduct.map
                  (Submodule.subtype
                    (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom)))
                  (LinearMap.id : (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
                    (Y.sc q).moduleCatLeftHomologyData.K)) ⊔
              LinearMap.range
                (TensorProduct.map
                  (LinearMap.id : (X.sc p).moduleCatLeftHomologyData.K →ₗ[R]
                    (X.sc p).moduleCatLeftHomologyData.K)
                  (Submodule.subtype
                    (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom)))))
            chainComplexKernelCrossProductToHomologyLinear
            chainComplexKernelCrossProductToHomologyLinear_range_le_ker).comp
          (TensorProduct.quotientTensorQuotientEquiv
            (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom))
            (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom))).toLinearMap)
  have hcancel :
      g ≫ ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.inv ≫
        ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom = g := by
    apply ModuleCat.hom_ext
    ext x
    change
      ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.toLinearEquiv
          (((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.toLinearEquiv.symm
            (ModuleCat.Hom.hom g x)) =
        ModuleCat.Hom.hom g x
    simpa using
      ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.toLinearEquiv.apply_symm_apply
        (ModuleCat.Hom.hom g x)
  exact hcancel

/-- Helper for Construction 17.2.1: after postcomposing with the concrete target homology model,
the defining quotient-tensor formula agrees with the cycle-level tensor representative map. -/
private theorem tensorSourceHomologyProjection_eq :
    ((X.sc p).moduleCatCyclesIso.inv ⊗ₘ (Y.sc q).moduleCatCyclesIso.inv) ≫
      (X.homologyπ p ⊗ₘ Y.homologyπ q) ≫
      ((X.sc p).moduleCatHomologyIso.hom ⊗ₘ (Y.sc q).moduleCatHomologyIso.hom) =
    (X.sc p).moduleCatLeftHomologyData.π ⊗ₘ
      (Y.sc q).moduleCatLeftHomologyData.π := by
  -- Convert each source factor from abstract homology to the concrete quotient model, then tensor
  -- the resulting quotient maps.
  rw [← Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  have hX :
      (X.sc p).moduleCatCyclesIso.inv ≫ X.homologyπ p ≫
          (X.sc p).moduleCatHomologyIso.hom =
        (X.sc p).moduleCatLeftHomologyData.π := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦ f ≫ (X.sc p).moduleCatHomologyIso.hom)
        (CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_π (S := X.sc p))
  have hY :
      (Y.sc q).moduleCatCyclesIso.inv ≫ Y.homologyπ q ≫
          (Y.sc q).moduleCatHomologyIso.hom =
        (Y.sc q).moduleCatLeftHomologyData.π := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦ f ≫ (Y.sc q).moduleCatHomologyIso.hom)
        (CategoryTheory.ShortComplex.moduleCatCyclesIso_inv_π (S := Y.sc q))
  simpa [Category.assoc] using
    congrArg₂ (fun f g ↦ f ⊗ₘ g) hX hY

private theorem chainComplexHomologyCrossProduct_spec_moduleCat :
    ((X.homologyπ p ⊗ₘ Y.homologyπ q) ≫ chainComplexHomologyCrossProduct ≫
        ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom) =
      chainComplexCycleCrossProduct ≫ (X ⊗ Y).homologyπ (p + q) ≫
        ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom := by
  -- Precompose with the concrete cycles model, rewrite the source homology factors to the
  -- concrete quotient maps, and then evaluate the quotient descent on pure tensors.
  apply (cancel_epi ((X.sc p).moduleCatCyclesIso.inv ⊗ₘ (Y.sc q).moduleCatCyclesIso.inv)).1
  calc
    ((X.sc p).moduleCatCyclesIso.inv ⊗ₘ (Y.sc q).moduleCatCyclesIso.inv) ≫
        ((X.homologyπ p ⊗ₘ Y.homologyπ q) ≫ chainComplexHomologyCrossProduct ≫
          ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom) =
      ((X.sc p).moduleCatLeftHomologyData.π ⊗ₘ
          (Y.sc q).moduleCatLeftHomologyData.π) ≫
        ModuleCat.ofHom
          ((Submodule.liftQ
              (LinearMap.range
                  (TensorProduct.map
                    (Submodule.subtype
                      (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom)))
                    (LinearMap.id : (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
                      (Y.sc q).moduleCatLeftHomologyData.K)) ⊔
                LinearMap.range
                  (TensorProduct.map
                    (LinearMap.id : (X.sc p).moduleCatLeftHomologyData.K →ₗ[R]
                      (X.sc p).moduleCatLeftHomologyData.K)
                    (Submodule.subtype
                      (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom)))))
              chainComplexKernelCrossProductToHomologyLinear
              chainComplexKernelCrossProductToHomologyLinear_range_le_ker).comp
            (TensorProduct.quotientTensorQuotientEquiv
              (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom))
              (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom))).toLinearMap) ≫
        ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.inv ≫
        ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom := by
      -- Expanding the definition leaves only the concrete quotient-model tensor descent.
      rw [chainComplexHomologyCrossProduct]
      simp [Category.assoc]
      have hsource :
          ((X.sc p).moduleCatCyclesIso.inv ≫ X.homologyπ p ≫
              (X.sc p).moduleCatHomologyIso.hom) ⊗ₘ
            ((Y.sc q).moduleCatCyclesIso.inv ≫ Y.homologyπ q ≫
              (Y.sc q).moduleCatHomologyIso.hom) =
          (X.sc p).moduleCatLeftHomologyData.π ⊗ₘ
            (Y.sc q).moduleCatLeftHomologyData.π := by
        simpa [Category.assoc] using
          tensorSourceHomologyProjection_eq (X := X) (Y := Y) (p := p) (q := q)
      exact congrArg
        (fun f ↦
          f ≫
            ModuleCat.ofHom
              ((Submodule.liftQ
                  (LinearMap.range
                      (TensorProduct.map
                        (Submodule.subtype
                          (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom)))
                        (LinearMap.id : (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
                          (Y.sc q).moduleCatLeftHomologyData.K)) ⊔
                    LinearMap.range
                      (TensorProduct.map
                        (LinearMap.id : (X.sc p).moduleCatLeftHomologyData.K →ₗ[R]
                          (X.sc p).moduleCatLeftHomologyData.K)
                        (Submodule.subtype
                          (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom)))))
                  chainComplexKernelCrossProductToHomologyLinear
                  chainComplexKernelCrossProductToHomologyLinear_range_le_ker).comp
                (TensorProduct.quotientTensorQuotientEquiv
                  (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom))
                  (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom))).toLinearMap) ≫
            ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.inv ≫
            ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom)
        hsource
    _ =
      ((X.sc p).moduleCatLeftHomologyData.π ⊗ₘ
          (Y.sc q).moduleCatLeftHomologyData.π) ≫
        ModuleCat.ofHom
          ((Submodule.liftQ
              (LinearMap.range
                  (TensorProduct.map
                    (Submodule.subtype
                      (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom)))
                    (LinearMap.id : (Y.sc q).moduleCatLeftHomologyData.K →ₗ[R]
                      (Y.sc q).moduleCatLeftHomologyData.K)) ⊔
                LinearMap.range
                  (TensorProduct.map
                    (LinearMap.id : (X.sc p).moduleCatLeftHomologyData.K →ₗ[R]
                      (X.sc p).moduleCatLeftHomologyData.K)
                    (Submodule.subtype
                      (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom)))))
              chainComplexKernelCrossProductToHomologyLinear
              chainComplexKernelCrossProductToHomologyLinear_range_le_ker).comp
            (TensorProduct.quotientTensorQuotientEquiv
              (LinearMap.range (((X.sc p).moduleCatLeftHomologyData.f').hom))
              (LinearMap.range (((Y.sc q).moduleCatLeftHomologyData.f').hom))).toLinearMap) := by
      exact quotientTensorDescent_postcompose_homologyIso (X := X) (Y := Y) (p := p) (q := q)
    _ = ModuleCat.ofHom chainComplexKernelCrossProductToHomologyLinear := by
      exact quotientTensorDescent_hom (X := X) (Y := Y) (p := p) (q := q)
    _ =
      ((X.sc p).moduleCatCyclesIso.inv ⊗ₘ (Y.sc q).moduleCatCyclesIso.inv) ≫
        chainComplexCycleCrossProduct ≫ (X ⊗ Y).homologyπ (p + q) ≫
          ((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom := by
      exact chainComplexKernelCrossProductToHomologyLinear_hom (X := X) (Y := Y) (p := p)
        (q := q)

theorem chainComplexHomologyCrossProduct_spec :
    CommSq (X.homologyπ p ⊗ₘ Y.homologyπ q) chainComplexCycleCrossProduct
      chainComplexHomologyCrossProduct ((X ⊗ Y).homologyπ (p + q)) := by
  refine ⟨?_⟩
  -- Compare after postcomposing with the concrete target homology model, then cancel the target
  -- homology isomorphism.
  apply (cancel_mono (((X ⊗ Y).sc (p + q)).moduleCatHomologyIso.hom)).1
  simpa [Category.assoc] using
    chainComplexHomologyCrossProduct_spec_moduleCat (X := X) (Y := Y) (p := p) (q := q)

end
