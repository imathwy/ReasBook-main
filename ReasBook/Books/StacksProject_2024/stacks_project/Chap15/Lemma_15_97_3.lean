import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import StacksProject_2024.stacks_project.Chap15.Lemma_15_97_1

noncomputable section

open CategoryTheory
open ComplexShape
open scoped FittingIdeal
open scoped TensorProduct

universe u

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ

open scoped EtaDeterminantalIdeal

/-- Helper for Lemma 15.97.3: the scalar-extended cochain complex obtained from `M`. -/
private abbrev scalarExtendedComplex (M : CpxA) :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M)

private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
  { __ := AddEquiv.refl B
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

private noncomputable def extendScalarsTermLinearEquiv (M : CpxA) (i : ℤ) :
    ((scalarExtendedComplex (A := A) (B := B) M).X i : ModuleCat B) ≃ₗ[B] (B ⊗[A] (M.X i)) := by
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl A (M.X i)))

noncomputable instance extendScalars_mapHomologicalComplex_term_moduleFree
    (M : CpxA) (i : ℤ) [Module.Free A (M.X i)] :
    Module.Free B
      ((scalarExtendedComplex (A := A) (B := B) M).X i : ModuleCat B) := by
  let b := (Module.Free.chooseBasis A (M.X i)).baseChange B
  exact Module.Free.of_basis (b.map (extendScalarsTermLinearEquiv M i).symm)

noncomputable instance extendScalars_mapHomologicalComplex_term_moduleFinite
    (M : CpxA) (i : ℤ) [Module.Free A (M.X i)] [Module.Finite A (M.X i)] :
    Module.Finite B
      ((scalarExtendedComplex (A := A) (B := B) M).X i : ModuleCat B) := by
  let b := (Module.Free.chooseBasis A (M.X i)).baseChange B
  exact Module.Finite.of_basis
    (b.map (extendScalarsTermLinearEquiv M i).symm)

/-- Helper for Lemma 15.97.3: scalar extension preserves the finite rank of each finite free
term. -/
private lemma extendScalars_mapHomologicalComplex_term_finrank_eq
    (M : CpxA) (j : ℤ) [Nontrivial A] [Nontrivial B] [Module.Free A (M.X j)] [Module.Finite A (M.X j)] :
    Module.finrank B ((scalarExtendedComplex (A := A) (B := B) M).X j : ModuleCat B) =
      Module.finrank A (M.X j) := by
  -- First transport the scalar-extended term to the canonical tensor-product model.
  calc
    Module.finrank B ((scalarExtendedComplex (A := A) (B := B) M).X j : ModuleCat B)
        = Module.finrank B (B ⊗[A] (M.X j)) :=
          (extendScalarsTermLinearEquiv (A := A) (B := B) M j).finrank_eq
    -- Then use the standard base-change finrank formula on the tensor-product model.
    _ = Module.finrank A (M.X j) :=
          Module.finrank_baseChange (S := A) (R := B) (M' := M.X j)

/-- Helper for Lemma 15.97.3: the target of the scalar-extended eta presentation identifies with
the product of the base-changed terms. -/
private noncomputable abbrev etaPresentationBaseChangeTargetEquiv
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (((scalarExtendedComplex (A := A) (B := B) M).X i : ModuleCat B) ×
        ((scalarExtendedComplex (A := A) (B := B) M).X (i + 1) : ModuleCat B)) ≃ₗ[B]
      ((B ⊗[A] (M.X i)) × (B ⊗[A] (M.X (i + 1))) : Type u) :=
  LinearEquiv.prodCongr
    (extendScalarsTermLinearEquiv (A := A) (B := B) M i)
    (extendScalarsTermLinearEquiv (A := A) (B := B) M (i + 1))

/-- Helper for Lemma 15.97.3: the target comparison equivalence acts coordinatewise on pairs. -/
private lemma etaPresentationBaseChangeTargetEquiv_toLinearMap_apply
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (y :
      ((scalarExtendedComplex (A := A) (B := B) M).X i : ModuleCat B) ×
        ((scalarExtendedComplex (A := A) (B := B) M).X (i + 1) : ModuleCat B)) :
    (etaPresentationBaseChangeTargetEquiv (A := A) (B := B) M i).toLinearMap y =
      ((extendScalarsTermLinearEquiv (A := A) (B := B) M i y.1),
        (extendScalarsTermLinearEquiv (A := A) (B := B) M (i + 1) y.2)) := by
  -- Unfold the product comparison once so later proofs can rewrite by name instead of reducing
  -- `LinearEquiv.prodCongr` inside larger tensor calculations.
  rfl

/-- Helper for Lemma 15.97.3: on pure tensors, the transported scalar-extended differential is
the base-changed original differential. -/
private lemma extendScalars_differential_tensor_apply
    (M : CpxA) (i : ℤ) (b : B) (x : M.X i) :
    (extendScalarsTermLinearEquiv (A := A) (B := B) M (i + 1))
      ((((scalarExtendedComplex (A := A) (B := B) M).d i (i + 1)).hom)
        ((extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm (b ⊗ₜ[A] x))) =
      b ⊗ₜ[A] (((M.d i (i + 1)).hom) x) := by
  -- Rewrite the mapped differential through `extendScalars.map` and evaluate on a pure tensor.
  change
    (LinearMap.baseChange B (ModuleCat.Hom.hom (M.d i (i + 1)))) (b ⊗ₜ[A] x) =
      b ⊗ₜ[A] (ModuleCat.Hom.hom (M.d i (i + 1)) x)
  simpa [extendScalarsTermLinearEquiv, restrictScalarsSelfEquiv, scalarExtendedComplex,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d, ModuleCat.extendScalars,
    ModuleCat.ExtendScalars.obj', ModuleCat.ExtendScalars.map', LinearMap.baseChange_tmul,
    LinearMap.lTensor_tmul]

/-- Helper for Lemma 15.97.3: the termwise scalar-extension equivalence carries scalar multiples of
transported pure tensors back to the obvious scalar multiples on the tensor side. -/
private lemma extendScalarsTermLinearEquiv_smul_symm_tmul
    (f : A) (M : CpxA) (i : ℤ) (b : B) (x : M.X i) :
    (extendScalarsTermLinearEquiv (A := A) (B := B) M i)
      ((algebraMap A B f) •
        (extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm (b ⊗ₜ[A] x)) =
      (algebraMap A B f) • (b ⊗ₜ[A] x) := by
  -- The comparison map is `B`-linear, so it preserves the scalar action on the transported tensor.
  let e := extendScalarsTermLinearEquiv (A := A) (B := B) M i
  calc
    e ((algebraMap A B f) • e.symm (b ⊗ₜ[A] x)) =
      (algebraMap A B f) • e (e.symm (b ⊗ₜ[A] x)) := by
        simpa [e] using e.map_smul (algebraMap A B f) (e.symm (b ⊗ₜ[A] x))
    _ = (algebraMap A B f) • (b ⊗ₜ[A] x) := by
        rw [LinearEquiv.apply_symm_apply]

/-- Helper for Lemma 15.97.3: tensoring the original eta presentation map and then distributing
over the product gives the canonical pair `(g, d_B^i)` on the tensor-product side. -/
private lemma etaPresentationLinearMap_tensor_factorization
    (f : A) (M : CpxA) (i : ℤ) :
    (TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
        ((etaPresentationLinearMap f M i).baseChange B) =
      LinearMap.prod
        ((algebraMap A B f • LinearMap.id : B ⊗[A] (M.X i) →ₗ[B] B ⊗[A] (M.X i)))
        (((M.d i (i + 1)).hom).baseChange B) := by
  -- Evaluate on pure tensors and use the defining formulas for `etaPresentationLinearMap`.
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · rfl
  · intro b x
    ext <;> simp [etaPresentationLinearMap, LinearMap.baseChange_tmul, TensorProduct.tmul_smul]
  · intro x y hx hy
    simpa [LinearMap.map_add, hx, hy]

/-- Helper for Lemma 15.97.3: the tensorized eta presentation comparison can be rewritten
pointwise as the explicit pair map on the tensor-product domain. -/
private lemma etaPresentationLinearMap_tensor_factorization_apply
    (f : A) (M : CpxA) (i : ℤ) (z : B ⊗[A] M.X i) :
    ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
        ((etaPresentationLinearMap f M i).baseChange B)) z =
      (LinearMap.prod
        ((algebraMap A B f • LinearMap.id : B ⊗[A] M.X i →ₗ[B] B ⊗[A] M.X i))
        (((M.d i (i + 1)).hom).baseChange B)) z := by
  -- Freeze the tensor-side application once so the later tensor induction can work with an
  -- explicit pair-valued formula rather than reducing `TensorProduct.prodRight` on the fly.
  simpa [LinearMap.comp_apply] using
    LinearMap.congr_fun
      (etaPresentationLinearMap_tensor_factorization (A := A) (B := B) f M i) z

/-- Helper for Lemma 15.97.3: after identifying the scalar-extended terms with tensor products,
the eta presentation map agrees with the tensor extension of the original presentation on the
common tensor-product domain. -/
private lemma etaPresentationLinearMap_baseChange_factorization_on_tensor_domain
    (f : A) (M : CpxA) (i : ℤ) :
    ((etaPresentationBaseChangeTargetEquiv (A := A) (B := B) M i).toLinearMap.comp
        (etaPresentationLinearMap (algebraMap A B f)
          (scalarExtendedComplex (A := A) (B := B) M) i)).comp
      (extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm.toLinearMap =
      (TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
        ((etaPresentationLinearMap f M i).baseChange B) := by
  -- Route correction: compare both maps first on the common tensor-product domain, so the two
  -- transport issues reduce to one scalar-action rewrite and one differential rewrite.
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · -- Both sides are linear maps, so they agree at `0`.
    constructor <;> simp [LinearMap.comp_apply, etaPresentationLinearMap]
  · intro b x
    -- Rewrite both sides to explicit pair-valued formulas before comparing coordinates.
    rw [LinearMap.comp_apply, LinearMap.comp_apply, etaPresentationBaseChangeTargetEquiv_toLinearMap_apply]
    rw [etaPresentationLinearMap_tensor_factorization_apply]
    -- The first coordinate is the scalar action, and the second coordinate is the differential.
    ext
    · change
        (extendScalarsTermLinearEquiv (A := A) (B := B) M i)
            ((algebraMap A B f) •
              (extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm (b ⊗ₜ[A] x)) =
          (algebraMap A B f) • (b ⊗ₜ[A] x)
      have hsmul :=
        (extendScalarsTermLinearEquiv (A := A) (B := B) M i).map_smul
          (algebraMap A B f)
          ((extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm (b ⊗ₜ[A] x))
      calc
        (extendScalarsTermLinearEquiv (A := A) (B := B) M i)
            ((algebraMap A B f) •
              (extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm (b ⊗ₜ[A] x)) =
          (algebraMap A B f) •
            (extendScalarsTermLinearEquiv (A := A) (B := B) M i)
              ((extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm (b ⊗ₜ[A] x)) := by
                exact hsmul
        _ = (algebraMap A B f) • (b ⊗ₜ[A] x) := by
              rw [LinearEquiv.apply_symm_apply]
    · change
        (extendScalarsTermLinearEquiv (A := A) (B := B) M (i + 1))
            ((((scalarExtendedComplex (A := A) (B := B) M).d i (i + 1)).hom)
              ((extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm (b ⊗ₜ[A] x))) =
          b ⊗ₜ[A] (((M.d i (i + 1)).hom) x)
      exact
        extendScalars_differential_tensor_apply
          (A := A) (B := B) (M := M) (i := i) b x
  · intro x y hx hy
    -- Bilinearity of all maps extends the pure-tensor computation to arbitrary tensors.
    simpa [LinearMap.comp_apply, LinearMap.map_add] using congrArg₂ HAdd.hAdd hx hy

/-- Helper for Lemma 15.97.3: after identifying the scalar-extended terms with tensor products,
the eta presentation map becomes the tensor extension of the original presentation. -/
private lemma etaPresentationLinearMap_baseChange_factorization
    (f : A) (M : CpxA) (i : ℤ) :
    (etaPresentationBaseChangeTargetEquiv (A := A) (B := B) M i).toLinearMap.comp
        (etaPresentationLinearMap (algebraMap A B f)
          (scalarExtendedComplex (A := A) (B := B) M) i) =
      ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
          ((etaPresentationLinearMap f M i).baseChange B)).comp
        (extendScalarsTermLinearEquiv (A := A) (B := B) M i).toLinearMap := by
  -- Evaluate the tensor-domain comparison on `extendScalarsTermLinearEquiv M i x` so the inverse
  -- comparison on the source collapses by `symm_apply_apply`.
  apply LinearMap.ext
  intro x
  have hx :=
    LinearMap.congr_fun
      (etaPresentationLinearMap_baseChange_factorization_on_tensor_domain
        (A := A) (B := B) f M i)
      ((extendScalarsTermLinearEquiv (A := A) (B := B) M i) x)
  change
    ((extendScalarsTermLinearEquiv (A := A) (B := B) M i)
        ((etaPresentationLinearMap (algebraMap A B f)
          (scalarExtendedComplex (A := A) (B := B) (M := M)) i)
          ((extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm
            ((extendScalarsTermLinearEquiv (A := A) (B := B) M i) x))).1,
      (extendScalarsTermLinearEquiv (A := A) (B := B) M (i + 1))
        ((etaPresentationLinearMap (algebraMap A B f)
          (scalarExtendedComplex (A := A) (B := B) (M := M)) i)
          ((extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm
            ((extendScalarsTermLinearEquiv (A := A) (B := B) M i) x))).2) =
      ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
        ((etaPresentationLinearMap f M i).baseChange B))
          ((extendScalarsTermLinearEquiv (A := A) (B := B) M i) x) at hx
  rw [LinearEquiv.symm_apply_apply] at hx
  change
    ((extendScalarsTermLinearEquiv (A := A) (B := B) M i)
        ((etaPresentationLinearMap (algebraMap A B f)
          (scalarExtendedComplex (A := A) (B := B) (M := M)) i x).1),
      (extendScalarsTermLinearEquiv (A := A) (B := B) M (i + 1))
        ((etaPresentationLinearMap (algebraMap A B f)
          (scalarExtendedComplex (A := A) (B := B) (M := M)) i x).2)) =
      ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
        ((etaPresentationLinearMap f M i).baseChange B))
          ((extendScalarsTermLinearEquiv (A := A) (B := B) M i) x)
  exact hx

/-- Helper for Lemma 15.97.3: base change identifies the tensorized subtype of the range of a
linear map with the range of the tensorized map itself. -/
private lemma range_subtype_baseChange_eq_range_baseChange
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (g : M →ₗ[A] N) :
    LinearMap.range (((LinearMap.range g).subtype).baseChange B) =
      LinearMap.range (g.baseChange B) := by
  -- Factor `g` through its range before tensoring, so the tensorized range restriction witnesses
  -- that tensoring the subtype inclusion does not change the image.
  have hfactor : g = (LinearMap.range g).subtype.comp g.rangeRestrict := by
    ext x
    rfl
  have hcomp :
      g.baseChange B =
        ((LinearMap.range g).subtype.baseChange B).comp (g.rangeRestrict.baseChange B) := by
    have hbase :=
      LinearMap.baseChange_comp (A := B) (f := g.rangeRestrict) ((LinearMap.range g).subtype)
    rw [hfactor] at hbase
    exact hbase
  rw [hcomp, LinearMap.range_comp_of_range_eq_top]
  rw [LinearMap.range_eq_top]
  simpa [LinearMap.baseChange_eq_ltensor] using
    LinearMap.lTensor_surjective B g.surjective_rangeRestrict

/-- Helper for Lemma 15.97.3: tensoring the quotient map by a submodule identifies its kernel with
the canonical tensorized submodule. -/
private lemma ker_mkQ_baseChange_eq
    {M : Type*} [AddCommGroup M] [Module A M] (P : Submodule A M) :
    LinearMap.ker (P.mkQ.baseChange B) = P.baseChange B := by
  -- Rewrite the tensorized quotient map in the canonical `lTensor` form and use its kernel owner
  -- theorem directly.
  ext x
  have hx := congrArg (fun S : Submodule A (TensorProduct A B M) => x ∈ S) (lTensor_mkQ B P)
  simpa [LinearMap.baseChange_eq_ltensor, Submodule.baseChange] using hx

/-- Helper for Lemma 15.97.3: the transported range of the scalar-extended eta presentation is the
range of the tensorized original presentation after distributing over the product target. -/
private lemma etaPresentationLinearMap_baseChange_range_eq
    (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    Submodule.map
        (etaPresentationBaseChangeTargetEquiv (A := A) (B := B) M i).toLinearMap
        (LinearMap.range
          (etaPresentationLinearMap (algebraMap A B f)
            (scalarExtendedComplex (A := A) (B := B) M) i)) =
      LinearMap.range
        ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
          ((etaPresentationLinearMap f M i).baseChange B)) := by
  -- Take ranges in the factorization and use surjectivity of the source identification to discard
  -- the trailing comparison map on the tensor side.
  calc
    Submodule.map
        (etaPresentationBaseChangeTargetEquiv (A := A) (B := B) M i).toLinearMap
        (LinearMap.range
          (etaPresentationLinearMap (algebraMap A B f)
            (scalarExtendedComplex (A := A) (B := B) M) i)) =
      LinearMap.range
        ((etaPresentationBaseChangeTargetEquiv (A := A) (B := B) M i).toLinearMap.comp
          (etaPresentationLinearMap (algebraMap A B f)
            (scalarExtendedComplex (A := A) (B := B) M) i)) := by
          symm
          simpa [LinearMap.range_comp] using
            LinearMap.range_comp
              (etaPresentationLinearMap (algebraMap A B f)
                (scalarExtendedComplex (A := A) (B := B) M) i)
              ((etaPresentationBaseChangeTargetEquiv (A := A) (B := B) M i).toLinearMap)
    _ = LinearMap.range
          (((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
              ((etaPresentationLinearMap f M i).baseChange B)).comp
            (extendScalarsTermLinearEquiv (A := A) (B := B) M i).toLinearMap) := by
          rw [etaPresentationLinearMap_baseChange_factorization (A := A) (B := B) f M i]
    _ = LinearMap.range
          ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
            ((etaPresentationLinearMap f M i).baseChange B)) := by
          rw [LinearMap.range_comp_of_range_eq_top]
          rw [LinearMap.range_eq_top]
          exact (extendScalarsTermLinearEquiv (A := A) (B := B) M i).surjective

/-- Helper for Lemma 15.97.3: the tensorized quotient map by the range of `(f, d^i)` has kernel
equal to the range of the tensorized presentation map. -/
private lemma etaPresentationQuotient_baseChange_ker_eq
    (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    LinearMap.ker
        (((LinearMap.range (etaPresentationLinearMap f M i)).mkQ).baseChange B) =
      LinearMap.range ((etaPresentationLinearMap f M i).baseChange B) := by
  -- Rewrite the kernel of the tensorized quotient map through the canonical owner theorem, then
  -- identify the resulting tensorized range subtype with the range of the tensorized map.
  calc
    LinearMap.ker
        (((LinearMap.range (etaPresentationLinearMap f M i)).mkQ).baseChange B) =
      (LinearMap.range (etaPresentationLinearMap f M i)).baseChange B := by
        rw [ker_mkQ_baseChange_eq (A := A) (B := B)]
    _ = LinearMap.range (((LinearMap.range (etaPresentationLinearMap f M i)).subtype).baseChange B) := by
          rw [Submodule.baseChange]
    _ = LinearMap.range ((etaPresentationLinearMap f M i).baseChange B) := by
          simpa using
            range_subtype_baseChange_eq_range_baseChange (A := A) (B := B)
              (etaPresentationLinearMap f M i)

/-- Helper for Lemma 15.97.3: the scalar-extended eta presentation quotient is the tensor product
of the original quotient with `B`. -/
private noncomputable def etaPresentationQuotient_baseChange_linearEquiv
    (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    etaPresentationQuotient (algebraMap A B f)
        (scalarExtendedComplex (A := A) (B := B) M) i ≃ₗ[B]
      B ⊗[A] etaPresentationQuotient f M i := by
  let eTarget :
      etaPresentationQuotient (algebraMap A B f)
          (scalarExtendedComplex (A := A) (B := B) M) i ≃ₗ[B]
        (((B ⊗[A] M.X i) × (B ⊗[A] M.X (i + 1))) ⧸
          LinearMap.range
            ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
              ((etaPresentationLinearMap f M i).baseChange B))) :=
    -- First descend the target identification through the already-proved range equality.
    Submodule.Quotient.equiv
      (LinearMap.range
        (etaPresentationLinearMap (algebraMap A B f)
          (scalarExtendedComplex (A := A) (B := B) M) i))
      (LinearMap.range
        ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
          ((etaPresentationLinearMap f M i).baseChange B)))
      (etaPresentationBaseChangeTargetEquiv (A := A) (B := B) M i)
      (etaPresentationLinearMap_baseChange_range_eq (A := A) (B := B) f M i)
  let eProd :
      (((B ⊗[A] M.X i) × (B ⊗[A] M.X (i + 1))) ⧸
        LinearMap.range
          ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
            ((etaPresentationLinearMap f M i).baseChange B))) ≃ₗ[B]
        ((B ⊗[A] (M.X i × M.X (i + 1))) ⧸
          LinearMap.range ((etaPresentationLinearMap f M i).baseChange B)) :=
    -- Then move from the product target back to the canonical tensorized product target.
    (Submodule.Quotient.equiv
      (LinearMap.range ((etaPresentationLinearMap f M i).baseChange B))
      (LinearMap.range
        ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
          ((etaPresentationLinearMap f M i).baseChange B)))
      (TensorProduct.prodRight A B B (M.X i) (M.X (i + 1)))
      (by
        simpa [LinearMap.range_comp] using
          LinearMap.range_comp
            ((etaPresentationLinearMap f M i).baseChange B)
            ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap))).symm
  let q :
      B ⊗[A] (M.X i × M.X (i + 1)) →ₗ[B] B ⊗[A] etaPresentationQuotient f M i :=
    ((LinearMap.range (etaPresentationLinearMap f M i)).mkQ).baseChange B
  have hqsurj : Function.Surjective q := by
    -- Base change preserves surjectivity of the canonical quotient map.
    simpa [q, LinearMap.baseChange_eq_ltensor] using
      (LinearMap.lTensor_surjective B
        (Submodule.mkQ_surjective (LinearMap.range (etaPresentationLinearMap f M i))))
  have hrange : LinearMap.range q = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact hqsurj
  let eQuot :
      ((B ⊗[A] (M.X i × M.X (i + 1))) ⧸
        LinearMap.range ((etaPresentationLinearMap f M i).baseChange B)) ≃ₗ[B]
        B ⊗[A] etaPresentationQuotient f M i :=
    -- Finally rewrite the denominator to the kernel of the tensorized quotient map and collapse
    -- its full range back to the target module.
    (Submodule.quotEquivOfEq _ _
      (etaPresentationQuotient_baseChange_ker_eq (A := A) (B := B) f M i).symm).trans
      (q.quotKerEquivRange.trans ((LinearEquiv.ofEq _ _ hrange).trans Submodule.topEquiv))
  exact eTarget.trans (eProd.trans eQuot)

/-- Helper for Lemma 15.97.3: once the scalar-extended eta quotient is identified with
`B ⊗[A] etaPresentationQuotient f M i`, the remaining step is the base-change formula for the
corresponding Fitting ideal. -/
private lemma etaPresentationQuotient_fittingIdeal_baseChange
    (f : A) (M : CpxA) (i : ℤ) [Nontrivial A] [Nontrivial B]
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    Fit[B]_(Module.finrank A (M.X (i + 1)))(B ⊗[A] etaPresentationQuotient f M i) =
      Ideal.map (algebraMap A B)
        (Fit[A]_(Module.finrank A (M.X (i + 1)))(etaPresentationQuotient f M i)) := by
  -- Route correction: the target file now avoids the broken import of `Lemma_15_8_4`, so the
  -- remaining gap is to re-establish the Fitting-ideal base-change step locally from the minors
  -- description of the eta presentation quotient.
  -- TODO: rewrite `Fit` for `etaPresentationQuotient f M i` as the source-rank minor ideal of the
  -- chosen matrix of `etaPresentationLinearMap f M i`, compare that matrix after scalar extension,
  -- and conclude via coefficientwise mapping of minors.
  sorry

/-
Domain-style sampling:
- primary domain: determinantal ideals for the Berthelot-Ogus presentation map `(f, d^i)` under
  tensor-product base change;
- sampled owner declarations:
  `etaDeterminantalIdeal`,
  `etaPresentationQuotient`,
  `(ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)`,
  `fittingIdeal_eq_of_linearEquiv`,
  `fittingIdeal_baseChange`;
- best owner abstraction:
  `source-facing`: `etaDeterminantalIdeal`, the degree-`i` ideal attached to `(f, d^i)`;
  `core/canonical`: the intrinsic Fitting ideal together with the chapter base-change owner
    `fittingIdeal_baseChange`;
  `bridge/view`: the scalar-extended cochain complex
    `((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M`;
- primitive data vs. derived API: the primitive source-facing data are the presentation map
  `etaPresentationLinearMap f M i` and its quotient; the base-changed complex itself is derived
  bridge data, and the equality below is the source-facing statement. -/

-- Proof sketch: `etaDeterminantalIdeal` is the intrinsic Fitting ideal of
-- `etaPresentationQuotient f M i`. After scalar extension, the degree terms remain finite free by
-- the canonical tensor-product instances.
-- Comparing the scalar-extended quotient with the quotient attached to the canonical scalar
-- extension `((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M`
-- reduces the statement to the chapter owner
-- `fittingIdeal_baseChange`.
/-- Lemma 15.97.3: the degree-`i` determinantal ideal attached to `(f, d^i)` commutes with base
change along `A → B`. The primitive data are only the finite free terms in degrees `i` and
`i + 1`; boundedness and nonzerodivisor hypotheses are not needed for this base-change identity
itself. -/
theorem etaDeterminantalIdeal_baseChange
    (f : A) (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    I[algebraMap A B f]_(i)(
      (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M)) =
      Ideal.map (algebraMap A B)
        (I[f]_(i)(M)) := by
  by_cases hB : Nontrivial B
  · letI := hB
    letI : Nontrivial A := by
      refine ⟨⟨(0 : A), (1 : A), ?_⟩⟩
      intro h01
      have h01B : (0 : B) = 1 := by
        simpa using congrArg (algebraMap A B) h01
      exact zero_ne_one h01B
    let bi := Module.Free.chooseBasis A (M.X i)
    let bi1 := Module.Free.chooseBasis A (M.X (i + 1))
    let _ : Module.Finite A (M.X i × M.X (i + 1)) :=
      Module.Finite.of_basis (bi.prod bi1)
    let _ : Module.Finite A (etaPresentationQuotient f M i) :=
      Module.Finite.quotient A (LinearMap.range (etaPresentationLinearMap f M i))
    let bsi :=
      bi.baseChange B |>.map (extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm
    let bsi1 :=
      bi1.baseChange B |>.map (extendScalarsTermLinearEquiv (A := A) (B := B) M (i + 1)).symm
    let _ : Module.Finite B
        (((scalarExtendedComplex (A := A) (B := B) M).X i : ModuleCat B) ×
          ((scalarExtendedComplex (A := A) (B := B) M).X (i + 1) : ModuleCat B)) :=
      Module.Finite.of_basis (bsi.prod bsi1)
    let _ : Module.Finite B
        (etaPresentationQuotient (algebraMap A B f)
          (scalarExtendedComplex (A := A) (B := B) M) i) :=
      Module.Finite.quotient B
        (LinearMap.range
          (etaPresentationLinearMap (algebraMap A B f)
            (scalarExtendedComplex (A := A) (B := B) M) i))
    let eBase :=
      etaPresentationQuotient_baseChange_linearEquiv (A := A) (B := B) f M i
    -- Rewrite the scalar-extended quotient by the explicit base-change linear equivalence.
    calc
      I[algebraMap A B f]_(i)(
        (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M)) =
        Fit[B]_(Module.finrank B ((scalarExtendedComplex (A := A) (B := B) M).X (i + 1) : ModuleCat B))(B ⊗[A] etaPresentationQuotient f M i) := by
            -- The determinantal ideal is the Fitting ideal of the eta-presentation quotient.
            simpa [etaDeterminantalIdeal] using
              fittingIdeal_eq_of_linearEquiv B
                (etaPresentationQuotient (algebraMap A B f)
                  (scalarExtendedComplex (A := A) (B := B) M) i)
                (Module.finrank B
                  ((scalarExtendedComplex (A := A) (B := B) M).X (i + 1) : ModuleCat B))
                eBase
      _ = Fit[B]_(Module.finrank A (M.X (i + 1)))(B ⊗[A] etaPresentationQuotient f M i) := by
            -- The finite rank of the target term is unchanged by scalar extension.
            rw [extendScalars_mapHomologicalComplex_term_finrank_eq
              (A := A) (B := B) (M := M) (j := i + 1)]
      _ = Ideal.map (algebraMap A B)
            (Fit[A]_(Module.finrank A (M.X (i + 1)))(etaPresentationQuotient f M i)) := by
            -- The remaining step is the local base-change formula for the eta presentation
            -- quotient itself.
            simpa using
              etaPresentationQuotient_fittingIdeal_baseChange
                (A := A) (B := B) (f := f) (M := M) (i := i)
      _ = Ideal.map (algebraMap A B) (I[f]_(i)(M)) := by
            rfl
  · letI : Subsingleton B := not_nontrivial_iff_subsingleton.mp hB
    -- In the degenerate target ring, all ideals of `B` coincide.
    exact Subsingleton.elim _ _

end
