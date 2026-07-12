import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import StacksProject_2024.Chap15.Definition_15_8_3
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Lemma_15_8_4
import StacksProject_2024.Chap15.PrincipalIdeal
import StacksProject_2024.Chap15.Lemma_15_76_8
import Mathlib.Data.Int.Range
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open scoped BigOperators
open scoped FittingIdeal
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "Q" => (DerivedCategory.Q : CpxA ⥤ DModA)

/- Domain-style sampling:
- primary domain: determinantal ideals of bounded finite-free cochain complexes, expressed through
  the intrinsic Fitting ideal of the degree-`i` presentation map `(f, d^i)`;
- sampled owner declarations:
  `fittingIdeal`,
  `fittingIdeal_eq_of_linearEquiv`,
  `fittingIdeal_baseChange`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `CategoryTheory.IsIsomorphic`;
- best owner abstraction:
  `source-facing`: `etaDeterminantalIdeal`, the degree-`i` ideal attached to `(f, d^i)`;
  `core/canonical`: the chapter Fitting-ideal owner `fittingIdeal`;
  `bridge/view`: the specific presentation map `etaPresentationLinearMap` and its quotient
    `etaPresentationQuotient`;
- primitive data vs. derived API: the primitive data are the presentation map and its quotient.
  The alternating rank tail is derived theorem-supporting data, and the pointwise rank helper stays
  internal. -/

/-- The linear map `(f, d^i) : M^i → M^i ⊕ M^{i + 1}` used to define the determinantal ideal
attached to `M^•` and `f` in degree `i`. -/
abbrev etaPresentationLinearMap (f : A) (M : CpxA) (i : ℤ) :
    M.X i →ₗ[A] M.X i × M.X (i + 1) :=
  LinearMap.prod ((f • LinearMap.id : M.X i →ₗ[A] M.X i)) (M.d i (i + 1)).hom

/-- The quotient module presented by `(f, d^i) : M^i → M^i ⊕ M^{i + 1}`. -/
abbrev etaPresentationQuotient (f : A) (M : CpxA) (i : ℤ) :=
  (M.X i × M.X (i + 1)) ⧸ LinearMap.range (etaPresentationLinearMap f M i)

/-- The rank of the `j`th term of a termwise finite free complex, computed by `Module.finrank`. -/
private def termwiseFiniteFreeRank (M : CpxA) [CochainComplex.IsTermwiseFiniteFree M]
    (j : ℤ) : ℕ :=
  Module.finrank A (M.X j)

/-- The truncated alternating tail sum `∑_{j = i}^b (-1)^{j - i} rk(M^j)` for a termwise finite
free complex. -/
def alternatingRankTail (M : CpxA) [CochainComplex.IsTermwiseFiniteFree M] (i b : ℤ) : ℤ :=
  ((Int.range i (b + 1)).map fun j ↦
      ((-1 : ℤ) ^ Int.toNat (j - i)) * (termwiseFiniteFreeRank M j : ℤ)).sum

/-- The ideal `I_i(M^•, f)`, defined intrinsically as the Fitting ideal of the cokernel of the map
`(f, d^i) : M^i → M^i ⊕ M^{i + 1}`. -/
def etaDeterminantalIdeal (f : A) (M : CpxA) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    Ideal A :=
  Fit[A]_(Module.finrank A (M.X (i + 1)))(etaPresentationQuotient f M i)

namespace EtaDeterminantalIdeal

scoped notation "I[" f "]_(" i ")(" M ")" => etaDeterminantalIdeal f M i

end EtaDeterminantalIdeal

open scoped EtaDeterminantalIdeal

local instance termwiseFiniteFreeTermModuleFree
    {M : CpxA} [hMff : CochainComplex.IsTermwiseFiniteFree M] (j : ℤ) :
    Module.Free A (M.X j) :=
  inferInstance

local instance termwiseFiniteFreeTermModuleFinite
    {M : CpxA} [hMff : CochainComplex.IsTermwiseFiniteFree M] (j : ℤ) :
    Module.Finite A (M.X j) :=
  inferInstance

section BaseChange

variable {B : Type u} [CommRing B] [Algebra A B]

/-- Helper for Lemma 15.97.1: the scalar-extended cochain complex obtained from `M`. -/
private abbrev scalarExtendedComplex (M : CpxA) :
    CochainComplex (ModuleCat B) ℤ :=
  (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj M)

/-- Helper for Lemma 15.97.1: after restricting scalars along `A → B`, the free rank-one
`B`-module is still canonically `B` itself. -/
private noncomputable def restrictScalarsSelfEquiv :
    ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) ≃ₗ[B] B :=
  { __ := AddEquiv.refl B
    map_smul' := fun _ _ ↦ rfl }

/-- Helper for Lemma 15.97.1: the restricted `B`-module structure on `B` is compatible with the
ambient scalar tower `A → B → B`. -/
private instance restrictScalarsSelfIsScalarTower :
    IsScalarTower A B ↑((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)) :=
  IsScalarTower.of_algebraMap_smul fun r s ↦ by
    rfl

/-- Helper for Lemma 15.97.1: each term of the scalar-extended complex identifies with the
canonical tensor-product model. -/
private noncomputable def extendScalarsTermLinearEquiv (M : CpxA) (i : ℤ) :
    ((scalarExtendedComplex (A := A) (B := B) M).X i : ModuleCat B) ≃ₗ[B] (B ⊗[A] (M.X i)) := by
  simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsSelfEquiv (A := A) (B := B))
      (LinearEquiv.refl A (M.X i)))

/-- Helper for Lemma 15.97.1: scalar extension preserves freeness of the individual terms. -/
noncomputable private instance extendScalars_mapHomologicalComplex_term_moduleFree
    (M : CpxA) (i : ℤ) [Module.Free A (M.X i)] :
    Module.Free B
      ((scalarExtendedComplex (A := A) (B := B) M).X i : ModuleCat B) := by
  let b := (Module.Free.chooseBasis A (M.X i)).baseChange B
  exact Module.Free.of_basis (b.map (extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm)

/-- Helper for Lemma 15.97.1: scalar extension preserves finite generation of the individual
terms. -/
noncomputable private instance extendScalars_mapHomologicalComplex_term_moduleFinite
    (M : CpxA) (i : ℤ) [Module.Free A (M.X i)] [Module.Finite A (M.X i)] :
    Module.Finite B
      ((scalarExtendedComplex (A := A) (B := B) M).X i : ModuleCat B) := by
  let b := (Module.Free.chooseBasis A (M.X i)).baseChange B
  exact Module.Finite.of_basis
    (b.map (extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm)

/-- Helper for Lemma 15.97.1: scalar extension preserves the finite rank of each finite-free
term. -/
private lemma extendScalars_mapHomologicalComplex_term_finrank_eq
    (M : CpxA) (j : ℤ)
    [Nontrivial A] [Nontrivial B] [Module.Free A (M.X j)] [Module.Finite A (M.X j)] :
    Module.finrank B ((scalarExtendedComplex (A := A) (B := B) M).X j : ModuleCat B) =
      Module.finrank A (M.X j) := by
  -- Proof comment: first transport the scalar-extended term to the tensor-product model, then
  -- apply the standard finrank formula for base change.
  calc
    Module.finrank B ((scalarExtendedComplex (A := A) (B := B) M).X j : ModuleCat B) =
        Module.finrank B (B ⊗[A] (M.X j)) :=
      (extendScalarsTermLinearEquiv (A := A) (B := B) M j).finrank_eq
    _ = Module.finrank A (M.X j) :=
      Module.finrank_baseChange (S := A) (R := B) (M' := M.X j)

/-- Helper for Lemma 15.97.1: the target of the scalar-extended eta presentation identifies with
the product of the base-changed terms. -/
private noncomputable abbrev etaPresentationBaseChangeTargetEquiv
    (M : CpxA) (i : ℤ) :
    (((scalarExtendedComplex (A := A) (B := B) M).X i : ModuleCat B) ×
        ((scalarExtendedComplex (A := A) (B := B) M).X (i + 1) : ModuleCat B)) ≃ₗ[B]
      ((B ⊗[A] (M.X i)) × (B ⊗[A] (M.X (i + 1))) : Type u) :=
  LinearEquiv.prodCongr
    (extendScalarsTermLinearEquiv (A := A) (B := B) M i)
    (extendScalarsTermLinearEquiv (A := A) (B := B) M (i + 1))

/-- Helper for Lemma 15.97.1: the target comparison equivalence acts coordinatewise on pairs. -/
private lemma etaPresentationBaseChangeTargetEquiv_toLinearMap_apply
    (M : CpxA) (i : ℤ)
    (y :
      ((scalarExtendedComplex (A := A) (B := B) M).X i : ModuleCat B) ×
        ((scalarExtendedComplex (A := A) (B := B) M).X (i + 1) : ModuleCat B)) :
    (etaPresentationBaseChangeTargetEquiv (A := A) (B := B) M i).toLinearMap y =
      ((extendScalarsTermLinearEquiv (A := A) (B := B) M i y.1),
        (extendScalarsTermLinearEquiv (A := A) (B := B) M (i + 1) y.2)) := by
  -- Proof comment: keep the product comparison explicit so later tensor calculations can rewrite
  -- by name instead of unfolding `LinearEquiv.prodCongr` under quotients.
  rfl

/-- Helper for Lemma 15.97.1: on pure tensors, the transported scalar-extended differential is
the base-changed original differential. -/
private lemma extendScalars_differential_tensor_apply
    (M : CpxA) (i : ℤ) (b : B) (x : M.X i) :
    (extendScalarsTermLinearEquiv (A := A) (B := B) M (i + 1))
      ((((scalarExtendedComplex (A := A) (B := B) M).d i (i + 1)).hom)
        ((extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm (b ⊗ₜ[A] x))) =
      b ⊗ₜ[A] (((M.d i (i + 1)).hom) x) := by
  -- Proof comment: after rewriting the differential through `extendScalars.map`, this is the
  -- defining formula for `LinearMap.baseChange` on a pure tensor.
  change
    (LinearMap.baseChange B (ModuleCat.Hom.hom (M.d i (i + 1)))) (b ⊗ₜ[A] x) =
      b ⊗ₜ[A] (ModuleCat.Hom.hom (M.d i (i + 1)) x)
  simpa [extendScalarsTermLinearEquiv, restrictScalarsSelfEquiv, scalarExtendedComplex,
    CategoryTheory.Functor.mapHomologicalComplex_obj_d, ModuleCat.extendScalars,
    ModuleCat.ExtendScalars.obj', ModuleCat.ExtendScalars.map', LinearMap.baseChange_tmul,
    LinearMap.lTensor_tmul]

/-- Helper for Lemma 15.97.1: the termwise scalar-extension equivalence carries scalar multiples
of transported pure tensors to the obvious scalar multiples on the tensor side. -/
private lemma extendScalarsTermLinearEquiv_smul_symm_tmul
    (f : A) (M : CpxA) (i : ℤ) (b : B) (x : M.X i) :
    (extendScalarsTermLinearEquiv (A := A) (B := B) M i)
      ((algebraMap A B f) •
        (extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm (b ⊗ₜ[A] x)) =
      (algebraMap A B f) • (b ⊗ₜ[A] x) := by
  -- Proof comment: the comparison map is `B`-linear, so it preserves the scalar action.
  let e := extendScalarsTermLinearEquiv (A := A) (B := B) M i
  calc
    e ((algebraMap A B f) • e.symm (b ⊗ₜ[A] x)) =
        (algebraMap A B f) • e (e.symm (b ⊗ₜ[A] x)) := by
      simpa [e] using e.map_smul (algebraMap A B f) (e.symm (b ⊗ₜ[A] x))
    _ = (algebraMap A B f) • (b ⊗ₜ[A] x) := by
      rw [LinearEquiv.apply_symm_apply]

/-- Helper for Lemma 15.97.1: tensoring the eta presentation map and distributing over the
product gives the canonical pair `(g, d_B^i)` on the tensor-product side. -/
private lemma etaPresentationLinearMap_tensor_factorization
    (f : A) (M : CpxA) (i : ℤ) :
    (TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
        ((etaPresentationLinearMap f M i).baseChange B) =
      LinearMap.prod
        ((algebraMap A B f • LinearMap.id : B ⊗[A] (M.X i) →ₗ[B] B ⊗[A] (M.X i)))
        (((M.d i (i + 1)).hom).baseChange B) := by
  -- Proof comment: evaluate on pure tensors and use the defining formulas for
  -- `etaPresentationLinearMap`.
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · rfl
  · intro b x
    ext <;> simp [etaPresentationLinearMap, LinearMap.baseChange_tmul, TensorProduct.tmul_smul]
  · intro x y hx hy
    simpa [LinearMap.map_add, hx, hy]

/-- Helper for Lemma 15.97.1: after identifying the scalar-extended terms with tensor products,
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
  -- Route correction: compare both maps first on the common tensor-product domain, so the scalar
  -- transport and the differential transport each become a single named rewrite.
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · constructor <;> simp [LinearMap.comp_apply, etaPresentationLinearMap]
  · intro b x
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      etaPresentationBaseChangeTargetEquiv_toLinearMap_apply]
    rw [etaPresentationLinearMap_tensor_factorization]
    ext
    · change
        (extendScalarsTermLinearEquiv (A := A) (B := B) M i)
            ((algebraMap A B f) •
              (extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm (b ⊗ₜ[A] x)) =
          (algebraMap A B f) • (b ⊗ₜ[A] x)
      exact
        extendScalarsTermLinearEquiv_smul_symm_tmul
          (A := A) (B := B) (f := f) (M := M) (i := i) b x
    · change
        (extendScalarsTermLinearEquiv (A := A) (B := B) M (i + 1))
            ((((scalarExtendedComplex (A := A) (B := B) M).d i (i + 1)).hom)
              ((extendScalarsTermLinearEquiv (A := A) (B := B) M i).symm (b ⊗ₜ[A] x))) =
          b ⊗ₜ[A] (((M.d i (i + 1)).hom) x)
      exact
        extendScalars_differential_tensor_apply
          (A := A) (B := B) (M := M) (i := i) b x
  · intro x y hx hy
    simpa [LinearMap.comp_apply, LinearMap.map_add] using congrArg₂ HAdd.hAdd hx hy

/-- Helper for Lemma 15.97.1: after identifying the scalar-extended terms with tensor products,
the eta presentation map becomes the tensor extension of the original presentation. -/
private lemma etaPresentationLinearMap_baseChange_factorization
    (f : A) (M : CpxA) (i : ℤ) :
    (etaPresentationBaseChangeTargetEquiv (A := A) (B := B) M i).toLinearMap.comp
        (etaPresentationLinearMap (algebraMap A B f)
          (scalarExtendedComplex (A := A) (B := B) M) i) =
      ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
          ((etaPresentationLinearMap f M i).baseChange B)).comp
        (extendScalarsTermLinearEquiv (A := A) (B := B) M i).toLinearMap := by
  -- Proof comment: evaluate the tensor-domain identity on the image of `x` so the inverse source
  -- comparison collapses by `symm_apply_apply`.
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

/-- Helper for Lemma 15.97.1: tensoring the range inclusion of a linear map gives the range of
the tensorized map. -/
private lemma range_subtype_baseChange_eq_range_baseChange
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (g : M →ₗ[A] N) :
    LinearMap.range (((LinearMap.range g).subtype).baseChange B) =
      LinearMap.range (g.baseChange B) := by
  -- Proof comment: factor `g` through its range before tensoring; the tensorized range
  -- restriction is surjective onto the tensorized image.
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

/-- Helper for Lemma 15.97.1: tensoring the quotient map by a submodule identifies its kernel
with the canonical tensorized submodule. -/
private lemma ker_mkQ_baseChange_eq
    {M : Type*} [AddCommGroup M] [Module A M] (P : Submodule A M) :
    LinearMap.ker (P.mkQ.baseChange B) = P.baseChange B := by
  -- Proof comment: rewrite the tensorized quotient map in the canonical `lTensor` form and use
  -- the kernel owner from the Fitting-ideal base-change file.
  ext x
  have hx := congrArg (fun S : Submodule A (TensorProduct A B M) ↦ x ∈ S) (lTensor_mkQ B P)
  simpa [LinearMap.baseChange_eq_ltensor, Submodule.baseChange] using hx

/-- Helper for Lemma 15.97.1: the transported range of the scalar-extended eta presentation is
the range of the tensorized original presentation after distributing over the product target. -/
private lemma etaPresentationLinearMap_baseChange_range_eq
    (f : A) (M : CpxA) (i : ℤ) :
    Submodule.map
        (etaPresentationBaseChangeTargetEquiv (A := A) (B := B) M i).toLinearMap
        (LinearMap.range
          (etaPresentationLinearMap (algebraMap A B f)
            (scalarExtendedComplex (A := A) (B := B) M) i)) =
      LinearMap.range
        ((TensorProduct.prodRight A B B (M.X i) (M.X (i + 1))).toLinearMap.comp
          ((etaPresentationLinearMap f M i).baseChange B)) := by
  -- Proof comment: take ranges in the factorization and discard the trailing source comparison by
  -- surjectivity of the termwise scalar-extension equivalence.
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

/-- Helper for Lemma 15.97.1: the tensorized quotient map by the range of `(f, d^i)` has kernel
equal to the range of the tensorized presentation map. -/
private lemma etaPresentationQuotient_baseChange_ker_eq
    (f : A) (M : CpxA) (i : ℤ) :
    LinearMap.ker
        (((LinearMap.range (etaPresentationLinearMap f M i)).mkQ).baseChange B) =
      LinearMap.range ((etaPresentationLinearMap f M i).baseChange B) := by
  -- Proof comment: rewrite the kernel through the canonical tensorized quotient map and then
  -- identify the tensorized range subtype with the range of the tensorized map itself.
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

/-- Helper for Lemma 15.97.1: the scalar-extended eta presentation quotient is the tensor product
of the original quotient with `B`. -/
private noncomputable def etaPresentationQuotient_baseChange_linearEquiv
    (f : A) (M : CpxA) (i : ℤ) :
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
    -- Proof comment: tensoring the canonical quotient map preserves surjectivity.
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
    (Submodule.quotEquivOfEq _ _
      (etaPresentationQuotient_baseChange_ker_eq (A := A) (B := B) f M i).symm).trans
      (q.quotKerEquivRange.trans ((LinearEquiv.ofEq _ _ hrange).trans Submodule.topEquiv))
  exact eTarget.trans (eProd.trans eQuot)

/-- Helper for Lemma 15.97.1: the determinantal ideal attached to `(f, d^i)` commutes with base
change along `A → B`. -/
private theorem etaDeterminantalIdeal_baseChange_aux
    (f : A) (M : CpxA) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    I[algebraMap A B f]_(i)(scalarExtendedComplex (A := A) (B := B) M) =
      Ideal.map (algebraMap A B) (I[f]_(i)(M)) := by
  let bi := Module.Free.chooseBasis A (M.X i)
  let bi1 := Module.Free.chooseBasis A (M.X (i + 1))
  let _ : Module.Finite A (M.X i × M.X (i + 1)) :=
    Module.Finite.of_basis (bi.prod bi1)
  let _ : Module.Finite A (etaPresentationQuotient f M i) :=
    Module.Finite.quotient A (LinearMap.range (etaPresentationLinearMap f M i))
  -- Proof comment: first transport the scalar-extended presentation quotient to the tensor
  -- product model, then rewrite the Fitting index by finite-rank preservation under scalar
  -- extension, and finally apply the canonical Fitting-ideal base-change theorem.
  calc
    I[algebraMap A B f]_(i)(scalarExtendedComplex (A := A) (B := B) M) =
      Fit[B]_(Module.finrank B ((scalarExtendedComplex (A := A) (B := B) M).X (i + 1) :
        ModuleCat B))(B ⊗[A] etaPresentationQuotient f M i) := by
        simpa [etaDeterminantalIdeal] using
          fittingIdeal_eq_of_linearEquiv (R := B)
            (M :=
              etaPresentationQuotient (algebraMap A B f)
                (scalarExtendedComplex (A := A) (B := B) M) i)
            (M' := B ⊗[A] etaPresentationQuotient f M i)
            (k :=
              Module.finrank B ((scalarExtendedComplex (A := A) (B := B) M).X (i + 1) :
                ModuleCat B))
            (etaPresentationQuotient_baseChange_linearEquiv
              (A := A) (B := B) (f := f) (M := M) (i := i))
    _ = Fit[B]_(Module.finrank A (M.X (i + 1)))(B ⊗[A] etaPresentationQuotient f M i) := by
          rw [extendScalars_mapHomologicalComplex_term_finrank_eq
            (A := A) (B := B) (M := M) (j := i + 1)]
    _ = Ideal.map (algebraMap A B)
          (Fit[A]_(Module.finrank A (M.X (i + 1)))(etaPresentationQuotient f M i)) := by
          simpa using
            (fittingIdeal_baseChange
              (R := A) (M := etaPresentationQuotient f M i)
              (R' := B) (k := Module.finrank A (M.X (i + 1))))
    _ = Ideal.map (algebraMap A B) (I[f]_(i)(M)) := by
          rfl

/-- Helper for Lemma 15.97.1: localizing the degree-`i` eta-determinantal ideal at a prime ideal
rewrites it as the eta-determinantal ideal of the localized complex. -/
lemma etaDeterminantalIdeal_map_atPrime
    (f : A) (M : CpxA) (i : ℤ) (p : PrimeSpectrum A)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))] :
    Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal)) (I[f]_(i)(M)) =
      I[algebraMap A (Localization.AtPrime p.asIdeal) f]_(i)
        (CategoryTheory.localizationAtPrimeComplex p M) := by
  -- Proof comment: specialize the base-change identity to the localization `A → A_𝔭` and then
  -- rewrite the scalar-extended complex by the source-facing localization owner.
  simpa [CategoryTheory.localizationAtPrimeComplex_def] using
    (etaDeterminantalIdeal_baseChange_aux
      (A := A) (B := Localization.AtPrime p.asIdeal) (f := f) (M := M) (i := i)).symm

end BaseChange

/-- Helper for Lemma 15.97.1: the product of the degree-`i` and degree-`i + 1` components of a
strict complex isomorphism. -/
private noncomputable def complexIsoComponentLinearEquiv
    {M N : CpxA} (e : M ≅ N) (i : ℤ) :
    ↑(M.X i) ≃ₗ[A] ↑(N.X i) :=
  LinearEquiv.ofLinear
    (e.hom.f i).hom
    (e.inv.f i).hom
    (by
      ext x
      exact
        LinearMap.congr_fun
          (congrArg ModuleCat.Hom.hom (congrArg (fun α : N ⟶ N ↦ α.f i) e.inv_hom_id)) x)
    (by
      ext x
      exact
        LinearMap.congr_fun
          (congrArg ModuleCat.Hom.hom (congrArg (fun α : M ⟶ M ↦ α.f i) e.hom_inv_id)) x)

/-- Helper for Lemma 15.97.1: the product of the degree-`i` and degree-`i + 1` components of a
strict complex isomorphism. -/
private abbrev etaPresentationIsoTargetEquiv
    {M N : CpxA} (e : M ≅ N) (i : ℤ) :
    (↑(M.X i) × ↑(M.X (i + 1))) ≃ₗ[A] (↑(N.X i) × ↑(N.X (i + 1))) :=
  LinearEquiv.prodCongr
    (complexIsoComponentLinearEquiv (A := A) e i)
    (complexIsoComponentLinearEquiv (A := A) e (i + 1))

/-- Helper for Lemma 15.97.1: a strict complex isomorphism intertwines the presentation maps
`(f, d^i)` in degree `i`. -/
private lemma etaPresentationLinearMap_iso_apply
    (f : A) {M N : CpxA} (e : M ≅ N) (i : ℤ) (x : ↑(M.X i)) :
    etaPresentationIsoTargetEquiv (A := A) e i (etaPresentationLinearMap f M i x) =
      etaPresentationLinearMap f N i ((complexIsoComponentLinearEquiv (A := A) e i) x) := by
  -- Proof comment: the first coordinate is `A`-linearity, and the second is exactly the
  -- cochain-map commutativity relation for `e`.
  ext <;> simp [etaPresentationIsoTargetEquiv, etaPresentationLinearMap]
  exact
    (LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (e.hom.comm i (i + 1))) x).symm

/-- Helper for Lemma 15.97.1: the target product equivalence sends the range of the presentation
map of `M` onto the range of the presentation map of `N`. -/
private lemma etaPresentationLinearMap_iso_range
    (f : A) {M N : CpxA} (e : M ≅ N) (i : ℤ) :
    (LinearMap.range (etaPresentationLinearMap f M i)).map
        (etaPresentationIsoTargetEquiv (A := A) e i).toLinearMap =
      LinearMap.range (etaPresentationLinearMap f N i) := by
  -- Proof comment: apply the intertwining identity on generators of the source and target
  -- ranges, using the inverse complex isomorphism for the reverse inclusion.
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨z, rfl⟩
    refine ⟨(complexIsoComponentLinearEquiv (A := A) e i) z, ?_⟩
    simpa using (etaPresentationLinearMap_iso_apply (A := A) (f := f) e i z).symm
  · rintro ⟨z, rfl⟩
    refine ⟨etaPresentationLinearMap f M i
        ((complexIsoComponentLinearEquiv (A := A) e i).symm z), ?_, ?_⟩
    · exact ⟨_, rfl⟩
    · simpa using
        etaPresentationLinearMap_iso_apply (A := A) (f := f) e i
          ((complexIsoComponentLinearEquiv (A := A) e i).symm z)

/-- Helper for Lemma 15.97.1: a strict complex isomorphism induces a linear equivalence between
the two presentation quotients in degree `i`. -/
private noncomputable def etaPresentationQuotientLinearEquivOfIso
    (f : A) {M N : CpxA} (e : M ≅ N) (i : ℤ) :
    etaPresentationQuotient f M i ≃ₗ[A] etaPresentationQuotient f N i :=
  Submodule.Quotient.equiv
    (LinearMap.range (etaPresentationLinearMap f M i))
    (LinearMap.range (etaPresentationLinearMap f N i))
    (etaPresentationIsoTargetEquiv (A := A) e i)
    (etaPresentationLinearMap_iso_range (A := A) (f := f) e i)

-- Proof sketch: transport the quotient module presented by `(f, d^i)` across a strict isomorphism
-- of complexes, then invoke the intrinsic `fittingIdeal` invariance under linear equivalence.
/-- Helper for Lemma 15.97.1: strict complex isomorphisms preserve the degree-`i`
determinantal ideal. -/
lemma etaDeterminantalIdeal_eq_of_iso
    (f : A) {M N : CpxA} (e : M ≅ N) (i : ℤ)
    [Module.Free A (M.X i)] [Module.Finite A (M.X i)]
    [Module.Free A (M.X (i + 1))] [Module.Finite A (M.X (i + 1))]
    [Module.Free A (N.X i)] [Module.Finite A (N.X i)]
    [Module.Free A (N.X (i + 1))] [Module.Finite A (N.X (i + 1))] :
    I[f]_(i)(M) = I[f]_(i)(N) := by
  let biM := Module.Free.chooseBasis A (M.X i)
  let biM1 := Module.Free.chooseBasis A (M.X (i + 1))
  let _ : Module.Finite A (M.X i × M.X (i + 1)) :=
    Module.Finite.of_basis (biM.prod biM1)
  let _ : Module.Finite A (etaPresentationQuotient f M i) :=
    Module.Finite.quotient A (LinearMap.range (etaPresentationLinearMap f M i))
  -- Proof comment: once the presentation quotients are identified, the intrinsic Fitting ideals
  -- agree; the rank index is unchanged because `e.app (i + 1)` is a linear equivalence.
  calc
    I[f]_(i)(M) =
      Fit[A]_(Module.finrank A (M.X (i + 1)))(etaPresentationQuotient f N i) := by
        simpa [etaDeterminantalIdeal] using
          fittingIdeal_eq_of_linearEquiv (R := A)
            (M := etaPresentationQuotient f M i)
            (M' := etaPresentationQuotient f N i)
            (k := Module.finrank A (M.X (i + 1)))
            (etaPresentationQuotientLinearEquivOfIso (A := A) f e i)
    _ = Fit[A]_(Module.finrank A (N.X (i + 1)))(etaPresentationQuotient f N i) := by
          simpa using
            congrArg
              (fun k : ℕ ↦ Fit[A]_(k)(etaPresentationQuotient f N i))
              (complexIsoComponentLinearEquiv (A := A) e (i + 1)).finrank_eq
    _ = I[f]_(i)(N) := by
          rfl

/-- Helper for Lemma 15.97.1: a strict complex isomorphism preserves the finite rank of each
term. -/
private theorem termwiseFiniteFreeRank_eq_of_iso
    {M N : CpxA} [CochainComplex.IsTermwiseFiniteFree M]
    [CochainComplex.IsTermwiseFiniteFree N] (e : M ≅ N) (j : ℤ) :
    termwiseFiniteFreeRank (A := A) M j = termwiseFiniteFreeRank (A := A) N j := by
  -- Proof comment: the `j`th components are linearly equivalent via `e.app j`.
  unfold termwiseFiniteFreeRank
  simpa using (complexIsoComponentLinearEquiv (A := A) e j).finrank_eq

-- Proof sketch: the alternating tail sum only depends on the degreewise finite ranks, and those
-- are invariant under a strict complex isomorphism.
/-- Helper for Lemma 15.97.1: strict complex isomorphisms preserve the truncated alternating tail
rank sum. -/
lemma alternatingRankTail_eq_of_iso
    {M N : CpxA} [CochainComplex.IsTermwiseFiniteFree M]
    [CochainComplex.IsTermwiseFiniteFree N] (e : M ≅ N) (i b : ℤ) :
    alternatingRankTail M i b = alternatingRankTail N i b := by
  -- Proof comment: rewrite every summand using the termwise finrank invariance and keep the
  -- common index range fixed.
  unfold alternatingRankTail
  simp_rw [termwiseFiniteFreeRank_eq_of_iso (A := A) e]

/-- Helper for Lemma 15.97.1: the biproduct of two termwise finite-free complexes is again
termwise finite free. -/
private instance biprod_isTermwiseFiniteFree
    {M N : CpxA} [CochainComplex.IsTermwiseFiniteFree M]
    [CochainComplex.IsTermwiseFiniteFree N] :
    CochainComplex.IsTermwiseFiniteFree (M ⊞ N) where
  out j := by
    -- Proof comment: in each degree the biproduct term is the product of two finite free
    -- modules, which is again finite free.
    exact ⟨inferInstance, inferInstance⟩

/-- Helper for Lemma 15.97.1: summing a pointwise sum over a list splits into the sum of the two
component lists. -/
private theorem list_sum_map_add
    {α : Type*} (L : List α) (f g : α → ℤ) :
    (L.map (fun a ↦ f a + g a)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil =>
      -- Proof comment: the empty list contributes no summands on either side.
      simp
  | cons a L ih =>
      -- Proof comment: peel off the head term and apply the induction hypothesis to the tail.
      simp [ih, add_assoc, add_left_comm, add_comm]

/-- Helper for Lemma 15.97.1: in each degree, the rank of a biproduct complex is the sum of the
two degreewise ranks. -/
private theorem termwiseFiniteFreeRank_biprod
    {M N : CpxA} [CochainComplex.IsTermwiseFiniteFree M]
    [CochainComplex.IsTermwiseFiniteFree N] (j : ℤ) :
    termwiseFiniteFreeRank (A := A) (M ⊞ N) j =
      termwiseFiniteFreeRank (A := A) M j + termwiseFiniteFreeRank (A := A) N j := by
  -- Proof comment: the `j`th term of a biproduct complex is the product `M.X j × N.X j`.
  unfold termwiseFiniteFreeRank
  simpa using Module.finrank_prod (R := A) (M := M.X j) (N := N.X j)

/-- Helper for Lemma 15.97.1: the alternating tail rank is additive under biproducts. -/
private theorem alternatingRankTail_biprod
    {M N : CpxA} [CochainComplex.IsTermwiseFiniteFree M]
    [CochainComplex.IsTermwiseFiniteFree N] (i b : ℤ) :
    alternatingRankTail (M ⊞ N) i b =
      alternatingRankTail M i b + alternatingRankTail N i b := by
  -- Proof comment: rewrite each summand using degreewise rank additivity, then split the list
  -- sum into the two component sums.
  unfold alternatingRankTail
  simp_rw [termwiseFiniteFreeRank_biprod (A := A), Nat.cast_add, mul_add]
  simpa using
    list_sum_map_add
      (L := Int.range i (b + 1))
      (f := fun j ↦ ((-1 : ℤ) ^ Int.toNat (j - i)) * (termwiseFiniteFreeRank (A := A) M j : ℤ))
      (g := fun j ↦ ((-1 : ℤ) ^ Int.toNat (j - i)) * (termwiseFiniteFreeRank (A := A) N j : ℤ))

/-- Helper for Lemma 15.97.1: a bounded-above termwise finite-free complex is already a
bounded-above projective complex in the sense needed to strictify derived morphisms. -/
private lemma projectiveMinus_of_strictlyLE_termwiseFiniteFree
    (K : CpxA) {b : ℤ} (hKb : K.IsStrictlyLE b)
    [CochainComplex.IsTermwiseFiniteFree K] :
    CochainComplex.ProjectiveMinus (ModuleCat A) := by
  -- Proof comment: finite free terms are projective degreewise, so the existing Chapter 15 owner
  -- upgrades the bounded-above finite-free complex to `ProjectiveMinus`.
  simpa using
    (CategoryTheory.projectiveMinus_of_isStrictlyLE_termwiseFiniteFree
      (A := A) K hKb inferInstance)

/-- Helper for Lemma 15.97.1: once both complexes are bounded above termwise finite free, an
isomorphism of their derived images is represented by a strict homotopy equivalence. -/
private lemma nonempty_homotopyEquiv_of_same_derivedObject
    {M N : CpxA} [CochainComplex.IsTermwiseFiniteFree M]
    [CochainComplex.IsTermwiseFiniteFree N] {bM bN : ℤ}
    (hMle : M.IsStrictlyLE bM) (hNle : N.IsStrictlyLE bN)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N)) :
    Nonempty (HomotopyEquiv M N) := by
  let PM : CochainComplex.ProjectiveMinus (ModuleCat A) :=
    projectiveMinus_of_strictlyLE_termwiseFiniteFree (A := A) M hMle
  let PN : CochainComplex.ProjectiveMinus (ModuleCat A) :=
    projectiveMinus_of_strictlyLE_termwiseFiniteFree (A := A) N hNle
  -- Proof comment: the source-faithful first reduction is to strictify the given derived
  -- isomorphism to a homotopy equivalence of the original complexes.
  simpa [PM, PN] using
    (CategoryTheory.nonempty_homotopyEquiv_of_isIsomorphic_q_obj_of_projectiveMinus
      (A := A) PM PN hMN)

/-- Helper for Lemma 15.97.1: after strictifying the derived isomorphism, the resulting mapping
cone is acyclic. This is the concrete contractible complex whose elementary-disk decomposition
would finish the source proof. -/
private lemma exists_acyclic_mappingCone_of_same_derivedObject
    {M N : CpxA} [CochainComplex.IsTermwiseFiniteFree M]
    [CochainComplex.IsTermwiseFiniteFree N] {bM bN : ℤ}
    (hMle : M.IsStrictlyLE bM) (hNle : N.IsStrictlyLE bN)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N)) :
    ∃ e : HomotopyEquiv M N, (CochainComplex.mappingCone e.hom).Acyclic := by
  rcases
      nonempty_homotopyEquiv_of_same_derivedObject
        (A := A) (M := M) (N := N) hMle hNle hMN with
    ⟨e⟩
  refine ⟨e, ?_⟩
  -- Proof comment: homotopy equivalences have acyclic mapping cones, so the problem is now to
  -- compute the eta-determinantal correction for this explicit acyclic bounded-above free cone.
  exact CategoryTheory.mappingCone_acyclic_of_homotopyEquiv (A := A) e

/-- Helper for Lemma 15.97.1: localizing at a prime preserves a strict upper bound on a
cochain complex. -/
private lemma localizationAtPrimeComplex_isStrictlyLE
    (p : PrimeSpectrum A) {M : CpxA} {b : ℤ} (hMle : M.IsStrictlyLE b) :
    (CategoryTheory.localizationAtPrimeComplex p M).IsStrictlyLE b := by
  -- Proof comment: localization is degreewise scalar extension, and scalar extension preserves
  -- zero objects termwise.
  rw [CategoryTheory.localizationAtPrimeComplex_def]
  rw [CochainComplex.isStrictlyLE_iff] at hMle ⊢
  intro j hj
  exact
    (ModuleCat.extendScalars (algebraMap A (Localization.AtPrime p.asIdeal))).map_isZero
      (hMle j hj)

/-- Helper for Lemma 15.97.1: a derived isomorphism remains a derived isomorphism after
localizing both complexes at a prime. -/
private lemma isIsomorphic_q_obj_localizationAtPrimeComplex
    {M N : CpxA} (p : PrimeSpectrum A)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N)) :
    IsIsomorphic
      ((Q).obj (CategoryTheory.localizationAtPrimeComplex p M))
      ((Q).obj (CategoryTheory.localizationAtPrimeComplex p N)) := by
  have hmap :
      IsIsomorphic
        (((ModuleCat.extendScalars (algebraMap A (Localization.AtPrime p.asIdeal)))
            .mapDerivedCategory).obj ((Q).obj M))
        (((ModuleCat.extendScalars (algebraMap A (Localization.AtPrime p.asIdeal)))
            .mapDerivedCategory).obj ((Q).obj N)) := by
    exact CategoryTheory.isIsomorphic_mapDerivedCategory
      (A := A) (B := Localization.AtPrime p.asIdeal) hMN
  rcases hmap with ⟨e⟩
  -- Proof comment: transport the localized derived isomorphism across the strict comparison
  -- isomorphisms between `Q.obj (M_𝔭)` and exact scalar extension of `Q.obj M`.
  exact
    ⟨(CategoryTheory.q_obj_localizationAtPrimeComplex_mapDerived_iso
        (R := A) (p := p) M) ≪≫ e ≪≫
      (CategoryTheory.q_obj_localizationAtPrimeComplex_mapDerived_iso
        (R := A) (p := p) N).symm⟩

/-- Helper for Lemma 15.97.1: after localizing at a prime, the common derived object is still
represented by a homotopy equivalence with acyclic mapping cone. -/
private lemma exists_localized_acyclic_mappingCone_of_same_derivedObject
    (p : PrimeSpectrum A) {M N : CpxA}
    [CochainComplex.IsTermwiseFiniteFree M]
    [CochainComplex.IsTermwiseFiniteFree N] {bM bN : ℤ}
    (hMle : M.IsStrictlyLE bM) (hNle : N.IsStrictlyLE bN)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N)) :
    ∃ e :
        HomotopyEquiv
          (CategoryTheory.localizationAtPrimeComplex p M)
          (CategoryTheory.localizationAtPrimeComplex p N),
      (CochainComplex.mappingCone e.hom).Acyclic := by
  let Mp := CategoryTheory.localizationAtPrimeComplex p M
  let Np := CategoryTheory.localizationAtPrimeComplex p N
  have hMpLE : Mp.IsStrictlyLE bM := by
    -- Proof comment: the localized complex inherits the same upper bound degreewise.
    exact localizationAtPrimeComplex_isStrictlyLE (A := A) (M := M) (b := bM) p hMle
  have hNpLE : Np.IsStrictlyLE bN := by
    -- Proof comment: the same strict upper bound is preserved for the second localized complex.
    exact localizationAtPrimeComplex_isStrictlyLE (A := A) (M := N) (b := bN) p hNle
  have hMNLocal :
      IsIsomorphic ((Q).obj Mp) ((Q).obj Np) := by
    -- Proof comment: exact scalar extension carries the given derived isomorphism to the local
    -- ring `A_𝔭`.
    exact isIsomorphic_q_obj_localizationAtPrimeComplex
      (A := A) (M := M) (N := N) p hMN
  -- Proof comment: apply the already-proved strictification package to the localized complexes.
  simpa [Mp, Np] using
    exists_acyclic_mappingCone_of_same_derivedObject
      (A := A) (M := Mp) (N := Np) hMpLE hNpLE hMNLocal

/-- Helper for Lemma 15.97.1: the range of the product map is the product of the two ranges. -/
private theorem range_prod_eq_prod_range
    {M₁ : Type*} [AddCommGroup M₁] [Module A M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module A M₂]
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂]
    (f : M₁ →ₗ[A] N₁) (g : M₂ →ₗ[A] N₂) :
    LinearMap.range (LinearMap.prod f g) =
      Submodule.prod (LinearMap.range f) (LinearMap.range g) := by
  -- Proof comment: an element of the product range is exactly a pair of independent images.
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨LinearMap.mem_range_self f x.1, LinearMap.mem_range_self g x.2⟩
  · rintro ⟨hy₁, hy₂⟩
    rcases LinearMap.mem_range.mp hy₁ with ⟨x₁, rfl⟩
    rcases LinearMap.mem_range.mp hy₂ with ⟨x₂, rfl⟩
    exact ⟨(x₁, x₂), rfl⟩

/-- Helper for Lemma 15.97.1: quotienting a product by a product submodule splits as the product
of the two quotient modules. -/
private theorem quotient_prod_submodule_equiv
    {M₁ : Type*} [AddCommGroup M₁] [Module A M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module A M₂]
    (P : Submodule A M₁) (Q : Submodule A M₂) :
    ((M₁ × M₂) ⧸ Submodule.prod P Q) ≃ₗ[A] ((M₁ ⧸ P) × (M₂ ⧸ Q)) := by
  let φ : M₁ × M₂ →ₗ[A] ((M₁ ⧸ P) × (M₂ ⧸ Q)) := LinearMap.prod P.mkQ Q.mkQ
  have hker : LinearMap.ker φ = Submodule.prod P Q := by
    -- Proof comment: the product quotient map vanishes exactly on `P × Q`.
    simpa [φ] using (LinearMap.ker_prodMap (f := P.mkQ) (g := Q.mkQ))
  have hsurj : Function.Surjective φ := by
    intro y
    rcases Submodule.mkQ_surjective P y.1 with ⟨x₁, rfl⟩
    rcases Submodule.mkQ_surjective Q y.2 with ⟨x₂, rfl⟩
    exact ⟨(x₁, x₂), rfl⟩
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.2 hsurj
  -- Proof comment: rewrite by the actual kernel and then collapse the full image.
  exact
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (φ.quotKerEquivRange.trans
        ((LinearEquiv.ofEq _ _ hrange).trans Submodule.topEquiv))

/-- Helper for Lemma 15.97.1: quotienting by the image of the first inclusion recovers the second
factor. -/
private noncomputable def quotient_range_inl_linearEquiv
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂] :
    ((N₁ × N₂) ⧸ LinearMap.range (LinearMap.inl A N₁ N₂)) ≃ₗ[A] N₂ := by
  let π : N₁ × N₂ →ₗ[A] N₂ := LinearMap.snd A N₁ N₂
  have hker : LinearMap.ker π = LinearMap.range (LinearMap.inl A N₁ N₂) := by
    -- Proof comment: the kernel of the second projection is exactly the first summand.
    ext z
    constructor
    · intro hz
      rw [LinearMap.mem_ker] at hz
      refine LinearMap.mem_range.mpr ⟨z.1, ?_⟩
      ext <;> simp [hz]
    · rintro ⟨x, rfl⟩
      simp [LinearMap.mem_ker]
  have hrange : LinearMap.range π = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    exact ⟨(0, y), by simp [π]⟩
  -- Proof comment: rewrite by the actual kernel of `snd`, then collapse its full image.
  exact
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (π.quotKerEquivRange.trans
        ((LinearEquiv.ofEq _ _ hrange).trans Submodule.topEquiv))

/-- Helper for Lemma 15.97.1: the standard shear automorphism of a product attached to a linear
map. -/
private noncomputable def product_shear
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂]
    (φ : N₁ →ₗ[A] N₂) :
    (N₁ × N₂) ≃ₗ[A] (N₁ × N₂) where
  toFun x := (x.1, x.2 - φ x.1)
  invFun x := (x.1, x.2 + φ x.1)
  left_inv x := by
    -- Proof comment: the two shear formulas are explicit inverses.
    ext <;> simp
  right_inv x := by
    -- Proof comment: the same coordinate calculation proves the reverse inverse relation.
    ext <;> simp
  map_add' x y := by
    -- Proof comment: the shear is linear in both coordinates.
    ext <;> simp [map_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  map_smul' a x := by
    -- Proof comment: scalar multiplication distributes through the shear correction term.
    ext <;> simp [map_smul, smul_sub]

/-- Helper for Lemma 15.97.1: the shear automorphism carries the graph of `φ` onto the first
summand. -/
private theorem product_shear_maps_graph_range_to_inl_range
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂]
    (φ : N₁ →ₗ[A] N₂) :
    (LinearMap.range (LinearMap.prod (LinearMap.id : N₁ →ₗ[A] N₁) φ)).map
        (product_shear (A := A) φ).toLinearMap =
      LinearMap.range (LinearMap.inl A N₁ N₂) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases LinearMap.mem_range.mp hx with ⟨y, rfl⟩
    -- Proof comment: the shear kills the second coordinate on graph points `(y, φ y)`.
    refine LinearMap.mem_range.mpr ⟨y, ?_⟩
    ext <;> simp [product_shear]
  · intro hz
    rcases LinearMap.mem_range.mp hz with ⟨x, rfl⟩
    -- Proof comment: each point of the first summand is the sheared image of a graph point.
    refine Submodule.mem_map.mpr ⟨(LinearMap.prod (LinearMap.id : N₁ →ₗ[A] N₁) φ) x,
      LinearMap.mem_range_self _ x, ?_⟩
    ext <;> simp [product_shear]

/-- Helper for Lemma 15.97.1: quotienting a product by the graph of `φ` recovers the second
factor. -/
private noncomputable def graph_quotient_linearEquiv_right
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂]
    (φ : N₁ →ₗ[A] N₂) :
    ((N₁ × N₂) ⧸ LinearMap.range (LinearMap.prod (LinearMap.id : N₁ →ₗ[A] N₁) φ)) ≃ₗ[A] N₂ :=
  -- Proof comment: shear the graph of `φ` onto the first factor and then project away that
  -- factor.
  (Submodule.Quotient.equiv
      (LinearMap.range (LinearMap.prod (LinearMap.id : N₁ →ₗ[A] N₁) φ))
      (LinearMap.range (LinearMap.inl A N₁ N₂))
      (product_shear (A := A) φ)
      (product_shear_maps_graph_range_to_inl_range (A := A) φ)).trans
    (quotient_range_inl_linearEquiv (A := A))

/-- Helper for Lemma 15.97.1: after localizing at a prime, two bounded-above termwise finite-free
complexes with the same derived object admit a common bounded-above termwise finite-free model
over the local ring. -/
private theorem localized_common_boundedAbove_termwiseFree_model_of_same_derivedObject
    {M N : CpxA}
    [hMff : CochainComplex.IsTermwiseFiniteFree M]
    [hNff : CochainComplex.IsTermwiseFiniteFree N]
    (p : PrimeSpectrum A)
    {bM bN : ℤ} (hMle : M.IsStrictlyLE bM) (hNle : N.IsStrictlyLE bN)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N)) :
    ∃ P : CochainComplex.MinusWithTermsIn
        (fun X : ModuleCat (Localization.AtPrime p.asIdeal) ↦
          Module.Free (Localization.AtPrime p.asIdeal) X ∧
            Module.Finite (Localization.AtPrime p.asIdeal) X),
      Nonempty
        (DerivedCategory.Q.obj (CategoryTheory.localizationAtPrimeComplex p M) ≅
          DerivedCategory.Q.obj
            (P : CochainComplex (ModuleCat (Localization.AtPrime p.asIdeal)) ℤ)) ∧
      Nonempty
        (DerivedCategory.Q.obj (CategoryTheory.localizationAtPrimeComplex p N) ≅
          DerivedCategory.Q.obj
            (P : CochainComplex (ModuleCat (Localization.AtPrime p.asIdeal)) ℤ)) := by
  let Rp := Localization.AtPrime p.asIdeal
  let Mp := CategoryTheory.localizationAtPrimeComplex p M
  let Np := CategoryTheory.localizationAtPrimeComplex p N
  letI : IsLocalRing Rp := IsLocalization.AtPrime.isLocalRing Rp p.asIdeal
  have hMleLocal : Mp.IsStrictlyLE bM := by
    -- Proof comment: localization preserves the bounded-above support interval termwise.
    exact localizationAtPrimeComplex_isStrictlyLE (A := A) (M := M) (b := bM) p hMle
  have hNleLocal : Np.IsStrictlyLE bN := by
    -- Proof comment: the same support transport applies to `N`.
    exact localizationAtPrimeComplex_isStrictlyLE (A := A) (M := N) (b := bN) p hNle
  have hMNp :
      IsIsomorphic (DerivedCategory.Q.obj Mp) (DerivedCategory.Q.obj Np) := by
    -- Proof comment: exact scalar extension to `A_𝔭` preserves the given derived isomorphism.
    exact isIsomorphic_q_obj_localizationAtPrimeComplex (A := A) (M := M) (N := N) p hMN
  have hMpPseudo : (DerivedCategory.Q.obj Mp).IsPseudoCoherent := by
    -- Proof comment: a bounded-above complex of finite localized terms is pseudo-coherent.
    refine CochainComplex.isPseudoCoherent_of_boundedAbove_of_termwise Mp ?_ ?_
    · exact (CochainComplex.minus_iff (ModuleCat Rp) Mp).2 ⟨bM, hMleLocal⟩
    · intro j
      exact
        (Module.isPseudoCoherent_iff_finite
          (R := Rp) (M := ↥((Mp.X j : ModuleCat Rp)))).2 inferInstance
  have hNpPseudo : (DerivedCategory.Q.obj Np).IsPseudoCoherent := by
    -- Proof comment: the identical bounded-above finite-term argument works for `Np`.
    refine CochainComplex.isPseudoCoherent_of_boundedAbove_of_termwise Np ?_ ?_
    · exact (CochainComplex.minus_iff (ModuleCat Rp) Np).2 ⟨bN, hNleLocal⟩
    · intro j
      exact
        (Module.isPseudoCoherent_iff_finite
          (R := Rp) (M := ↥((Np.X j : ModuleCat Rp)))).2 inferInstance
  let d : ℤ → ℕ := fun j ↦
    Module.finrank (ResidueField Rp)
      (residueFieldDerivedHomology (R := Rp) (DerivedCategory.Q.obj Mp) j)
  have hMpFiniteDim :
      ∀ j : ℤ,
        FiniteDimensional (ResidueField Rp)
          (residueFieldDerivedHomology (R := Rp) (DerivedCategory.Q.obj Mp) j) := by
    -- Proof comment: pseudo-coherent local complexes have finite-dimensional residue-field
    -- homology in every degree.
    intro j
    exact
      (residueFieldDerivedHomology_finiteDimensional_and_eventually_isZero_of_isPseudoCoherent
        (R := Rp) (K := DerivedCategory.Q.obj Mp) hMpPseudo).1 j
  have hNpFiniteDim :
      ∀ j : ℤ,
        FiniteDimensional (ResidueField Rp)
          (residueFieldDerivedHomology (R := Rp) (DerivedCategory.Q.obj Np) j) := by
    -- Proof comment: the same finite-dimensionality statement holds for `Np`.
    intro j
    exact
      (residueFieldDerivedHomology_finiteDimensional_and_eventually_isZero_of_isPseudoCoherent
        (R := Rp) (K := DerivedCategory.Q.obj Np) hNpPseudo).1 j
  have hdMp :
      ∀ j : ℤ,
        Nonempty
          ((residueFieldDerivedHomology (R := Rp) (DerivedCategory.Q.obj Mp) j) ≃ₗ[
              ResidueField Rp] (Fin (d j) → ResidueField Rp)) := by
    -- Proof comment: choose coordinates on each residue-field homology group of `Mp` using its
    -- finrank.
    intro j
    let _ := hMpFiniteDim j
    simpa [d] using
      (nonempty_linearEquiv_fin_of_finrank_eq
        (k := ResidueField Rp)
        (V := residueFieldDerivedHomology (R := Rp) (DerivedCategory.Q.obj Mp) j)
        (n := d j) rfl)
  have hdNp :
      ∀ j : ℤ,
        Nonempty
          ((residueFieldDerivedHomology (R := Rp) (DerivedCategory.Q.obj Np) j) ≃ₗ[
              ResidueField Rp] (Fin (d j) → ResidueField Rp)) := by
    -- Proof comment: derived isomorphism preserves those residue-field homology dimensions, so
    -- the same rank function `d` works for `Np`.
    intro j
    let _ := hNpFiniteDim j
    have hfin :
        Module.finrank (ResidueField Rp)
            (residueFieldDerivedHomology (R := Rp) (DerivedCategory.Q.obj Np) j) = d j := by
      calc
        Module.finrank (ResidueField Rp)
            (residueFieldDerivedHomology (R := Rp) (DerivedCategory.Q.obj Np) j) =
            Module.finrank (ResidueField Rp)
              (residueFieldDerivedHomology (R := Rp) (DerivedCategory.Q.obj Mp) j) := by
                symm
                exact residueFieldDerivedHomology_finrank_eq_of_isIsomorphic
                  (A := Rp) hMNp j
        _ = d j := rfl
    exact
      nonempty_linearEquiv_fin_of_finrank_eq
        (k := ResidueField Rp)
        (V := residueFieldDerivedHomology (R := Rp) (DerivedCategory.Q.obj Np) j)
        (n := d j) hfin
  obtain ⟨Pm, hPmTerms, hPmQ⟩ :=
    exists_boundedAbove_termwiseFree_representative_of_residueFieldDerivedHomology
      (R := Rp) (K := DerivedCategory.Q.obj Mp) hMpPseudo d hdMp
  obtain ⟨Pn, hPnTerms, hPnQ⟩ :=
    exists_boundedAbove_termwiseFree_representative_of_residueFieldDerivedHomology
      (R := Rp) (K := DerivedCategory.Q.obj Np) hNpPseudo d hdNp
  have hPnQFromMp :
      Nonempty
        (DerivedCategory.Q.obj Mp ≅
          DerivedCategory.Q.obj
            (Pn : CochainComplex (ModuleCat Rp) ℤ)) := by
    rcases hMNp with ⟨eMNp⟩
    rcases hPnQ with ⟨ePnQ⟩
    -- Proof comment: transport the chosen `Np`-model across the localized derived isomorphism.
    exact ⟨eMNp ≪≫ ePnQ⟩
  have hPmPn :
      Nonempty
        ((Pm : CochainComplex (ModuleCat Rp) ℤ) ≅
          (Pn : CochainComplex (ModuleCat Rp) ℤ)) := by
    -- Proof comment: the bounded-above finite-free local model is unique once the residue-field
    -- rank function `d` has been fixed.
    exact
      boundedAbove_termwiseFree_representative_unique_of_residueFieldDerivedHomology
        (R := Rp) (K := DerivedCategory.Q.obj Mp) d hdMp
        hPmTerms hPmQ hPnTerms hPnQFromMp
  refine ⟨Pm, hPmQ, ?_⟩
  rcases hPnQ with ⟨ePnQ⟩
  rcases hPmPn with ⟨ePmPn⟩
  -- Proof comment: identify the `Np`-model with the same chosen representative `Pm`.
  exact ⟨ePnQ ≪≫ (DerivedCategory.Q).mapIso ePmPn.symm⟩

/-- Helper for Lemma 15.97.1: localizing at a prime preserves the alternating tail rank sum. -/
private theorem alternatingRankTail_localizationAtPrimeComplex_eq
    (p : PrimeSpectrum A) (M : CpxA)
    [CochainComplex.IsTermwiseFiniteFree M] (i b : ℤ) :
    alternatingRankTail (CategoryTheory.localizationAtPrimeComplex p M) i b =
      alternatingRankTail M i b := by
  -- Proof comment: localization is termwise scalar extension, and each localized term has the
  -- same finite rank as the original term by the base-change finrank formula proved above.
  unfold alternatingRankTail termwiseFiniteFreeRank
  simp_rw [CategoryTheory.localizationAtPrimeComplex_def]
  simp_rw [extendScalars_mapHomologicalComplex_term_finrank_eq
    (A := A) (B := Localization.AtPrime p.asIdeal) (M := M)]

/-- Helper for Lemma 15.97.1: after localizing at a prime, the global ideal identity reduces to
the source-faithful finite disk-sum computation over the local ring. -/
private theorem localized_pow_etaDeterminantalIdeal_eq_of_same_derivedObject
    (f : A) (hf : IsRegular f) {M N : CpxA} (i : ℤ)
    [hMff : CochainComplex.IsTermwiseFiniteFree M]
    [hNff : CochainComplex.IsTermwiseFiniteFree N]
    {bM bN : ℤ} (hMle : M.IsStrictlyLE bM) (hNle : N.IsStrictlyLE bN)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    {m n : ℕ}
    (hbalance :
      (m : ℤ) + alternatingRankTail M i bM =
        (n : ℤ) + alternatingRankTail N i bN)
    (p : PrimeSpectrum A) :
    principalIdeal ((algebraMap A (Localization.AtPrime p.asIdeal)) (f ^ m)) *
        I[algebraMap A (Localization.AtPrime p.asIdeal) f]_(i)
          (CategoryTheory.localizationAtPrimeComplex p M) =
      principalIdeal ((algebraMap A (Localization.AtPrime p.asIdeal)) (f ^ n)) *
        I[algebraMap A (Localization.AtPrime p.asIdeal) f]_(i)
          (CategoryTheory.localizationAtPrimeComplex p N) := by
  let _ := hf
  obtain ⟨P, hMpP, hNpP⟩ :=
    localized_common_boundedAbove_termwiseFree_model_of_same_derivedObject
      (A := A) (M := M) (N := N) p hMle hNle hMN
  have hbalanceLocal :
      (m : ℤ) +
          alternatingRankTail (CategoryTheory.localizationAtPrimeComplex p M) i bM =
        (n : ℤ) +
          alternatingRankTail (CategoryTheory.localizationAtPrimeComplex p N) i bN := by
    -- Proof comment: the exponent balance is numerical, so after localizing the complexes the two
    -- alternating tails remain unchanged.
    simpa [alternatingRankTail_localizationAtPrimeComplex_eq
      (A := A) (p := p)] using hbalance
  let _ := P
  let _ := hMpP
  let _ := hNpP
  let _ := hbalanceLocal
  -- Route correction: replace the abstract localized derived isomorphism by a single common
  -- bounded-above finite-free model `P` over `A_𝔭`. The remaining source-faithful gap is now the
  -- explicit disk-peeling statement that compares each localized complex with `P` by adjoining
  -- elementary trivial disks, together with the one-disk eta/Fitting corrections.
  -- Proof comment: localization has already reduced the global theorem to a statement over the
  -- local ring `A_𝔭`, and both localized complexes have been strictified to the same common
  -- bounded-above finite-free model `P`. What remains is to stabilize `CategoryTheory
  -- .localizationAtPrimeComplex p M` and `CategoryTheory.localizationAtPrimeComplex p N` by
  -- elementary trivial disks above the cutoff, compare their eta-determinantal ideals to that of
  -- `P`, and then read off the exponent shift from `hbalance`.
  -- TODO: prove the bounded-above local disk-sum stabilization package from the common model `P`,
  -- then establish the one-disk eta/Fitting formulas using
  -- `quotient_prod_submodule_equiv` and `graph_quotient_linearEquiv_right`; the localized rank
  -- balance needed at the end is already packaged above as `hbalanceLocal`.
  sorry

-- Proof sketch: localize at each prime ideal and use Lemma `15.76.8` to replace derived-equivalent
-- bounded finite free complexes by stabilizations with finite direct sums of trivial two-term
-- complexes. The resulting determinantal ideals are compared case-by-case according to the degree
-- of the trivial summand, using the block-diagonal minors formula from Lemma `15.8.1`; this gives
-- the claimed equality after correcting by the shift in alternating tail ranks.
/-- Lemma 15.97.1: if bounded complexes `M^•` and `N^•` of finite free `A`-modules represent the
same object of `D(A)`, then the determinantal ideals `I_i(M^•, f)` and `I_i(N^•, f)` agree up to
a power of the nonzerodivisor `f`, with exponent shift measured by the alternating tail ranks. -/
@[stacks 0GSS]
theorem pow_etaDeterminantalIdeal_eq_of_same_derivedObject
    (f : A) (hf : IsRegular f) {M N : CpxA} (i : ℤ)
    [hMff : CochainComplex.IsTermwiseFiniteFree M]
    [hNff : CochainComplex.IsTermwiseFiniteFree N]
    {bM bN : ℤ} (hMle : M.IsStrictlyLE bM) (hNle : N.IsStrictlyLE bN)
    (hMN : IsIsomorphic ((Q).obj M) ((Q).obj N))
    {m n : ℕ}
    (hbalance :
      (m : ℤ) + alternatingRankTail M i bM =
        (n : ℤ) + alternatingRankTail N i bN) :
    principalIdeal (f ^ m) * I[f]_(i)(M) =
      principalIdeal (f ^ n) * I[f]_(i)(N) := by
  -- Proof comment: ideal equality is detected after localizing at every maximal ideal, so it
  -- remains to prove the localized identity over each `A_𝔪`.
  refine Ideal.eq_of_localization_maximal ?_
  intro p hp
  have hprincipalM :
      Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal)) (principalIdeal (f ^ m)) =
        principalIdeal ((algebraMap A (Localization.AtPrime p.asIdeal)) (f ^ m)) := by
    -- Proof comment: localization commutes with the span of the singleton generator `f ^ m`.
    simp [principalIdeal, Ideal.map_span, Set.image_singleton]
  have hprincipalN :
      Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal)) (principalIdeal (f ^ n)) =
        principalIdeal ((algebraMap A (Localization.AtPrime p.asIdeal)) (f ^ n)) := by
    -- Proof comment: the same singleton-span rewrite applies on the right-hand side.
    simp [principalIdeal, Ideal.map_span, Set.image_singleton]
  -- Proof comment: after rewriting both localized sides, the remaining statement is exactly the
  -- prime-local helper above.
  simpa [Ideal.map_mul, hprincipalM, hprincipalN,
    etaDeterminantalIdeal_map_atPrime (A := A) (f := f) (M := M) (i := i) p,
    etaDeterminantalIdeal_map_atPrime (A := A) (f := f) (M := N) (i := i) p] using
    localized_pow_etaDeterminantalIdeal_eq_of_same_derivedObject
      (A := A) (f := f) hf (M := M) (N := N) i hMle hNle hMN hbalance p

end
