import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Tactic.Recall
import stacks_project.LinearAlgebra.PowerOperations

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open CategoryTheory ExteriorAlgebra exteriorPower

variable {R : Type u} {E : Type v} [CommRing R] [AddCommGroup E] [Module R E]

/- Domain-style sampling:
- primary domain: Koszul complexes from a linear form on a module, realized through the exterior
  algebra and its graded pieces;
- sampled owner declarations:
  `CliffordAlgebra.contractLeft`,
  `ExteriorAlgebra.gradedAlgebra`,
  `ModuleCat.exteriorPower`,
  `exteriorPower.leftTensorMap`,
  `ChainComplex.of`;
- best owner abstraction: the canonical contraction operator on `ExteriorAlgebra R E`, with the
  chain-complex structure on the exterior powers and the canonical exterior-power left tensor map
  as the derived bridge/view;
- primitive data: a linear form `φ : E →ₗ[R] R`;
- derived API: the degree-lowering restriction to `⋀[R]^n E`, the induced differential in
  `ModuleCat R`, the Koszul complex, and the degree-raising left-wedge maps obtained from
  `exteriorPower.leftTensorMap`;

Source/core/bridge triage:
- `source-facing`: `koszulComplex`, `koszulLeftWedge`, `koszulCoprodScalarLinearMap`;
- `core/canonical`: `CliffordAlgebra.contractLeft`, `ExteriorAlgebra`, `ModuleCat.exteriorPower`,
  `ChainComplex.of`;
- `bridge/view`: the degree-lowering restriction of `CliffordAlgebra.contractLeft`,
  `koszulDifferentialLinearMap`, and `koszulDifferential`. -/

/- Definition 15.28.1, source-facing layer: the Koszul complex is built on the canonical graded
commutative algebra structure on `ExteriorAlgebra R E`. -/
recall ExteriorAlgebra.gradedAlgebra

/- The source-facing Koszul differential on `ExteriorAlgebra R E` is the canonical contraction
operator `CliffordAlgebra.contractLeft φ`. -/
recall CliffordAlgebra.contractLeft

/- On generators, the source-facing Koszul differential extends the linear form `φ`. -/
recall CliffordAlgebra.contractLeft_ι

/- The source-facing Koszul differential satisfies the graded Leibniz rule. -/
recall CliffordAlgebra.contractLeft_ι_mul

private theorem contractLeft_ιMulti_mem_exteriorPower (φ : E →ₗ[R] R) :
    ∀ n (v : Fin (n + 1) → E),
      CliffordAlgebra.contractLeft φ (ExteriorAlgebra.ιMulti R (n + 1) v) ∈ ⋀[R]^n E
  | 0, v => by
      rw [ExteriorAlgebra.exteriorPower]
      simp [ExteriorAlgebra.ιMulti_succ_apply, Algebra.algebraMap_eq_smul_one]
  | n + 1, v => by
      rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ <|
          ExteriorAlgebra.ιMulti_range R (n + 1) ⟨Matrix.vecTail v, rfl⟩
      · have htail :
            CliffordAlgebra.contractLeft φ
              (ExteriorAlgebra.ιMulti R (n + 1) (Matrix.vecTail v)) ∈ ⋀[R]^n E := by
          simpa using contractLeft_ιMulti_mem_exteriorPower φ n (Matrix.vecTail v)
        have hι : ι R (v 0) ∈ ⋀[R]^1 E := by
          rw [ExteriorAlgebra.exteriorPower]
          simp
        rw [ExteriorAlgebra.exteriorPower] at htail hι ⊢
        simpa [add_comm] using SetLike.mul_mem_graded hι htail

private theorem contractLeft_mem_exteriorPower (φ : E →ₗ[R] R) (n : ℕ) (x : ExteriorAlgebra R E)
    (hx : x ∈ ⋀[R]^(n + 1) E) :
    CliffordAlgebra.contractLeft φ x ∈ ⋀[R]^n E := by
  have hx' :
      x ∈ Submodule.span R
        (Set.range (ExteriorAlgebra.ιMulti R (n + 1) : (Fin (n + 1) → E) → ExteriorAlgebra R E)) := by
    rw [ExteriorAlgebra.ιMulti_span_fixedDegree R (n + 1)]
    exact hx
  refine Submodule.span_induction ?mem ?zero ?add ?smul hx'
  · intro y hy
    rcases hy with ⟨v, rfl⟩
    exact contractLeft_ιMulti_mem_exteriorPower φ n v
  · simp
  · intro a b _ _ ha hb
    simpa [map_add] using Submodule.add_mem (⋀[R]^n E) ha hb
  · intro a y _ hy
    simpa [map_smul] using Submodule.smul_mem (⋀[R]^n E) a hy

/-- The degree `n + 1` Koszul differential is the restriction of `CliffordAlgebra.contractLeft φ`
to the `(n + 1)`st exterior power. -/
noncomputable def koszulDifferentialLinearMap (φ : E →ₗ[R] R) (n : ℕ) :
    ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^n E :=
  (CliffordAlgebra.contractLeft φ).restrict fun x hx ↦ contractLeft_mem_exteriorPower φ n x hx

/-- The degree `n + 1` differential in the Koszul complex attached to `φ`, viewed in
`ModuleCat R`. -/
noncomputable abbrev koszulDifferential (φ : E →ₗ[R] R) (n : ℕ) :
    (ModuleCat.of R E).exteriorPower (n + 1) ⟶ (ModuleCat.of R E).exteriorPower n :=
  ModuleCat.ofHom (koszulDifferentialLinearMap φ n)

/-- Consecutive differentials in the Koszul complex of `φ` compose to zero. -/
private theorem koszulDifferential_sq (φ : E →ₗ[R] R) (n : ℕ) :
    koszulDifferential φ (n + 1) ≫ koszulDifferential φ n =
      (0 :
        (ModuleCat.of R E).exteriorPower (n + 2) ⟶ (ModuleCat.of R E).exteriorPower n) := by
  sorry

/-- Definition 15.28.1: the Koszul complex associated to an `R`-linear map `φ : E →ₗ[R] R` is
the chain-complex bridge/view of `CliffordAlgebra.contractLeft φ` on the graded algebra
`ExteriorAlgebra R E`. -/
noncomputable abbrev koszulComplex (φ : E →ₗ[R] R) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of ((ModuleCat.of R E).exteriorPower)
    (koszulDifferential φ)
    (koszulDifferential_sq φ)

/-- Left wedge by `e`, viewed as the specialization of the canonical exterior-power left tensor
map to `LinearMap.id`. -/
noncomputable abbrev koszulLeftWedge (e : E) (n : ℕ) :
    ⋀[R]^n E →ₗ[R] ⋀[R]^(n + 1) E :=
  leftTensorMap n (LinearMap.id : E →ₗ[R] E) ∘ₗ
    TensorProduct.mk R E (⋀[R]^n E) e

@[simp] theorem koszulLeftWedge_apply_ιMulti (e : E) (n : ℕ) (x : Fin n → E) :
    koszulLeftWedge e n (exteriorPower.ιMulti R n x) =
      exteriorPower.ιMulti R (n + 1) (Matrix.vecCons e x) := by
  simpa [koszulLeftWedge, LinearMap.comp_apply, Matrix.vecCons] using
    exteriorPower.leftTensorMap_tmul_ιMulti n (LinearMap.id : E →ₗ[R] E) e x

@[simp] theorem koszulLeftWedge_apply_coe (e : E) (n : ℕ) (x : ⋀[R]^n E) :
    (koszulLeftWedge e n x : ExteriorAlgebra R E) = ι R e * x := by
  sorry

/-- In degree `0`, the Koszul differential followed by left wedge by `e` is multiplication by the
scalar `φ e`. -/
theorem koszulDifferentialLinearMap_comp_koszulLeftWedge_zero
    (φ : E →ₗ[R] R) (e : E) :
    (koszulDifferentialLinearMap φ 0).comp (koszulLeftWedge e 0) =
      (φ e) • (LinearMap.id : ⋀[R]^0 E →ₗ[R] ⋀[R]^0 E) := by
  sorry

/-- On positive degrees, contraction by `φ` and left wedge by `e` satisfy the standard Koszul
homotopy relation. -/
theorem koszulDifferentialLinearMap_comp_koszulLeftWedge_add_koszulLeftWedge_comp_koszulDifferential
    (φ : E →ₗ[R] R) (e : E) (n : ℕ) :
    (koszulDifferentialLinearMap φ (n + 1)).comp (koszulLeftWedge e (n + 1)) +
        (koszulLeftWedge e n).comp (koszulDifferentialLinearMap φ n) =
      (φ e) • (LinearMap.id : ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^(n + 1) E) := by
  sorry

/-- The linear form on `E × R` given by `φ` on `E` and multiplication by `a` on the `R`-summand. -/
noncomputable abbrev koszulCoprodScalarLinearMap (φ : E →ₗ[R] R) (a : R) :
    E × R →ₗ[R] R :=
  φ.coprod ((LinearMap.id : R →ₗ[R] R).smulRight a)

@[simp] theorem koszulCoprodScalarLinearMap_apply
    (φ : E →ₗ[R] R) (a : R) (x : E × R) :
    koszulCoprodScalarLinearMap φ a x = φ x.1 + x.2 * a := by
  simp [koszulCoprodScalarLinearMap]
