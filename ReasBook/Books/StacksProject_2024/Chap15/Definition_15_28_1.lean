import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open CategoryTheory ModuleCat ExteriorAlgebra

variable {R : Type u} {E : Type v} [CommRing R] [AddCommGroup E] [Module R E]

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
      CliffordAlgebra.contractLeft φ (ιMulti R (n + 1) v) ∈ ⋀[R]^n E
  | 0, v => by
      simp [ιMulti_succ_apply, Algebra.algebraMap_eq_smul_one, ExteriorAlgebra.exteriorPower]
  | n + 1, v => by
      rw [ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ <| ιMulti_range R (n + 1) ⟨Matrix.vecTail v, rfl⟩
      · have htail : CliffordAlgebra.contractLeft φ (ιMulti R (n + 1) (Matrix.vecTail v)) ∈ ⋀[R]^n E := by
          simpa using contractLeft_ιMulti_mem_exteriorPower φ n (Matrix.vecTail v)
        have hι : ι R (v 0) ∈ ⋀[R]^1 E := by
          simp [ExteriorAlgebra.exteriorPower]
        simpa [ExteriorAlgebra.exteriorPower, add_comm] using SetLike.mul_mem_graded hι htail

/-- The canonical Koszul differential on `ExteriorAlgebra R E` lowers exterior degree by one. -/
theorem contractLeft_mem_exteriorPower (φ : E →ₗ[R] R) (n : ℕ) {x : ExteriorAlgebra R E}
    (hx : x ∈ ⋀[R]^(n + 1) E) :
    CliffordAlgebra.contractLeft φ x ∈ ⋀[R]^n E := by
  rw [← ιMulti_span_fixedDegree R (n + 1)] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨v, rfl⟩
      exact contractLeft_ιMulti_mem_exteriorPower φ n v
  | zero =>
      simp
  | add a b _ _ ha hb =>
      simpa [map_add] using Submodule.add_mem (⋀[R]^n E) ha hb
  | smul a y _ hy =>
      simpa [map_smul] using Submodule.smul_mem (⋀[R]^n E) a hy

/-- The degree `n + 1` Koszul differential is the restriction of `CliffordAlgebra.contractLeft φ`
to the `(n + 1)`st exterior power. -/
noncomputable def koszulDifferentialLinearMap (φ : E →ₗ[R] R) (n : ℕ) :
    ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^n E :=
  (CliffordAlgebra.contractLeft φ).restrict fun _ hx ↦ contractLeft_mem_exteriorPower φ n hx

/-- On each graded piece, `koszulDifferentialLinearMap` is literally the restriction of
`CliffordAlgebra.contractLeft φ`. -/
@[simp] theorem koszulDifferentialLinearMap_apply (φ : E →ₗ[R] R) (n : ℕ) (x : ⋀[R]^(n + 1) E) :
    (koszulDifferentialLinearMap φ n x : ExteriorAlgebra R E) = CliffordAlgebra.contractLeft φ x :=
  rfl

/-- The degree `n + 1` differential in the Koszul complex attached to `φ`, viewed in
`ModuleCat R`. -/
noncomputable def koszulDifferential (φ : E →ₗ[R] R) (n : ℕ) :
    (ModuleCat.of R E).exteriorPower (n + 1) ⟶ (ModuleCat.of R E).exteriorPower n :=
  ModuleCat.ofHom (koszulDifferentialLinearMap φ n)

/-- Consecutive differentials in the Koszul complex of `φ` compose to zero. -/
theorem koszulDifferential_sq (φ : E →ₗ[R] R) (n : ℕ) :
    koszulDifferential φ (n + 1) ≫ koszulDifferential φ n = 0 := by
  change ModuleCat.ofHom ((koszulDifferentialLinearMap φ n).comp (koszulDifferentialLinearMap φ (n + 1))) = 0
  ext x
  simp [koszulDifferentialLinearMap, CliffordAlgebra.contractLeft_contractLeft]

/-- Definition 15.28.1: the Koszul complex associated to an `R`-linear map `φ : E →ₗ[R] R` is
the chain-complex bridge/view of `CliffordAlgebra.contractLeft φ` on the graded algebra
`ExteriorAlgebra R E`. -/
noncomputable abbrev koszulComplex (φ : E →ₗ[R] R) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of ((ModuleCat.of R E).exteriorPower)
    (koszulDifferential φ)
    (koszulDifferential_sq φ)

/-- The degree `n` object of the Koszul complex of `φ` is the `n`th exterior power of `E`. -/
theorem koszulComplex_X (φ : E →ₗ[R] R) (n : ℕ) :
    (koszulComplex φ).X n = (ModuleCat.of R E).exteriorPower n :=
  rfl
