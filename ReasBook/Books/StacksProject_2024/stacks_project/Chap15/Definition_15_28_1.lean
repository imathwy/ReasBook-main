import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.Tactic.Recall
import StacksProject_2024.LinearAlgebra.PowerOperations

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

/-- Helper for Definition 15.28.1: coercing the restricted Koszul differential back to the
ambient exterior algebra recovers contraction by `φ`. -/
@[simp] private theorem koszulDifferentialLinearMap_apply_coe
    (φ : E →ₗ[R] R) (n : ℕ) (x : ⋀[R]^(n + 1) E) :
    (koszulDifferentialLinearMap φ n x : ExteriorAlgebra R E) =
      CliffordAlgebra.contractLeft φ x :=
  rfl

/-- Helper for Definition 15.28.1: the degree-one Koszul differential on a generator is the
singleton alternating deletion sum. -/
private theorem koszul_generator_formula_zero
    (φ : E →ₗ[R] R) (v : Fin 1 → E) :
    (koszulDifferentialLinearMap φ 0 (exteriorPower.ιMulti R 1 v) : ExteriorAlgebra R E) =
      ∑ k : Fin 1, ((-1 : R) ^ (k : ℕ) * φ (v k)) •
        (((exteriorPower.ιMulti R 0 (fun i ↦ v (Fin.succAbove k i)) : ⋀[R]^0 E) :
          ExteriorAlgebra R E)) := by
  -- Compare the restricted differential with ambient contraction on the unique generator.
  rw [koszulDifferentialLinearMap_apply_coe]
  -- Normalize the degree-zero target and collapse the unique summand.
  rw [Fin.sum_univ_one]
  simp [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι,
    Algebra.algebraMap_eq_smul_one]

/-- Helper for Definition 15.28.1: deleting the successor index from a tuple and then taking the
tail agrees with taking the tail first and deleting the corresponding index there. -/
private theorem deleted_tuple_tail_eq
    {n : ℕ} (v : Fin (n + 2) → E) (k : Fin (n + 1)) :
    Matrix.vecTail (fun i : Fin (n + 1) ↦ v (Fin.succAbove k.succ i)) =
      fun i : Fin n ↦ Matrix.vecTail v (Fin.succAbove k i) := by
  -- Both tuples evaluate by the same successor-index identity for `Fin.succAbove`.
  funext i
  simpa [Matrix.vecTail] using congrArg v (Fin.succ_succAbove_succ k i)

/-- Helper for Definition 15.28.1: ambient contraction of an `ιMulti` generator is the
alternating deletion sum before restricting back to the exterior-power subtype. -/
private theorem contractLeft_ιMulti_eq_sum
    (φ : E →ₗ[R] R) :
    ∀ n (v : Fin (n + 1) → E),
      CliffordAlgebra.contractLeft φ (ExteriorAlgebra.ιMulti R (n + 1) v) =
        ∑ k : Fin (n + 1), ((-1 : R) ^ (k : ℕ) * φ (v k)) •
          ExteriorAlgebra.ιMulti R n (fun i ↦ v (Fin.succAbove k i))
  | 0, v => by
      -- Reuse the degree-one computation after identifying subtype generators with their coercions.
      simpa [exteriorPower.ιMulti_apply_coe, koszulDifferentialLinearMap_apply_coe] using
        koszul_generator_formula_zero (R := R) (E := E) φ v
  | n + 1, v => by
      -- Split off the head generator and invoke the recursive formula on the tail tuple.
      rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul,
        contractLeft_ιMulti_eq_sum φ n (Matrix.vecTail v)]
      conv_rhs => rw [Fin.sum_univ_succ]
      rw [sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
      -- Match the isolated head term and then normalize each successor deletion term.
      have hzero :
          (fun i : Fin (n + 1) ↦ v (Fin.succAbove 0 i)) = Matrix.vecTail v := by
        funext i
        simp [Matrix.vecTail]
      have hhead :
          φ (v 0) • (ExteriorAlgebra.ιMulti R (n + 1)) (Matrix.vecTail v) =
            (((-1 : R) ^ (0 : ℕ) * φ (v 0)) •
              (ExteriorAlgebra.ιMulti R (n + 1)) fun i ↦ v (Fin.succAbove 0 i)) := by
        rw [hzero]
        simp
      have htail :
          ∑ i : Fin (n + 1),
              -((ι R (v 0)) *
                (((-1 : R) ^ (i : ℕ) * φ (Matrix.vecTail v i)) •
                  (ExteriorAlgebra.ιMulti R n) fun i_1 ↦ Matrix.vecTail v (Fin.succAbove i i_1))) =
            ∑ i : Fin (n + 1),
              ((-1 : R) ^ (i.succ : ℕ) * φ (v i.succ)) •
                (ExteriorAlgebra.ιMulti R (n + 1)) fun i_1 ↦ v (Fin.succAbove i.succ i_1) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [mul_smul_comm, ExteriorAlgebra.ιMulti_succ_apply]
        rw [deleted_tuple_tail_eq (v := v) (k := k)]
        simp [Matrix.vecTail, pow_succ]
      rw [hhead, htail]
      simp

/-- Helper for Definition 15.28.1: on an `ιMulti` generator, the Koszul differential is the
usual alternating deletion sum. -/
theorem koszulDifferentialLinearMap_apply_ιMulti_eq_sum
    (φ : E →ₗ[R] R) (n : ℕ) (v : Fin (n + 1) → E) :
    koszulDifferentialLinearMap φ n (exteriorPower.ιMulti R (n + 1) v) =
      ∑ k : Fin (n + 1), ((-1 : R) ^ (k : ℕ) * φ (v k)) •
        exteriorPower.ιMulti R n (fun i ↦ v (Fin.succAbove k i)) := by
  -- Route correction: the base-change comparison later in the chapter needs this owner-level
  -- generator formula before any scalar-extension transport is introduced.
  -- Compare the subtype equality after coercing both sides to the ambient exterior algebra.
  apply Subtype.ext
  rw [koszulDifferentialLinearMap_apply_coe, exteriorPower.ιMulti_apply_coe]
  simpa [exteriorPower.ιMulti_apply_coe] using contractLeft_ιMulti_eq_sum (R := R) (E := E) φ n v

/-- Consecutive differentials in the Koszul complex of `φ` compose to zero. -/
private theorem koszulDifferential_sq (φ : E →ₗ[R] R) (n : ℕ) :
    koszulDifferential φ (n + 1) ≫ koszulDifferential φ n =
      (0 :
        (ModuleCat.of R E).exteriorPower (n + 2) ⟶ (ModuleCat.of R E).exteriorPower n) := by
  apply ModuleCat.hom_ext
  ext x
  apply Subtype.ext
  -- Compare the composite with ambient contraction, where square-zero is already available.
  change ((koszulDifferentialLinearMap φ n) (koszulDifferentialLinearMap φ (n + 1) x) :
      ExteriorAlgebra R E) = 0
  rw [koszulDifferentialLinearMap_apply_coe, koszulDifferentialLinearMap_apply_coe,
    CliffordAlgebra.contractLeft_contractLeft]

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
  let wedgeMap : ⋀[R]^n E →ₗ[R] ExteriorAlgebra R E :=
    (Submodule.subtype _).comp (koszulLeftWedge e n)
  let mulMap : ⋀[R]^n E →ₗ[R] ExteriorAlgebra R E :=
    (LinearMap.mulLeft R (ι R e)).comp (Submodule.subtype _)
  have hMaps : wedgeMap = mulMap := by
    apply exteriorPower.linearMap_ext
    ext m
    -- The two maps agree on the canonical exterior-power generators.
    dsimp [wedgeMap, mulMap]
    rw [exteriorPower.leftTensorMap_tmul_ιMulti, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_succ_apply]
    congr 1
  have hx : wedgeMap x = mulMap x := congrArg (fun f => f x) hMaps
  dsimp [wedgeMap, mulMap] at hx ⊢
  simpa [LinearMap.comp_apply] using hx

/-- Helper for Definition 15.28.1: contraction by `φ` vanishes on degree-zero elements of the
exterior algebra. -/
private theorem contractLeft_eq_zero_of_mem_exteriorPower_zero
    (φ : E →ₗ[R] R) {x : ExteriorAlgebra R E} (hx : x ∈ ⋀[R]^0 E) :
    CliffordAlgebra.contractLeft φ x = 0 := by
  -- Degree-zero elements are scalars, and contraction kills scalars.
  obtain ⟨r, rfl : algebraMap R (ExteriorAlgebra R E) r = x⟩ := Submodule.mem_one.mp hx
  simp

/-- In degree `0`, the Koszul differential followed by left wedge by `e` is multiplication by the
scalar `φ e`. -/
theorem koszulDifferentialLinearMap_comp_koszulLeftWedge_zero
    (φ : E →ₗ[R] R) (e : E) :
    (koszulDifferentialLinearMap φ 0).comp (koszulLeftWedge e 0) =
      (φ e) • (LinearMap.id : ⋀[R]^0 E →ₗ[R] ⋀[R]^0 E) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx0 : CliffordAlgebra.contractLeft φ (x : ExteriorAlgebra R E) = 0 :=
    contractLeft_eq_zero_of_mem_exteriorPower_zero φ x.prop
  -- Rewrite the composite in the ambient algebra and apply the degree-zero contraction formula.
  rw [LinearMap.comp_apply, koszulDifferentialLinearMap_apply_coe, koszulLeftWedge_apply_coe,
    LinearMap.smul_apply, LinearMap.id_apply, CliffordAlgebra.contractLeft_ι_mul]
  simp [hx0]

/-- On positive degrees, contraction by `φ` and left wedge by `e` satisfy the standard Koszul
homotopy relation. -/
theorem koszulDifferentialLinearMap_comp_koszulLeftWedge_add_koszulLeftWedge_comp_koszulDifferential
    (φ : E →ₗ[R] R) (e : E) (n : ℕ) :
    (koszulDifferentialLinearMap φ (n + 1)).comp (koszulLeftWedge e (n + 1)) +
        (koszulLeftWedge e n).comp (koszulDifferentialLinearMap φ n) =
      (φ e) • (LinearMap.id : ⋀[R]^(n + 1) E →ₗ[R] ⋀[R]^(n + 1) E) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  -- Move to the ambient exterior algebra and invoke the standard contraction identity.
  change
    (koszulDifferentialLinearMap φ (n + 1) (koszulLeftWedge e (n + 1) x) :
        ExteriorAlgebra R E) +
      (koszulLeftWedge e n (koszulDifferentialLinearMap φ n x) : ExteriorAlgebra R E) =
        (φ e) • (x : ExteriorAlgebra R E)
  simp only [koszulDifferentialLinearMap_apply_coe, koszulLeftWedge_apply_coe]
  rw [CliffordAlgebra.contractLeft_ι_mul]
  abel

/-- The linear form on `E × R` given by `φ` on `E` and multiplication by `a` on the `R`-summand. -/
noncomputable abbrev koszulCoprodScalarLinearMap (φ : E →ₗ[R] R) (a : R) :
    E × R →ₗ[R] R :=
  φ.coprod ((LinearMap.id : R →ₗ[R] R).smulRight a)

@[simp] theorem koszulCoprodScalarLinearMap_apply
    (φ : E →ₗ[R] R) (a : R) (x : E × R) :
    koszulCoprodScalarLinearMap φ a x = φ x.1 + x.2 * a := by
  simp [koszulCoprodScalarLinearMap]
