import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Exercise_2_2_6_3
import LinearRepresentations_Serre_1977.Chap04.Remark_4_4_3_1.MatrixCoefficientMaps
import LinearRepresentations_Serre_1977.Chap04.Remark_4_4_3_1.SubrepresentationBridges
import LinearRepresentations_Serre_1977.Chap04.Remark_4_4_3_1.InvariantDual
import LinearRepresentations_Serre_1977.Chap04.Remark_4_4_3_1.AdjointRecovery

open MeasureTheory
open DomMulAct
open scoped ENNReal MonoidAlgebra
open scoped ComplexStarModule

noncomputable section

universe u v

namespace Representation

namespace Remark_4_4_3_1

local notation "L²(" G ")" => G →₂[(Measure.haar : Measure G)] ℂ

section L2RegularModel

variable (G : Type u) [MeasurableSpace G] [Group G] [TopologicalSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]
variable {W : Type v} [TopologicalSpace W] [AddCommGroup W] [Module ℂ W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]

/-- Helper for Remark 4-4.3-1: theorem-local owner for the left-regular `L²` representation used
by the extracted support modules. It is definitionally the same regular representation as the main
target declaration `Representation.l2Regular`. -/
abbrev l2RegularModel :
    Representation ℂ G L²(G) :=
  (ofDistribMulAction ℂ Gᵈᵐᵃ L²(G)).comp ((MulEquiv.inv' G).toMonoidHom : G →* Gᵈᵐᵃ)

/-- Helper for Remark 4-4.3-1: defining formula for the theorem-local left-regular model. -/
@[simp] theorem l2RegularModel_apply (g : G) (f : L²(G)) :
    l2RegularModel G g f =
      Lp.compMeasurePreservingₗ ℂ (fun t : G ↦ g⁻¹ * t)
        (measurePreserving_mul_left (Measure.haar : Measure G) g⁻¹) f :=
  rfl

/-- Helper for Remark 4-4.3-1: the theorem-local left-regular model preserves the ambient `L²`
inner product. -/
theorem l2RegularModel_inner_map_map (g : G)
    (f h : L²(G)) :
    inner ℂ (l2RegularModel G g f) (l2RegularModel G g h) =
      inner ℂ f h := by
  let T : L²(G) →ₗᵢ[ℂ] L²(G) :=
    Lp.compMeasurePreservingₗᵢ ℂ (fun t : G ↦ g⁻¹ * t)
      (measurePreserving_mul_left (Measure.haar : Measure G) g⁻¹)
  change inner ℂ (T f) (T h) = inner ℂ f h
  exact T.inner_map_map f h

end L2RegularModel

section PeterWeyl

variable {G : Type u} [MeasurableSpace G] [Group G] [TopologicalSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
variable {W : Type v} [TopologicalSpace W] [AddCommGroup W] [Module ℂ W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]

/-- Helper for Remark 4-4.3-1: a fixed linear functional on `W` produces an intertwiner from `σ`
to the left-regular `L²` representation via matrix coefficients. -/
noncomputable def matrixCoefficientIntertwining_l2Regular
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    (ℓ : Module.Dual ℂ W) :
    σ.IntertwiningMap (l2RegularModel G) where
  toLinearMap :=
    (ContinuousMap.toLp (E := ℂ) 2 (Measure.haar : Measure G) ℂ).toLinearMap.comp
      (matrixCoefficientLinear σ hσ ℓ)
  isIntertwining' := by
    intro g
    ext x
    let f := matrixCoefficientContinuousMap σ hσ x ℓ
    have hcomp :
        f.comp ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩ =
          matrixCoefficientContinuousMap σ hσ (σ g x) ℓ := by
      simpa using (matrixCoefficientContinuousMap_mul_left σ hσ g x ℓ).symm
    have hright :
        (((l2RegularModel G) g)
            (ContinuousMap.toLp (E := ℂ) 2 (Measure.haar : Measure G) ℂ f) : G →ₘ[Measure.haar] ℂ)
          =ᵐ[Measure.haar] f.comp ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩ := by
      rw [l2RegularModel_apply]
      refine (Lp.coeFn_compMeasurePreserving
          (f := fun t : G ↦ g⁻¹ * t)
          (hf := measurePreserving_mul_left (Measure.haar : Measure G) g⁻¹)
          (g := ContinuousMap.toLp (E := ℂ) 2 (Measure.haar : Measure G) ℂ f)).trans ?_
      simpa [f] using
        (measurePreserving_mul_left (Measure.haar : Measure G) g⁻¹).quasiMeasurePreserving.ae_eq_comp
          (ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := (Measure.haar : Measure G))
            (𝕜 := ℂ) f)
    have hcomp_fun :
        ((matrixCoefficientContinuousMap σ hσ (σ g x) ℓ : C(G, ℂ)) : G → ℂ) =
          (f.comp ⟨fun t : G ↦ g⁻¹ * t, continuous_const.mul continuous_id⟩ : C(G, ℂ)) := by
      simpa using congrArg (fun h : C(G, ℂ) => (h : G → ℂ)) hcomp.symm
    simp only [LinearMap.comp_apply]
    exact (ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := (Measure.haar : Measure G))
        (𝕜 := ℂ) (matrixCoefficientContinuousMap σ hσ (σ g x) ℓ)).trans
      (hcomp_fun.eventuallyEq.trans hright.symm)
/-- Helper for Remark 4-4.3-1: the `L²` matrix-coefficient intertwiner remembers the original
functional on `W`. -/
theorem matrixCoefficientIntertwining_l2Regular_eq_zero_iff
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    (ℓ : Module.Dual ℂ W) :
    matrixCoefficientIntertwining_l2Regular (G := G) σ hσ ℓ = 0 ↔ ℓ = 0 := by
  constructor
  · intro hzero
    ext x
    have hx :
        ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
            (matrixCoefficientContinuousMap σ hσ x ℓ) = 0 := by
      simpa [matrixCoefficientIntertwining_l2Regular, matrixCoefficientLinear] using
        congrArg (fun F : σ.IntertwiningMap (l2RegularModel G) ↦ F x) hzero
    have hcont :
        matrixCoefficientContinuousMap σ hσ x ℓ = 0 :=
      (ContinuousMap.toLp_injective (E := ℂ) (p := (2 : ℝ≥0∞))
        (μ := (Measure.haar : Measure G)) (𝕜 := ℂ)) hx
    have hpoint :
        matrixCoefficientContinuousMap σ hσ x ℓ 1 = 0 := by
      simpa using congrArg (fun f : C(G, ℂ) ↦ f 1) hcont
    simpa [matrixCoefficientContinuousMap] using hpoint
  · intro hℓ
    subst hℓ
    apply Representation.IntertwiningMap.ext
    ext x
    have hcont :
        matrixCoefficientContinuousMap σ hσ x (0 : Module.Dual ℂ W) = 0 := by
      ext t
      simp [matrixCoefficientContinuousMap]
    simp [matrixCoefficientIntertwining_l2Regular, matrixCoefficientLinear, hcont]

/-- Helper for Remark 4-4.3-1: transporting the source vector by `σ g` moves the matrix
coefficient by right translation on `G`. This is the source-level covariance used later to show
that the recovered coefficient form is `G`-invariant. -/
theorem matrixCoefficientContinuousMap_invariantDual_mul_left
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (g : G) (x y : W) :
    matrixCoefficientContinuousMap σ hσ y (J (σ g x)) =
      (matrixCoefficientContinuousMap σ hσ y (J x)).comp
        ⟨fun t : G ↦ t * g, continuous_id.mul continuous_const⟩ := by
  -- Rewrite the translated functional using the `G`-invariance of `J`.
  ext t
  have hJg :=
    hJ g x (σ ((t * g)⁻¹) y)
  simpa [matrixCoefficientContinuousMap, map_mul] using hJg
/-- Helper for Remark 4-4.3-1: the matrix-coefficient construction is linear in the chosen
functional. -/
noncomputable def matrixCoefficientIntertwining_l2RegularLinear
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2) :
    Module.Dual ℂ W →ₗ[ℂ] σ.IntertwiningMap (l2RegularModel G) where
  toFun ℓ := matrixCoefficientIntertwining_l2Regular (G := G) σ hσ ℓ
  map_add' ℓ₁ ℓ₂ := by
    apply Representation.IntertwiningMap.ext
    ext x
    have hEq :
        (ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
          (matrixCoefficientContinuousMap σ hσ x (ℓ₁ + ℓ₂)) : L²(G))
          =
        ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
            (matrixCoefficientContinuousMap σ hσ x ℓ₁)
          +
        ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
            (matrixCoefficientContinuousMap σ hσ x ℓ₂) := by
      calc
        (ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
          (matrixCoefficientContinuousMap σ hσ x (ℓ₁ + ℓ₂)) : L²(G))
            =
          ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
            (matrixCoefficientContinuousMap σ hσ x ℓ₁ +
              matrixCoefficientContinuousMap σ hσ x ℓ₂) := by
                rfl
        _ =
          ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
              (matrixCoefficientContinuousMap σ hσ x ℓ₁)
            +
          ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
              (matrixCoefficientContinuousMap σ hσ x ℓ₂) := by
                rw [map_add]
    simpa [matrixCoefficientIntertwining_l2Regular, matrixCoefficientLinear, Lp.ext_iff] using hEq
  map_smul' a ℓ := by
    apply Representation.IntertwiningMap.ext
    ext x
    have hEq :
        (ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
          (matrixCoefficientContinuousMap σ hσ x (a • ℓ)) : L²(G))
          =
        a •
          (ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
            (matrixCoefficientContinuousMap σ hσ x ℓ) : L²(G)) := by
      calc
        (ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
          (matrixCoefficientContinuousMap σ hσ x (a • ℓ)) : L²(G))
            =
          ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
            (a • matrixCoefficientContinuousMap σ hσ x ℓ) := by
                rfl
        _ =
          a •
            (ContinuousMap.toLp (E := ℂ) (p := (2 : ℝ≥0∞)) (Measure.haar : Measure G) ℂ
              (matrixCoefficientContinuousMap σ hσ x ℓ) : L²(G)) := by
                rw [map_smul]
    simpa [matrixCoefficientIntertwining_l2Regular, matrixCoefficientLinear, Lp.ext_iff] using hEq
/-- Helper for Remark 4-4.3-1: the linear matrix-coefficient family in `L²(G)` is injective. -/
theorem matrixCoefficientIntertwining_l2RegularLinear_injective
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2) :
    Function.Injective (matrixCoefficientIntertwining_l2RegularLinear (G := G) σ hσ) := by
  intro ℓ₁ ℓ₂ hEq
  have hzero :
      matrixCoefficientIntertwining_l2RegularLinear (G := G) σ hσ (ℓ₁ - ℓ₂) = 0 := by
    rw [LinearMap.map_sub, hEq, sub_self]
  have hdiff :
      ℓ₁ - ℓ₂ = 0 :=
    (matrixCoefficientIntertwining_l2Regular_eq_zero_iff (G := G) σ hσ (ℓ₁ - ℓ₂)).mp hzero
  exact sub_eq_zero.mp hdiff
/-- Helper for Remark 4-4.3-1: the canonical `σ`-isotypic subrepresentation inside the `L²`
regular representation is obtained by viewing the owner isotypic component as a stable
subrepresentation. -/
abbrev l2RegularIsotypicSubrepresentation
    (σ : Representation ℂ G W) :
    Subrepresentation (l2RegularModel G) :=
  letI : Module ℂ[G] L²(G) := (l2RegularModel G).instModuleMonoidAlgebraAsModule
  letI : Module ℂ[G] W := σ.instModuleMonoidAlgebraAsModule
  Subrepresentation.ofSubmodule' (isotypicComponent ℂ[G] L²(G) W)
/-- Helper for Remark 4-4.3-1: the range of an intertwiner into `L²(G)` lies in the canonical
`σ`-isotypic subrepresentation. -/
theorem intertwiningMap_range_le_l2RegularIsotypicSubrepresentation
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (f : σ.IntertwiningMap (l2RegularModel G)) :
    f.range.toSubmodule ≤ (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule := by
  letI : Module ℂ[G] L²(G) := (l2RegularModel G).instModuleMonoidAlgebraAsModule
  letI : Module ℂ[G] W := σ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] W := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule σ).mp inferInstance
  let fA := (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := σ) (σ := l2RegularModel G)) f
  letI : IsSimpleModule ℂ[G] (⊤ : Submodule ℂ[G] W) :=
    IsSimpleModule.congr (Submodule.topEquiv : (⊤ : Submodule ℂ[G] W) ≃ₗ[ℂ[G]] W)
  have hmap :
      LinearMap.range fA ≤ isotypicComponent ℂ[G] L²(G) W := by
    simpa [fA] using
      (Submodule.map_le_isotypicComponent (R := ℂ[G]) (M := W) (N := L²(G))
        (S := (⊤ : Submodule ℂ[G] W)) (f := fA)).trans_eq
        ((Submodule.topEquiv : (⊤ : Submodule ℂ[G] W) ≃ₗ[ℂ[G]] W).isotypicComponent_eq)
  simpa [l2RegularIsotypicSubrepresentation, Representation.IntertwiningMap.range, fA] using hmap
/-- Helper for Remark 4-4.3-1: every intertwiner from an irreducible `σ` into `L²(G)` already
lands in the canonical `σ`-isotypic subrepresentation of the regular representation. -/
theorem intertwiningMap_apply_mem_l2Regular_isotypicSubrepresentation
    (σ : Representation ℂ G W) [σ.IsIrreducible]
    (f : σ.IntertwiningMap (l2RegularModel G)) :
    ∀ x, f x ∈ (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule := by
  intro x
  exact intertwiningMap_range_le_l2RegularIsotypicSubrepresentation (G := G) σ f <|
    (Representation.IntertwiningMap.mem_range _ _ f _).2 ⟨x, rfl⟩
/-- Helper for Remark 4-4.3-1: postcomposing with the inclusion of the `σ`-isotypic
subrepresentation of `L²(G)` is a linear equivalence on `σ`-intertwining maps. -/
theorem nonempty_intertwiningMap_l2Regular_isotypicSubrepresentation_linearEquiv
    (σ : Representation ℂ G W) [σ.IsIrreducible] :
    Nonempty
      (σ.IntertwiningMap ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) ≃ₗ[ℂ]
        σ.IntertwiningMap (l2RegularModel G)) := by
  let incl : ((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule →ₗ[ℂ] L²(G)) :=
    (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule.subtype
  let iσ :
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation).IntertwiningMap
        (l2RegularModel G) :=
    incl.intertwiningMap_of_isIntertwiningMap
        ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) (l2RegularModel G)
        (fun g x ↦ by
          apply Subtype.ext
          rfl)
  refine ⟨{
      toFun := fun f ↦ iσ.comp f
      invFun := fun f ↦
        let fσ :=
          f.toLinearMap.codRestrict
            ((l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
            (intertwiningMap_apply_mem_l2Regular_isotypicSubrepresentation
              (G := G) σ f)
        fσ.intertwiningMap_of_isIntertwiningMap σ
          ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
          (intertwiningMap_codRestrict_isIntertwining σ (l2RegularModel G)
            (l2RegularIsotypicSubrepresentation (G := G) σ) f
            (intertwiningMap_apply_mem_l2Regular_isotypicSubrepresentation
              (G := G) σ f))
      map_add' := by
        intro f g
        apply Representation.IntertwiningMap.ext
        ext x
        rfl
      map_smul' := by
        intro a f
        apply Representation.IntertwiningMap.ext
        ext x
        rfl
      left_inv := by
        intro f
        apply Representation.IntertwiningMap.ext
        ext x
        rfl
      right_inv := by
        intro f
        apply Representation.IntertwiningMap.ext
        ext x
        rfl }⟩
/-- Helper for Remark 4-4.3-1: the canonical matrix-coefficient family into the `σ`-isotypic
summand is linear in the chosen functional. -/
noncomputable def matrixCoefficientIntertwining_l2Regular_codRestrictLinear
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible] :
    Module.Dual ℂ W →ₗ[ℂ]
      σ.IntertwiningMap ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) := by
  let e :=
    (nonempty_intertwiningMap_l2Regular_isotypicSubrepresentation_linearEquiv
      (G := G) (σ := σ)).some
  exact e.symm.toLinearMap.comp (matrixCoefficientIntertwining_l2RegularLinear (G := G) σ hσ)
/-- Helper for Remark 4-4.3-1: the corestricted linear matrix-coefficient family is injective. -/
theorem matrixCoefficientIntertwining_l2Regular_codRestrictLinear_injective
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible] :
    Function.Injective (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
      (G := G) σ hσ) := by
  let e :=
    (nonempty_intertwiningMap_l2Regular_isotypicSubrepresentation_linearEquiv
      (G := G) (σ := σ)).some
  exact e.symm.injective.comp
    (matrixCoefficientIntertwining_l2RegularLinear_injective (G := G) σ hσ)

/-- Helper for Remark 4-4.3-1: the injective coefficient family admits an algebraic left inverse,
independent of the analytic recovery construction. -/
noncomputable def matrixCoefficientIntertwining_l2Regular_codRestrictLinear_leftInverse
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible] :
    σ.IntertwiningMap ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) →ₗ[ℂ]
      Module.Dual ℂ W :=
  (matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
    |>.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr
        (matrixCoefficientIntertwining_l2Regular_codRestrictLinear_injective
          (G := G) σ hσ))
    |>.choose

/-- Helper for Remark 4-4.3-1: the algebraic left inverse recovers every dual vector from its
matrix-coefficient image. -/
theorem matrixCoefficientIntertwining_l2Regular_codRestrictLinear_leftInverse_apply
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible] (ℓ : Module.Dual ℂ W) :
    matrixCoefficientIntertwining_l2Regular_codRestrictLinear_leftInverse
        (G := G) σ hσ
        ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ) ℓ) = ℓ := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψalg := matrixCoefficientIntertwining_l2Regular_codRestrictLinear_leftInverse
    (G := G) σ hσ
  have hcomp :
      Ψalg.comp Φ = LinearMap.id := by
    simpa [Ψalg, Φ, matrixCoefficientIntertwining_l2Regular_codRestrictLinear_leftInverse]
      using
        ((Φ.exists_leftInverse_of_injective
            (LinearMap.ker_eq_bot.mpr
              (matrixCoefficientIntertwining_l2Regular_codRestrictLinear_injective
                (G := G) σ hσ))).choose_spec)
  have happly := congrArg (fun F : Module.Dual ℂ W →ₗ[ℂ] Module.Dual ℂ W ↦ F ℓ) hcomp
  simpa [Ψalg, Φ] using happly

/-- Helper for Remark 4-4.3-1: once the canonical coefficient map `Φ` has full range, the
algebraic left inverse already constructed from injectivity becomes a genuine two-sided inverse.
This separates the remaining Peter-Weyl issue from basic finite-dimensional linear algebra. -/
theorem
    matrixCoefficientIntertwining_l2Regular_codRestrictLinear_leftInverse_rightInverse_of_range_eq_top
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (hrange :
      LinearMap.range (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
        (G := G) σ hσ) = ⊤) :
    (matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ).comp
        (matrixCoefficientIntertwining_l2Regular_codRestrictLinear_leftInverse
          (G := G) σ hσ) =
      LinearMap.id := by
  let Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ
  let Ψalg := matrixCoefficientIntertwining_l2Regular_codRestrictLinear_leftInverse
    (G := G) σ hσ
  -- Every target intertwiner lies in `range Φ`, so the algebraic left inverse evaluates it by
  -- first choosing a preimage and then applying the already proved left-inverse identity.
  apply LinearMap.ext
  intro T
  have hT_range : T ∈ LinearMap.range Φ := by
    rw [hrange]
    exact Submodule.mem_top
  rcases hT_range with ⟨ℓ, rfl⟩
  simp [Φ, Ψalg,
    matrixCoefficientIntertwining_l2Regular_codRestrictLinear_leftInverse_apply]
/-- Helper for Remark 4-4.3-1: the `σ`-isotypic summand inherits the ambient `L²`-inner-product
invariance of the left-regular action. -/
theorem l2RegularIsotypicSubrepresentation_inner_map_map
    (σ : Representation ℂ G W) (g : G)
    (f h : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule) :
    inner ℂ (((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) g f)
      (((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) g h) =
        inner ℂ f h := by
  change inner ℂ ((l2RegularModel G) g f.1) ((l2RegularModel G) g h.1) = inner ℂ f.1 h.1
  simpa using l2RegularModel_inner_map_map (G := G) g f.1 h.1
noncomputable def intertwiningMap_toDualAdjointMap (σ : Representation ℂ G W)
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y) :
    σ.IntertwiningMap ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) →ₗ⋆[ℂ]
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation).IntertwiningMap σ :=
  Remark_4_4_3_1.intertwiningMap_toDualAdjointMap_generic
    (G := G) (σ := σ)
    (τ := (l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    J hJ (l2RegularIsotypicSubrepresentation_inner_map_map (G := G) (σ := σ))
/-- Helper for Remark 4-4.3-1: evaluating the conjugate-linear `J`-adjoint construction against `J` recovers the ambient inner product pairing. -/
theorem intertwiningMap_toDualAdjointMap_apply (σ : Representation ℂ G W)
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (v : (l2RegularIsotypicSubrepresentation (G := G) σ).toSubmodule)
    (x : W) :
    J (intertwiningMap_toDualAdjointMap (G := G) σ J hJ T v) x =
      inner ℂ v (T x) := by
  simpa [intertwiningMap_toDualAdjointMap] using
    Remark_4_4_3_1.intertwiningMap_toDualAdjointMap_generic_apply
      (G := G) (σ := σ)
      (τ := (l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
      (J := J) (hJ := hJ)
      (hτ_inner_map_map := l2RegularIsotypicSubrepresentation_inner_map_map
        (G := G) (σ := σ))
      (T := T) (v := v) (x := x)
noncomputable def matrixCoefficient_codRestrict_dualRecovery
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y) :
    σ.IntertwiningMap ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation) →ₗ[ℂ]
      Module.Dual ℂ W :=
  Remark_4_4_3_1.dualRecovery_generic
    (G := G) (σ := σ)
    (τ := (l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
    (matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
    J hJ (l2RegularIsotypicSubrepresentation_inner_map_map (G := G) (σ := σ))
/-- Helper for Remark 4-4.3-1: the recovery functional evaluates to the conjugated Schur scalar
used in the source proof. -/
theorem matrixCoefficient_codRestrict_dualRecovery_apply
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (x : W) :
    matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ T x =
      star
        (scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp
            (matrixCoefficientIntertwining_l2Regular_codRestrictLinear
              (G := G) σ hσ (J x)))) := by
  simpa [matrixCoefficient_codRestrict_dualRecovery, intertwiningMap_toDualAdjointMap] using
    Remark_4_4_3_1.dualRecovery_generic_apply
      (G := G) (σ := σ)
      (τ := (l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
      (Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
      (J := J) (hJ := hJ)
      (hτ_inner_map_map := l2RegularIsotypicSubrepresentation_inner_map_map
        (G := G) (σ := σ))
      (T := T) (x := x)
/-- Helper for Remark 4-4.3-1: pairing a test intertwiner with a coefficient image already
evaluates the chosen dual vector on the recovered `J`-representative, with no extra conjugation.
-/
theorem matrixCoefficient_codRestrict_pairing_eval_on_image_exact
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (ℓ : Module.Dual ℂ W) :
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp
        ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ) ℓ)) =
      ℓ
        (J.symm
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) := by
  -- Route correction: use the generic pairing identity directly, rather than rederiving it from
  -- the positivity-normalized fixed-vector scalar.
  simpa [matrixCoefficient_codRestrict_dualRecovery, intertwiningMap_toDualAdjointMap] using
    Remark_4_4_3_1.pairing_eval_generic
      (G := G) (σ := σ)
      (τ := (l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
      (Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
      (J := J) (hJ := hJ)
      (hJ_herm := hJ_herm)
      (hτ_inner_map_map := l2RegularIsotypicSubrepresentation_inner_map_map
        (G := G) (σ := σ))
      (S := T) (ℓ := ℓ)

/-- Helper for Remark 4-4.3-1: the analytic recovery functional is uniquely determined by its
pairings against all matrix-coefficient images. This reduces any future proof of `Ψ T = η` to one
source pairing computation. -/
theorem matrixCoefficient_codRestrict_dualRecovery_eq_of_pairing_eval
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation))
    (η : Module.Dual ℂ W)
    (hpair :
      ∀ ℓ : Module.Dual ℂ W,
        scalar_of_intertwining_end (G := G) σ
          ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp
            ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ) ℓ)) =
          ℓ (J.symm η)) :
    (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T = η := by
  let Ψ := matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ
  have hvec : J.symm (Ψ T) = J.symm η := by
    by_contra hne
    have hdiff : J.symm (Ψ T) - J.symm η ≠ 0 := sub_ne_zero.mpr hne
    rcases Module.Projective.exists_dual_eq_one ℂ hdiff with ⟨ℓ, hℓ⟩
    have hrecoverℓ :=
      matrixCoefficient_codRestrict_pairing_eval_on_image_exact
        (G := G) (σ := σ) (hσ := hσ) (J := J) (hJ := hJ)
        (hJ_herm := hJ_herm) (T := T) (ℓ := ℓ)
    have hsame : ℓ (J.symm (Ψ T)) = ℓ (J.symm η) := by
      -- The source pairing formula identifies the recovered dual by its values on every test
      -- functional `ℓ`.
      calc
        ℓ (J.symm (Ψ T))
            =
          scalar_of_intertwining_end (G := G) σ
            ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ T).comp
              ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear
                (G := G) σ hσ) ℓ)) := by
                  symm
                  exact hrecoverℓ
        _ = ℓ (J.symm η) := hpair ℓ
    have hzero : ℓ (J.symm (Ψ T) - J.symm η) = 0 := by
      rw [map_sub, hsame, sub_self]
    have hone : (1 : ℂ) = 0 := by
      rw [← hℓ, hzero]
    exact one_ne_zero hone
  exact J.symm.injective hvec
/-- Helper for Remark 4-4.3-1: the recovery pairing against a test intertwiner is represented by
evaluating the recovered dual vector on the `J`-representative of that test intertwiner. -/
theorem matrixCoefficient_codRestrict_recovery_represents_testPairing
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (S T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    scalar_of_intertwining_end (G := G) σ
      ((intertwiningMap_toDualAdjointMap (G := G) σ J hJ S).comp
        ((matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ).comp
          (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T)) =
    (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) T
      (J.symm
        ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ) S)) := by
  simpa [matrixCoefficient_codRestrict_dualRecovery, intertwiningMap_toDualAdjointMap] using
    Remark_4_4_3_1.recovery_represents_testPairing_generic
      (G := G) (σ := σ)
      (τ := (l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)
      (Φ := matrixCoefficientIntertwining_l2Regular_codRestrictLinear (G := G) σ hσ)
      (J := J) (hJ := hJ) (hJ_herm := hJ_herm)
      (hτ_inner_map_map := l2RegularIsotypicSubrepresentation_inner_map_map
        (G := G) (σ := σ))
      (S := S) (T := T)
/-- Helper for Remark 4-4.3-1: Hermitian symmetry swaps the two recovered dual vectors after
complex conjugation. -/
theorem matrixCoefficient_codRestrict_dualRecovery_swap_star
    (σ : Representation ℂ G W) (hσ : Continuous fun p : G × W ↦ σ p.1 p.2)
    [σ.IsIrreducible]
    (J : W ≃ₗ⋆[ℂ] Module.Dual ℂ W)
    (hJ : ∀ g : G, ∀ x y : W, J (σ g x) (σ g y) = J x y)
    (hJ_herm : ∀ x y : W, star (J x y) = J y x)
    (S T : σ.IntertwiningMap
      ((l2RegularIsotypicSubrepresentation (G := G) σ).toRepresentation)) :
    star
        ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ S)
          (J.symm
            ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ T)))) =
      (matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ T)
        (J.symm
          ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ S))) := by
  -- The recovered dual vectors live inside the same Hermitian form `J`, so `hJ_herm` swaps them.
  simpa using
    hJ_herm
      (J.symm
        ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ S)))
      (J.symm
        ((matrixCoefficient_codRestrict_dualRecovery (G := G) σ hσ J hJ T)))


end PeterWeyl

end Remark_4_4_3_1

end Representation
