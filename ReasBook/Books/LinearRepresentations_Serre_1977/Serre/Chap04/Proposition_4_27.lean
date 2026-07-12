import LinearRepresentations_Serre_1977.Chap04.Definition_4_26
import LinearRepresentations_Serre_1977.Chap04.Proposition_4_18
import LinearRepresentations_Serre_1977.Chap04.Proposition_4_21
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_5
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section

open MeasureTheory

universe u v

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V]

-- Analogue note: the finite-group owner
-- `Representation.asAlgebraHom_classFunction_sum_eq_character_sum_smul_id` in Chapter 2 and
-- the canonical Schur lemma `Representation.intertwiningMap_eq_smul_id`, recalled in
-- Proposition 4-21 for the compact-group setting, determine the API shape here.

/-- The averaged operator attached to `f : G → ℂ` and `ρ` is the normalized-Haar integral
`∫ t, f t • ρ t`. -/
def classFunctionAveragedEndomorphism
    (ρ : Representation ℂ G V) (f : G → ℂ) : V →L[ℂ] V :=
  ∫ t, f t • LinearMap.toContinuousLinearMap (ρ t) ∂μG

/-- Helper for Proposition 4-27: the operator-valued integrand `t ↦ f t • ρ t` is Bochner
integrable on the compact group `G`. -/
private theorem classFunctionAveragedEndomorphism_integrable
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] (f : G → ℂ)
    (hf_cont : Continuous f) :
    Integrable (fun t ↦ f t • (LinearMap.toContinuousLinearMap (ρ t) : V →L[ℂ] V)) μG := by
  -- Compactness upgrades continuity of the operator-valued integrand to integrability.
  let b := Module.Free.chooseBasis ℂ V
  let ι := Module.Free.ChooseBasisIndex ℂ V
  letI : Fintype ι := Fintype.ofFinite ι
  let fromMatrixLinear : Matrix ι ι ℂ →ₗ[ℂ] (V →L[ℂ] V) :=
    { toFun := fun A ↦ LinearMap.toContinuousLinearMap ((Matrix.toLin b b) A)
      map_add' := by
        intro A B
        ext v
        simp
      map_smul' := by
        intro c A
        ext v
        simp }
  have hρclm : Continuous fun t ↦ (LinearMap.toContinuousLinearMap (ρ t) : V →L[ℂ] V) := by
    -- Reconstruct the continuous operator from its continuous matrix coefficients.
    have hcomp :
        Continuous fun t ↦ fromMatrixLinear (LinearMap.toMatrix b b (ρ t)) := by
      exact
        ((LinearMap.toContinuousLinearMap fromMatrixLinear).continuous.comp
          (Representation.continuous_toMatrix ρ b))
    refine hcomp.congr ?_
    intro t
    ext v
    simpa [fromMatrixLinear] using
      congrArg (fun L : V →ₗ[ℂ] V ↦ L v) (Matrix.toLin_toMatrix (v₁ := b) (v₂ := b) (f := ρ t))
  have hcont : Continuous fun t ↦ f t • (LinearMap.toContinuousLinearMap (ρ t) : V →L[ℂ] V) := by
    exact hf_cont.smul hρclm
  have hIntOn :
      IntegrableOn (fun t ↦ f t • (LinearMap.toContinuousLinearMap (ρ t) : V →L[ℂ] V))
        Set.univ μG :=
    ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ hcont.continuousOn
  simpa [MeasureTheory.integrableOn_univ] using hIntOn

/-- Helper for Proposition 4-27: for each `v : V`, the source-facing vector integrand
`t ↦ f t • ρ t v` is Bochner integrable. -/
private theorem classFunctionAveragedVectorIntegrand_integrable
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] (f : G → ℂ)
    (hf_cont : Continuous f) (v : V) :
    Integrable (fun t ↦ f t • ρ t v) μG := by
  -- The orbit map is continuous, so the compact-domain integrand is integrable.
  have hcont : Continuous fun t ↦ f t • ρ t v :=
    hf_cont.smul (Representation.continuous_apply ρ v)
  have hIntOn : IntegrableOn (fun t ↦ f t • ρ t v) Set.univ μG :=
    ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ hcont.continuousOn
  simpa [MeasureTheory.integrableOn_univ] using hIntOn

/-- Evaluating `classFunctionAveragedEndomorphism ρ f` on a vector recovers the source-facing
vector-valued integral `∫ t, f t • ρ t v`. -/
theorem classFunctionAveragedEndomorphism_apply
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] (f : G → ℂ)
    (hf_cont : Continuous f) (v : V) :
    classFunctionAveragedEndomorphism ρ f v =
      ∫ t, f t • ρ t v ∂μG := by
  -- Commute evaluation at `v` through the operator-valued integral.
  have hInt := classFunctionAveragedEndomorphism_integrable ρ f hf_cont
  simpa [classFunctionAveragedEndomorphism] using
    (ContinuousLinearMap.integral_apply hInt v)

/-- Helper for Proposition 4-27: normalized Haar integration is invariant under conjugation. -/
private theorem integral_conjugation_eq_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (φ : G → E) (s : G) :
    ∫ t, φ (s * t * s⁻¹) ∂μG = ∫ t, φ t ∂μG := by
  -- First remove the left translation, then remove the right translation.
  calc
    ∫ t, φ (s * t * s⁻¹) ∂μG = ∫ t, φ (t * s⁻¹) ∂μG := by
      simpa [mul_assoc] using
        (MeasureTheory.integral_mul_left_eq_self (μ := μG) (f := fun t ↦ φ (t * s⁻¹)) s)
    _ = ∫ t, φ t ∂μG := by
      simpa using
        (MeasureTheory.integral_mul_right_eq_self (μ := μG) (f := φ) s⁻¹)

/-- A continuous class function yields a `G`-equivariant averaged operator. -/
theorem classFunctionAveragedEndomorphism_isIntertwiningMap
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] (f : G → ℂ)
    (hf_cont : Continuous f) (hf_class : _root_.IsClassFunction f) :
    ρ.IsIntertwiningMap ρ (classFunctionAveragedEndomorphism ρ f).toLinearMap := by
  refine Representation.IsIntertwiningMap.mk ?_
  intro s v
  -- Rewrite the average on `ρ s v` as a conjugated integral.
  calc
    classFunctionAveragedEndomorphism ρ f (ρ s v)
        = ∫ t, f t • ρ t (ρ s v) ∂μG := by
            rw [classFunctionAveragedEndomorphism_apply ρ f hf_cont]
    _ = ∫ t, f (s * t * s⁻¹) • ρ (s * t * s⁻¹) (ρ s v) ∂μG := by
          symm
          exact integral_conjugation_eq_self (φ := fun t ↦ f t • ρ t (ρ s v)) s
    _ = ∫ t, ρ s (f t • ρ t v) ∂μG := by
          -- The class-function hypothesis turns the conjugated scalar factor back into `f t`.
          refine integral_congr_ae ?_
          filter_upwards with t
          have hs :
              ρ (s * t * s⁻¹) (ρ s v) = ρ s (ρ t v) := by
            simp [map_mul, mul_assoc]
          have hf_class_root : _root_.IsClassFunction f := by
            simpa using hf_class
          have hconj : f (s * t * s⁻¹) = f t := by
            exact _root_.IsClassFunction.map_conj_eq hf_class_root s t
          calc
            f (s * t * s⁻¹) • ρ (s * t * s⁻¹) (ρ s v)
                = f t • ρ (s * t * s⁻¹) (ρ s v) := by
                    rw [hconj]
            _ = f t • ρ s (ρ t v) := by rw [hs]
            _ = ρ s (f t • ρ t v) := by simp
    _ = ρ s (∫ t, f t • ρ t v ∂μG) := by
          -- Pull the fixed operator `ρ s` through the vector-valued integral.
          simpa [Representation.toContinuousLinearEquivHom_apply_apply] using
            (ContinuousLinearEquiv.integral_comp_comm (ρ.toContinuousLinearEquivHom s)
              (fun t ↦ f t • ρ t v))
    _ = ρ s (classFunctionAveragedEndomorphism ρ f v) := by
          rw [classFunctionAveragedEndomorphism_apply ρ f hf_cont]

/-- The canonical intertwining-map owner attached to the averaged operator
`classFunctionAveragedEndomorphism ρ f`. -/
def classFunctionAveragedIntertwiningMap
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] (f : G → ℂ)
    (hf_cont : Continuous f) (hf_class : _root_.IsClassFunction f) :
    ρ.IntertwiningMap ρ :=
  (classFunctionAveragedEndomorphism ρ f).toLinearMap.intertwiningMap_of_isIntertwiningMap ρ ρ
    (classFunctionAveragedEndomorphism_isIntertwiningMap ρ f hf_cont hf_class).isIntertwining

/-- The underlying linear map of `classFunctionAveragedIntertwiningMap ρ f hf_cont hf_class`
is the averaged endomorphism `classFunctionAveragedEndomorphism ρ f`. -/
@[simp] theorem classFunctionAveragedIntertwiningMap_toLinearMap
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] (f : G → ℂ)
    (hf_cont : Continuous f) (hf_class : _root_.IsClassFunction f) :
    (classFunctionAveragedIntertwiningMap ρ f hf_cont hf_class).toLinearMap =
      (classFunctionAveragedEndomorphism ρ f).toLinearMap :=
  rfl

/-- Helper for Proposition 4-27: an irreducible representation cannot have zero-dimensional
carrier. -/
private theorem nontrivial_of_isIrreducible
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] : Nontrivial V := by
  -- If every vector were equal, then the zero subrepresentation would equal the whole space.
  by_contra hV
  letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
  have hbot : (⊥ : Subrepresentation ρ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext y
    constructor
    · intro _
      trivial
    · intro _
      simpa using (Subsingleton.elim y 0)
  exact bot_ne_top hbot

/-- Helper for Proposition 4-27: the trace of the averaged operator is the character integral
`∫ t, f t * ρ.character t`. -/
private theorem trace_classFunctionAveragedEndomorphism
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] (f : G → ℂ)
    (hf_cont : Continuous f) :
    LinearMap.trace ℂ V (classFunctionAveragedEndomorphism ρ f).toLinearMap =
      ∫ t, f t * ρ.character t ∂μG := by
  let b := Module.Free.chooseBasis ℂ V
  let ι := Module.Free.ChooseBasisIndex ℂ V
  letI : Fintype ι := Fintype.ofFinite ι
  have hdiag (i : Module.Free.ChooseBasisIndex ℂ V) :
      b.coord i ((classFunctionAveragedEndomorphism ρ f) (b i)) =
        ∫ t, f t * b.coord i (ρ t (b i)) ∂μG := by
    -- Evaluate the averaged operator on a basis vector, then commute the coordinate map inward.
    calc
      b.coord i ((classFunctionAveragedEndomorphism ρ f) (b i))
          = b.coord i (∫ t, f t • ρ t (b i) ∂μG) := by
              rw [classFunctionAveragedEndomorphism_apply ρ f hf_cont]
      _ = ∫ t, b.coord i (f t • ρ t (b i)) ∂μG := by
            simpa using
              ((LinearMap.toContinuousLinearMap (b.coord i)).integral_comp_comm
                (classFunctionAveragedVectorIntegrand_integrable ρ f hf_cont (b i))).symm
      _ = ∫ t, f t * b.coord i (ρ t (b i)) ∂μG := by
            refine integral_congr_ae ?_
            filter_upwards with t
            simp [smul_eq_mul]
  have hdiagInt (i : Module.Free.ChooseBasisIndex ℂ V) :
      Integrable (fun t ↦ f t * b.coord i (ρ t (b i))) μG := by
    -- Each diagonal matrix coefficient is continuous on the compact group.
    have hcont : Continuous fun t ↦ f t * b.coord i (ρ t (b i)) := by
      exact hf_cont.mul
        (((LinearMap.toContinuousLinearMap (b.coord i)).continuous).comp
          (Representation.continuous_apply ρ (b i)))
    have hIntOn : IntegrableOn (fun t ↦ f t * b.coord i (ρ t (b i))) Set.univ μG :=
      ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ hcont.continuousOn
    simpa [MeasureTheory.integrableOn_univ] using hIntOn
  have hchar (t : G) :
      ρ.character t = ∑ i, b.coord i (ρ t (b i)) := by
    -- Rewrite the character trace using the chosen basis.
    rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    simp [Matrix.diag, LinearMap.toMatrix_apply]
  -- Sum the diagonal formulas and rewrite the resulting diagonal sum as the character.
  calc
    LinearMap.trace ℂ V (classFunctionAveragedEndomorphism ρ f).toLinearMap
        = ∑ i, b.coord i ((classFunctionAveragedEndomorphism ρ f) (b i)) := by
            rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
            simp [Matrix.diag, LinearMap.toMatrix_apply]
    _ = ∑ i, ∫ t, f t * b.coord i (ρ t (b i)) ∂μG := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hdiag i
    _ = ∫ t, ∑ i, f t * b.coord i (ρ t (b i)) ∂μG := by
          rw [integral_finset_sum Finset.univ (fun i _ ↦ hdiagInt i)]
    _ = ∫ t, f t * ρ.character t ∂μG := by
          refine integral_congr_ae ?_
          filter_upwards with t
          rw [hchar t, Finset.mul_sum]

/-- Proposition 4-27: if `f` is a continuous class function on the compact group `G` and `ρ` is
an irreducible finite-dimensional continuous complex representation, then the averaged operator
`classFunctionAveragedEndomorphism ρ f = ∫ t, f t • ρ t ∂μG` is the homothety with ratio
`((Module.finrank ℂ V : ℂ)⁻¹ * ∫ t, f t * ρ.character t ∂μG)`. -/
theorem classFunctionAveragedEndomorphism_eq_characterIntegral_smul_id_of_isIrreducible
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] [Representation.IsIrreducible ρ]
    (f : G → ℂ) (hf_cont : Continuous f) (hf_class : _root_.IsClassFunction f) :
    classFunctionAveragedEndomorphism ρ f =
      (((Module.finrank ℂ V : ℂ)⁻¹ * ∫ t, f t * ρ.character t ∂μG) : ℂ) •
        ContinuousLinearMap.id ℂ V := by
  letI : Nontrivial V := nontrivial_of_isIrreducible (ρ := ρ)
  obtain ⟨c, hc⟩ :=
    Representation.intertwiningMap_eq_smul_id (ρ := ρ)
      (classFunctionAveragedIntertwiningMap ρ f hf_cont hf_class)
  have hTlin :
      (classFunctionAveragedEndomorphism ρ f).toLinearMap = c • (LinearMap.id : V →ₗ[ℂ] V) := by
    -- Forget the canonical intertwining-map owner back to the underlying linear endomorphism.
    simpa using congrArg Representation.IntertwiningMap.toLinearMap hc
  have hc_trace :
      c * (Module.finrank ℂ V : ℂ) = ∫ t, f t * ρ.character t ∂μG := by
    -- Compare the trace of the scalar form from Schur's lemma with the trace integral formula.
    calc
      c * (Module.finrank ℂ V : ℂ)
          = LinearMap.trace ℂ V (c • (LinearMap.id : V →ₗ[ℂ] V)) := by
              simp [LinearMap.trace_id, smul_eq_mul]
      _ = LinearMap.trace ℂ V (classFunctionAveragedEndomorphism ρ f).toLinearMap := by
            rw [hTlin]
      _ = ∫ t, f t * ρ.character t ∂μG := by
            exact trace_classFunctionAveragedEndomorphism ρ f hf_cont
  have hfinrank_ne_zero : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  calc
    classFunctionAveragedEndomorphism ρ f = c • ContinuousLinearMap.id ℂ V := by
      ext v
      exact congrArg (fun L : V →ₗ[ℂ] V ↦ L v) hTlin
    _ = (((Module.finrank ℂ V : ℂ)⁻¹ * ∫ t, f t * ρ.character t ∂μG) : ℂ) •
          ContinuousLinearMap.id ℂ V := by
            congr 1
            calc
              c = (Module.finrank ℂ V : ℂ)⁻¹ * (c * (Module.finrank ℂ V : ℂ)) := by
                    rw [mul_comm c, ← mul_assoc, inv_mul_cancel₀ hfinrank_ne_zero, one_mul]
              _ = (Module.finrank ℂ V : ℂ)⁻¹ * ∫ t, f t * ρ.character t ∂μG := by
                    rw [hc_trace]

/-- In the canonical owner `ρ.IntertwiningMap ρ`, Proposition 4-27 says that the averaged
intertwining operator is the scalar endomorphism with the same character integral ratio. -/
theorem classFunctionAveragedIntertwiningMap_eq_characterIntegral_smul_id_of_isIrreducible
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ] [Representation.IsIrreducible ρ]
    (f : G → ℂ) (hf_cont : Continuous f) (hf_class : _root_.IsClassFunction f) :
    classFunctionAveragedIntertwiningMap ρ f hf_cont hf_class =
      (((Module.finrank ℂ V : ℂ)⁻¹ * ∫ t, f t * ρ.character t ∂μG) : ℂ) • 1 := by
  apply Representation.IntertwiningMap.ext
  simpa using congrArg ContinuousLinearMap.toLinearMap
    (classFunctionAveragedEndomorphism_eq_characterIntegral_smul_id_of_isIrreducible
      ρ f hf_cont hf_class)

end

end Representation
