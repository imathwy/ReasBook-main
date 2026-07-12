import LinearRepresentations_Serre_1977.Chap04.Definition_4_9
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_5
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

open MeasureTheory
open scoped ENNReal

noncomputable section

-- Semantic recall verified via `lean_leansearch`: `MeasureTheory.Lp` is the canonical `L²`
-- owner for square-integrable classes, and Definition 4-28 gives the local precedent for
-- packaging a source-facing `L²` subspace as a subtype of a closed submodule.

universe u v

section

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G]
variable [BorelSpace G] [IsTopologicalGroup G] [MeasurableMul G]
variable (H : ClosedSubgroup G)
variable {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
variable [MeasurableSpace W] [BorelSpace W]

instance instIsTopologicalGroupClosedSubgroup : IsTopologicalGroup H := by
  change IsTopologicalGroup ((H : Subgroup G))
  infer_instance

local notation "L²W" => (G →₂[(μG : Measure G)] W)

variable (θ : Representation ℂ H W) [Representation.IsContinuous θ]

/-- For each `t : H`, the value action `θ t` is a continuous linear endomorphism of `W`. -/
def inducedRepresentationInfiniteIndexValueAction (t : H) : W →L[ℂ] W :=
  { toLinearMap := θ t
    cont :=
      (Representation.continuousAction θ).comp
        (continuous_const.prodMk continuous_id) }

/-- Helper for the induced infinite-index construction: left translation by `t ∈ H` acts
continuously on `L²(G, W)`. -/
def inducedRepresentationInfiniteIndexLeftTranslate (t : H) : L²W →L[ℂ] L²W :=
  (((MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
      (fun u : G ↦ (t : G) * u)
      (MeasureTheory.measurePreserving_mul_left (μG : Measure G) (t : G))) :
      L²W →ₗᵢ[ℂ] L²W)).toContinuousLinearMap

/-- The pointwise `H`-action on values extends continuously to `L²(G, W)`. -/
def inducedRepresentationInfiniteIndexPointwiseAction (t : H) : L²W →L[ℂ] L²W :=
  (inducedRepresentationInfiniteIndexValueAction H θ t).compLpL 2 (μG : Measure G)

omit [MeasurableMul G] [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Helper for Definition 4-46: pointwise application of `θ t` is represented almost everywhere by
`u ↦ θ t (f u)`. -/
theorem inducedRepresentationInfiniteIndexPointwiseAction_apply_ae_eq
    (t : H) (f : L²W) :
    inducedRepresentationInfiniteIndexPointwiseAction H θ t f =ᵐ[μG]
      fun u : G ↦ θ t (f u) := by
  simpa [inducedRepresentationInfiniteIndexPointwiseAction] using
    (ContinuousLinearMap.coeFn_compLpL
      (inducedRepresentationInfiniteIndexValueAction H θ t) f)

/-- The closed `L²(G, W)` submodule of square-integrable classes satisfying the covariance
relation almost everywhere. -/
def inducedRepresentationInfiniteIndexSubmodule : ClosedSubmodule ℂ L²W :=
  ⨅ t : H,
    ClosedSubmodule.comap
      (inducedRepresentationInfiniteIndexLeftTranslate H t -
        inducedRepresentationInfiniteIndexPointwiseAction H θ t)
      (⊥ : ClosedSubmodule ℂ L²W)

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Membership in the induced `L²`-submodule means satisfying the covariance relation in `L²`
for every `t : H`. -/
@[simp]
theorem mem_inducedRepresentationInfiniteIndexSubmodule_iff (f : L²W) :
    f ∈ inducedRepresentationInfiniteIndexSubmodule H θ ↔
      ∀ t : H,
        inducedRepresentationInfiniteIndexLeftTranslate H t f =
          inducedRepresentationInfiniteIndexPointwiseAction H θ t f := by
  constructor
  · intro hf t
    have hmem :
        ∀ t : H,
          f ∈ ClosedSubmodule.comap
            (inducedRepresentationInfiniteIndexLeftTranslate H t -
              inducedRepresentationInfiniteIndexPointwiseAction H θ t)
            (⊥ : ClosedSubmodule ℂ L²W) := by
      simpa [inducedRepresentationInfiniteIndexSubmodule] using hf
    have ht := hmem t
    change
      (inducedRepresentationInfiniteIndexLeftTranslate H t f -
        inducedRepresentationInfiniteIndexPointwiseAction H θ t f) ∈
        (⊥ : ClosedSubmodule ℂ L²W) at ht
    change
      inducedRepresentationInfiniteIndexLeftTranslate H t f -
        inducedRepresentationInfiniteIndexPointwiseAction H θ t f = 0 at ht
    exact sub_eq_zero.mp ht
  · intro hf
    have hmem :
        ∀ t : H,
          f ∈ ClosedSubmodule.comap
            (inducedRepresentationInfiniteIndexLeftTranslate H t -
              inducedRepresentationInfiniteIndexPointwiseAction H θ t)
            (⊥ : ClosedSubmodule ℂ L²W) := by
      intro t
      change
        (inducedRepresentationInfiniteIndexLeftTranslate H t f -
          inducedRepresentationInfiniteIndexPointwiseAction H θ t f) ∈
          (⊥ : ClosedSubmodule ℂ L²W)
      change
        inducedRepresentationInfiniteIndexLeftTranslate H t f -
          inducedRepresentationInfiniteIndexPointwiseAction H θ t f = 0
      exact sub_eq_zero.mpr (hf t)
    simpa [inducedRepresentationInfiniteIndexSubmodule] using hmem

/-- The internal Hilbert-space realization is the closed `L²` submodule of covariant
square-integrable classes. -/
abbrev inducedRepresentationInfiniteIndexSpace : Type _ :=
  (inducedRepresentationInfiniteIndexSubmodule H θ : Submodule ℂ L²W)

/-- Elements of the induced Hilbert space are canonically viewed as `W`-valued functions on `G`
through their `L²` representatives. -/
instance inducedRepresentationInfiniteIndexSpace_coeFun :
    CoeFun (inducedRepresentationInfiniteIndexSpace H θ) (fun _ ↦ G → W) where
  coe f := ((f : L²W) : G → W)

/-- Right translation on `L²(G, W)` is given by composing with `u ↦ u * s`. -/
def inducedRepresentationInfiniteIndexAmbientAction (s : G) : L²W →ₗ[ℂ] L²W :=
  MeasureTheory.Lp.compMeasurePreservingₗ ℂ
    (fun u : G ↦ u * s)
    (MeasureTheory.measurePreserving_mul_right μG s)

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Helper for Definition 4-46: left translation is represented almost everywhere by
`u ↦ f ((t : G) * u)`. -/
theorem inducedRepresentationInfiniteIndexLeftTranslate_apply_ae_eq
    (t : H) (f : L²W) :
    inducedRepresentationInfiniteIndexLeftTranslate H t f =ᵐ[μG]
      fun u : G ↦ f ((t : G) * u) := by
  simpa [inducedRepresentationInfiniteIndexLeftTranslate, Function.comp] using
    (MeasureTheory.Lp.coeFn_compMeasurePreserving f
      (MeasureTheory.measurePreserving_mul_left (μG : Measure G) (t : G)))

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Helper for Definition 4-46: the ambient right-translation action on `L²(G, W)` is represented
almost everywhere by `u ↦ f (u * s)`. -/
theorem inducedRepresentationInfiniteIndexAmbientAction_apply_ae_eq
    (s : G) (f : L²W) :
    inducedRepresentationInfiniteIndexAmbientAction s f =ᵐ[μG]
      fun u : G ↦ f (u * s) := by
  simpa [inducedRepresentationInfiniteIndexAmbientAction, Function.comp] using
    (MeasureTheory.Lp.coeFn_compMeasurePreserving f
      (MeasureTheory.measurePreserving_mul_right (μG : Measure G) s))

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Helper for Definition 4-46: left `H`-translation commutes with ambient right translation on
`L²(G, W)`. -/
theorem inducedRepresentationInfiniteIndexLeftTranslate_ambientAction_comm
    (t : H) (s : G) (f : L²W) :
    inducedRepresentationInfiniteIndexLeftTranslate H t
      (inducedRepresentationInfiniteIndexAmbientAction s f) =
      inducedRepresentationInfiniteIndexAmbientAction s
        (inducedRepresentationInfiniteIndexLeftTranslate H t f) := by
  calc
    inducedRepresentationInfiniteIndexLeftTranslate H t
        (inducedRepresentationInfiniteIndexAmbientAction s f)
      = MeasureTheory.Lp.compMeasurePreserving
          (fun u : G ↦ ((t : G) * u) * s)
          ((MeasureTheory.measurePreserving_mul_right (μG : Measure G) s).comp
            (MeasureTheory.measurePreserving_mul_left (μG : Measure G) (t : G))) f := by
          simpa [inducedRepresentationInfiniteIndexLeftTranslate,
            inducedRepresentationInfiniteIndexAmbientAction, Function.comp] using
            (MeasureTheory.Lp.compMeasurePreserving_comp_apply
              (E := W) (p := (2 : ℝ≥0∞)) (μ := (μG : Measure G))
              (μb := (μG : Measure G)) (μc := (μG : Measure G))
              (g := f)
              (hf := MeasureTheory.measurePreserving_mul_right (μG : Measure G) s)
              (hf' := MeasureTheory.measurePreserving_mul_left (μG : Measure G) (t : G))).symm
    _ = MeasureTheory.Lp.compMeasurePreserving
          (fun u : G ↦ (t : G) * (u * s))
          ((MeasureTheory.measurePreserving_mul_left (μG : Measure G) (t : G)).comp
            (MeasureTheory.measurePreserving_mul_right (μG : Measure G) s)) f := by
          congr 1
          ext u
          simp [mul_assoc]
    _ = inducedRepresentationInfiniteIndexAmbientAction s
          (inducedRepresentationInfiniteIndexLeftTranslate H t f) := by
          simpa [inducedRepresentationInfiniteIndexLeftTranslate,
            inducedRepresentationInfiniteIndexAmbientAction, Function.comp] using
            (MeasureTheory.Lp.compMeasurePreserving_comp_apply
              (E := W) (p := (2 : ℝ≥0∞)) (μ := (μG : Measure G))
              (μb := (μG : Measure G)) (μc := (μG : Measure G))
              (g := f)
              (hf := MeasureTheory.measurePreserving_mul_left (μG : Measure G) (t : G))
              (hf' := MeasureTheory.measurePreserving_mul_right (μG : Measure G) s))

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Helper for Definition 4-46: evaluating the pointwise `H`-action at `u * s` is represented
almost everywhere by `θ t (f (u * s))`. -/
theorem inducedRepresentationInfiniteIndexPointwiseAction_apply_mul_ae_eq
    (t : H) (s : G) (f : L²W) :
    ∀ᵐ u ∂(μG : Measure G),
      inducedRepresentationInfiniteIndexPointwiseAction H θ t f (u * s) =
        θ t (f (u * s)) := by
  simpa [Function.comp] using
    (inducedRepresentationInfiniteIndexPointwiseAction_apply_ae_eq H θ t f).comp_tendsto
      (le_of_eq (MeasureTheory.map_mul_right_ae (μ := (μG : Measure G)) s))

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Helper for Definition 4-46: pointwise application of `θ t` commutes with ambient right
translation on `L²(G, W)`. -/
theorem inducedRepresentationInfiniteIndexPointwiseAction_ambientAction_comm
    (t : H) (s : G) (f : L²W) :
    inducedRepresentationInfiniteIndexPointwiseAction H θ t
      (inducedRepresentationInfiniteIndexAmbientAction s f) =
      inducedRepresentationInfiniteIndexAmbientAction s
        (inducedRepresentationInfiniteIndexPointwiseAction H θ t f) := by
  rw [Lp.ext_iff]
  filter_upwards [
    inducedRepresentationInfiniteIndexPointwiseAction_apply_ae_eq H θ t
      (inducedRepresentationInfiniteIndexAmbientAction s f),
    inducedRepresentationInfiniteIndexAmbientAction_apply_ae_eq s f,
    inducedRepresentationInfiniteIndexAmbientAction_apply_ae_eq s
      (inducedRepresentationInfiniteIndexPointwiseAction H θ t f),
    inducedRepresentationInfiniteIndexPointwiseAction_apply_mul_ae_eq H θ t s f
  ] with u hleft hambient hright hpointwise
  simp [hleft, hambient, hright, hpointwise]

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Right translations preserve the induced Hilbert-space realization. -/
theorem inducedRepresentationInfiniteIndexAmbientAction_mem
    (s : G) {f : L²W}
    (hf : f ∈ inducedRepresentationInfiniteIndexSubmodule H θ) :
    inducedRepresentationInfiniteIndexAmbientAction s f ∈
      inducedRepresentationInfiniteIndexSubmodule H θ := by
  rw [mem_inducedRepresentationInfiniteIndexSubmodule_iff] at hf ⊢
  intro t
  -- Transport the defining covariance identity through the commuting ambient action.
  calc
    inducedRepresentationInfiniteIndexLeftTranslate H t
        (inducedRepresentationInfiniteIndexAmbientAction s f) =
        inducedRepresentationInfiniteIndexAmbientAction s
          (inducedRepresentationInfiniteIndexLeftTranslate H t f) := by
          exact inducedRepresentationInfiniteIndexLeftTranslate_ambientAction_comm H t s f
    _ = inducedRepresentationInfiniteIndexAmbientAction s
          (inducedRepresentationInfiniteIndexPointwiseAction H θ t f) := by
          rw [hf t]
    _ = inducedRepresentationInfiniteIndexPointwiseAction H θ t
          (inducedRepresentationInfiniteIndexAmbientAction s f) := by
          exact
            (inducedRepresentationInfiniteIndexPointwiseAction_ambientAction_comm H θ t s f).symm

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Helper for Definition 4-46: ambient right translation by `1` is the identity on `L²(G, W)`. -/
theorem inducedRepresentationInfiniteIndexAmbientAction_one :
    inducedRepresentationInfiniteIndexAmbientAction (G := G) (W := W) (1 : G) = 1 := by
  ext f
  refine
    (inducedRepresentationInfiniteIndexAmbientAction_apply_ae_eq
      (G := G) (W := W) (1 : G) f).trans ?_
  exact Filter.Eventually.of_forall fun u : G ↦ by simp

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Helper for Definition 4-46: two successive ambient right translations are represented almost
everywhere by `u ↦ f ((u * s) * t)`. -/
theorem inducedRepresentationInfiniteIndexAmbientAction_apply_mul_ae_eq
    (s t : G) (f : L²W) :
    inducedRepresentationInfiniteIndexAmbientAction (G := G) (W := W) s
        (inducedRepresentationInfiniteIndexAmbientAction (G := G) (W := W) t f) =ᵐ[μG]
      fun u : G ↦ f ((u * s) * t) := by
  refine (inducedRepresentationInfiniteIndexAmbientAction_apply_ae_eq (G := G) (W := W) s
    (inducedRepresentationInfiniteIndexAmbientAction (G := G) (W := W) t f)).trans ?_
  simpa [Function.comp] using
    (inducedRepresentationInfiniteIndexAmbientAction_apply_ae_eq (G := G) (W := W) t f).comp_tendsto
      (le_of_eq (MeasureTheory.map_mul_right_ae (μ := (μG : Measure G)) s))

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Helper for Definition 4-46: ambient right translations compose according to multiplication in
`G`. -/
theorem inducedRepresentationInfiniteIndexAmbientAction_mul (s t : G) :
    inducedRepresentationInfiniteIndexAmbientAction (G := G) (W := W) (s * t) =
      inducedRepresentationInfiniteIndexAmbientAction (G := G) (W := W) s *
        inducedRepresentationInfiniteIndexAmbientAction (G := G) (W := W) t := by
  ext f
  refine
    (inducedRepresentationInfiniteIndexAmbientAction_apply_ae_eq
      (G := G) (W := W) (s * t) f).trans ?_
  exact
    Filter.EventuallyEq.trans
      (Filter.Eventually.of_forall fun u : G ↦ by simp [mul_assoc])
      (inducedRepresentationInfiniteIndexAmbientAction_apply_mul_ae_eq (G := G) (W := W) s t f).symm

/-- Helper for Definition 4-46: the ambient right-translation action on `L²(G, W)` is a
`G`-representation. -/
def inducedRepresentationInfiniteIndexAmbientRepresentation :
    Representation ℂ G L²W where
  toFun := inducedRepresentationInfiniteIndexAmbientAction
  map_one' := inducedRepresentationInfiniteIndexAmbientAction_one (G := G) (W := W)
  map_mul' := inducedRepresentationInfiniteIndexAmbientAction_mul (G := G) (W := W)

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- Helper for Definition 4-46: ambient right translation acts inside the covariant `L²`
subrepresentation. -/
theorem inducedRepresentationInfiniteIndexSubrepresentation_apply_mem
    (H : ClosedSubgroup G) (θ : Representation ℂ H W) [Representation.IsContinuous θ]
    (g : G) {f : L²W}
    (hf : f ∈ inducedRepresentationInfiniteIndexSubmodule H θ) :
    inducedRepresentationInfiniteIndexAmbientRepresentation (G := G) (W := W) g f ∈
      inducedRepresentationInfiniteIndexSubmodule H θ := by
  exact inducedRepresentationInfiniteIndexAmbientAction_mem (H := H) (θ := θ) (f := f) g hf

/-- Helper for Definition 4-46: the covariant `L²`-subspace is stable under the ambient
right-translation representation. -/
def inducedRepresentationInfiniteIndexSubrepresentation
    (H : ClosedSubgroup G) (θ : Representation ℂ H W) [Representation.IsContinuous θ] :
    Subrepresentation (inducedRepresentationInfiniteIndexAmbientRepresentation (G := G) (W := W)) :=
  { toSubmodule := inducedRepresentationInfiniteIndexSubmodule H θ
    apply_mem_toSubmodule := inducedRepresentationInfiniteIndexSubrepresentation_apply_mem
      (H := H) (θ := θ) }

/-- Definition 4-46 — Induced Representation, Infinite-Index Case: for a closed subgroup `H ≤ G`
and a Hilbert-space representation of `H` on `W`, formalized here as
`θ : Representation ℂ H W` together with `[Representation.IsContinuous θ]`,
`inducedRepresentationInfiniteIndex H θ` is the induced `G`-representation on the Hilbert space
`inducedRepresentationInfiniteIndexSpace H θ` of square-integrable `W`-valued functions on `G`,
realized as the closed `L²` subspace of classes satisfying the covariance relation
`f (t * u) = θ t (f u)` almost everywhere, with `G` acting by right translation
`(ρ_s f) (u) = f (u * s)` almost everywhere. -/
def inducedRepresentationInfiniteIndex
    (θ : Representation ℂ H W) [Representation.IsContinuous θ] :
    Representation ℂ G (inducedRepresentationInfiniteIndexSpace H θ) :=
  (inducedRepresentationInfiniteIndexSubrepresentation H θ).toRepresentation

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] in
/-- The induced infinite-index representation acts by right translation on the induced Hilbert
space, almost everywhere. -/
theorem inducedRepresentationInfiniteIndex_apply
    (s : G) (f : inducedRepresentationInfiniteIndexSpace H θ) :
    inducedRepresentationInfiniteIndex H θ s f =ᵐ[μG] fun u : G ↦ f (u * s) := by
  simpa [
    inducedRepresentationInfiniteIndex,
    inducedRepresentationInfiniteIndexAmbientRepresentation,
    inducedRepresentationInfiniteIndexSubrepresentation
  ] using
    inducedRepresentationInfiniteIndexAmbientAction_apply_ae_eq s (f : L²W)

end
