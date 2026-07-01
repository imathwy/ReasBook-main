import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open WithAbs
open UniformSpace.Completion

namespace AbsoluteValue

variable {K : Type u} [Field K] (v : AbsoluteValue K ℝ)

/-- Definition 1.2.15: a ring homomorphism from `K` into a complete normed field `L` realizes a
completion of the absolute value `v` if it preserves the given absolute value and has dense image;
the density is the Lean form of the minimality condition among complete normed field extensions. -/
class IsCompletion {L : Type v} [NormedField L] (f : K →+* L) : Prop extends CompleteSpace L where
  /-- The embedding into the candidate completion preserves the given absolute value. -/
  norm_eq : ∀ x : K, ‖f x‖ = v x
  /-- The image of the embedding is dense, expressing minimality of the complete extension. -/
  denseRange : DenseRange f

namespace IsCompletion

variable {v} {L : Type v} [NormedField L] {f : K →+* L}

theorem isometry (hf : IsCompletion v f) : Isometry (f.comp (equiv v).toRingHom) :=
  AddMonoidHomClass.isometry_of_norm _ fun x ↦ by simpa using hf.norm_eq x.ofAbs

theorem denseRange_withAbs (hf : IsCompletion v f) : DenseRange (f.comp (equiv v).toRingHom) := by
  simpa [DenseRange, (equiv v).surjective.range_comp f] using hf.denseRange

/-- Bridge from the source-facing completion predicate to the canonical abstract completion owner
on `WithAbs v`. -/
noncomputable def toAbstractCompletion (hf : IsCompletion v f) : AbstractCompletion (WithAbs v)
    where
  space := L
  coe := f.comp (equiv v).toRingHom
  uniformStruct := inferInstance
  complete := hf.toCompleteSpace
  separation := inferInstance
  isUniformInducing := hf.isometry.isUniformInducing
  dense := hf.denseRange_withAbs

end IsCompletion

/-- The canonical embedding of `K` into its completion at the absolute value `v`. -/
noncomputable abbrev completionEmbedding : K →+* v.Completion :=
  show K →+* v.Completion from coeRingHom.comp (equiv v).symm.toRingHom

/-- Helper for Definition 1.2.15: the canonical embedding is the standard coercion into the
completion after transporting `x : K` to `WithAbs v`. -/
lemma completionEmbedding_apply (x : K) :
    completionEmbedding v x = (((equiv v).symm x : WithAbs v) : v.Completion) := rfl

/-- Helper for Definition 1.2.15: the canonical embedding preserves the given absolute value. -/
lemma completionEmbedding_norm_eq (x : K) : ‖completionEmbedding v x‖ = v x := by
  -- Rewrite the embedding into the literal coercion so the completion norm lemma applies.
  rw [completionEmbedding_apply]
  -- Transport the norm computation from the completion back to `WithAbs v`.
  rw [UniformSpace.Completion.norm_coe]
  -- On `WithAbs v`, the norm is definitionally the original absolute value.
  simpa using WithAbs.norm_toAbs_eq v x

/-- Helper for Definition 1.2.15: the canonical embedding has dense image in the completion. -/
lemma completionEmbedding_denseRange : DenseRange (completionEmbedding v) := by
  -- Rewrite the image of `completionEmbedding` through the surjective equivalence
  -- `K ≃+* WithAbs v` so density reduces to the standard completion coercion.
  simpa [completionEmbedding, DenseRange] using
    (((equiv v).symm.surjective.range_comp ((↑) : WithAbs v → v.Completion)) ▸
      (UniformSpace.Completion.denseRange_coe : DenseRange ((↑) : WithAbs v → v.Completion)))

/-- The canonical completion `v.Completion` is a completion of the absolute value `v`. -/
instance : IsCompletion v (completionEmbedding v) where
  -- The completion type already carries the canonical completeness instance.
  toCompleteSpace := inferInstance
  -- Norm preservation is exactly the transport statement proved above.
  norm_eq := completionEmbedding_norm_eq v
  -- Minimality is encoded by density of the canonical embedding.
  denseRange := completionEmbedding_denseRange v

end AbsoluteValue
