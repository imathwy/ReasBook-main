import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_35.Proposition_5_37
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_54.Definition_8_54_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_58.Definition_8_58_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold Set

section

universe uE uH uM uE' uH'

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ∞ S]

namespace VectorField

-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so this item was
-- matched against the local `tangentVector_mem_submanifold_iff_forall_smooth_eq_zero` criterion
-- from Proposition 5.37 and the Chapter 8 `IsTangentToSubmanifold` API.

/-- Proposition 8.22: let `M` be a smooth manifold, let `S ⊆ M` be an embedded submanifold with
or without boundary, and let `X` be a smooth vector field on `M`. Then `X` is tangent to `S` if
and only if, for every smooth function `f` on `M` whose restriction to `S` vanishes, the
directional derivative `Xf` also vanishes on `S`. -/
theorem isTangentToSubmanifold_iff_forall_smooth_apply_eq_zero
    (hS : IsSmoothEmbedding J I ∞ (Subtype.val : S → M))
    (X : ∀ p : M, TangentSpace I p) :
    IsTangentToSubmanifold S J X ↔
      ∀ f : C^∞⟮I, M; ℝ⟯, EqOn f 0 S →
        EqOn (VectorField.apply X f) 0 S := by
  constructor
  · intro hX f hf p hp
    simpa using
      (tangentVector_mem_submanifold_iff_forall_smooth_eq_zero S hS ⟨p, hp⟩ (X p)).mp
        (hX ⟨p, hp⟩) f hf
  · intro h p
    refine (tangentVector_mem_submanifold_iff_forall_smooth_eq_zero S hS p (X p)).mpr ?_
    intro f hf
    simpa using h f hf p.2

end VectorField

end
