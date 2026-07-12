import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Definition_8_57_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Domain sampling for this item:
-- * source-facing statement: extension of smooth vector fields along an embedded submanifold;
-- * core/canonical owner: bundled smooth sections `ContMDiffSection` of the tangent bundle;
-- * bridge/view already available upstream: `VectorField.f_related` for relation to the
--   inclusion, together with `smooth_vector_fields` from `Example_8_36`.
-- Semantic recall via `lean_leansearch` did not surface a direct submanifold vector-field
-- extension owner, so the source-facing `f_related` formulation remains the right local API here.
-- This file should use the bundled owner directly and treat the submodule presentation only as a
-- derived chapter bridge.

universe uE uE' uH uH' uM

noncomputable section

section

open VectorField

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'}
  [IsManifold I (∞ : ℕ∞ω) M]
  {S : Set M} [ChartedSpace H' S] [IsManifold J (∞ : ℕ∞ω) S]

/-- Problem 8-15 (1): if `S ⊆ M` is an embedded smooth submanifold, with or without boundary, then
every smooth vector field on `S` extends to a smooth vector field on some neighborhood of `S` in
`M`. The agreement along `S` is expressed through the chapter's owner
`f_related` for the codomain-restricted inclusion `S → U`; the pointwise derivative formula is the
derived API `f_related_apply`. -/
theorem exists_local_vectorField_extension_of_isSmoothEmbedding
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M))
    {X : Cₛ^∞⟮J; E', TangentSpace J⟯} :
    ∃ U : TopologicalSpace.Opens M, ∃ hSU : (S : Set M) ⊆ U,
      ∃ Y : Cₛ^∞⟮I; E, fun p : U ↦ TangentSpace I p⟯,
        f_related
          (fun p : S ↦ ⟨(p : M), hSU p.2⟩)
          X
          Y :=
            sorry

section GlobalExtension

variable [T2Space M] [SigmaCompactSpace M]

/-- Problem 8-15 (2): every smooth vector field on a neighborhood of `S` in `M` whose restriction
to `S` is an intrinsic smooth vector field on the embedded submanifold `S` extends to a globally
defined smooth vector field on `M` exactly when `S` is properly embedded in `M`. This is the
source's "every such vector field": the quantified object is the neighborhood field `Y`, not just
an intrinsic field `X` on `S`. In the chapter's formal development, the global extension direction
uses the ambient global vector-field existence machinery, so the manifold `M` carries the standard
hypotheses `[T2Space M]` and `[SigmaCompactSpace M]`. -/
theorem exists_global_vectorField_extension_iff_isProperlyEmbedded
    (hS : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : S → M)) :
    (∀ X : Cₛ^∞⟮J; E', TangentSpace J⟯,
        ∀ U : TopologicalSpace.Opens M, ∀ hSU : (S : Set M) ⊆ U,
          ∀ Y : Cₛ^∞⟮I; E, fun p : U ↦ TangentSpace I p⟯,
            f_related
              (fun p : S ↦ ⟨(p : M), hSU p.2⟩)
              X
              Y →
            ∃ Z : Cₛ^∞⟮I; E, TangentSpace I⟯,
              f_related (Subtype.val : U → M) Y Z) ↔
      S.IsProperlyEmbedded := sorry

end GlobalExtension

end
