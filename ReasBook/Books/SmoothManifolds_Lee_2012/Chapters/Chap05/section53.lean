import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_5_53 (from Chap05/Sec05_36) -/
open scoped Manifold
open Manifold

section RestrictingMapsToSubmanifoldsWithBoundary

universe u𝕜 uE uH uM uE' uH' uS uE'' uH'' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {S : Set M}
variable [ChartedSpace H' S]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ⊤ S]
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H'' N]
variable {K : ModelWithCorners 𝕜 E'' H''} [IsManifold K ⊤ N]

-- Theorem 5.53 is source-facing, while the canonical owners are the chapter-level restriction
-- theorem `contMDiff_restrict_subtype` and the owner method
-- `Manifold.IsSmoothEmbedding.contMDiff_toSubtype`.

/-- Theorem 5.53 (1): if `S ⊆ M` is an embedded submanifold with boundary and `F : M → N` is
smooth, then the restriction `S → N` is smooth. -/
theorem contMDiff_restrict_subtype_of_isEmbeddedSubmanifoldWithBoundary
    {F : M → N} (hS : IsSmoothEmbedding J I ⊤ (Subtype.val : S → M))
    (hF : ContMDiff I K ⊤ F) :
    ContMDiff J K ⊤ (fun x : S ↦ F x.1) := by
  have hsub : ContMDiff J I ⊤ (Subtype.val : S → M) := by
    sorry
  simpa using contMDiff_restrict_subtype hsub F hF

/- Theorem 5.53 (2): this is exactly the canonical owner theorem
`Manifold.IsSmoothEmbedding.contMDiff_toSubtype`; no additional boundaryless hypothesis on the
ambient manifold is part of the mathematics. -/
recall Manifold.IsSmoothEmbedding.contMDiff_toSubtype

end RestrictingMapsToSubmanifoldsWithBoundary
