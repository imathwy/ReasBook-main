import Mathlib.Tactic.Recall
import Mathlib.Geometry.Manifold.ContMDiff.Basic

open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH' uN uS uHS uE'' uH''

section RestrictingMapsToSubmanifolds

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ⊤ M]

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {J : ModelWithCorners 𝕜 E' H'} [IsManifold J ⊤ N]

variable {S : Type uS} [TopologicalSpace S]
variable {HS : Type uHS} [TopologicalSpace HS]
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable [ChartedSpace HS S]
variable {K : ModelWithCorners 𝕜 E'' HS} [IsManifold K ⊤ S]

/- Theorem 5.27 is exactly the canonical manifold chain rule `ContMDiff.comp`, specialized to the
smooth inclusion map of an immersed or embedded submanifold. -/
recall ContMDiff.comp

end RestrictingMapsToSubmanifolds

section RestrictingMapsToSubtypes

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H}

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {J : ModelWithCorners 𝕜 E' H'}

variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {s : Set M}
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {K' : ModelWithCorners 𝕜 E'' H''}
variable [ChartedSpace H'' s]

-- Proof sketch: apply the main restriction theorem to the subtype inclusion `Subtype.val : s → M`
-- and identify `F ∘ Subtype.val` with `fun x : s ↦ F x.1`.
/-- If a subtype inclusion into a manifold is smooth, then restricting a smooth map to that
subtype is smooth. -/
theorem contMDiff_restrict_subtype (hsub : ContMDiff K' I ⊤ (Subtype.val : s → M))
    (F : M → N) (hF : ContMDiff I J ⊤ F) :
    ContMDiff K' J ⊤ (fun x : s ↦ F x.1) :=
  hF.comp hsub

end RestrictingMapsToSubtypes
