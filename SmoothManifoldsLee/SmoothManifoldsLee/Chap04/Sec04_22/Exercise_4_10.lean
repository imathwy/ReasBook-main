import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph

-- Declarations for this item will be appended below by the statement pipeline.

universe u𝕜 uE uH uM uE' uH' uN uE'' uH'' uP

open scoped Manifold ContDiff Topology

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {K : ModelWithCorners 𝕜 E'' H''}
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P]

-- Proof sketch: The forward implication is closure of smoothness under composition. For the
-- reverse implication, continuity of `G` lets us stay inside a source neighborhood where `F`
-- admits a smooth local inverse, and there `G` is locally `localInverse ∘ (F ∘ G)`.
/-- Exercise 4.10 (1): Part (a). For a continuous map `G`, composing on the left with a smooth
local diffeomorphism preserves and detects smoothness. -/
theorem smooth_iff_comp_left_of_isLocalDiffeomorph
    {F : M → N} (hF : IsLocalDiffeomorph I J ∞ F) {G : P → M} (hG : Continuous G) :
    ContMDiff K I ∞ G ↔ ContMDiff K J ∞ (F ∘ G) := by
  constructor
  · intro h
    exact hF.contMDiff.comp h
  · intro h p
    have hFp : IsLocalDiffeomorphAt I J ∞ F (G p) := hF (G p)
    have hlocal :
        ContMDiffAt K I ∞ (hFp.localInverse ∘ (F ∘ G)) p :=
      hFp.localInverse_contMDiffAt.comp p (h p)
    have heq : (hFp.localInverse ∘ (F ∘ G)) =ᶠ[𝓝 p] G := by
      simpa [Function.comp_assoc] using
        hFp.localInverse_eventuallyEq_left.comp_tendsto hG.continuousAt
    exact hlocal.congr_of_eventuallyEq heq.symm

-- Proof sketch: The forward implication is again smoothness of a composition. For the reverse
-- implication, for each `y : N` choose `x` with `F x = y`; a smooth local inverse to `F` at `x`
-- writes `G` locally near `y` as `(G ∘ F) ∘ localInverse`.
/-- Exercise 4.10 (2): Part (b). If a smooth local diffeomorphism is surjective, then composing on
the right with it preserves and detects smoothness. -/
theorem smooth_iff_comp_right_of_surjective_isLocalDiffeomorph
    {F : M → N} (hF : IsLocalDiffeomorph I J ∞ F) (hFs : Function.Surjective F) {G : N → P} :
    ContMDiff J K ∞ G ↔ ContMDiff I K ∞ (G ∘ F) := by
  constructor
  · intro h
    exact h.comp hF.contMDiff
  · intro h y
    obtain ⟨x, rfl⟩ := hFs y
    have hFx : IsLocalDiffeomorphAt I J ∞ F x := hF x
    have hlocal :
        ContMDiffAt J K ∞ ((G ∘ F) ∘ hFx.localInverse) (F x) :=
      ContMDiffAt.comp_of_eq (h x) hFx.localInverse_contMDiffAt
        (hFx.localInverse_left_inv hFx.localInverse_mem_target)
    have heq : ((G ∘ F) ∘ hFx.localInverse) =ᶠ[𝓝 (F x)] G := by
      simpa [Function.comp_assoc] using hFx.localInverse_eventuallyEq_right.fun_comp G
    exact hlocal.congr_of_eventuallyEq heq.symm
