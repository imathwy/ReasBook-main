import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe w t v₁ v₂ u₁ u₂

noncomputable section

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D) [u.IsContinuous J K]
variable [HasWeakSheafify K (Type t)]
variable [∀ P : Cᵒᵖ ⥤ Type t, u.op.HasLeftKanExtension P]
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-
Domain-style sampling for Lemma 7.21.6:
- primary domain: lower shriek functors on sheaves attached to continuous functors of sites;
- sampled owner API:
  `Functor.sheafPullback`,
  `Functor.sheafAdjunctionContinuous`,
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
  `Functor.sheafPullbackConstruction.sheafPullbackIso`,
  `LocalizationLeftKanExtension.preservesFiniteConnectedLimits`;
- source/core/bridge triage:
  `source-facing`: the Stacks lower shriek `g_!`;
  `core/canonical`: `u.sheafPullback (Type t) J K`;
  `bridge/view`: Lemma `7.21.5` identifies `g_!` with the sheafified left Kan extension along
  `u.op`, and the chapter's localization file shows the same finite-connected-limit surface for
  the analogous localization lower shriek.

Primitive data are the continuous functor `u`, the left-Kan-extension and weak-sheafification
inputs needed to construct `u.sheafPullback`, and the pullback/equalizer hypotheses on `C` and
`u`. The source also places this lemma in the cocontinuous setup, but that extra hypothesis is
redundant for the canonical owner statement below: finite connected limit preservation concerns
only the lower-shriek owner `u.sheafPullback`, which is already defined from the continuous-side
data.
-/

-- Proof sketch: realize `g_!` as the sheafified left Kan extension along `u.op` from
-- Lemma `7.21.5`. Limits of sheaves are computed on the underlying presheaves, sheafification
-- preserves finite limits, and the presheaf left Kan extension commutes with finite connected
-- limits because the indexing categories `(𝓘_V^u)ᵒᵖ` are filtered under the pullback/equalizer
-- hypotheses on `u`, so their colimits commute with finite connected limits by Lemmas `7.5.1`
-- and `4.19.9`.
/-- Lemma 7.21.6: if `u : C ⥤ D` is continuous, `C` has fibre products and equalizers, and `u`
commutes with them, then the lower shriek `g_!`, realized by
`u.sheafPullback (Type t) J K`, commutes with finite connected limits. -/
theorem sheafPullback_preserves_finite_connected_limits
    (I : Type w) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesLimitsOfShape I (u.sheafPullback (Type t) J K) := sorry

-- Proof sketch: specialize the finite-connected-limit statement to the walking cospan, whose
-- limits are pullbacks.
/-- The canonical lower shriek `u.sheafPullback (Type t) J K` preserves fibre products. -/
theorem sheafPullback_preserves_pullbacks :
    PreservesLimitsOfShape WalkingCospan (u.sheafPullback (Type t) J K) := sorry

-- Proof sketch: specialize the finite-connected-limit statement to the walking parallel pair,
-- whose limits are equalizers.
/-- The canonical lower shriek `u.sheafPullback (Type t) J K` preserves equalizers. -/
theorem sheafPullback_preserves_equalizers :
    PreservesLimitsOfShape WalkingParallelPair (u.sheafPullback (Type t) J K) := sorry

end

end
