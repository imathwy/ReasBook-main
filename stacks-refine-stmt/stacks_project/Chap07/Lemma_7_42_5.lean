import Mathlib
import stacks_project.Chap07.Definition_7_42_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

section

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
variable [u.IsContinuous J K] [u.IsAlmostCocontinuous J K]

/- Domain-style sampling for Lemma 7.42.5:
- primary domain: direct-image functors on sheaves of types for continuous, almost cocontinuous
  functors of sites;
- sampled owner API:
  `Functor.sheafPushforwardContinuous`,
  `PreservesColimitsOfShape`,
  `Functor.IsAlmostCocontinuous`,
  `Limits.preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts`;
- source/core/bridge triage:
  `source-facing`: the Stacks Project statement that `u_*` commutes with finite connected
  colimits, hence with pushouts and coequalizers;
  `core/canonical`: the owner property
  `PreservesColimitsOfShape I (u.sheafPushforwardContinuous (Type w) J K)`;
  `bridge/view`: the specializations to `WalkingCospan` and `WalkingParallelPair`.

Primitive data are only the site functor `u`, the two topologies, the weak sheafification
hypotheses, and the continuity/almost-cocontinuity assumptions. The pushout and coequalizer
statements are derived API from the finite-connected-colimit owner and should remain companion
specializations rather than parallel root declarations. -/

-- Proof sketch: for a finite connected diagram of sheaves on `(D, K)`, compute its colimit as the
-- sheafification of the presheaf colimit. Finite connected colimits of singleton sets are
-- singleton, so Lemma `7.42.4` applies to the underlying presheaf colimit and identifies pulling
-- back after sheafification with sheafifying after pullback. Precomposition on presheaves preserves
-- all colimits, hence the direct-image functor on sheaves preserves the original finite connected
-- colimit.
private instance sheafPushforwardContinuous_preservesFiniteConnectedColimits
    (I : Type u₃) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesColimitsOfShape I (u.sheafPushforwardContinuous (Type w) J K) := by
  sorry

end

section

variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]

/-- Lemma 7.42.5: if `u : (C, J) ⥤ (D, K)` is continuous and almost cocontinuous, then the
direct-image functor `u^s = u^p : Sh(K, Type w) ⥤ Sh(J, Type w)` preserves finite connected
colimits. -/
theorem sheafPushforwardContinuous_preserves_finite_connected_colimits_of_isAlmostCocontinuous
    [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
    [u.IsAlmostCocontinuous J K]
    (I : Type u₃) [SmallCategory I] [FinCategory I] [IsConnected I] :
    PreservesColimitsOfShape I (u.sheafPushforwardContinuous (Type w) J K) := by
  infer_instance

-- Proof sketch: `WalkingSpan` is a finite connected indexing category, so this is the
-- specialization of the finite-connected-colimit preservation statement to pushout diagrams.
/-- Under the continuous and almost cocontinuous hypotheses, the direct-image functor on sheaves
of sets preserves pushouts. -/
theorem sheafPushforwardContinuous_preservesPushouts_of_isAlmostCocontinuous
    [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
    [u.IsAlmostCocontinuous J K]
    :
    PreservesColimitsOfShape WalkingSpan
      (u.sheafPushforwardContinuous (Type w) J K) :=
  sheafPushforwardContinuous_preserves_finite_connected_colimits_of_isAlmostCocontinuous
    u J K WalkingSpan

-- Proof sketch: `WalkingParallelPair` is a finite connected indexing category, so this is the
-- specialization of the finite-connected-colimit preservation statement to coequalizer diagrams.
/-- Under the continuous and almost cocontinuous hypotheses, the direct-image functor on sheaves
of sets preserves coequalizers. -/
theorem sheafPushforwardContinuous_preservesCoequalizers_of_isAlmostCocontinuous
    [HasWeakSheafify J (Type w)] [HasWeakSheafify K (Type w)]
    [u.IsAlmostCocontinuous J K]
    :
    PreservesColimitsOfShape WalkingParallelPair
      (u.sheafPushforwardContinuous (Type w) J K) :=
  sheafPushforwardContinuous_preserves_finite_connected_colimits_of_isAlmostCocontinuous
    u J K WalkingParallelPair

end

end CategoryTheory.Functor
