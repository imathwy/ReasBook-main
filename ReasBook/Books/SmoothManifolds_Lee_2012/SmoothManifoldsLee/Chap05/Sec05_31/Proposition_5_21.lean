import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_31.Definition_5_31_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_24.Proposition_4_22

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff
open Topology

universe uE uH uM

namespace Manifold
namespace ImmersedSubmanifold

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]

-- Semantic recall note: `lean_leansearch` returned only general `IsSmoothEmbedding` owners, while
-- local repo precedent in `Problem_5_3` recalls these exact `IsEmbedding` owners on the local
-- `ImmersedSubmanifold.inclusion : S → M` API.
omit [IsManifold I ω M] in
/-- Helper for Proposition 5.21: the inclusion of an empty immersed submanifold is an embedding. -/
lemma inclusion_isEmbedding_of_isEmptyDomain (S : ImmersedSubmanifold I M) [IsEmpty S] :
    IsEmbedding S.inclusion := by
  -- A map out of a subsingleton source is automatically an embedding.
  simpa using (Topology.IsEmbedding.of_subsingleton S.inclusion)

omit [IsManifold I ω M] in
/-- Helper for Proposition 5.21: the chosen `C^ω` inclusion immersion also defines a `C^∞`
immersion, since the same chart normal forms work after lowering the regularity index. -/
lemma inclusion_isImmersion_smooth (S : ImmersedSubmanifold I M) :
    IsImmersion (modelWithCornersSelf ℝ S.ModelSpace) I ∞ S.inclusion := by
  rcases S.inclusion_isImmersion with ⟨F, instNormedAddCommGroupF, instNormedSpaceF, hF⟩
  let _ : NormedAddCommGroup F := instNormedAddCommGroupF
  let _ : NormedSpace ℝ F := instNormedSpaceF
  refine ⟨F, instNormedAddCommGroupF, instNormedSpaceF, ?_⟩
  intro x
  let hx := hF x
  -- Lower the differentiability order by keeping the same source and target charts.
  exact IsImmersionAtOfComplement.mk_of_charts hx.equiv hx.domChart hx.codChart
    hx.mem_domChart_source hx.mem_codChart_source
    (IsManifold.maximalAtlas_subset_of_le
      (I := modelWithCornersSelf ℝ S.ModelSpace) (M := S) (m := ∞) (n := ω) le_top
      hx.domChart_mem_maximalAtlas)
    (IsManifold.maximalAtlas_subset_of_le
      (I := I) (M := M) (m := ∞) (n := ω) le_top hx.codChart_mem_maximalAtlas)
    hx.source_subset_preimage_source hx.writtenInCharts

omit [IsManifold I ω M] in
/-- Helper for Proposition 5.21: a nonempty immersed submanifold has model-space dimension at most
the ambient dimension. -/
lemma modelSpaceFinrank_le_ambient_of_nonempty (S : ImmersedSubmanifold I M)
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ S.ModelSpace] (hS : Nonempty S) :
    Module.finrank ℝ S.ModelSpace ≤ Module.finrank ℝ E := by
  rcases hS with ⟨p⟩
  let hp := S.inclusion_isImmersion.isImmersionAt p
  -- Route correction: read the dimension bound from the immersion chart normal form instead of
  -- from a missing direct `mfderiv` API for the local `ImmersedSubmanifold` wrapper.
  have hinj_comp :
      Function.Injective
        ((hp.equiv.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr ℝ S.ModelSpace hp.complement)).toLinearMap) := by
    intro x y hxy
    have hxy' :
        ContinuousLinearMap.inr ℝ S.ModelSpace hp.complement x =
          ContinuousLinearMap.inr ℝ S.ModelSpace hp.complement y := hp.equiv.injective hxy
    simpa using congrArg Prod.snd hxy'
  letI : FiniteDimensional ℝ hp.complement :=
    FiniteDimensional.of_injective
      ((hp.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inr ℝ S.ModelSpace hp.complement)).toLinearMap)
      hinj_comp
  -- The immersion witness identifies the ambient model space with `S.ModelSpace × hp.complement`.
  have hprod : Module.finrank ℝ (S.ModelSpace × hp.complement) = Module.finrank ℝ E := by
    simpa using hp.equiv.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at hprod
  omega

omit [IsManifold I ω M] in
/-- Helper for Proposition 5.21: codimension `0` forces the immersed submanifold and the ambient
manifold to have the same model-space dimension once the source is nonempty. -/
lemma modelSpaceFinrank_eq_of_codimension_zero_of_nonempty (S : ImmersedSubmanifold I M)
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ S.ModelSpace] (hS : Nonempty S)
    (hcodim : S.codimension = 0) :
    Module.finrank ℝ S.ModelSpace = Module.finrank ℝ E := by
  have hle : Module.finrank ℝ S.ModelSpace ≤ Module.finrank ℝ E :=
    modelSpaceFinrank_le_ambient_of_nonempty S hS
  have hge : Module.finrank ℝ E ≤ Module.finrank ℝ S.ModelSpace := by
    -- Expand the codimension definition and read `a - b = 0` as `a ≤ b`.
    exact Nat.sub_eq_zero_iff_le.mp (by simpa [ImmersedSubmanifold.codimension] using hcodim)
  exact le_antisymm hle hge

/-- Proposition 5.21 (1): an immersed submanifold of codimension `0` in a smooth manifold is
embedded, i.e. its inclusion into the ambient manifold is an embedding. -/
theorem isEmbedding_of_codimension_zero (S : ImmersedSubmanifold I M)
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ S.ModelSpace] (hcodim : S.codimension = 0) :
    IsEmbedding S.inclusion := by
  have hImmersion : IsImmersion (modelWithCornersSelf ℝ S.ModelSpace) I ∞ S.inclusion :=
    inclusion_isImmersion_smooth S
  by_cases hS : Nonempty S
  · have hdim : Module.finrank ℝ S.ModelSpace = Module.finrank ℝ E :=
      modelSpaceFinrank_eq_of_codimension_zero_of_nonempty S hS hcodim
    -- Equal source and target dimensions upgrade the injective immersion to a smooth embedding.
    simpa using
      (smooth_embedding_of_injective_isImmersion_boundaryless_of_eq_finrank
        (I := modelWithCornersSelf ℝ S.ModelSpace) (J := I) (M := S) (N := M)
        (F := S.inclusion) hdim S.inclusion_injective hImmersion).isEmbedding
  · letI : IsEmpty S := ⟨fun p ↦ hS ⟨p⟩⟩
    -- The empty-source case reduces to the subsingleton embedding criterion.
    exact inclusion_isEmbedding_of_isEmptyDomain S

/-- Proposition 5.21 (2): if the inclusion map of an immersed submanifold into a Hausdorff
ambient manifold is proper, then the immersed submanifold is embedded. -/
theorem isEmbedding_of_proper (S : ImmersedSubmanifold I M)
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ S.ModelSpace] [T2Space M]
    (hproper : IsProperMap S.inclusion) :
    IsEmbedding S.inclusion := by
  have hImmersion : IsImmersion (modelWithCornersSelf ℝ S.ModelSpace) I ∞ S.inclusion :=
    inclusion_isImmersion_smooth S
  -- Properness upgrades the injective immersion directly to a smooth embedding.
  simpa using
    (smooth_embedding_of_injective_isImmersion_isProperMap
      (I := modelWithCornersSelf ℝ S.ModelSpace) (J := I) (M := S) (N := M)
      (F := S.inclusion) S.inclusion_injective hImmersion hproper).isEmbedding

/-- Proposition 5.21 (3): a compact immersed submanifold of a Hausdorff smooth manifold is
embedded. -/
theorem isEmbedding_of_compact (S : ImmersedSubmanifold I M)
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ S.ModelSpace] [CompactSpace S] [T2Space M] :
    IsEmbedding S.inclusion := by
  have hImmersion : IsImmersion (modelWithCornersSelf ℝ S.ModelSpace) I ∞ S.inclusion :=
    inclusion_isImmersion_smooth S
  -- Compactness of the source is the Chapter 4 criterion for turning an injective immersion into
  -- a smooth embedding.
  simpa using
    (smooth_embedding_of_compact_source_injective_isImmersion
      (I := modelWithCornersSelf ℝ S.ModelSpace) (J := I) (M := S) (N := M)
      (F := S.inclusion) S.inclusion_injective hImmersion).isEmbedding

end

end ImmersedSubmanifold
end Manifold
