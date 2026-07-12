import Mathlib
import SmoothManifolds_Lee_2012.Chap06.Sec06_44.Definition_6_44_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold Set

-- Semantic search note: the `lean_leansearch` tool requested by the statement policy was
-- unavailable in this session, so the statement surface below reuses the source-facing
-- transversality owner from `Definition_6_44_extra_1` together with the local
-- embedded-submanifold conventions from Chapter 5.

section MutualTransversality

universe uEN uEN' uEM uHN uHN' uHM uN uN' uM uDiag uEX uHX uEΔ uHΔ uES uHS

variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
variable {EN' : Type uEN'} [NormedAddCommGroup EN'] [NormedSpace ℝ EN']
variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {HN' : Type uHN'} [TopologicalSpace HN']
variable {HM : Type uHM} [TopologicalSpace HM]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {N' : Type uN'} [TopologicalSpace N'] [ChartedSpace HN' N']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {I : ModelWithCorners ℝ EN HN} [IsManifold I ∞ N]
variable {I' : ModelWithCorners ℝ EN' HN'} [IsManifold I' ∞ N']
variable {J : ModelWithCorners ℝ EM HM} [IsManifold J ∞ M]

/-- Two smooth maps into the same manifold are transverse to each other when, at each pair of
source points with the same image, the ranges of their manifold derivatives together span the
ambient tangent space. -/
def MapsTransverseToEachOther
    (I : ModelWithCorners ℝ EN HN) (I' : ModelWithCorners ℝ EN' HN')
    (J : ModelWithCorners ℝ EM HM) (F : N → M) (F' : N' → M) : Prop :=
  ContMDiff I J ∞ F ∧
    ContMDiff I' J ∞ F' ∧
    ∀ p : N × N', F p.1 = F' p.2 →
      (mfderiv I J F p.1).range ⊔ (mfderiv I' J F' p.2).range = ⊤

omit [IsManifold I ∞ N] [IsManifold I' ∞ N'] [IsManifold J ∞ M] in
/-- `MapsTransverseToEachOther` unfolds to the tangent-space spanning condition in its defining
formula. -/
theorem mapsTransverseToEachOther_iff (F : N → M) (F' : N' → M) :
    MapsTransverseToEachOther I I' J F F' ↔
      ContMDiff I J ∞ F ∧
        ContMDiff I' J ∞ F' ∧
        ∀ p : N × N', F p.1 = F' p.2 →
          (mfderiv I J F p.1).range ⊔ (mfderiv I' J F' p.2).range = ⊤ :=
  Iff.rfl

/-- Problem 6-13 (1): two maps `F : N → M` and `F' : N' → M` are transverse to each other if and
only if the product map `N × N' → M × M`, `(x, x') ↦ (F x, F' x')`, is transverse to the
diagonal subset `{(y, y) : y ∈ M}`. -/
theorem maps_transverse_to_each_other_iff_prod_transverse_to_diagonal
    {EΔ : Type uEΔ} [NormedAddCommGroup EΔ] [NormedSpace ℝ EΔ]
    {HΔ : Type uHΔ} [TopologicalSpace HΔ]
    (JΔ : ModelWithCorners ℝ EΔ HΔ)
    [ChartedSpace HΔ (Set.diagonal M)] [IsManifold JΔ ∞ (Set.diagonal M)]
    [IsEmbeddedSubmanifold (J.prod J) JΔ (Set.diagonal M)]
    {F : N → M} {F' : N' → M} :
    MapsTransverseToEachOther I I' J F F' ↔
      IsTransverseToSubmanifold (J.prod J) (I.prod I') JΔ (Set.diagonal M)
        (fun p : N × N' ↦ (F p.1, F' p.2)) := sorry

/-- Problem 6-13 (2): for a chosen embedded submanifold structure on `S ⊆ M`, a smooth map
`F : N → M` is transverse to `S` exactly when it is transverse to the inclusion `S ↪ M`. -/
theorem map_transverse_to_submanifold_iff_transverse_to_inclusion
    {ES : Type uES} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
    {HS : Type uHS} [TopologicalSpace HS]
    (JS : ModelWithCorners ℝ ES HS) (S : Set M)
    [ChartedSpace HS S] [IsManifold JS ∞ S]
    [IsEmbeddedSubmanifold J JS S]
    {F : N → M} :
    IsTransverseToSubmanifold J I JS S F ↔
      MapsTransverseToEachOther I JS J F ((↑) : S → M) := sorry

/- Problem 6-13 (3) is intentionally omitted: the author's errata deletes this part because the
stated preimage-of-range claim is false in general. -/

end MutualTransversality
