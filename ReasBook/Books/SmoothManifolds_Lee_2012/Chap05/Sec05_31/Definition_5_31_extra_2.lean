import Mathlib
import SmoothManifolds_Lee_2012.Chap05.Sec05_31.Definition_5_31_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped Manifold

universe uE uH uM

namespace Manifold
namespace ImmersedSubmanifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]

/-- Definition 5.31-extra-2: A local parametrization of an immersed `k`-dimensional submanifold
`S` is a map from an open subset of `ℝ^k` that factors through an open embedding into the
underlying manifold of `S`. Equivalently, regarded as a map into `S`, it is a homeomorphism onto an
open subset of `S`. -/
structure IsLocalParametrization (S : ImmersedSubmanifold I M) {k : ℕ}
    (U : Opens (EuclideanSpace ℝ (Fin k))) (X : U → M) : Prop where
  /-- A local parametrization factors through the inclusion of `S` by an open embedding. -/
  exists_lift :
    ∃ F : U → S.domain, X = S.inclusion ∘ F ∧ Topology.IsOpenEmbedding F

/-- A local parametrization provides its factorization through the immersed submanifold as an
instance-level fact. -/
instance instFactExistsLift
    {S : ImmersedSubmanifold I M} {k : ℕ}
    {U : Opens (EuclideanSpace ℝ (Fin k))} {X : U → M}
    (_hX : IsLocalParametrization S U X) :
    Fact (∃ F : U → S.domain, X = S.inclusion ∘ F ∧ Topology.IsOpenEmbedding F) := sorry

/-- A smooth local parametrization is a local parametrization whose lift to the manifold underlying
`S` is smooth. -/
def IsSmoothLocalParametrization (S : ImmersedSubmanifold I M) {k : ℕ}
    (U : Opens (EuclideanSpace ℝ (Fin k))) (X : U → M) : Prop :=
  ∃ F : U → S.domain,
    X = S.inclusion ∘ F ∧
      ContMDiff (𝓡 k) (modelWithCornersSelf ℝ S.ModelSpace) (⊤ : WithTop ℕ∞) F ∧
        Topology.IsOpenEmbedding F

/-- A global parametrization is a local parametrization whose lift to the manifold underlying `S`
is surjective. -/
def IsGlobalParametrization (S : ImmersedSubmanifold I M) {k : ℕ}
    (U : Opens (EuclideanSpace ℝ (Fin k))) (X : U → M) : Prop :=
  ∃ F : U → S.domain,
    X = S.inclusion ∘ F ∧ Topology.IsOpenEmbedding F ∧ Function.Surjective F

-- Proof sketch: forget the smoothness field in the defining witness for a smooth local
-- parametrization and keep the same factorization through the open embedding into `S`.
/-- Any smooth local parametrization is a local parametrization. -/
theorem IsSmoothLocalParametrization.isLocalParametrization
    {S : ImmersedSubmanifold I M} {k : ℕ}
    {U : Opens (EuclideanSpace ℝ (Fin k))} {X : U → M}
    (hX : IsSmoothLocalParametrization S U X) :
    IsLocalParametrization S U X := sorry

-- Proof sketch: if `X = S.inclusion ∘ F` with `F` surjective, then every point of `S.carrier`
-- comes from some `u : U`, and conversely every point in the range of `X` lies in the range of the
-- inclusion map of `S`.
/-- A global parametrization has image equal to the underlying subset of the immersed
submanifold. -/
theorem IsGlobalParametrization.range_eq_carrier
    {S : ImmersedSubmanifold I M} {k : ℕ}
    {U : Opens (EuclideanSpace ℝ (Fin k))} {X : U → M}
    (hX : IsGlobalParametrization S U X) :
    Set.range X = S.carrier := sorry

end ImmersedSubmanifold
end Manifold
