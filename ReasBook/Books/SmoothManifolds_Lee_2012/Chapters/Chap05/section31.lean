import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_31_extra_1 (from Chap05/Sec05_31) -/
open scoped Manifold

universe u v w u1 u2 u3

namespace Manifold

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]

section

variable (I : ModelWithCorners 𝕜 E H)
variable (M : Type u2) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M]

/-- Definition 5.31-extra-1: An immersed submanifold of a smooth manifold `M` is a boundaryless
smooth manifold together with an injective smooth immersion into `M`; its underlying subset is the
range of the inclusion map. -/
structure ImmersedSubmanifold where
  /-- The model vector space for the boundaryless manifold structure on the immersed submanifold. -/
  ModelSpace : Type u1
  /-- The model space carries its canonical normed additive group structure. -/
  instNormedAddCommGroupModelSpace : NormedAddCommGroup ModelSpace
  /-- The model space is a normed vector space over the ambient field. -/
  instNormedSpaceModelSpace : NormedSpace 𝕜 ModelSpace
  /-- The type carrying the chosen topology and smooth structure on the immersed submanifold. -/
  domain : Type u3
  /-- The chosen topology on the immersed submanifold. -/
  instTopologicalSpaceDomain : TopologicalSpace domain
  /-- The chosen atlas on the immersed submanifold. -/
  instChartedSpaceDomain : ChartedSpace ModelSpace domain
  /-- The immersed submanifold is a boundaryless smooth manifold. -/
  instIsManifoldDomain :
    IsManifold (modelWithCornersSelf 𝕜 ModelSpace) (⊤ : WithTop ℕ∞) domain
  /-- The inclusion map of the immersed submanifold into the ambient manifold. -/
  inclusion : domain → M
  /-- The inclusion map is injective, so its image is a genuine subset of the ambient manifold. -/
  inclusion_injective : Function.Injective inclusion
  /-- The inclusion map is a smooth immersion. -/
  inclusion_isImmersion :
    IsImmersion (modelWithCornersSelf 𝕜 ModelSpace) I (⊤ : WithTop ℕ∞) inclusion

end

attribute [instance] ImmersedSubmanifold.instNormedAddCommGroupModelSpace
attribute [instance] ImmersedSubmanifold.instNormedSpaceModelSpace
attribute [instance] ImmersedSubmanifold.instTopologicalSpaceDomain
attribute [instance] ImmersedSubmanifold.instChartedSpaceDomain
attribute [instance] ImmersedSubmanifold.instIsManifoldDomain

namespace ImmersedSubmanifold

variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type u2} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M]

/-- An immersed submanifold coerces to the boundaryless manifold type carrying its chosen smooth
structure. -/
instance : CoeSort (ImmersedSubmanifold I M) (Type u3) where
  coe S := S.domain

/-- The coerced type underlying an immersed submanifold carries its chosen topology. -/
instance (S : ImmersedSubmanifold I M) : TopologicalSpace S :=
  S.instTopologicalSpaceDomain

/-- The underlying subset of an immersed submanifold is the range of its inclusion into the ambient
manifold. -/
def carrier (S : ImmersedSubmanifold I M) : Set M :=
  Set.range S.inclusion

/-- The codimension of an immersed submanifold is the ambient dimension minus the dimension of its
boundaryless manifold structure. -/
noncomputable def codimension [FiniteDimensional 𝕜 E] (S : ImmersedSubmanifold I M)
    [FiniteDimensional 𝕜 S.ModelSpace] : ℕ :=
  Module.finrank 𝕜 E - Module.finrank 𝕜 S.ModelSpace

/-- An immersed submanifold is a hypersurface when its codimension is `1`. -/
noncomputable def IsHypersurface [FiniteDimensional 𝕜 E] (S : ImmersedSubmanifold I M)
    [FiniteDimensional 𝕜 S.ModelSpace] : Prop :=
  S.codimension = 1

end ImmersedSubmanifold

namespace IsSmoothEmbedding

variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type u2} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {E' : Type u1} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {N : Type u3} [TopologicalSpace N] [ChartedSpace E' N]
variable [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) N]
variable {f : N → M}

/-- A smooth embedding of a boundaryless manifold into `M` canonically determines an immersed
submanifold of `M`. -/
def toImmersedSubmanifold
    (hf : IsSmoothEmbedding (modelWithCornersSelf 𝕜 E') I (⊤ : WithTop ℕ∞) f) :
    ImmersedSubmanifold I M where
  ModelSpace := E'
  instNormedAddCommGroupModelSpace := inferInstance
  instNormedSpaceModelSpace := inferInstance
  domain := N
  instTopologicalSpaceDomain := inferInstance
  instChartedSpaceDomain := inferInstance
  instIsManifoldDomain := inferInstance
  inclusion := f
  inclusion_injective := hf.isEmbedding.injective
  inclusion_isImmersion := hf.isImmersion

end IsSmoothEmbedding

namespace IsImmersion

variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type u2} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {E' : Type u1} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {N : Type u3} [TopologicalSpace N] [ChartedSpace E' N]
variable [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) N]
variable {f : N → M}

/-- An injective smooth immersion of a boundaryless manifold into `M` canonically determines an
immersed submanifold of `M`. -/
def toImmersedSubmanifold
    (hf : IsImmersion (modelWithCornersSelf 𝕜 E') I (⊤ : WithTop ℕ∞) f)
    (hf_injective : Function.Injective f) :
    ImmersedSubmanifold I M where
  ModelSpace := E'
  instNormedAddCommGroupModelSpace := inferInstance
  instNormedSpaceModelSpace := inferInstance
  domain := N
  instTopologicalSpaceDomain := inferInstance
  instChartedSpaceDomain := inferInstance
  instIsManifoldDomain := inferInstance
  inclusion := f
  inclusion_injective := hf_injective
  inclusion_isImmersion := hf

end IsImmersion

end Manifold

/-! ### Definition_5_31_extra_2 (from Chap05/Sec05_31) -/
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

/-! ### Theorem_5_31 (from Chap05/Sec05_33) -/
open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uH'

section UniquenessOfSubmanifoldStructures

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J (⊤ : WithTop ℕ∞) S]
variable [IsEmbeddedSubmanifold I J S]

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the statement shape
-- was chosen from the local `IsEmbeddedSubmanifold` / `ImmersedSubmanifold` API in Chapter 5.
-- Proof sketch: use Corollary 5.30 to view the alternative inclusion as a smooth map
-- `S̃ → S`, check from injectivity of the ambient differential that this map is an immersion, and
-- then apply the global rank theorem to obtain a diffeomorphism.
/-- Theorem 5.31: if `S ⊆ M` already carries the canonical embedded-submanifold structure, then any
immersed submanifold structure on the same underlying subset is diffeomorphic to `S` through the
ambient inclusion map. Consequently the subspace topology and the smooth structure from Theorem
5.8 are unique among topology and smooth-structure choices making `S` an immersed submanifold. -/
theorem immersed_submanifold_structure_unique_of_same_carrier
    (T : Manifold.ImmersedSubmanifold I M) (hT : T.carrier = S) :
    ∃ Φ : T ≃ₘ⟮modelWithCornersSelf 𝕜 T.ModelSpace, J⟯ S,
      ∀ x : T, (Φ x : M) = T.inclusion x := sorry

end UniquenessOfSubmanifoldStructures
