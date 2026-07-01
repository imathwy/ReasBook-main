import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
