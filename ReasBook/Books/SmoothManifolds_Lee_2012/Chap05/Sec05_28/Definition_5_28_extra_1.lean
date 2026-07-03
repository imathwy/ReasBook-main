import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.SmoothEmbedding
import SmoothManifoldsLee.Chap05.Sec05_31.Definition_5_31_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold

universe u𝕜 uE uH uM uE' uH'

section EmbeddedSubmanifolds

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I (⊤ : ℕ∞ω) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable (J : ModelWithCorners 𝕜 E' H') (S : Set M)
variable [ChartedSpace H' S] [IsManifold J (⊤ : ℕ∞ω) S]

/-- Definition 5.28-extra-1: A subset `S ⊆ M` is an embedded submanifold if the subtype `S`
inherits its subspace topology, carries a boundaryless smooth manifold structure, and the inclusion
`S ↪ M` is a smooth embedding. Some authors call this a regular submanifold. -/
class IsEmbeddedSubmanifold : Prop extends BoundarylessManifold J S where
  /-- The subtype inclusion of the embedded submanifold into the ambient manifold is smooth. -/
  isSmoothEmbedding_subtype_val :
    IsSmoothEmbedding J I (⊤ : ℕ∞ω) (Subtype.val : S → M)

/-- The empty subset is an embedded submanifold for any chosen smooth manifold structure on the
empty subtype. This captures the textbook convention that the empty set has every dimension. -/
instance isEmbeddedSubmanifold_empty [ChartedSpace H' (∅ : Set M)]
    [IsManifold J (⊤ : ℕ∞ω) (∅ : Set M)] :
    IsEmbeddedSubmanifold I J (∅ : Set M) where
  toBoundarylessManifold := by
    refine ⟨fun x ↦ False.elim x.2⟩
  isSmoothEmbedding_subtype_val := by
    refine ⟨?_, ⟨Topology.IsInducing.subtypeVal, Subtype.val_injective⟩⟩
    exact ⟨PUnit, inferInstance, inferInstance, fun x ↦ False.elim x.2⟩

end EmbeddedSubmanifolds

section EmbeddedToImmersedBridge

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I (⊤ : ℕ∞ω) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable (S : Set M)
variable [ChartedSpace E' S] [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : ℕ∞ω) S]

namespace IsEmbeddedSubmanifold

/-- Bridge/view: when the embedded submanifold structure is already modeled on the boundaryless
vector-space model, its subtype inclusion canonically defines the chapter's core
`ImmersedSubmanifold` owner. -/
abbrev toImmersedSubmanifold
    (hS : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') S) :
    Manifold.ImmersedSubmanifold I M :=
  hS.isSmoothEmbedding_subtype_val.toImmersedSubmanifold

end IsEmbeddedSubmanifold

end EmbeddedToImmersedBridge

section EmbeddedSubmanifoldCodimension

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I (⊤ : ℕ∞ω) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable (J : ModelWithCorners 𝕜 E' H') (S : Set M)
variable [ChartedSpace H' S] [IsManifold J (⊤ : ℕ∞ω) S]

namespace IsEmbeddedSubmanifold

omit [IsManifold I (⊤ : ℕ∞ω) M] [IsManifold J (⊤ : ℕ∞ω) S] in
/-- The codimension of an embedded submanifold is the ambient dimension minus the dimension of its
boundaryless manifold structure. -/
noncomputable def codimension (_ : IsEmbeddedSubmanifold I J S)
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] : ℕ :=
  Module.finrank 𝕜 E - Module.finrank 𝕜 E'

omit [IsManifold I (⊤ : ℕ∞ω) M] [IsManifold J (⊤ : ℕ∞ω) S] in
/-- The codimension is computed as the difference of the model-space dimensions. -/
lemma codimension_eq_finrank_sub (hS : IsEmbeddedSubmanifold I J S)
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] :
    hS.codimension = Module.finrank 𝕜 E - Module.finrank 𝕜 E' := rfl
attribute [simp] codimension_eq_finrank_sub

omit [IsManifold I (⊤ : ℕ∞ω) M] [IsManifold J (⊤ : ℕ∞ω) S] in
/-- An embedded hypersurface is an embedded submanifold of codimension `1`. -/
def IsHypersurface (hS : IsEmbeddedSubmanifold I J S) [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 E'] : Prop :=
  hS.codimension = 1

omit [IsManifold I (⊤ : ℕ∞ω) M] [IsManifold J (⊤ : ℕ∞ω) S] in
/-- An embedded submanifold is a hypersurface exactly when its codimension is `1`. -/
lemma isHypersurface_iff (hS : IsEmbeddedSubmanifold I J S)
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] :
    hS.IsHypersurface ↔ hS.codimension = 1 := Iff.rfl

end IsEmbeddedSubmanifold

end EmbeddedSubmanifoldCodimension

section EmbeddedToImmersedCodimension

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I (⊤ : ℕ∞ω) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable (S : Set M)
variable [ChartedSpace E' S] [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : ℕ∞ω) S]

namespace IsEmbeddedSubmanifold

instance instFiniteDimensionalToImmersedSubmanifoldModelSpace
    (hS : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') S)
    [FiniteDimensional 𝕜 E'] :
    FiniteDimensional 𝕜 hS.toImmersedSubmanifold.ModelSpace := by
  simpa [toImmersedSubmanifold, Manifold.IsSmoothEmbedding.toImmersedSubmanifold] using
    (inferInstance : FiniteDimensional 𝕜 E')

omit [IsManifold I (⊤ : ℕ∞ω) M] in
/-- In the self-model case, the source-facing codimension agrees definitionally with the core
immersed-submanifold codimension. -/
@[simp] lemma toImmersedSubmanifold_codimension
    (hS : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') S)
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] :
    hS.toImmersedSubmanifold.codimension = hS.codimension := rfl

end IsEmbeddedSubmanifold

end EmbeddedToImmersedCodimension
