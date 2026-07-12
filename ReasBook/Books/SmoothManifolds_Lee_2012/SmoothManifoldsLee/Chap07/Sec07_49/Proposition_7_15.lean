import Mathlib.Topology.Algebra.OpenSubgroup
import SmoothManifolds_Lee_2012.Chap07.Sec07_46.Definition_7_46_extra_3

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` identified `Subgroup.connectedComponentOfOne` as the
-- canonical owner of the identity component. The diffeomorphism clause is packaged below through
-- the source-facing left-translation map from Definition 7.46-extra-3.

open scoped LieGroup Manifold ContDiff

universe u𝕜 uE uH uG

section LieGroupIdentityComponent

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H] [LocallyConnectedSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [IsTopologicalGroup G] [LieGroup I ∞ G]

/-- Helper for Proposition 7.15: conjugation preserves the identity component of a Lie group. -/
lemma identityComponentConjMem {g x : G} (hx : x ∈ connectedComponent (1 : G)) :
    g * x * g⁻¹ ∈ connectedComponent (1 : G) := sorry

/-- The identity component `Subgroup.connectedComponentOfOne G` of a Lie group is normal. -/
instance identityComponent_normal : (Subgroup.connectedComponentOfOne G).Normal := sorry

/-- Helper: the carrier of `Subgroup.connectedComponentOfOne G` is connected. -/
theorem identityComponent_isConnected :
    IsConnected ((Subgroup.connectedComponentOfOne G : Set G)) := sorry

/-- The identity component `Subgroup.connectedComponentOfOne G` of a Lie group is open. -/
theorem identityComponent_isOpen :
    IsOpen ((Subgroup.connectedComponentOfOne G : Set G)) := sorry

/-- A connected open subgroup of a Lie group is its identity component. -/
theorem connected_openSubgroup_eq_identityComponent (K : OpenSubgroup G)
    (hK_connected : IsConnected (K : Set G)) :
    K.toSubgroup = Subgroup.connectedComponentOfOne G := sorry

section ConnectedComponentDiffeomorph

/-- Helper: each connected component of a Lie group is open. -/
theorem connectedComponent_isOpen (g : G) :
    IsOpen (connectedComponent g : Set G) := sorry

/-- Proposition 7.15. Let `G` be a Lie group and let `G₀` be its identity component. Then `G₀`
is a normal subgroup of `G`, `G₀` is the only connected open subgroup of `G`, and every connected
component of `G` is diffeomorphic to `G₀`. The preceding declarations record the normality,
openness, and uniqueness clauses; this theorem records the diffeomorphism clause. -/
theorem connectedComponent_diffeomorph_identityComponent (g : G) :
    let Cg : TopologicalSpace.Opens G := ⟨connectedComponent g,
      connectedComponent_isOpen g⟩
    let G₀ : TopologicalSpace.Opens G := ⟨(Subgroup.connectedComponentOfOne G : Set G),
      identityComponent_isOpen⟩
    Nonempty (Cg ≃ₘ⟮I, I⟯ G₀) := sorry

/-- Helper: the connected component of `g` is the image of the identity component under left
translation by `g`. -/
theorem connectedComponent_eq_leftTranslation_image_identityComponent (g : G) :
    connectedComponent g = 𝑳 I g '' (connectedComponent (1 : G) : Set G) := sorry

end ConnectedComponentDiffeomorph

end LieGroupIdentityComponent
