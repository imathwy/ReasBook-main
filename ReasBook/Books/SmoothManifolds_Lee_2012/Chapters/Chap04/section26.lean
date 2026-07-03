import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.Covering.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_26_extra_1 (from Chap04/Sec04_26) -/
open scoped Manifold ContDiff

universe u𝕜 uE uE' uH uH' uM uM'

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {M' : Type uM'} [TopologicalSpace M'] [ChartedSpace H' M']

namespace Manifold

/-- Definition 4.26-extra-1: A smooth covering map between smooth manifolds is a surjective
topological covering map that is also a smooth local diffeomorphism. This packages Lee's
requirement that every sheet over an evenly covered neighborhood be mapped diffeomorphically onto
the base neighborhood. -/
def IsSmoothCoveringMap
    (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') (π : M → M') : Prop :=
  IsCoveringMap π ∧ Function.Surjective π ∧ IsLocalDiffeomorph I I' ∞ π

namespace IsSmoothCoveringMap

theorem surjective {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsSmoothCoveringMap I I' π) : Function.Surjective π :=
  hπ.2.1

theorem isCoveringMap {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsSmoothCoveringMap I I' π) : IsCoveringMap π :=
  hπ.1

theorem isLocalDiffeomorph
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsSmoothCoveringMap I I' π) : IsLocalDiffeomorph I I' ∞ π :=
  hπ.2.2

end IsSmoothCoveringMap

/-- Helper for Definition 4.26-extra-1: the source of the global trivialization for the identity
map is all of `M`. -/
theorem id_covering_trivialization_source_eq :
    ((Homeomorph.prodPUnit M).symm.toOpenPartialHomeomorph).source =
      (id : M → M) ⁻¹' (Set.univ : Set M) := by
  -- Both the partial homeomorphism source and the preimage of `univ` are all of `M`.
  ext x
  simp

/-- Helper for Definition 4.26-extra-1: the target of the global trivialization for the identity
map is the full product `M × PUnit`. -/
theorem id_covering_trivialization_target_eq :
    ((Homeomorph.prodPUnit M).symm.toOpenPartialHomeomorph).target =
      (Set.univ : Set M) ×ˢ (Set.univ : Set PUnit.{1}) := by
  -- The homeomorphism to `M × PUnit` is global, so its target is all of the product.
  ext x
  simp

/-- Helper for Definition 4.26-extra-1: the global trivialization for `id` projects back to the
identity on the base. -/
theorem id_covering_trivialization_proj_toFun
    (x : M) (_hx : x ∈ ((Homeomorph.prodPUnit M).symm.toOpenPartialHomeomorph).source) :
    (((Homeomorph.prodPUnit M).symm.toOpenPartialHomeomorph x).1) = (id : M → M) x := by
  -- The first coordinate of `(x, ())` is exactly `x`.
  change (((Equiv.prodPUnit M).symm x).1) = x
  simp [Equiv.prodPUnit_symm_apply]

/-- Helper for Definition 4.26-extra-1: the identity map has a global one-sheet trivialization. -/
noncomputable def id_covering_trivialization : Bundle.Trivialization PUnit.{1} (id : M → M) :=
  { toOpenPartialHomeomorph := (Homeomorph.prodPUnit M).symm.toOpenPartialHomeomorph
    baseSet := Set.univ
    open_baseSet := isOpen_univ
    source_eq := id_covering_trivialization_source_eq
    target_eq := id_covering_trivialization_target_eq
    proj_toFun := id_covering_trivialization_proj_toFun }

/-- Helper for Definition 4.26-extra-1: the identity map is a topological covering map. -/
theorem id_isCoveringMap : IsCoveringMap (id : M → M) := by
  -- The identity map is the globally trivial one-sheet cover.
  refine IsCoveringMap.mk (f := (id : M → M)) (fun _ : M ↦ PUnit.{1})
    (fun _ ↦ id_covering_trivialization) ?_
  -- Every point lies in the global base set `univ`.
  intro x
  simp [id_covering_trivialization]

/-- Helper for Definition 4.26-extra-1: the identity diffeomorphism is a local diffeomorphism. -/
theorem refl_isLocalDiffeomorph_id (I : ModelWithCorners 𝕜 E H) :
    IsLocalDiffeomorph I I ∞ (id : M → M) := by
  -- The identity diffeomorphism supplies the local inverse data at every point.
  simpa using (Diffeomorph.refl I M ∞).isLocalDiffeomorph

/-- The identity map is a smooth covering map. -/
-- Proof sketch: combine the identity map's surjectivity, the covering-map structure coming from
-- the identity homeomorphism, and the local diffeomorphism structure from `Diffeomorph.refl`.
theorem isSmoothCoveringMap_id (I : ModelWithCorners 𝕜 E H) :
    IsSmoothCoveringMap I I (id : M → M) := by
  -- Package the topological covering, surjectivity, and local diffeomorphism data.
  refine ⟨id_isCoveringMap, Function.surjective_id, refl_isLocalDiffeomorph_id I⟩

/-- A universal smooth covering map is a smooth covering map whose total space is simply
connected. -/
def IsUniversalSmoothCoveringMap
    (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') (π : M → M') : Prop :=
  IsSmoothCoveringMap I I' π ∧ SimplyConnectedSpace M

namespace IsUniversalSmoothCoveringMap

theorem isSmoothCoveringMap
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsUniversalSmoothCoveringMap I I' π) : IsSmoothCoveringMap I I' π :=
  hπ.1

theorem simplyConnectedSpace
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsUniversalSmoothCoveringMap I I' π) : SimplyConnectedSpace M :=
  hπ.2

end IsUniversalSmoothCoveringMap

/-- On a simply connected manifold, the identity map is a universal smooth covering map. -/
-- Proof sketch: use `isSmoothCoveringMap_id` for the covering-map part and the ambient
-- `SimplyConnectedSpace M` instance for the universal-cover condition.
theorem isUniversalSmoothCoveringMap_id (I : ModelWithCorners 𝕜 E H) [SimplyConnectedSpace M] :
    IsUniversalSmoothCoveringMap I I (id : M → M) := by
  -- Pair the identity covering map with the ambient simple connectivity assumption.
  exact ⟨isSmoothCoveringMap_id I, inferInstance⟩

end Manifold

/-! ### Theorem_4_26 (from Chap04/Sec04_25) -/
-- Semantic search tool unavailable in this environment; local precedents used:
-- `Manifold.is_smooth_submersion_iff_forall_surjective_mfderiv` from
-- `Definition_4_21_extra_1` and `Manifold.IsSmoothSubmersion` from `Proposition_4_28`.

open scoped ContDiff Manifold

namespace Manifold

section

universe uK uE uE' uH uH' uM uN

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H}
variable {J : ModelWithCorners 𝕜 E' H'}

/-- A smooth local section of `π : M → N` over an open subset `U ⊆ N` is a smooth map
`σ : U → M` whose composite with `π` is the identity on `U`. -/
def IsSmoothLocalSection (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    (π : M → N) (U : TopologicalSpace.Opens N) (σ : U → M) : Prop :=
  ContMDiff J I ∞ σ ∧ ∀ x : U, π (σ x) = x

namespace IsSmoothLocalSection

-- Proof sketch: evaluate the defining right-inverse equation in
-- `Manifold.IsSmoothLocalSection` at the chosen point of the open subset.
/-- A smooth local section satisfies the section equation at each point of its domain. -/
theorem apply_eq {π : M → N} {U : TopologicalSpace.Opens N} {σ : U → M}
    (hσ : IsSmoothLocalSection I J π U σ) (x : U) :
    π (σ x) = x := sorry

end IsSmoothLocalSection

end

section

universe uE uE' uH uH' uM uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]

-- Proof sketch: for the forward implication, apply the rank theorem in local coordinates to write
-- `π` near each `p` as a coordinate projection and take the coordinate inclusion as a smooth local
-- section through `p`. For the reverse implication, differentiate the identity `π ∘ σ = id` at
-- `q = π p`; then `mfderiv I J π p ∘ mfderiv J I σ q = ContinuousLinearMap.id ℝ _`, so
-- `mfderiv I J π p` is surjective.
/-- Theorem 4.26 (Local Section Theorem): a smooth map between finite-dimensional smooth manifolds
is a smooth submersion exactly when each point of the source lies on a smooth local section
through its image. -/
theorem smooth_submersion_iff_exists_smooth_local_section_through_every_point {π : M → N}
    (hπ : ContMDiff I J ∞ π) :
    (∀ p : M, Function.Surjective (mfderiv I J π p)) ↔
      ∀ p : M, ∃ U : TopologicalSpace.Opens N, ∃ hq : π p ∈ U, ∃ σ : U → M,
        IsSmoothLocalSection I J π U σ ∧ σ ⟨π p, hq⟩ = p := sorry

end

end Manifold
