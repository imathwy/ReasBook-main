import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Tactic.Recall
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_2_extra_1 (from Chap01/Sec01_02) -/
open scoped ContDiff Manifold

variable (n m : ℕ)
variable (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))
variable (V : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)))

/- Definition 1.2-extra-1 (core/canonical): smoothness for maps between open subsets of Euclidean
spaces is formalized by `ContDiffOn ℝ ∞` on the open domain. Since open subsets `U ⊆ ℝⁿ` and
`V ⊆ ℝᵐ` inherit the canonical manifold structures, the public owner for diffeomorphisms between
them is the diffeomorphism type on the open-subset types themselves, `U ≃ₘ⟮𝓡 n, 𝓡 m⟯ V`. Its
underlying topological data is recovered by the standard forgetful bridge
`Diffeomorph.toHomeomorph`. The auxiliary `PartialDiffeomorph` API belongs to
local-diffeomorphism internals, not to the public surface for diffeomorphisms between open
subsets. -/
#check (ContDiffOn ℝ ∞)
#check (U ≃ₘ⟮𝓡 n, 𝓡 m⟯ V)
recall Diffeomorph.toHomeomorph

/-! ### Definition_1_2_extra_2 (from Chap01/Sec01_02) -/
open scoped ContDiff Manifold

universe u𝕜 uE uH uM

namespace OpenPartialHomeomorph

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M]

variable (I : ModelWithCorners 𝕜 E H) (e e' : OpenPartialHomeomorph M H)

/- Definition 1.2-extra-2 (core/canonical): smooth compatibility of two charts is the canonical
owner condition that the chart change `e.symm ≫ₕ e'` belongs to the smooth structure groupoid. -/
#check (e.symm ≫ₕ e' ∈ contDiffGroupoid ∞ I)

/-- In Lee's source wording, if the chart domains are disjoint then the chart change has empty
source, so the textbook "disjoint or smooth" condition is equivalent to direct membership in the
smooth structure groupoid. This is the source-facing bridge from Lee's formulation to the
canonical owner condition. -/
theorem mem_contDiffGroupoid_of_source_inter_eq_empty
    (I : ModelWithCorners 𝕜 E H) {e e' : OpenPartialHomeomorph M H}
    (h : e.source ∩ e'.source = ∅) :
    e.symm ≫ₕ e' ∈ contDiffGroupoid ∞ I := by
  apply ContDiffGroupoid.mem_of_source_eq_empty
  rw [trans_source'']
  simp [h]

/-- In Lee's source wording, if the chart domains are disjoint then the chart change has empty
source, so the textbook "disjoint or smooth" condition is equivalent to direct membership in the
smooth structure groupoid. This is the source-facing bridge from Lee's formulation to the
canonical owner condition. -/
theorem source_inter_eq_empty_or_mem_contDiffGroupoid_iff
    (I : ModelWithCorners 𝕜 E H) (e e' : OpenPartialHomeomorph M H) :
    e.source ∩ e'.source = ∅ ∨ e.symm ≫ₕ e' ∈ contDiffGroupoid ∞ I ↔
      e.symm ≫ₕ e' ∈ contDiffGroupoid ∞ I := by
  constructor
  · rintro (h | h)
    · exact mem_contDiffGroupoid_of_source_inter_eq_empty I h
    · exact h
  · exact Or.inr

end OpenPartialHomeomorph

/-! ### Definition_1_extra_2 (from Chap01/Sec01) -/
universe u

section

variable {H : Type*} [PseudoMetricSpace H]
variable {n : ℕ} {M : Type u} [TopologicalSpace M]

/- Definition 1-extra-2: a coordinate chart on a topological `n`-manifold is an open partial
homeomorphism from `M` to `EuclideanSpace ℝ (Fin n)`. -/
#check OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))

namespace OpenPartialHomeomorph

/-- A chart has coordinate-ball image if its target is an open metric ball. -/
def IsCoordinateBall (e : OpenPartialHomeomorph M H) : Prop :=
  ∃ c : H, ∃ r : ℝ, 0 < r ∧ e.target = Metric.ball c r

/-- A chart with target equal to an open Euclidean ball is a coordinate ball. -/
-- Proof sketch: unfold `IsCoordinateBall` and use the specified center and radius.
theorem isCoordinateBall_of_target_eq_ball
    (e : OpenPartialHomeomorph M H) (c : H) (r : ℝ) (hr : 0 < r)
    (h : e.target = Metric.ball c r) : e.IsCoordinateBall :=
  ⟨c, r, hr, h⟩

variable (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))

/-- A chart is centered at `p` if `p` lies in its source and the chart sends `p` to `0`. -/
def IsCenteredAt (p : M) : Prop :=
  p ∈ e.source ∧ e p = 0

/-- A chart has coordinate-box image if its target is a product of open intervals. -/
def IsCoordinateBox : Prop :=
  ∃ a b : EuclideanSpace ℝ (Fin n),
    (∀ i, a i < b i) ∧ e.target = { x | ∀ i : Fin n, x i ∈ Set.Ioo (a i) (b i) }

/-- A chart with target equal to an open coordinate box is a coordinate box. -/
-- Proof sketch: unfold `IsCoordinateBox` and use the specified interval endpoints.
theorem isCoordinateBox_of_target_eq
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (a b : EuclideanSpace ℝ (Fin n))
    (hab : ∀ i, a i < b i)
    (h : e.target = { x | ∀ i : Fin n, x i ∈ Set.Ioo (a i) (b i) }) : e.IsCoordinateBox :=
  ⟨a, b, hab, h⟩

/-- Center a chart at a source point `p` by translating its coordinates so that `p` maps to `0`.
-/
def centerAt (p : e.source) : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
  e.transHomeomorph (Homeomorph.addRight (-e p))

@[simp] theorem centerAt_source (p : e.source) : (e.centerAt p).source = e.source :=
  rfl

/-- The centered chart at a source point `p` is centered at `p`. -/
theorem centerAt_isCenteredAt (p : e.source) : (e.centerAt p).IsCenteredAt p := by
  exact ⟨p.2, by simp [centerAt]⟩

end OpenPartialHomeomorph

/- A charted topological manifold provides the preferred chart `chartAt`, whose source contains
the chosen point by `mem_chart_source`. -/
#check chartAt (EuclideanSpace ℝ (Fin n))
#check mem_chart_source (EuclideanSpace ℝ (Fin n))

end

/-! ### Problem_1_2 (from Chap01/Sec01_07) -/
universe u

open Topology

/-- Problem 1-2 (1): every point of the disjoint union of copies of `ℝ` lies in the source of a
local chart to `ℝ`, so this disjoint union is locally Euclidean of dimension `1`. -/
-- Proof sketch: for `x = ⟨i, r⟩`, the inclusion
-- `Sigma.mk i : ℝ → Sigma fun j : ι ↦ ℝ` is an open embedding.
-- Its associated open partial homeomorphism has target the `i`-th summand, and the inverse chart
-- is therefore an `OpenPartialHomeomorph (Sigma fun j : ι ↦ ℝ) ℝ` whose source contains `x`.
theorem sigma_real_exists_open_homeomorph {ι : Type u} (x : Sigma fun _ : ι ↦ ℝ) :
    ∃ e : OpenPartialHomeomorph (Sigma fun _ : ι ↦ ℝ) ℝ, x ∈ e.source := by
  rcases x with ⟨i, r⟩
  let σ : ι → Type := fun _ : ι ↦ ℝ
  have hsigmaMk : Topology.IsOpenEmbedding (@Sigma.mk ι σ i) := Topology.IsOpenEmbedding.sigmaMk
  let e : OpenPartialHomeomorph (Sigma σ) ℝ :=
    (hsigmaMk.toOpenPartialHomeomorph (@Sigma.mk ι σ i)).symm
  have hx : @Sigma.mk ι σ i r ∈ e.source := by
    change @Sigma.mk ι σ i r ∈ (hsigmaMk.toOpenPartialHomeomorph (@Sigma.mk ι σ i)).target
    simpa using (Set.mem_range_self r : @Sigma.mk ι σ i r ∈ Set.range (@Sigma.mk ι σ i))
  refine ⟨by simpa [σ] using e, ?_⟩
  simpa [σ] using hx

/- Problem 1-2 (2): the disjoint union of copies of `ℝ` is Hausdorff. -/
recall Sigma.t2Space

/-- Problem 1-2 (3): if the index set is uncountable, then the disjoint union of copies of `ℝ` is
not second-countable. -/
-- Proof sketch: in a second-countable space, any family of pairwise disjoint nonempty open sets is
-- countable. The summand ranges `Set.range (Sigma.mk i)` form such a family in
-- `Sigma fun i : ι ↦ ℝ`, so an
-- uncountable index set contradicts second countability.
theorem sigma_real_not_secondCountableTopology {ι : Type u} [Uncountable ι] :
    ¬ SecondCountableTopology (Sigma fun _ : ι ↦ ℝ) := by
  intro hσ
  letI : SecondCountableTopology (Sigma fun _ : ι ↦ ℝ) := hσ
  let s : ι → Set (Sigma fun _ : ι ↦ ℝ) := fun i ↦ Set.range (Sigma.mk i)
  have hs : Pairwise fun i j ↦ Disjoint (s i) (s j) := fun i j hij ↦ by
    refine Set.disjoint_left.2 fun x hx hx' ↦ hij ?_
    rcases hx with ⟨y, rfl⟩
    rcases hx' with ⟨z, h⟩
    exact (congr_arg Sigma.fst h).symm
  have hcount : Countable ι :=
    hs.countable_of_isOpen_disjoint
      (fun _ ↦ isOpen_range_sigmaMk)
      (fun i ↦ ⟨⟨i, (0 : ℝ)⟩, Set.mem_range_self (0 : ℝ)⟩)
  exact Uncountable.not_countable hcount

/-! ### Theorem_1_2 (from Chap01/Sec01) -/
/- Theorem 1.2: a nonempty topological `n`-manifold cannot be homeomorphic to a topological
`m`-manifold unless `m = n`. This is exactly the canonical owner theorem
`TopologicalManifold.dimension_eq_of_homeomorph`. -/
recall TopologicalManifold.dimension_eq_of_homeomorph

/-! ### Definition_1_2_extra_3 (from Chap01/Sec01_02) -/
open scoped ContDiff Manifold
open ChartedSpace

universe u𝕜 uE uH uM

namespace OpenPartialHomeomorph

/-- Definition 1.2-extra-3 (source-facing): a smooth atlas on `M` is a collection of charts whose
domains cover `M`, with pairwise compatibility expressed through the canonical smooth structure
groupoid. By `Definition_1_2_extra_2`, this is equivalent to Lee's "disjoint or smooth transition
map" wording. -/
class IsSmoothAtlas {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    {M : Type uM} [TopologicalSpace M]
    (A : Set (OpenPartialHomeomorph M H)) : Prop where
  cover (x : M) : ∃ e ∈ A, x ∈ e.source
  compatible {e e' : OpenPartialHomeomorph M H} (he : e ∈ A) (he' : e' ∈ A) :
    e.symm ≫ₕ e' ∈ contDiffGroupoid ∞ I

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M]
variable {I : ModelWithCorners 𝕜 E H}

variable [ChartedSpace H M]

/-- For the charted-space atlas, being a smooth atlas is exactly the canonical smooth
compatibility condition `HasGroupoid`. -/
theorem isSmoothAtlas_atlas_iff :
    IsSmoothAtlas I (atlas H M) ↔ HasGroupoid M (contDiffGroupoid ∞ I) := by
  constructor
  · intro h
    exact ⟨fun he he' ↦ h.compatible he he'⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro x
      exact ⟨chartAt H x, chart_mem_atlas H x, mem_chart_source H x⟩
    · intro e e' he he'
      exact h.compatible he he'

/-- Any charted-space atlas compatible with the smooth structure groupoid is a smooth atlas. -/
instance [HasGroupoid M (contDiffGroupoid ∞ I)] :
    IsSmoothAtlas I (atlas H M) where
  cover x := ⟨chartAt H x, chart_mem_atlas H x, mem_chart_source H x⟩
  compatible he he' := HasGroupoid.compatible he he'

end OpenPartialHomeomorph

/-! ### Definition_1_2_extra_4 (from Chap01/Sec01_02) -/
/- Definition 1.2-extra-4: a complete or maximal smooth atlas is the maximal atlas attached to a
charted space and structure groupoid; its members are exactly the charts smoothly compatible with
every chart in the given atlas. This is the core owner abstraction; the manifold-specialized
bridge is `IsManifold.maximalAtlas`. -/
recall StructureGroupoid.maximalAtlas

/-! ### Definition_1_2_extra_5 (from Chap01/Sec01_02) -/
open scoped Manifold ContDiff

universe u𝕜 uE uH uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H}

/- Definition 1.2-extra-5: in mathlib, a smooth manifold modeled on `I` is expressed by the
typeclass `IsManifold I ∞ M`; the corresponding smooth structure is the maximal
smooth atlas `IsManifold.maximalAtlas I ∞ M`, so one usually suppresses the atlas from the
notation once it is fixed. -/
#check (IsManifold I ∞ M)

-- Proof sketch: unfold `IsManifold.maximalAtlas`; for regularity `∞` it is definitionally the
-- maximal atlas of the smooth structure groupoid `contDiffGroupoid ∞ I`.
/-- Definition 1.2-extra-5: a smooth manifold carries the maximal smooth atlas determined by its
smooth structure. -/
theorem smooth_manifold_smooth_structure [IsManifold I ∞ M] :
    IsManifold.maximalAtlas I ∞ M = (contDiffGroupoid ∞ I).maximalAtlas M := sorry

/-! ### Remark_1_2_extra_6 (from Chap01/Sec01_02) -/
/- Remark 1.2-extra-6: Mathlib’s canonical owner for the generalized manifold structures mentioned
here is `IsManifold I n M`, where the regularity parameter `n : ℕ∞ω` specializes to topological
manifolds when `n = 0`, to `C^k` manifolds for finite `k`, to smooth manifolds when `n = ∞`,
and to real-analytic (`C^ω`) manifolds when `n = ω`; over complex model spaces (`𝕜 = ℂ`), the
same notion is used for complex-analytic manifold structures. -/
recall IsManifold
