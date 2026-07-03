import Mathlib
import cartan.VI.section25.«0008_Proposition_4_I»
import cartan.VI.section26.«0002_Definition_VI_5_extra_2»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold
open Set

-- Domain sampling: the primary domain here is analytic continuation on one-dimensional complex
-- manifolds over `ℂ`. The relevant owner declarations inspected before this refinement were:
-- * the chapter-local source-facing owner `ConnectedHausdorffUnramifiedSurfaceOver ℂ` from
--   `0002_Definition_VI_5_extra_2.lean`;
-- * its inherited manifold API `ConnectedHausdorffUnramifiedSurfaceOver.mdifferentiable_projection`
--   in `0002`, which places projection maps directly in the canonical holomorphic interface;
-- * the section-26 use of `MDifferentiable`, which is the owner for holomorphic maps between the
--   resulting Riemann-surface charts.
-- The best owner abstraction for this item is the source-facing extension object
-- `PlaneHolomorphicExtension U f`. Primitive data in the extension problem is the connected
-- Hausdorff unramified surface over `ℂ`, the embedding of `U`, and the extended holomorphic
-- function. Compatibility of continuation maps and maximality are derived API: they are
-- properties of an existing extension object, not additional primitive data that should be packed
-- into a second wrapper owner.

namespace ConnectedHausdorffUnramifiedSurfaceOver

/-- A morphism of connected Hausdorff unramified surfaces over `ℂ` is a holomorphic map commuting
with the projections to `ℂ`. -/
structure Hom (X Y : ConnectedHausdorffUnramifiedSurfaceOver ℂ) where
  toFun : X → Y
  holomorphic_toFun : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) toFun
  commutes (x : X) : Y.projection (toFun x) = X.projection x

instance {X Y : ConnectedHausdorffUnramifiedSurfaceOver ℂ} :
    CoeFun (Hom X Y) (fun _ ↦ X → Y) where
  coe h := h.toFun

end ConnectedHausdorffUnramifiedSurfaceOver

/-- A holomorphic extension of `f` from the open set `U ⊆ ℂ` to a connected Hausdorff unramified
surface over `ℂ`. -/
structure PlaneHolomorphicExtension (U : Set ℂ) (f : ℂ → ℂ) where
  surface : ConnectedHausdorffUnramifiedSurfaceOver ℂ
  embedding : U → surface
  isOpenEmbedding_embedding : Topology.IsOpenEmbedding embedding
  projection_comp_embedding (z : U) : surface.projection (embedding z) = z
  extension : surface → ℂ
  holomorphic_extension : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) extension
  extension_comp_embedding (z : U) : extension (embedding z) = f z

namespace PlaneHolomorphicExtension

open ConnectedHausdorffUnramifiedSurfaceOver

variable {U : Set ℂ} {f : ℂ → ℂ}

/-- A comparison morphism between two holomorphic extensions of the same germ is a surface map
that preserves both the distinguished embedding of `U` and the extended holomorphic value. -/
def Compatible (E₁ E₂ : PlaneHolomorphicExtension U f) (h : Hom E₁.surface E₂.surface) : Prop :=
  (∀ z : U, h (E₁.embedding z) = E₂.embedding z) ∧
    ∀ x : E₁.surface, E₂.extension (h x) = E₁.extension x

/-- A holomorphic extension is maximal when every other extension of the same germ admits a unique
comparison morphism into it. -/
def IsMaximal (E : PlaneHolomorphicExtension U f) : Prop :=
  ∀ E' : PlaneHolomorphicExtension U f,
    ∃! h : Hom E'.surface E.surface, Compatible E' E h

end PlaneHolomorphicExtension

/-- Helper for Problem VI.5-extra-8: the original open set `U` is itself an unramified surface
over `ℂ` via the inclusion map. -/
noncomputable def tautological_surface
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U] :
    ConnectedHausdorffUnramifiedSurfaceOver ℂ :=
  ConnectedHausdorffUnramifiedSurfaceOver.ofIsLocalHomeomorph
    (Subtype.val : U → ℂ) hU_open.isOpenEmbedding_subtypeVal.isLocalHomeomorph

/-- Helper for Problem VI.5-extra-8: every point of the tautological surface projects back into
the original open set `U`. -/
lemma tautological_surface_projection_eq
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U]
    (z : tautological_surface hU_open) :
    (tautological_surface hU_open).projection z = z.1 := by
  rfl

/-- Helper for Problem VI.5-extra-8: every point of the tautological surface projects back into
the original open set `U`. -/
lemma tautological_surface_projection_mem
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U]
    (z : tautological_surface hU_open) :
    (tautological_surface hU_open).projection z ∈ U := by
  -- The tautological projection is just the subtype value map.
  rw [tautological_surface_projection_eq hU_open z]
  exact z.2

/-- Helper for Problem VI.5-extra-8: the pullback of `f` along the tautological projection is
holomorphic on the tautological surface. -/
lemma subtype_extension_mdifferentiable
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U]
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : tautological_surface hU_open ↦ f ((tautological_surface hU_open).projection z)) := by
  let X := tautological_surface hU_open
  -- First record the ambient holomorphicity of `f` on the open set `U`.
  have hf_on : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f U := hf.mdifferentiableOn
  have hproj : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) X.projection :=
    ConnectedHausdorffUnramifiedSurfaceOver.mdifferentiable_projection X
  -- Then compose with the tautological projection, whose image is contained in `U`.
  have hcomp : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (f ∘ X.projection) Set.univ :=
    hf_on.comp hproj.mdifferentiableOn (by
      intro z _hz
      simpa [X] using tautological_surface_projection_mem hU_open z)
  simpa [X, Function.comp] using (mdifferentiableOn_univ.mp hcomp)

/-- Helper for Problem VI.5-extra-8: the tautological embedding into the tautological surface
commutes with the projection to `ℂ`. -/
lemma tautological_surface_projection_comp_embedding
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U]
    (z : U) :
    (tautological_surface hU_open).projection z = z := by
  simpa using tautological_surface_projection_eq hU_open z

/-- Helper for Problem VI.5-extra-8: the tautological extension agrees with `f` on the embedded
copy of `U`. -/
lemma tautological_extension_comp_embedding
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U]
    {f : ℂ → ℂ} (z : U) :
    (fun x : tautological_surface hU_open ↦ f ((tautological_surface hU_open).projection x)) z = f z := by
  -- On the tautological surface the projection is the subtype inclusion.
  simpa using congrArg f (tautological_surface_projection_comp_embedding hU_open z)

/-- Helper for Problem VI.5-extra-8: the given germ on `U` already determines a base
holomorphic extension object. -/
noncomputable def tautological_extension
    {U : Set ℂ} (hU_open : IsOpen U) [ConnectedSpace U]
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) : PlaneHolomorphicExtension U f where
  surface := tautological_surface hU_open
  embedding := fun z ↦ z
  isOpenEmbedding_embedding := Topology.IsOpenEmbedding.id
  projection_comp_embedding := tautological_surface_projection_comp_embedding hU_open
  extension := fun z ↦ f ((tautological_surface hU_open).projection z)
  holomorphic_extension := subtype_extension_mdifferentiable hU_open hf
  extension_comp_embedding := tautological_extension_comp_embedding hU_open

/-- Helper for Problem VI.5-extra-8: the hypotheses already give a nonempty family of
holomorphic extensions, namely the tautological one on `U` itself. -/
theorem plane_holomorphic_extension_nonempty
    {U : Set ℂ} (hU_open : IsOpen U) (hU_nonempty : U.Nonempty)
    (hU_connected : IsPreconnected U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    Nonempty (PlaneHolomorphicExtension U f) := by
  letI : ConnectedSpace U := Subtype.connectedSpace ⟨hU_nonempty, hU_connected⟩
  -- The open subtype carries the initial extension object before any maximal quotient is formed.
  exact ⟨tautological_extension hU_open hf⟩

/-- Helper for Problem VI.5-extra-8: a continuation representative is a point on some
holomorphic extension of the original germ. -/
abbrev ContinuationRepresentative (U : Set ℂ) (f : ℂ → ℂ) :=
  Σ E : PlaneHolomorphicExtension U f, E.surface

/-- Helper for Problem VI.5-extra-8: the chosen local inverse branch around a continuation
representative has an open source in `ℂ`. -/
lemma continuation_chart_isOpen
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    IsOpen ((r.1.surface.isLocalHomeomorph.localInverseAt r.2).source) :=
  (r.1.surface.isLocalHomeomorph.localInverseAt r.2).open_source

/-- Helper for Problem VI.5-extra-8: the local projection chart attached to a continuation
representative. -/
noncomputable def continuation_chart
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    TopologicalSpace.Opens ℂ :=
  ⟨(r.1.surface.isLocalHomeomorph.localInverseAt r.2).source, continuation_chart_isOpen r⟩

/-- Helper for Problem VI.5-extra-8: the local branch of the extended holomorphic function
obtained by pulling back along the chosen local inverse branch. -/
noncomputable def continuation_branch
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_chart r → ℂ :=
  fun z ↦ r.1.extension ((r.1.surface.isLocalHomeomorph.localInverseAt r.2) z)

/-- Helper for Problem VI.5-extra-8: the projection of a continuation representative lies in its
chosen local chart source. -/
lemma continuation_projection_mem_chart
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    r.1.surface.projection r.2 ∈ continuation_chart r := by
  -- The local inverse chart is built precisely so that the base projection of the center point
  -- lies in its source.
  simpa [continuation_chart] using
    (r.1.surface.isLocalHomeomorph.apply_self_mem_localInverseAt_source (x := r.2))

/-- Helper for Problem VI.5-extra-8: on the local continuation chart, the chosen inverse branch
is a right inverse to the projection. -/
lemma continuation_projection_localInverse
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f)
    (z : continuation_chart r) :
    r.1.surface.projection ((r.1.surface.isLocalHomeomorph.localInverseAt r.2) z) = (z : ℂ) := by
  -- This is the defining right-inverse identity of `localInverseAt` on its source.
  simpa using
    (r.1.surface.isLocalHomeomorph.apply_localInverseAt_of_mem (x := r.2) z.2)

/-- Helper for Problem VI.5-extra-8: the pulled-back local branch recovers the original extension
value at the base point of the representative. -/
lemma continuation_branch_at_projection
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_branch r
        ⟨r.1.surface.projection r.2, continuation_projection_mem_chart r⟩ =
      r.1.extension r.2 := by
  -- Evaluating the local branch at the center projection returns the original point of the
  -- extension via `localInverseAt_apply_self`.
  simpa [continuation_branch] using
    congrArg r.1.extension
      (r.1.surface.isLocalHomeomorph.localInverseAt_apply_self (x := r.2))

/-- Helper for Problem VI.5-extra-8: the common chart used to compare two continuation
representatives is the intersection of their local continuation charts. -/
noncomputable def continuation_common_chart
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    TopologicalSpace.Opens ℂ :=
  continuation_chart r ⊓ continuation_chart s

/-- Helper for Problem VI.5-extra-8: the left continuation branch restricted to the common chart
of two representatives. -/
noncomputable def continuation_left_branch
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    continuation_common_chart r s → ℂ :=
  fun z ↦ continuation_branch r ⟨z.1, z.2.1⟩

/-- Helper for Problem VI.5-extra-8: the right continuation branch restricted to the common chart
of two representatives. -/
noncomputable def continuation_right_branch
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    continuation_common_chart r s → ℂ :=
  fun z ↦ continuation_branch s ⟨z.1, z.2.2⟩

/-- Helper for Problem VI.5-extra-8: the overlap relation is the local coincidence locus of the
two restricted branches on a fixed common chart subtype. -/
def continuation_branch_overlap
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    Set (continuation_common_chart r s) :=
  {z | continuation_left_branch r s =ᶠ[nhds z] continuation_right_branch r s}

/-- Helper for Problem VI.5-extra-8: branch coincidence is an open condition on the common chart.
-/
lemma continuation_branch_overlap_isOpen
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    IsOpen (continuation_branch_overlap r s) := by
  -- On the fixed common-chart domain, the overlap predicate is exactly the local coincidence
  -- locus handled by Proposition 4.I (1).
  simpa [continuation_branch_overlap] using
    (local_coincidence_set_isOpen
      (f := continuation_left_branch r s) (g := continuation_right_branch r s))

/-- Helper for Problem VI.5-extra-8: identical representatives have identical restricted branches
on their common chart. -/
lemma continuation_left_right_self_eq
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_left_branch r r = continuation_right_branch r r := by
  rfl

/-- Helper for Problem VI.5-extra-8: every point of the self-overlap chart lies in the overlap
locus. This is the `V_id` input for the future gluing data. -/
lemma continuation_branch_overlap_self
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_branch_overlap r r = Set.univ := by
  ext z
  constructor
  · intro _hz
    simp
  · intro _hz
    -- The two restricted branches are definitionally the same when the representative is fixed.
    simpa [continuation_branch_overlap, continuation_left_right_self_eq r]
      using (Filter.EventuallyEq.rfl : continuation_left_branch r r =ᶠ[nhds z]
        continuation_left_branch r r)

/-- Helper for Problem VI.5-extra-8: a point in the overlap locus is in particular a pointwise
coincidence point of the two restricted branches. -/
lemma continuation_branch_eq_of_mem_overlap
    {U : Set ℂ} {f : ℂ → ℂ} {r s : ContinuationRepresentative U f}
    {z : continuation_common_chart r s} (hz : z ∈ continuation_branch_overlap r s) :
    continuation_left_branch r s z = continuation_right_branch r s z := by
  -- Specializing an eventual equality to the center point recovers ordinary equality.
  have hz' : continuation_left_branch r s =ᶠ[nhds z] continuation_right_branch r s := by
    simpa [continuation_branch_overlap] using hz
  exact hz'.eq_of_nhds

/-- Helper for Problem VI.5-extra-8: the local inverse branch attached to a continuation
representative is itself a holomorphic open partial homeomorphism. -/
lemma continuation_localInverseAt_mdifferentiable
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    (r.1.surface.isLocalHomeomorph.localInverseAt r.2).MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := by
  -- Route correction: rather than proving holomorphicity of the common-chart branch directly, we
  -- first identify the raw inverse branch with the inverse preferred chart at `r.2`.
  have hchart :
      chartAt ℂ r.2 = (r.1.surface.isLocalHomeomorph.localInverseAt r.2).symm := by
    change
      (r.1.surface.isLocalHomeomorph.localInverseAt r.2).symm.trans
          (chartAt ℂ (r.1.surface.projection r.2)) =
        (r.1.surface.isLocalHomeomorph.localInverseAt r.2).symm
    simpa
  simpa [hchart] using (mdifferentiable_chart (I := 𝓘(ℂ)) (x := r.2)).symm

/-- Helper for Problem VI.5-extra-8: restricting the raw inverse branch to its open chart source
gives a holomorphic map from the chart subtype into the continuation surface. -/
lemma continuation_local_inverse_mdifferentiable
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun z : continuation_chart r ↦
        (r.1.surface.isLocalHomeomorph.localInverseAt r.2) z) := by
  have hsub :
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : continuation_chart r → ℂ) :=
    (contMDiff_subtype_val (I := 𝓘(ℂ)) (n := 1)).mdifferentiable one_ne_zero
  -- Compose the ambient inverse branch with the subtype inclusion of its source.
  have hcomp :
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
        ((r.1.surface.isLocalHomeomorph.localInverseAt r.2) ∘
          (Subtype.val : continuation_chart r → ℂ)) Set.univ :=
    (continuation_localInverseAt_mdifferentiable r).1.comp hsub.mdifferentiableOn
      (by intro z hz; exact z.2)
  exact (mdifferentiableOn_univ.mp <| by simpa [Function.comp] using hcomp)

/-- Helper for Problem VI.5-extra-8: the pulled-back continuation branch on one local chart is
holomorphic because it is the extension composed with the raw local inverse branch. -/
lemma continuation_branch_mdifferentiable
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (continuation_branch r) := by
  -- The extension is holomorphic on the surface, and the raw inverse branch is holomorphic on the
  -- chart source.
  simpa [continuation_branch, Function.comp] using
    r.1.holomorphic_extension.comp (continuation_local_inverse_mdifferentiable r)

/-- Helper for Problem VI.5-extra-8: both restricted continuation branches on the common chart
remain holomorphic after restricting along the subtype inclusions. -/
lemma continuation_common_branch_mdifferentiable
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (continuation_left_branch r s) ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (continuation_right_branch r s) := by
  have hleft_inc :
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (TopologicalSpace.Opens.inclusion
          (show continuation_common_chart r s ≤ continuation_chart r from inf_le_left)) :=
    (contMDiff_inclusion (I := 𝓘(ℂ)) (n := 1)
      (show continuation_common_chart r s ≤ continuation_chart r from inf_le_left)).mdifferentiable
      one_ne_zero
  have hright_inc :
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (TopologicalSpace.Opens.inclusion
          (show continuation_common_chart r s ≤ continuation_chart s from inf_le_right)) :=
    (contMDiff_inclusion (I := 𝓘(ℂ)) (n := 1)
      (show continuation_common_chart r s ≤ continuation_chart s from inf_le_right)).mdifferentiable
      one_ne_zero
  constructor
  · -- The left branch is the local chart branch precomposed with the left inclusion.
    simpa [continuation_left_branch, continuation_branch, Function.comp]
      using (continuation_branch_mdifferentiable r).comp hleft_inc
  · -- The right branch is the symmetric restriction along the right inclusion.
    simpa [continuation_right_branch, continuation_branch, Function.comp]
      using (continuation_branch_mdifferentiable s).comp hright_inc

/-- Helper for Problem VI.5-extra-8: the branch-overlap locus is closed because the two
restricted holomorphic branches into `ℂ` have a closed local coincidence set. -/
lemma continuation_branch_overlap_isClosed
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    IsClosed (continuation_branch_overlap r s) := by
  let hbranches := continuation_common_branch_mdifferentiable r s
  -- Proposition 4.I (2) applies on the fixed common-chart subtype.
  simpa [continuation_branch_overlap] using
    holomorphic_local_coincidence_set_isClosed
      (f := continuation_left_branch r s) (g := continuation_right_branch r s)
      hbranches.1 hbranches.2

/-- Helper for Problem VI.5-extra-8: the common chart sits as an open subchart of the left
continuation chart. This is the source-side embedding needed to transport overlap opens into the
`TopCat.GlueData.MkCore` language. -/
lemma continuation_common_chart_left_inclusion_isOpenEmbedding
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    Topology.IsOpenEmbedding
      (TopologicalSpace.Opens.inclusion
        (show continuation_common_chart r s ≤ continuation_chart r from inf_le_left) :
          continuation_common_chart r s → continuation_chart r) := by
  -- The common chart is an open subset of the left chart, so the subtype inclusion is an open
  -- embedding.
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact continuous_inclusion
      (show (continuation_common_chart r s : Set ℂ) ⊆ continuation_chart r from inf_le_left)
  · intro x y hxy
    exact Subtype.ext (congrArg (fun w : continuation_chart r ↦ (w : ℂ)) hxy)
  · exact IsOpen.isOpenMap_inclusion (continuation_common_chart r s).2
      (show (continuation_common_chart r s : Set ℂ) ⊆ continuation_chart r from inf_le_left)

/-- Helper for Problem VI.5-extra-8: the chartwise overlap carrier on the left continuation chart.
It records exactly those left-chart points whose canonical common-chart lift lies in the raw
branch-overlap locus. -/
def continuation_overlap_set
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    Set (continuation_chart r) :=
  {z | ∃ hzs : (z : ℂ) ∈ continuation_chart s,
      (⟨(z : ℂ), ⟨z.2, hzs⟩⟩ : continuation_common_chart r s) ∈
        continuation_branch_overlap r s}

/-- Helper for Problem VI.5-extra-8: the chartwise overlap carrier is open in the left chart,
because it is the image of the raw open overlap locus under the left inclusion of the common
chart. -/
lemma continuation_overlap_set_isOpen
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    IsOpen (continuation_overlap_set r s) := by
  let ιrs :
      continuation_common_chart r s → continuation_chart r :=
    TopologicalSpace.Opens.inclusion
      (show continuation_common_chart r s ≤ continuation_chart r from inf_le_left)
  have hιrs_open :
      IsOpenMap ιrs :=
    IsOpen.isOpenMap_inclusion (continuation_common_chart r s).2
      (show (continuation_common_chart r s : Set ℂ) ⊆ continuation_chart r from inf_le_left)
  have himage :
      continuation_overlap_set r s =
        Set.image ιrs (continuation_branch_overlap r s) := by
    ext z
    constructor
    · rintro ⟨hzs, hz⟩
      refine ⟨⟨(z : ℂ), ⟨z.2, hzs⟩⟩, hz, ?_⟩
      rfl
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2.2, by simpa using hx⟩
  -- Re-express the carrier as an open image so that the chartwise overlap is ready for gluing.
  rw [himage]
  exact hιrs_open _ (continuation_branch_overlap_isOpen r s)

/-- Helper for Problem VI.5-extra-8: the raw overlap locus on the common chart, viewed as an open
subset of the left continuation chart. This is the chartwise overlap object expected by
`TopCat.GlueData.MkCore`. -/
noncomputable def continuation_overlap_open
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    TopologicalSpace.Opens (continuation_chart r) :=
  ⟨continuation_overlap_set r s, continuation_overlap_set_isOpen r s⟩

/-- Helper for Problem VI.5-extra-8: membership in the chartwise overlap open means that the
point admits a witness in the right chart whose common-chart representative lies in the raw
branch-overlap locus. -/
lemma mem_continuation_overlap_open_iff
    {U : Set ℂ} {f : ℂ → ℂ} {r s : ContinuationRepresentative U f}
    {z : continuation_chart r} :
    z ∈ continuation_overlap_open r s ↔
      ∃ hzs : (z : ℂ) ∈ continuation_chart s,
        (⟨(z : ℂ), ⟨z.2, hzs⟩⟩ : continuation_common_chart r s) ∈
          continuation_branch_overlap r s := by
  -- After naming the transported carrier explicitly, the membership statement is definitional.
  rfl

/-- Helper for Problem VI.5-extra-8: the transported self-overlap open is the whole chart. This
is the `V_id` input for the future gluing data. -/
lemma continuation_overlap_open_self
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    continuation_overlap_open r r = ⊤ := by
  ext z
  constructor
  · intro _hz
    trivial
  · intro _hz
    exact (mem_continuation_overlap_open_iff (r := r) (s := r) (z := z)).2 <| by
      refine ⟨z.2, ?_⟩
    -- The raw self-overlap already fills the entire common chart.
      simpa [continuation_branch_overlap_self] using
        (show
          (⟨(z : ℂ), ⟨z.2, z.2⟩⟩ : continuation_common_chart r r) ∈ Set.univ
        from trivial)

/-- Helper for Problem VI.5-extra-8: a point of the chartwise overlap open carries the raw
eventual equality of the two local continuation branches at the corresponding common-chart point.
This is the reusable overlap witness behind the future gluing transition maps. -/
lemma continuation_overlap_open_eventuallyEq
    {U : Set ℂ} {f : ℂ → ℂ} {r s : ContinuationRepresentative U f}
    {z : continuation_chart r} (hz : z ∈ continuation_overlap_open r s) :
    ∃ hzs : (z : ℂ) ∈ continuation_chart s,
      continuation_left_branch r s =ᶠ[nhds (⟨(z : ℂ), ⟨z.2, hzs⟩⟩ : continuation_common_chart r s)]
        continuation_right_branch r s := by
  -- Unpack the transported overlap membership back to the raw common-chart coincidence statement.
  rcases (mem_continuation_overlap_open_iff (r := r) (s := s) (z := z)).1 hz with ⟨hzs, hzrs⟩
  refine ⟨hzs, ?_⟩
  simpa [continuation_branch_overlap] using hzrs

/-- Helper for Problem VI.5-extra-8: overlap membership is symmetric after transporting the raw
eventual equality witness across the swapped common chart. This supplies the codomain membership
for the gluing transition map. -/
noncomputable def continuation_common_chart_swap
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    continuation_common_chart s r ≃ₜ continuation_common_chart r s :=
  Homeomorph.ofEqSubtypes <| by
    ext z
    simp [continuation_common_chart, and_left_comm, and_assoc, and_comm]

/-- Helper for Problem VI.5-extra-8: overlap membership is symmetric after transporting the raw
eventual equality witness across the swapped common chart. This supplies the codomain membership
for the gluing transition map. -/
lemma continuation_overlap_open_symm
    {U : Set ℂ} {f : ℂ → ℂ} {r s : ContinuationRepresentative U f}
    {z : continuation_chart r} (hz : z ∈ continuation_overlap_open r s) :
    ∃ hzs : (z : ℂ) ∈ continuation_chart s,
      (⟨(z : ℂ), hzs⟩ : continuation_chart s) ∈ continuation_overlap_open s r := by
  rcases continuation_overlap_open_eventuallyEq (r := r) (s := s) hz with ⟨hzs, hzrs⟩
  refine ⟨hzs, ?_⟩
  refine (mem_continuation_overlap_open_iff
    (r := s) (s := r) (z := ⟨(z : ℂ), hzs⟩)).2 ?_
  refine ⟨z.2, ?_⟩
  -- Route correction: the future transition is the identity on the base coordinate, so the only
  -- real work is transporting the overlap witness across the swapped common chart.
  let zsr : continuation_common_chart s r := ⟨(z : ℂ), ⟨hzs, z.2⟩⟩
  have hzsr :
      continuation_right_branch r s ∘ continuation_common_chart_swap (r := r) (s := s) =ᶠ[nhds zsr]
        continuation_left_branch r s ∘ continuation_common_chart_swap (r := r) (s := s) :=
    hzrs.symm.comp_tendsto
      (continuation_common_chart_swap (r := r) (s := s)).continuous_toFun.continuousAt
  simpa [zsr, continuation_branch_overlap, continuation_common_chart_swap,
    continuation_left_branch, continuation_right_branch, continuation_common_chart]
    using hzsr

/-- Helper for Problem VI.5-extra-8: the point-level transport between chartwise overlap opens is
the identity on the ambient complex coordinate, with codomain membership coming from symmetry of
branch coincidence. -/
noncomputable def continuation_overlap_swap
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    continuation_overlap_open r s → continuation_overlap_open s r :=
  fun x ↦
    let hsymm := continuation_overlap_open_symm (r := r) (s := s) x.2
    ⟨⟨(x.1 : ℂ), hsymm.choose⟩, hsymm.choose_spec⟩

/-- Helper for Problem VI.5-extra-8: the point-level overlap transport is continuous because it is
the identity map between nested open subtypes of the ambient complex plane. -/
lemma continuation_overlap_swap_continuous
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    Continuous (continuation_overlap_swap (r := r) (s := s)) := by
  -- The transport forgets to the ambient coordinate inclusion twice, then rebuilds the target
  -- subtype using the symmetric overlap witness.
  exact Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
      (fun x ↦ (continuation_overlap_open_symm (r := r) (s := s) x.2).choose))
    (fun x ↦ (continuation_overlap_open_symm (r := r) (s := s) x.2).choose_spec)

/-- Helper for Problem VI.5-extra-8: the chartwise transition morphism for gluing continuation
charts is the identity on the underlying complex coordinate. -/
noncomputable def continuation_overlap_transition
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    (TopologicalSpace.Opens.toTopCat (TopCat.of (continuation_chart r))).obj
        (continuation_overlap_open r s) ⟶
      (TopologicalSpace.Opens.toTopCat (TopCat.of (continuation_chart s))).obj
        (continuation_overlap_open s r) :=
  TopCat.ofHom
    ⟨continuation_overlap_swap (r := r) (s := s),
      continuation_overlap_swap_continuous (r := r) (s := s)⟩

/-- Problem VI.5-extra-8: every holomorphic function on a nonempty connected open set `U ⊆ ℂ`
admits a
maximal extension to an unramified surface over `ℂ`, in the sense of the universal property
described in (i), (ii), and (iii). -/
theorem exists_maximal_unramified_surface_extension
    {U : Set ℂ} (hU_open : IsOpen U) (hU_nonempty : U.Nonempty)
    (hU_connected : IsPreconnected U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ E : PlaneHolomorphicExtension U f, E.IsMaximal := by
  letI : ConnectedSpace U := Subtype.connectedSpace ⟨hU_nonempty, hU_connected⟩
  have hbase : Nonempty (PlaneHolomorphicExtension U f) :=
    plane_holomorphic_extension_nonempty hU_open hU_nonempty hU_connected hf
  -- The verified prefix is the tautological extension on `U`.
  -- Route correction: instead of the previous unsupported raw quotient-topology route, the next
  -- source-faithful step is to glue the local continuation charts `continuation_chart r` of all
  -- representatives `r : ContinuationRepresentative U f` along equality of their local branches.
  -- TODO: package those overlaps into `TopCat.GlueData`, descend projection/extension through the
  -- gluing, and prove the resulting extension satisfies `PlaneHolomorphicExtension.IsMaximal`.
  sorry
