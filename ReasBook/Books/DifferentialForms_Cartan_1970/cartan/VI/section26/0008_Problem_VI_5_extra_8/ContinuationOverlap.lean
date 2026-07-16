import DifferentialForms_Cartan_1970.cartan.VI.section26.«0008_Problem_VI_5_extra_8».ExtensionObjects

open scoped Manifold
open Set

/-- Helper for Problem VI.5-extra-8: a continuation representative is a point on some
holomorphic extension of the original germ. -/
abbrev ContinuationRepresentative (U : Set ℂ) (f : ℂ → ℂ) :=
  Σ E : PlaneHolomorphicExtension.{0} U f, E.surface

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

/-- Helper for Problem VI.5-extra-8: the overlap transport does not change the ambient complex
coordinate. This is the identity-on-base rewrite used by the gluing API. -/
lemma continuation_overlap_swap_val
    {U : Set ℂ} {f : ℂ → ℂ} {r s : ContinuationRepresentative U f}
    (x : continuation_overlap_open r s) :
    ((((continuation_overlap_swap (r := r) (s := s) x :
        continuation_overlap_open s r) : continuation_chart s) : ℂ)) = (x : ℂ) := by
  -- The transport was defined by reusing the same ambient coordinate and only changing the proof
  -- of overlap membership.
  rfl

/-- Helper for Problem VI.5-extra-8: on an overlap point, the two local continuation branches
agree after transporting the point across the chart transition. -/
lemma continuation_branch_eq_of_overlap
    {U : Set ℂ} {f : ℂ → ℂ} {r s : ContinuationRepresentative U f}
    (x : continuation_overlap_open r s) :
    continuation_branch r (x : continuation_chart r) =
      continuation_branch s
        (((continuation_overlap_swap (r := r) (s := s) x :
            continuation_overlap_open s r) : continuation_chart s)) := by
  rcases continuation_overlap_open_eventuallyEq (r := r) (s := s) x.2 with ⟨hzs, hzrs⟩
  let z : continuation_common_chart r s := ⟨(x : ℂ), ⟨x.1.2, hzs⟩⟩
  have hz :
      z ∈ continuation_branch_overlap r s := by
    simpa [continuation_branch_overlap, z] using hzrs
  have hbranch :
      continuation_branch r (x : continuation_chart r) =
        continuation_branch s ⟨(x : ℂ), hzs⟩ := by
    -- First compare both branches on the common-chart point provided by the overlap witness.
    simpa [continuation_left_branch, continuation_right_branch, z] using
      continuation_branch_eq_of_mem_overlap (r := r) (s := s) hz
  have hswap :
      (((continuation_overlap_swap (r := r) (s := s) x :
          continuation_overlap_open s r) : continuation_chart s)) = ⟨(x : ℂ), hzs⟩ := by
    -- The transported point has the same complex coordinate, so the subtype points coincide.
    apply Subtype.ext
    exact continuation_overlap_swap_val (r := r) (s := s) x
  simpa [hswap] using hbranch

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

/-- Helper for Problem VI.5-extra-8: each continuation chart is viewed as an object of `TopCat`
before the gluing data is assembled. Naming this owner avoids repeated coercion unfolding in the
gluing package. -/
noncomputable def continuation_chart_space
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) : TopCat :=
  TopCat.of.{0} ↥(continuation_chart r)

/-- Helper for Problem VI.5-extra-8: the chartwise transition morphism for gluing continuation
charts is the identity on the underlying complex coordinate. -/
noncomputable def continuation_overlap_transition
    {U : Set ℂ} {f : ℂ → ℂ} (r s : ContinuationRepresentative U f) :
    (TopologicalSpace.Opens.toTopCat (continuation_chart_space r)).obj
        (continuation_overlap_open r s) ⟶
      (TopologicalSpace.Opens.toTopCat (continuation_chart_space s)).obj
        (continuation_overlap_open s r) :=
  TopCat.ofHom
    ⟨continuation_overlap_swap (r := r) (s := s),
      continuation_overlap_swap_continuous (r := r) (s := s)⟩

/-- Helper for Problem VI.5-extra-8: overlap coincidence is transitive on triple chart overlaps.
This is the `t_inter` input for the gluing data of continuation charts. -/
lemma continuation_overlap_open_trans
    {U : Set ℂ} {f : ℂ → ℂ} {r s : ContinuationRepresentative U f}
    (t : ContinuationRepresentative U f) (x : continuation_overlap_open r s)
    (hx : ((x : continuation_overlap_open r s) : continuation_chart r) ∈
      continuation_overlap_open r t) :
    ((continuation_overlap_swap (r := r) (s := s) x :
        continuation_overlap_open s r) : continuation_chart s) ∈
      continuation_overlap_open s t := by
  rcases continuation_overlap_open_eventuallyEq (r := r) (s := s) x.2 with ⟨hzs, hzrs⟩
  rcases continuation_overlap_open_eventuallyEq (r := r) (s := t) hx with ⟨hzt, hzrt⟩
  let zst : continuation_common_chart s t := ⟨(x : ℂ), ⟨hzs, hzt⟩⟩
  let tripleSet : Set (continuation_common_chart s t) := {w | (w : ℂ) ∈ continuation_chart r}
  have hztriple : zst ∈ tripleSet := x.1.2
  let ztriple : tripleSet := ⟨zst, hztriple⟩
  let ιrs : tripleSet → continuation_common_chart r s :=
    fun w ↦ ⟨(w : ℂ), ⟨w.2, w.1.2.1⟩⟩
  let ιrt : tripleSet → continuation_common_chart r t :=
    fun w ↦ ⟨(w : ℂ), ⟨w.2, w.1.2.2⟩⟩
  have hιrs : Continuous ιrs := by
    fun_prop
  have hιrt : Continuous ιrt := by
    fun_prop
  have hrs_triple :
      (fun w : tripleSet ↦ continuation_branch r ⟨(w : ℂ), w.2⟩) =ᶠ[nhds ztriple]
        (fun w : tripleSet ↦ continuation_branch s ⟨(w : ℂ), w.1.2.1⟩) := by
    -- Restrict the `r = s` overlap witness to the triple-overlap subtype.
    simpa [ιrs, ztriple, zst, continuation_left_branch, continuation_right_branch]
      using hzrs.comp_tendsto (hιrs.continuousAt : ContinuousAt ιrs ztriple)
  have hrt_triple :
      (fun w : tripleSet ↦ continuation_branch r ⟨(w : ℂ), w.2⟩) =ᶠ[nhds ztriple]
        (fun w : tripleSet ↦ continuation_branch t ⟨(w : ℂ), w.1.2.2⟩) := by
    -- Restrict the `r = t` overlap witness to the same triple-overlap subtype.
    simpa [ιrt, ztriple, zst, continuation_left_branch, continuation_right_branch]
      using hzrt.comp_tendsto (hιrt.continuousAt : ContinuousAt ιrt ztriple)
  have hst_triple :
      (fun w : tripleSet ↦ continuation_left_branch s t w.1) =ᶠ[nhds ztriple]
        (fun w : tripleSet ↦ continuation_right_branch s t w.1) := by
    -- On the triple overlap, both branches agree with the common `r`-branch, so they agree with
    -- each other by transitivity of eventual equality.
    exact hrs_triple.symm.trans hrt_triple
  have hst_within :
      continuation_left_branch s t =ᶠ[nhdsWithin zst tripleSet] continuation_right_branch s t := by
    rw [nhdsWithin_eq_map_subtype_coe hztriple]
    simpa [ztriple] using hst_triple
  have htriple_open : IsOpen tripleSet := by
    simpa [tripleSet] using (continuation_chart_isOpen r).preimage continuous_subtype_val
  have htriple_nhds : tripleSet ∈ nhds zst := htriple_open.mem_nhds hztriple
  have hst :
      continuation_left_branch s t =ᶠ[nhds zst] continuation_right_branch s t := by
    rw [(nhdsWithin_eq_nhds).2 htriple_nhds] at hst_within
    exact hst_within
  -- Convert the triple-overlap eventual equality back to the chartwise overlap open.
  refine (mem_continuation_overlap_open_iff
    (r := s) (s := t) (z := ⟨(x : ℂ), hzs⟩)).2 ?_
  refine ⟨hzt, ?_⟩
  simpa [continuation_branch_overlap, zst] using hst

/-- Helper for Problem VI.5-extra-8: the self-transition on a chartwise overlap open is the
identity. This is the `t_id` field required by `TopCat.GlueData.mk'`. -/
lemma continuation_overlap_transition_id
    {U : Set ℂ} {f : ℂ → ℂ} (r : ContinuationRepresentative U f) :
    ⇑(continuation_overlap_transition (r := r) (s := r)) = id := by
  -- Since the overlap transport fixes the ambient coordinate, it fixes the whole subtype point.
  funext x
  apply Subtype.ext
  apply Subtype.ext
  exact continuation_overlap_swap_val (r := r) (s := r) x

/-- Helper for Problem VI.5-extra-8: the chartwise overlap transports satisfy the pointwise
cocycle condition required by `TopCat.GlueData.mk'`. -/
lemma continuation_overlap_transition_cocycle
    {U : Set ℂ} {f : ℂ → ℂ}
    (i j k : ContinuationRepresentative U f) (x : continuation_overlap_open i j)
    (hx : ((x : continuation_overlap_open i j) : continuation_chart i) ∈
      continuation_overlap_open i k) :
    (((↑) : continuation_overlap_open k j → continuation_chart k)
        (continuation_overlap_swap (r := j) (s := k)
          ⟨continuation_overlap_swap (r := i) (s := j) x,
            continuation_overlap_open_trans (r := i) (s := j) (t := k) x hx⟩)) =
      ((↑) : continuation_overlap_open k i → continuation_chart k)
        (continuation_overlap_swap (r := i) (s := k) ⟨x, hx⟩) := by
  let y : continuation_overlap_open j k :=
    ⟨continuation_overlap_swap (r := i) (s := j) x,
      continuation_overlap_open_trans (r := i) (s := j) (t := k) x hx⟩
  let z : continuation_overlap_open i k := ⟨x, hx⟩
  have hy :
      ((((continuation_overlap_swap (r := j) (s := k) y :
          continuation_overlap_open k j) : continuation_chart k) : ℂ)) = (y : ℂ) :=
    continuation_overlap_swap_val (r := j) (s := k) y
  have hxy : (y : ℂ) = (x : ℂ) :=
    continuation_overlap_swap_val (r := i) (s := j) x
  have hz :
      ((((continuation_overlap_swap (r := i) (s := k) z :
          continuation_overlap_open k i) : continuation_chart k) : ℂ)) = (x : ℂ) := by
    simpa using continuation_overlap_swap_val (r := i) (s := k) z
  have hleft :
      ((((continuation_overlap_swap (r := j) (s := k) y :
          continuation_overlap_open k j) : continuation_chart k) : ℂ)) = (x : ℂ) :=
    hy.trans hxy
  apply Subtype.ext
  -- Each transition fixes the ambient coordinate, so both sides reduce to the coordinate of `x`.
  exact hleft.trans hz.symm

/-- Helper for Problem VI.5-extra-8: the cocycle identity for the gluing data, rewritten in the
exact morphism form expected by `TopCat.GlueData.mk'`. -/
lemma continuation_overlap_transition_mkCore_cocycle
    {U : Set ℂ} {f : ℂ → ℂ}
    (i j k : ContinuationRepresentative U f) (x : continuation_overlap_open i j)
    (hx : ((x : continuation_overlap_open i j) : continuation_chart i) ∈
      continuation_overlap_open i k) :
    (((↑) : continuation_overlap_open k j → continuation_chart k)
        ((continuation_overlap_transition (r := j) (s := k))
          ⟨((show continuation_overlap_open j i from
                (continuation_overlap_transition (r := i) (s := j)) x) :
              continuation_chart j),
            continuation_overlap_open_trans (r := i) (s := j) (t := k) x hx⟩)) =
      ((↑) : continuation_overlap_open k i → continuation_chart k)
        ((continuation_overlap_transition (r := i) (s := k))
          ⟨(x : continuation_chart i), hx⟩) := by
  -- This is just the pointwise cocycle written through the `TopCat` morphism coercions.
  simpa [continuation_overlap_transition] using
    continuation_overlap_transition_cocycle (i := i) (j := j) (k := k) x hx

/-- Helper for Problem VI.5-extra-8: the continuation cocycle in the exact coercion shape of the
`TopCat.GlueData.MkCore.cocycle` field. -/
lemma continuation_overlap_transition_mkCore_cocycle_exact
    {U : Set ℂ} {f : ℂ → ℂ} :
    let chartSpace : ContinuationRepresentative U f → TopCat :=
      continuation_chart_space (U := U) (f := f)
    let overlapOpen : ∀ i, ContinuationRepresentative U f → TopologicalSpace.Opens (chartSpace i) :=
      continuation_overlap_open (U := U) (f := f)
    let overlapTransition :
        ∀ i j, (TopologicalSpace.Opens.toTopCat (chartSpace i)).obj (overlapOpen i j) ⟶
          (TopologicalSpace.Opens.toTopCat (chartSpace j)).obj (overlapOpen j i) :=
      continuation_overlap_transition (U := U) (f := f)
    ∀ (i j k : ContinuationRepresentative U f) (x : overlapOpen i j)
      (hx : ((x : overlapOpen i j) : chartSpace i) ∈ overlapOpen i k),
      (((↑) : overlapOpen k j → chartSpace k)
          ((CategoryTheory.ConcreteCategory.hom (overlapTransition j k))
            ⟨((show overlapOpen j i from
                  (CategoryTheory.ConcreteCategory.hom (overlapTransition i j)) x) :
                chartSpace j),
              continuation_overlap_open_trans (r := i) (s := j) (t := k) x hx⟩)) =
        ((↑) : overlapOpen k i → chartSpace k)
          ((CategoryTheory.ConcreteCategory.hom (overlapTransition i k))
            ⟨((show overlapOpen i j from x) : chartSpace i), hx⟩) := by
  -- Route correction: match the local `MkCore` abbreviations first, then reduce to the already
  -- proved pointwise cocycle for continuation overlap transports.
  dsimp
  intro i j k x hx
  simpa [continuation_overlap_transition] using
    continuation_overlap_transition_mkCore_cocycle (i := i) (j := j) (k := k) x hx
