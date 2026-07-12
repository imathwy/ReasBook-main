import DifferentialForms_Cartan_1970.VI.section25.«0016_Theorem_VI_4_extra_13».SphereNeighborhoodContinuation

open scoped Manifold
open Set

namespace Cartan

section

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]
variable {c₀ : SphereNeighborhoodChart X}

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the common target chart used to
compare the inverse branches of two seeded sphere charts. -/
noncomputable def seededSphereChartCommonTarget
    (i j : SeededSphereNeighborhoodChart c₀) :
    TopologicalSpace.Opens RiemannSphere :=
  i.chart.target ⊓ j.chart.target

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the left inverse branch restricted to
the common target of two seeded sphere charts. -/
noncomputable def seededSphereChartLeftBranch
    (i j : SeededSphereNeighborhoodChart c₀) :
    seededSphereChartCommonTarget i j → X :=
  fun z ↦ i.chart.branch ⟨z.1, z.2.1⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the right inverse branch restricted
to the same common target. -/
noncomputable def seededSphereChartRightBranch
    (i j : SeededSphereNeighborhoodChart c₀) :
    seededSphereChartCommonTarget i j → X :=
  fun z ↦ j.chart.branch ⟨z.1, z.2.2⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the raw target-side overlap relation
for two seeded charts is the local coincidence locus of their restricted inverse branches. -/
def seededSphereChartBranchOverlap
    (i j : SeededSphereNeighborhoodChart c₀) :
    Set (seededSphereChartCommonTarget i j) :=
  {z | seededSphereChartLeftBranch i j =ᶠ[nhds z] seededSphereChartRightBranch i j}

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: target-side branch coincidence is an
open condition on the common target of two seeded charts. -/
lemma seededSphereChartBranchOverlap_isOpen
    (i j : SeededSphereNeighborhoodChart c₀) :
    IsOpen (seededSphereChartBranchOverlap i j) := by
  -- On the fixed common-target subtype this is exactly the local coincidence locus handled by
  -- Proposition 4.I (1).
  simpa [seededSphereChartBranchOverlap] using
    (local_coincidence_set_isOpen
      (f := seededSphereChartLeftBranch i j)
      (g := seededSphereChartRightBranch i j))

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a seeded chart overlaps with itself on
its whole target. This is the `V_id` input for the later gluing data. -/
lemma seededSphereChartBranchOverlap_self
    (i : SeededSphereNeighborhoodChart c₀) :
    seededSphereChartBranchOverlap i i = Set.univ := by
  ext z
  constructor
  · intro _hz
    trivial
  · intro _hz
    -- The two restricted branches are definitionally the same when the seeded chart is fixed.
    refine Filter.EventuallyEq.of_eq ?_
    funext w
    rfl

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a point in the raw overlap locus is in
particular a pointwise coincidence point of the two restricted branches. -/
lemma seededSphereChartBranchEq_of_memOverlap
    {i j : SeededSphereNeighborhoodChart c₀}
    {z : seededSphereChartCommonTarget i j}
    (hz : z ∈ seededSphereChartBranchOverlap i j) :
    seededSphereChartLeftBranch i j z = seededSphereChartRightBranch i j z := by
  -- Specializing an eventual equality to the center point recovers ordinary equality.
  have hz' :
      seededSphereChartLeftBranch i j =ᶠ[nhds z] seededSphereChartRightBranch i j := by
    simpa [seededSphereChartBranchOverlap] using hz
  exact hz'.eq_of_nhds

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: both restricted inverse branches on
the common target remain holomorphic. -/
lemma seededSphereChartCommonBranch_mdifferentiable
    (i j : SeededSphereNeighborhoodChart c₀) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (seededSphereChartLeftBranch i j) ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (seededSphereChartRightBranch i j) := by
  have hleft_inc :
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (TopologicalSpace.Opens.inclusion
          (show seededSphereChartCommonTarget i j ≤ i.chart.target from inf_le_left)) :=
    (contMDiff_inclusion (I := 𝓘(ℂ)) (n := 1)
      (show seededSphereChartCommonTarget i j ≤ i.chart.target from inf_le_left)).mdifferentiable
      one_ne_zero
  have hright_inc :
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (TopologicalSpace.Opens.inclusion
          (show seededSphereChartCommonTarget i j ≤ j.chart.target from inf_le_right)) :=
    (contMDiff_inclusion (I := 𝓘(ℂ)) (n := 1)
      (show seededSphereChartCommonTarget i j ≤ j.chart.target from inf_le_right)).mdifferentiable
      one_ne_zero
  constructor
  · -- The left branch is the chart branch precomposed with the left target inclusion.
    simpa [seededSphereChartLeftBranch, Function.comp] using
      (SphereNeighborhoodChart.branch_mdifferentiable i.chart).comp hleft_inc
  · -- The right branch is handled symmetrically.
    simpa [seededSphereChartRightBranch, Function.comp] using
      (SphereNeighborhoodChart.branch_mdifferentiable j.chart).comp hright_inc

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the raw target-side overlap locus is
also closed, because the two restricted inverse branches are holomorphic. -/
lemma seededSphereChartBranchOverlap_isClosed
    (i j : SeededSphereNeighborhoodChart c₀) :
    IsClosed (seededSphereChartBranchOverlap i j) := by
  let hbranches := seededSphereChartCommonBranch_mdifferentiable i j
  -- Proposition 4.I (2) applies on the fixed common-target subtype.
  simpa [seededSphereChartBranchOverlap] using
    holomorphic_local_coincidence_set_isClosed
      (f := seededSphereChartLeftBranch i j)
      (g := seededSphereChartRightBranch i j)
      hbranches.1 hbranches.2

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the chartwise target-overlap carrier
on the left seeded chart target. -/
def seededSphereChartBranchOverlapSet
    (i j : SeededSphereNeighborhoodChart c₀) :
    Set i.chart.target :=
  {z | ∃ hzs : (z : RiemannSphere) ∈ j.chart.target,
      (⟨(z : RiemannSphere), ⟨z.2, hzs⟩⟩ :
          seededSphereChartCommonTarget i j) ∈ seededSphereChartBranchOverlap i j}

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the chartwise target-overlap carrier
is open in the left seeded chart target. -/
lemma seededSphereChartBranchOverlapSet_isOpen
    (i j : SeededSphereNeighborhoodChart c₀) :
    IsOpen (seededSphereChartBranchOverlapSet i j) := by
  let ιij :
      seededSphereChartCommonTarget i j → i.chart.target :=
    TopologicalSpace.Opens.inclusion
      (show seededSphereChartCommonTarget i j ≤ i.chart.target from inf_le_left)
  have hιij_open :
      IsOpenMap ιij :=
    IsOpen.isOpenMap_inclusion (seededSphereChartCommonTarget i j).2
      (show (seededSphereChartCommonTarget i j : Set RiemannSphere) ⊆ i.chart.target from
        inf_le_left)
  have himage :
      seededSphereChartBranchOverlapSet i j =
        Set.image ιij (seededSphereChartBranchOverlap i j) := by
    ext z
    constructor
    · rintro ⟨hzs, hz⟩
      refine ⟨⟨(z : RiemannSphere), ⟨z.2, hzs⟩⟩, hz, ?_⟩
      rfl
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2.2, by simpa using hx⟩
  -- Re-express the transported overlap as an open image.
  rw [himage]
  exact hιij_open _ (seededSphereChartBranchOverlap_isOpen i j)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the target-side overlap open on the
left seeded chart target. This is the chartwise overlap object expected by `TopCat.GlueData`. -/
noncomputable def seededSphereChartBranchOverlapOpen
    (i j : SeededSphereNeighborhoodChart c₀) :
    TopologicalSpace.Opens i.chart.target :=
  ⟨seededSphereChartBranchOverlapSet i j, seededSphereChartBranchOverlapSet_isOpen i j⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: membership in the chartwise overlap
open is exactly membership of the corresponding common-target point in the raw overlap locus. -/
lemma mem_seededSphereChartBranchOverlapOpen_iff
    {i j : SeededSphereNeighborhoodChart c₀}
    {z : i.chart.target} :
    z ∈ seededSphereChartBranchOverlapOpen i j ↔
      ∃ hzs : (z : RiemannSphere) ∈ j.chart.target,
        (⟨(z : RiemannSphere), ⟨z.2, hzs⟩⟩ :
            seededSphereChartCommonTarget i j) ∈ seededSphereChartBranchOverlap i j := by
  -- After naming the transported carrier explicitly, the membership statement is definitional.
  rfl

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the transported self-overlap open is
the whole seeded chart target. -/
lemma seededSphereChartBranchOverlapOpen_self
    (i : SeededSphereNeighborhoodChart c₀) :
    seededSphereChartBranchOverlapOpen i i = ⊤ := by
  ext z
  constructor
  · intro _hz
    trivial
  · intro _hz
    exact (mem_seededSphereChartBranchOverlapOpen_iff (i := i) (j := i) (z := z)).2 <| by
      refine ⟨z.2, ?_⟩
      -- The raw self-overlap already fills the whole common target.
      simpa [seededSphereChartBranchOverlap_self] using
        (show
          (⟨(z : RiemannSphere), ⟨z.2, z.2⟩⟩ : seededSphereChartCommonTarget i i) ∈ Set.univ
        from trivial)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a point of the chartwise overlap open
carries the raw eventual equality of the two restricted inverse branches. -/
lemma seededSphereChartBranchOverlapOpen_eventuallyEq
    {i j : SeededSphereNeighborhoodChart c₀}
    {z : i.chart.target} (hz : z ∈ seededSphereChartBranchOverlapOpen i j) :
    ∃ hzs : (z : RiemannSphere) ∈ j.chart.target,
      seededSphereChartLeftBranch i j =ᶠ[
          nhds (⟨(z : RiemannSphere), ⟨z.2, hzs⟩⟩ : seededSphereChartCommonTarget i j)]
        seededSphereChartRightBranch i j := by
  -- Unpack the transported overlap witness back to the raw common-target coincidence statement.
  rcases (mem_seededSphereChartBranchOverlapOpen_iff (i := i) (j := j) (z := z)).1 hz with
    ⟨hzs, hzrs⟩
  refine ⟨hzs, ?_⟩
  simpa [seededSphereChartBranchOverlap] using hzrs

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the swapped common-target subtype
homeomorphism used to transport overlap witnesses symmetrically. -/
noncomputable def seededSphereChartCommonTarget_swap
    (i j : SeededSphereNeighborhoodChart c₀) :
    seededSphereChartCommonTarget j i ≃ₜ seededSphereChartCommonTarget i j :=
  Homeomorph.ofEqSubtypes <| by
    ext z
    simp [seededSphereChartCommonTarget, and_left_comm, and_assoc, and_comm]

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: target-overlap membership is
symmetric after transporting the raw eventual-equality witness across the swapped common target.
-/
lemma seededSphereChartBranchOverlapOpen_symm
    {i j : SeededSphereNeighborhoodChart c₀}
    {z : i.chart.target} (hz : z ∈ seededSphereChartBranchOverlapOpen i j) :
    ∃ hzs : (z : RiemannSphere) ∈ j.chart.target,
      (⟨(z : RiemannSphere), hzs⟩ : j.chart.target) ∈
        seededSphereChartBranchOverlapOpen j i := by
  rcases seededSphereChartBranchOverlapOpen_eventuallyEq (i := i) (j := j) hz with ⟨hzs, hzrs⟩
  refine ⟨hzs, ?_⟩
  refine (mem_seededSphereChartBranchOverlapOpen_iff
    (i := j) (j := i) (z := ⟨(z : RiemannSphere), hzs⟩)).2 ?_
  refine ⟨z.2, ?_⟩
  -- The future transition is the identity on the ambient target coordinate, so the only work is
  -- transporting the overlap witness across the swapped common-target homeomorphism.
  let zji : seededSphereChartCommonTarget j i := ⟨(z : RiemannSphere), ⟨hzs, z.2⟩⟩
  have hzji :
      seededSphereChartRightBranch i j ∘ seededSphereChartCommonTarget_swap i j =ᶠ[nhds zji]
        seededSphereChartLeftBranch i j ∘ seededSphereChartCommonTarget_swap i j :=
    hzrs.symm.comp_tendsto
      (seededSphereChartCommonTarget_swap i j).continuous_toFun.continuousAt
  simpa [zji, seededSphereChartBranchOverlap, seededSphereChartCommonTarget_swap,
    seededSphereChartLeftBranch, seededSphereChartRightBranch, seededSphereChartCommonTarget]
    using hzji

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the point-level overlap transport
between seeded chart targets is the identity on the ambient sphere coordinate. -/
noncomputable def seededSphereChartBranchOverlapSwap
    (i j : SeededSphereNeighborhoodChart c₀) :
    seededSphereChartBranchOverlapOpen i j → seededSphereChartBranchOverlapOpen j i :=
  fun x ↦
    let hsymm := seededSphereChartBranchOverlapOpen_symm (i := i) (j := j) x.2
    ⟨⟨(x.1 : RiemannSphere), hsymm.choose⟩, hsymm.choose_spec⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the overlap transport does not change
the ambient sphere coordinate. -/
lemma seededSphereChartBranchOverlapSwap_val
    {i j : SeededSphereNeighborhoodChart c₀}
    (x : seededSphereChartBranchOverlapOpen i j) :
    ((((seededSphereChartBranchOverlapSwap i j x :
        seededSphereChartBranchOverlapOpen j i) : j.chart.target) : RiemannSphere)) =
      (x : RiemannSphere) := by
  -- The transport only changes the proof of overlap membership.
  rfl

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the point-level overlap transport is
continuous because it is the identity between open subtypes of the sphere. -/
lemma seededSphereChartBranchOverlapSwap_continuous
    (i j : SeededSphereNeighborhoodChart c₀) :
    Continuous (seededSphereChartBranchOverlapSwap i j) := by
  -- The transport forgets to the ambient target coordinate twice, then rebuilds the target
  -- subtype using the symmetric overlap witness.
  exact Continuous.subtype_mk
    (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
      (fun x ↦ (seededSphereChartBranchOverlapOpen_symm (i := i) (j := j) x.2).choose))
    (fun x ↦ (seededSphereChartBranchOverlapOpen_symm (i := i) (j := j) x.2).choose_spec)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: each seeded chart target is viewed as
an object of `TopCat` before the gluing data is assembled. -/
noncomputable def seededSphereChart_targetSpace
    (i : SeededSphereNeighborhoodChart c₀) : TopCat :=
  TopCat.of ↥(i.chart.target)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the chartwise transition morphism for
gluing seeded chart targets is the identity on the underlying sphere coordinate. -/
noncomputable def seededSphereChartBranchOverlapTransition
    (i j : SeededSphereNeighborhoodChart c₀) :
    (TopologicalSpace.Opens.toTopCat (seededSphereChart_targetSpace i)).obj
        (seededSphereChartBranchOverlapOpen i j) ⟶
      (TopologicalSpace.Opens.toTopCat (seededSphereChart_targetSpace j)).obj
        (seededSphereChartBranchOverlapOpen j i) :=
  TopCat.ofHom
    ⟨seededSphereChartBranchOverlapSwap i j,
      seededSphereChartBranchOverlapSwap_continuous i j⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: target-overlap coincidence is
transitive on triple seeded chart overlaps. This is the `t_inter` input for `TopCat.GlueData`.
-/
lemma seededSphereChartBranchOverlapOpen_trans
    {i j : SeededSphereNeighborhoodChart c₀}
    (k : SeededSphereNeighborhoodChart c₀) (x : seededSphereChartBranchOverlapOpen i j)
    (hx : ((x : seededSphereChartBranchOverlapOpen i j) : i.chart.target) ∈
      seededSphereChartBranchOverlapOpen i k) :
    ((seededSphereChartBranchOverlapSwap i j x :
        seededSphereChartBranchOverlapOpen j i) : j.chart.target) ∈
      seededSphereChartBranchOverlapOpen j k := by
  rcases seededSphereChartBranchOverlapOpen_eventuallyEq (i := i) (j := j) x.2 with ⟨hzj, hzij⟩
  rcases seededSphereChartBranchOverlapOpen_eventuallyEq (i := i) (j := k) hx with ⟨hzk, hzik⟩
  let zjk : seededSphereChartCommonTarget j k :=
    ⟨(x : RiemannSphere), ⟨hzj, hzk⟩⟩
  let tripleSet : Set (seededSphereChartCommonTarget j k) :=
    {w | (w : RiemannSphere) ∈ i.chart.target}
  have hztriple : zjk ∈ tripleSet := x.1.2
  let ztriple : tripleSet := ⟨zjk, hztriple⟩
  let ιij : tripleSet → seededSphereChartCommonTarget i j :=
    fun w ↦ ⟨(w : RiemannSphere), ⟨w.2, w.1.2.1⟩⟩
  let ιik : tripleSet → seededSphereChartCommonTarget i k :=
    fun w ↦ ⟨(w : RiemannSphere), ⟨w.2, w.1.2.2⟩⟩
  have hιij : Continuous ιij := by
    fun_prop
  have hιik : Continuous ιik := by
    fun_prop
  have hij_triple :
      (fun w : tripleSet ↦ i.chart.branch ⟨(w : RiemannSphere), w.2⟩) =ᶠ[nhds ztriple]
        (fun w : tripleSet ↦ j.chart.branch ⟨(w : RiemannSphere), w.1.2.1⟩) := by
    -- Restrict the `i = j` overlap witness to the triple-overlap subtype.
    simpa [ιij, ztriple, zjk, seededSphereChartLeftBranch, seededSphereChartRightBranch]
      using hzij.comp_tendsto (hιij.continuousAt : ContinuousAt ιij ztriple)
  have hik_triple :
      (fun w : tripleSet ↦ i.chart.branch ⟨(w : RiemannSphere), w.2⟩) =ᶠ[nhds ztriple]
        (fun w : tripleSet ↦ k.chart.branch ⟨(w : RiemannSphere), w.1.2.2⟩) := by
    -- Restrict the `i = k` overlap witness to the same triple-overlap subtype.
    simpa [ιik, ztriple, zjk, seededSphereChartLeftBranch, seededSphereChartRightBranch]
      using hzik.comp_tendsto (hιik.continuousAt : ContinuousAt ιik ztriple)
  have hjk_triple :
      (fun w : tripleSet ↦ seededSphereChartLeftBranch j k w.1) =ᶠ[nhds ztriple]
        (fun w : tripleSet ↦ seededSphereChartRightBranch j k w.1) := by
    -- On the triple overlap, both branches agree with the common `i`-branch.
    exact hij_triple.symm.trans hik_triple
  have hjk_within :
      seededSphereChartLeftBranch j k =ᶠ[nhdsWithin zjk tripleSet]
        seededSphereChartRightBranch j k := by
    rw [nhdsWithin_eq_map_subtype_coe hztriple]
    simpa [ztriple] using hjk_triple
  have htriple_open : IsOpen tripleSet := by
    simpa [tripleSet] using i.chart.target.isOpen.preimage continuous_subtype_val
  have htriple_nhds : tripleSet ∈ nhds zjk := htriple_open.mem_nhds hztriple
  have hjk :
      seededSphereChartLeftBranch j k =ᶠ[nhds zjk] seededSphereChartRightBranch j k := by
    rw [(nhdsWithin_eq_nhds).2 htriple_nhds] at hjk_within
    exact hjk_within
  -- Convert the triple-overlap eventual equality back to the chartwise overlap open.
  refine (mem_seededSphereChartBranchOverlapOpen_iff
    (i := j) (j := k) (z := ⟨(x : RiemannSphere), hzj⟩)).2 ?_
  refine ⟨hzk, ?_⟩
  simpa [seededSphereChartBranchOverlap, zjk] using hjk

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the self-transition on a seeded chart
overlap is the identity. This is the `t_id` input for `TopCat.GlueData.mk'`. -/
lemma seededSphereChartBranchOverlapTransition_id
    (i : SeededSphereNeighborhoodChart c₀) :
    ⇑(seededSphereChartBranchOverlapTransition i i) = id := by
  -- Since the overlap transport fixes the ambient sphere coordinate, it fixes the whole subtype.
  funext x
  apply Subtype.ext
  apply Subtype.ext
  exact seededSphereChartBranchOverlapSwap_val (i := i) (j := i) x

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the chartwise overlap transports for
seeded targets satisfy the pointwise cocycle condition required by `TopCat.GlueData.mk'`. -/
lemma seededSphereChartBranchOverlapTransition_cocycle
    (i j k : SeededSphereNeighborhoodChart c₀) (x : seededSphereChartBranchOverlapOpen i j)
    (hx : ((x : seededSphereChartBranchOverlapOpen i j) : i.chart.target) ∈
      seededSphereChartBranchOverlapOpen i k) :
    (((↑) : seededSphereChartBranchOverlapOpen k j → k.chart.target)
        (seededSphereChartBranchOverlapSwap j k
          ⟨seededSphereChartBranchOverlapSwap i j x,
            seededSphereChartBranchOverlapOpen_trans (i := i) (j := j) k x hx⟩)) =
      ((↑) : seededSphereChartBranchOverlapOpen k i → k.chart.target)
        (seededSphereChartBranchOverlapSwap i k ⟨x, hx⟩) := by
  let y : seededSphereChartBranchOverlapOpen j k :=
    ⟨seededSphereChartBranchOverlapSwap i j x,
      seededSphereChartBranchOverlapOpen_trans (i := i) (j := j) (k := k) x hx⟩
  let z : seededSphereChartBranchOverlapOpen i k := ⟨x, hx⟩
  have hy :
      ((((seededSphereChartBranchOverlapSwap j k y :
          seededSphereChartBranchOverlapOpen k j) : k.chart.target) : RiemannSphere)) = (y : RiemannSphere) :=
    seededSphereChartBranchOverlapSwap_val (i := j) (j := k) y
  have hxy : (y : RiemannSphere) = (x : RiemannSphere) :=
    seededSphereChartBranchOverlapSwap_val (i := i) (j := j) x
  have hz :
      ((((seededSphereChartBranchOverlapSwap i k z :
          seededSphereChartBranchOverlapOpen k i) : k.chart.target) : RiemannSphere)) = (x : RiemannSphere) := by
    simpa using seededSphereChartBranchOverlapSwap_val (i := i) (j := k) z
  have hleft :
      ((((seededSphereChartBranchOverlapSwap j k y :
          seededSphereChartBranchOverlapOpen k j) : k.chart.target) : RiemannSphere)) = (x : RiemannSphere) :=
    hy.trans hxy
  apply Subtype.ext
  -- Each transition fixes the ambient coordinate, so both sides reduce to the coordinate of `x`.
  exact hleft.trans hz.symm

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the seeded cocycle identity written
in the exact coercion shape expected by `TopCat.GlueData.MkCore.cocycle`. -/
lemma seededSphereChartBranchOverlapTransition_mkCore_cocycle_exact :
    let chartSpace : SeededSphereNeighborhoodChart c₀ → TopCat :=
      seededSphereChart_targetSpace
    let overlapOpen :
        ∀ i, SeededSphereNeighborhoodChart c₀ → TopologicalSpace.Opens (chartSpace i) :=
      seededSphereChartBranchOverlapOpen
    let overlapTransition :
        ∀ i j, (TopologicalSpace.Opens.toTopCat (chartSpace i)).obj (overlapOpen i j) ⟶
          (TopologicalSpace.Opens.toTopCat (chartSpace j)).obj (overlapOpen j i) :=
      seededSphereChartBranchOverlapTransition
    ∀ (i j k : SeededSphereNeighborhoodChart c₀) (x : overlapOpen i j)
      (hx : ((x : overlapOpen i j) : chartSpace i) ∈ overlapOpen i k),
      (((↑) : overlapOpen k j → chartSpace k)
          ((CategoryTheory.ConcreteCategory.hom (overlapTransition j k))
            ⟨((show overlapOpen j i from
                  (CategoryTheory.ConcreteCategory.hom (overlapTransition i j)) x) :
                chartSpace j),
              seededSphereChartBranchOverlapOpen_trans (i := i) (j := j) (k := k) x hx⟩)) =
        ((↑) : overlapOpen k i → chartSpace k)
          ((CategoryTheory.ConcreteCategory.hom (overlapTransition i k))
            ⟨((show overlapOpen i j from x) : chartSpace i), hx⟩) := by
  -- Match the local `MkCore` abbreviations first, then reduce to the already proved pointwise
  -- cocycle for seeded target-overlap transports.
  dsimp
  intro i j k x hx
  simpa [seededSphereChartBranchOverlapTransition] using
    seededSphereChartBranchOverlapTransition_cocycle (i := i) (j := j) (k := k) x hx

-- Route correction: the unlifted overlap API is stable, but `SeededSphereNeighborhoodChart c₀`
-- need not live in the same universe as each raw target chart. We therefore lift the target-side
-- chart family once before forming `TopCat.GlueData`.
/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the seeded chart target lifted to the
common universe used by the glued quotient. -/
noncomputable def seededSphereChart_liftedTargetSpace
    (i : SeededSphereNeighborhoodChart c₀) : TopCat :=
  TopCat.uliftFunctor.obj (seededSphereChart_targetSpace i)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the chartwise overlap open
transported across the lifted target homeomorphism. -/
noncomputable def seededSphereChart_liftedOverlapOpen
    (i j : SeededSphereNeighborhoodChart c₀) :
    TopologicalSpace.Opens (seededSphereChart_liftedTargetSpace i) :=
  ⟨{z | (seededSphereChart_targetSpace i).uliftFunctorObjHomeo.symm z ∈
      seededSphereChartBranchOverlapOpen i j},
    by
      -- The lifted overlap is the homeomorphic preimage of the already proved unlifted overlap.
      change IsOpen (((seededSphereChart_targetSpace i).uliftFunctorObjHomeo.symm) ⁻¹'
        (show Set (seededSphereChart_targetSpace i) from
          (seededSphereChartBranchOverlapOpen i j).1))
      exact (seededSphereChartBranchOverlapOpen i j).2.preimage
        (seededSphereChart_targetSpace i).uliftFunctorObjHomeo.symm.continuous_toFun⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: membership in the lifted overlap open
is exactly membership of the lowered point in the original overlap open. -/
lemma mem_seededSphereChart_liftedOverlapOpen_iff
    {i j : SeededSphereNeighborhoodChart c₀}
    {z : seededSphereChart_liftedTargetSpace i} :
    z ∈ seededSphereChart_liftedOverlapOpen i j ↔
      (seededSphereChart_targetSpace i).uliftFunctorObjHomeo.symm z ∈
        seededSphereChartBranchOverlapOpen i j := by
  rfl

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: lowering a lifted overlap point
recovers the original target-overlap point. -/
noncomputable def seededSphereChart_liftedOverlapDown
    (i j : SeededSphereNeighborhoodChart c₀) :
    seededSphereChart_liftedOverlapOpen i j → seededSphereChartBranchOverlapOpen i j :=
  fun x ↦
    ⟨(seededSphereChart_targetSpace i).uliftFunctorObjHomeo.symm x.1,
      (mem_seededSphereChart_liftedOverlapOpen_iff (i := i) (j := j) (z := x.1)).1 x.2⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: an original overlap point can be
lifted back to the universe-stable chart family. -/
noncomputable def seededSphereChart_liftedOverlapUp
    (i j : SeededSphereNeighborhoodChart c₀) :
    seededSphereChartBranchOverlapOpen i j → seededSphereChart_liftedOverlapOpen i j :=
  fun x ↦
    ⟨(seededSphereChart_targetSpace i).uliftFunctorObjHomeo x.1,
      by
        show (seededSphereChart_targetSpace i).uliftFunctorObjHomeo.symm
            ((seededSphereChart_targetSpace i).uliftFunctorObjHomeo x.1) ∈
          seededSphereChartBranchOverlapOpen i j
        exact x.2⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: lifting and then lowering a seeded
overlap point recovers the original point. -/
lemma seededSphereChart_liftedOverlapDown_up
    (i j : SeededSphereNeighborhoodChart c₀)
    (x : seededSphereChartBranchOverlapOpen i j) :
    seededSphereChart_liftedOverlapDown i j
        (seededSphereChart_liftedOverlapUp i j x) = x := by
  -- The lift only changes the universe level of the target chart carrier.
  apply Subtype.ext
  rfl

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: lowering and then lifting a seeded
lifted-overlap point returns the same point. -/
lemma seededSphereChart_liftedOverlapUp_down
    (i j : SeededSphereNeighborhoodChart c₀)
    (x : seededSphereChart_liftedOverlapOpen i j) :
    seededSphereChart_liftedOverlapUp i j
        (seededSphereChart_liftedOverlapDown i j x) = x := by
  -- Again only the proof component changes, not the underlying lifted point.
  apply Subtype.ext
  rfl

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: lowering a lifted overlap point is
continuous. -/
lemma seededSphereChart_liftedOverlapDown_continuous
    (i j : SeededSphereNeighborhoodChart c₀) :
    Continuous (seededSphereChart_liftedOverlapDown i j) := by
  -- Lowering is the inverse lifted-chart homeomorphism restricted to the overlap subtype.
  exact Continuous.subtype_mk
    ((seededSphereChart_targetSpace i).uliftFunctorObjHomeo.symm.continuous_toFun.comp
      continuous_subtype_val)
    (fun x ↦
      (mem_seededSphereChart_liftedOverlapOpen_iff (i := i) (j := j) (z := x.1)).1 x.2)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: lifting an original overlap point
back to the universe-stable chart family is continuous. -/
lemma seededSphereChart_liftedOverlapUp_continuous
    (i j : SeededSphereNeighborhoodChart c₀) :
    Continuous (seededSphereChart_liftedOverlapUp i j) := by
  -- Lifting is the forward lifted-chart homeomorphism restricted to the overlap subtype.
  exact Continuous.subtype_mk
    ((seededSphereChart_targetSpace i).uliftFunctorObjHomeo.continuous_toFun.comp
      continuous_subtype_val)
    (fun x ↦ by
      show (seededSphereChart_targetSpace i).uliftFunctorObjHomeo.symm
          ((seededSphereChart_targetSpace i).uliftFunctorObjHomeo x.1) ∈
        seededSphereChartBranchOverlapOpen i j
      exact x.2)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the lifted overlap transition is
obtained by conjugating the original target-overlap transport by the lifted target homeomorphisms.
-/
noncomputable def seededSphereChart_liftedOverlapTransition
    (i j : SeededSphereNeighborhoodChart c₀) :
    (TopologicalSpace.Opens.toTopCat (seededSphereChart_liftedTargetSpace i)).obj
        (seededSphereChart_liftedOverlapOpen i j) ⟶
      (TopologicalSpace.Opens.toTopCat (seededSphereChart_liftedTargetSpace j)).obj
        (seededSphereChart_liftedOverlapOpen j i) :=
  TopCat.ofHom
    ⟨seededSphereChart_liftedOverlapUp j i ∘
        seededSphereChartBranchOverlapSwap i j ∘
        seededSphereChart_liftedOverlapDown i j,
      -- Conjugating the unlifted transition by homeomorphisms preserves continuity.
      (seededSphereChart_liftedOverlapUp_continuous j i).comp <|
        (seededSphereChartBranchOverlapSwap_continuous i j).comp <|
          seededSphereChart_liftedOverlapDown_continuous i j⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the transported self-overlap on the
lifted chart family is still the whole chart. -/
lemma seededSphereChart_liftedOverlapOpen_self
    (i : SeededSphereNeighborhoodChart c₀) :
    seededSphereChart_liftedOverlapOpen i i = ⊤ := by
  ext z
  constructor
  · intro _hz
    trivial
  · intro _hz
    exact (mem_seededSphereChart_liftedOverlapOpen_iff (i := i) (j := i) (z := z)).2 <| by
      rw [seededSphereChartBranchOverlapOpen_self]
      trivial

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the lifted self-transition is the
identity. -/
lemma seededSphereChart_liftedOverlapTransition_id
    (i : SeededSphereNeighborhoodChart c₀) :
    ⇑(seededSphereChart_liftedOverlapTransition i i) = id := by
  funext x
  -- Lower to the original overlap, use the unlifted identity, then lift back.
  have hswap :
      seededSphereChartBranchOverlapSwap i i
          (seededSphereChart_liftedOverlapDown i i x) =
        seededSphereChart_liftedOverlapDown i i x := by
    simpa [seededSphereChartBranchOverlapTransition] using
      congrFun (seededSphereChartBranchOverlapTransition_id (i := i))
        (seededSphereChart_liftedOverlapDown i i x)
  change seededSphereChart_liftedOverlapUp i i
      (seededSphereChartBranchOverlapSwap i i
        (seededSphereChart_liftedOverlapDown i i x)) = x
  rw [hswap]
  exact seededSphereChart_liftedOverlapUp_down i i x

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: lowering the lifted transition
recovers the original target-overlap transport exactly. -/
lemma seededSphereChart_liftedTransition_lower_eq
    {i j : SeededSphereNeighborhoodChart c₀}
    (x : seededSphereChart_liftedOverlapOpen i j) :
    seededSphereChart_liftedOverlapDown j i
        ((seededSphereChart_liftedOverlapTransition i j) x) =
      seededSphereChartBranchOverlapSwap i j
        (seededSphereChart_liftedOverlapDown i j x) := by
  -- Lowering cancels the final lift in the definition of the lifted transition.
  apply Subtype.ext
  rfl

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: overlap transitivity on the lifted
chart family reduces to the already proved unlifted transitivity after lowering. -/
lemma seededSphereChart_liftedOverlapOpen_trans
    {i j : SeededSphereNeighborhoodChart c₀}
    (k : SeededSphereNeighborhoodChart c₀) (x : seededSphereChart_liftedOverlapOpen i j)
    (hx : ((x : seededSphereChart_liftedOverlapOpen i j) :
        seededSphereChart_liftedTargetSpace i) ∈
      seededSphereChart_liftedOverlapOpen i k) :
    (((↑) : seededSphereChart_liftedOverlapOpen j i →
          seededSphereChart_liftedTargetSpace j)
      ((seededSphereChart_liftedOverlapTransition i j) x)) ∈
      seededSphereChart_liftedOverlapOpen j k := by
  have hx_down :
      ((seededSphereChart_liftedOverlapDown i j x :
          seededSphereChartBranchOverlapOpen i j) : i.chart.target) ∈
        seededSphereChartBranchOverlapOpen i k := by
    -- Lower the second overlap hypothesis to the original chart family.
    simpa [seededSphereChart_liftedOverlapDown,
      mem_seededSphereChart_liftedOverlapOpen_iff] using hx
  have htrans :
      ((seededSphereChartBranchOverlapSwap i j
          (seededSphereChart_liftedOverlapDown i j x) :
            seededSphereChartBranchOverlapOpen j i) : j.chart.target) ∈
        seededSphereChartBranchOverlapOpen j k :=
    seededSphereChartBranchOverlapOpen_trans (i := i) (j := j) k
      (seededSphereChart_liftedOverlapDown i j x) hx_down
  let y : seededSphereChart_liftedOverlapOpen j i :=
    seededSphereChart_liftedOverlapTransition i j x
  have hlower :
      (seededSphereChart_targetSpace j).uliftFunctorObjHomeo.symm
          (y : seededSphereChart_liftedTargetSpace j) =
        ((seededSphereChartBranchOverlapSwap i j
            (seededSphereChart_liftedOverlapDown i j x) :
              seededSphereChartBranchOverlapOpen j i) : j.chart.target) := by
    -- The lowering rewrite eliminates the `ULift` transport boundary.
    simpa [seededSphereChart_liftedOverlapDown] using
      congrArg (fun y : seededSphereChartBranchOverlapOpen j i ↦ (y : j.chart.target))
        (seededSphereChart_liftedTransition_lower_eq (i := i) (j := j) x)
  -- Re-express lifted membership as lowered membership and close with the unlifted transitivity.
  exact (mem_seededSphereChart_liftedOverlapOpen_iff
    (i := j) (j := k) (z := (y : seededSphereChart_liftedTargetSpace j))).2 <| by
    simpa [hlower] using htrans

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the lowered intermediate point in
the lifted cocycle is exactly the original overlap-transported point on the unlifted chart
family. -/
lemma seededSphereChart_liftedCocycleInput_down_eq
    {i j k : SeededSphereNeighborhoodChart c₀}
    (x : seededSphereChart_liftedOverlapOpen i j)
    (hx : ((x : seededSphereChart_liftedOverlapOpen i j) :
        seededSphereChart_liftedTargetSpace i) ∈
      seededSphereChart_liftedOverlapOpen i k)
    (hx_down :
      ((seededSphereChart_liftedOverlapDown i j x :
          seededSphereChartBranchOverlapOpen i j) : i.chart.target) ∈
        seededSphereChartBranchOverlapOpen i k) :
    let xji : seededSphereChart_liftedOverlapOpen j i :=
      seededSphereChart_liftedOverlapTransition i j x
    seededSphereChart_liftedOverlapDown j k
        ⟨(xji : seededSphereChart_liftedTargetSpace j),
          seededSphereChart_liftedOverlapOpen_trans (i := i) (j := j) (k := k) x hx⟩ =
      ⟨((seededSphereChartBranchOverlapSwap i j
            (seededSphereChart_liftedOverlapDown i j x) :
              seededSphereChartBranchOverlapOpen j i) : j.chart.target),
        seededSphereChartBranchOverlapOpen_trans (i := i) (j := j) (k := k)
          (seededSphereChart_liftedOverlapDown i j x) hx_down⟩ := by
  dsimp
  -- Lowering the nested lifted input only changes the proof component.
  apply Subtype.ext
  simpa [seededSphereChart_liftedOverlapDown] using
    congrArg (fun y : seededSphereChartBranchOverlapOpen j i ↦ (y : j.chart.target))
      (seededSphereChart_liftedTransition_lower_eq (i := i) (j := j) x)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the lifted overlap transitions satisfy
the same cocycle identity as the original target-overlap transports. -/
lemma seededSphereChart_liftedOverlapTransition_cocycle
    (i j k : SeededSphereNeighborhoodChart c₀) (x : seededSphereChart_liftedOverlapOpen i j)
    (hx : ((x : seededSphereChart_liftedOverlapOpen i j) :
        seededSphereChart_liftedTargetSpace i) ∈
      seededSphereChart_liftedOverlapOpen i k) :
    (((↑) : seededSphereChart_liftedOverlapOpen k j → seededSphereChart_liftedTargetSpace k)
        (seededSphereChart_liftedOverlapTransition j k
          ⟨((show seededSphereChart_liftedOverlapOpen j i from
                seededSphereChart_liftedOverlapTransition i j x) :
              seededSphereChart_liftedTargetSpace j),
            seededSphereChart_liftedOverlapOpen_trans (i := i) (j := j) (k := k) x hx⟩)) =
      ((↑) : seededSphereChart_liftedOverlapOpen k i → seededSphereChart_liftedTargetSpace k)
        (seededSphereChart_liftedOverlapTransition i k
          ⟨((show seededSphereChart_liftedOverlapOpen i j from x) :
              seededSphereChart_liftedTargetSpace i), hx⟩) := by
  let x_down : seededSphereChartBranchOverlapOpen i j :=
    seededSphereChart_liftedOverlapDown i j x
  have hx_down :
      ((x_down : seededSphereChartBranchOverlapOpen i j) : i.chart.target) ∈
        seededSphereChartBranchOverlapOpen i k := by
    -- Lower the third-overlap hypothesis before appealing to the original cocycle.
    simpa [x_down, seededSphereChart_liftedOverlapDown,
      mem_seededSphereChart_liftedOverlapOpen_iff] using hx
  let xji : seededSphereChart_liftedOverlapOpen j i :=
    seededSphereChart_liftedOverlapTransition i j x
  let y : seededSphereChart_liftedOverlapOpen j k :=
    ⟨(xji : seededSphereChart_liftedTargetSpace j),
      seededSphereChart_liftedOverlapOpen_trans (i := i) (j := j) (k := k) x hx⟩
  let z : seededSphereChart_liftedOverlapOpen i k :=
    ⟨((show seededSphereChart_liftedOverlapOpen i j from x) :
        seededSphereChart_liftedTargetSpace i), hx⟩
  let lhs : seededSphereChart_liftedOverlapOpen k j :=
    seededSphereChart_liftedOverlapTransition j k y
  let rhs : seededSphereChart_liftedOverlapOpen k i :=
    seededSphereChart_liftedOverlapTransition i k z
  apply (seededSphereChart_targetSpace k).uliftFunctorObjHomeo.symm.injective
  have hleft_lower :
      (seededSphereChart_targetSpace k).uliftFunctorObjHomeo.symm
          (lhs : seededSphereChart_liftedTargetSpace k) =
        ((seededSphereChartBranchOverlapSwap j k
            (seededSphereChart_liftedOverlapDown j k y) :
              seededSphereChartBranchOverlapOpen k j) : k.chart.target) := by
    -- Lower the outer left transition to the original chart transport.
    simpa [lhs, seededSphereChart_liftedOverlapDown] using
      congrArg (fun q : seededSphereChartBranchOverlapOpen k j ↦ (q : k.chart.target))
        (seededSphereChart_liftedTransition_lower_eq (i := j) (j := k) y)
  have hright_lower :
      (seededSphereChart_targetSpace k).uliftFunctorObjHomeo.symm
          (rhs : seededSphereChart_liftedTargetSpace k) =
        ((seededSphereChartBranchOverlapSwap i k
            (seededSphereChart_liftedOverlapDown i k z) :
              seededSphereChartBranchOverlapOpen k i) : k.chart.target) := by
    -- The right branch lowers in the same way.
    simpa [rhs, seededSphereChart_liftedOverlapDown] using
      congrArg (fun q : seededSphereChartBranchOverlapOpen k i ↦ (q : k.chart.target))
        (seededSphereChart_liftedTransition_lower_eq (i := i) (j := k) z)
  have hy_down :
      seededSphereChart_liftedOverlapDown j k y =
        ⟨((seededSphereChartBranchOverlapSwap i j x_down :
              seededSphereChartBranchOverlapOpen j i) : j.chart.target),
          seededSphereChartBranchOverlapOpen_trans (i := i) (j := j) (k := k)
            x_down hx_down⟩ := by
    -- Normalize the nested left input before invoking the unlifted cocycle theorem.
    simpa [x_down, y] using
      seededSphereChart_liftedCocycleInput_down_eq (i := i) (j := j) (k := k) x hx hx_down
  have hz_down :
      seededSphereChart_liftedOverlapDown i k z =
        ⟨(x_down : i.chart.target), hx_down⟩ := by
    -- The right input is lowered by forgetting only the extra universe lift.
    simpa [x_down, z, seededSphereChart_liftedOverlapDown]
  have hcocycle :
      ((seededSphereChartBranchOverlapSwap j k
          (seededSphereChart_liftedOverlapDown j k y) :
            seededSphereChartBranchOverlapOpen k j) : k.chart.target) =
        ((seededSphereChartBranchOverlapSwap i k
          (seededSphereChart_liftedOverlapDown i k z) :
            seededSphereChartBranchOverlapOpen k i) : k.chart.target) := by
    -- After lowering the intermediate point, the statement is exactly the original cocycle.
    rw [hy_down, hz_down]
    simpa [x_down] using
      seededSphereChartBranchOverlapTransition_cocycle (i := i) (j := j) (k := k) x_down hx_down
  exact hleft_lower.trans (hcocycle.trans hright_lower.symm)

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the universe-stable gluing core for
the seeded chart family. -/
noncomputable def seededSphereChart_liftedGlueDataCore :
    TopCat.GlueData.MkCore where
  J := SeededSphereNeighborhoodChart c₀
  U := seededSphereChart_liftedTargetSpace
  V := seededSphereChart_liftedOverlapOpen
  t := seededSphereChart_liftedOverlapTransition
  V_id := seededSphereChart_liftedOverlapOpen_self
  t_id := seededSphereChart_liftedOverlapTransition_id
  t_inter := fun {i j} k x hx ↦
    seededSphereChart_liftedOverlapOpen_trans (i := i) (j := j) k x hx
  cocycle := fun i j k x hx ↦
    seededSphereChart_liftedOverlapTransition_cocycle i j k x hx

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the seeded chart family and its
identity-on-coordinate overlap transitions package into topological gluing data. -/
noncomputable def seededSphereChart_liftedGlueData :
    TopCat.GlueData :=
  TopCat.GlueData.mk' (seededSphereChart_liftedGlueDataCore (c₀ := c₀))

end

end Cartan
