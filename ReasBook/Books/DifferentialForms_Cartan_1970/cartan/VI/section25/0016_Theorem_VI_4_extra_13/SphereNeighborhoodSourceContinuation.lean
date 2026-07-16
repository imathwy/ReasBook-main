import DifferentialForms_Cartan_1970.cartan.VI.section25.«0016_Theorem_VI_4_extra_13».OpenSphereUniformization

universe u

open scoped Complex.UnitDisc Manifold
open Filter

section

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: every point of a one-dimensional
complex manifold has a neighborhood biholomorphic to an open subset of the Riemann sphere. -/
lemma point_has_riemannSphere_chartNeighborhood
    {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (x : X) :
    ∃ U : TopologicalSpace.Opens X, x ∈ U ∧
      ∃ V : TopologicalSpace.Opens RiemannSphere,
        Nonempty (U ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ V) := by
  let f : OpenPartialHomeomorph RiemannSphere X :=
    RiemannSphere.affineOpenPartialHomeomorph.trans (chartAt ℂ x).symm
  have h_affine_to :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.affineOpenPartialHomeomorph
        RiemannSphere.affineOpenPartialHomeomorph.source := by
    -- The forward affine chart is the preferred sphere chart on the finite locus.
    simpa [RiemannSphere.chartAt_coe, extChartAt_coe, Function.comp]
      using contMDiffOn_extChartAt (I := 𝓘(ℂ)) (x := ((0 : ℂ) : RiemannSphere))
  have h_affine_inv :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 RiemannSphere.affineOpenPartialHomeomorph.symm
        RiemannSphere.affineOpenPartialHomeomorph.target := by
    -- The inverse affine chart is the inverse preferred sphere chart at the same base point.
    simpa [RiemannSphere.chartAt_coe, extChartAt_coe_symm, Function.comp]
      using contMDiffOn_extChartAt_symm (I := 𝓘(ℂ)) (x := ((0 : ℂ) : RiemannSphere))
  have h_chart_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (chartAt ℂ x) (chartAt ℂ x).source := by
    -- The chosen chart of `X` is smooth on its source by the charted-manifold axioms.
    simpa [extChartAt_coe, Function.comp] using
      contMDiffOn_extChartAt (I := 𝓘(ℂ)) (x := x)
  have h_chart_inv :
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 (chartAt ℂ x).symm (chartAt ℂ x).target := by
    -- Its inverse branch is smooth on the chart target for the same reason.
    simpa [extChartAt_coe_symm, Function.comp] using
      contMDiffOn_extChartAt_symm (I := 𝓘(ℂ)) (x := x)
  have h_to : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f f.source := by
    -- Compose the sphere affine chart with the inverse preferred chart around `x`.
    simpa [f, OpenPartialHomeomorph.trans_apply, Function.comp_def,
      OpenPartialHomeomorph.trans_source, Set.preimage_inter, Set.inter_assoc,
      Set.inter_left_comm, Set.inter_comm] using
      h_chart_inv.comp' h_affine_to
  have h_inv : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) 1 f.symm f.target := by
    -- The inverse composition is smooth by reversing the same two chart branches.
    simpa [f, OpenPartialHomeomorph.trans_apply, Function.comp_def,
      OpenPartialHomeomorph.trans_target, Set.preimage_inter, Set.inter_assoc,
      Set.inter_left_comm, Set.inter_comm] using
      h_affine_inv.comp' h_chart_to
  let U : TopologicalSpace.Opens X := ⟨f.target, f.open_target⟩
  let V : TopologicalSpace.Opens RiemannSphere := ⟨f.source, f.open_source⟩
  have hxU : x ∈ U := by
    -- The base point lies in the target because its chart coordinate is a finite complex number.
    change x ∈ (RiemannSphere.affineOpenPartialHomeomorph.trans (chartAt ℂ x).symm).target
    rw [OpenPartialHomeomorph.trans_target]
    refine ⟨by simp, ?_⟩
    simpa using Set.mem_univ ((chartAt ℂ x) x)
  have hVU : Nonempty (V ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ U) := by
    -- Package the local branch as a biholomorphism between the source and target open subsets.
    simpa [U, V] using
      openPartialHomeomorph_toComplexManifoldEquivSourceTarget (f := f) h_to h_inv
  rcases hVU with ⟨e⟩
  -- Invert the packaged local equivalence so the neighborhood of `x` is the source-facing side.
  exact ⟨U, hxU, V, ⟨e.symm⟩⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a local sphere chart on `X`,
packaged by its source and target open subsets and the corresponding biholomorphic equivalence. -/
structure SphereNeighborhoodChart
    (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] where
  source : TopologicalSpace.Opens X
  target : TopologicalSpace.Opens RiemannSphere
  equiv : source ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ target

namespace SphereNeighborhoodChart

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the inverse branch attached to a
local sphere chart. -/
noncomputable def branch (c : SphereNeighborhoodChart X) : c.target → X :=
  fun z ↦ c.equiv.symm z

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the forward coordinate map attached to
a local sphere chart. -/
noncomputable def coord (c : SphereNeighborhoodChart X) : c.source → RiemannSphere :=
  fun x ↦ c.equiv x

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the inverse branch of a local sphere
chart is holomorphic. -/
lemma branch_mdifferentiable (c : SphereNeighborhoodChart X) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c.branch) := by
  -- Forget the source subtype only after composing the inverse branch with the subtype inclusion.
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val ∘ c.equiv.symm)
  simpa [Function.comp] using
    (contMDiff_subtype_val.comp c.equiv.symm.contMDiff_toFun).mdifferentiable one_ne_zero

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the forward coordinate map of a local
sphere chart is holomorphic. -/
lemma coord_mdifferentiable (c : SphereNeighborhoodChart X) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c.coord) := by
  -- Again, first forget the target subtype and then apply the smoothness of the equivalence.
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val ∘ c.equiv)
  simpa [Function.comp] using
    (contMDiff_subtype_val.comp c.equiv.contMDiff_toFun).mdifferentiable one_ne_zero

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the inverse branch lands back in the
source open of the packaged chart. -/
lemma branch_mem_source (c : SphereNeighborhoodChart X) (z : c.target) :
    c.branch z ∈ c.source := by
  -- This is just the subtype witness carried by the inverse branch.
  exact (c.equiv.symm z).2

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: evaluating the inverse branch at the
forward coordinate of a point recovers the original point. -/
lemma branch_coord (c : SphereNeighborhoodChart X) (x : c.source) :
    c.branch (c.equiv x) = x := by
  -- This is the left-inverse law of the local biholomorphism.
  simpa [branch] using c.equiv.symm_apply_apply x

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: evaluating the forward coordinate at
the inverse branch of a point recovers the original sphere point. -/
lemma coord_branch (c : SphereNeighborhoodChart X) (z : c.target) :
    c.coord ⟨c.branch z, c.branch_mem_source z⟩ = z := by
  -- This is the right-inverse law of the local biholomorphism.
  simpa [coord, branch] using c.equiv.apply_symm_apply z

end SphereNeighborhoodChart

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: lift an open subset of an open
submanifold back to an ambient open subset. This is the basic subtype-transport bridge needed
when local inverse data is produced inside a chart target subtype. -/
def ambientOpenOfOpenSubset
    {Y : Type*} [TopologicalSpace Y]
    (U : TopologicalSpace.Opens Y) (V : TopologicalSpace.Opens U) :
    TopologicalSpace.Opens Y :=
  ⟨Subtype.val '' (V : Set U),
    -- The subtype inclusion of an open subset is an open embedding, so its image is open.
    U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ V.isOpen⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a point lies in the ambient lift of
an open subset `V : Opens U` exactly when its ambient representative belongs to `U` and then to
`V`. -/
@[simp] lemma mem_ambientOpenOfOpenSubset
    {Y : Type*} [TopologicalSpace Y]
    {U : TopologicalSpace.Opens Y} {V : TopologicalSpace.Opens U} {y : Y} :
    y ∈ ambientOpenOfOpenSubset U V ↔
      ∃ hyU : y ∈ U, (⟨y, hyU⟩ : U) ∈ V := by
  constructor
  · intro hy
    rcases hy with ⟨z, hzV, rfl⟩
    exact ⟨z.2, hzV⟩
  · rintro ⟨hyU, hyV⟩
    exact ⟨⟨y, hyU⟩, hyV, rfl⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: when a point is already known in a
open subset `V : Opens U`, the subtype `V` is biholomorphic to its ambient image
`ambientOpenOfOpenSubset U V`. This is the stable transport step needed before reparameterizing a
chart target by a local inverse branch. -/
noncomputable def ambientOpenOfOpenSubsetEquiv
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
    (U : TopologicalSpace.Opens Y) (V : TopologicalSpace.Opens U) :
    ambientOpenOfOpenSubset U V ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ V := by
  let A := ambientOpenOfOpenSubset U V
  let toAmbient : V → A := fun z ↦ ⟨z.1.1, ⟨z.1, z.2, rfl⟩⟩
  let toSubtype : A → V := fun y ↦
    let hy : ∃ hyU : y.1 ∈ U, (⟨y.1, hyU⟩ : U) ∈ V :=
      (mem_ambientOpenOfOpenSubset (U := U) (V := V) (y := y.1)).1 y.2
    ⟨⟨y.1, hy.1⟩, hy.2⟩
  have hAtoU : A ≤ U := by
    intro y hy
    exact (mem_ambientOpenOfOpenSubset (U := U) (V := V) (y := y)).1 hy |>.1
  refine
    { toEquiv :=
        { toFun := toSubtype
          invFun := toAmbient
          left_inv := ?_
          right_inv := ?_ }
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · intro y
    -- The inverse map only forgets the existential witness carried by the ambient-open point.
    apply Subtype.ext
    rfl
  · intro z
    -- Re-expanding the ambient-image witness recovers the original point of `V`.
    apply Subtype.ext
    rfl
  · -- The forward map is the open-submanifold inclusion `A ↪ U`, then repackaged into `V`.
    have hToU : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ toSubtype) := by
      simpa [toSubtype, Function.comp, TopologicalSpace.Opens.inclusion] using
        (contMDiff_inclusion (I := 𝓘(ℂ)) (n := 1) hAtoU)
    exact
      (contMDiff_subtypeValComp_iff (Z := A) (Y := U) (U := V) (f := toSubtype)).mp hToU
  · -- The inverse map is the composition of the two subtype inclusions into the ambient manifold.
    have hToY : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ toAmbient) := by
      have hVtoU : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : V → U) := contMDiff_subtype_val
      have hUtoY : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : U → Y) := contMDiff_subtype_val
      simpa [toAmbient, Function.comp] using hUtoY.comp hVtoU
    exact
      (contMDiff_subtypeValComp_iff (Z := V) (Y := Y) (U := A) (f := toAmbient)).mp hToY

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: restricting a packaged local sphere
chart `d` to a smaller target open `W : Opens d.target` yields a new packaged chart whose source
and target are the corresponding ambient opens in `X` and `RiemannSphere`. This separates the
ambient-open transport from the later local-inverse reparameterization step. -/
noncomputable def sphereNeighborhoodChart_restrictTarget
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (d : SphereNeighborhoodChart X) (W : TopologicalSpace.Opens d.target) :
    SphereNeighborhoodChart X := by
  let Vsrc : TopologicalSpace.Opens d.source :=
    ⟨{x | d.equiv x ∈ W}, by
      -- The restricted source is the target-preimage of `W` under the chart map.
      simpa using W.isOpen.preimage d.equiv.toHomeomorph.continuous_toFun⟩
  let eVW : Vsrc ≃ₘ^1⟮𝓘(ℂ), 𝓘(ℂ)⟯ W := by
    let toTarget : Vsrc → W := fun x ↦ ⟨d.equiv x.1, x.2⟩
    let toSource : W → Vsrc := fun z ↦
      ⟨d.equiv.symm z.1, by
        change d.equiv (d.equiv.symm z.1) ∈ W
        simpa using z.2⟩
    refine
      { toEquiv :=
          { toFun := toTarget
            invFun := toSource
            left_inv := ?_
            right_inv := ?_ }
        contMDiff_toFun := ?_
        contMDiff_invFun := ?_ }
    · intro x
      -- Restricting and then applying the inverse chart recovers the original source point.
      apply Subtype.ext
      simpa [toSource, toTarget] using d.equiv.symm_apply_apply x.1
    · intro z
      -- Dually, the forward chart map recovers the original restricted target point.
      apply Subtype.ext
      simpa [toSource, toTarget] using d.equiv.apply_symm_apply z.1
    · -- The forward restricted chart map is just `d.equiv` precomposed with the source inclusion.
      have hToTargetAmbient : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ toTarget) := by
        have hsub : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : Vsrc → d.source) := contMDiff_subtype_val
        change ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (fun x : Vsrc ↦ d.equiv x.1)
        exact d.equiv.contMDiff_toFun.comp hsub
      exact
        (contMDiff_subtypeValComp_iff (Z := Vsrc) (Y := d.target) (U := W)
          (f := toTarget)).mp hToTargetAmbient
    · -- The inverse restricted chart map is `d.equiv.symm` precomposed with the target inclusion.
      have hToSourceAmbient : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ toSource) := by
        have hsub : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : W → d.target) := contMDiff_subtype_val
        change ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (fun z : W ↦ d.equiv.symm z.1)
        exact d.equiv.symm.contMDiff_toFun.comp hsub
      exact
        (contMDiff_subtypeValComp_iff (Z := W) (Y := d.source) (U := Vsrc)
          (f := toSource)).mp hToSourceAmbient
  -- Package the restricted source/target with the ambient-open transport on both sides.
  exact
    { source := ambientOpenOfOpenSubset d.source Vsrc
      target := ambientOpenOfOpenSubset d.target W
      equiv :=
        (ambientOpenOfOpenSubsetEquiv d.source Vsrc).trans
          (eVW.trans (ambientOpenOfOpenSubsetEquiv d.target W).symm) }

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: if a chart branch is literally the
seed branch on a subset of the seed target, then the chart source stays inside the seed source.
This records why a too-rigid seed-coordinate normalization cannot by itself globalize beyond the
original seed chart. -/
lemma SphereNeighborhoodChart.source_subset_of_branch_eq_seed
    {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ c : SphereNeighborhoodChart X}
    (ht : (c.target : Set RiemannSphere) ⊆ c₀.target)
    (hbranch :
      ∀ z : c.target, c.branch z = c₀.branch ⟨z.1, ht z.2⟩) :
    (c.source : Set X) ⊆ c₀.source := by
  intro x hx
  let z : c.target := c.equiv ⟨x, hx⟩
  have hx_eq :
      x = c₀.branch ⟨z.1, ht z.2⟩ := by
    -- Rewrite `x` through the local inverse branch and then replace that branch by the seed one.
    calc
      x = c.branch z := by
        simpa [z] using (c.branch_coord ⟨x, hx⟩).symm
      _ = c₀.branch ⟨z.1, ht z.2⟩ := hbranch z
  -- The seed branch always lands in the seed chart source.
  exact hx_eq ▸ c₀.branch_mem_source ⟨z.1, ht z.2⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: every point of `X` admits a packaged
local sphere chart. -/
lemma point_has_sphereNeighborhoodChart
    {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (x : X) :
    ∃ c : SphereNeighborhoodChart X, x ∈ c.source := by
  -- Repackage the already proved neighborhood equivalence into the theorem-local chart owner.
  rcases point_has_riemannSphere_chartNeighborhood (X := X) x with ⟨U, hxU, V, hUV⟩
  rcases hUV with ⟨e⟩
  exact ⟨⟨U, V, e⟩, hxU⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on a preconnected complex manifold,
two holomorphic maps that agree near one point already agree everywhere. -/
lemma mdifferentiable_eq_of_eventuallyEq
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) 1 Z]
    [PreconnectedSpace Z]
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {f g : Z → X} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    {z : Z} (hfg : f =ᶠ[nhds z] g) :
    f = g := by
  let D : Set Z := {x : Z | f =ᶠ[nhds x] g}
  have hD_open : IsOpen D := by
    -- Local coincidence is itself an open condition on the source manifold.
    simpa [D] using (local_coincidence_set_isOpen (f := f) (g := g))
  have hD_nonempty : D.Nonempty := ⟨z, hfg⟩
  have hEqOn : Set.EqOn f g D := by
    -- A neighborhood-wise equality specializes to pointwise equality at the center point.
    intro x hx
    change f =ᶠ[nhds x] g at hx
    exact hx.eq_of_nhds
  -- Apply the chapter's global identity theorem to the nonempty open coincidence set.
  exact MDifferentiable.eq_of_eqOn_nonempty_open hf hg hD_open hD_nonempty hEqOn

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on the connected component of a point
in an open subset of the sphere, local agreement of two holomorphic branches propagates to the
whole component. -/
lemma mdifferentiable_eqOn_connectedComponent_of_eventuallyEq
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {U : TopologicalSpace.Opens RiemannSphere}
    {f g : U → X}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (z : U) (hnear : f =ᶠ[nhds z] g) :
    Set.EqOn f g (connectedComponentIn (Set.univ : Set U) z) := by
  letI : LocallyConnectedSpace RiemannSphere := ChartedSpace.locallyConnectedSpace ℂ RiemannSphere
  letI : LocallyConnectedSpace U := U.isOpen.locallyConnectedSpace
  let C : TopologicalSpace.Opens U :=
    ⟨connectedComponentIn (Set.univ : Set U) z, isOpen_univ.connectedComponentIn⟩
  let j : C → U := fun w ↦ w.1
  have hj : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) j := by
    -- The connected component sits as an open submanifold of `U`, so its inclusion is smooth.
    exact (contMDiff_subtype_val : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 j).mdifferentiable one_ne_zero
  letI : PreconnectedSpace C := Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  have hEq : f ∘ j = g ∘ j := by
    -- Restrict both branches to the connected component and invoke the preconnected identity
    -- theorem proved just above.
    exact
      mdifferentiable_eq_of_eventuallyEq (hf := hf.comp hj) (hg := hg.comp hj)
        (z := ⟨z, mem_connectedComponentIn (by simp)⟩)
        (hnear.comp_tendsto continuous_subtype_val.continuousAt)
  -- Evaluate the equality of restricted maps at each point of the connected component.
  intro w hw
  exact congrArg (fun h : C → X ↦ h ⟨w, hw⟩) hEq

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: two holomorphic inverse branches on
overlapping open subsets of the sphere agree on the whole connected overlap component once they
agree near one point of that overlap. -/
lemma sphereContinuationBranchEqOfOverlap
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {W1 W2 : TopologicalSpace.Opens RiemannSphere}
    {b1 : W1 → X} {b2 : W2 → X}
    (hb1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b1)
    (hb2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b2)
    (z : {w : RiemannSphere | w ∈ (W1 : Set RiemannSphere) ∩ (W2 : Set RiemannSphere)})
    (hnear :
      (fun w : {w : RiemannSphere | w ∈ (W1 : Set RiemannSphere) ∩ (W2 : Set RiemannSphere)} ↦
        b1 ⟨w.1, w.2.1⟩) =ᶠ[nhds z]
      (fun w ↦ b2 ⟨w.1, w.2.2⟩)) :
    Set.EqOn
      (fun w : {w : RiemannSphere | w ∈ (W1 : Set RiemannSphere) ∩ (W2 : Set RiemannSphere)} ↦
        b1 ⟨w.1, w.2.1⟩)
      (fun w ↦ b2 ⟨w.1, w.2.2⟩)
      (connectedComponentIn
        (Set.univ :
          Set {w : RiemannSphere | w ∈ (W1 : Set RiemannSphere) ∩ (W2 : Set RiemannSphere)}) z) := by
  let common : TopologicalSpace.Opens RiemannSphere :=
    ⟨(W1 : Set RiemannSphere) ∩ (W2 : Set RiemannSphere), W1.isOpen.inter W2.isOpen⟩
  let i1 : common → W1 := fun w ↦ ⟨w.1, w.2.1⟩
  let i2 : common → W2 := fun w ↦ ⟨w.1, w.2.2⟩
  let f : common → X := b1 ∘ i1
  let g : common → X := b2 ∘ i2
  have hi1ambient : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ i1) := by
    -- Forgetting the `W1`-subtype turns the comparison map into the ambient subtype inclusion.
    simpa [i1, Function.comp] using
      (contMDiff_subtype_val : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : common → RiemannSphere))
  have hi1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) i1 := by
    have hcont : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 i1 := by
      exact
        (contMDiff_subtypeValComp_iff (Z := common) (Y := RiemannSphere) (U := W1)
          (f := i1)).mp hi1ambient
    exact hcont.mdifferentiable one_ne_zero
  have hi2ambient : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val ∘ i2) := by
    -- The right overlap inclusion is treated identically.
    simpa [i2, Function.comp] using
      (contMDiff_subtype_val : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 (Subtype.val : common → RiemannSphere))
  have hi2 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) i2 := by
    have hcont : ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1 i2 := by
      exact
        (contMDiff_subtypeValComp_iff (Z := common) (Y := RiemannSphere) (U := W2)
          (f := i2)).mp hi2ambient
    exact hcont.mdifferentiable one_ne_zero
  have hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := hb1.comp hi1
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := hb2.comp hi2
  -- Reduce the overlap statement to the single-domain connected-component lemma.
  simpa [common, f, g, i1, i2] using
    mdifferentiable_eqOn_connectedComponent_of_eventuallyEq (hf := hf) (hg := hg) (z := z) hnear

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: if two packaged local sphere charts
have inverse branches that agree near one point of a common target coordinate, then the agreement
propagates to the whole connected overlap component. -/
lemma SphereNeighborhoodChart.branch_eqOn_connectedOverlap_of_eventuallyEq
    {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₁ c₂ : SphereNeighborhoodChart X}
    (z :
      {w : RiemannSphere |
        w ∈ (c₁.target : Set RiemannSphere) ∩ (c₂.target : Set RiemannSphere)})
    (hnear :
      (fun w :
          {w : RiemannSphere |
            w ∈ (c₁.target : Set RiemannSphere) ∩ (c₂.target : Set RiemannSphere)} ↦
        c₁.branch ⟨w.1, w.2.1⟩) =ᶠ[nhds z]
      (fun w ↦ c₂.branch ⟨w.1, w.2.2⟩)) :
    Set.EqOn
      (fun w :
          {w : RiemannSphere |
            w ∈ (c₁.target : Set RiemannSphere) ∩ (c₂.target : Set RiemannSphere)} ↦
        c₁.branch ⟨w.1, w.2.1⟩)
      (fun w ↦ c₂.branch ⟨w.1, w.2.2⟩)
      (connectedComponentIn
        (Set.univ :
          Set {w : RiemannSphere |
            w ∈ (c₁.target : Set RiemannSphere) ∩ (c₂.target : Set RiemannSphere)}) z) := by
  -- The packaged chart API reduces the statement to the previously proved raw branch lemma.
  simpa [SphereNeighborhoodChart.branch] using
    sphereContinuationBranchEqOfOverlap
      (X := X)
      (hb1 := SphereNeighborhoodChart.branch_mdifferentiable c₁)
      (hb2 := SphereNeighborhoodChart.branch_mdifferentiable c₂)
      (z := z) hnear

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a one-step continuation witness
between two packaged local sphere charts. The witness records one common sphere coordinate where
the two inverse branches agree near that coordinate, which is the exact data needed for an
identity transition in the later gluing argument. -/
structure SphereNeighborhoodChartOverlap
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c₁ c₂ : SphereNeighborhoodChart X) where
  point :
    {w : RiemannSphere | w ∈ (c₁.target : Set RiemannSphere) ∩ (c₂.target : Set RiemannSphere)}
  branch_eq_near :
    (fun w :
        {w : RiemannSphere | w ∈ (c₁.target : Set RiemannSphere) ∩ (c₂.target : Set RiemannSphere)} ↦
      c₁.branch ⟨w.1, w.2.1⟩) =ᶠ[nhds point]
    (fun w ↦ c₂.branch ⟨w.1, w.2.2⟩)

namespace SphereNeighborhoodChartOverlap

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X]
variable {c₁ c₂ : SphereNeighborhoodChart X}

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: an overlap witness between two local
sphere charts produces an actual point of `X` contained in both chart sources. -/
lemma exists_common_source_point (h : SphereNeighborhoodChartOverlap c₁ c₂) :
    ∃ x : X, x ∈ c₁.source ∧ x ∈ c₂.source := by
  let z₁ : c₁.target := ⟨h.point.1, h.point.2.1⟩
  let z₂ : c₂.target := ⟨h.point.1, h.point.2.2⟩
  let x : X := c₁.branch z₁
  have hx₁ : x ∈ c₁.source := by
    -- The left branch already lands in the left chart source by construction.
    simpa [x, z₁] using c₁.branch_mem_source z₁
  have hEqOn :
      Set.EqOn
        (fun w :
            {w : RiemannSphere |
              w ∈ (c₁.target : Set RiemannSphere) ∩ (c₂.target : Set RiemannSphere)} ↦
          c₁.branch ⟨w.1, w.2.1⟩)
        (fun w ↦ c₂.branch ⟨w.1, w.2.2⟩)
        (connectedComponentIn
          (Set.univ :
            Set {w : RiemannSphere |
              w ∈ (c₁.target : Set RiemannSphere) ∩ (c₂.target : Set RiemannSphere)}) h.point) :=
    SphereNeighborhoodChart.branch_eqOn_connectedOverlap_of_eventuallyEq h.point h.branch_eq_near
  have hpoint_mem :
      h.point ∈ connectedComponentIn
        (Set.univ :
          Set {w : RiemannSphere |
            w ∈ (c₁.target : Set RiemannSphere) ∩ (c₂.target : Set RiemannSphere)}) h.point :=
    mem_connectedComponentIn (F := (Set.univ :
      Set {w : RiemannSphere |
        w ∈ (c₁.target : Set RiemannSphere) ∩ (c₂.target : Set RiemannSphere)}))
      (Set.mem_univ h.point)
  have hxEq : c₁.branch z₁ = c₂.branch z₂ := by
    -- The witness point lies in its own connected overlap component, so the propagated equality
    -- specializes there.
    have hxEq' := hEqOn (x := h.point) hpoint_mem
    simpa [z₁, z₂] using hxEq'
  have hx₂' : c₂.branch z₂ ∈ c₂.source := c₂.branch_mem_source z₂
  have hx₂ : x ∈ c₂.source := by
    -- Transport the right-source membership across the equality of the two branch values.
    simpa [x] using hxEq ▸ hx₂'
  exact ⟨x, hx₁, hx₂⟩

end SphereNeighborhoodChartOverlap

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the common source of two local sphere
charts, viewed as an open submanifold of `X`. This is the source-side domain on which coordinate
coincidence is later measured. -/
def sphereNeighborhoodChartCommonSource
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c₁ c₂ : SphereNeighborhoodChart X) : TopologicalSpace.Opens X :=
  c₁.source ⊓ c₂.source

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the left sphere coordinate restricted
to the common source of two local charts. -/
noncomputable def sphereNeighborhoodChartLeftCoord
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c₁ c₂ : SphereNeighborhoodChart X) :
    sphereNeighborhoodChartCommonSource c₁ c₂ → RiemannSphere :=
  fun x ↦ c₁.coord ⟨x.1, x.2.1⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the right sphere coordinate
restricted to the same common source. -/
noncomputable def sphereNeighborhoodChartRightCoord
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c₁ c₂ : SphereNeighborhoodChart X) :
    sphereNeighborhoodChartCommonSource c₁ c₂ → RiemannSphere :=
  fun x ↦ c₂.coord ⟨x.1, x.2.2⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a source-side continuation witness
between two local sphere charts. The witness records a common source point where the two
restricted sphere coordinates agree on some neighborhood inside the common source. -/
structure SphereNeighborhoodChartCoordContinuation
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c₁ c₂ : SphereNeighborhoodChart X) where
  point : sphereNeighborhoodChartCommonSource c₁ c₂
  coord_eq_near :
    sphereNeighborhoodChartLeftCoord c₁ c₂ =ᶠ[nhds point]
      sphereNeighborhoodChartRightCoord c₁ c₂

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the continuation family generated by
one seed sphere chart. A chart is reachable if it is the seed itself or is obtained from an
already reachable chart by one source-side coordinate continuation step. -/
inductive SeededSphereChartReachable
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c₀ : SphereNeighborhoodChart X) : SphereNeighborhoodChart X → Prop
  | seed : SeededSphereChartReachable c₀ c₀
  | step {c₁ c₂ : SphereNeighborhoodChart X} :
      SeededSphereChartReachable c₀ c₁ →
        SphereNeighborhoodChartCoordContinuation c₁ c₂ →
        SeededSphereChartReachable c₀ c₂

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a packaged local sphere chart together
with the explicit certificate that it belongs to the continuation family generated by the fixed
seed chart `c₀`. -/
structure SeededSphereNeighborhoodChart
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c₀ : SphereNeighborhoodChart X) where
  chart : SphereNeighborhoodChart X
  reachable : SeededSphereChartReachable c₀ chart

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the seed chart itself is the first
member of its continuation family. -/
def seededSphereNeighborhoodChart_seed
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c₀ : SphereNeighborhoodChart X) :
    SeededSphereNeighborhoodChart c₀ := by
  -- The generating continuation family contains its seed by definition.
  exact ⟨c₀, SeededSphereChartReachable.seed⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: one verified source-side
continuation step extends the seeded continuation family. -/
def seededSphereNeighborhoodChart_of_continuation
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₀ : SphereNeighborhoodChart X}
    (c : SeededSphereNeighborhoodChart c₀) {c' : SphereNeighborhoodChart X}
    (hstep : SphereNeighborhoodChartCoordContinuation c.chart c') :
    SeededSphereNeighborhoodChart c₀ := by
  -- Append the new source-side continuation step to the existing reachability certificate.
  exact ⟨c', SeededSphereChartReachable.step c.reachable hstep⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: every point already lying in the
seed chart source is covered by the seeded continuation family. This isolates the base segment of
the desired coverage theorem from the still-missing continuation refinement step. -/
lemma seededSphereNeighborhoodChart_exists_onSeedSource
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c₀ : SphereNeighborhoodChart X) :
    ∀ ⦃x : X⦄, x ∈ c₀.source → ∃ c : SeededSphereNeighborhoodChart c₀, x ∈ c.chart.source := by
  intro x hx
  -- The seed chart itself already covers every point of its own source.
  refine ⟨seededSphereNeighborhoodChart_seed c₀, ?_⟩
  change x ∈ c₀.source
  exact hx

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the source-side overlap relation of
two local sphere charts. A point of the common source lies in this set when the two local sphere
coordinates agree on some neighborhood of that point inside the common source. -/
def sphereNeighborhoodChartCoordOverlap
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c₁ c₂ : SphereNeighborhoodChart X) :
    Set (sphereNeighborhoodChartCommonSource c₁ c₂) :=
  {x | sphereNeighborhoodChartLeftCoord c₁ c₂ =ᶠ[nhds x]
      sphereNeighborhoodChartRightCoord c₁ c₂}

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: source-side coordinate coincidence is
an open condition on the common source. -/
lemma sphereNeighborhoodChartCoordOverlap_isOpen
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c₁ c₂ : SphereNeighborhoodChart X) :
    IsOpen (sphereNeighborhoodChartCoordOverlap c₁ c₂) := by
  -- On the fixed common-source subtype this is exactly Proposition 4.I (1).
  simpa [sphereNeighborhoodChartCoordOverlap] using
    (local_coincidence_set_isOpen
      (f := sphereNeighborhoodChartLeftCoord c₁ c₂)
      (g := sphereNeighborhoodChartRightCoord c₁ c₂))

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: both source-side coordinate
restrictions remain holomorphic on the common source. -/
lemma sphereNeighborhoodChartCommonCoord_mdifferentiable
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    (c₁ c₂ : SphereNeighborhoodChart X) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (sphereNeighborhoodChartLeftCoord c₁ c₂) ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (sphereNeighborhoodChartRightCoord c₁ c₂) := by
  have hleft_cont :
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1
        (TopologicalSpace.Opens.inclusion
          (show sphereNeighborhoodChartCommonSource c₁ c₂ ≤ c₁.source from inf_le_left)) :=
    contMDiff_inclusion (I := 𝓘(ℂ)) (n := 1)
      (show sphereNeighborhoodChartCommonSource c₁ c₂ ≤ c₁.source from inf_le_left)
  have hleft_inc :
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (TopologicalSpace.Opens.inclusion
          (show sphereNeighborhoodChartCommonSource c₁ c₂ ≤ c₁.source from inf_le_left)) :=
    hleft_cont.mdifferentiable one_ne_zero
  have hright_cont :
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) 1
        (TopologicalSpace.Opens.inclusion
          (show sphereNeighborhoodChartCommonSource c₁ c₂ ≤ c₂.source from inf_le_right)) :=
    contMDiff_inclusion (I := 𝓘(ℂ)) (n := 1)
      (show sphereNeighborhoodChartCommonSource c₁ c₂ ≤ c₂.source from inf_le_right)
  have hright_inc :
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
        (TopologicalSpace.Opens.inclusion
          (show sphereNeighborhoodChartCommonSource c₁ c₂ ≤ c₂.source from inf_le_right)) :=
    hright_cont.mdifferentiable one_ne_zero
  constructor
  · -- Restrict the left coordinate along the open inclusion of the common source.
    simpa [sphereNeighborhoodChartLeftCoord, Function.comp] using
      (SphereNeighborhoodChart.coord_mdifferentiable c₁).comp hleft_inc
  · -- The right coordinate is handled symmetrically.
    simpa [sphereNeighborhoodChartRightCoord, Function.comp] using
      (SphereNeighborhoodChart.coord_mdifferentiable c₂).comp hright_inc

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: source-side coordinate coincidence is
also closed on the common source, because the two coordinate restrictions are holomorphic. -/
lemma sphereNeighborhoodChartCoordOverlap_isClosed
    {X : Type u} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) 1 X]
    (c₁ c₂ : SphereNeighborhoodChart X) :
    IsClosed (sphereNeighborhoodChartCoordOverlap c₁ c₂) := by
  let hcoords := sphereNeighborhoodChartCommonCoord_mdifferentiable c₁ c₂
  -- Proposition 4.I (2) applies on the fixed common-source subtype.
  simpa [sphereNeighborhoodChartCoordOverlap] using
    holomorphic_local_coincidence_set_isClosed
      (f := sphereNeighborhoodChartLeftCoord c₁ c₂)
      (g := sphereNeighborhoodChartRightCoord c₁ c₂)
      hcoords.1 hcoords.2

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a point of the source-side overlap
locus is, in particular, a pointwise coincidence point of the two restricted coordinate maps. -/
lemma sphereNeighborhoodChartCoordEq_of_memCoordOverlap
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
    {c₁ c₂ : SphereNeighborhoodChart X}
    {x : sphereNeighborhoodChartCommonSource c₁ c₂}
    (hx : x ∈ sphereNeighborhoodChartCoordOverlap c₁ c₂) :
    sphereNeighborhoodChartLeftCoord c₁ c₂ x =
      sphereNeighborhoodChartRightCoord c₁ c₂ x := by
  -- Specializing the neighborhood equality at the center point gives ordinary equality.
  have hx' :
      sphereNeighborhoodChartLeftCoord c₁ c₂ =ᶠ[nhds x]
        sphereNeighborhoodChartRightCoord c₁ c₂ := by
    simpa [sphereNeighborhoodChartCoordOverlap] using hx
  exact hx'.eq_of_nhds

namespace SphereNeighborhoodChartCoordContinuation

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
variable {c₁ c₂ : SphereNeighborhoodChart X}

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: any point of the source-side overlap
locus packages to a continuation witness. -/
def ofMemCoordOverlap {x : sphereNeighborhoodChartCommonSource c₁ c₂}
    (hx : x ∈ sphereNeighborhoodChartCoordOverlap c₁ c₂) :
    SphereNeighborhoodChartCoordContinuation c₁ c₂ :=
  ⟨x, by simpa [sphereNeighborhoodChartCoordOverlap] using hx⟩

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a continuation witness gives an
actual point of the source-side overlap locus. -/
lemma memCoordOverlap (h : SphereNeighborhoodChartCoordContinuation c₁ c₂) :
    h.point ∈ sphereNeighborhoodChartCoordOverlap c₁ c₂ := by
  -- Specialize the witness neighborhood equality at its center point.
  simpa [sphereNeighborhoodChartCoordOverlap] using h.coord_eq_near

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: the two restricted coordinates already
agree pointwise at the witness point. -/
lemma coord_eq_at_point (h : SphereNeighborhoodChartCoordContinuation c₁ c₂) :
    sphereNeighborhoodChartLeftCoord c₁ c₂ h.point =
      sphereNeighborhoodChartRightCoord c₁ c₂ h.point := by
  -- The witness is a neighborhood equality, so evaluate it at the center point.
  exact h.coord_eq_near.eq_of_nhds

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: on a preconnected common source, one
continuation witness forces the two restricted coordinates to agree everywhere. -/
lemma coord_eq
    [T2Space X] [PreconnectedSpace (sphereNeighborhoodChartCommonSource c₁ c₂)]
    (h : SphereNeighborhoodChartCoordContinuation c₁ c₂) :
    sphereNeighborhoodChartLeftCoord c₁ c₂ =
      sphereNeighborhoodChartRightCoord c₁ c₂ := by
  have hOverlapUniv :
      sphereNeighborhoodChartCoordOverlap c₁ c₂ = Set.univ := by
    -- The overlap locus is clopen, and the witness supplies a nonempty point of it.
    apply IsClopen.eq_univ
    · exact
        ⟨sphereNeighborhoodChartCoordOverlap_isClosed (X := X) c₁ c₂,
          sphereNeighborhoodChartCoordOverlap_isOpen (X := X) c₁ c₂⟩
    · exact ⟨h.point, h.memCoordOverlap⟩
  ext x
  -- After the clopen argument, every common-source point lies in the overlap locus.
  have hx : x ∈ sphereNeighborhoodChartCoordOverlap c₁ c₂ := by
    simpa [hOverlapUniv]
  exact sphereNeighborhoodChartCoordEq_of_memCoordOverlap hx

/-- Helper for Cartan section25 0016_Theorem_VI_4_extra_13: a continuation witness propagates
coordinate equality across any chosen preconnected subset of the common source that contains the
witness point. This is the source-side uniqueness owner used when a later frontier argument works
on one fixed preconnected path image instead of the whole common source. -/
lemma coord_eqOnPreconnectedSubset
    [T2Space X]
    (h : SphereNeighborhoodChartCoordContinuation c₁ c₂)
    {W : Set (sphereNeighborhoodChartCommonSource c₁ c₂)}
    (hWpre : IsPreconnected W) (hpointW : h.point ∈ W) :
    Set.EqOn (sphereNeighborhoodChartLeftCoord c₁ c₂)
      (sphereNeighborhoodChartRightCoord c₁ c₂) W := by
  let A : Set W := Subtype.val ⁻¹' sphereNeighborhoodChartCoordOverlap c₁ c₂
  have hAopen : IsOpen A := by
    -- Restrict the common-source overlap locus to the chosen preconnected subset.
    simpa [A] using
      (sphereNeighborhoodChartCoordOverlap_isOpen (X := X) c₁ c₂).preimage continuous_subtype_val
  have hAclosed : IsClosed A := by
    -- The same restriction preserves closedness because the inclusion `W ↪ c₁.source ∩ c₂.source`
    -- is continuous.
    simpa [A] using
      (sphereNeighborhoodChartCoordOverlap_isClosed (X := X) c₁ c₂).preimage
        continuous_subtype_val
  letI : PreconnectedSpace W := Subtype.preconnectedSpace hWpre
  have hAnonempty : A.Nonempty := by
    -- The witness point already belongs to the restricted overlap locus.
    refine ⟨⟨h.point, hpointW⟩, ?_⟩
    exact h.memCoordOverlap
  have hAuniv : A = Set.univ := IsClopen.eq_univ ⟨hAclosed, hAopen⟩ hAnonempty
  intro y hy
  have hyA : (⟨y, hy⟩ : W) ∈ A := by
    simpa [A, hAuniv]
  -- Every point of the preconnected subset lies in the common-source overlap locus, so the two
  -- coordinates agree there pointwise.
  exact sphereNeighborhoodChartCoordEq_of_memCoordOverlap hyA

end SphereNeighborhoodChartCoordContinuation

end
