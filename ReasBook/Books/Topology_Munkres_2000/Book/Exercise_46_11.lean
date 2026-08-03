module

public import Topology_Munkres_2000.Book.Exercise_46_11.FineTopology
public import Topology_Munkres_2000.Book.Exercise_43_8.UniformTopology
public import Topology_Munkres_2000.Book.Definition_19_1.BoxTopology
public import Topology_Munkres_2000.Book.Theorem_19_1.Basis

universe u v

public section

namespace FineContinuousMap

variable (X : Type u) (Y : Type v) [TopologicalSpace X] [PseudoMetricSpace Y]

/-- Helper for Exercise 46.11: a point in two fine balls has a fine ball contained in their
intersection. -/
private lemma exists_ball_subset_inter (f₁ f₂ h : FineContinuousMap X Y)
    (δ₁ δ₂ : C(X, ℝ))
    (hh : h ∈ ball X Y f₁ δ₁ ∩ ball X Y f₂ δ₂) :
    ∃ ρ : C(X, ℝ), (∀ x, 0 < ρ x) ∧ h ∈ ball X Y h ρ ∧
      ball X Y h ρ ⊆ ball X Y f₁ δ₁ ∩ ball X Y f₂ δ₂ := by
  -- Subtract the distance already used at the new center, then take the smaller margin.
  have hρContinuous : Continuous (fun x ↦
      (δ₁ x - dist (f₁ x) (h x)) ⊓ (δ₂ x - dist (f₂ x) (h x))) :=
    (δ₁.continuous.sub
      ((equivContinuousMap X Y f₁).continuous.dist (equivContinuousMap X Y h).continuous)).inf
      (δ₂.continuous.sub
        ((equivContinuousMap X Y f₂).continuous.dist (equivContinuousMap X Y h).continuous))
  let ρ : C(X, ℝ) :=
    ⟨fun x ↦ (δ₁ x - dist (f₁ x) (h x)) ⊓ (δ₂ x - dist (f₂ x) (h x)), hρContinuous⟩
  have hρPositive : ∀ x, 0 < ρ x := by
    intro x
    rw [show ρ x = (δ₁ x - dist (f₁ x) (h x)) ⊓
      (δ₂ x - dist (f₂ x) (h x)) by rfl, lt_inf_iff]
    constructor
    · exact sub_pos.mpr ((mem_ball X Y f₁ h δ₁).mp hh.1 x)
    · exact sub_pos.mpr ((mem_ball X Y f₂ h δ₂).mp hh.2 x)
  refine ⟨ρ, hρPositive, ?_, ?_⟩
  · -- The new center lies in its ball because every remaining margin is positive.
    apply (mem_ball X Y h h ρ).mpr
    intro x
    simpa only [dist_self] using hρPositive x
  · -- The triangle inequality spends at most the chosen remaining margin.
    intro g hg
    constructor
    · apply (mem_ball X Y f₁ g δ₁).mpr
      intro x
      have hρ₁ : ρ x ≤ δ₁ x - dist (f₁ x) (h x) := inf_le_left
      have hTriangle := dist_triangle (f₁ x) (h x) (g x)
      linarith [(mem_ball X Y h g ρ).mp hg x]
    · apply (mem_ball X Y f₂ g δ₂).mpr
      intro x
      have hρ₂ : ρ x ≤ δ₂ x - dist (f₂ x) (h x) := inf_le_right
      have hTriangle := dist_triangle (f₂ x) (h x) (g x)
      linarith [(mem_ball X Y h g ρ).mp hg x]

/-- The basis assertion in Exercise 46.11: positive continuous variable-radius balls form a
basis for the fine topology on continuous maps from `X` to `Y`. -/
theorem basis_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis (basis X Y) := by
  -- The remaining-margin construction supplies the intersection-refinement field.
  refine ⟨?_, ?_, topology_eq_generateFrom X Y⟩
  · intro U hU V hV h hUV
    obtain ⟨f₁, δ₁, hδ₁, rfl⟩ := (mem_basis_iff X Y U).mp hU
    obtain ⟨f₂, δ₂, hδ₂, rfl⟩ := (mem_basis_iff X Y V).mp hV
    obtain ⟨ρ, hρ, hhρ, hsub⟩ :=
      exists_ball_subset_inter X Y f₁ f₂ h δ₁ δ₂ hUV
    exact ⟨ball X Y h ρ, (mem_basis_iff X Y _).mpr ⟨h, ρ, hρ, rfl⟩, hhρ, hsub⟩
  · -- Constant radius one gives a basis set through every map.
    apply Set.sUnion_eq_univ_iff.mpr
    intro f
    let δ : C(X, ℝ) := ContinuousMap.const X 1
    have hδ : ∀ x, 0 < δ x := by
      intro x
      exact zero_lt_one
    refine ⟨ball X Y f δ, (mem_basis_iff X Y _).mpr ⟨f, δ, hδ, rfl⟩, ?_⟩
    apply (mem_ball X Y f f δ).mpr
    intro x
    simpa only [dist_self] using hδ x

/-- Helper for Exercise 46.11: the uniform topology has its induced normal form on the exposed
fine-map synonym. -/
private lemma uniformTopology_eq_induced_equivContinuousMap :
    ContinuousMap.uniformTopology X Y =
      TopologicalSpace.induced
        (fun g : FineContinuousMap X Y ↦ UniformFun.ofFun (equivContinuousMap X Y g))
        (UniformFun.topologicalSpace X Y) := by
  -- Compare the two inducing maps pointwise through the owner computation theorem.
  rw [ContinuousMap.uniformTopology_def]
  congr 1 with g
  exact congrArg (fun h : C(X, Y) ↦ UniformFun.ofFun (h : X → Y))
    (equivContinuousMap_eq X Y g).symm

/-- Helper for Exercise 46.11: uniform-convergence neighborhoods have a basis of positive
constant-radius pointwise balls. -/
private lemma uniformTopology_hasBasis_constBalls (f : FineContinuousMap X Y) :
    (@nhds (FineContinuousMap X Y) (ContinuousMap.uniformTopology X Y) f).HasBasis
      (fun ε : ℝ ↦ 0 < ε)
      (fun ε ↦ {g : FineContinuousMap X Y | ∀ x, dist (f x) (g x) < ε}) := by
  -- Rewrite once to the induced topology and pull back the metric uniformity basis.
  rw [uniformTopology_eq_induced_equivContinuousMap X Y, nhds_induced]
  -- Pull back the metric uniformity basis and normalize its pointwise membership condition.
  let hUniform := (UniformFun.hasBasis_nhds_of_basis X Y
    (UniformFun.ofFun (equivContinuousMap X Y f)) Metric.uniformity_basis_dist).comap
      (fun g : FineContinuousMap X Y ↦ UniformFun.ofFun (equivContinuousMap X Y g))
  exact hUniform.to_hasBasis
    (fun ε hε ↦ ⟨ε, hε, fun g hg x ↦ hg x⟩)
    (fun ε hε ↦ ⟨ε, hε, fun g hg x ↦ hg x⟩)

/-- Helper for Exercise 46.11: a fine ball with constant radius is the corresponding
pointwise uniform ball. -/
private lemma constFineBall_eq (f : FineContinuousMap X Y) (ε : ℝ) :
    ball X Y f (ContinuousMap.const X ε) =
      {g : FineContinuousMap X Y | ∀ x, dist (f x) (g x) < ε} := by
  -- Unfold only membership and evaluation of the constant continuous radius.
  ext g
  simp only [mem_ball, ContinuousMap.const_apply, Set.mem_setOf_eq]

/-- The uniform-containment assertion in Exercise 46.11: the fine topology contains the
uniform topology. -/
theorem fine_le_uniform :
    topologicalSpace X Y ≤ ContinuousMap.uniformTopology X Y := by
  -- Refine each positive constant-radius uniform neighborhood by the equal fine basic ball.
  rw [le_iff_nhds]
  intro f
  have hFine := (basis_isTopologicalBasis X Y).nhds_hasBasis (a := f)
  have hUniform := uniformTopology_hasBasis_constBalls X Y f
  apply (hFine.le_basis_iff hUniform).mpr
  intro ε hε
  let δ : C(X, ℝ) := ContinuousMap.const X ε
  refine ⟨ball X Y f δ, ?_, ?_⟩
  · constructor
    · exact (mem_basis_iff X Y _).mpr ⟨f, δ, fun _ ↦ hε, rfl⟩
    · apply (mem_ball X Y f f δ).mpr
      intro x
      simpa only [δ, ContinuousMap.const_apply, dist_self] using hε
  · rw [constFineBall_eq X Y f ε]

/-- Helper for Exercise 46.11: on a compact domain, a fine ball around a contained point
contains a positive constant-radius ball around that point. -/
private lemma exists_constBall_subset_ball_of_compact [CompactSpace X]
    (f h : FineContinuousMap X Y) (δ : C(X, ℝ))
    (hh : h ∈ ball X Y f δ) :
    ∃ ε : ℝ, 0 < ε ∧
      {g : FineContinuousMap X Y | ∀ x, dist (h x) (g x) < ε} ⊆ ball X Y f δ := by
  -- Compactness gives a uniform positive lower bound for the unused pointwise margin.
  have hMarginContinuous : Continuous (fun x ↦ δ x - dist (f x) (h x)) :=
    δ.continuous.sub
      ((equivContinuousMap X Y f).continuous.dist (equivContinuousMap X Y h).continuous)
  have hMarginPositive : ∀ x ∈ (Set.univ : Set X), 0 < δ x - dist (f x) (h x) := by
    intro x hx
    exact sub_pos.mpr ((mem_ball X Y f h δ).mp hh x)
  obtain ⟨ε, hε, hεLower⟩ :=
    isCompact_univ.exists_forall_le' hMarginContinuous.continuousOn hMarginPositive
  refine ⟨ε, hε, ?_⟩
  intro g hg
  apply (mem_ball X Y f g δ).mpr
  intro x
  have hTriangle := dist_triangle (f x) (h x) (g x)
  have hLower := hεLower x (Set.mem_univ x)
  linarith [hg x]

/-- Exercise 46.11 (3): On a compact domain, the fine and uniform topologies agree. -/
theorem fine_eq_uniform_of_compact [CompactSpace X] :
    topologicalSpace X Y = ContinuousMap.uniformTopology X Y := by
  -- The forward comparison is general; compactness supplies constant-radius refinements back.
  refine le_antisymm (fine_le_uniform X Y) ?_
  apply (@le_iff_nhds (FineContinuousMap X Y)
    (ContinuousMap.uniformTopology X Y) (topologicalSpace X Y)).mpr
  intro f
  have hUniform := uniformTopology_hasBasis_constBalls X Y f
  have hFine := (basis_isTopologicalBasis X Y).nhds_hasBasis (a := f)
  apply (hUniform.le_basis_iff hFine).mpr
  intro U hU
  obtain ⟨h, δ, hδ, rfl⟩ := (mem_basis_iff X Y U).mp hU.1
  obtain ⟨ε, hε, hsub⟩ :=
    exists_constBall_subset_ball_of_compact X Y h f δ hU.2
  exact ⟨ε, hε, hsub⟩

/- Exercise 46.11 (4): On a discrete domain, continuous maps are equivalent to all functions. -/
#check equivFnOfDiscrete

/-- Helper for Exercise 46.11: neighborhoods in the induced box topology are generated by
preimages of basic open boxes. -/
private lemma inducedBox_hasBasis [DiscreteTopology X] (f : FineContinuousMap X Y) :
    (@nhds (FineContinuousMap X Y)
      (TopologicalSpace.induced (equivFnOfDiscrete X Y)
        (Pi.boxTopologicalSpace (fun _ : X ↦ Y))) f).HasBasis
      (fun U : Set (X → Y) ↦
        U ∈ Pi.boxBasis (fun _ : X ↦ Y) ∧ equivFnOfDiscrete X Y f ∈ U)
      (fun U ↦ (equivFnOfDiscrete X Y) ⁻¹' U) := by
  -- Install the two explicit topology normal forms while deriving the transported basis.
  letI : TopologicalSpace (X → Y) := Pi.boxTopologicalSpace (fun _ : X ↦ Y)
  letI : TopologicalSpace (FineContinuousMap X Y) :=
    TopologicalSpace.induced (equivFnOfDiscrete X Y)
      (Pi.boxTopologicalSpace (fun _ : X ↦ Y))
  exact ((Pi.isTopologicalBasis_boxBasis.induced (equivFnOfDiscrete X Y)).nhds_hasBasis
    (a := f)).to_hasBasis
      (fun V hV ↦ by
        obtain ⟨U, hU, rfl⟩ := hV.1
        exact ⟨U, ⟨hU, hV.2⟩, subset_rfl⟩)
      (fun U hU ↦
        ⟨(equivFnOfDiscrete X Y) ⁻¹' U, ⟨⟨U, hU.1, rfl⟩, hU.2⟩, subset_rfl⟩)

/-- Helper for Exercise 46.11: every variable-radius fine ball is open in the induced box
topology on a discrete domain. -/
private lemma fineBall_isOpen_inducedBox [DiscreteTopology X]
    (f : FineContinuousMap X Y) (δ : C(X, ℝ)) :
    @IsOpen (FineContinuousMap X Y)
      (TopologicalSpace.induced (equivFnOfDiscrete X Y)
        (Pi.boxTopologicalSpace (fun _ : X ↦ Y))) (ball X Y f δ) := by
  -- Represent the fine ball as the preimage of the box of coordinate metric balls.
  let U : X → Set Y := fun x ↦ Metric.ball (f x) (δ x)
  have hUOpen : ∀ x, IsOpen (U x) := fun x ↦ Metric.isOpen_ball
  have hBall : ball X Y f δ = (equivFnOfDiscrete X Y) ⁻¹' Set.pi Set.univ U := by
    ext g
    simp only [mem_ball, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
      equivFnOfDiscrete_apply, U, Metric.mem_ball, dist_comm]
  rw [hBall]
  letI : TopologicalSpace (X → Y) := Pi.boxTopologicalSpace (fun _ : X ↦ Y)
  letI : TopologicalSpace (FineContinuousMap X Y) :=
    TopologicalSpace.induced (equivFnOfDiscrete X Y)
      (Pi.boxTopologicalSpace (fun _ : X ↦ Y))
  exact (continuous_induced_dom : Continuous (equivFnOfDiscrete X Y)).isOpen_preimage _
    (Pi.isOpen_box U hUOpen)

/-- Helper for Exercise 46.11: every basic box around a fine continuous map on a discrete
domain contains a positive variable-radius fine ball. -/
private lemma exists_fineBall_subset_boxBasis [DiscreteTopology X]
    (f : FineContinuousMap X Y) (U : Set (X → Y))
    (hU : U ∈ Pi.boxBasis (fun _ : X ↦ Y)) (hfU : equivFnOfDiscrete X Y f ∈ U) :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧
      ball X Y f δ ⊆ (equivFnOfDiscrete X Y) ⁻¹' U := by
  classical
  -- Choose a metric radius independently in each open coordinate of the basic box.
  obtain ⟨V, hVOpen, rfl⟩ := (Pi.mem_boxBasis U).mp hU
  have hfV : ∀ x, f x ∈ V x := by
    intro x
    rw [← equivFnOfDiscrete_apply X Y f x]
    exact hfU x (Set.mem_univ x)
  choose ε hε hεSub using
    fun x ↦ (Metric.isOpen_iff.mp (hVOpen x)) (f x) (hfV x)
  let δ : C(X, ℝ) := ⟨ε, continuous_of_discreteTopology⟩
  refine ⟨δ, hε, ?_⟩
  -- Discreteness makes the selected coordinate radii continuous.
  intro g hg x hx
  apply hεSub x
  have hgx := (mem_ball X Y f g δ).mp hg x
  rw [equivFnOfDiscrete_apply X Y g x]
  exact (dist_comm _ _).trans_lt (show dist (f x) (g x) < ε x from hgx)

/-- The discrete-domain assertion in Exercise 46.11: the fine topology agrees with the box
topology. -/
theorem fine_eq_box_of_discrete [DiscreteTopology X] :
    topologicalSpace X Y =
      TopologicalSpace.induced (equivFnOfDiscrete X Y)
        (Pi.boxTopologicalSpace (fun _ : X ↦ Y)) := by
  -- Compare the fine and transported box neighborhood bases in both directions.
  apply le_antisymm
  · rw [le_iff_nhds]
    intro f
    have hFineBasis := (basis_isTopologicalBasis X Y).nhds_hasBasis (a := f)
    have hBoxBasis := inducedBox_hasBasis X Y f
    apply (hFineBasis.le_basis_iff hBoxBasis).mpr
    intro U hU
    obtain ⟨δ, hδ, hsub⟩ := exists_fineBall_subset_boxBasis X Y f U hU.1 hU.2
    refine ⟨ball X Y f δ, ?_, hsub⟩
    constructor
    · exact (mem_basis_iff X Y _).mpr ⟨f, δ, hδ, rfl⟩
    · apply (mem_ball X Y f f δ).mpr
      intro x
      simpa only [dist_self] using hδ x
  · rw [le_iff_nhds]
    intro f
    have hBoxBasis := inducedBox_hasBasis X Y f
    have hFineBasis := (basis_isTopologicalBasis X Y).nhds_hasBasis (a := f)
    apply (hBoxBasis.le_basis_iff hFineBasis).mpr
    intro U hU
    obtain ⟨h, δ, hδ, rfl⟩ := (mem_basis_iff X Y U).mp hU.1
    have hOpen := fineBall_isOpen_inducedBox X Y h δ
    have hfBall : f ∈ ball X Y h δ := hU.2
    have hNhds : ball X Y h δ ∈
        @nhds (FineContinuousMap X Y)
          (TopologicalSpace.induced (equivFnOfDiscrete X Y)
            (Pi.boxTopologicalSpace (fun _ : X ↦ Y))) f := by
      exact @IsOpen.mem_nhds (FineContinuousMap X Y)
        (TopologicalSpace.induced (equivFnOfDiscrete X Y)
          (Pi.boxTopologicalSpace (fun _ : X ↦ Y))) f (ball X Y h δ) hOpen hfBall
    exact hBoxBasis.mem_iff.mp hNhds

end FineContinuousMap
