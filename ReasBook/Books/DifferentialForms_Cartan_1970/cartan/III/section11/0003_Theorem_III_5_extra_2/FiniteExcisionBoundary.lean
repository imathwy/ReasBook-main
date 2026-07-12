import DifferentialForms_Cartan_1970.III.section11.«0003_Theorem_III_5_extra_2».BoundaryCircleIntegrals
import DifferentialForms_Cartan_1970.III.section11.«0003_Theorem_III_5_extra_2».LocalResidueExcision

open scoped BigOperators Topology unitInterval

noncomputable section

universe u

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: the punctured owner's boundary family
consists of the original outer boundary components together with one clockwise circle for each
excised disc. -/
def finite_excision_boundary_family
    {ι : Type u} [Fintype ι] (Γ : ι → ClosedPath ℂ) (s : Finset ℂ) (ρ : ℂ → ℝ) :
    ι ⊕ s.attach → ClosedPath ℂ
  | Sum.inl i => Γ i
  | Sum.inr z => ((boundary_circle_path z.1 (ρ z.1)).symm).toClosedPath

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: summing a circle-integral expression
over `s.attach` is definitionally the same as summing it over `s`. -/
lemma sum_attach_circleIntegral_eq_sum
    {f : ℂ → ℂ} {s : Finset ℂ} {ρ : ℂ → ℝ} :
    (∑ z : s.attach, ∮ w in C(z.1, ρ z.1), f w) =
      Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := by
  calc
    (∑ z : s.attach, ∮ w in C(z.1, ρ z.1), f w) =
        Finset.sum s.attach.attach (fun z ↦ ∮ w in C(z.1.1, ρ z.1.1), f w) := by
          rw [Finset.univ_eq_attach]
    _ = Finset.sum s.attach (fun z ↦ ∮ w in C(z.1, ρ z.1), f w) := by
          exact (s.attach).sum_attach (fun z : ↥s ↦ ∮ w in C(z.1, ρ z.1), f w)
    _ = Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := by
          exact s.sum_attach (fun z ↦ ∮ w in C(z, ρ z), f w)

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: once the punctured owner has the
expected boundary family, its total boundary integral is the outer sum minus the positive inner
circle integrals. -/
lemma sum_curveIntegral_finite_excision_boundary_family
    {ι : Type u} [Fintype ι] (Γ : ι → ClosedPath ℂ) {f : ℂ → ℂ}
    (s : Finset ℂ) (ρ : ℂ → ℝ) :
    ∑ j, ∫ᶜ z in (finite_excision_boundary_family Γ s ρ j).toPath, (f dz) z =
      (∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z) -
        Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := by
  rw [Fintype.sum_sum_type]
  simp_rw [finite_excision_boundary_family,
    curveIntegral_clockwise_boundary_circle_eq_neg_circleIntegral]
  calc
    (∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z) +
        ∑ z : s.attach, -(∮ w in C(z.1, ρ z.1), f w) =
      (∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z) -
        ∑ z : s.attach, ∮ w in C(z.1, ρ z.1), f w := by
          rw [sub_eq_add_neg]
          congr 1
          simpa [Finset.univ_eq_attach] using
            (Finset.sum_neg_distrib
              (s := s.attach) (f := fun z : s.attach ↦ ∮ w in C(z.1, ρ z.1), f w)).symm
    _ = (∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z) -
        Finset.sum s (fun z ↦ ∮ w in C(z, ρ z), f w) := by
          rw [sum_attach_circleIntegral_eq_sum]

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: the explicit excision boundary family
already has pairwise disjoint path ranges once the outer boundary misses each excision disc and the
discs are pairwise disjoint. -/
lemma pairwiseDisjoint_ranges_finite_excision_boundary_family
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    {s : Finset ℂ} {ρ : ℂ → ℝ} (hΓ : IsOrientedBoundaryOf K Γ)
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    (hpair : ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w))) :
    Pairwise fun i j ↦
      Disjoint (Set.range ((finite_excision_boundary_family Γ s ρ i).toPath))
        (Set.range ((finite_excision_boundary_family Γ s ρ j).toPath)) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          have hij' : i ≠ j := by
            intro hEq
            apply hij
            exact congrArg Sum.inl hEq
          simpa [finite_excision_boundary_family] using hΓ.pairwiseDisjoint_ranges hij'
      | inr z =>
          have houter :
              Disjoint (Set.range (Γ i).toPath) (Metric.closedBall z.1.1 (ρ z.1.1)) :=
            boundary_path_disjoint_of_closedBall_subset_interior
              (Γ := Γ) hΓ (hball := hρK z.1.1 z.1.2) i
          refine houter.mono_right ?_
          intro w hw
          have hw' :
              w ∈ Set.range (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.toPath) := by
            simpa [finite_excision_boundary_family] using hw
          rw [range_clockwise_boundary_circle_toPath_eq_sphere (hρpos z.1.1 z.1.2)] at hw'
          exact Metric.sphere_subset_closedBall hw'
  | inr z =>
      cases j with
      | inl j =>
          have houter :
              Disjoint (Set.range (Γ j).toPath) (Metric.closedBall z.1.1 (ρ z.1.1)) :=
            boundary_path_disjoint_of_closedBall_subset_interior
              (Γ := Γ) hΓ (hball := hρK z.1.1 z.1.2) j
          have houter' :
              Disjoint (Set.range (Γ j).toPath)
                (Set.range (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.toPath)) :=
            houter.mono_right (by
              intro w hw
              rw [range_clockwise_boundary_circle_toPath_eq_sphere (hρpos z.1.1 z.1.2)] at hw
              exact Metric.sphere_subset_closedBall hw)
          simpa [finite_excision_boundary_family] using houter'.symm
      | inr w =>
          have hzw : z.1.1 ≠ w.1.1 := by
            intro hEq
            apply hij
            exact congrArg Sum.inr (Subtype.ext (Subtype.ext hEq))
          have hclosed :
              Disjoint (Metric.closedBall z.1.1 (ρ z.1.1)) (Metric.closedBall w.1.1 (ρ w.1.1)) :=
            hpair z.1.1 z.1.2 w.1.1 w.1.2 hzw
          have hzsubset :
              Set.range (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.toPath) ⊆
                Metric.closedBall z.1.1 (ρ z.1.1) := by
            intro u hu
            rw [range_clockwise_boundary_circle_toPath_eq_sphere (hρpos z.1.1 z.1.2)] at hu
            exact Metric.sphere_subset_closedBall hu
          have hwsubset :
              Set.range (((boundary_circle_path w.1.1 (ρ w.1.1)).symm).toClosedPath.toPath) ⊆
                Metric.closedBall w.1.1 (ρ w.1.1) := by
            intro u hu
            rw [range_clockwise_boundary_circle_toPath_eq_sphere (hρpos w.1.1 w.1.2)] at hu
            exact Metric.sphere_subset_closedBall hu
          have hdisj :
              Disjoint
                (Set.range (((boundary_circle_path z.1.1 (ρ z.1.1)).symm).toClosedPath.toPath))
                (Set.range (((boundary_circle_path w.1.1 (ρ w.1.1)).symm).toClosedPath.toPath)) :=
            hclosed.mono hzsubset hwsubset
          simpa [finite_excision_boundary_family] using hdisj

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: removing an open set from a closed
owner splits the frontier into the surviving owner frontier and the removed-set frontier inside the
owner. -/
lemma frontier_diff_open_of_isClosed {α : Type*} [TopologicalSpace α] {A W : Set α}
    (hA : IsClosed A) (hW : IsOpen W) :
    frontier (A \ W) = (frontier A \ W) ∪ (A ∩ frontier W) := by
  have hdiff : IsClosed (A \ W) := by
    simpa [Set.diff_eq] using hA.inter hW.isClosed_compl
  ext x
  constructor
  · intro hx
    rw [hdiff.frontier_eq, Set.mem_diff] at hx
    rcases hx with ⟨hxAW, hxnotIntAW⟩
    have hxA : x ∈ A := hxAW.1
    have hxW : x ∉ W := hxAW.2
    by_cases hxIntA : x ∈ interior A
    · right
      refine ⟨hxA, ?_⟩
      rw [hW.frontier_eq, Set.mem_diff]
      refine ⟨?_, hxW⟩
      have hxnotIntWc : x ∉ interior Wᶜ := by
        intro hxIntWc
        apply hxnotIntAW
        rw [Set.diff_eq, interior_inter]
        exact ⟨hxIntA, hxIntWc⟩
      by_contra hxClosureW
      apply hxnotIntWc
      rw [interior_compl]
      exact hxClosureW
    · left
      rw [Set.mem_diff, hA.frontier_eq, Set.mem_diff]
      exact ⟨⟨hxA, hxIntA⟩, hxW⟩
  · intro hx
    rcases hx with hx | hx
    · rw [Set.mem_diff, hA.frontier_eq, Set.mem_diff] at hx
      rcases hx with ⟨⟨hxA, hxnotIntA⟩, hxW⟩
      rw [hdiff.frontier_eq, Set.mem_diff]
      refine ⟨⟨hxA, hxW⟩, ?_⟩
      intro hxIntAW
      exact hxnotIntA ((interior_mono Set.diff_subset) hxIntAW)
    · rcases hx with ⟨hxA, hxFrontW⟩
      rw [hW.frontier_eq, Set.mem_diff] at hxFrontW
      rcases hxFrontW with ⟨hxClosureW, hxW⟩
      rw [hdiff.frontier_eq, Set.mem_diff]
      refine ⟨⟨hxA, hxW⟩, ?_⟩
      intro hxIntAW
      have hxnotIntWc : x ∉ interior Wᶜ := by
        rw [interior_compl]
        simpa [Set.mem_compl_iff] using hxClosureW
      apply hxnotIntWc
      exact (interior_mono (by
        intro y hy
        exact hy.2)) hxIntAW

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: removing one open ball from a closed
owner splits the frontier into the surviving outer frontier and the new boundary sphere. -/
lemma frontier_diff_ball_eq_of_closedBall_subset_interior
    {K : Set ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r) (hKclosed : IsClosed K)
    (hball : Metric.closedBall a r ⊆ interior K) :
    frontier (K \ Metric.ball a r) = frontier K ∪ Metric.sphere a r := by
  have hfrontier_disjoint : frontier K \ Metric.ball a r = frontier K := by
    ext z
    constructor
    · intro hz
      exact hz.1
    · intro hz
      refine ⟨hz, ?_⟩
      intro hzBall
      have hzInterior : z ∈ interior K := hball (Metric.ball_subset_closedBall hzBall)
      exact (Set.disjoint_left.1 disjoint_interior_frontier) hzInterior hz
  have hsphere_subset : Metric.sphere a r ⊆ K := by
    intro z hz
    exact interior_subset (hball (Metric.sphere_subset_closedBall hz))
  have hfrontier_ball :
      K ∩ frontier (Metric.ball a r) = Metric.sphere a r := by
    rw [frontier_ball a hr.ne']
    ext z
    constructor
    · intro hz
      exact hz.2
    · intro hz
      exact ⟨hsphere_subset hz, hz⟩
  rw [frontier_diff_open_of_isClosed hKclosed Metric.isOpen_ball, hfrontier_disjoint, hfrontier_ball]

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: if a closed excision disc is disjoint
from another closed disc already contained in `interior K`, then that second disc stays inside the
interior after the first open ball is removed. -/
lemma closedBall_subset_interior_diff_ball_of_disjoint
    {K : Set ℂ} {a z : ℂ} {ra rz : ℝ}
    (hzK : Metric.closedBall z rz ⊆ interior K)
    (hdisj : Disjoint (Metric.closedBall a ra) (Metric.closedBall z rz)) :
    Metric.closedBall z rz ⊆ interior (K \ Metric.ball a ra) := by
  intro w hw
  have hwInteriorK : w ∈ interior K := hzK hw
  have hwNotClosed : w ∉ Metric.closedBall a ra := by
    intro hwClosed
    exact Set.disjoint_left.1 hdisj hwClosed hw
  have hwBallCompl : (Metric.ball a ra)ᶜ ∈ 𝓝 w := by
    have hwClosedCompl : (Metric.closedBall a ra)ᶜ ∈ 𝓝 w :=
      Metric.isClosed_closedBall.isOpen_compl.mem_nhds hwNotClosed
    refine Filter.mem_of_superset hwClosedCompl ?_
    intro u hu
    exact fun huBall ↦ hu (Metric.ball_subset_closedBall huBall)
  rw [mem_interior_iff_mem_nhds] at hwInteriorK ⊢
  simpa [Set.diff_eq] using Filter.inter_mem hwInteriorK hwBallCompl

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: the reversed boundary circle is
globally `C¹`, hence piecewise differentiable just like the positive circle. -/
lemma boundary_circle_path_symm_isPiecewiseDifferentiable (a : ℂ) (r : ℝ) :
    (boundary_circle_path a r).symm.IsPiecewiseDifferentiable := by
  have hdiff : (boundary_circle_path a r).symm.IsDifferentiable := by
    rw [Path.IsDifferentiable]
    let g : ℝ → ℂ := fun t ↦ circleMap a r (2 * Real.pi * (1 - t))
    have hlin : ContDiff ℝ 1 (fun t : ℝ ↦ 2 * Real.pi * (1 - t)) := by
      fun_prop
    have hg : ContDiff ℝ 1 g := by
      simpa [g] using (contDiff_circleMap a r).comp hlin
    refine hg.contDiffOn.congr ?_
    intro t ht
    rw [Path.extend_apply ((boundary_circle_path a r).symm) ht]
    simp [boundary_circle_path, Path.symm, unitInterval.symm, g, sub_eq_add_neg, add_comm,
      mul_comm, mul_left_comm]
  exact hdiff.isPiecewiseDifferentiable

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: the clockwise boundary circle is
simple up to identifying its endpoints, exactly as for the counterclockwise circle. -/
lemma clockwise_boundary_circle_simple_eq_or_endpoints {a : ℂ} {r : ℝ} (hr : r ≠ 0)
    {s t : Set.Icc (0 : ℝ) 1}
    (h :
      (((boundary_circle_path a r).symm).toClosedPath.toPath) s =
        (((boundary_circle_path a r).symm).toClosedPath.toPath) t) :
    s = t ∨ (s, t) = ((0 : I), (1 : I)) ∨ (s, t) = ((1 : I), (0 : I)) := by
  have hsymm :
      (boundary_circle_path a r).symm s = (boundary_circle_path a r).symm t := by
    simpa [loop_toClosedPath_toPath_eq_cast] using h
  have hforward : boundary_circle_path a r (σ s) = boundary_circle_path a r (σ t) := by
    simpa [Path.symm] using hsymm
  rcases boundary_circle_path_simple_eq_or_endpoints (a := a) (r := r) hr hforward with
    hst | hst | hst
  · exact Or.inl (by simpa using congrArg σ hst)
  · right
    right
    have hs1 : s = (1 : I) := by
      apply unitInterval.symm_eq_zero.mp
      exact Subtype.ext hst.1
    have ht0 : t = (0 : I) := by
      apply unitInterval.symm_eq_one.mp
      exact Subtype.ext hst.2
    simpa [hs1, ht0]
  · right
    left
    have hs0 : s = (0 : I) := by
      apply unitInterval.symm_eq_one.mp
      exact Subtype.ext hst.1
    have ht1 : t = (1 : I) := by
      apply unitInterval.symm_eq_zero.mp
      exact Subtype.ext hst.2
    simpa [hs0, ht1]

/-- Helper for Cartan section11 0003_Theorem_III_5_extra_2: finite disjoint excision splits the
punctured owner's frontier into the original outer frontier together with the boundary spheres of
the removed discs. -/
lemma frontier_diff_iUnion_ball_eq_of_pairwise_disjoint_closedBall_subset_interior
    {K : Set ℂ} {s : Finset ℂ} {ρ : ℂ → ℝ} (hKclosed : IsClosed K)
    (hρpos : ∀ z ∈ s, 0 < ρ z)
    (hρK : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior K)
    (hpair : ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
      Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w))) :
    frontier (K \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z)) =
      frontier K ∪ ⋃ z ∈ (↑s : Set ℂ), Metric.sphere z (ρ z) := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hρpos' : ∀ z ∈ s, 0 < ρ z := by
        intro z hz
        exact hρpos z (by simp [hz])
      have hρK' : ∀ z ∈ s, Metric.closedBall z (ρ z) ⊆ interior (K \ Metric.ball a (ρ a)) := by
        intro z hz
        refine closedBall_subset_interior_diff_ball_of_disjoint (hρK z (by simp [hz])) ?_
        have hza : z ≠ a := by
          intro hza
          apply ha
          simpa [hza] using hz
        exact hpair a (by simp) z (by simp [hz]) hza.symm
      have hpair' :
          ∀ z ∈ s, ∀ w ∈ s, z ≠ w →
            Disjoint (Metric.closedBall z (ρ z)) (Metric.closedBall w (ρ w)) := by
        intro z hz w hw hzw
        exact hpair z (by simp [hz]) w (by simp [hw]) hzw
      have hclosed' : IsClosed (K \ Metric.ball a (ρ a)) := by
        simpa [Set.diff_eq] using hKclosed.inter Metric.isOpen_ball.isClosed_compl
      have hUnionBalls :
          (⋃ z ∈ (↑(insert a s) : Set ℂ), Metric.ball z (ρ z)) =
            Metric.ball a (ρ a) ∪ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z) := by
        ext x
        simp [Set.mem_iUnion, Finset.mem_insert, or_left_comm, or_assoc]
      have hUnionSpheres :
          (⋃ z ∈ (↑(insert a s) : Set ℂ), Metric.sphere z (ρ z)) =
            Metric.sphere a (ρ a) ∪ ⋃ z ∈ (↑s : Set ℂ), Metric.sphere z (ρ z) := by
        ext x
        simp [Set.mem_iUnion, Finset.mem_insert, or_left_comm, or_assoc]
      have hDiffExcision :
          K \ (Metric.ball a (ρ a) ∪ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z)) =
            (K \ Metric.ball a (ρ a)) \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z) := by
        ext x
        simp [Set.mem_diff, not_or, and_assoc, and_left_comm]
      calc
        frontier (K \ ⋃ z ∈ (↑(insert a s) : Set ℂ), Metric.ball z (ρ z)) =
            frontier ((K \ Metric.ball a (ρ a)) \ ⋃ z ∈ (↑s : Set ℂ), Metric.ball z (ρ z)) := by
              rw [hUnionBalls, hDiffExcision]
        _ =
            frontier (K \ Metric.ball a (ρ a)) ∪ ⋃ z ∈ (↑s : Set ℂ), Metric.sphere z (ρ z) :=
              ih hclosed' hρpos' hρK' hpair'
        _ =
            (frontier K ∪ Metric.sphere a (ρ a)) ∪
              ⋃ z ∈ (↑s : Set ℂ), Metric.sphere z (ρ z) := by
                rw [frontier_diff_ball_eq_of_closedBall_subset_interior
                  (hρpos a (by simp)) hKclosed (hρK a (by simp))]
        _ =
            frontier K ∪ ⋃ z ∈ (↑(insert a s) : Set ℂ), Metric.sphere z (ρ z) := by
                rw [hUnionSpheres]
                ext x
                simp [or_left_comm, or_assoc, or_comm]
