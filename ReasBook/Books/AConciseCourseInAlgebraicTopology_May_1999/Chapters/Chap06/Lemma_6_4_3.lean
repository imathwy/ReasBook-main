import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_4_1

universe u v

open Set
open Filter
open scoped unitInterval

/-- The product subspace `X × B ∪ A × Y ⊆ X × Y` associated to subsets `A ⊆ X` and `B ⊆ Y`. -/
def prodPairUnion {X : Type u} {Y : Type v} (A : Set X) (B : Set Y) : Set (X × Y) :=
  Set.univ ×ˢ B ∪ A ×ˢ Set.univ

@[simp] theorem mem_prodPairUnion {X : Type u} {Y : Type v} {A : Set X} {B : Set Y} {p : X × Y} :
    p ∈ prodPairUnion A B ↔ p.1 ∈ A ∨ p.2 ∈ B := by
  rcases p with ⟨x, y⟩
  simp [prodPairUnion, or_comm]

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

-- Semantic recall: Chapter 6 already formalizes NDR-pairs as the predicate `IsNDRPair A` on a
-- subspace `A ⊆ X`, so the product statement is expressed on the subset `prodPairUnion A B` of
-- `X × Y`.

/-- Helper for Lemma 6.4.3: the product control map vanishes exactly on `prodPairUnion A B`. -/
theorem prodControl_eq_zero_iff {A : Set X} {B : Set Y} (a : NDRPair A) (b : NDRPair B)
    (p : X × Y) :
    (((a.control.comp ContinuousMap.fst) ⊓ (b.control.comp ContinuousMap.snd)) p = 0) ↔
      p ∈ prodPairUnion A B := by
  -- The infimum control is the pointwise minimum, so one factor control must already vanish.
  rw [mem_prodPairUnion]
  constructor
  · intro hp
    by_cases hxy : a.control p.1 ≤ b.control p.2
    · left
      have hzero : a.control p.1 = 0 := by
        simpa [ContinuousMap.inf_apply, min_eq_left hxy] using hp
      exact (a.control_eq_zero_iff p.1).mp hzero
    · right
      have hyx : b.control p.2 ≤ a.control p.1 := le_of_not_ge hxy
      have hzero : b.control p.2 = 0 := by
        simpa [ContinuousMap.inf_apply, min_eq_right hyx] using hp
      exact (b.control_eq_zero_iff p.2).mp hzero
  · rintro (hpA | hpB)
    · have hzero : a.control p.1 = 0 := (a.control_eq_zero_iff p.1).2 hpA
      simp [ContinuousMap.inf_apply, hzero]
    · have hzero : b.control p.2 = 0 := (b.control_eq_zero_iff p.2).2 hpB
      simp [ContinuousMap.inf_apply, hzero]

/-- Helper for Lemma 6.4.3: the product control is `< 1` when at least one factor control is `< 1`.
-/
theorem prodControl_lt_one_iff {A : Set X} {B : Set Y} (a : NDRPair A) (b : NDRPair B)
    (p : X × Y) :
    (((a.control.comp ContinuousMap.fst) ⊓ (b.control.comp ContinuousMap.snd)) p < 1) ↔
      a.control p.1 < 1 ∨ b.control p.2 < 1 := by
  constructor
  · intro hp
    by_cases hx : a.control p.1 < 1
    · exact Or.inl hx
    · have hx' : a.control p.1 = 1 := by
        by_contra hne
        exact hx (lt_of_le_of_ne le_top hne)
      exact Or.inr <| by
        simpa [ContinuousMap.inf_apply, hx'] using hp
  · rintro (hx | hy)
    · exact lt_of_le_of_lt inf_le_left hx
    · exact lt_of_le_of_lt inf_le_right hy

/-- Helper for Lemma 6.4.3: when the left control is no larger than the right control, the
product deformation runs the left homotopy at full speed and scales the right homotopy. -/
private noncomputable def prodUnionLeftTime {A : Set X} {B : Set Y} (a : NDRPair A) (b : NDRPair B)
    (p : X × Y) (t : I) : I :=
  if _ : a.control p.1 ≤ b.control p.2 then
    t
  else
    projIcc 0 1 zero_le_one (((t : ℝ) * (b.control p.2 : ℝ)) / (a.control p.1 : ℝ))

/-- Helper for Lemma 6.4.3: when the right control is smaller, the product deformation runs the
right homotopy at full speed and scales the left homotopy. -/
private noncomputable def prodUnionRightTime {A : Set X} {B : Set Y} (a : NDRPair A) (b : NDRPair B)
    (p : X × Y) (t : I) : I :=
  if _ : a.control p.1 ≤ b.control p.2 then
    projIcc 0 1 zero_le_one (((t : ℝ) * (a.control p.1 : ℝ)) / (b.control p.2 : ℝ))
  else
    t

/-- Helper for Lemma 6.4.3: this is the source-style ratio-speed deformation before continuity is
packaged into a bundled homotopy. -/
private noncomputable def prodUnionRatioHomotopyFun {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) :
    I × (X × Y) → X × Y :=
  fun st ↦
    let t := st.1
    let p := st.2
    (a.homotopy (prodUnionLeftTime a b p t, p.1), b.homotopy (prodUnionRightTime a b p t, p.2))

/-- Helper for Lemma 6.4.3: the endpoint of the ratio-speed deformation is the map used for the
product NDR retract. -/
private noncomputable def prodUnionRatioEndpointFun {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) :
    X × Y → X × Y :=
  fun p ↦ prodUnionRatioHomotopyFun a b (1, p)

/-- Helper for Lemma 6.4.3: the ratio-speed deformation written in textbook square order
`(X × Y) × I → X × Y`. -/
private noncomputable def prodUnionRatioSquareFun {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) :
    (X × Y) × I → X × Y :=
  fun st ↦ prodUnionRatioHomotopyFun a b (st.2, st.1)

/-- Helper for Lemma 6.4.3: the ratio-speed deformation starts at the identity map on `X × Y`. -/
private theorem prodUnionRatioHomotopyFun_apply_zero {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) (p : X × Y) :
    prodUnionRatioHomotopyFun a b (0, p) = p := by
  -- At time `0`, both factor-time parameters collapse to `0`.
  rcases p with ⟨x, y⟩
  simp [prodUnionRatioHomotopyFun, prodUnionLeftTime, prodUnionRightTime]

/-- Helper for Lemma 6.4.3: evaluating the ratio-speed deformation at `t = 1` recovers its
endpoint map. -/
private theorem prodUnionRatioHomotopyFun_apply_one {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) (p : X × Y) :
    prodUnionRatioHomotopyFun a b (1, p) = prodUnionRatioEndpointFun a b p := by
  -- The endpoint map is defined as the time-`1` slice of the deformation.
  rfl

/-- Helper for Lemma 6.4.3: every stage of the ratio-speed deformation fixes
`prodPairUnion A B` pointwise. -/
private theorem prodUnionRatioHomotopyFun_eqOn_prodPairUnion {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) {p : X × Y} (hp : p ∈ prodPairUnion A B) (t : I) :
    prodUnionRatioHomotopyFun a b (t, p) = p := by
  -- Membership in the union means one factor control vanishes, so the other factor-time
  -- parameter collapses to `0` and the remaining factor is fixed by the relative homotopy.
  rcases p with ⟨x, y⟩
  rw [mem_prodPairUnion] at hp
  rcases hp with hxA | hyB
  · have hx0 : a.control x = 0 := (a.control_eq_zero_iff x).2 hxA
    have hxy : a.control x ≤ b.control y := by
      simp [hx0]
    ext
    · exact a.homotopy.eq_fst (prodUnionLeftTime a b (x, y) t) hxA
    · have hright : prodUnionRightTime a b (x, y) t = 0 := by
        simp [prodUnionRightTime, hx0]
      change b.homotopy (prodUnionRightTime a b (x, y) t, y) = y
      rw [hright, b.homotopy.apply_zero]
      simp
  · have hy0 : b.control y = 0 := (b.control_eq_zero_iff y).2 hyB
    by_cases hxy : a.control x ≤ b.control y
    · have hxle : a.control x ≤ 0 := by
        simpa [hy0] using hxy
      have hx0 : a.control x = 0 := le_antisymm hxle bot_le
      have hxA : x ∈ A := (a.control_eq_zero_iff x).1 hx0
      ext
      · exact a.homotopy.eq_fst (prodUnionLeftTime a b (x, y) t) hxA
      · exact b.homotopy.eq_fst (prodUnionRightTime a b (x, y) t) hyB
    · have hleft : prodUnionLeftTime a b (x, y) t = 0 := by
        have hxne0 : a.control x ≠ 0 := by
          intro hx0
          apply hxy
          simp [hx0, hy0]
        simp [prodUnionLeftTime, hy0, hxne0]
      ext
      · change a.homotopy (prodUnionLeftTime a b (x, y) t, x) = x
        rw [hleft, a.homotopy.apply_zero]
        simp
      · exact b.homotopy.eq_fst (prodUnionRightTime a b (x, y) t) hyB

/-- Helper for Lemma 6.4.3: the endpoint of the ratio-speed deformation also fixes
`prodPairUnion A B` pointwise. -/
private theorem prodUnionRatioEndpointFun_eqOn_prodPairUnion {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) {p : X × Y} (hp : p ∈ prodPairUnion A B) :
    prodUnionRatioEndpointFun a b p = p := by
  -- This is the relative fixedness lemma specialized to the final time `1`.
  simpa [prodUnionRatioEndpointFun] using prodUnionRatioHomotopyFun_eqOn_prodPairUnion a b hp 1

/-- Helper for Lemma 6.4.3: if the product control is `< 1`, then the endpoint of the ratio-speed
deformation lands in `prodPairUnion A B`. -/
private theorem prodUnionRatioEndpointFun_mem {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) (p : X × Y) :
    (((a.control.comp ContinuousMap.fst) ⊓ (b.control.comp ContinuousMap.snd)) p < 1) →
      prodUnionRatioEndpointFun a b p ∈ prodPairUnion A B := by
  -- Compare the two controls. The smaller one is `< 1`, and the larger-control branch forces the
  -- corresponding factor to reach its retract at time `1`.
  intro hp
  rcases p with ⟨x, y⟩
  rw [mem_prodPairUnion]
  have hlt := (prodControl_lt_one_iff a b (x, y)).1 hp
  by_cases hxy : a.control x ≤ b.control y
  · left
    have hxlt : a.control x < 1 := by
      rcases hlt with hxlt | hylt
      · exact hxlt
      · exact lt_of_le_of_lt hxy hylt
    simpa [prodUnionRatioEndpointFun, prodUnionRatioHomotopyFun, prodUnionLeftTime, hxy] using
      a.retract_mem_of_control_lt_one (x := x) hxlt
  · right
    have hyx : b.control y ≤ a.control x := le_of_not_ge hxy
    have hylt : b.control y < 1 := by
      rcases hlt with hxlt | hylt
      · exact lt_of_le_of_lt hyx hxlt
      · exact hylt
    simpa [prodUnionRatioEndpointFun, prodUnionRatioHomotopyFun, prodUnionRightTime, hxy] using
      b.retract_mem_of_control_lt_one (x := y) hylt

/-- Helper for Lemma 6.4.3: the square-order ratio-speed deformation starts at the identity map on
`X × Y`. -/
private theorem prodUnionRatioSquareFun_apply_zero {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) (p : X × Y) :
    prodUnionRatioSquareFun a b (p, 0) = p := by
  -- Swapping the product factors does not change the time-zero computation.
  simpa [prodUnionRatioSquareFun] using prodUnionRatioHomotopyFun_apply_zero a b p

/-- Helper for Lemma 6.4.3: the square-order ratio-speed deformation has the endpoint map
`prodUnionRatioEndpointFun a b` at time `1`. -/
private theorem prodUnionRatioSquareFun_apply_one {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) (p : X × Y) :
    prodUnionRatioSquareFun a b (p, 1) = prodUnionRatioEndpointFun a b p := by
  -- The time-one slice is the same endpoint map after swapping the square coordinates.
  simpa [prodUnionRatioSquareFun] using prodUnionRatioHomotopyFun_apply_one a b p

/-- Helper for Lemma 6.4.3: every time slice of the square-order ratio-speed deformation fixes
`prodPairUnion A B` pointwise. -/
private theorem prodUnionRatioSquareFun_eqOn_prodPairUnion {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) {p : X × Y} (hp : p ∈ prodPairUnion A B) (t : I) :
    prodUnionRatioSquareFun a b (p, t) = p := by
  -- The square-order formulation is just the previous relative fixedness lemma with the factors
  -- swapped.
  simpa [prodUnionRatioSquareFun] using prodUnionRatioHomotopyFun_eqOn_prodPairUnion a b hp t

/-- Helper for Lemma 6.4.3: once the square-order ratio-speed map is known to be continuous, the
remaining product NDR data packages formally into a relative homotopy and endpoint map. -/
private theorem prodUnionHomotopyRelAndEndpoint_ofContinuousSquareMap {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B)
    (hcont : Continuous (prodUnionRatioSquareFun a b)) :
    ∃ r : C(X × Y, X × Y),
      ∃ _ : (ContinuousMap.id (X × Y)).HomotopyRel r (prodPairUnion A B),
        ∀ p : X × Y,
          (((a.control.comp ContinuousMap.fst) ⊓ (b.control.comp ContinuousMap.snd)) p < 1) →
            r p ∈ prodPairUnion A B := by
  let F : C((X × Y) × I, X × Y) :=
    ⟨prodUnionRatioSquareFun a b, hcont⟩
  let r : C(X × Y, X × Y) :=
    { toFun := fun p ↦ F (p, 1)
      continuous_toFun := F.continuous.comp (continuous_id.prodMk continuous_const) }
  have hr_eq : ∀ p : X × Y, r p = prodUnionRatioEndpointFun a b p := by
    -- The endpoint slice of the bundled square map is the textbook endpoint map.
    intro p
    simpa [r, F] using prodUnionRatioSquareFun_apply_one a b p
  let H : (ContinuousMap.id (X × Y)).Homotopy r :=
    { toFun := fun st ↦ F (st.2, st.1)
      continuous_toFun := F.continuous.comp (continuous_snd.prodMk continuous_fst)
      map_zero_left := fun p ↦ by
        simpa [F] using prodUnionRatioSquareFun_apply_zero a b p
      map_one_left := fun p ↦ by
        rfl }
  let hrel : (ContinuousMap.id (X × Y)).HomotopyRel r (prodPairUnion A B) :=
    { toHomotopy := H
      prop' := by
        -- Each time slice fixes the product union because the raw ratio-speed square already does.
        intro t p hp
        simpa [H, F] using prodUnionRatioSquareFun_eqOn_prodPairUnion a b hp t }
  refine ⟨r, hrel, ?_⟩
  · intro p hp
    -- Endpoint membership is the previously isolated NDR endpoint argument.
    rw [hr_eq p]
    exact prodUnionRatioEndpointFun_mem a b p hp

/-- Helper for Lemma 6.4.3: fixing the spatial point turns an NDR homotopy into a path. -/
private theorem ndrHomotopyPathContinuous {Z : Type*} [TopologicalSpace Z] {B : Set Z}
    (b : NDRPair B) (z : Z) :
    Continuous fun t : I ↦ b.homotopy (t, z) := by
  -- The homotopy is continuous in both variables, so freezing the point keeps continuity in time.
  simpa using b.homotopy.continuous.comp (continuous_id.prodMk continuous_const)

/-- Helper for Lemma 6.4.3: the `b`-homotopy at a fixed point is packaged as a continuous path. -/
private noncomputable def ndrHomotopyPath {Z : Type*} [TopologicalSpace Z] {B : Set Z}
    (b : NDRPair B) (z : Z) : C(I, Z) :=
  ⟨fun t ↦ b.homotopy (t, z), ndrHomotopyPathContinuous b z⟩

/-- Helper for Lemma 6.4.3: varying the endpoint varies continuously in the compact-open path
topology. -/
private theorem ndrHomotopyPathFamilyContinuous {Z : Type*} [TopologicalSpace Z] {B : Set Z}
    (b : NDRPair B) :
    Continuous fun z : Z ↦ ndrHomotopyPath b z := by
  -- Currying the continuous two-variable homotopy gives a continuous path family.
  apply ContinuousMap.continuous_of_continuous_uncurry
  simpa [Function.uncurry, ndrHomotopyPath] using
    b.homotopy.continuous.comp (continuous_snd.prodMk continuous_fst)

/-- Helper for Lemma 6.4.3: on the zero set `B`, the whole `b`-homotopy path is constant. -/
private theorem ndrHomotopyPath_eq_const_of_mem {Z : Type*} [TopologicalSpace Z] {B : Set Z}
    (b : NDRPair B) {z : Z} (hz : z ∈ B) :
    ndrHomotopyPath b z = ContinuousMap.const I z := by
  -- Relative fixedness says every time slice of the path stays at `y`.
  apply ContinuousMap.ext
  intro t
  exact b.homotopy.eq_fst t hz

/-- Helper for Lemma 6.4.3: near a point of `B`, the `b`-homotopy stays uniformly close to that
point for every projected real time parameter. -/
private theorem ndrHomotopy_projIcc_tendsto_top_of_mem {Z : Type*} [TopologicalSpace Z]
    {B : Set Z} (b : NDRPair B) {z : Z} (hz : z ∈ B) :
    Filter.Tendsto (fun p : Z × ℝ ↦ b.homotopy (Set.projIcc 0 1 zero_le_one p.2, p.1))
      (nhds z ×ˢ ⊤) (nhds z) := by
  -- Compact-open convergence to the constant path gives a neighborhood on which the full path
  -- image stays inside any chosen neighborhood of `y`.
  have hPath :
      Filter.Tendsto (fun z' : Z ↦ ndrHomotopyPath b z') (nhds z)
        (nhds (ContinuousMap.const I z)) := by
    simpa [ndrHomotopyPath_eq_const_of_mem b hz] using
      (((ndrHomotopyPathFamilyContinuous b).continuousAt :
        ContinuousAt (fun z' : Z ↦ ndrHomotopyPath b z') z).tendsto)
  rw [ContinuousMap.tendsto_nhds_compactOpen] at hPath
  rw [tendsto_def]
  intro U hU
  rcases mem_nhds_iff.1 hU with ⟨V, hVU, hVopen, hzV⟩
  have hzVMaps : MapsTo (ContinuousMap.const I z) (Set.univ : Set I) V := by
    intro t ht
    exact hzV
  have hEvent :
      {z' : Z | MapsTo (ndrHomotopyPath b z') (Set.univ : Set I) V} ∈ nhds z :=
    hPath (Set.univ : Set I) isCompact_univ V hVopen hzVMaps
  refine mem_of_superset (Filter.prod_mem_prod hEvent univ_mem) ?_
  intro p hp
  exact hVU (hp.1 trivial)

/-- Helper for Lemma 6.4.3: the left comparison formula is the raw branch used when
`a.control x ≤ b.control y`. -/
private noncomputable def prodUnionLeftComparisonBranch {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) :
    (X × Y) × I → X × Y :=
  fun st ↦
    (a.homotopy (st.2, st.1.1),
      b.homotopy
        (Set.projIcc 0 1 zero_le_one
          (((st.2 : ℝ) * (a.control st.1.1 : ℝ)) / (b.control st.1.2 : ℝ)),
          st.1.2))

/-- Helper for Lemma 6.4.3: the right comparison formula is the raw branch used when
`b.control y ≤ a.control x`. -/
private noncomputable def prodUnionRightComparisonBranch {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) :
    (X × Y) × I → X × Y :=
  fun st ↦
    (a.homotopy
        (Set.projIcc 0 1 zero_le_one
          (((st.2 : ℝ) * (b.control st.1.2 : ℝ)) / (a.control st.1.1 : ℝ)),
          st.1.1),
      b.homotopy (st.2, st.1.2))

/-- Helper for Lemma 6.4.3: on the left comparison region, the raw ratio-speed map is exactly the
left comparison branch. -/
private theorem prodUnionRatioSquareFun_eq_ifComparisonBranches {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) (st : (X × Y) × I) :
    prodUnionRatioSquareFun a b st =
      if a.control st.1.1 ≤ b.control st.1.2 then
        prodUnionLeftComparisonBranch a b st
      else
        prodUnionRightComparisonBranch a b st := by
  -- Unfolding the square-order definition exposes the same outer comparison used in the branches.
  by_cases hcmp : a.control st.1.1 ≤ b.control st.1.2
  · simp [prodUnionRatioSquareFun, prodUnionRatioHomotopyFun, prodUnionLeftTime, prodUnionRightTime,
      prodUnionLeftComparisonBranch, hcmp]
  · simp [prodUnionRatioSquareFun, prodUnionRatioHomotopyFun, prodUnionLeftTime, prodUnionRightTime,
      prodUnionRightComparisonBranch, hcmp]

/-- Helper for Lemma 6.4.3: the left comparison branch is continuous on the region
`a.control x ≤ b.control y`. -/
private theorem prodUnionLeftComparisonBranchContinuous {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) :
    ContinuousOn (prodUnionLeftComparisonBranch a b)
      {st : (X × Y) × I | a.control st.1.1 ≤ b.control st.1.2} := by
  -- Restricting to the comparison region makes the singular denominator compatible with the
  -- relative fixedness of `b.homotopy` along `B`.
  let L : Set ((X × Y) × I) := {st : (X × Y) × I | a.control st.1.1 ≤ b.control st.1.2}
  suffices hcont :
      Continuous fun s : L ↦ prodUnionLeftComparisonBranch a b s.1 by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous fun s : L ↦ prodUnionLeftComparisonBranch a b s.1
    exact hcont
  have hfirst : Continuous fun s : L ↦ a.homotopy (s.1.2, s.1.1.1) := by
    -- The first coordinate is just the left factor homotopy at the ambient time.
    simpa [prodUnionLeftComparisonBranch] using
      a.homotopy.continuous.comp
        ((continuous_snd.comp continuous_subtype_val).prodMk
          (continuous_fst.comp (continuous_fst.comp continuous_subtype_val)))
  have hbase :
      Continuous fun p : L × ℝ ↦
        b.homotopy (Set.projIcc 0 1 zero_le_one p.2, p.1.1.1.2) := by
    -- Away from the singular locus, this is the obvious continuous composite into `b.homotopy`.
    simpa using b.homotopy.continuous.comp
      ((continuous_projIcc.comp continuous_snd).prodMk
        (continuous_snd.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))))
  have hsecond :
      Continuous fun s : L ↦
        b.homotopy
          (Set.projIcc 0 1 zero_le_one
            (((s.1.2 : ℝ) * (a.control s.1.1.1 : ℝ)) / (b.control s.1.1.2 : ℝ)),
            s.1.1.2) := by
    -- `comp_div_cases` packages the only real issue: when the denominator vanishes, the point is
    -- already in `B`, so `b.homotopy` is locally constant in the time variable.
    refine Continuous.comp_div_cases
        (h := fun p : L ↦ fun r ↦
          b.homotopy (Set.projIcc 0 1 zero_le_one r, p.1.1.2))
        ?_ ?_ ?_ ?_
    · exact (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).mul
        (continuous_subtype_val.comp
          (a.control.continuous.comp
            (continuous_fst.comp (continuous_fst.comp continuous_subtype_val))))
    · exact continuous_subtype_val.comp
        (b.control.continuous.comp
          (continuous_snd.comp (continuous_fst.comp continuous_subtype_val)))
    · intro s hs
      exact hbase.continuousAt
    · intro s hs
      have hdenom : b.control s.1.1.2 = 0 := by
        apply Subtype.ext
        simpa using hs
      have hyB : s.1.1.2 ∈ B := (b.control_eq_zero_iff s.1.1.2).1 hdenom
      let yCoord : L → Y := fun q ↦ q.1.1.2
      have hy :
          Filter.Tendsto (fun p : L × ℝ ↦ yCoord p.1) (nhds s ×ˢ ⊤) (nhds (yCoord s)) := by
        exact
          (((show Continuous yCoord by
            exact continuous_snd.comp
              (continuous_fst.comp continuous_subtype_val)).continuousAt).tendsto).comp
          tendsto_fst
      simpa [yCoord, b.homotopy.apply_zero] using
        (ndrHomotopy_projIcc_tendsto_top_of_mem b hyB).comp (hy.prodMk tendsto_snd)
  -- The two continuous coordinates assemble into the continuous branch map.
  simpa [prodUnionLeftComparisonBranch] using hfirst.prodMk hsecond

/-- Helper for Lemma 6.4.3: the right comparison branch is continuous on the region
`b.control y ≤ a.control x`. -/
private theorem prodUnionRightComparisonBranchContinuous {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) :
    ContinuousOn (prodUnionRightComparisonBranch a b)
      {st : (X × Y) × I | b.control st.1.2 ≤ a.control st.1.1} := by
  -- This is the symmetric argument, now using the relative fixedness of `a.homotopy` along `A`.
  let R : Set ((X × Y) × I) := {st : (X × Y) × I | b.control st.1.2 ≤ a.control st.1.1}
  suffices hcont :
      Continuous fun s : R ↦ prodUnionRightComparisonBranch a b s.1 by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous fun s : R ↦ prodUnionRightComparisonBranch a b s.1
    exact hcont
  have hsecond : Continuous fun s : R ↦ b.homotopy (s.1.2, s.1.1.2) := by
    -- The second coordinate now runs at the ambient time without any singularity.
    simpa [prodUnionRightComparisonBranch] using
      b.homotopy.continuous.comp
        ((continuous_snd.comp continuous_subtype_val).prodMk
          (continuous_snd.comp (continuous_fst.comp continuous_subtype_val)))
  have hbase :
      Continuous fun p : R × ℝ ↦
        a.homotopy (Set.projIcc 0 1 zero_le_one p.2, p.1.1.1.1) := by
    -- The quotient parameter only appears in the first coordinate for the symmetric branch.
    simpa using a.homotopy.continuous.comp
      ((continuous_projIcc.comp continuous_snd).prodMk
        (continuous_fst.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))))
  have hfirst :
      Continuous fun s : R ↦
        a.homotopy
          (Set.projIcc 0 1 zero_le_one
            (((s.1.2 : ℝ) * (b.control s.1.1.2 : ℝ)) / (a.control s.1.1.1 : ℝ)),
            s.1.1.1) := by
    -- The same denominator-vanishing argument applies with the roles of `a` and `b` reversed.
    refine Continuous.comp_div_cases
        (h := fun p : R ↦ fun r ↦
          a.homotopy (Set.projIcc 0 1 zero_le_one r, p.1.1.1))
        ?_ ?_ ?_ ?_
    · exact (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).mul
        (continuous_subtype_val.comp
          (b.control.continuous.comp
            (continuous_snd.comp (continuous_fst.comp continuous_subtype_val))))
    · exact continuous_subtype_val.comp
        (a.control.continuous.comp
          (continuous_fst.comp (continuous_fst.comp continuous_subtype_val)))
    · intro s hs
      exact hbase.continuousAt
    · intro s hs
      have hdenom : a.control s.1.1.1 = 0 := by
        apply Subtype.ext
        simpa using hs
      have hxA : s.1.1.1 ∈ A := (a.control_eq_zero_iff s.1.1.1).1 hdenom
      let xCoord : R → X := fun q ↦ q.1.1.1
      have hx :
          Filter.Tendsto (fun p : R × ℝ ↦ xCoord p.1) (nhds s ×ˢ ⊤) (nhds (xCoord s)) := by
        exact
          (((show Continuous xCoord by
            exact continuous_fst.comp
              (continuous_fst.comp continuous_subtype_val)).continuousAt).tendsto).comp
          tendsto_fst
      simpa [xCoord, a.homotopy.apply_zero] using
        (ndrHomotopy_projIcc_tendsto_top_of_mem a hxA).comp (hx.prodMk tendsto_snd)
  -- Again, the continuous coordinates assemble into the full branch map.
  simpa [prodUnionRightComparisonBranch] using hfirst.prodMk hsecond

/-- Helper for Lemma 6.4.3: on the comparison boundary `a.control x = b.control y`, the two raw
comparison branches coincide. -/
private theorem prodUnionComparisonBranchesAgreeOnBoundary {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) {st : (X × Y) × I}
    (hEq : a.control st.1.1 = b.control st.1.2) :
    prodUnionLeftComparisonBranch a b st = prodUnionRightComparisonBranch a b st := by
  -- On the zero boundary both factors are already fixed; otherwise both rescaled times simplify
  -- to the ambient time parameter.
  rcases st with ⟨⟨x, y⟩, t⟩
  by_cases hx0 : a.control x = 0
  · have hy0 : b.control y = 0 := by rw [← hEq]; exact hx0
    have hxA : x ∈ A := (a.control_eq_zero_iff x).1 hx0
    have hyB : y ∈ B := (b.control_eq_zero_iff y).1 hy0
    ext
    · calc
        a.homotopy (t, x) = x := a.homotopy.eq_fst t hxA
        _ = a.homotopy
              (Set.projIcc 0 1 zero_le_one
                (((t : ℝ) * (b.control y : ℝ)) / (a.control x : ℝ)),
                x) := (a.homotopy.eq_fst _ hxA).symm
    · calc
        b.homotopy
            (Set.projIcc 0 1 zero_le_one
              (((t : ℝ) * (a.control x : ℝ)) / (b.control y : ℝ)),
              y) = y := b.homotopy.eq_fst _ hyB
        _ = b.homotopy (t, y) := (b.homotopy.eq_fst t hyB).symm
  · have hx0R : (a.control x : ℝ) ≠ 0 := by simpa using hx0
    have hy0 : b.control y ≠ 0 := by
      intro hy0
      apply hx0
      rw [hEq]
      exact hy0
    have hy0R : (b.control y : ℝ) ≠ 0 := by simpa using hy0
    have hEqR : (a.control x : ℝ) = (b.control y : ℝ) := by
      simpa using congrArg (fun z : I ↦ (z : ℝ)) hEq
    have hLeftReal :
        (((t : ℝ) * (a.control x : ℝ)) / (b.control y : ℝ)) = (t : ℝ) := by
      rw [← hEqR, mul_div_cancel_right₀ _ hx0R]
    have hRightReal :
        (((t : ℝ) * (b.control y : ℝ)) / (a.control x : ℝ)) = (t : ℝ) := by
      rw [hEqR, mul_div_cancel_right₀ _ hy0R]
    have hLeftTime :
        Set.projIcc 0 1 zero_le_one
            (((t : ℝ) * (a.control x : ℝ)) / (b.control y : ℝ)) = t := by
      have hmem :
          (((t : ℝ) * (a.control x : ℝ)) / (b.control y : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
        simp [hLeftReal]
      rw [Set.projIcc_of_mem zero_le_one hmem]
      exact Subtype.ext hLeftReal
    have hRightTime :
        Set.projIcc 0 1 zero_le_one
            (((t : ℝ) * (b.control y : ℝ)) / (a.control x : ℝ)) = t := by
      have hmem :
          (((t : ℝ) * (b.control y : ℝ)) / (a.control x : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
        simp [hRightReal]
      rw [Set.projIcc_of_mem zero_le_one hmem]
      exact Subtype.ext hRightReal
    ext <;> simp [prodUnionLeftComparisonBranch, prodUnionRightComparisonBranch, hLeftTime,
      hRightTime]

/-- Helper for Lemma 6.4.3: the square-order ratio-speed deformation is continuous after gluing
its two comparison branches along the equality frontier. -/
private theorem prodUnionRatioSquareFunContinuous {A : Set X} {B : Set Y}
    (a : NDRPair A) (b : NDRPair B) :
    Continuous (prodUnionRatioSquareFun a b) := by
  -- `continuous_if_le` matches the source proof: prove continuity on each comparison region and
  -- then glue the two formulas across the equality boundary.
  have hLeftControl : Continuous fun st : (X × Y) × I ↦ a.control st.1.1 := by
    exact a.control.continuous.comp (continuous_fst.comp continuous_fst)
  have hRightControl : Continuous fun st : (X × Y) × I ↦ b.control st.1.2 := by
    exact b.control.continuous.comp (continuous_snd.comp continuous_fst)
  have hGlue := continuous_if_le hLeftControl hRightControl
    (prodUnionLeftComparisonBranchContinuous a b)
    (prodUnionRightComparisonBranchContinuous a b)
    (fun st hEq ↦ prodUnionComparisonBranchesAgreeOnBoundary a b hEq)
  refine hGlue.congr ?_
  intro st
  exact (prodUnionRatioSquareFun_eq_ifComparisonBranches a b st).symm

/-- Helper for Lemma 6.4.3: once the ratio-speed product deformation is built, its time-`1` slice
packages the relative homotopy and endpoint data needed for the product NDR witness. -/
private theorem prodUnionWitnessData {A : Set X} {B : Set Y} (a : NDRPair A) (b : NDRPair B) :
    ∃ r : C(X × Y, X × Y),
      ∃ _ : (ContinuousMap.id (X × Y)).HomotopyRel r (prodPairUnion A B),
        ∀ p : X × Y,
          (((a.control.comp ContinuousMap.fst) ⊓ (b.control.comp ContinuousMap.snd)) p < 1) →
            r p ∈ prodPairUnion A B := by
  -- Route correction: the direct product homotopy fixes only `A × B`, so the remaining proof must
  -- use the source-style ratio-speed deformation that keeps `X × B ∪ A × Y` pointwise fixed.
  have hcont : Continuous (prodUnionRatioSquareFun a b) := prodUnionRatioSquareFunContinuous a b
  -- Once continuity is available, the remaining homotopy packaging is formal.
  rcases prodUnionHomotopyRelAndEndpoint_ofContinuousSquareMap a b hcont with ⟨r, hrel, hmem⟩
  exact ⟨r, hrel, hmem⟩

/-- Lemma 6.4.3. Products of NDR-pairs are NDR-pairs: if `A ⊆ X` and `B ⊆ Y` are NDR-pairs, then
`prodPairUnion A B = Set.univ ×ˢ B ∪ A ×ˢ Set.univ ⊆ X × Y` is an NDR-pair. -/
theorem prodUnionHomotopyRelAndEndpoint {A : Set X} {B : Set Y} (hA : IsNDRPair A)
    (hB : IsNDRPair B) :
    IsNDRPair (prodPairUnion A B) := by
  rcases isNDRPair_iff_nonempty_ndrPair.mp hA with ⟨a⟩
  rcases isNDRPair_iff_nonempty_ndrPair.mp hB with ⟨b⟩
  rcases prodUnionWitnessData a b with ⟨r, hrel, hr_mem⟩
  let prodControl : C(X × Y, I) :=
    (a.control.comp ContinuousMap.fst) ⊓ (b.control.comp ContinuousMap.snd)
  have hzero :
      prodControl ⁻¹' ({0} : Set I) = prodPairUnion A B := by
    -- The product witness uses the infimum control, whose zero set is already identified above.
    ext p
    simpa [prodControl] using prodControl_eq_zero_iff a b p
  have hendpoint : ∀ p, prodControl p < 1 → r p ∈ prodPairUnion A B := by
    -- The remaining endpoint condition is packaged with the homotopy placeholder helper.
    intro p hp
    simpa [prodControl] using hr_mem p hp
  let witness : NDRPair (prodPairUnion A B) :=
    { control := prodControl
      retract := r
      homotopy := hrel
      zeroSet_eq := hzero
      endpoint_mem := hendpoint }
  exact witness.toIsNDRPair

/-- Helper for Lemma 6.4.3: `isNDRPair_prod_union` is the chapter API alias for the main product
NDR-pair theorem. -/
theorem isNDRPair_prod_union {A : Set X} {B : Set Y} (hA : IsNDRPair A) (hB : IsNDRPair B) :
    IsNDRPair (prodPairUnion A B) :=
  prodUnionHomotopyRelAndEndpoint hA hB
