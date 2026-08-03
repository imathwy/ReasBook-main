module

public import Topology_Munkres_2000.Book.Theorem_80_3
public import Topology_Munkres_2000.Book.Lemma_80_2
public import Topology_Munkres_2000.Book.Definition_80_1.Covering
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Algebra.Module.LocallyConvex

public section

universe u v w t

open TopologicalSpace Topology

/-- Helper for Exercise 80.1: the source of a local homeomorphism into a locally
path-connected space is locally path-connected. -/
theorem IsLocalHomeomorph.locallyPathConnectedSpace_of_codomain
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    [LocallyPathConnectedSpace B] {f : E → B} (hf : IsLocalHomeomorph f) :
    LocallyPathConnectedSpace E := by
  -- Refine the local-section basis by path-connected open neighborhoods in the base.
  let ℘ : Set (Set E) := {U | IsOpen U ∧ IsPathConnected U}
  have h℘ : IsTopologicalBasis ℘ := by
    refine isTopologicalBasis_of_isOpen_of_nhds (fun U hU ↦ hU.1) ?_
    intro x U hxU hU
    obtain ⟨S, ⟨V, hV, s, hs, hsS⟩, hxS, hSU⟩ :=
      hf.isTopologicalBasis.exists_subset_of_mem_open hxU hU
    rw [← hsS] at hxS
    obtain ⟨x', rfl⟩ := hxS
    have hs_open : IsOpenEmbedding s :=
      hf.isOpenEmbedding_of_comp (hs ▸ hV.isOpenEmbedding_subtypeVal) s.continuous
    haveI : LocallyPathConnectedSpace V := hV.locallyPathConnectedSpace
    obtain ⟨W, hW⟩ := (isOpen_isPathConnected_basis x').ex_mem
    refine ⟨s '' W, ⟨hs_open.isOpenMap W hW.1, hW.2.2.image s.continuous⟩,
      ⟨x', hW.2.1, rfl⟩, ?_⟩
    exact (Set.image_subset_range s W).trans (hsS.symm ▸ hSU)
  -- The resulting topological basis is precisely a basis by path-connected neighborhoods.
  refine LocallyPathConnectedSpace.of_bases (fun x ↦ h℘.nhds_hasBasis) ?_
  intro x U hU
  exact hU.1.2

/-- Helper for Exercise 80.1: a product of path-connected, locally path-connected
spaces is locally path-connected, even for an infinite index type. -/
theorem locallyPathConnectedSpace_pi_of_pathConnected
    {ι : Type u} {A : ι → Type v} [∀ i, TopologicalSpace (A i)]
    [∀ i, PathConnectedSpace (A i)] [∀ i, LocallyPathConnectedSpace (A i)] :
    LocallyPathConnectedSpace (∀ i, A i) := by
  -- Refine each finite-coordinate basic neighborhood by path-connected factor neighborhoods.
  let ℘ : Set (Set (∀ i, A i)) := {U | IsOpen U ∧ IsPathConnected U}
  have h℘ : IsTopologicalBasis ℘ := by
    refine isTopologicalBasis_of_isOpen_of_nhds (fun U hU ↦ hU.1) ?_
    intro x U hxU hU
    obtain ⟨I, u, hu, huU⟩ := isOpen_pi_iff.mp hU x hxU
    have hexists (i : ι) (hi : i ∈ I) :
        ∃ V : Set (A i), IsOpen V ∧ x i ∈ V ∧ IsPathConnected V ∧ V ⊆ u i := by
      obtain ⟨V, hV, hVu⟩ :=
        (isOpen_isPathConnected_basis (x i)).mem_iff.mp ((hu i hi).1.mem_nhds (hu i hi).2)
      exact ⟨V, hV.1, hV.2.1, hV.2.2, hVu⟩
    classical
    choose V hVopen hxV hVpath hVu using hexists
    let W : ∀ i, Set (A i) := fun i ↦ if hi : i ∈ I then V i hi else Set.univ
    have hW_open : IsOpen (Set.univ.pi W) := by
      have heq : Set.univ.pi W = (I : Set ι).pi W := by
        ext y
        simp only [Set.mem_pi, Set.mem_univ, true_implies]
        constructor
        · exact fun h i hi ↦ h i
        · intro h i
          by_cases hi : i ∈ I
          · exact h i hi
          · simp [W, hi]
      rw [heq]
      refine isOpen_set_pi I.finite_toSet fun i hi ↦ ?_
      have hiI : i ∈ I := hi
      have hWi : W i = V i hiI := by simp [W, hiI]
      rw [hWi]
      exact hVopen i hiI
    have hxW : x ∈ Set.univ.pi W := by
      intro i hi
      by_cases hiI : i ∈ I
      · simpa [W, hiI] using hxV i hiI
      · simp [W, hiI]
    have hW_path : IsPathConnected (Set.univ.pi W) := by
      refine IsPathConnected.pi fun i ↦ ?_
      by_cases hi : i ∈ I
      · simpa [W, hi] using hVpath i hi
      · simpa [W, hi] using (isPathConnected_univ : IsPathConnected (Set.univ : Set (A i)))
    refine ⟨Set.univ.pi W, ⟨hW_open, hW_path⟩, hxW, ?_⟩
    intro y hy
    apply huU
    intro i hi
    have hiI : i ∈ I := hi
    have hWi : W i = V i hiI := by simp [W, hiI]
    exact hVu i hiI (hWi ▸ hy i trivial)
  -- The refined basic opens supply the required path-connected neighborhood basis.
  refine LocallyPathConnectedSpace.of_bases (fun x ↦ h℘.nhds_hasBasis) ?_
  intro x U hU
  exact hU.1.2

/-- Helper for Exercise 80.1: a binary product of locally path-connected spaces is locally
path-connected. -/
instance prodLocallyPathConnectedSpace
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    [LocallyPathConnectedSpace A] [LocallyPathConnectedSpace B] :
    LocallyPathConnectedSpace (A × B) := by
  -- Take products of path-connected neighborhood bases in the two factors.
  refine LocallyPathConnectedSpace.of_bases
    (fun x ↦ (path_connected_basis x.1).prod_nhds (path_connected_basis x.2)) ?_
  intro x U hU
  exact hU.1.2.prod hU.2.2

/-- Helper for Exercise 80.1: the lift of a map through one fixed fiber coordinate of a
covering trivialization. -/
noncomputable def trivializationLift
    {E : Type u} {B : Type v} {F : Type w}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    {p : E → B} (t : Bundle.Trivialization F p) (γ : unitInterval → B)
    (i : F) : unitInterval → E :=
  fun s ↦ t.toOpenPartialHomeomorph.symm (γ s, i)

/-- Helper for Exercise 80.1: a fixed-fiber lift is continuous while its base map remains in
the trivialization base set. -/
lemma continuous_trivializationLift
    {E : Type u} {B : Type v} {F : Type w}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    {p : E → B} (t : Bundle.Trivialization F p) (γ : unitInterval → B) (i : F)
    (hγ : Continuous γ) (hbase : ∀ s, γ s ∈ t.baseSet) :
    Continuous (trivializationLift t γ i) := by
  -- The pair `(γ s, i)` stays in the target on which the inverse chart is continuous.
  apply t.continuousOn_invFun.comp_continuous (hγ.prodMk continuous_const)
  intro s
  rw [t.target_eq]
  exact ⟨hbase s, trivial⟩

/-- Helper for Exercise 80.1: projection of a fixed-fiber trivialization lift recovers its
base map. -/
lemma apply_trivializationLift
    {E : Type u} {B : Type v} {F : Type w}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    {p : E → B} (t : Bundle.Trivialization F p) (γ : unitInterval → B) (i : F)
    (hbase : ∀ s, γ s ∈ t.baseSet) (s : unitInterval) :
    p (trivializationLift t γ i s) = γ s := by
  -- This is the projection computation rule for the inverse trivialization chart.
  apply t.proj_symm_apply
  rw [t.target_eq]
  exact ⟨hbase s, trivial⟩

/-- Helper for Exercise 80.1: when the base map reaches `p e`, the lift with the chart
coordinate of `e` reaches `e`. -/
lemma trivializationLift_eq_of_eq_proj
    {E : Type u} {B : Type v} {F : Type w}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    {p : E → B} (t : Bundle.Trivialization F p) (γ : unitInterval → B)
    (hbase : ∀ s, γ s ∈ t.baseSet) (e : E) (s : unitInterval) (hs : γ s = p e) :
    trivializationLift t γ (t e).2 s = e := by
  -- Rewrite to the projection of `e` and apply the inverse-chart identity.
  rw [trivializationLift, hs]
  exact t.symm_apply_mk_proj (t.mem_source.mpr (hs ▸ hbase s))

/-- Helper for Exercise 80.1: a lift of a loop contained in one covering trivialization
returns to its initial point. -/
lemma IsCoveringMap.lift_endpoint_eq_of_trivialization
    {E : Type u} {B : Type v} {F : Type w}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
    {p : E → B} (hp : IsCoveringMap p) (t : Bundle.Trivialization F p)
    (γ : C(unitInterval, B)) (hbase : ∀ s, γ s ∈ t.baseSet) (e : E)
    (hzero : γ 0 = p e) (hone : γ 1 = p e) (α : C(unitInterval, E))
    (hα : p ∘ α = γ) (hαzero : α 0 = e) : α 1 = e := by
  -- Compare `α` with the fixed-fiber lift supplied by the chosen trivialization.
  let β : C(unitInterval, E) :=
    ⟨trivializationLift t γ (t e).2,
      continuous_trivializationLift t γ (t e).2 γ.continuous hbase⟩
  have hβ : p ∘ β = γ := by
    funext s
    exact apply_trivializationLift t γ (t e).2 hbase s
  have hβzero : β 0 = e :=
    trivializationLift_eq_of_eq_proj t γ hbase e 0 hzero
  have hαβ_fun : (α : unitInterval → E) = β :=
    hp.eq_of_comp_eq α.continuous β.continuous (hα.trans hβ.symm) 0
      (hαzero.trans hβzero.symm)
  have hαβ : α = β := ContinuousMap.ext fun s ↦ congrFun hαβ_fun s
  -- The same inverse-chart identity at the other endpoint closes the lift.
  rw [hαβ]
  exact trivializationLift_eq_of_eq_proj t γ hbase e 1 hone

/-- Exercise 80.1 (1). If `q : X → Y` and `r : Y → Z` are covering maps and `Z`
has a universal covering space, then `r ∘ q` is a covering map. -/
theorem IsCoveringMap.comp_of_universalCovering {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [PathConnectedSpace X] [PathConnectedSpace Y] [PathConnectedSpace Z]
    [LocallyPathConnectedSpace X] [LocallyPathConnectedSpace Y]
    [LocallyPathConnectedSpace Z]
    {q : X → Y} {r : Y → Z} (hq : IsCoveringMap q)
    (hq_surjective : Function.Surjective q) (hr : IsCoveringMap r)
    (hr_surjective : Function.Surjective r) (hZ : Nonempty (UniversalCovering.{t} Z)) :
    IsCoveringMap (r ∘ q) ∧ Function.Surjective (r ∘ q) := by
  -- Lift the universal cover successively through `r` and through `q`.
  obtain ⟨C⟩ := hZ
  letI : SimplyConnectedSpace C.Total := C.simplyConnectedSpace
  letI : LocallyPathConnectedSpace C.Total :=
    C.isCoveringMap.isLocalHomeomorph.locallyPathConnectedSpace_of_codomain
  obtain ⟨a, ha, ha_surjective, ha_factor⟩ :=
    exists_coveringMap_lift C.proj C.isCoveringMap C.surjective r hr hr_surjective
  obtain ⟨b, hb, hb_surjective, hb_factor⟩ :=
    exists_coveringMap_lift a ha ha_surjective q hq hq_surjective
  have hfactor : C.proj = (r ∘ q) ∘ b := by
    rw [← ha_factor, ← hb_factor]
    rfl
  -- Cancellation of the covering `b` now gives the composite covering and its surjectivity.
  exact coveringMap_of_comp_left ((hr.continuous.comp hq.continuous)) hfactor
    C.isCoveringMap C.surjective hb hb_surjective

namespace ShiftSuspension

/-- Helper for Exercise 80.1: the unit additive circle is locally path-connected. -/
instance unitAddCircleLocallyPathConnectedSpace : LocallyPathConnectedSpace UnitAddCircle :=
  (AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)).toIsQuotientMap.locallyPathConnectedSpace

/-- Helper for Exercise 80.1: the infinite torus used in the shift suspension. -/
abbrev Torus := ℤ → UnitAddCircle

/-- Helper for Exercise 80.1: the total space on which the coordinate shift acts. -/
abbrev Total := Torus × ℝ

/-- Helper for Exercise 80.1: the infinite torus is locally path-connected. -/
instance torusLocallyPathConnectedSpace : LocallyPathConnectedSpace Torus :=
  locallyPathConnectedSpace_pi_of_pathConnected

/-- Helper for Exercise 80.1: translating by `n` shifts the torus coordinates and the
real coordinate simultaneously. -/
def translate (n : ℤ) (x : Total) : Total :=
  (fun k ↦ x.1 (k + n), (n : ℝ) + x.2)

/-- Helper for Exercise 80.1: the shift suspension carries the coordinate-shift action of `ℤ`. -/
instance instVAdd : VAdd ℤ Total := ⟨translate⟩

/-- Helper for Exercise 80.1: zero acts trivially on the shift-suspension total space. -/
lemma zero_vadd (x : Total) : (0 : ℤ) +ᵥ x = x := by
  -- Both the coordinate reindexing and the real translation reduce to identities.
  change translate 0 x = x
  apply Prod.ext
  · funext k
    simp [translate]
  · simp [translate]

/-- Helper for Exercise 80.1: successive shifts agree with addition in `ℤ`. -/
lemma add_vadd (m n : ℤ) (x : Total) : (m + n) +ᵥ x = m +ᵥ n +ᵥ x := by
  -- Associativity normalizes both the torus index and the real translation.
  change translate (m + n) x = translate m (translate n x)
  apply Prod.ext
  · funext k
    simp [translate, add_assoc]
  · simp [translate, Int.cast_add, add_assoc]

/-- Helper for Exercise 80.1: the coordinate shifts form an additive action. -/
instance instAddAction : AddAction ℤ Total where
  zero_vadd := zero_vadd
  add_vadd := add_vadd

/-- Helper for Exercise 80.1: every fixed coordinate shift is continuous. -/
lemma continuous_translate (n : ℤ) : Continuous fun x : Total ↦ n +ᵥ x := by
  -- Continuity is checked coordinatewise on the torus and directly on `ℝ`.
  refine (continuous_pi fun k ↦ (continuous_apply (k + n)).comp continuous_fst).prodMk ?_
  exact continuous_const.add continuous_snd

/-- Helper for Exercise 80.1: the shift action is continuous in the total-space variable. -/
instance instContinuousConstVAdd : ContinuousConstVAdd ℤ Total where
  continuous_const_vadd := continuous_translate

/-- Helper for Exercise 80.1: the orbit space of the simultaneous coordinate and real shifts. -/
abbrev Base := Quotient (AddAction.orbitRel ℤ Total)

/-- Helper for Exercise 80.1: the canonical projection to the shift-suspension orbit space. -/
def proj : Total → Base := Quotient.mk _

/-- Helper for Exercise 80.1: the shift-suspension projection is a quotient covering map. -/
private lemma projIsAddQuotientCoveringMap : IsAddQuotientCoveringMap proj ℤ := by
  -- A real interval of length less than one is disjoint from each nontrivial integer translate.
  refine
    { toIsQuotientMap := isQuotientMap_quotient_mk'
      toContinuousConstVAdd := inferInstance
      apply_eq_iff_mem_orbit := Quotient.eq''
      disjoint := ?_ }
  intro x
  let U : Set Total := Set.univ ×ˢ Set.Ioo (x.2 - (1 : ℝ) / 3) (x.2 + (1 : ℝ) / 3)
  refine ⟨U, (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨trivial, by constructor <;> norm_num⟩, ?_⟩
  intro n hn
  obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := hn
  have hy_real := hy.2
  have hz_real : (n : ℝ) + y.2 ∈
      Set.Ioo (x.2 - (1 : ℝ) / 3) (x.2 + (1 : ℝ) / 3) := by
    change translate n y ∈ U at hz
    exact hz.2
  have hn_bounds : (-1 : ℝ) < (n : ℝ) ∧ (n : ℝ) < 1 := by
    constructor
    · linarith [hy_real.2, hz_real.1]
    · linarith [hy_real.1, hz_real.2]
  norm_cast at hn_bounds
  omega

/-- Helper for Exercise 80.1: the shift-suspension projection is a covering map. -/
lemma proj_isCoveringMap : IsCoveringMap proj :=
  projIsAddQuotientCoveringMap.isCoveringMap

/-- Helper for Exercise 80.1: the shift-suspension projection is surjective. -/
lemma proj_surjective : Function.Surjective proj :=
  projIsAddQuotientCoveringMap.surjective

/-- Helper for Exercise 80.1: the orbit projection is invariant under every integer shift. -/
lemma proj_vadd (n : ℤ) (x : Total) : proj (n +ᵥ x) = proj x :=
  projIsAddQuotientCoveringMap.map_vadd n

/-- Helper for Exercise 80.1: the zero point of the shift-suspension total space. -/
def basepoint : Total := (0, 0)

/-- Helper for Exercise 80.1: a loop that winds once in one selected torus coordinate. -/
def coordinateLoopFn (n : ℤ) (s : unitInterval) : Total :=
  (fun k ↦ if k = n then (((s : unitInterval) : ℝ) : UnitAddCircle) else 0, 0)

/-- Helper for Exercise 80.1: the selected-coordinate loop is continuous. -/
lemma continuous_coordinateLoopFn (n : ℤ) : Continuous (coordinateLoopFn n) := by
  -- Each coordinate is either the canonical real-to-circle path or a constant.
  refine (continuous_pi fun k ↦ ?_).prodMk continuous_const
  by_cases hkn : k = n
  · subst k
    simp only [if_pos]
    fun_prop
  · simpa [coordinateLoopFn, hkn] using (continuous_const : Continuous fun _ : unitInterval ↦
      (0 : UnitAddCircle))

/-- Helper for Exercise 80.1: the selected-coordinate loop starts at the zero point. -/
lemma coordinateLoopFn_zero (n : ℤ) : coordinateLoopFn n 0 = basepoint := by
  -- The circle quotient sends real zero to its additive identity.
  apply Prod.ext
  · funext k
    simp [coordinateLoopFn, basepoint]
  · rfl

/-- Helper for Exercise 80.1: the selected-coordinate loop ends at the zero point. -/
lemma coordinateLoopFn_one (n : ℤ) : coordinateLoopFn n 1 = basepoint := by
  -- One full real period is zero in `UnitAddCircle`.
  apply Prod.ext
  · funext k
    by_cases hkn : k = n
    · simp [coordinateLoopFn, basepoint, hkn, AddCircle.coe_period]
    · simp [coordinateLoopFn, basepoint, hkn]
  · rfl

/-- Helper for Exercise 80.1: the selected-coordinate function bundled as a based path. -/
def coordinateLoop (n : ℤ) : Path basepoint basepoint :=
  ⟨⟨coordinateLoopFn n, continuous_coordinateLoopFn n⟩,
    coordinateLoopFn_zero n, coordinateLoopFn_one n⟩

end ShiftSuspension

namespace ShiftCoordinateCover

open AddSubgroup

/-- Helper for Exercise 80.1: all circle coordinates other than coordinate zero. -/
abbrev Rest := {k : ℤ // k ≠ 0} → UnitAddCircle

/-- Helper for Exercise 80.1: the source that unwraps coordinate zero of the infinite torus. -/
abbrev Total := (ℝ × Rest) × ℝ

/-- Helper for Exercise 80.1: the split presentation of the shift-suspension total space. -/
abbrev Split := (UnitAddCircle × Rest) × ℝ

/-- Helper for Exercise 80.1: the product of the nonzero circle coordinates is locally
path-connected. -/
instance restLocallyPathConnectedSpace : LocallyPathConnectedSpace Rest :=
  locallyPathConnectedSpace_pi_of_pathConnected

/-- Helper for Exercise 80.1: the product map that unwraps only the zero coordinate. -/
def splitMap : Total → Split :=
  Prod.map (Prod.map ((↑) : ℝ → UnitAddCircle) id) id

/-- Helper for Exercise 80.1: splitting coordinate zero identifies the split target with the
infinite-torus total space. -/
noncomputable def splitHomeomorph : Split ≃ₜ ShiftSuspension.Total :=
  Homeomorph.prodCongr
    (Homeomorph.piSplitAt (0 : ℤ) (fun _ ↦ UnitAddCircle)).symm
    (Homeomorph.refl ℝ)

/-- Helper for Exercise 80.1: the covering that unwraps coordinate zero. -/
noncomputable def map : Total → ShiftSuspension.Total :=
  splitHomeomorph ∘ splitMap

/-- Helper for Exercise 80.1: the coordinate cover sends its first real coordinate to torus
coordinate zero. -/
lemma map_apply_zero (x : Total) : (map x).1 0 = (x.1.1 : UnitAddCircle) := by
  -- Evaluate the inverse coordinate-splitting homeomorphism at the distinguished coordinate.
  simp [map, splitHomeomorph, splitMap, Function.comp_apply, Homeomorph.piSplitAt,
    Equiv.piSplitAt]

/-- Helper for Exercise 80.1: away from zero, the coordinate cover preserves the stored circle
coordinate. -/
lemma map_apply_ne_zero (x : Total) {k : ℤ} (hk : k ≠ 0) :
    (map x).1 k = x.1.2 ⟨k, hk⟩ := by
  -- The inverse coordinate splitting selects the nonzero-coordinate function.
  simp [map, splitHomeomorph, splitMap, Function.comp_apply, Homeomorph.piSplitAt,
    Equiv.piSplitAt, hk]

/-- Helper for Exercise 80.1: the coordinate cover preserves the suspension real coordinate. -/
lemma map_apply_real (x : Total) : (map x).2 = x.2 := by
  -- The target homeomorphism acts only on the torus factor.
  rfl

/-- Helper for Exercise 80.1: the explicit lift that unwraps a selected shifted loop. -/
def coordinateLiftFn (n : ℤ) (s : unitInterval) : Total :=
  ((((s : unitInterval) : ℝ), 0), (n : ℝ))

/-- Helper for Exercise 80.1: the explicit selected-coordinate lift is continuous. -/
lemma continuous_coordinateLiftFn (n : ℤ) : Continuous (coordinateLiftFn n) := by
  -- Only the first real coordinate varies along the unit interval.
  exact (continuous_subtype_val.prodMk continuous_const).prodMk continuous_const

/-- Helper for Exercise 80.1: the explicit selected-coordinate lift as a continuous map. -/
def coordinateLift (n : ℤ) : C(unitInterval, Total) :=
  ⟨coordinateLiftFn n, continuous_coordinateLiftFn n⟩

/-- Helper for Exercise 80.1: the coordinate lift begins with unwrapped value zero. -/
lemma coordinateLift_zero (n : ℤ) : coordinateLift n 0 = (((0, 0), (n : ℝ)) : Total) := by
  -- Evaluate the defining real path at the left endpoint.
  rfl

/-- Helper for Exercise 80.1: the coordinate lift ends with unwrapped value one. -/
lemma coordinateLift_one (n : ℤ) : coordinateLift n 1 = (((1, 0), (n : ℝ)) : Total) := by
  -- Evaluate the defining real path at the right endpoint.
  rfl

/-- Helper for Exercise 80.1: the coordinate lift is not closed. -/
lemma coordinateLift_one_ne_zero (n : ℤ) : coordinateLift n 1 ≠ coordinateLift n 0 := by
  -- Equality would force the distinct real endpoints `1` and `0` to coincide.
  intro h
  have hreal : (1 : ℝ) = 0 := congrArg (fun x : Total ↦ x.1.1) h
  norm_num at hreal

/-- Helper for Exercise 80.1: applying the coordinate cover to the explicit lift gives the
integer translate of the selected-coordinate loop. -/
lemma map_coordinateLiftFn (n : ℤ) (s : unitInterval) :
    map (coordinateLiftFn n s) = n +ᵥ ShiftSuspension.coordinateLoopFn n s := by
  -- Coordinate zero carries the winding path; every other coordinate and the real factor agree.
  change map (coordinateLiftFn n s) =
    ShiftSuspension.translate n (ShiftSuspension.coordinateLoopFn n s)
  apply Prod.ext
  · funext k
    by_cases hk : k = 0
    · subst k
      simp [map_apply_zero, coordinateLiftFn, ShiftSuspension.translate,
        ShiftSuspension.coordinateLoopFn]
    · rw [map_apply_ne_zero _ hk]
      simp [coordinateLiftFn, ShiftSuspension.translate, ShiftSuspension.coordinateLoopFn, hk]
  · simp [map_apply_real, coordinateLiftFn, ShiftSuspension.translate,
      ShiftSuspension.coordinateLoopFn]

/-- Helper for Exercise 80.1: the explicit lift projects to the selected-coordinate base loop. -/
lemma proj_map_coordinateLiftFn (n : ℤ) (s : unitInterval) :
    ShiftSuspension.proj (map (coordinateLiftFn n s)) =
      ShiftSuspension.proj (ShiftSuspension.coordinateLoopFn n s) := by
  -- Rewrite to an integer translate and use invariance of the orbit projection.
  rw [map_coordinateLiftFn]
  exact ShiftSuspension.proj_vadd n _

/-- Helper for Exercise 80.1: the composite of the coordinate cover and shift-suspension
projection is not a covering map. -/
lemma composite_not_isCoveringMap :
    ¬ IsCoveringMap (ShiftSuspension.proj ∘ map) := by
  -- An alleged evenly covered neighborhood at the orbit basepoint has finite coordinate support.
  intro hp
  classical
  let z₀ := ShiftSuspension.proj ShiftSuspension.basepoint
  let e₀ : Total := coordinateLift 0 0
  have he₀ : (ShiftSuspension.proj ∘ map) e₀ = z₀ := by
    calc
      (ShiftSuspension.proj ∘ map) e₀ =
          ShiftSuspension.proj (ShiftSuspension.coordinateLoopFn 0 0) :=
        proj_map_coordinateLiftFn 0 0
      _ = ShiftSuspension.proj ShiftSuspension.basepoint :=
        congrArg ShiftSuspension.proj (ShiftSuspension.coordinateLoopFn_zero 0)
      _ = z₀ := rfl
  letI : Nonempty ((ShiftSuspension.proj ∘ map) ⁻¹' {z₀}) := ⟨⟨e₀, he₀⟩⟩
  let t := (hp z₀).toTrivialization
  have hz₀ : z₀ ∈ t.baseSet := (hp z₀).mem_toTrivialization_baseSet
  let V : Set ShiftSuspension.Total := ShiftSuspension.proj ⁻¹' t.baseSet
  have hV_open : IsOpen V :=
    t.open_baseSet.preimage ShiftSuspension.proj_isCoveringMap.continuous
  have hbasepointV : ShiftSuspension.basepoint ∈ V := hz₀
  have hV_nhds : V ∈ 𝓝 ShiftSuspension.basepoint :=
    hV_open.mem_nhds hbasepointV
  obtain ⟨A, hA, B, hB, hABV⟩ := mem_nhds_prod_iff.mp hV_nhds
  obtain ⟨A₀, hA₀A, hA₀_open, hzeroA₀⟩ := mem_nhds_iff.mp hA
  obtain ⟨J, u, hu, huA₀⟩ :=
    isOpen_pi_iff.mp hA₀_open (0 : ShiftSuspension.Torus) hzeroA₀
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset J
  -- The loop in coordinate `n` lies in the neighborhood because `n` is unrestricted.
  have hloopA₀ (s : unitInterval) :
      (ShiftSuspension.coordinateLoopFn n s).1 ∈ A₀ := by
    apply huA₀
    intro k hk
    have hkn : k ≠ n := fun h ↦ hn (h ▸ hk)
    simpa [ShiftSuspension.coordinateLoopFn, hkn] using (hu k hk).2
  have hloopV (s : unitInterval) : ShiftSuspension.coordinateLoopFn n s ∈ V := by
    apply hABV
    exact ⟨hA₀A (hloopA₀ s), mem_of_mem_nhds hB⟩
  let γ : C(unitInterval, ShiftSuspension.Base) :=
    ⟨fun s ↦ ShiftSuspension.proj (ShiftSuspension.coordinateLoopFn n s),
      ShiftSuspension.proj_isCoveringMap.continuous.comp
        (ShiftSuspension.continuous_coordinateLoopFn n)⟩
  let α : C(unitInterval, Total) := coordinateLift n
  have hγbase (s : unitInterval) : γ s ∈ t.baseSet := hloopV s
  have hzero : γ 0 = (ShiftSuspension.proj ∘ map) (α 0) := by
    simpa [γ, α, coordinateLift, Function.comp_apply] using
      (proj_map_coordinateLiftFn n 0).symm
  have hone : γ 1 = (ShiftSuspension.proj ∘ map) (α 0) := by
    calc
      γ 1 = ShiftSuspension.proj ShiftSuspension.basepoint :=
        congrArg ShiftSuspension.proj (ShiftSuspension.coordinateLoopFn_one n)
      _ = γ 0 :=
        (congrArg ShiftSuspension.proj (ShiftSuspension.coordinateLoopFn_zero n)).symm
      _ = (ShiftSuspension.proj ∘ map) (α 0) := hzero
  have hα : (ShiftSuspension.proj ∘ map) ∘ α = γ := by
    funext s
    exact proj_map_coordinateLiftFn n s
  -- A lift contained in one sheet must close, contradicting its real endpoints `0` and `1`.
  have hclosed : α 1 = α 0 :=
    hp.lift_endpoint_eq_of_trivialization t γ hγbase (α 0) hzero hone α hα rfl
  exact coordinateLift_one_ne_zero n hclosed

/-- Helper for Exercise 80.1: the deck group of the real cover of the unit additive circle. -/
abbrev Deck := zmultiples (1 : ℝ)

/-- Helper for Exercise 80.1: deck translations act on the unwrapped zero coordinate. -/
def translate (g : Deck) (x : Total) : Total :=
  ((g +ᵥ x.1.1, x.1.2), x.2)

/-- Helper for Exercise 80.1: the coordinate-cover source carries the zero-coordinate deck
action. -/
instance instVAdd : VAdd Deck Total := ⟨translate⟩

/-- Helper for Exercise 80.1: zero deck translation fixes the coordinate-cover source. -/
lemma zero_vadd (x : Total) : (0 : Deck) +ᵥ x = x := by
  -- Only the first real coordinate is acted on.
  change translate 0 x = x
  simp [translate]

/-- Helper for Exercise 80.1: successive zero-coordinate deck translations add. -/
lemma add_vadd (g h : Deck) (x : Total) : (g + h) +ᵥ x = g +ᵥ h +ᵥ x := by
  -- The inherited additive action on `ℝ` supplies the action law.
  change translate (g + h) x = translate g (translate h x)
  apply Prod.ext
  · apply Prod.ext
    · exact AddSemigroupAction.add_vadd g h x.1.1
    · rfl
  · rfl

/-- Helper for Exercise 80.1: zero-coordinate deck translations form an additive action. -/
instance instAddAction : AddAction Deck Total where
  zero_vadd := zero_vadd
  add_vadd := add_vadd

/-- Helper for Exercise 80.1: each zero-coordinate deck translation is continuous. -/
lemma continuous_translate (g : Deck) : Continuous fun x : Total ↦ g +ᵥ x := by
  -- Translation on `ℝ` is continuous and the remaining coordinates are unchanged.
  exact ((continuous_const_vadd g).comp continuous_fst.fst).prodMk continuous_fst.snd |>.prodMk
    continuous_snd

/-- Helper for Exercise 80.1: the zero-coordinate deck action is continuous. -/
instance instContinuousConstVAdd : ContinuousConstVAdd Deck Total where
  continuous_const_vadd := continuous_translate

/-- Helper for Exercise 80.1: the split coordinate map is a quotient covering map. -/
private lemma splitMapIsAddQuotientCoveringMap : IsAddQuotientCoveringMap splitMap Deck := by
  let hcoe := AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)
  -- Product with identity maps preserves the quotient-map and local-disjointness interfaces.
  refine
    { toIsQuotientMap :=
        ((hcoe.isOpenQuotientMap.prodMap IsOpenQuotientMap.id).prodMap
          IsOpenQuotientMap.id).isQuotientMap
      toContinuousConstVAdd := inferInstance
      apply_eq_iff_mem_orbit := ?_
      disjoint := ?_ }
  · intro x y
    constructor
    · intro hxy
      have hzero : ((x.1.1 : ℝ) : UnitAddCircle) = (y.1.1 : UnitAddCircle) :=
        congrArg (fun z ↦ z.1.1) hxy
      have hrest : x.1.2 = y.1.2 := congrArg (fun z ↦ z.1.2) hxy
      have hreal : x.2 = y.2 := congrArg (fun z ↦ z.2) hxy
      obtain ⟨g, hg⟩ := AddAction.mem_orbit_iff.mp (hcoe.apply_eq_iff_mem_orbit.mp hzero)
      apply AddAction.mem_orbit_iff.mpr
      refine ⟨g, ?_⟩
      apply Prod.ext
      · exact Prod.ext hg hrest.symm
      · exact hreal.symm
    · intro hxy
      obtain ⟨g, rfl⟩ := AddAction.mem_orbit_iff.mp hxy
      apply Prod.ext
      · apply Prod.ext
        · exact hcoe.apply_eq_iff_mem_orbit.mpr ⟨g, rfl⟩
        · rfl
      · rfl
  · intro x
    obtain ⟨U, hU, hU_disjoint⟩ := hcoe.disjoint x.1.1
    let W : Set Total := (U ×ˢ Set.univ) ×ˢ Set.univ
    refine ⟨W, ?_, ?_⟩
    · have hW : W ∈ 𝓝 ((x.1.1, x.1.2), x.2) := by
        dsimp only [W]
        rw [nhds_prod_eq, nhds_prod_eq]
        exact Filter.prod_mem_prod (Filter.prod_mem_prod hU Filter.univ_mem) Filter.univ_mem
      simpa only [Prod.eta] using hW
    intro g hg
    obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := hg
    apply hU_disjoint g
    refine ⟨g +ᵥ y.1.1, ⟨y.1.1, hy.1.1, rfl⟩, ?_⟩
    change translate g y ∈ W at hz
    exact hz.1.1

/-- Helper for Exercise 80.1: unwrapping coordinate zero is a covering map. -/
lemma isCoveringMap : IsCoveringMap map := by
  -- Transport the split product covering through the coordinate-splitting homeomorphism.
  exact splitMapIsAddQuotientCoveringMap.isCoveringMap.homeomorph_comp splitHomeomorph

/-- Helper for Exercise 80.1: the zero-coordinate cover is surjective. -/
lemma surjective : Function.Surjective map := by
  -- Both the split product cover and the target homeomorphism are surjective.
  exact splitHomeomorph.surjective.comp splitMapIsAddQuotientCoveringMap.surjective

end ShiftCoordinateCover

/-- Companion to Exercise 80.1 (2). There are covering maps `q : X → Y` and `r : Y → Z`
whose composite `r ∘ q` is not a covering map. -/
theorem exists_coveringMap_comp_not_coveringMap :
    ∃ (X : TopCat.{u}) (Y : TopCat.{v}) (Z : TopCat.{w}),
      PathConnectedSpace X ∧ PathConnectedSpace Y ∧ PathConnectedSpace Z ∧
      LocallyPathConnectedSpace X ∧ LocallyPathConnectedSpace Y ∧
      LocallyPathConnectedSpace Z ∧ ∃ (q : X → Y) (r : Y → Z),
        IsCoveringMap q ∧ Function.Surjective q ∧ IsCoveringMap r ∧
        Function.Surjective r ∧ ¬IsCoveringMap (r ∘ q) := by
  -- Transport the concrete shift-suspension counterexample independently to the three universes.
  letI : PathConnectedSpace (ULift.{u} ShiftCoordinateCover.Total) :=
    (Homeomorph.ulift : ULift.{u} ShiftCoordinateCover.Total ≃ₜ
      ShiftCoordinateCover.Total).symm.surjective.pathConnectedSpace
        (Homeomorph.ulift : ULift.{u} ShiftCoordinateCover.Total ≃ₜ
          ShiftCoordinateCover.Total).symm.continuous
  letI : LocallyPathConnectedSpace (ULift.{u} ShiftCoordinateCover.Total) :=
    (Homeomorph.ulift : ULift.{u} ShiftCoordinateCover.Total ≃ₜ
      ShiftCoordinateCover.Total).isLocalHomeomorph.locallyPathConnectedSpace_of_codomain
  letI : PathConnectedSpace (ULift.{v} ShiftSuspension.Total) :=
    (Homeomorph.ulift : ULift.{v} ShiftSuspension.Total ≃ₜ
      ShiftSuspension.Total).symm.surjective.pathConnectedSpace
        (Homeomorph.ulift : ULift.{v} ShiftSuspension.Total ≃ₜ
          ShiftSuspension.Total).symm.continuous
  letI : LocallyPathConnectedSpace (ULift.{v} ShiftSuspension.Total) :=
    (Homeomorph.ulift : ULift.{v} ShiftSuspension.Total ≃ₜ
      ShiftSuspension.Total).isLocalHomeomorph.locallyPathConnectedSpace_of_codomain
  letI : PathConnectedSpace (ULift.{w} ShiftSuspension.Base) :=
    (Homeomorph.ulift : ULift.{w} ShiftSuspension.Base ≃ₜ
      ShiftSuspension.Base).symm.surjective.pathConnectedSpace
        (Homeomorph.ulift : ULift.{w} ShiftSuspension.Base ≃ₜ
          ShiftSuspension.Base).symm.continuous
  letI : LocallyPathConnectedSpace (ULift.{w} ShiftSuspension.Base) :=
    (Homeomorph.ulift : ULift.{w} ShiftSuspension.Base ≃ₜ
      ShiftSuspension.Base).isLocalHomeomorph.locallyPathConnectedSpace_of_codomain
  let X : TopCat.{u} := TopCat.of (ULift.{u} ShiftCoordinateCover.Total)
  let Y : TopCat.{v} := TopCat.of (ULift.{v} ShiftSuspension.Total)
  let Z : TopCat.{w} := TopCat.of (ULift.{w} ShiftSuspension.Base)
  let q : X → Y :=
    Homeomorph.ulift.symm ∘ ShiftCoordinateCover.map ∘ Homeomorph.ulift
  let r : Y → Z :=
    Homeomorph.ulift.symm ∘ ShiftSuspension.proj ∘ Homeomorph.ulift
  have hq : IsCoveringMap q := by
    -- Conjugating the coordinate cover by homeomorphisms preserves covering maps.
    exact (ShiftCoordinateCover.isCoveringMap.homeomorph_comp Homeomorph.ulift.symm).comp_homeomorph
      Homeomorph.ulift
  have hq_surjective : Function.Surjective q := by
    -- Surjectivity is preserved by the same conjugation.
    exact Homeomorph.ulift.symm.surjective.comp
      (ShiftCoordinateCover.surjective.comp Homeomorph.ulift.surjective)
  have hr : IsCoveringMap r := by
    -- Conjugating the orbit projection by homeomorphisms preserves its covering interface.
    exact (ShiftSuspension.proj_isCoveringMap.homeomorph_comp Homeomorph.ulift.symm).comp_homeomorph
      Homeomorph.ulift
  have hr_surjective : Function.Surjective r := by
    -- The orbit projection and both universe homeomorphisms are surjective.
    exact Homeomorph.ulift.symm.surjective.comp
      (ShiftSuspension.proj_surjective.comp Homeomorph.ulift.surjective)
  have hcomp : ¬ IsCoveringMap (r ∘ q) := by
    -- A lifted composite covering would conjugate back to the forbidden concrete composite.
    intro h
    have hconcrete :=
      (h.comp_homeomorph (Homeomorph.ulift.symm :
        ShiftCoordinateCover.Total ≃ₜ ULift.{u} ShiftCoordinateCover.Total)).homeomorph_comp
        (Homeomorph.ulift : ULift.{w} ShiftSuspension.Base ≃ₜ ShiftSuspension.Base)
    apply ShiftCoordinateCover.composite_not_isCoveringMap
    simpa [q, r, Function.comp_def] using hconcrete
  exact ⟨X, Y, Z, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, q, r, hq, hq_surjective, hr, hr_surjective, hcomp⟩
