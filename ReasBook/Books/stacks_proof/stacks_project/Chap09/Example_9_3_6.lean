import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold Topology

universe u

section

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

private noncomputable abbrev chartExpression (x : X) (f : X → ℂ) : ℂ → ℂ :=
  writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f

/-- A representative for the meromorphic function field is meromorphic if, in every complex
chart, its coordinate expression is meromorphic at the charted point. -/
def MeromorphicFunctionField.IsMeromorphic (f : X → ℂ) : Prop :=
  ∀ x, MeromorphicAt (chartExpression X x f) (extChartAt 𝓘(ℂ) x x)

private abbrev IsMeromorphic (f : X → ℂ) : Prop :=
  MeromorphicFunctionField.IsMeromorphic X f

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Constant functions are meromorphic representatives for the meromorphic function field. -/
theorem MeromorphicFunctionField.isMeromorphic_const (c : ℂ) :
    MeromorphicFunctionField.IsMeromorphic X (fun _ ↦ c) := by
  intro x
  change MeromorphicAt (fun _ : ℂ ↦ c) ((chartAt ℂ x) x)
  exact MeromorphicAt.const c ((chartAt ℂ x) x)

private def meromorphicSubalgebra : Subalgebra ℂ (X → ℂ) where
  carrier := {f | IsMeromorphic X f}
  zero_mem' := by
    intro x
    change MeromorphicAt (fun _ : ℂ ↦ (0 : ℂ)) ((chartAt ℂ x) x)
    exact MeromorphicAt.const (0 : ℂ) ((chartAt ℂ x) x)
  add_mem' := by
    intro f g hf hg x
    simpa [IsMeromorphic, writtenInExtChartAt, Function.comp] using (hf x).add (hg x)
  one_mem' := by
    intro x
    change MeromorphicAt (fun _ : ℂ ↦ (1 : ℂ)) ((chartAt ℂ x) x)
    exact MeromorphicAt.const (1 : ℂ) ((chartAt ℂ x) x)
  mul_mem' := by
    intro f g hf hg x
    simpa [IsMeromorphic, writtenInExtChartAt, Function.comp] using (hf x).mul (hg x)
  algebraMap_mem' := by
    intro c x
    exact MeromorphicFunctionField.isMeromorphic_const X c x

omit [IsManifold 𝓘(ℂ) 1 X] in
private theorem isMeromorphic_inv {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X f⁻¹ := by
  intro x
  change MeromorphicAt ((chartExpression X x f)⁻¹) ((chartAt ℂ x) x)
  simpa [IsMeromorphic, chartExpression] using (hf x).inv

private noncomputable instance : Inv ↥(meromorphicSubalgebra X) where
  inv f := ⟨(f : X → ℂ)⁻¹, isMeromorphic_inv X f.property⟩

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Helper for Chap09 Example 9 3 6: inverse representatives in the meromorphic
subalgebra are computed pointwise. -/
private theorem meromorphicSubalgebra_inv_apply (f : ↥(meromorphicSubalgebra X)) (x : X) :
    ((f⁻¹ : ↥(meromorphicSubalgebra X)) : X → ℂ) x = ((f : X → ℂ) x)⁻¹ := by
  -- The inverse operation on representatives was defined by pointwise inversion.
  rfl

private def meromorphicCon : RingCon ↥(meromorphicSubalgebra X) where
  r f g := (f : X → ℂ) =ᶠ[Filter.codiscrete X] (g : X → ℂ)
  iseqv := ⟨fun f ↦ Filter.EventuallyEq.rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩
  add' := by
    intro a b c d hab hcd
    exact hab.add hcd
  mul' := by
    intro a b c d hab hcd
    exact hab.mul hcd

/-- The meromorphic function field `ℂ(X)`, realized as meromorphic representatives modulo
codiscrete equality, which forgets inessential point values at isolated poles. -/
abbrev MeromorphicFunctionField := RingCon.Quotient (meromorphicCon X)

/-- The quotient class of a meromorphic representative in the meromorphic function field. -/
noncomputable def MeromorphicFunctionField.mk (f : X → ℂ)
    (hf : MeromorphicFunctionField.IsMeromorphic X f) : MeromorphicFunctionField X :=
  ↑(⟨f, hf⟩ : meromorphicSubalgebra X)

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Meromorphic representatives that agree on the codiscrete filter define the same element of
the meromorphic function field. -/
theorem MeromorphicFunctionField.mk_eq_mk_of_eventuallyEq {f g : X → ℂ}
    {hf : MeromorphicFunctionField.IsMeromorphic X f}
    {hg : MeromorphicFunctionField.IsMeromorphic X g}
    (h : f =ᶠ[Filter.codiscrete X] g) :
    MeromorphicFunctionField.mk X f hf = MeromorphicFunctionField.mk X g hg := by
  change (↑(⟨f, hf⟩ : meromorphicSubalgebra X) : MeromorphicFunctionField X) =
    ↑(⟨g, hg⟩ : meromorphicSubalgebra X)
  apply (RingCon.eq (meromorphicCon X)).mpr
  exact h

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- A meromorphic representative that is codiscretely zero defines zero in the meromorphic
function field. -/
theorem MeromorphicFunctionField.mk_eq_zero_of_eventuallyEq_zero {f : X → ℂ}
    {hf : MeromorphicFunctionField.IsMeromorphic X f}
    (h : f =ᶠ[Filter.codiscrete X] 0) :
    MeromorphicFunctionField.mk X f hf = 0 := by
  change (↑(⟨f, hf⟩ : meromorphicSubalgebra X) : MeromorphicFunctionField X) =
    ↑(0 : meromorphicSubalgebra X)
  apply (RingCon.eq (meromorphicCon X)).mpr
  exact h

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- A meromorphic representative that is codiscretely constant defines the corresponding
constant element of the meromorphic function field. -/
theorem MeromorphicFunctionField.mk_eq_algebraMap_of_eventuallyEq_const {f : X → ℂ}
    {hf : MeromorphicFunctionField.IsMeromorphic X f} {c : ℂ}
    (h : f =ᶠ[Filter.codiscrete X] (fun _ ↦ c)) :
    MeromorphicFunctionField.mk X f hf = algebraMap ℂ (MeromorphicFunctionField X) c := by
  change (↑(⟨f, hf⟩ : meromorphicSubalgebra X) : MeromorphicFunctionField X) =
    ↑(algebraMap ℂ (meromorphicSubalgebra X) c)
  apply (RingCon.eq (meromorphicCon X)).mpr
  exact h

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Helper for Chap09 Example 9.3.6: if a representative gives a constant element of the
meromorphic function field, then it is codiscretely equal to that constant. -/
theorem MeromorphicFunctionField.eventuallyEq_const_of_mk_eq_algebraMap {f : X → ℂ}
    {hf : MeromorphicFunctionField.IsMeromorphic X f} {c : ℂ}
    (h : MeromorphicFunctionField.mk X f hf = algebraMap ℂ (MeromorphicFunctionField X) c) :
    f =ᶠ[Filter.codiscrete X] (fun _ ↦ c) := by
  change (↑(⟨f, hf⟩ : meromorphicSubalgebra X) : MeromorphicFunctionField X) =
    ↑(algebraMap ℂ (meromorphicSubalgebra X) c) at h
  exact (RingCon.eq (meromorphicCon X)).mp h

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Helper for Chap09 Example 9.3.6: a representative that is not codiscretely constant gives a
nonconstant element of the meromorphic function field. -/
theorem MeromorphicFunctionField.mk_notMem_range_algebraMap_of_forall_not_eventuallyEq_const
    {f : X → ℂ} {hf : MeromorphicFunctionField.IsMeromorphic X f}
    (h : ∀ c : ℂ, ¬ f =ᶠ[Filter.codiscrete X] (fun _ ↦ c)) :
    MeromorphicFunctionField.mk X f hf ∉
      Set.range (algebraMap ℂ (MeromorphicFunctionField X)) := by
  rintro ⟨c, hc⟩
  exact h c <|
    MeromorphicFunctionField.eventuallyEq_const_of_mk_eq_algebraMap X hc.symm

end

notation:max "ℂ(" X ")" => MeromorphicFunctionField X

section

variable (X : Type u) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X]

omit [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] in
/-- Helper for Chap09 Example 9 3 6: a complex chart around any point contains two distinct
points of the source. -/
private theorem complexChartedSpace_nontrivial (x : X) : Nontrivial X := by
  -- A punctured neighborhood in the chart target is nonempty because `ℂ` is perfect.
  let e := chartAt ℂ x
  let p : ℂ := e x
  have htarget : e.target ∈ 𝓝 p := by
    simpa [e, p] using chart_target_mem_nhds (H := ℂ) x
  have htarget' : e.target ∈ 𝓝[≠] p := mem_nhdsWithin_of_mem_nhds htarget
  have hpunct : ({p}ᶜ : Set ℂ) ∈ 𝓝[≠] p := self_mem_nhdsWithin
  obtain ⟨y, hy_target, hy_ne⟩ :=
    (Filter.NeBot.nonempty_of_mem (inferInstance : Filter.NeBot (𝓝[≠] p))
      (Filter.inter_mem htarget' hpunct))
  -- Pull the second chart point back to `X` and compare it with the base point.
  refine nontrivial_iff.2 ⟨e.symm y, x, ?_⟩
  intro hsymm
  apply hy_ne
  have hy_eq : e (e.symm y) = y := e.right_inv hy_target
  calc
    y = e (e.symm y) := hy_eq.symm
    _ = e x := by rw [hsymm]
    _ = p := rfl

omit [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] in
/-- Helper for Chap09 Example 9 3 6: the chosen chart maps punctured neighborhoods to
punctured neighborhoods. -/
private theorem chartAt_tendsto_punctured_nhds (x : X) :
    Filter.Tendsto (chartAt ℂ x) (𝓝[≠] x) (𝓝[≠] ((chartAt ℂ x) x)) := by
  -- Continuity gives the ordinary limit, and local injectivity keeps away from the base point.
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (chartAt ℂ x) ?_ ?_
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x)).tendsto
  · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (chartAt ℂ x).eventually_ne_nhdsWithin (mem_chart_source ℂ x)

omit [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] in
/-- Helper for Chap09 Example 9 3 6: pulling a chart expression back by the chart recovers the
original function near the base point. -/
private theorem chartExpression_comp_chartAt_eventuallyEq (x : X) (f : X → ℂ) :
    (fun y ↦ chartExpression X x f ((chartAt ℂ x) y)) =ᶠ[𝓝[≠] x] f := by
  -- On the chart source, the chart inverse cancels the chart itself.
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (chart_source_mem_nhds ℂ x)]
    with y hy
  simp [chartExpression, writtenInExtChartAt, (chartAt ℂ x).left_inv hy]

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Helper for Chap09 Example 9 3 6: punctured neighborhoods on a connected complex
manifold are nontrivial. -/
private theorem manifold_punctured_nhds_neBot (x : X) :
    Filter.NeBot (𝓝[≠] x) := by
  -- The complex chart supplies nontriviality, so the connected T1-space instance has no
  -- isolated points.
  letI : T1Space X := (𝓘(ℂ)).t1Space X
  letI : Nontrivial X := complexChartedSpace_nontrivial X x
  exact inferInstance

omit [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] in
/-- Helper for Chap09 Example 9 3 6: a meromorphic representative is either eventually
zero or eventually nonzero on each punctured neighborhood. -/
private theorem isMeromorphic_eventually_eq_zero_or_eventually_ne_zero {f : X → ℂ}
    (hf : IsMeromorphic X f) (x : X) :
    f =ᶠ[𝓝[≠] x] 0 ∨ ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 := by
  -- Apply the one-variable meromorphic dichotomy in the chart coordinates.
  have hfx : MeromorphicAt (chartExpression X x f) ((chartAt ℂ x) x) := by
    simpa [IsMeromorphic, chartExpression] using hf x
  rcases hfx.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
  · left
    -- Transport the coordinate zero statement through the chart and rewrite to `f`.
    have hpull : ∀ᶠ y in 𝓝[≠] x, chartExpression X x f ((chartAt ℂ x) y) = 0 :=
      (chartAt_tendsto_punctured_nhds X x).eventually hzero
    have hrew := chartExpression_comp_chartAt_eventuallyEq X x f
    filter_upwards [hpull, hrew] with y hy hxy
    simpa [hxy.symm] using hy
  · right
    -- The nonzero branch is transported through the same chart bridge.
    have hpull : ∀ᶠ y in 𝓝[≠] x, chartExpression X x f ((chartAt ℂ x) y) ≠ 0 :=
      (chartAt_tendsto_punctured_nhds X x).eventually hnonzero
    have hrew := chartExpression_comp_chartAt_eventuallyEq X x f
    filter_upwards [hpull, hrew] with y hy hxy
    simpa [hxy.symm] using hy

omit [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X] in
/-- Helper for Chap09 Example 9 3 6: if a function has a zero/nonzero punctured-neighborhood
dichotomy at every point, then its zero-germ locus is clopen. -/
private theorem eventuallyEqZeroSet_isClopen [T1Space X] (f : X → ℂ)
    (hdich : ∀ x : X, f =ᶠ[𝓝[≠] x] 0 ∨ ∀ᶠ y in 𝓝[≠] x, f y ≠ 0)
    (hne : ∀ x : X, Filter.NeBot (𝓝[≠] x)) :
    IsClopen {x | f =ᶠ[𝓝[≠] x] 0} := by
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    -- At a point outside the zero-germ locus, the local dichotomy gives a nonzero punctured
    -- neighborhood, which excludes nearby zero germs by nontriviality of punctured filters.
    have hz_not : ¬ f =ᶠ[𝓝[≠] z] 0 := by simpa using hz
    rcases hdich z with hzero | hnonzero
    · exact False.elim (hz_not hzero)
    obtain ⟨t, ht_nonzero, ht_open, hz_mem⟩ :=
      eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hnonzero)
    refine ⟨t, ?_, ht_open, hz_mem⟩
    intro w hw hwS
    change ∀ᶠ y in 𝓝[≠] w, f y = (0 : X → ℂ) y at hwS
    by_cases hwz : w = z
    · exact hz_not (by simpa [hwz] using hwS)
    · have hnonzero_w : ∀ᶠ y in 𝓝[≠] w, f y ≠ 0 := by
        rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
        refine ⟨t \ {z}, ?_, ht_open.sdiff isClosed_singleton, ?_⟩
        · intro y hy _hyw
          exact ht_nonzero y hy.1 hy.2
        · exact ⟨hw, by simpa [Set.mem_singleton_iff] using hwz⟩
      have hcontra : ∀ᶠ y in 𝓝[≠] w, f y = (0 : X → ℂ) y ∧ f y ≠ 0 :=
        hwS.and hnonzero_w
      obtain ⟨y, hy⟩ := (hne w).nonempty_of_mem hcontra
      exact hy.2 (by simpa using hy.1)
  · rw [isOpen_iff_forall_mem_open]
    intro z hz
    -- A zero punctured neighborhood at `z` remains zero at every nearby point in the same
    -- neighborhood, after deleting `z`.
    obtain ⟨t, ht_zero, ht_open, hz_mem⟩ :=
      eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hz)
    refine ⟨t, ?_, ht_open, hz_mem⟩
    intro w hw
    change ∀ᶠ y in 𝓝[≠] w, f y = (0 : X → ℂ) y
    by_cases hwz : w = z
    · simpa [hwz] using hz
    · rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
      refine ⟨t \ {z}, ?_, ht_open.sdiff isClosed_singleton, ?_⟩
      · intro y hy _hyw
        exact ht_zero y hy.1 hy.2
      · exact ⟨hw, by simpa [Set.mem_singleton_iff] using hwz⟩

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Helper for Chap09 Example 9 3 6: on a connected manifold, a meromorphic
representative is either codiscretely zero or codiscretely nonzero. -/
private theorem isMeromorphic_eq_zero_or_nonzero_mem_codiscrete {f : X → ℂ}
    (hf : IsMeromorphic X f) :
    f =ᶠ[Filter.codiscrete X] 0 ∨ {x | f x ≠ 0} ∈ Filter.codiscrete X := by
  -- The zero-germ locus is clopen, hence either empty or all of the connected space.
  letI : T1Space X := (𝓘(ℂ)).t1Space X
  have hclopen : IsClopen {x | f =ᶠ[𝓝[≠] x] 0} :=
    eventuallyEqZeroSet_isClopen X f
      (fun x ↦ isMeromorphic_eventually_eq_zero_or_eventually_ne_zero X hf x)
      (fun x ↦ manifold_punctured_nhds_neBot X x)
  rcases isClopen_iff.mp hclopen with hzeroSet | hzeroSet
  · right
    rw [mem_codiscrete]
    intro x
    rw [Filter.disjoint_principal_right]
    -- Empty zero-germ locus forces the nonzero branch at every point.
    have hx_not : ¬ f =ᶠ[𝓝[≠] x] 0 := by
      intro hx_zero
      have hx_mem : x ∈ ({x | f =ᶠ[𝓝[≠] x] 0} : Set X) := hx_zero
      rw [hzeroSet] at hx_mem
      exact hx_mem
    rcases isMeromorphic_eventually_eq_zero_or_eventually_ne_zero X hf x with hx_zero | hx_nonzero
    · exact False.elim (hx_not hx_zero)
    · simpa using hx_nonzero
  · left
    rw [Filter.EventuallyEq, Filter.Eventually, mem_codiscrete]
    intro x
    rw [Filter.disjoint_principal_right]
    -- If every point has zero germ, those germs are exactly the codiscrete zero equality.
    have hx_mem : x ∈ ({x | f =ᶠ[𝓝[≠] x] 0} : Set X) := by
      rw [hzeroSet]
      exact Set.mem_univ x
    change ∀ᶠ y in 𝓝[≠] x, f y = (0 : X → ℂ) y at hx_mem
    simpa using hx_mem

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- Helper for Chap09 Example 9 3 6: the codiscrete filter of the connected complex manifold is
nontrivial. -/
private theorem codiscrete_neBot : Filter.NeBot (Filter.codiscrete X) := by
  rw [Filter.neBot_iff]
  intro hbot
  -- If the codiscrete filter were bottom, the empty set would be codiscrete.
  have hempty : (∅ : Set X) ∈ Filter.codiscrete X := by
    rw [Filter.empty_mem_iff_bot]
    exact hbot
  rw [mem_codiscrete] at hempty
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hxempty : (∅ : Set X) ∈ 𝓝[≠] x := by
    simpa using (Filter.disjoint_principal_right.mp (hempty x))
  exact @Filter.empty_notMem X (𝓝[≠] x) (manifold_punctured_nhds_neBot X x) hxempty

omit [IsManifold 𝓘(ℂ) 1 X] in
private theorem meromorphicFunctionField_zero_ne_one :
    (0 : ℂ(X)) ≠ 1 := by
  intro h
  -- Equality of quotient constants would make the contradictory constant equality hold on a
  -- codiscrete set.
  have hrel : ((0 : ↥(meromorphicSubalgebra X)) : X → ℂ) =ᶠ[Filter.codiscrete X]
      ((1 : ↥(meromorphicSubalgebra X)) : X → ℂ) := by
    have hrel' := (RingCon.eq (meromorphicCon X)).mp h
    simpa [meromorphicCon] using hrel'
  have hbad : ∀ᶠ (_ : X) in Filter.codiscrete X, (0 : ℂ) = 1 := hrel
  obtain ⟨x, hx⟩ := (codiscrete_neBot X).nonempty_of_mem hbad
  norm_num at hx

noncomputable instance : Nontrivial (ℂ(X)) :=
  ⟨0, 1, meromorphicFunctionField_zero_ne_one X⟩

omit [IsManifold 𝓘(ℂ) 1 X] in
private theorem meromorphicFunctionField_isUnit_or_eq_zero (f : ℂ(X)) :
    IsUnit f ∨ f = 0 := by
  -- Work with a representative and use the global zero/nonzero dichotomy for that representative.
  refine Quotient.inductionOn f ?_
  intro a
  rcases isMeromorphic_eq_zero_or_nonzero_mem_codiscrete X a.property with hzero | hnonzero
  · right
    apply (RingCon.eq (meromorphicCon X)).mpr
    simpa [meromorphicCon] using hzero
  · left
    rw [isUnit_iff_exists_inv]
    refine ⟨(↑(a⁻¹) : ℂ(X)), ?_⟩
    apply (RingCon.eq (meromorphicCon X)).mpr
    rw [meromorphicCon]
    -- On the codiscrete nonzero set, the pointwise inverse is a multiplicative inverse.
    filter_upwards [hnonzero] with x hx
    simpa [meromorphicSubalgebra_inv_apply] using mul_inv_cancel₀ hx

/-
Pipeline pseudo-name for the anonymous field instance below:
instance anonymous Field instance for MeromorphicFunctionField
-/
/-- Chap09 Example 9 3 6: the meromorphic function field `ℂ(X)` of a connected Riemann
surface carries its canonical field structure. -/
noncomputable instance : Field (MeromorphicFunctionField X) :=
  Field.ofIsUnitOrEqZero fun f ↦ meromorphicFunctionField_isUnit_or_eq_zero X f

end
