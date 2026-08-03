module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Connected.LocallyConnected

public section

universe u v w

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Helper for Lemma 80.2: the range of a covering map is both closed and open. -/
lemma isClopen_range {p : E → B} (hp : IsCoveringMap p) : IsClopen (Set.range p) := by
  -- Openness is immediate because a covering map is an open map.
  have hopen : IsOpen (Set.range p) := by
    simpa only [Set.image_univ] using hp.isOpenMap Set.univ isOpen_univ
  -- An evenly covered neighborhood of a point outside the range has empty preimage.
  have hclosed : IsClosed (Set.range p) := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_forall_mem_open]
    intro b hb
    obtain ⟨_, V, hbV, hVopen, _, H, _⟩ := hp b
    refine ⟨V, ?_, hVopen, hbV⟩
    intro b' hb' hb'range
    obtain ⟨e, rfl⟩ := hb'range
    have heV : e ∈ p ⁻¹' V := hb'
    have hfiber := (H ⟨e, heV⟩).2.property
    exact hb ⟨(H ⟨e, heV⟩).2.1, Set.mem_singleton_iff.mp hfiber⟩
  exact ⟨hclosed, hopen⟩

/-- Helper for Lemma 80.2: a covering map from a nonempty space onto a preconnected
base is surjective. -/
lemma surjective_of_preconnected {p : E → B} [PreconnectedSpace B]
    (hp : IsCoveringMap p) (e : E) : Function.Surjective p := by
  -- The nonempty clopen range must be the whole preconnected base.
  rw [← Set.range_eq_univ]
  exact hp.isClopen_range.eq_univ ⟨p e, e, rfl⟩

/-- Helper for Lemma 80.2: varying the base coordinate in a connected
trivialization does not leave the connected component of a point. -/
private lemma trivializationSymm_mem_connectedComponent {F : Type*} [TopologicalSpace F]
    {p : E → B} (t : Bundle.Trivialization F p) (e₀ e : E) {V : Set B}
    (hV : IsConnected V) (hVt : V ⊆ t.baseSet) (he : e ∈ connectedComponent e₀)
    (hpe : p e ∈ V) {b : B} (hb : b ∈ V) :
    t.toOpenPartialHomeomorph.symm (b, (t e).2) ∈ connectedComponent e₀ := by
  let g : B → E := fun b' ↦ t.toOpenPartialHomeomorph.symm (b', (t e).2)
  -- The inverse of a fixed sheet coordinate maps the connected base into one component.
  have hg : ContinuousOn g V :=
    (t.continuousOn_symm_prodMk_left (v := (t e).2)).mono hVt
  have hge : g (p e) = e := t.symm_apply_mk_proj (t.mem_source.mpr (hVt hpe))
  have himage : IsConnected (g '' V) := hV.image g hg
  have hsubset : g '' V ⊆ connectedComponent e :=
    himage.subset_connectedComponent ⟨p e, hpe, hge⟩
  have hgb : g b ∈ connectedComponent e := hsubset ⟨b, hb, rfl⟩
  -- The chosen point and `e₀` determine the same connected component.
  rw [connectedComponent_eq he]
  exact hgb

/-- Helper for Lemma 80.2: a connected part of a covering trivialization evenly
covers the restriction to a chosen connected component. -/
private lemma isEvenlyCovered_restrictConnectedComponent {F : Type*} [TopologicalSpace F]
    [DiscreteTopology F] {p : E → B} (hp : IsCoveringMap p)
    (t : Bundle.Trivialization F p) (e₀ : E) {b : B} {V : Set B}
    (hVopen : IsOpen V) (hbV : b ∈ V) (hV : IsConnected V)
    (hVt : V ⊆ t.baseSet) :
    IsEvenlyCovered (fun x : connectedComponent e₀ ↦ p x) b
      ((fun x : connectedComponent e₀ ↦ p x) ⁻¹' {b}) := by
  let q : connectedComponent e₀ → B := fun x ↦ p x
  let F₀ := {i : F // ∀ b' ∈ V,
    t.toOpenPartialHomeomorph.symm (b', i) ∈ connectedComponent e₀}
  -- A point over `V` determines a sheet coordinate that stays in the component.
  let toFun : q ⁻¹' V → V × F₀ := fun x ↦
    (⟨q x, x.2⟩, ⟨(t x.1.1).2, fun b' hb' ↦
      trivializationSymm_mem_connectedComponent t e₀ x.1.1 hV hVt x.1.2 x.2 hb'⟩)
  let invMem (x : V × F₀) :
      p (t.toOpenPartialHomeomorph.symm (x.1.1, x.2.1)) ∈ V :=
    (t.proj_symm_apply' (hVt x.1.2)).symm ▸ x.1.2
  let invFun : V × F₀ → q ⁻¹' V := fun x ↦
    ⟨⟨t.toOpenPartialHomeomorph.symm (x.1.1, x.2.1), x.2.2 x.1.1 x.1.2⟩, invMem x⟩
  -- The two maps are inverse by the named trivialization identities.
  have leftInv : Function.LeftInverse invFun toFun := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact t.symm_apply_mk_proj (t.mem_source.mpr (hVt x.2))
  have rightInv : Function.RightInverse invFun toFun := by
    intro x
    apply Prod.ext
    · apply Subtype.ext
      exact t.proj_symm_apply' (hVt x.1.2)
    · apply Subtype.ext
      exact congrArg Prod.snd (t.apply_symm_apply' (hVt x.1.2))
  -- Continuity is inherited from the original trivialization in both directions.
  have hval : Continuous (fun x : q ⁻¹' V ↦ (x.1.1 : E)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have htapp : Continuous (fun x : q ⁻¹' V ↦ t x.1.1) :=
    t.continuousOn_toFun.comp_continuous hval fun x ↦ t.mem_source.mpr (hVt x.2)
  have continuousToFun : Continuous toFun := by
    exact (Continuous.subtype_mk (hp.continuous.comp hval) _).prodMk
      (Continuous.subtype_mk (continuous_snd.comp htapp) _)
  have hpair : Continuous (fun x : V × F₀ ↦ (x.1.1, x.2.1)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hinv : Continuous (fun x : V × F₀ ↦
      t.toOpenPartialHomeomorph.symm (x.1.1, x.2.1)) :=
    t.continuousOn_invFun.comp_continuous hpair fun x ↦
      t.mem_target.mpr (hVt x.1.2)
  have continuousInvFun : Continuous invFun := by
    exact Continuous.subtype_mk (Continuous.subtype_mk hinv _) _
  let H : q ⁻¹' V ≃ₜ V × F₀ :=
    { toFun := toFun
      invFun := invFun
      left_inv := leftInv
      right_inv := rightInv
      continuous_toFun := continuousToFun
      continuous_invFun := continuousInvFun }
  -- Package the component chart and replace its index by the canonical fiber.
  have hcovered : IsEvenlyCovered q b F₀ := by
    refine ⟨inferInstance, V, hbV, hVopen, ?_, H, ?_⟩
    · exact hVopen.preimage (hp.continuous.comp continuous_subtype_val)
    · intro x
      rfl
  simpa [q] using hcovered.to_isEvenlyCovered_preimage

/-- Helper for Lemma 80.2: a covering map restricts to a covering map on each
connected component when the base is preconnected and locally connected. -/
lemma restrictConnectedComponent {p : E → B} [PreconnectedSpace B]
    [LocallyConnectedSpace B] (hp : IsCoveringMap p) (e₀ : E) :
    IsCoveringMap (fun x : connectedComponent e₀ ↦ p x) := by
  intro b
  -- The original covering has nonempty fibers over the preconnected base.
  obtain ⟨e, he⟩ := hp.surjective_of_preconnected e₀ b
  letI : Nonempty (p ⁻¹' {b}) := ⟨⟨e, he⟩⟩
  letI : DiscreteTopology (p ⁻¹' {b}) := (hp b).1
  let t := (hp b).toTrivialization
  have hbt : b ∈ t.baseSet := (hp b).mem_toTrivialization_baseSet
  -- Shrink the covering chart to a connected open neighborhood.
  obtain ⟨V, ⟨hVopen, hbV, hV⟩, hVt⟩ :=
    (LocallyConnectedSpace.open_connected_basis b).mem_iff.mp
      (t.open_baseSet.mem_nhds hbt)
  exact isEvenlyCovered_restrictConnectedComponent hp t e₀ hVopen hbV hV hVt

/-- Helper for Lemma 80.2: the restriction of a covering map to a connected
component surjects onto a preconnected, locally connected base. -/
lemma surjective_restrictConnectedComponent {p : E → B} [PreconnectedSpace B]
    [LocallyConnectedSpace B] (hp : IsCoveringMap p) (e₀ : E) :
    Function.Surjective (fun x : connectedComponent e₀ ↦ p x) := by
  -- Apply the clopen-range argument to the component restriction.
  exact (hp.restrictConnectedComponent e₀).surjective_of_preconnected
    ⟨e₀, mem_connectedComponent⟩

/-- Helper for Lemma 80.2: cancellation on the right produces an evenly covered
neighborhood by grouping composite sheets with the same outer sheet coordinate. -/
private lemma isEvenlyCovered_of_comp_right {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [LocallyConnectedSpace Z] {q : X → Y} {r : Y → Z}
    (hq_continuous : Continuous q) (hcomp : IsCoveringMap (r ∘ q))
    (hcomp_surjective : Function.Surjective (r ∘ q)) (hr : IsCoveringMap r)
    (y : Y) : IsEvenlyCovered q y (q ⁻¹' {y}) := by
  classical
  let z := r y
  -- Choose the canonical trivializations of the composite and outer coverings at `z`.
  obtain ⟨x₀, hx₀⟩ := hcomp_surjective z
  letI : Nonempty ((r ∘ q) ⁻¹' {z}) := ⟨⟨x₀, hx₀⟩⟩
  letI : DiscreteTopology ((r ∘ q) ⁻¹' {z}) := (hcomp z).1
  let tcomp := (hcomp z).toTrivialization
  letI : Nonempty (r ⁻¹' {z}) := ⟨⟨y, rfl⟩⟩
  letI : DiscreteTopology (r ⁻¹' {z}) := (hr z).1
  let tout := (hr z).toTrivialization
  have hztcomp : z ∈ tcomp.baseSet := (hcomp z).mem_toTrivialization_baseSet
  have hztout : z ∈ tout.baseSet := (hr z).mem_toTrivialization_baseSet
  -- Shrink both base sets to one connected open neighborhood.
  obtain ⟨V, ⟨hVopen, hzV, hVconnected⟩, hVsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis z).mem_iff.mp
      ((tcomp.open_baseSet.inter tout.open_baseSet).mem_nhds ⟨hztcomp, hztout⟩)
  have hVcomp : V ⊆ tcomp.baseSet := hVsub.trans Set.inter_subset_left
  have hVout : V ⊆ tout.baseSet := hVsub.trans Set.inter_subset_right
  let P := (r ∘ q) ⁻¹' {z}
  let R := r ⁻¹' {z}
  -- `φ` records which outer sheet receives a composite sheet.
  let φ : P → R := fun i ↦
    (tout (q (tcomp.toOpenPartialHomeomorph.symm (z, i)))).2
  let iy : R := (tout y).2
  let I := {i : P // φ i = iy}
  -- Uniqueness of lifts forces the coordinate assignment to be constant over `V`.
  have sheetEq (i : P) : Set.EqOn
      (fun z' ↦ q (tcomp.toOpenPartialHomeomorph.symm (z', i)))
      (fun z' ↦ tout.toOpenPartialHomeomorph.symm (z', φ i)) V := by
    refine hr.eqOn_of_comp_eqOn hVconnected.isPreconnected
      (hq_continuous.comp_continuousOn
        ((tcomp.continuousOn_symm_prodMk_left (v := i)).mono hVcomp))
      ((tout.continuousOn_symm_prodMk_left (v := φ i)).mono hVout) ?_ hzV ?_
    · intro z' hz'
      simp only [Function.comp_apply]
      exact (tcomp.proj_symm_apply' (hVcomp hz')).trans
        (tout.proj_symm_apply' (hVout hz')).symm
    · have hsource : q (tcomp.toOpenPartialHomeomorph.symm (z, i)) ∈ tout.source := by
        have hbase : r (q (tcomp.toOpenPartialHomeomorph.symm (z, i))) = z := by
          simpa only [Function.comp_apply] using tcomp.proj_symm_apply' (hVcomp hzV)
        apply tout.mem_source.mpr
        rw [hbase]
        exact hVout hzV
      have hbase : r (q (tcomp.toOpenPartialHomeomorph.symm (z, i))) = z := by
        simpa only [Function.comp_apply] using tcomp.proj_symm_apply' (hVcomp hzV)
      have hrecover := (tout.symm_apply_mk_proj hsource).symm
      rw [hbase] at hrecover
      simpa only [φ] using hrecover
  -- The chosen outer sheet and the selected composite sheets are open.
  let W : Set Y := r ⁻¹' V ∩ (Prod.snd ∘ tout) ⁻¹' {iy}
  let S (a : I) : Set X := (r ∘ q) ⁻¹' V ∩ (Prod.snd ∘ tcomp) ⁻¹' {a.1}
  have hpreWsub : r ⁻¹' V ⊆ tout.source := by
    intro y' hy'
    exact tout.mem_source.mpr (hVout hy')
  have hWopen : IsOpen W := by
    have hcoord : IsOpen (tout.source ∩ (Prod.snd ∘ tout) ⁻¹' {iy}) :=
      tout.continuousOn_toFun.isOpen_inter_preimage tout.open_source
        (continuous_snd.isOpen_preimage _ (isOpen_discrete {iy}))
    have hinter := (hVopen.preimage hr.continuous).inter hcoord
    rw [← Set.inter_assoc, Set.inter_eq_left.mpr hpreWsub] at hinter
    exact hinter
  have hyW : y ∈ W := by
    refine ⟨hzV, ?_⟩
    simpa only [Set.mem_preimage, Function.comp_apply, iy] using
      Set.mem_singleton (tout y).2
  have hpreSsub : ∀ a : I, (r ∘ q) ⁻¹' V ⊆ tcomp.source := by
    intro a x hx
    exact tcomp.mem_source.mpr (hVcomp hx)
  have hSopen (a : I) : IsOpen (S a) := by
    have hcoord : IsOpen (tcomp.source ∩ (Prod.snd ∘ tcomp) ⁻¹' {a.1}) :=
      tcomp.continuousOn_toFun.isOpen_inter_preimage tcomp.open_source
        (continuous_snd.isOpen_preimage _ (isOpen_discrete {a.1}))
    have hinter := (hVopen.preimage hcomp.continuous).inter hcoord
    rw [← Set.inter_assoc, Set.inter_eq_left.mpr (hpreSsub a)] at hinter
    exact hinter
  -- On a selected composite sheet, `q` lands in the chosen outer sheet.
  have hS_maps (a : I) : Set.MapsTo q (S a) W := by
    intro x hx
    have hxsource : x ∈ tcomp.source := hpreSsub a hx.1
    have hinv : tcomp.toOpenPartialHomeomorph.symm ((r ∘ q) x, a.1) = x := by
      rw [← hx.2]
      exact tcomp.symm_apply_mk_proj hxsource
    have hsheet := sheetEq a.1 hx.1
    dsimp only at hsheet
    rw [hinv] at hsheet
    have hqsource : q x ∈ tout.source := tout.mem_source.mpr (hVout hx.1)
    have htout := congrArg tout hsheet
    rw [tout.apply_symm_apply' (hVout hx.1)] at htout
    refine ⟨hx.1, ?_⟩
    exact (congrArg Prod.snd htout).trans a.2
  -- Each selected sheet maps injectively to `W` because the composite chart fixes its coordinate.
  have hS_inj (a : I) : Set.InjOn q (S a) := by
    intro x hx x' hx' hqxx'
    have htx : tcomp x = tcomp x' := by
      apply Prod.ext
      · exact (tcomp.proj_toFun x (hpreSsub a hx.1)).trans
          ((congrArg r hqxx').trans
            (tcomp.proj_toFun x' (hpreSsub a hx'.1)).symm)
      · exact hx.2.trans hx'.2.symm
    exact tcomp.injOn (hpreSsub a hx.1) (hpreSsub a hx'.1) htx
  -- The sheet equation also supplies every point of `W` from every selected sheet.
  have hS_surj (a : I) : Set.SurjOn q (S a) W := by
    intro y' hy'
    let x' := tcomp.toOpenPartialHomeomorph.symm (r y', a.1)
    have hxbase : (r ∘ q) x' = r y' := tcomp.proj_symm_apply' (hVcomp hy'.1)
    have hsheet := sheetEq a.1 hy'.1
    dsimp only at hsheet
    have hy'source : y' ∈ tout.source := hpreWsub hy'.1
    have hy'recover : tout.toOpenPartialHomeomorph.symm (r y', iy) = y' := by
      rw [← hy'.2]
      exact tout.symm_apply_mk_proj hy'source
    have hqx : q x' = y' := by
      rw [hsheet, a.2, hy'recover]
    refine ⟨x', ?_, hqx⟩
    refine ⟨?_, ?_⟩
    · simpa only [Set.mem_preimage, hxbase] using hy'.1
    exact congrArg Prod.snd (tcomp.apply_symm_apply' (hVcomp hy'.1))
  have hS_pairwise : Pairwise (fun a b ↦ Disjoint (S a) (S b)) := by
    intro a b hab
    refine Set.disjoint_left.mpr fun x hxa hxb ↦ hab ?_
    apply Subtype.ext
    exact hxa.2.symm.trans hxb.2
  -- Every point over `W` determines a selected composite coordinate.
  have hS_exhaustive : q ⁻¹' W ⊆ ⋃ a : I, S a := by
    intro x hx
    have hxbase : (r ∘ q) x ∈ V := hx.1
    have hxsource : x ∈ tcomp.source := tcomp.mem_source.mpr (hVcomp hxbase)
    let i : P := (tcomp x).2
    have hinv : tcomp.toOpenPartialHomeomorph.symm ((r ∘ q) x, i) = x :=
      tcomp.symm_apply_mk_proj hxsource
    have hsheet := sheetEq i hxbase
    dsimp only at hsheet
    rw [hinv] at hsheet
    have hqsource : q x ∈ tout.source := hpreWsub hx.1
    have htout := congrArg tout hsheet
    rw [tout.apply_symm_apply' (hVout hxbase)] at htout
    have hi : φ i = iy := by
      exact (congrArg Prod.snd htout).symm.trans hx.2
    let a : I := ⟨i, hi⟩
    refine Set.mem_iUnion.mpr ⟨a, hxbase, ?_⟩
    rfl
  cases isEmpty_or_nonempty I with
  | inl hI =>
      letI : IsEmpty I := hI
      have hqW : q ⁻¹' W = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro x hx
        obtain ⟨a, _⟩ := Set.mem_iUnion.mp (hS_exhaustive hx)
        exact isEmptyElim a
      -- An absent selected coordinate means that this outer sheet misses the range of `q`.
      exact (IsEvenlyCovered.of_preimage_eq_empty Empty
        (hWopen.mem_nhds hyW) hqW).to_isEvenlyCovered_preimage
  | inr hI =>
      letI : Nonempty I := hI
      letI : Nonempty (Y → X) := ⟨fun _ ↦ (Classical.arbitrary I).1.1⟩
      have hqlocal : IsLocalHomeomorph q :=
        IsLocalHomeomorph.of_comp hcomp.isLocalHomeomorph hr.isLocalHomeomorph hq_continuous
      have hopen_iff (a : I) {A : Set Y} (hAW : A ⊆ W) :
          IsOpen A ↔ IsOpen (q ⁻¹' A ∩ S a) := by
        constructor
        · intro hA
          exact (hA.preimage hq_continuous).inter (hSopen a)
        · intro hA
          have himage : q '' (q ⁻¹' A ∩ S a) = A := by
            apply Set.Subset.antisymm
            · intro y' hy'
              obtain ⟨x, hx, rfl⟩ := hy'
              exact hx.1
            · intro y' hy'
              obtain ⟨x, hxS, hqx⟩ := hS_surj a (hAW hy')
              have hxA : q x ∈ A := by
                simpa only [Set.mem_preimage, hqx] using hy'
              exact ⟨x, ⟨hxA, hxS⟩, hqx⟩
          rw [← himage]
          exact hqlocal.isOpenMap _ hA
      let t := hWopen.trivializationDiscrete S W hopen_iff hS_inj hS_surj
        hS_pairwise hS_exhaustive
      -- The sheet partition is a local trivialization of `q` at `y`.
      exact (IsEvenlyCovered.of_trivialization (t := t) hyW).to_isEvenlyCovered_preimage

/-- Helper for Lemma 80.2: cancellation on the left makes the connected components
of an outer preimage into the sheets of an evenly covered neighborhood. -/
private lemma isEvenlyCovered_of_comp_left {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [LocallyConnectedSpace Y] [LocallyConnectedSpace Z]
    {q : X → Y} {r : Y → Z} (hr_continuous : Continuous r)
    (hcomp : IsCoveringMap (r ∘ q)) (hcomp_surjective : Function.Surjective (r ∘ q))
    (hq : IsCoveringMap q) (hq_surjective : Function.Surjective q) (z : Z) :
    IsEvenlyCovered r z (r ⁻¹' {z}) := by
  classical
  -- Start with a connected open neighborhood inside a composite covering chart.
  obtain ⟨x₀, hx₀⟩ := hcomp_surjective z
  letI : Nonempty ((r ∘ q) ⁻¹' {z}) := ⟨⟨x₀, hx₀⟩⟩
  letI : DiscreteTopology ((r ∘ q) ⁻¹' {z}) := (hcomp z).1
  let tcomp := (hcomp z).toTrivialization
  have hztcomp : z ∈ tcomp.baseSet := (hcomp z).mem_toTrivialization_baseSet
  obtain ⟨V, ⟨hVopen, hzV, hVconnected⟩, hVcomp⟩ :=
    (LocallyConnectedSpace.open_connected_basis z).mem_iff.mp
      (tcomp.open_baseSet.mem_nhds hztcomp)
  let T : Set Y := r ⁻¹' V
  have hTopen : IsOpen T := hVopen.preimage hr_continuous
  letI : LocallyConnectedSpace T := hTopen.locallyConnectedSpace
  let J := ConnectedComponents T
  let rep : J → T := fun j ↦ Classical.choose (ConnectedComponents.surjective_coe j)
  have hrep (j : J) : (rep j : ConnectedComponents T) = j :=
    Classical.choose_spec (ConnectedComponents.surjective_coe j)
  let O (j : J) : Set Y := Subtype.val '' connectedComponent (rep j)
  -- Connected components of the open preimage are open, disjoint, and exhaustive.
  have hOopen (j : J) : IsOpen (O j) :=
    hTopen.isOpenMap_subtype_val _ isOpen_connectedComponent
  have hO_maps (j : J) : Set.MapsTo r (O j) V := by
    intro y hy
    obtain ⟨yT, _, rfl⟩ := hy
    exact yT.property
  have hO_pairwise : Pairwise (fun j k ↦ Disjoint (O j) (O k)) := by
    intro j k hjk
    refine Set.disjoint_left.mpr fun y hyj hyk ↦ hjk ?_
    obtain ⟨a, ha, hay⟩ := hyj
    obtain ⟨b, hb, hby⟩ := hyk
    have hab : a = b := Subtype.ext (hay.trans hby.symm)
    calc
      j = (rep j : ConnectedComponents T) := (hrep j).symm
      _ = (a : ConnectedComponents T) := (ConnectedComponents.coe_eq_coe'.mpr ha).symm
      _ = (b : ConnectedComponents T) := congrArg (fun t : T ↦ (t : ConnectedComponents T)) hab
      _ = (rep k : ConnectedComponents T) := ConnectedComponents.coe_eq_coe'.mpr hb
      _ = k := hrep k
  have hO_exhaustive : r ⁻¹' V ⊆ ⋃ j : J, O j := by
    intro y hy
    let yT : T := ⟨y, hy⟩
    let j : J := (yT : ConnectedComponents T)
    have hycomp : yT ∈ connectedComponent (rep j) := by
      apply ConnectedComponents.coe_eq_coe'.mp
      exact (hrep j).symm
    exact Set.mem_iUnion.mpr ⟨j, yT, hycomp, rfl⟩
  let P := (r ∘ q) ⁻¹' {z}
  -- Each component maps onto `V`: follow one composite sheet across the connected base.
  have hO_surj (j : J) : Set.SurjOn r (O j) V := by
    let y₀ : T := rep j
    obtain ⟨x, hqx⟩ := hq_surjective y₀.1
    have hxbase : (r ∘ q) x ∈ V := by
      change r (q x) ∈ V
      rw [hqx]
      exact y₀.property
    have hxsource : x ∈ tcomp.source := tcomp.mem_source.mpr (hVcomp hxbase)
    let i : P := (tcomp x).2
    have gmem (b : V) :
        r (q (tcomp.toOpenPartialHomeomorph.symm (b.1, i))) ∈ V := by
      have hproj : r (q (tcomp.toOpenPartialHomeomorph.symm (b.1, i))) = b.1 := by
        simpa only [Function.comp_apply] using
          tcomp.proj_symm_apply' (x := i) (hVcomp b.2)
      rw [hproj]
      exact b.2
    let g : V → T := fun b ↦
      ⟨q (tcomp.toOpenPartialHomeomorph.symm (b.1, i)), gmem b⟩
    have hinv : Continuous (fun b : V ↦
        tcomp.toOpenPartialHomeomorph.symm (b.1, i)) :=
      (tcomp.continuousOn_symm_prodMk_left (v := i)).comp_continuous
        continuous_subtype_val fun b ↦ hVcomp b.2
    have hg : Continuous g :=
      Continuous.subtype_mk (hq.continuous.comp hinv) _
    letI : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVconnected
    let b₀ : V := ⟨r y₀.1, y₀.property⟩
    have hgb₀ : g b₀ = y₀ := by
      apply Subtype.ext
      have hrecover := tcomp.symm_apply_mk_proj hxsource
      simpa only [g, b₀, i, Function.comp_apply, hqx] using congrArg q hrecover
    have hgrange : Set.range g ⊆ connectedComponent y₀ :=
      (isConnected_range hg).subset_connectedComponent ⟨b₀, hgb₀⟩
    intro z' hz'
    let b : V := ⟨z', hz'⟩
    have hgb : g b ∈ connectedComponent (rep j) := hgrange ⟨b, rfl⟩
    refine ⟨(g b).1, ⟨g b, hgb, rfl⟩, ?_⟩
    exact tcomp.proj_symm_apply' (hVcomp hz')
  -- A component is also injective: lift it through one connected component of the restricted `q`.
  have hO_inj (j : J) : Set.InjOn r (O j) := by
    let C : Set T := connectedComponent (rep j)
    let qT := T.restrictPreimage q
    let qC := C.restrictPreimage qT
    letI : PreconnectedSpace C :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_connectedComponent
    letI : LocallyConnectedSpace C := isOpen_connectedComponent.locallyConnectedSpace
    have hqC : IsCoveringMap qC := (hq.restrictPreimage T).restrictPreimage C
    let y₀ : T := rep j
    obtain ⟨x, hqx⟩ := hq_surjective y₀.1
    have hxT : q x ∈ T := by
      simpa only [hqx] using y₀.property
    let xT : q ⁻¹' T := ⟨x, hxT⟩
    have hxC : qT xT ∈ C := by
      have heq : qT xT = y₀ := Subtype.ext hqx
      rw [heq]
      exact mem_connectedComponent
    let D := qT ⁻¹' C
    let d₀ : D := ⟨xT, hxC⟩
    have hqCsurj := hqC.surjective_restrictConnectedComponent d₀
    have hDsource (d : D) : d.1.1 ∈ tcomp.source := by
      exact tcomp.mem_source.mpr (hVcomp d.1.2)
    let coord : D → P := fun d ↦ (tcomp d.1.1).2
    have hval : Continuous (fun d : D ↦ d.1.1) :=
      continuous_subtype_val.comp continuous_subtype_val
    have htcomp : Continuous (fun d : D ↦ tcomp d.1.1) :=
      tcomp.continuousOn_toFun.comp_continuous hval hDsource
    have hcoord : Continuous coord := continuous_snd.comp htcomp
    have hcoord_constant (d : connectedComponent d₀) : coord d = coord d₀ :=
      isPreconnected_connectedComponent.constant hcoord.continuousOn
        d.property mem_connectedComponent
    intro a ha b hb hrab
    obtain ⟨aT, haC, rfl⟩ := ha
    obtain ⟨bT, hbC, rfl⟩ := hb
    obtain ⟨da, hda⟩ := hqCsurj ⟨aT, haC⟩
    obtain ⟨db, hdb⟩ := hqCsurj ⟨bT, hbC⟩
    have hqda : q da.1.1.1 = aT.1 :=
      congrArg (fun c : C ↦ c.1.1) hda
    have hqdb : q db.1.1.1 = bT.1 :=
      congrArg (fun c : C ↦ c.1.1) hdb
    have ht : tcomp da.1.1.1 = tcomp db.1.1.1 := by
      apply Prod.ext
      · exact (tcomp.proj_toFun _ (hDsource da.1)).trans
          (((congrArg r hqda).trans (hrab.trans (congrArg r hqdb).symm)).trans
            (tcomp.proj_toFun _ (hDsource db.1)).symm)
      · exact (hcoord_constant da).trans (hcoord_constant db).symm
    have hdab : da.1.1.1 = db.1.1.1 :=
      tcomp.injOn (hDsource da.1) (hDsource db.1) ht
    exact hqda.symm.trans ((congrArg q hdab).trans hqdb)
  -- Surjectivity of `q` transfers openness from the composite to `r`.
  have hr_open : IsOpenMap r := by
    intro A hA
    have himage : r '' A = (r ∘ q) '' (q ⁻¹' A) := by
      apply Set.Subset.antisymm
      · intro z' hz'
        obtain ⟨y, hyA, rfl⟩ := hz'
        obtain ⟨x, hqx⟩ := hq_surjective y
        have hxA : q x ∈ A := by
          simpa only [Set.mem_preimage, hqx] using hyA
        exact ⟨x, hxA, congrArg r hqx⟩
      · intro z' hz'
        obtain ⟨x, hxA, rfl⟩ := hz'
        exact ⟨q x, hxA, rfl⟩
    rw [himage]
    exact hcomp.isOpenMap _ (hA.preimage hq.continuous)
  have hopen_iff (j : J) {A : Set Z} (hAV : A ⊆ V) :
      IsOpen A ↔ IsOpen (r ⁻¹' A ∩ O j) := by
    constructor
    · intro hA
      exact (hA.preimage hr_continuous).inter (hOopen j)
    · intro hA
      have himage : r '' (r ⁻¹' A ∩ O j) = A := by
        apply Set.Subset.antisymm
        · intro z' hz'
          obtain ⟨y, hy, rfl⟩ := hz'
          exact hy.1
        · intro z' hz'
          obtain ⟨y, hyO, hry⟩ := hO_surj j (hAV hz')
          have hyA : r y ∈ A := by
            simpa only [hry] using hz'
          exact ⟨y, ⟨hyA, hyO⟩, hry⟩
      rw [← himage]
      exact hr_open _ hA
  have hx₀T : q x₀ ∈ T := by
    change (r ∘ q) x₀ ∈ V
    rw [hx₀]
    exact hzV
  letI : Nonempty T := ⟨⟨q x₀, hx₀T⟩⟩
  letI : Nonempty J := inferInstance
  letI : Nonempty (Z → Y) := ⟨fun _ ↦ (rep (Classical.arbitrary J)).1⟩
  let t := hVopen.trivializationDiscrete O V hopen_iff hO_inj hO_surj
    hO_pairwise hO_exhaustive
  -- The component partition is the desired outer covering chart.
  exact (IsEvenlyCovered.of_trivialization (t := t) hzV).to_isEvenlyCovered_preimage

end IsCoveringMap

/-- Lemma 80.2 (1). Let `p : X → Z`, `q : X → Y`, and `r : Y → Z` be continuous
maps with `p = r ∘ q`. If `p` and `r` are covering maps in the surjective sense,
then so is `q`. -/
theorem coveringMap_of_comp_right {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [PreconnectedSpace Y] [LocallyConnectedSpace Z]
    {p : X → Z} {q : X → Y} {r : Y → Z}
    (hq_continuous : Continuous q) (hpq : p = r ∘ q) (hp : IsCoveringMap p)
    (hp_surjective : Function.Surjective p) (hr : IsCoveringMap r) :
    IsCoveringMap q ∧ Function.Surjective q := by
  -- Route correction: this declaration alone owns the label; the left-cancellation
  -- result is a companion.
  -- Normalize the composite before constructing its local sheets.
  rw [hpq] at hp hp_surjective
  have hq : IsCoveringMap q := fun y ↦
    IsCoveringMap.isEvenlyCovered_of_comp_right
      hq_continuous hp hp_surjective hr y
  constructor
  · exact hq
  · intro y
    obtain ⟨x, _⟩ := hp_surjective (r y)
    exact hq.surjective_of_preconnected x y

/-- Companion to Lemma 80.2 (2). Let `p : X → Z`, `q : X → Y`, and `r : Y → Z` be continuous
maps with `p = r ∘ q`. If `p` and `q` are covering maps in the surjective sense,
then so is `r`. -/
theorem coveringMap_of_comp_left {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [LocallyConnectedSpace Y] [LocallyConnectedSpace Z]
    {p : X → Z} {q : X → Y} {r : Y → Z}
    (hr_continuous : Continuous r) (hpq : p = r ∘ q) (hp : IsCoveringMap p)
    (hp_surjective : Function.Surjective p) (hq : IsCoveringMap q)
    (hq_surjective : Function.Surjective q) :
    IsCoveringMap r ∧ Function.Surjective r := by
  -- Normalize the composite before assembling componentwise local sheets.
  rw [hpq] at hp hp_surjective
  constructor
  · intro z
    exact IsCoveringMap.isEvenlyCovered_of_comp_left
      hr_continuous hp hp_surjective hq hq_surjective z
  · exact Function.Surjective.of_comp hp_surjective
