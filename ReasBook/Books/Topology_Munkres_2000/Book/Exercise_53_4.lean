module

public import Mathlib.Topology.Covering.Basic

public section

universe u v w

namespace IsCoveringMap

/-- Helper for Exercise 53.4: a composite of covering maps is evenly covered at a point
whose fiber under the second map is finite. -/
private lemma evenlyCovered_comp_of_finite_fiber {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {q : X → Y} {r : Y → Z} (hq : IsCoveringMap q) (hr : IsCoveringMap r)
    (z : Z) [Finite {y : Y // r y = z}] :
    IsEvenlyCovered (r ∘ q) z ((r ∘ q) ⁻¹' {z}) := by
  classical
  let R := {y : Y // r y = z}
  cases isEmpty_or_nonempty R with
  | inl hR =>
      letI : IsEmpty R := hR
      obtain ⟨_, V, hzV, hV, _, H, _⟩ := hr z
      letI : IsEmpty (r ⁻¹' V) := ⟨fun a ↦ hR.false (H a).2⟩
      have hrV : r ⁻¹' V = ∅ := Set.eq_empty_of_isEmpty _
      have hcompV : (r ∘ q) ⁻¹' V = ∅ := by
        rw [Set.preimage_comp, hrV, Set.preimage_empty]
      -- An empty outer fiber remains empty on a whole evenly covered neighborhood.
      exact (IsEvenlyCovered.of_preimage_eq_empty Empty
        (hV.mem_nhds hzV) hcompV).to_isEvenlyCovered_preimage
  | inr hR =>
      letI : Nonempty R := hR
      obtain ⟨hRdisc, V, hzV, hV, hrV, H, hH⟩ := hr z
      letI : DiscreteTopology R := hRdisc
      let y (i : R) : Y := H.symm (⟨z, hzV⟩, i)
      letI : ∀ i : R, DiscreteTopology (q ⁻¹' {y i}) := fun i ↦ (hq (y i)).1
      choose Q hyQ hQ hqQ K hK using fun i : R ↦ (hq (y i)).2
      -- For each outer sheet, record where its inverse section lies in the chosen inner base.
      let N (i : R) : Set Z :=
        Subtype.val '' ((fun x : V ↦ (H.symm (x, i) : Y)) ⁻¹' Q i)
      have hNopen (i : R) : IsOpen (N i) := by
        refine hV.isOpenMap_subtype_val _ ((hQ i).preimage ?_)
        fun_prop
      have hzN (i : R) : z ∈ N i := by
        exact ⟨⟨z, hzV⟩, hyQ i, rfl⟩
      let W : Set Z := ⋂ i : R, N i
      have hWopen : IsOpen W := isOpen_iInter_of_finite hNopen
      have hzW : z ∈ W := Set.mem_iInter.mpr hzN
      have hWV : W ⊆ V := by
        intro z' hz'
        obtain ⟨x, _, hx⟩ := Set.mem_iInter.mp hz' (Classical.arbitrary R)
        rw [← hx]
        exact x.property
      -- `O i` is the part of the `i`-th outer sheet lying over the common base `W`.
      let O (i : R) : Set Y :=
        Subtype.val '' (H ⁻¹' ((Subtype.val ⁻¹' W) ×ˢ ({i} : Set R)))
      have hOopen (i : R) : IsOpen (O i) := by
        refine hrV.isOpenMap_subtype_val _ ?_
        exact ((hWopen.preimage continuous_subtype_val).prod
          (isOpen_discrete ({i} : Set R))).preimage H.continuous
      have hO_maps (i : R) : Set.MapsTo r (O i) W := by
        intro y' hy'
        obtain ⟨a, ha, rfl⟩ := hy'
        rw [← hH a]
        exact ha.1
      have hO_coord (i : R) {a : r ⁻¹' V}
          (ha : (a : Y) ∈ O i) : (H a).2 = i := by
        obtain ⟨a', ha', haa'⟩ := ha
        have haa : a = a' := Subtype.ext haa'.symm
        rw [haa]
        exact ha'.2
      have hO_inj (i : R) : Set.InjOn r (O i) := by
        intro a ha b hb hab
        have haV : r a ∈ V := hWV (hO_maps i ha)
        have hbV : r b ∈ V := hWV (hO_maps i hb)
        have hpair : H ⟨a, haV⟩ = H ⟨b, hbV⟩ := by
          apply Prod.ext
          · apply Subtype.ext
            simpa only [hH] using hab
          · rw [hO_coord i ha, hO_coord i hb]
        exact congrArg Subtype.val (H.injective hpair)
      have hO_surj (i : R) : Set.SurjOn r (O i) W := by
        intro z' hz'
        let a : r ⁻¹' V := H.symm (⟨z', hWV hz'⟩, i)
        have happ : H a = (⟨z', hWV hz'⟩, i) := H.apply_symm_apply _
        refine ⟨a, ?_, ?_⟩
        · refine ⟨a, ?_, rfl⟩
          constructor
          · rw [happ]
            exact hz'
          · rw [happ]
            exact rfl
        · exact (hH a).symm.trans (congrArg (fun p ↦ p.1.1) happ)
      have hO_pairwise : Pairwise (fun i j ↦ Disjoint (O i) (O j)) := by
        intro i j hij
        refine Set.disjoint_left.mpr fun a hai haj ↦ hij ?_
        have haV : r a ∈ V := hWV (hO_maps i hai)
        have hi : (H ⟨a, haV⟩).2 = i := hO_coord i hai
        have hj : (H ⟨a, haV⟩).2 = j := hO_coord j haj
        exact hi.symm.trans hj
      have hO_subset (i : R) : O i ⊆ Q i := by
        intro a ha
        have hraW := hO_maps i ha
        obtain ⟨x, hxQ, hxr⟩ := Set.mem_iInter.mp hraW i
        have haV : r a ∈ V := hWV hraW
        have hx : x = ⟨r a, haV⟩ := Subtype.ext hxr
        have hHa : H ⟨a, haV⟩ = (x, i) := by
          apply Prod.ext
          · apply Subtype.ext
            simpa only [hH] using hxr.symm
          · exact hO_coord i ha
        have haeq : a = H.symm (x, i) := by
          exact congrArg Subtype.val (H.injective (hHa.trans (H.apply_symm_apply (x, i)).symm))
        rw [haeq]
        exact hxQ
      -- `S a` refines an outer sheet by fixing one coordinate in the corresponding inner cover.
      let I := Σ i : R, q ⁻¹' {y i}
      let S (a : I) : Set X :=
        Subtype.val '' ((K a.1) ⁻¹'
          ((Subtype.val ⁻¹' O a.1) ×ˢ ({a.2} : Set (q ⁻¹' {y a.1}))))
      have hSopen (a : I) : IsOpen (S a) := by
        refine (hqQ a.1).isOpenMap_subtype_val _ ?_
        exact (((hOopen a.1).preimage continuous_subtype_val).prod
          (isOpen_discrete ({a.2} : Set (q ⁻¹' {y a.1})))).preimage (K a.1).continuous
      have hS_maps (a : I) : Set.MapsTo q (S a) (O a.1) := by
        intro x hx
        obtain ⟨b, hb, rfl⟩ := hx
        rw [← hK a.1 b]
        exact hb.1
      have hS_coord (a : I) {b : q ⁻¹' Q a.1}
          (hb : (b : X) ∈ S a) : (K a.1 b).2 = a.2 := by
        obtain ⟨b', hb', hbb'⟩ := hb
        have hbb : b = b' := Subtype.ext hbb'.symm
        rw [hbb]
        exact hb'.2
      have hS_inj (a : I) : Set.InjOn q (S a) := by
        intro b hb c hc hbc
        have hbQ : q b ∈ Q a.1 := hO_subset a.1 (hS_maps a hb)
        have hcQ : q c ∈ Q a.1 := hO_subset a.1 (hS_maps a hc)
        have hpair : K a.1 ⟨b, hbQ⟩ = K a.1 ⟨c, hcQ⟩ := by
          apply Prod.ext
          · apply Subtype.ext
            simpa only [hK] using hbc
          · rw [hS_coord a hb, hS_coord a hc]
        exact congrArg Subtype.val ((K a.1).injective hpair)
      have hS_surj (a : I) : Set.SurjOn q (S a) (O a.1) := by
        intro y' hy'
        let b : q ⁻¹' Q a.1 := (K a.1).symm (⟨y', hO_subset a.1 hy'⟩, a.2)
        have happ : K a.1 b = (⟨y', hO_subset a.1 hy'⟩, a.2) :=
          (K a.1).apply_symm_apply _
        refine ⟨b, ?_, ?_⟩
        · refine ⟨b, ?_, rfl⟩
          constructor
          · rw [happ]
            exact hy'
          · rw [happ]
            exact rfl
        · exact (hK a.1 b).symm.trans (congrArg (fun p ↦ p.1.1) happ)
      have hS_pairwise : Pairwise (fun a b ↦ Disjoint (S a) (S b)) := by
        intro a b hab
        refine Set.disjoint_left.mpr fun x hxa hxb ↦ hab ?_
        have houter : a.1 = b.1 := by
          by_contra hij
          exact (hO_pairwise hij).le_bot ⟨hS_maps a hxa, hS_maps b hxb⟩
        obtain ⟨i, ai⟩ := a
        obtain ⟨j, bj⟩ := b
        dsimp only at houter
        subst j
        have hxQ : q x ∈ Q i := hO_subset i (hS_maps ⟨i, ai⟩ hxa)
        have hxQ' : x ∈ q ⁻¹' Q i := hxQ
        let xQ : q ⁻¹' Q i := ⟨x, hxQ'⟩
        have hcoord : ai = bj :=
          (hS_coord ⟨i, ai⟩ (b := xQ) hxa).symm.trans
            (hS_coord ⟨i, bj⟩ (b := xQ) hxb)
        rw [hcoord]
      have hp_inj (a : I) : Set.InjOn (r ∘ q) (S a) := by
        intro x hx x' hx' hxx'
        have hqx : q x ∈ O a.1 := hS_maps a hx
        have hqx' : q x' ∈ O a.1 := hS_maps a hx'
        apply hS_inj a hx hx'
        exact hO_inj a.1 hqx hqx' hxx'
      have hp_surj (a : I) : Set.SurjOn (r ∘ q) (S a) W := by
        intro z' hz'
        obtain ⟨y', hy', hry'⟩ := hO_surj a.1 hz'
        obtain ⟨x, hx, hqx⟩ := hS_surj a hy'
        have hpx : (r ∘ q) x = z' := by
          simp only [Function.comp_apply, hqx, hry']
        exact ⟨x, hx, hpx⟩
      have hp_exhaustive : (r ∘ q) ⁻¹' W ⊆ ⋃ a : I, S a := by
        intro x hx
        have hqxV : r (q x) ∈ V := hWV hx
        have hqxV' : q x ∈ r ⁻¹' V := hqxV
        let xR : r ⁻¹' V := ⟨q x, hqxV'⟩
        let i : R := (H xR).2
        have hqxO : q x ∈ O i := by
          refine ⟨xR, ?_, rfl⟩
          have hbaseval : (H xR).1.1 ∈ W := by
            rw [hH xR]
            exact hx
          have hbase : (H xR).1 ∈ Subtype.val ⁻¹' W := hbaseval
          exact ⟨hbase, rfl⟩
        have hqxQ : q x ∈ Q i := hO_subset i hqxO
        have hqxQ' : x ∈ q ⁻¹' Q i := hqxQ
        let xQ : q ⁻¹' Q i := ⟨x, hqxQ'⟩
        let j : q ⁻¹' {y i} := (K i xQ).2
        refine Set.mem_iUnion.mpr ⟨⟨i, j⟩, ?_⟩
        refine ⟨xQ, ?_, rfl⟩
        have hbaseval : (K i xQ).1.1 ∈ O i := by
          rw [hK i xQ]
          exact hqxO
        have hbase : (K i xQ).1 ∈ Subtype.val ⁻¹' O i := hbaseval
        exact ⟨hbase, rfl⟩
      cases isEmpty_or_nonempty I with
      | inl hI =>
          letI : IsEmpty I := hI
          have hpW : (r ∘ q) ⁻¹' W = ∅ := by
            apply Set.eq_empty_of_forall_notMem
            intro x hx
            obtain ⟨a, _⟩ := Set.mem_iUnion.mp (hp_exhaustive hx)
            exact isEmptyElim a
          -- If no composite sheet exists, the common neighborhood has empty preimage.
          exact (IsEvenlyCovered.of_preimage_eq_empty Empty
            (hWopen.mem_nhds hzW) hpW).to_isEvenlyCovered_preimage
      | inr hI =>
          letI : Nonempty I := hI
          letI : Nonempty X := ⟨(Classical.arbitrary I).2⟩
          have hp_continuous : Continuous (r ∘ q) := hr.continuous.comp hq.continuous
          have hp_open : IsOpenMap (r ∘ q) := hr.isOpenMap.comp hq.isOpenMap
          have hp_open_iff (a : I) {A : Set Z} (hAW : A ⊆ W) :
              IsOpen A ↔ IsOpen ((r ∘ q) ⁻¹' A ∩ S a) := by
            constructor
            · intro hA
              exact (hA.preimage hp_continuous).inter (hSopen a)
            · intro hA
              have himage : (r ∘ q) '' ((r ∘ q) ⁻¹' A ∩ S a) = A := by
                apply Set.Subset.antisymm
                · intro z' hz'
                  obtain ⟨x, hx, rfl⟩ := hz'
                  exact hx.1
                · intro z' hz'
                  obtain ⟨x, hxS, hxz⟩ := hp_surj a (hAW hz')
                  have hxA : (r ∘ q) x ∈ A := by
                    rw [hxz]
                    exact hz'
                  exact ⟨x, ⟨hxA, hxS⟩, hxz⟩
              rw [← himage]
              exact hp_open _ hA
          let t := hWopen.trivializationDiscrete S W hp_open_iff hp_inj hp_surj
            hS_pairwise hp_exhaustive
          -- The sheet partition gives a trivialization; its fiber type is then replaced by
          -- the actual fiber of the composite through the standard covering API.
          exact (IsEvenlyCovered.of_trivialization (t := t) hzW).to_isEvenlyCovered_preimage

/-- Exercise 53.4. If `q : X → Y` and `r : Y → Z` are covering maps and every fiber
of `r` is finite, then `r ∘ q` is a covering map. -/
theorem comp_of_finite_fiber {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {q : X → Y} {r : Y → Z} (hq : IsCoveringMap q) (hr : IsCoveringMap r)
    [∀ z : Z, Finite {y : Y // r y = z}] : IsCoveringMap (r ∘ q) := by
  -- Apply the finite-intersection construction independently at every point of the base.
  intro z
  exact evenlyCovered_comp_of_finite_fiber hq hr z

end IsCoveringMap
