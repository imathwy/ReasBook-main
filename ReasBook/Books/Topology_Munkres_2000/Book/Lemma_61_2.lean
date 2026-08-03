module

public import Topology_Munkres_2000.Book.Lemma_61_1
public import Topology_Munkres_2000.Book.Proposition_61_1.Stereographic
public import Mathlib.Topology.Homotopy.Contractible

public section

open Set

universe u

/-- Helper for Lemma 61.2: an unbounded component of the complement of a
compact range contains an endpoint outside the compact radial hull, joined to
the puncture by a path in that component. -/
private lemma existsPathInUnboundedComponentAvoidingRadialRange
    {A : Type u} {E : Type*} [TopologicalSpace A] [CompactSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (q : E)
    (g : C(A, ({q}ᶜ : Set E)))
    (hunbounded : ¬ Bornology.IsBounded
      (connectedComponentIn (Set.range (fun x : A ↦ (g x : E)))ᶜ q)) :
    ∃ (p : E) (alpha : Path q p),
      p ≠ q ∧ (∀ t, alpha t ∈ connectedComponentIn
        (Set.range (fun x : A ↦ (g x : E)))ᶜ q) ∧
      p ∉ Set.range (fun z : unitInterval × A ↦
        q + (z.1 : ℝ) • ((g z.2 : E) - q)) := by
  classical
  let radial : unitInterval × A → E := fun z ↦
    q + (z.1 : ℝ) • ((g z.2 : E) - q)
  -- Compactness bounds every radial segment from `q` through the image of `g`.
  have hradialContinuous : Continuous radial := by
    fun_prop
  have hradialCompact : IsCompact (Set.range radial) :=
    isCompact_range hradialContinuous
  have hp : ∃ p ∈ connectedComponentIn
      (Set.range (fun x : A ↦ (g x : E)))ᶜ q,
      p ∉ Set.range radial ∪ {q} := by
    by_contra h
    push Not at h
    exact hunbounded
      ((hradialCompact.union isCompact_singleton).isBounded.subset h)
  obtain ⟨p, hpComponent, hpOutside⟩ := hp
  have hpNe : p ≠ q := by
    intro hpq
    have hpSingleton : p ∈ ({q} : Set E) := by
      simpa only [mem_singleton_iff] using hpq
    exact hpOutside (Or.inr hpSingleton)
  have hpRadial : p ∉ Set.range radial := fun hp ↦ hpOutside (Or.inl hp)
  -- The compact range has open complement, whose connected component is path connected.
  have hgContinuous : Continuous (fun x : A ↦ (g x : E)) := by
    fun_prop
  have hrangeCompact : IsCompact (Set.range (fun x : A ↦ (g x : E))) :=
    isCompact_range hgContinuous
  have hqComplement : q ∈ (Set.range (fun x : A ↦ (g x : E)))ᶜ := by
    rintro ⟨x, hx⟩
    have hxSingleton : (g x : E) ∈ ({q} : Set E) := by
      simpa only [mem_singleton_iff] using hx
    exact (g x).property hxSingleton
  have hcomponentPathConnected : IsPathConnected
      (connectedComponentIn (Set.range (fun x : A ↦ (g x : E)))ᶜ q) := by
    have hopen : IsOpen (Set.range (fun x : A ↦ (g x : E)))ᶜ :=
      hrangeCompact.isClosed.isOpen_compl
    apply (hopen.connectedComponentIn.isConnected_iff_isPathConnected).mp
    exact isConnected_connectedComponentIn_iff.mpr hqComplement
  let joined := hcomponentPathConnected.joinedIn q
    (mem_connectedComponentIn hqComplement) p hpComponent
  exact ⟨p, joined.somePath, hpNe, joined.somePath_mem, hpRadial⟩

/-- Helper for Lemma 61.2: a map into a punctured normed space is
nullhomotopic when the component of the puncture in the complement of its
ambient range is unbounded. -/
private lemma nullhomotopicIntoPuncturedNormedSpaceOfUnboundedComponent
    {A : Type u} {E : Type*} [TopologicalSpace A] [CompactSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (q : E)
    (g : C(A, ({q}ᶜ : Set E)))
    (hunbounded : ¬ Bornology.IsBounded
      (connectedComponentIn (Set.range (fun x : A ↦ (g x : E)))ᶜ q)) :
    g.Nullhomotopic := by
  obtain ⟨p, alpha, hpNe, halpha, hpRadial⟩ :=
    existsPathInUnboundedComponentAvoidingRadialRange q g hunbounded
  -- Translating the image opposite the path from `q` to `p` never reaches `q`.
  have hfirstAvoids (z : unitInterval × A) :
      (g z.2 : E) - alpha z.1 + q ∈ ({q}ᶜ : Set E) := by
    intro hz
    simp only [mem_singleton_iff] at hz
    have halphaEq : alpha z.1 = (g z.2 : E) := by
      have hzero : (g z.2 : E) - alpha z.1 = 0 := by
        apply add_right_cancel (b := q)
        simpa only [zero_add] using hz
      exact (sub_eq_zero.mp hzero).symm
    have hnotRange := connectedComponentIn_subset
      (Set.range (fun x : A ↦ (g x : E)))ᶜ q (halpha z.1)
    apply hnotRange
    exact ⟨z.2, halphaEq.symm⟩
  have hfirstContinuous : Continuous (fun z : unitInterval × A ↦
      (⟨(g z.2 : E) - alpha z.1 + q, hfirstAvoids z⟩ : ({q}ᶜ : Set E))) := by
    apply Continuous.subtype_mk
    fun_prop
  let firstMap : C(unitInterval × A, ({q}ᶜ : Set E)) :=
    ⟨fun z ↦ ⟨(g z.2 : E) - alpha z.1 + q, hfirstAvoids z⟩,
      hfirstContinuous⟩
  have hkAvoids (x : A) : (g x : E) - p + q ∈ ({q}ᶜ : Set E) := by
    simpa only [Path.target] using hfirstAvoids (1, x)
  have hkContinuous : Continuous (fun x : A ↦
      (⟨(g x : E) - p + q, hkAvoids x⟩ : ({q}ᶜ : Set E))) := by
    apply Continuous.subtype_mk
    fun_prop
  let k : C(A, ({q}ᶜ : Set E)) :=
    ⟨fun x ↦ ⟨(g x : E) - p + q, hkAvoids x⟩, hkContinuous⟩
  have hfirstZero (x : A) : firstMap (0, x) = g x := by
    apply Subtype.ext
    change (g x : E) - alpha 0 + q = (g x : E)
    rw [alpha.source]
    abel
  have hfirstOne (x : A) : firstMap (1, x) = k x := by
    apply Subtype.ext
    change (g x : E) - alpha 1 + q = (g x : E) - p + q
    rw [alpha.target]
  let firstHomotopy : ContinuousMap.Homotopy g k :=
    ⟨firstMap, hfirstZero, hfirstOne⟩
  -- Radially contracting the translated map would hit `q` only if `p` lay in
  -- the compact radial hull excluded by its choice.
  have hsecondAvoids (z : unitInterval × A) :
      q + (unitInterval.symm z.1 : ℝ) • ((g z.2 : E) - q) - (p - q) ∈
        ({q}ᶜ : Set E) := by
    intro hz
    simp only [mem_singleton_iff] at hz
    apply hpRadial
    refine ⟨(unitInterval.symm z.1, z.2), ?_⟩
    have hqp : q + (p - q) = p := by
      abel
    calc
      q + (unitInterval.symm z.1 : ℝ) • ((g z.2 : E) - q) =
          q + (p - q) := (sub_eq_iff_eq_add.mp hz)
      _ = p := hqp
  have hsecondContinuous : Continuous (fun z : unitInterval × A ↦
      (⟨q + (unitInterval.symm z.1 : ℝ) • ((g z.2 : E) - q) - (p - q),
        hsecondAvoids z⟩ : ({q}ᶜ : Set E))) := by
    apply Continuous.subtype_mk
    fun_prop
  let secondMap : C(unitInterval × A, ({q}ᶜ : Set E)) :=
    ⟨fun z ↦ ⟨q + (unitInterval.symm z.1 : ℝ) • ((g z.2 : E) - q) - (p - q),
        hsecondAvoids z⟩,
      hsecondContinuous⟩
  have hcAvoids : q - (p - q) ∈ ({q}ᶜ : Set E) := by
    intro hc
    apply hpNe
    simp only [mem_singleton_iff] at hc
    have hsum : q = q + (p - q) := sub_eq_iff_eq_add.mp hc
    apply sub_eq_zero.mp
    apply add_left_cancel (a := q)
    simpa only [add_zero] using hsum.symm
  let c : ({q}ᶜ : Set E) := ⟨q - (p - q), hcAvoids⟩
  have hsecondZero (x : A) : secondMap (0, x) = k x := by
    apply Subtype.ext
    change q + (unitInterval.symm 0 : ℝ) • ((g x : E) - q) - (p - q) =
      (g x : E) - p + q
    rw [unitInterval.symm_zero]
    norm_num
    abel
  have hsecondOne (x : A) : secondMap (1, x) = ContinuousMap.const A c x := by
    apply Subtype.ext
    change q + (unitInterval.symm 1 : ℝ) • ((g x : E) - q) - (p - q) =
      q - (p - q)
    rw [unitInterval.symm_one]
    norm_num
  let secondHomotopy : ContinuousMap.Homotopy k (ContinuousMap.const A c) :=
    ⟨secondMap, hsecondZero, hsecondOne⟩
  -- Concatenating the translation and radial contraction gives the nullhomotopy.
  exact ⟨c, ⟨firstHomotopy.trans secondHomotopy⟩⟩

/-- Helper for Lemma 61.2: deleting the same point twice from the standard
two-sphere gives a contractible punctured sphere, so every map into it is
nullhomotopic. -/
private lemma nullhomotopicIntoRepeatedPuncture
    {A : Type u} [TopologicalSpace A] (a : StandardSphere 2)
    (f : C(A, ({a, a}ᶜ : Set (StandardSphere 2)))) : f.Nullhomotopic := by
  -- Collapse the repeated deletion and use stereographic projection to the plane.
  have hsets : ({a, a}ᶜ : Set (StandardSphere 2)) = ({a}ᶜ : Set (StandardSphere 2)) := by
    ext x
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, or_self]
  let e : ({a, a}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    (Homeomorph.setCongr hsets).trans (StandardSphere.puncturedHomeomorphPlane a)
  letI : ContractibleSpace ({a, a}ᶜ : Set (StandardSphere 2)) :=
    e.contractibleSpace
  -- Precomposing the nullhomotopic identity with `f` proves the claim.
  simpa only [ContinuousMap.id_comp] using
    (id_nullhomotopic ({a, a}ᶜ : Set (StandardSphere 2))).comp_left f

/-- Helper for Lemma 61.2: stereographic projection identifies every point
of the spherical component containing the puncture with a point of the
canonical unbounded planar component. -/
private lemma puncturedSphereComponentAtUnbounded
    (C U : Set (StandardSphere 2)) (b : StandardSphere 2)
    (h : ({b}ᶜ : Set (StandardSphere 2)) ≃ₜ EuclideanSpace ℝ (Fin 2))
    (hC : IsCompact C) (hU : IsConnectedComponentIn Cᶜ U) (hbU : b ∈ U)
    (x : ({b}ᶜ : Set (StandardSphere 2))) (hxU : x.1 ∈ U) :
    ¬ Bornology.IsBounded
      (connectedComponentIn (h '' (Subtype.val ⁻¹' C))ᶜ (h x)) := by
  obtain ⟨hcomponent, hunbounded⟩ :=
    puncturedSphere_componentImage_unbounded C U b h hC hU hbU
  -- Component uniqueness normalizes Lemma 61.1's set-valued conclusion at `h x`.
  have hxImage : h x ∈ h '' (Subtype.val ⁻¹' U) := ⟨x, hxU, rfl⟩
  rw [← hcomponent.eq_connectedComponentIn hxImage]
  exact hunbounded

/-- Lemma 61.2 (Nulhomotopy lemma). Let `a` and `b` be points of the standard
2-sphere. If a continuous map from a compact space into the sphere with `a`
and `b` removed has `a` and `b` in the same connected component of the
complement of its image, then the map is nullhomotopic. -/
theorem nulhomotopyLemma {A : Type u} [TopologicalSpace A] [CompactSpace A]
    (a b : StandardSphere 2) (f : C(A, ({a, b}ᶜ : Set (StandardSphere 2))))
    (hab : b ∈ connectedComponentIn
      (Set.range (fun x : A ↦ (f x : StandardSphere 2)))ᶜ a) :
    f.Nullhomotopic := by
  by_cases habEq : a = b
  · -- Repeated deletion is a punctured sphere and hence contractible.
    subst b
    exact nullhomotopicIntoRepeatedPuncture a f
  · -- In the distinct-point case, use the stereographic chart punctured at `b`.
    have hfAvoidsPair (x : A) :
        (f x : StandardSphere 2) ≠ a ∧ (f x : StandardSphere 2) ≠ b := by
      simpa only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] using
        (f x).property
    let C : Set (StandardSphere 2) :=
      Set.range (fun x : A ↦ (f x : StandardSphere 2))
    have hC : IsCompact C := by
      apply isCompact_range
      fun_prop
    have haC : a ∈ Cᶜ := by
      rintro ⟨x, hx⟩
      exact (hfAvoidsPair x).1 hx
    let U : Set (StandardSphere 2) := connectedComponentIn Cᶜ a
    have hU : IsConnectedComponentIn Cᶜ U :=
      IsConnectedComponentIn.of_mem haC
    have haU : a ∈ U := mem_connectedComponentIn haC
    have hbU : b ∈ U := hab
    let h := StandardSphere.puncturedHomeomorphPlane b
    have haPuncture : a ∈ ({b}ᶜ : Set (StandardSphere 2)) := by
      simpa only [mem_compl_iff, mem_singleton_iff] using habEq
    let ap : ({b}ᶜ : Set (StandardSphere 2)) := ⟨a, haPuncture⟩
    let q : EuclideanSpace ℝ (Fin 2) := h ap
    -- Regard `f` first as a map into the sphere punctured at `b`.
    have hfAvoidsB (x : A) : (f x : StandardSphere 2) ∈
        ({b}ᶜ : Set (StandardSphere 2)) := by
      simpa only [mem_compl_iff, mem_singleton_iff] using (hfAvoidsPair x).2
    have hfbContinuous : Continuous (fun x : A ↦
        (⟨(f x : StandardSphere 2), hfAvoidsB x⟩ :
          ({b}ᶜ : Set (StandardSphere 2)))) := by
      apply Continuous.subtype_mk
      fun_prop
    let fb : C(A, ({b}ᶜ : Set (StandardSphere 2))) :=
      ⟨fun x ↦ ⟨(f x : StandardSphere 2), hfAvoidsB x⟩, hfbContinuous⟩
    -- Injectivity of the chart shows that the charted map avoids `q`.
    have hgAvoids (x : A) : h (fb x) ∈ ({q}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
      intro hx
      simp only [mem_singleton_iff] at hx
      have hfbEq : fb x = ap := h.injective hx
      have hvalEq : (f x : StandardSphere 2) = a := congrArg Subtype.val hfbEq
      exact (hfAvoidsPair x).1 hvalEq
    have hgContinuous : Continuous (fun x : A ↦
        (⟨h (fb x), hgAvoids x⟩ : ({q}ᶜ : Set (EuclideanSpace ℝ (Fin 2))))) := by
      apply Continuous.subtype_mk
      fun_prop
    let g : C(A, ({q}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :=
      ⟨fun x ↦ ⟨h (fb x), hgAvoids x⟩, hgContinuous⟩
    -- Normalize the ambient range of `g` to the chart image used by Lemma 61.1.
    have hgRange : Set.range (fun x : A ↦ (g x : EuclideanSpace ℝ (Fin 2))) =
        h '' (Subtype.val ⁻¹' C) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨fb x, ?_, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        change z.1 ∈ Set.range (fun x : A ↦ (f x : StandardSphere 2)) at hz
        obtain ⟨x, hx⟩ := hz
        refine ⟨x, ?_⟩
        change h (fb x) = h z
        apply congrArg h
        apply Subtype.ext
        exact hx
    have hplanarUnbounded : ¬ Bornology.IsBounded
        (connectedComponentIn
          (Set.range (fun x : A ↦ (g x : EuclideanSpace ℝ (Fin 2))))ᶜ q) := by
      rw [hgRange]
      exact puncturedSphereComponentAtUnbounded C U b h hC hU hbU ap haU
    have hgNull : g.Nullhomotopic :=
      nullhomotopicIntoPuncturedNormedSpaceOfUnboundedComponent q g hplanarUnbounded
    -- Map the planar puncture complement back through the chart and flatten the
    -- two avoidance conditions into the original pair complement.
    have htransportAvoids
        (y : ({q}ᶜ : Set (EuclideanSpace ℝ (Fin 2)))) :
        (h.symm y.1).1 ∈ ({a, b}ᶜ : Set (StandardSphere 2)) := by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro hay
        have hpreimageEq : h.symm y.1 = ap := by
          apply Subtype.ext
          exact hay
        have hyq : y.1 = q := by
          calc
            y.1 = h (h.symm y.1) := (h.apply_symm_apply y.1).symm
            _ = h ap := congrArg h hpreimageEq
            _ = q := rfl
        have hySingleton : y.1 ∈ ({q} : Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa only [mem_singleton_iff] using hyq
        exact y.property hySingleton
      · simpa only [mem_compl_iff, mem_singleton_iff] using (h.symm y.1).property
    have htransportContinuous : Continuous (fun y :
        ({q}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) ↦
        (⟨(h.symm y.1).1, htransportAvoids y⟩ :
          ({a, b}ᶜ : Set (StandardSphere 2)))) := by
      apply Continuous.subtype_mk
      fun_prop
    let transport : C(({q}ᶜ : Set (EuclideanSpace ℝ (Fin 2))),
        ({a, b}ᶜ : Set (StandardSphere 2))) :=
      ⟨fun y ↦ ⟨(h.symm y.1).1, htransportAvoids y⟩, htransportContinuous⟩
    have htransportComp : transport.comp g = f := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      change (h.symm (h (fb x))).1 = (f x : StandardSphere 2)
      rw [h.symm_apply_apply]
      rfl
    have htransportedNull : (transport.comp g).Nullhomotopic :=
      hgNull.comp_right transport
    rwa [htransportComp] at htransportedNull
