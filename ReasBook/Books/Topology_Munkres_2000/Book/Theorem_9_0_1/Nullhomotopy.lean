module

public import Topology_Munkres_2000.Book.Definition_61_1.Separation
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Homotopy.Contractible

public section

open Set

universe u

namespace Theorem901

/-- Helper for Theorem 9.0.1: an unbounded component of the complement of a
compact range contains an endpoint outside the compact radial hull, joined to
the puncture by a path in that component. -/
lemma existsPathInUnboundedComponentAvoidingRadialRange
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

/-- Helper for Theorem 9.0.1: a map into a punctured normed space is
nullhomotopic when the component of the puncture in the complement of its
ambient range is unbounded. -/
lemma nullhomotopicIntoPuncturedNormedSpaceOfUnboundedComponent
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


end Theorem901

end
