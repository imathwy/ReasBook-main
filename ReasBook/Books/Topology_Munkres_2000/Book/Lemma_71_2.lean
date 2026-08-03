module

public import Topology_Munkres_2000.Book.Definition_71_4.WedgeOfCircles
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.DiscreteSubset

public section

universe u v

namespace Topology.IsWedgeOfCircles

/-- Helper for Lemma 71.2: a coherent wedge of circles is a T₁ space. -/
lemma t1Space {J : Type v} {X : Type u} [TopologicalSpace X]
    {S : J → Set X} {p : X} (h : Topology.IsWedgeOfCircles S p) : T1Space X := by
  -- Coherence reduces closedness of an ambient singleton to each component circle.
  refine ⟨fun x ↦ h.isCoherentWith.isClosed_iff.mpr ?_⟩
  rintro _ ⟨α, rfl⟩
  obtain ⟨e⟩ := h.homeomorphic_circle α
  letI : T1Space (S α) := e.symm.t1Space
  -- The pullback of a singleton along the subtype inclusion is a subsingleton.
  apply Set.Subsingleton.isClosed
  intro y hy z hz
  apply Subtype.ext
  exact (hy : (y : X) = x).trans (hz : (z : X) = x).symm

/-- Helper for Lemma 71.2: componentwise separated neighborhoods that consistently
contain the wedge point on the left glue to ambient separated neighborhoods. -/
private lemma gluedSeparatedNhds {J : Type v} {X : Type u} [TopologicalSpace X]
    {S : J → Set X} {p : X} (h : Topology.IsWedgeOfCircles S p)
    {A B : Set X} (U V : ∀ α, Set (S α))
    (hUopen : ∀ α, IsOpen (U α)) (hVopen : ∀ α, IsOpen (V α))
    (hAU : ∀ α, Subtype.val ⁻¹' A ⊆ U α) (hBV : ∀ α, Subtype.val ⁻¹' B ⊆ V α)
    (hpU : ∀ α, p ∈ Subtype.val '' U α) (hUV : ∀ α, Disjoint (U α) (V α)) :
    SeparatedNhds A B := by
  let U' : Set X := ⋃ α, Subtype.val '' U α
  let V' : Set X := ⋃ α, Subtype.val '' V α
  -- On each circle, the glued left neighborhood restricts to the chosen neighborhood.
  have hUrestrict (α : J) : Subtype.val ⁻¹' U' = U α := by
    ext y
    constructor
    · intro hy
      obtain ⟨β, z, hzU, hzy⟩ := Set.mem_iUnion.mp hy
      rcases eq_or_ne β α with rfl | hβα
      · have hzy' : z = y := Subtype.ext hzy
        exact hzy' ▸ hzU
      · have hyp : (y : X) = p := by
          have hyinter : (y : X) ∈ S β ∩ S α := ⟨hzy ▸ z.property, y.property⟩
          rw [h.inter_eq hβα] at hyinter
          exact Set.mem_singleton_iff.mp hyinter
        obtain ⟨q, hqU, hqp⟩ := hpU α
        rwa [Subtype.ext (hqp.trans hyp.symm)] at hqU
    · intro hy
      exact Set.mem_iUnion.mpr ⟨α, y, hy, rfl⟩
  -- The right neighborhoods avoid the wedge point, so their restrictions also glue exactly.
  have hVrestrict (α : J) : Subtype.val ⁻¹' V' = V α := by
    ext y
    constructor
    · intro hy
      obtain ⟨β, z, hzV, hzy⟩ := Set.mem_iUnion.mp hy
      rcases eq_or_ne β α with rfl | hβα
      · have hzy' : z = y := Subtype.ext hzy
        exact hzy' ▸ hzV
      · have hyp : (y : X) = p := by
          have hyinter : (y : X) ∈ S β ∩ S α := ⟨hzy ▸ z.property, y.property⟩
          rw [h.inter_eq hβα] at hyinter
          exact Set.mem_singleton_iff.mp hyinter
        obtain ⟨q, hqU, hqp⟩ := hpU β
        have hqz : q = z := Subtype.ext (hqp.trans (hzy.trans hyp).symm)
        exact (Set.disjoint_left.mp (hUV β) hqU (hqz ▸ hzV)).elim
    · intro hy
      exact Set.mem_iUnion.mpr ⟨α, y, hy, rfl⟩
  have hU'open : IsOpen U' := by
    rw [h.isCoherentWith.isOpen_iff]
    rintro _ ⟨α, rfl⟩
    rw [hUrestrict α]
    exact hUopen α
  have hV'open : IsOpen V' := by
    rw [h.isCoherentWith.isOpen_iff]
    rintro _ ⟨α, rfl⟩
    rw [hVrestrict α]
    exact hVopen α
  have hAU' : A ⊆ U' := by
    intro x hxA
    have hxUnion : x ∈ ⋃ α, S α := by
      rw [h.covers]
      exact Set.mem_univ x
    obtain ⟨α, hxS⟩ := Set.mem_iUnion.mp hxUnion
    exact Set.mem_iUnion.mpr ⟨α, ⟨x, hxS⟩, hAU α hxA, rfl⟩
  have hBV' : B ⊆ V' := by
    intro x hxB
    have hxUnion : x ∈ ⋃ α, S α := by
      rw [h.covers]
      exact Set.mem_univ x
    obtain ⟨α, hxS⟩ := Set.mem_iUnion.mp hxUnion
    exact Set.mem_iUnion.mpr ⟨α, ⟨x, hxS⟩, hBV α hxB, rfl⟩
  have hU'V' : Disjoint U' V' := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    obtain ⟨α, y, hyU, hyx⟩ := Set.mem_iUnion.mp hxU
    obtain ⟨β, z, hzV, hzx⟩ := Set.mem_iUnion.mp hxV
    rcases eq_or_ne α β with hαβ | hαβ
    · subst β
      exact Set.disjoint_left.mp (hUV α) hyU (Subtype.ext (hyx.trans hzx.symm) ▸ hzV)
    · have hxp : x = p := by
        have hxinter : x ∈ S α ∩ S β := ⟨hyx ▸ y.property, hzx ▸ z.property⟩
        rw [h.inter_eq hαβ] at hxinter
        exact Set.mem_singleton_iff.mp hxinter
      obtain ⟨q, hqU, hqp⟩ := hpU β
      have hqz : q = z := Subtype.ext (hqp.trans (hzx.trans hxp).symm)
      exact Set.disjoint_left.mp (hUV β) hqU (hqz ▸ hzV)
  -- The exact restriction lemmas make the final ambient assembly immediate.
  exact ⟨U', V', hU'open, hV'open, hAU', hBV', hU'V'⟩

/-- Helper for Lemma 71.2: disjoint closed sets in a wedge have separated
neighborhoods when the right-hand set omits the wedge point. -/
private lemma separatedNhds_of_not_mem_right {J : Type v} {X : Type u}
    [TopologicalSpace X] {S : J → Set X} {p : X}
    (h : Topology.IsWedgeOfCircles S p) {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) (hpB : p ∉ B) :
    SeparatedNhds A B := by
  classical
  letI : Topology.IsWedgeOfCircles S p := h
  letI : T1Space X := t1Space h
  have hseparated (α : J) :
      SeparatedNhds (Subtype.val ⁻¹' insert p A : Set (S α))
        (Subtype.val ⁻¹' B : Set (S α)) := by
    obtain ⟨e⟩ := h.homeomorphic_circle α
    letI : T4Space (S α) := e.symm.t4Space
    have hinsert : IsClosed (insert p A) := by
      rw [Set.insert_eq]
      exact isClosed_singleton.union hA
    have hleft : IsClosed (Subtype.val ⁻¹' insert p A : Set (S α)) :=
      hinsert.preimage continuous_subtype_val
    have hright : IsClosed (Subtype.val ⁻¹' B : Set (S α)) :=
      hB.preimage continuous_subtype_val
    have hdisjoint : Disjoint (Subtype.val ⁻¹' insert p A : Set (S α))
        (Subtype.val ⁻¹' B : Set (S α)) := by
      rw [Set.disjoint_left]
      intro y hyA hyB
      rcases hyA with hyP | hyA
      · exact hpB (hyP.symm ▸ hyB)
      · exact Set.disjoint_left.mp hAB hyA hyB
    -- Normality of the component circle supplies the local neighborhoods.
    exact normal_separation hleft hright hdisjoint
  choose U V hUopen hVopen hleft hright hdisjoint using hseparated
  -- The left local neighborhoods all contain the common point, so the gluing
  -- interface applies to the chosen componentwise separations.
  refine gluedSeparatedNhds h U V hUopen hVopen ?_ hright ?_ hdisjoint
  · intro α y hyA
    exact hleft α (Set.mem_insert_iff.mpr (Or.inr hyA))
  · intro α
    have hpS : p ∈ S α := mem_basepoint α
    let q : S α := ⟨p, hpS⟩
    exact ⟨q, hleft α (Set.mem_insert p A), rfl⟩

/-- Helper for Lemma 71.2: a coherent wedge of circles is normal. -/
private lemma normalSpace {J : Type v} {X : Type u} [TopologicalSpace X]
    {S : J → Set X} {p : X} (h : Topology.IsWedgeOfCircles S p) : NormalSpace X := by
  refine ⟨?_⟩
  intro A B hA hB hAB
  -- Whichever closed set omits the wedge point is placed on the right.
  by_cases hpB : p ∈ B
  · have hpA : p ∉ A := fun hpA ↦ Set.disjoint_left.mp hAB hpA hpB
    exact (separatedNhds_of_not_mem_right h hB hA hAB.symm hpA).symm
  · exact separatedNhds_of_not_mem_right h hA hB hAB hpB

/-- Lemma 71.2 (1): A wedge of an arbitrary indexed family of circles is normal,
using the book's `T4Space` convention. -/
theorem t4Space {J : Type v} {X : Type u} [TopologicalSpace X]
    {S : J → Set X} {p : X} (h : Topology.IsWedgeOfCircles S p) : T4Space X := by
  -- The two separation fields were isolated above, so the T₄ structure is direct.
  exact { toT1Space := t1Space h, toNormalSpace := normalSpace h }

/-- Helper for Lemma 71.2: a chosen non-basepoint from one component belongs to
another component exactly when the two component indices agree. -/
private lemma componentRepresentative_mem_iff {J : Type v} {X : Type u}
    [TopologicalSpace X] {S : J → Set X} {p : X}
    (h : Topology.IsWedgeOfCircles S p) (I : Set J) (x : I → X)
    (hxS : ∀ i, x i ∈ S i.1) (hxp : ∀ i, x i ≠ p) (i : I) (α : J) :
    x i ∈ S α ↔ i.1 = α := by
  constructor
  · intro hxiα
    by_contra hiα
    have hxinter : x i ∈ S i.1 ∩ S α := ⟨hxS i, hxiα⟩
    rw [h.inter_eq hiα] at hxinter
    exact hxp i (Set.mem_singleton_iff.mp hxinter)
  · intro hiα
    rw [← hiα]
    exact hxS i

/-- Helper for Lemma 71.2: every subset of a transversal consisting of one
non-basepoint from each selected component is closed in the wedge. -/
private lemma isClosed_of_subset_range_componentRepresentatives
    {J : Type v} {X : Type u} [TopologicalSpace X] {S : J → Set X} {p : X}
    (h : Topology.IsWedgeOfCircles S p) (I : Set J) (x : I → X)
    (hxS : ∀ i, x i ∈ S i.1) (hxp : ∀ i, x i ≠ p)
    {E : Set X} (hE : E ⊆ Set.range x) : IsClosed E := by
  -- Coherence reduces closedness to a subsingleton calculation on each circle.
  rw [h.isCoherentWith.isClosed_iff]
  rintro _ ⟨α, rfl⟩
  obtain ⟨e⟩ := h.homeomorphic_circle α
  letI : T1Space (S α) := e.symm.t1Space
  apply Set.Subsingleton.isClosed
  intro y hy z hz
  apply Subtype.ext
  obtain ⟨i, hiy⟩ := hE hy
  obtain ⟨j, hjz⟩ := hE hz
  have hiα : i.1 = α := (componentRepresentative_mem_iff h I x hxS hxp i α).mp
    (hiy.symm ▸ y.property)
  have hjα : j.1 = α := (componentRepresentative_mem_iff h I x hxS hxp j α).mp
    (hjz.symm ▸ z.property)
  have hij : i = j := Subtype.ext (hiα.trans hjα.symm)
  exact hiy.symm.trans (congrArg x hij) |>.trans hjz

/-- Companion for Lemma 71.2: Every compact subset of a wedge of circles is
contained in the union of finitely many component circles. -/
theorem isCompact_subset_iUnion_finset {J : Type v} {X : Type u} [TopologicalSpace X]
    {S : J → Set X} {p : X} (h : Topology.IsWedgeOfCircles S p)
    {K : Set X} (hK : IsCompact K) : ∃ F : Finset J, K ⊆ ⋃ α ∈ F, S α := by
  classical
  let I : Set J := { α | (K ∩ (S α \ {p})).Nonempty }
  have hchoice : ∀ i : I, ∃ y, y ∈ K ∩ (S i.1 \ {p}) := fun i ↦ i.property
  choose x hx using hchoice
  have hxK : ∀ i, x i ∈ K := fun i ↦ (hx i).1
  have hxS : ∀ i, x i ∈ S i.1 := fun i ↦ (hx i).2.1
  have hxp : ∀ i, x i ≠ p := by
    intro i hip
    exact (hx i).2.2 (Set.mem_singleton_iff.mpr hip)
  -- The source's transversal is closed, and in fact all of its subsets are closed.
  have hrangeClosed : IsClosed (Set.range x) :=
    isClosed_of_subset_range_componentRepresentatives h I x hxS hxp (fun _ hx ↦ hx)
  have hrangeDiscrete : IsDiscrete (Set.range x) := by
    rw [isDiscrete_iff_forall_mem_exists_isClosed]
    intro E hE
    refine ⟨E, isClosed_of_subset_range_componentRepresentatives h I x hxS hxp hE, ?_⟩
    exact Set.inter_eq_left.mpr hE
  have hrangeSubset : Set.range x ⊆ K := by
    rintro _ ⟨i, rfl⟩
    exact hxK i
  have hrangeFinite : (Set.range x).Finite :=
    (hK.of_isClosed_subset hrangeClosed hrangeSubset).finite hrangeDiscrete
  have hxinjective : Function.Injective x := by
    intro i j hij
    apply Subtype.ext
    exact (componentRepresentative_mem_iff h I x hxS hxp i j.1).mp (hij ▸ hxS j)
  letI : Finite (Set.range x) := hrangeFinite.to_subtype
  letI : Finite I := Finite.of_injective_finite_range hxinjective
  have hIfinite : I.Finite := Set.finite_coe_iff.mp inferInstance
  -- Add one component containing the wedge point, then convert the finite index set to a finset.
  have hpUnion : p ∈ ⋃ α, S α := by
    rw [h.covers]
    exact Set.mem_univ p
  obtain ⟨α0, hpS⟩ := Set.mem_iUnion.mp hpUnion
  have hFfinite : (insert α0 I).Finite := hIfinite.insert α0
  refine ⟨hFfinite.toFinset, ?_⟩
  intro y hyK
  by_cases hyp : y = p
  · have hα0F : α0 ∈ hFfinite.toFinset :=
      hFfinite.mem_toFinset.mpr (Set.mem_insert α0 I)
    exact Set.mem_iUnion.mpr ⟨α0, Set.mem_iUnion.mpr ⟨hα0F, hyp.symm ▸ hpS⟩⟩
  · have hyUnion : y ∈ ⋃ α, S α := by
      rw [h.covers]
      exact Set.mem_univ y
    obtain ⟨α, hyS⟩ := Set.mem_iUnion.mp hyUnion
    have hαI : α ∈ I := ⟨y, hyK, hyS, fun hyp' ↦ hyp (Set.mem_singleton_iff.mp hyp')⟩
    have hαF : α ∈ hFfinite.toFinset :=
      hFfinite.mem_toFinset.mpr (Set.mem_insert_of_mem α0 hαI)
    exact Set.mem_iUnion.mpr ⟨α, Set.mem_iUnion.mpr ⟨hαF, hyS⟩⟩

end Topology.IsWedgeOfCircles
