module

public import Topology_Munkres_2000.Book.Definition_71_4.WedgeOfCircles

public section

universe u v

namespace Topology.IsWedgeOfCircles

/-- Helper for Proposition 71.1: componentwise separated neighborhoods whose left sides
contain the wedge point glue to ambient separated neighborhoods. -/
private lemma gluedSeparatedNhds {J : Type v} {X : Type u} [TopologicalSpace X]
    {S : J → Set X} {p : X} (h : IsWedgeOfCircles S p)
    {A B : Set X} (U V : ∀ α, Set (S α))
    (hUopen : ∀ α, IsOpen (U α)) (hVopen : ∀ α, IsOpen (V α))
    (hAU : ∀ α, Subtype.val ⁻¹' A ⊆ U α) (hBV : ∀ α, Subtype.val ⁻¹' B ⊆ V α)
    (hpU : ∀ α, p ∈ Subtype.val '' U α) (hUV : ∀ α, Disjoint (U α) (V α)) :
    SeparatedNhds A B := by
  let U' : Set X := ⋃ α, Subtype.val '' U α
  let V' : Set X := ⋃ α, Subtype.val '' V α
  -- The common point in every left neighborhood makes its restriction to each circle exact.
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
        have hqy : q = y := Subtype.ext (hqp.trans hyp.symm)
        exact hqy ▸ hqU
    · intro hy
      exact Set.mem_iUnion.mpr ⟨α, y, hy, rfl⟩
  -- Disjointness from the left side forces the right neighborhoods to omit the wedge point.
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
  -- Coherence now promotes the exact component restrictions to ambient openness.
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
  -- Any overlap either occurs in one circle or is the wedge point,
  -- contradicting local disjointness.
  have hU'V' : Disjoint U' V' := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    obtain ⟨α, y, hyU, hyx⟩ := Set.mem_iUnion.mp hxU
    obtain ⟨β, z, hzV, hzx⟩ := Set.mem_iUnion.mp hxV
    rcases eq_or_ne α β with hαβ | hαβ
    · subst β
      have hyz : y = z := Subtype.ext (hyx.trans hzx.symm)
      exact Set.disjoint_left.mp (hUV α) hyU (hyz ▸ hzV)
    · have hxp : x = p := by
        have hxinter : x ∈ S α ∩ S β := ⟨hyx ▸ y.property, hzx ▸ z.property⟩
        rw [h.inter_eq hαβ] at hxinter
        exact Set.mem_singleton_iff.mp hxinter
      obtain ⟨q, hqU, hqp⟩ := hpU β
      have hqz : q = z := Subtype.ext (hqp.trans (hzx.trans hxp).symm)
      exact Set.disjoint_left.mp (hUV β) hqU (hqz ▸ hzV)
  exact ⟨U', V', hU'open, hV'open, hAU', hBV', hU'V'⟩

/-- Helper for Proposition 71.1: two distinct points have separated neighborhoods when
the point on the right is not the wedge point. -/
private lemma separatedSingletonsOfRightNeBasepoint {J : Type v} {X : Type u}
    [TopologicalSpace X] {S : J → Set X} {p x y : X} (h : IsWedgeOfCircles S p)
    (hxy : x ≠ y) (hyp : y ≠ p) : SeparatedNhds {x} {y} := by
  letI : IsWedgeOfCircles S p := h
  -- In every circle, separate the finite preimages of `{p, x}` and `{y}`.
  have hseparated (α : J) :
      SeparatedNhds (Subtype.val ⁻¹' {p, x} : Set (S α))
        (Subtype.val ⁻¹' {y} : Set (S α)) := by
    obtain ⟨e⟩ := h.homeomorphic_circle α
    letI : T2Space (S α) := e.symm.t2Space
    have hleftFinite : (Subtype.val ⁻¹' {p, x} : Set (S α)).Finite :=
      (Set.finite_singleton x).insert p |>.preimage Subtype.val_injective.injOn
    have hrightFinite : (Subtype.val ⁻¹' {y} : Set (S α)).Finite :=
      (Set.finite_singleton y).preimage Subtype.val_injective.injOn
    have hdisjoint : Disjoint (Subtype.val ⁻¹' {p, x} : Set (S α))
        (Subtype.val ⁻¹' {y} : Set (S α)) := by
      rw [Set.disjoint_left]
      intro z hzleft hzright
      have hzy : (z : X) = y := Set.mem_singleton_iff.mp hzright
      rcases Set.mem_insert_iff.mp hzleft with hzp | hzx
      · exact hyp (hzp.symm.trans hzy).symm
      · exact hxy ((Set.mem_singleton_iff.mp hzx).symm.trans hzy)
    exact SeparatedNhds.of_finite hleftFinite hrightFinite hdisjoint
  choose U V hUopen hVopen hleft hright hdisjoint using hseparated
  -- The componentwise left neighborhoods contain `p`, so the gluing interface applies.
  refine gluedSeparatedNhds h U V hUopen hVopen ?_ hright ?_ hdisjoint
  · intro α z hzx
    exact hleft α (Set.mem_insert_iff.mpr (Or.inr hzx))
  · intro α
    have hpS : p ∈ S α := mem_basepoint α
    let q : S α := ⟨p, hpS⟩
    exact ⟨q, hleft α (Set.mem_insert p {x}), rfl⟩

/-- Proposition 71.1: A wedge of an arbitrary indexed family of circles is Hausdorff. -/
theorem t2Space {J : Type v} {X : Type u} [TopologicalSpace X]
    {S : J → Set X} {p : X} (h : IsWedgeOfCircles S p) : T2Space X := by
  refine ⟨?_⟩
  intro x y hxy
  by_cases hyp : y = p
  · -- If the right point is the basepoint, reverse the oriented separation and swap its witnesses.
    have hxp : x ≠ p := fun hxp ↦ hxy (hxp.trans hyp.symm)
    obtain ⟨V, U, hVopen, hUopen, hyV, hxU, hVU⟩ :=
      separatedSingletonsOfRightNeBasepoint h hxy.symm hxp
    exact ⟨U, V, hUopen, hVopen, hxU (Set.mem_singleton x),
      hyV (Set.mem_singleton y), hVU.symm⟩
  · -- Otherwise the componentwise construction already has the required orientation.
    obtain ⟨U, V, hUopen, hVopen, hxU, hyV, hUV⟩ :=
      separatedSingletonsOfRightNeBasepoint h hxy hyp
    exact ⟨U, V, hUopen, hVopen, hxU (Set.mem_singleton x),
      hyV (Set.mem_singleton y), hUV⟩

end Topology.IsWedgeOfCircles
