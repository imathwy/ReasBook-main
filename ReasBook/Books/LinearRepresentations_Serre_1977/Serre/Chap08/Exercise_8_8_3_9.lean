import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap08.Definition_8_8_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {G : Type u} [Group G]

open QuotientGroup
open Subgroup

/- Source clause (1): every subgroup of a solvable group is solvable. This is the existing
instance `subgroup_solvable_of_solvable`. -/
recall subgroup_solvable_of_solvable

/- Source clause (2): every quotient of a solvable group is solvable. This is the existing
instance `solvable_quotient_of_solvable`. -/
recall solvable_quotient_of_solvable

-- Proof sketch: intersect a finite subnormal series for `G` with the subgroup `H`; the induced
-- series on `H` is still monotone, has endpoints `⊥` and `⊤`, and each successive quotient maps
-- into the corresponding cyclic quotient for `G`, hence is cyclic.
/-- Exercise 8-8.3-9 (1): source clause (3). Every subgroup of a supersolvable group is
supersolvable. -/
instance subgroup_supersolvable_of_supersolvable (H : Subgroup G) [IsSupersolvable G] :
    IsSupersolvable H := by
  refine ⟨?_⟩
  let hsup : IsSupersolvable G := inferInstance
  rcases hsup.supersolvable with ⟨n, f, hmono, hnormal, hcyclic, h0, hn⟩
  refine ⟨n, fun i ↦ (f i).subgroupOf H, ?_⟩
  refine ⟨?_, ⟨?_, ⟨?_, ?_, ?_⟩⟩⟩
  · intro i j hij
    exact subgroupOf_mono H (hmono hij)
  · intro i hi
    simpa using (hnormal i hi).subgroupOf H
  · intro i hi
    let A := f (i + 1)
    let B : Subgroup A := (f i).subgroupOf A
    letI : B.Normal := (hnormal i hi).subgroupOf A
    letI : (((f i).subgroupOf H).subgroupOf (A.subgroupOf H)).Normal :=
      ((hnormal i hi).subgroupOf H).subgroupOf (A.subgroupOf H)
    let eAH : A.subgroupOf H ≃* (A ⊓ H : Subgroup G) :=
      (MulEquiv.subgroupCongr (inf_subgroupOf_right A H)).symm.trans
        (subgroupOfEquivOfLe inf_le_right)
    let eHA : H.subgroupOf A ≃* (A ⊓ H : Subgroup G) :=
      (MulEquiv.subgroupCongr (inf_subgroupOf_left H A)).symm.trans
        (subgroupOfEquivOfLe inf_le_left)
    let e : A.subgroupOf H ≃* H.subgroupOf A := eAH.trans eHA.symm
    let φ : A.subgroupOf H →* A ⧸ B :=
      ((QuotientGroup.mk' B).comp (H.subgroupOf A).subtype).comp e.toMonoidHom
    letI : IsCyclic (A ⧸ B) := hcyclic i hi
    letI : IsCyclic φ.range := inferInstance
    have hker :
        MonoidHom.ker φ = ((f i).subgroupOf H).subgroupOf (A.subgroupOf H) := by
      ext x
      constructor
      · intro hx
        change ((e x : H.subgroupOf A) : A) ∈ B
        exact (eq_one_iff ((e x : H.subgroupOf A) : A)).1 hx
      · intro hx
        change ((e x : H.subgroupOf A) : A) ∈ B at hx
        exact (eq_one_iff ((e x : H.subgroupOf A) : A)).2 hx
    let e' :
        A.subgroupOf H ⧸ ((f i).subgroupOf H).subgroupOf (A.subgroupOf H) ≃* φ.range :=
      (quotientMulEquivOfEq hker.symm).trans (quotientKerEquivRange φ)
    exact (e'.isCyclic).2 inferInstance
  · simp [h0]
  · simp [hn]

-- Proof sketch: push a finite subnormal series for `G` forward along the quotient map
-- `G → G ⧸ H`; the images still form a finite monotone series from `⊥` to `⊤`, and each
-- successive quotient is a quotient of a cyclic group, hence cyclic.
/-- Exercise 8-8.3-9 (2): source clause (4). Every quotient of a supersolvable group is
supersolvable. -/
instance supersolvable_quotient_of_supersolvable (H : Subgroup G) [H.Normal]
    [IsSupersolvable G] : IsSupersolvable (G ⧸ H) := by
  refine ⟨?_⟩
  let hsup : IsSupersolvable G := inferInstance
  rcases hsup.supersolvable with ⟨n, f, hmono, hnormal, hcyclic, h0, hn⟩
  let q : G →* G ⧸ H := QuotientGroup.mk' H
  have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective H
  refine ⟨n, fun i ↦ (f i).map q, ?_⟩
  refine ⟨?_, ⟨?_, ⟨?_, ?_, ?_⟩⟩⟩
  · intro i j hij
    exact map_mono (hmono hij)
  · intro i hi
    exact Normal.map (hnormal i hi) q hq_surj
  · intro i hi
    let A := f (i + 1)
    let B : Subgroup A := (f i).subgroupOf A
    let C := A.map q
    let D := (f i).map q
    letI : B.Normal := (hnormal i hi).subgroupOf A
    letI : D.Normal := Normal.map (hnormal i hi) q hq_surj
    letI : (D.subgroupOf C).Normal := (inferInstance : D.Normal).subgroupOf C
    let φ : A →* C := q.subgroupMap A
    have hφ :
        Function.Surjective (QuotientGroup.mk' (D.subgroupOf C) ∘ φ) :=
      (QuotientGroup.mk'_surjective (D.subgroupOf C)).comp (q.subgroupMap_surjective A)
    have hle : B ≤ Subgroup.comap φ (D.subgroupOf C) := by
      intro x hx
      change ((φ x : C) : G ⧸ H) ∈ D
      exact ⟨x.1, hx, rfl⟩
    have hψ :
        Function.Surjective (QuotientGroup.map B (D.subgroupOf C) φ hle) :=
      QuotientGroup.map_surjective_of_surjective B (D.subgroupOf C) φ hφ hle
    letI : IsCyclic (A ⧸ B) := hcyclic i hi
    exact isCyclic_of_surjective (QuotientGroup.map B (D.subgroupOf C) φ hle) hψ
  · simp [q, h0]
  · simpa [hn, q] using map_top_of_surjective q hq_surj

/- Source clause (5): every subgroup of a nilpotent group is nilpotent. This is the existing
instance `Subgroup.isNilpotent`. -/
recall Subgroup.isNilpotent

/- Source clause (6): every quotient of a nilpotent group is nilpotent. This is the existing
instance `nilpotent_quotient_of_nilpotent`. -/
recall nilpotent_quotient_of_nilpotent

end
