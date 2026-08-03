module

public import Topology_Munkres_2000.Book.Definition_73_1.DunceCap

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import all Topology_Munkres_2000.Book.Definition_73_1.DunceCap

public section

namespace DunceCap

/-- Helper for Proposition 73.1: iterating the boundary rotation adds the
corresponding multiple of its angle to an exponential parameter. -/
private lemma rotation_pow_apply_exp (n k : ℕ) (θ : ℝ) :
    (rotation n ^ k) (Circle.exp θ) =
      Circle.exp (θ + k * (2 * Real.pi / n)) := by
  -- Induction exposes one rotation at a time and accumulates its angle.
  induction k generalizing θ with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Homeomorph.mul_apply, rotation_apply_exp, ih, Nat.cast_succ]
    congr 1
    ring

/-- Helper for Proposition 73.1: the rotation through `2 * π / n` has order
dividing `n`. -/
private lemma rotation_pow_order (n : ℕ) : rotation n ^ n = 1 := by
  -- For positive `n`, the accumulated angle is `2 * π`; the zero case is formal.
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · apply Homeomorph.ext
    intro z
    obtain ⟨θ, rfl⟩ := Circle.exp_surjective z
    rw [rotation_pow_apply_exp]
    have hnCast : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hangle : (n : ℝ) * (2 * Real.pi / n) = 2 * Real.pi :=
      mul_div_cancel₀ _ hnCast
    rw [hangle, Circle.exp_add, Circle.exp_two_pi, mul_one, Homeomorph.one_apply]

/-- Helper for Proposition 73.1: the boundary inclusion is injective. -/
private lemma boundary_injective : Function.Injective boundary := by
  -- Equality in the disk descends to equality of the underlying circle points.
  intro z w h
  exact Subtype.ext (congrArg (fun x : Disk ↦ (x : ℂ)) h)

/-- Helper for Proposition 73.1: equality or a single indexed boundary rotation
is an equivalence relation on the disk. -/
private lemma finiteRotationRelationEquivalence (n : ℕ) :
    Equivalence (fun x y : Disk ↦ x = y ∨ Related n x y) := by
  -- Reflexivity is supplied by the equality branch.
  refine ⟨fun x ↦ Or.inl rfl, ?_, ?_⟩
  · intro x y hxy
    rcases hxy with hxy | hxy
    · exact Or.inl hxy.symm
    · obtain ⟨z, k, rfl, rfl⟩ := hxy
      by_cases hk : (k : ℕ) = 0
      · left
        simp [hk]
      · right
        have hn : 0 < n := Nat.zero_lt_of_lt k.isLt
        have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk
        have hjlt : n - (k : ℕ) < n := Nat.sub_lt hn hkpos
        refine ⟨(rotation n ^ (k : ℕ)) z, ⟨n - (k : ℕ), hjlt⟩, rfl, ?_⟩
        apply congrArg boundary
        rw [← Homeomorph.mul_apply, pow_sub_mul_pow _ k.isLt.le,
          rotation_pow_order, Homeomorph.one_apply]
  · intro x y w hxy hyw
    rcases hxy with hxy | hxy
    · subst y
      exact hyw
    · rcases hyw with hyw | hyw
      · subst w
        exact Or.inr hxy
      · obtain ⟨z, k, hx, hy⟩ := hxy
        obtain ⟨z', l, hy', hw⟩ := hyw
        have hz' : z' = (rotation n ^ (k : ℕ)) z :=
          boundary_injective (hy'.symm.trans hy)
        have hn : 0 < n := Nat.zero_lt_of_lt k.isLt
        have hjlt : ((l : ℕ) + (k : ℕ)) % n < n := Nat.mod_lt _ hn
        refine Or.inr ⟨z, ⟨((l : ℕ) + (k : ℕ)) % n, hjlt⟩, hx, ?_⟩
        calc
          w = boundary ((rotation n ^ (l : ℕ)) z') := hw
          _ = boundary ((rotation n ^ (l : ℕ)) ((rotation n ^ (k : ℕ)) z)) := by
            rw [hz']
          _ = boundary (((rotation n ^ (l : ℕ)) * (rotation n ^ (k : ℕ))) z) := by
            rw [Homeomorph.mul_apply]
          _ = boundary ((rotation n ^ ((l : ℕ) + (k : ℕ))) z) := by
            rw [pow_add]
          _ = boundary ((rotation n ^ (((l : ℕ) + (k : ℕ)) % n)) z) := by
            rw [pow_eq_pow_mod _ (rotation_pow_order n)]

/-- Helper for Proposition 73.1: the finite boundary-rotation relation as a
setoid on the disk. -/
private def finiteRotationSetoid (n : ℕ) : Setoid Disk :=
  -- Package the verified equivalence relation without introducing new instance search.
  ⟨fun x y ↦ x = y ∨ Related n x y, finiteRotationRelationEquivalence n⟩

/-- Helper for Proposition 73.1: generated identification is exactly equality
or one indexed boundary rotation. -/
private lemma identified_iff_eq_or_related (n : ℕ) {x y : Disk} :
    Identified n x y ↔ x = y ∨ Related n x y := by
  -- Minimality of `Identified` gives the forward containment in the finite setoid.
  constructor
  · intro hxy
    have hle : Identified n ≤ finiteRotationSetoid n := by
      apply (identified_le_iff_boundary_rotations n (finiteRotationSetoid n)).2
      intro z k
      exact Or.inr ⟨z, k, rfl, rfl⟩
    exact hle hxy
  · intro hxy
    -- Equality and direct generators both lie in the generated relation.
    rcases hxy with rfl | hxy
    · exact Relation.EqvGen.refl x
    · exact Relation.EqvGen.rel _ _ hxy

/-- Helper for Proposition 73.1: the canonical inclusion of the circle into the
closed disk is continuous. -/
private lemma continuous_boundary : Continuous boundary := by
  -- The inclusion is the subtype lift of the circle's continuous coercion to `ℂ`.
  exact continuous_subtype_val.subtype_mk boundary_mem

/-- Helper for Proposition 73.1: the generated disk-identification relation has
a closed graph. -/
private lemma isClosed_identifiedGraph (n : ℕ) :
    IsClosed {pair : Disk × Disk | Identified n pair.1 pair.2} := by
  -- Normalize the generated relation to the diagonal and finitely many rotation graphs.
  have hgraph :
      {pair : Disk × Disk | Identified n pair.1 pair.2} =
        Set.diagonal Disk ∪
          ⋃ k : Fin n,
            Set.range (fun z : Circle ↦
              (boundary z, boundary ((rotation n ^ (k : ℕ)) z))) := by
    ext pair
    constructor
    · intro hpair
      rcases (identified_iff_eq_or_related n).1 hpair with heq | hrelated
      · exact Set.mem_union_left _ (Set.mem_diagonal_iff.2 heq)
      · obtain ⟨z, k, hx, hy⟩ := hrelated
        apply Set.mem_union_right
        apply Set.mem_iUnion.2
        refine ⟨k, Set.mem_range.2 ⟨z, ?_⟩⟩
        apply Prod.ext
        · exact hx.symm
        · exact hy.symm
    · intro hpair
      rcases hpair with hdiagonal | hrotation
      · exact (identified_iff_eq_or_related n).2
          (Or.inl (Set.mem_diagonal_iff.1 hdiagonal))
      · obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hrotation
        obtain ⟨z, hz⟩ := Set.mem_range.1 hk
        apply (identified_iff_eq_or_related n).2
        right
        refine ⟨z, k, ?_, ?_⟩
        · exact (congrArg Prod.fst hz).symm
        · exact (congrArg Prod.snd hz).symm
  rw [hgraph]
  -- Each rotation graph is a compact continuous image, hence closed in the disk product.
  apply isClosed_diagonal.union
  apply isClosed_iUnion_of_finite
  intro k
  apply IsCompact.isClosed
  apply isCompact_range
  exact continuous_boundary.prodMk
    (continuous_boundary.comp (rotation n ^ (k : ℕ)).continuous)

/-- Helper for Proposition 73.1: the explicit and inferred-setoid quotient
constructors define the same projection. -/
private lemma quotientMk_eq_quotientMk' {X : Type*} (setoid : Setoid X) :
    Quotient.mk setoid = @Quotient.mk' X setoid := by
  -- Both constructors represent the same point of the quotient.
  funext x
  exact Quotient.sound (setoid.refl x)

/-- Helper for Proposition 73.1: a quotient of a compact Hausdorff space by a
closed equivalence relation has a closed quotient map. -/
private lemma isClosedMap_quotientMk_of_isClosed_relation
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (setoid : Setoid X)
    (hrelation : IsClosed {pair : X × X | setoid pair.1 pair.2}) :
    IsClosedMap (Quotient.mk setoid) := by
  -- Pull the image of a closed set back to its relation-saturation.
  rw [quotientMk_eq_quotientMk' setoid]
  intro C hC
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
  have hsaturation :
      (@Quotient.mk' X setoid) ⁻¹' ((@Quotient.mk' X setoid) '' C) =
        Prod.fst ''
          ({pair : X × X | setoid pair.1 pair.2} ∩ (Set.univ ×ˢ C)) := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      refine ⟨(x, y), ⟨Quotient.exact heq.symm, Set.mem_prod.2 ⟨Set.mem_univ x, hy⟩⟩, rfl⟩
    · rintro ⟨⟨x', y⟩, ⟨hxy, _, hy⟩, hx'⟩
      have hx : x' = x := hx'
      have hrelation_xy : setoid x' y := hxy
      have hyC : y ∈ C := hy
      subst x'
      exact ⟨y, hyC, (Quotient.sound hrelation_xy).symm⟩
  rw [hsaturation]
  -- Compactness of the closed graph section survives the first projection.
  exact ((hrelation.inter (isClosed_univ.prod hC)).isCompact.image continuous_fst).isClosed

/-- Proposition 73.1: The quotient map from the closed disk to the `n`-fold dunce cap
is a closed map. -/
theorem quotientMap_isClosedMap (n : ℕ) : IsClosedMap (quotientMap n) := by
  -- Normalize the named quotient topology before applying the closed-graph criterion.
  unfold quotientMap Space instTopologicalSpaceSpace
  exact isClosedMap_quotientMk_of_isClosed_relation (Identified n)
    (isClosed_identifiedGraph n)

end DunceCap
