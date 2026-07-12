import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_6_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

section

universe u

variable (R : Type*) {E : Type u} [Zero R] [LE R] [SMul R E]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 2.6.12 says that a convex set `C` is the section at height `1` of
  a convex cone in one higher dimension, while the concrete lifted model is the subset
  `homogenizationSet C = {(λ, x) | 0 ≤ λ, x ∈ λ • C}`.
- `core/canonical`: the owner abstractions are the source-facing set `homogenizationSet C` and the
  generated pointed cone `PointedCone.hull R (Prod.mk 1 '' C)` from Definition 2.6.10.
- `bridge/view`: the canonical bridge identifies the generated pointed cone with
  `insert 0 (homogenizationSet C)`, so later chapter files can use the source-facing owner
  `homogenizationSet C` while still reusing the chapter-level cone owner from
  Definition 2.6.10.
- Primitive data vs derived API: the primitive concrete data are the lifted set
  `homogenizationSet C` and the lift image `Prod.mk 1 '' C`; the pointed-cone bridge and the
  unit-section equivalences are derived API from the canonical generated-cone owner.
  `PointedCone.ofConeComb`, `PointedCone.mem_hull_set`, and the source-facing convex-combination
  structure of `homogenizationSet`.
- Layer target: `bridge/view`.
-/

/-- The lifted set `K_C = {(λ, x) | 0 ≤ λ, x ∈ λ • C}` attached to a subset `C`. -/
def homogenizationSet (C : Set E) : Set (R × E) :=
  {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C}

scoped[Rockafellar] notation "K[" R " | " C "]" => homogenizationSet R C

open scoped Rockafellar

/-- Membership in `homogenizationSet C` means having nonnegative first coordinate and second
coordinate in the corresponding scalar multiple of `C`. -/
theorem mem_homogenizationSet_iff (C : Set E) (p : R × E) :
    p ∈ K[R | C] ↔ 0 ≤ p.1 ∧ p.2 ∈ p.1 • C :=
  Iff.rfl

end

open scoped Rockafellar

section

universe u

variable (R : Type*) [One R] {E : Type u}

/-- The canonical height-`1` lift `{(1, x) | x ∈ C}` of a set `C`. -/
def unitLift (C : Set E) : Set (R × E) :=
  Prod.mk (1 : R) '' C

scoped[Rockafellar] notation "L[" R " | " C "]" => unitLift R C

@[simp] theorem mem_unitLift_iff (C : Set E) (x : E) :
    ((1 : R), x) ∈ L[R | C] ↔ x ∈ C := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    cases hxy
    simpa using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The height-`1` section of a subset of `R × E`. -/
def unitSection (S : Set (R × E)) : Set E :=
  Prod.mk (1 : R) ⁻¹' S

scoped[Rockafellar] notation "U[" R " | " S "]" => unitSection R (S : Set _)

@[simp] theorem mem_unitSection_iff (S : Set (R × E)) (x : E) :
    x ∈ U[R | S] ↔ ((1 : R), x) ∈ S :=
  Iff.rfl

/-- The height-`1` section turns intersections in `R × E` into intersections in `E`. -/
@[simp] theorem unitSection_inter (S T : Set (R × E)) :
    U[R | S ∩ T] = U[R | S] ∩ U[R | T] := by
  ext x
  rfl

end

section

universe u

variable {R : Type*} {E : Type u}
  [Semiring R] [PartialOrder R] [IsOrderedRing R]
  [AddCommMonoid E] [Module R E]

namespace PointedCone

/-- Projecting the generated cone of the unit lift `{(1, x) | x ∈ C}` to the second coordinate
recovers exactly the generated cone of `C`. -/
theorem map_cone_unitLift_eq_cone (C : Set E) :
    (cone[R] (L[R | C])).map (LinearMap.snd R R E) = cone[R] C := by
  have hlift_comap :
      L[R | C] ⊆ (cone[R] C).comap (LinearMap.snd R R E) := by
    intro p hp
    rcases hp with ⟨x, hx, rfl⟩
    simpa [PointedCone.mem_comap] using
      (PointedCone.subset_hull (R := R) (s := C) hx : x ∈ cone[R] C)
  have hmap_le :
      (cone[R] (L[R | C])).map (LinearMap.snd R R E) ≤ cone[R] C := by
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    exact (Submodule.span_le.2 hlift_comap hp : LinearMap.snd R R E p ∈ cone[R] C)
  have hsubset : C ⊆ (cone[R] (L[R | C])).map (LinearMap.snd R R E) := by
    intro x hx
    exact ⟨(1, x), PointedCone.subset_hull (R := R) (s := L[R | C]) ⟨x, hx, rfl⟩, rfl⟩
  have hcone_le_map :
      (cone[R] C : PointedCone R E) ≤ (cone[R] (L[R | C])).map (LinearMap.snd R R E) := by
    exact Submodule.span_le.mpr hsubset
  exact le_antisymm hmap_le hcone_le_map

/-- Set-level projection form of `map_cone_unitLift_eq_cone`. -/
@[simp] theorem snd_image_cone_unitLift_eq_cone (C : Set E) :
    LinearMap.snd R R E '' (cone[R] (L[R | C]) : Set (R × E)) = (cone[R] C : Set E) := by
  simpa [PointedCone.map] using
    congrArg (fun K : PointedCone R E => (K : Set E)) (map_cone_unitLift_eq_cone (R := R) C)

end PointedCone

end

open scoped Rockafellar

section

universe u

variable {R : Type*} {E : Type u} [Monoid R] [Zero R] [LE R] [ZeroLEOneClass R]
  [MulAction R E]

/-- At height `1`, the unit section of `homogenizationSet C` is exactly `C`. -/
@[simp] theorem mem_unitSection_homogenizationSet_iff (C : Set E) (x : E) :
    x ∈ U[R | K[R | C]] ↔ x ∈ C := by
  rw [mem_unitSection_iff, mem_homogenizationSet_iff R C]
  constructor
  · intro hx
    rcases Set.mem_smul_set.mp hx.2 with ⟨y, hy, hyx⟩
    have hxy : y = x := by
      exact (one_smul R y).symm.trans hyx
    simpa [hxy] using hy
  · intro hx
    refine ⟨zero_le_one, Set.mem_smul_set.mpr ⟨x, hx, ?_⟩⟩
    change (1 : R) • x = x
    exact one_smul R x

/-- At height `1`, the unit section of `homogenizationSet C` is exactly `C`. -/
@[simp] theorem unitSection_homogenizationSet_eq (C : Set E) :
    U[R | K[R | C]] = C := by
  ext x
  simpa using (mem_unitSection_homogenizationSet_iff (R := R) (C := C) (x := x))

/-- Raw ambient view of `mem_unitSection_homogenizationSet_iff` at height `1`. -/
@[simp] theorem mem_homogenizationSet_one_iff (C : Set E) (x : E) :
    ((1 : R), x) ∈ K[R | C] ↔ x ∈ C := by
  exact
    (mem_unitSection_iff (R := R) (S := K[R | C]) (x := x)).symm.trans
      (mem_unitSection_homogenizationSet_iff (R := R) (C := C) (x := x))

end

section

universe u

variable {R : Type*} {E : Type u} [Semifield R] [PartialOrder R] [IsOrderedRing R]
  [PosMulReflectLT R] [AddCommMonoid E] [Module R E]

omit [PosMulReflectLT R] in
private theorem smul_mem_homogenizationSet
    (C : Set E) {a : R} (ha : 0 < a) {p : R × E} (hp : p ∈ K[R | C]) :
    a • p ∈ K[R | C] := by
  rcases p with ⟨r, x⟩
  rcases (mem_homogenizationSet_iff R C (r, x)).1 hp with ⟨hr, hx⟩
  refine (mem_homogenizationSet_iff R C _).2 ?_
  constructor
  · exact mul_nonneg ha.le hr
  · have hx' : a • x ∈ a • (r • C) := Set.smul_mem_smul_set hx
    simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using hx'

private theorem combo_mem_homogenizationSet
    (C : Set E) (hC : Convex R C) {p q : R × E} {a b : R}
    (hp : p ∈ K[R | C]) (hq : q ∈ K[R | C])
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • p + b • q ∈ K[R | C] := by
  rcases p with ⟨r₁, x₁⟩
  rcases q with ⟨r₂, x₂⟩
  rcases (mem_homogenizationSet_iff R C (r₁, x₁)).1 hp with ⟨hr₁, hx₁⟩
  rcases (mem_homogenizationSet_iff R C (r₂, x₂)).1 hq with ⟨hr₂, hx₂⟩
  rcases Set.mem_smul_set.mp hx₁ with ⟨y₁, hy₁, hyx₁⟩
  rcases Set.mem_smul_set.mp hx₂ with ⟨y₂, hy₂, hyx₂⟩
  change (a * r₁ + b * r₂, a • x₁ + b • x₂) ∈ K[R | C]
  let r : R := a * r₁ + b * r₂
  have hr_nonneg : 0 ≤ r := add_nonneg (mul_nonneg ha hr₁) (mul_nonneg hb hr₂)
  refine (mem_homogenizationSet_iff R C _).2 ⟨hr_nonneg, ?_⟩
  change a • x₁ + b • x₂ ∈ r • C
  by_cases hr : r = 0
  · rw [hr]
    have hsum : a * r₁ + b * r₂ = 0 := by simpa [r] using hr
    have hzero_terms :=
      (add_eq_zero_iff_of_nonneg (mul_nonneg ha hr₁) (mul_nonneg hb hr₂)).1 hsum
    have har₁ : a * r₁ = 0 := hzero_terms.1
    have hbr₂ : b * r₂ = 0 := hzero_terms.2
    have hx₁' : (a * r₁) • y₁ = a • x₁ := by
      simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z ↦ a • z) hyx₁
    have hx₂' : (b * r₂) • y₂ = b • x₂ := by
      simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z ↦ b • z) hyx₂
    refine Set.mem_smul_set.mpr ⟨y₁, hy₁, ?_⟩
    calc
      (0 : R) • y₁ = 0 := by simp
      _ = (a * r₁) • y₁ + (b * r₂) • y₂ := by simp [har₁, hbr₂]
      _ = a • x₁ + b • x₂ := by rw [hx₁', hx₂']
  · have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (by simpa [eq_comm] using hr)
    let α : R := a * r₁ / r
    let β : R := b * r₂ / r
    have hα_nonneg : 0 ≤ α := by
      dsimp [α]
      exact div_nonneg (mul_nonneg ha hr₁) hr_nonneg
    have hβ_nonneg : 0 ≤ β := by
      dsimp [β]
      exact div_nonneg (mul_nonneg hb hr₂) hr_nonneg
    have hαβ : α + β = 1 := by
      calc
        α + β = (a * r₁ + b * r₂) / r := by
          dsimp [α, β]
          rw [← add_div]
        _ = r / r := by rfl
        _ = 1 := by field_simp [hr]
    have hmem : α • y₁ + β • y₂ ∈ C := hC hy₁ hy₂ hα_nonneg hβ_nonneg hαβ
    have hx₁' : (a * r₁) • y₁ = a • x₁ := by
      simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z ↦ a • z) hyx₁
    have hx₂' : (b * r₂) • y₂ = b • x₂ := by
      simpa [smul_smul, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun z ↦ b • z) hyx₂
    refine Set.mem_smul_set.mpr ⟨α • y₁ + β • y₂, hmem, ?_⟩
    calc
      r • (α • y₁ + β • y₂) = (r * α) • y₁ + (r * β) • y₂ := by
        rw [smul_add, smul_smul, smul_smul]
      _ = (a * r₁) • y₁ + (b * r₂) • y₂ := by
        congr 1
        · dsimp [α]
          field_simp [hr]
        · dsimp [β]
          field_simp [hr]
      _ = a • x₁ + b • x₂ := by rw [hx₁', hx₂']

/-- The homogenization set of a convex set is convex. -/
theorem Convex.homogenizationSet {C : Set E} (hC : Convex R C) :
    Convex R (K[R | C]) := by
  exact convex_iff_add_mem.2 <| by
    intro p hp q hq a b ha hb _
    exact combo_mem_homogenizationSet C hC hp hq ha hb

/-- The intersection of the homogenization sets of two convex sets is convex. -/
theorem Convex.homogenizationSet_inter {C₁ C₂ : Set E}
    (hC₁ : Convex R C₁) (hC₂ : Convex R C₂) :
    Convex R (K[R | C₁] ∩ K[R | C₂]) :=
  hC₁.homogenizationSet.inter hC₂.homogenizationSet

/-- The pointwise sum of the homogenization sets of two convex sets is convex. -/
theorem Convex.homogenizationSet_add {C₁ C₂ : Set E}
    (hC₁ : Convex R C₁) (hC₂ : Convex R C₂) :
    Convex R (K[R | C₁] + K[R | C₂]) :=
  hC₁.homogenizationSet.add hC₂.homogenizationSet

/- For a convex set `C`, the pointed cone generated by `{(1, x) | x ∈ C}` is exactly the
source-facing homogenization set together with the origin. This is the exact owner-level bridge
between the chapter's source-facing set `homogenizationSet C` and the canonical pointed-cone hull;
the nonempty specialization below removes the inserted origin. -/
theorem pointedConeHull_lift_eq_insert_homogenizationSet
    (C : Set E) (hC : Convex R C) :
    (cone[R] (L[R | C]) : Set (R × E)) = insert 0 (K[R | C]) := by
  ext p
  constructor
  · intro hp
    let K : PointedCone R (R × E) :=
      PointedCone.ofConeComb (insert 0 (K[R | C])) ⟨0, by simp⟩ <| by
        intro x hx y hy a ha b hb
        rcases hx with rfl | hx
        · rcases hy with rfl | hy
          · simp
          · by_cases hb0 : b = 0
            · simp [hb0]
            · right
              simpa [zero_smul] using
                smul_mem_homogenizationSet C (lt_of_le_of_ne hb (by simpa [eq_comm] using hb0)) hy
        · rcases hy with rfl | hy
          · by_cases ha0 : a = 0
            · simp [ha0]
            · right
              simpa [zero_smul, add_comm] using
                smul_mem_homogenizationSet C (lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)) hx
          · right
            exact combo_mem_homogenizationSet C hC hx hy ha hb
    have hHull_le : PointedCone.hull R (L[R | C]) ≤ K :=
      Submodule.span_le.mpr fun p hp ↦ by
        rcases hp with ⟨x, hx, rfl⟩
        right
        exact (mem_homogenizationSet_iff R C ((1 : R), x)).2 ⟨zero_le_one, by simpa⟩
    exact hHull_le hp
  · rintro (rfl | hp)
    · exact (cone[R] (L[R | C])).zero_mem
    · rcases (mem_homogenizationSet_iff R C p).1 hp with ⟨hp1, hp2⟩
      by_cases hzero : p = 0
      · simp [hzero]
      · have hp1ne : p.1 ≠ 0 := by
          intro hp10
          rcases Set.mem_smul_set.mp (hp10 ▸ hp2) with ⟨x, hx, hx0⟩
          apply hzero
          ext
          · simp [hp10]
          · simpa [eq_comm] using hx0
        rcases Set.mem_smul_set.mp hp2 with ⟨x, hx, hpx⟩
        have hx_hull : ((1 : R), x) ∈ cone[R] (L[R | C]) :=
          PointedCone.subset_hull ⟨x, hx, rfl⟩
        have hp_hull :
            p.1 • ((1 : R), x) ∈ cone[R] (L[R | C]) :=
          (cone[R] (L[R | C])).smul_mem hp1 hx_hull
        simpa [hpx] using hp_hull

/-- Pointwise form of `pointedConeHull_lift_eq_insert_homogenizationSet`. -/
@[simp] theorem mem_pointedConeHull_lift_iff (C : Set E) (hC : Convex R C) (p : R × E) :
    p ∈ (cone[R] (L[R | C]) : Set (R × E)) ↔ p = 0 ∨ p ∈ K[R | C] := by
  rw [pointedConeHull_lift_eq_insert_homogenizationSet (R := R) (C := C) hC]
  exact Set.mem_insert_iff

/-- If `C` is nonempty and convex, then the inserted origin in
`pointedConeHull_lift_eq_insert_homogenizationSet` is already contained in `homogenizationSet C`,
so the source-facing homogenization set is exactly the canonical pointed cone generated by its
lift `{(1, x) | x ∈ C}`. -/
theorem homogenizationSet_eq_pointedConeHull
    (C : Set E) (hC : Convex R C) (hC_nonempty : C.Nonempty) :
    K[R | C] = (cone[R] (L[R | C]) : Set (R × E)) := by
  have hzero : (0 : R × E) ∈ K[R | C] := by
    rcases hC_nonempty with ⟨x, hx⟩
    refine (mem_homogenizationSet_iff R C 0).2 ⟨le_rfl, ?_⟩
    exact Set.mem_smul_set.mpr ⟨x, hx, by simp⟩
  rw [pointedConeHull_lift_eq_insert_homogenizationSet C hC, Set.insert_eq_of_mem hzero]

/-- Canonical owner-oriented form of `homogenizationSet_eq_pointedConeHull`: for nonempty convex
`C`, the generated pointed cone of the unit lift equals `homogenizationSet C`. -/
@[simp] theorem pointedConeHull_lift_eq_homogenizationSet
    (C : Set E) (hC : Convex R C) (hC_nonempty : C.Nonempty) :
    (cone[R] (L[R | C]) : Set (R × E)) = K[R | C] := by
  simpa [eq_comm] using homogenizationSet_eq_pointedConeHull (R := R) C hC hC_nonempty

/-- Proposition 2.6.12, pointwise form: a point `x` lies in `C` exactly when `((1, x) : R × E)`
lies in the height-`1` section of the canonical pointed cone generated by the lift
`{(1, y) | y ∈ C}`. -/
-- Proof sketch: rewrite the canonical pointed cone by
-- `pointedConeHull_lift_eq_insert_homogenizationSet`. At height `1`, the origin is impossible, so
-- the section reduces to the height-`1` homogenization membership bridge
-- `mem_homogenizationSet_one_iff`.
theorem mem_unitSection_pointedConeHull_lift_iff (C : Set E) (hC : Convex R C) (x : E) :
    x ∈ U[R | cone[R] (L[R | C])] ↔ x ∈ C := by
  rw [mem_unitSection_iff, pointedConeHull_lift_eq_insert_homogenizationSet C hC]
  simp [mem_homogenizationSet_one_iff]

/-- Proposition 2.6.12: a convex set `C` is the height-`1` preimage of the canonical pointed cone
generated by its lift `{(1, x) | x ∈ C}` in `R × E`. -/
@[simp] theorem unitSection_pointedConeHull_lift_eq (C : Set E) (hC : Convex R C) :
    U[R | cone[R] (L[R | C])] = C := by
  ext x
  exact mem_unitSection_pointedConeHull_lift_iff C hC x

/-- Compatibility orientation of `unitSection_pointedConeHull_lift_eq`. -/
theorem convex_eq_unitSection_homogenizationCone (C : Set E) (hC : Convex R C) :
    C = U[R | cone[R] (L[R | C])] := by
  simpa [eq_comm] using (unitSection_pointedConeHull_lift_eq (R := R) C hC)

end
