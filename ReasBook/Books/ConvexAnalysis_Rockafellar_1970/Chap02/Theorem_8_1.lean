import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_9
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Pointwise

section

variable {R : Type v} [Zero R] [LE R]
variable {E : Type u} [AddZeroClass E] [SMulZeroClass R E]

/- 
Source/core/bridge triage:
- `source-facing`: Theorem 8.1 studies the recession cone `0⁺[R] C` of a convex set `C`.
- `core/canonical`: the chapter owner object is the source-facing set-valued declaration
  `recessionCone` from Definition 8.0.2, while the project owner abstraction for its cone laws is
  `Set.IsCone R`.
- `bridge/view`: the nontrivial content of the theorem is the identification of the recession cone
  with translation invariance. This file now takes the intrinsic owner-facing surface
  `y +ᵥ C ⊆ C` as primary and keeps `C + {y} ⊆ C` as the source-facing bridge view; the
  membership theorem is the atomic bridge and the set equalities are derived corollaries. Any
  temporary bundled-cone view belongs downstream as an internal bridge, not as a second public
  owner here.
- Primitive data vs derived API: the primitive owner data is the imported operation
  `recessionCone C`, whose source-facing theorem surface in this file is written with the
  scalar-annotated notation `0⁺[R] C`; the owner-side derived API first proves
  `zero_mem_recessionCone`, `recessionCone_isCone`, and the convexity corollary
  `recessionCone_convex`, while the translation characterization stays theorem-level.
- Domain-style sampling: this item reuses the chapter owner pair `recessionCone` /
  `Set.mem_recessionCone_iff`, the chapter cone owner `Set.IsCone R`, and intrinsic translation
  owner `Set.vaddSet`; the bundled cone owners
  `PointedCone R E` and `ConvexCone R E` were sampled only to confirm that no extra public wrapper
  is needed in this file.
- Layer target: the cone-law lemmas are companion owner API on `recessionCone`. The later
  translation-invariance bridge remains in the ordered-ring-with-floor section because its proof
  is genuinely about filling intervals between consecutive integer translates.
-/

/-- The zero vector is always a recession direction. -/
theorem zero_mem_recessionCone (C : Set E) :
    (0 : E) ∈ 0⁺[R] C := by
  rw [Set.mem_recessionCone_iff]
  intro x hx a ha
  simpa

end

section

variable {R : Type v} [Semiring R] [Preorder R] [PosMulMono R]
variable {E : Type u} [Add E] [MulAction R E]

/-- The recession cone is a cone in the Chapter 1 owner sense. -/
theorem recessionCone_isCone (C : Set E) : Set.IsCone R (0⁺[R] C) := by
  refine (Set.isCone_iff_forall_pos_smul_subset (𝕜 := R) (K := 0⁺[R] C)).2 ?_
  intro a ha y hy
  rcases Set.mem_smul_set.mp hy with ⟨z, hz, rfl⟩
  rw [Set.mem_recessionCone_iff] at hz ⊢
  intro x hx b hb
  have hxy : x + (b * a) • z ∈ C := hz x hx (b * a) (mul_nonneg hb ha.le)
  simpa [smul_smul] using hxy

end

section

variable {R : Type v} [Semiring R] [PartialOrder R] [PosMulMono R]
variable {E : Type u} [AddCommMonoid E] [DistribMulAction R E]

/-- The recession cone is convex. -/
theorem recessionCone_convex (C : Set E) : Convex R (0⁺[R] C) := by
  intro y hy z hz a b ha hb hab
  rw [Set.mem_recessionCone_iff] at hy hz ⊢
  intro x hx t ht
  have hxy : x + (t * a) • y ∈ C := hy x hx (t * a) (mul_nonneg ht ha)
  have hxyz : x + (t * a) • y + (t * b) • z ∈ C :=
    hz (x + (t * a) • y) hxy (t * b) (mul_nonneg ht hb)
  simpa [smul_add, smul_smul, mul_assoc, add_assoc, add_left_comm, add_comm] using hxyz

end

section

-- The converse direction uses `Nat.floor` and subtraction on scalars, so this section keeps
-- exactly the ordered-ring + floor stack needed by that interval-filling argument.
variable {R : Type v} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]
variable {E : Type u} [AddCommMonoid E] [Module R E]

/-
For a convex set, a vector lies in the recession cone exactly when translating by that vector
sends `C` into itself.
-/
-- Proof sketch: one implication is the special case `a = 1` of the defining recession property.
-- For the converse, iterate the inclusion `y +ᵥ C ⊆ C` to get `x + m • y ∈ C` for integers
-- `m ≥ 0`, then use convexity of `C` to fill the segments between consecutive integer translates
-- and obtain `x + a • y ∈ C` for every scalar `a ≥ 0`.
namespace Convex

variable {C : Set E}

/-- For a convex set, a vector lies in the recession cone exactly when translating by that vector
sends `C` into itself. -/
theorem mem_recessionCone_iff_vadd_subset_self
    (hC : Convex R C) (y : E) :
    y ∈ 0⁺[R] C ↔ y +ᵥ C ⊆ C := by
  constructor
  · intro hy
    rw [Set.mem_recessionCone_iff] at hy
    intro z hz
    rcases Set.mem_vadd_set.mp hz with ⟨x, hx, rfl⟩
    simpa [vadd_eq_add, add_comm] using hy x hx 1 zero_le_one
  · intro hsubset
    rw [Set.mem_recessionCone_iff]
    intro x hx a ha
    let S : Set R := {r | x + r • y ∈ C}
    have hstep : ∀ {z : E}, z ∈ C → z + y ∈ C := by
      intro z hz
      have hz' : y +ᵥ z ∈ C := hsubset (Set.mem_vadd_set.mpr ⟨z, hz, rfl⟩)
      simpa [vadd_eq_add, add_comm] using hz'
    have hS_convex : Convex R S := by
      intro a ha b hb s t hs ht hst
      change x + (s * a + t * b) • y ∈ C
      have hab : s • (x + a • y) + t • (x + b • y) ∈ C := hC ha hb hs ht hst
      have hab' : (s • x + t • x) + ((s * a) • y + (t * b) • y) ∈ C := by
        simpa [smul_add, smul_smul, add_assoc, add_left_comm, add_comm] using hab
      have hxst : s • x + t • x = x := by
        calc
          s • x + t • x = (s + t) • x := by rw [add_smul]
          _ = x := by simp [hst]
      simpa [hxst, add_assoc, add_left_comm, add_comm, add_smul] using hab'
    have hnat : ∀ n : ℕ, (n : R) ∈ S := by
      intro n
      induction n with
      | zero =>
          simpa [S] using hx
      | succ n hn =>
          change x + (((n + 1 : ℕ) : R) • y) ∈ C
          have hEq : x + (n : R) • y + y = x + (((n + 1 : ℕ) : R) • y) := by
            simp [Nat.cast_add, add_left_comm, add_comm, add_smul]
          exact hEq ▸ hstep hn
    let n : ℕ := Nat.floor a
    have ha_seg : a ∈ [(n : R) -[R] (n + 1 : ℕ)] := by
      have hna : (n : R) ≤ a := Nat.floor_le ha
      have han1 : a ≤ (n + 1 : ℕ) := by
        exact le_of_lt (by
          simpa [n, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
            Nat.lt_floor_add_one a)
      rw [segment_eq_image R (n : R) (n + 1 : ℕ), Set.mem_image]
      refine ⟨a - n, ?_, ?_⟩
      · exact (Set.mem_Icc).2 ⟨sub_nonneg.mpr hna, by
          rw [sub_le_iff_le_add]
          simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using han1⟩
      · have hcast : ((n + 1 : ℕ) : R) = (n : R) + 1 := by
          simp [Nat.cast_add]
        calc
          (1 - (a - (n : R))) • (n : R) + (a - (n : R)) • ((n + 1 : ℕ) : R)
              = (1 - (a - (n : R))) * (n : R) + (a - (n : R)) * ((n : R) + 1) := by
                  simp [hcast]
          _ = (1 - (a - (n : R))) * (n : R) + ((a - (n : R)) * (n : R) + (a - (n : R)) * 1) := by
                rw [mul_add]
          _ = ((1 - (a - (n : R))) * (n : R) + (a - (n : R)) * (n : R)) + (a - (n : R)) := by
                simp [add_assoc]
          _ = ((1 - (a - (n : R)) + (a - (n : R))) * (n : R)) + (a - (n : R)) := by
                rw [add_mul]
          _ = (n : R) + (a - (n : R)) := by simp
          _ = a := by
                simp [sub_eq_add_neg, add_left_comm]
    exact hS_convex.segment_subset (hnat n) (hnat (n + 1)) ha_seg

/-- Source-facing singleton-addition bridge view of Theorem 8.1. -/
theorem mem_recessionCone_iff_add_singleton_subset_self
    (hC : Convex R C) (y : E) :
    y ∈ 0⁺[R] C ↔ C + {y} ⊆ C := by
  rw [mem_recessionCone_iff_vadd_subset_self hC y]
  rw [Set.add_singleton, ← Set.image_vadd]
  simp [vadd_eq_add, add_comm]

/-- Intrinsic set-equality form of Theorem 8.1: for a convex set `C`, the recession cone
coincides with the vectors whose translations preserve `C`. -/
theorem recessionCone_eq_setOf_vadd_subset_self (hC : Convex R C) :
    0⁺[R] C = {y : E | y +ᵥ C ⊆ C} := by
  ext y
  rw [Set.mem_setOf_eq]
  exact hC.mem_recessionCone_iff_vadd_subset_self y

/-- Theorem 8.1: for a convex set `C`, the recession cone `0⁺[R] C` coincides with the set of
vectors `y` such that the translate `C + {y}` is contained in `C`. -/
-- Proof sketch: extensionality reduces the statement to
-- `Convex.mem_recessionCone_iff_vadd_subset_self` plus `C + {y} = y +ᵥ C`.
theorem recessionCone_eq_setOf_add_singleton_subset_self (hC : Convex R C) :
    0⁺[R] C = {y : E | C + {y} ⊆ C} := by
  ext y
  rw [Set.mem_setOf_eq, hC.mem_recessionCone_iff_vadd_subset_self y]
  rw [Set.add_singleton, ← Set.image_vadd]
  simp [vadd_eq_add, add_comm]

end Convex

end
