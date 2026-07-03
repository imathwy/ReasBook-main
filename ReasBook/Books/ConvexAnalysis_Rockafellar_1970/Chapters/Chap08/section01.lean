

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_8_1_1 (from Chap02) -/
section

universe u v

variable {k : Type v} {E : Type u} [Ring k] [LE k]
  [AddCommGroup E] [Module k E]

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 8.1.1 identifies the recession directions of a nonempty affine set
  with its parallel linear subspace.
- `core/canonical`: the chapter owner is `recessionCone`, and the affine owner is
  `AffineSubspace.direction`.
- `bridge/view`: `Set.mem_recessionCone_iff` expands recession-cone membership into the source ray
  condition, while `AffineSubspace.vadd_mem_iff_mem_direction` is the canonical affine-owner
  bridge between translated-point membership and direction membership. The source-facing parallel
  submodule phrasing is exposed below as a thin bridge theorem derived from
  `AffineSubspace.Parallel.direction_eq` and `Submodule.toAffineSubspace_direction`.
- Domain-style sampling used here: `Set.mem_recessionCone_iff`,
  `AffineSubspace.vadd_mem_iff_mem_direction`,
  `AffineSubspace.Parallel.direction_eq`, and `Submodule.toAffineSubspace_direction`.
- Primitive data vs derived API: the primitive data are just the affine subspace `M` and its
  intrinsic nonemptiness datum `[Nonempty M]`. Any equality with a separately named parallel
  submodule is derived API from the owner theorem below, and the submodule bridge theorem derives
  this nonemptiness from parallelism to `D.toAffineSubspace`.
- Layer target: this refinement is `core/canonical`; the source wording is recovered from the
  owner theorem through the thin parallel bridge theorem below.
-/

namespace AffineSubspace

variable [ZeroLEOneClass k]

/-- Corollary 8.1.1, owner form: the recession cone of a nonempty affine set is exactly its
direction subspace. The proof uses only affine-module algebra and the scalar-side fact `0 ≤ 1`,
so the owner theorem is kept at this weaker ordered-scalar layer; specializing to `ℝ` recovers
the textbook statement `0⁺[k] M = (M.direction : Set E)`. -/
theorem recessionCone_eq_direction
    (M : AffineSubspace k E) [Nonempty M] :
    0⁺[k] M = (M.direction : Set E) := by
  ext y
  rw [Set.mem_recessionCone_iff]
  constructor
  · intro hy
    rcases (show Nonempty M from inferInstance) with ⟨⟨x, hx⟩⟩
    have hxy : y +ᵥ x ∈ M := by
      simpa [vadd_eq_add, add_comm] using hy x hx 1 zero_le_one
    exact (M.vadd_mem_iff_mem_direction y hx).1 hxy
  · intro hy x hx a ha
    have haxy : a • y +ᵥ x ∈ M :=
      M.vadd_mem_of_mem_direction (M.direction.smul_mem a hy) hx
    simpa [vadd_eq_add, add_comm] using haxy

/-- Corollary 8.1.1, source-facing bridge: if `M` is nonempty and parallel to `N`, then the
recession cone of `M` is exactly the direction of `N`. -/
theorem recessionCone_eq_direction_of_parallel
    (M N : AffineSubspace k E) (hMN : M.Parallel N) (hM : Nonempty M) :
    0⁺[k] M = (N.direction : Set E) := by
  letI : Nonempty M := hM
  calc
    0⁺[k] (M : Set E) = (M.direction : Set E) := M.recessionCone_eq_direction
    _ = (N.direction : Set E) := by
      simpa using congrArg (fun S : Submodule k E => (S : Set E)) hMN.direction_eq

/-- Corollary 8.1.1, source-facing bridge: if an affine subspace `M` is parallel to a
submodule `D`, then the recession cone of `M` is exactly `D`. -/
theorem recessionCone_eq_of_parallel
    (M : AffineSubspace k E) (D : Submodule k E)
    (hMD : M.Parallel D.toAffineSubspace) :
    0⁺[k] M = (D : Set E) := by
  have hD : Nonempty D.toAffineSubspace := by
    refine ⟨⟨0, ?_⟩⟩
    simp [Submodule.mem_toAffineSubspace]
  have hM : Nonempty M := by
    rcases hMD.symm with ⟨v, rfl⟩
    rcases hD with ⟨⟨x, hx⟩⟩
    refine ⟨⟨v +ᵥ x, ?_⟩⟩
    exact AffineSubspace.mem_map_of_mem
      (f := (AffineEquiv.constVAdd k E v : E →ᵃ[k] E)) hx
  calc
    0⁺[k] (M : Set E) = (D.toAffineSubspace.direction : Set E) :=
      recessionCone_eq_direction_of_parallel (M := M) (N := D.toAffineSubspace) hMD hM
    _ = (D : Set E) := by simp

end AffineSubspace

end

/-! ### Theorem_8_1 (from Chap02) -/
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

/-! ### Corollary_8_1_2 (from Chap02) -/
open scoped Pointwise Rockafellar

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [HasPairing X Y 𝕜] {I : Sort*}

/-
Source/core/bridge triage:
- `source-facing`: Corollary 8.1.2 identifies the recession cone of the feasible region cut out by
  the inequalities `β i ≤ ⟪x, b i⟫ₚ`.
- `core/canonical`: the chapter owner abstractions are `0⁺`,
  `LinearConstraintRelation.geFeasible`, and
  `LinearConstraintRelation.homogeneousGeFeasibleSet`; this item is the `.ge` feasible-region
  specialization of the mixed owner layer.
- `bridge/view`: the textbook sets `⋂ i, closedHalfSpaceGE (b i) (β i)` and
  `⋂ i, closedHalfSpaceGE (b i) 0` are the `.ge` specializations of the owner feasible sets with
  right-hand sides `β` and `0`.
- Domain-style sampling: the relevant existing declarations in this domain are
  `HasPairing`, `IsLinearMap`, `LinearConstraintRelation.geFeasible`,
  `LinearConstraintRelation.mem_geFeasible`,
  `LinearConstraintRelation.mem_homogeneousGeFeasibleSet`,
  `closedHalfSpaceGE`, `0⁺`, `Set.mem_recessionCone_iff`,
  `mem_recessionCone_iff_add_singleton_subset_self`, and
  `LinearConstraintRelation.convex_feasibleSet`; the primitive owner layer for this corollary only
  needs the indexed linearity data `x ↦ ⟪x, b i⟫ₚ`, while the global
  `HasLinearPairing` owner stays as a derived bridge.
- Primitive data vs derived API: the primitive inputs are the normals `b` and thresholds `β`,
  together with linearity of each map `x ↦ ⟪x, b i⟫ₚ`; the recession-cone equality is derived API
  on the canonical feasible-region owner.
- Layer target: the main theorem is `core/canonical`, and the displayed half-space intersection is
  retained only as a thin `bridge/view` corollary.
-/

namespace LinearConstraintRelation

/-- Corollary 8.1.2, primitive owner form: if the feasible region of the `.ge` linear constraints
`β i ≤ ⟪x, b i⟫ₚ` is nonempty and each indexed pairing evaluation is linear in `x`, then its
recession cone `0⁺ C` is exactly the corresponding homogeneous `.ge` feasible region. -/
-- Proof sketch: choose `x ∈ C` from the nonemptiness hypothesis. For the forward inclusion,
-- apply the defining property of `recessionCone` to `x + a • y ∈ C`, compare the inequalities
-- with those for `x`, and divide by `a ≥ 0` to get `0 ≤ ⟪y, b i⟫ₚ`. For the reverse inclusion,
-- use the owner definition of `recessionCone`: a homogeneous feasible direction stays feasible
-- after nonnegative scaling, and then adding that scaled direction preserves every `.ge`
-- constraint.
theorem recessionCone_geFeasible_eq_homogeneousGeFeasibleSet_of_forall_isLinear
    (b : I → Y) (β : I → 𝕜)
    (hlin : ∀ i, IsLinearMap 𝕜 (((fun x : X ↦ ⟪x, b i⟫ₚ) : X → 𝕜)))
    (hC : (geFeasible b β : Set X).Nonempty) :
    0⁺[𝕜] (geFeasible b β : Set X) = (homogeneousGeFeasibleSet 𝕜 b : Set X) := by
  let C : Set X := geFeasible b β
  let K : Set X := homogeneousGeFeasibleSet 𝕜 b
  have pairing_add (i : I) (x y : X) :
      (⟪x + y, b i⟫ₚ : 𝕜) = ⟪x, b i⟫ₚ + ⟪y, b i⟫ₚ :=
    (hlin i).map_add x y
  have pairing_smul (i : I) (a : 𝕜) (x : X) :
      (⟪a • x, b i⟫ₚ : 𝕜) = a * ⟪x, b i⟫ₚ := by
    simpa [smul_eq_mul] using (hlin i).map_smul a x
  obtain ⟨x, hx⟩ := hC
  have mem_C_iff (x : X) : x ∈ C ↔ ∀ i, β i ≤ ⟪x, b i⟫ₚ := by
    change x ∈ geFeasible b β ↔ ∀ i, β i ≤ ⟪x, b i⟫ₚ
    exact (mem_geFeasible (b := b) (β := β) (x := x))
  have mem_K_iff (y : X) : y ∈ K ↔ ∀ i, (0 : 𝕜) ≤ ⟪y, b i⟫ₚ := by
    change y ∈ homogeneousGeFeasibleSet 𝕜 b ↔ ∀ i, (0 : 𝕜) ≤ ⟪y, b i⟫ₚ
    exact (mem_homogeneousGeFeasibleSet (𝕜 := 𝕜) (b := b) (x := y))
  have hx : x ∈ C := by
    simpa [C] using hx
  have hx' : ∀ i, β i ≤ ⟪x, b i⟫ₚ := (mem_C_iff x).mp hx
  have mem_K_of_mem_recession {y : X} (hy : y ∈ 0⁺[𝕜] C) : y ∈ K := by
    rw [mem_K_iff]
    rw [Set.mem_recessionCone_iff] at hy
    intro i
    have hxi : β i ≤ ⟪x, b i⟫ₚ := hx' i
    by_contra hyi
    have hyi_lt : ⟪y, b i⟫ₚ < (0 : 𝕜) := lt_of_not_ge hyi
    let a : 𝕜 := (⟪x, b i⟫ₚ - β i + 1) / (-⟪y, b i⟫ₚ)
    have ha : 0 ≤ a := by
      have hnum : 0 ≤ ⟪x, b i⟫ₚ - β i + 1 := by
        linarith
      have hden : (0 : 𝕜) ≤ -⟪y, b i⟫ₚ := by
        linarith
      exact div_nonneg hnum hden
    have hxy : β i ≤ ⟪x, b i⟫ₚ + a * ⟪y, b i⟫ₚ := by
      have hxy : x + a • y ∈ C := hy x hx a ha
      have hxy' : β i ≤ ⟪x + a • y, b i⟫ₚ := (mem_C_iff (x + a • y)).mp hxy i
      simpa [pairing_add i x (a • y), pairing_smul i a y] using hxy'
    have ha_mul : a * ⟪y, b i⟫ₚ = -(⟪x, b i⟫ₚ - β i + 1) := by
      dsimp [a]
      have hyi_ne : (⟪y, b i⟫ₚ : 𝕜) ≠ 0 := by
        linarith
      have hqq : (⟪y, b i⟫ₚ : 𝕜) * (⟪y, b i⟫ₚ : 𝕜)⁻¹ = 1 := by
        field_simp [hyi_ne]
      calc
        ((⟪x, b i⟫ₚ - β i + 1) / (-⟪y, b i⟫ₚ)) * ⟪y, b i⟫ₚ
            = -((⟪x, b i⟫ₚ - β i + 1) * (⟪y, b i⟫ₚ * (⟪y, b i⟫ₚ)⁻¹)) := by
                ring_nf
        _ = -((⟪x, b i⟫ₚ - β i + 1) * 1) := by rw [hqq]
        _ = -(⟪x, b i⟫ₚ - β i + 1) := by ring
    linarith
  have smul_mem_K {a : 𝕜} {y : X} (hy : y ∈ K) (ha : 0 ≤ a) : a • y ∈ K := by
    rw [mem_K_iff] at hy ⊢
    intro i
    have hai : (0 : 𝕜) ≤ a * ⟪y, b i⟫ₚ := mul_nonneg ha (hy i)
    simpa [pairing_smul i a y] using hai
  have add_mem_C {y z : X} (hy : y ∈ C) (hz : z ∈ K) : y + z ∈ C := by
    rw [mem_C_iff] at hy ⊢
    intro i
    have hyi : β i ≤ ⟪y, b i⟫ₚ := hy i
    have hzi : (0 : 𝕜) ≤ ⟪z, b i⟫ₚ := (mem_K_iff z).mp hz i
    have hyz : β i ≤ ⟪y, b i⟫ₚ + ⟪z, b i⟫ₚ := by
      linarith
    simpa [pairing_add i y z] using hyz
  ext y
  constructor
  · intro hy
    change y ∈ 0⁺[𝕜] C at hy
    change y ∈ K
    exact mem_K_of_mem_recession hy
  · intro hy
    change y ∈ K at hy
    change y ∈ 0⁺[𝕜] C
    rw [Set.mem_recessionCone_iff]
    intro z hz a ha
    exact add_mem_C hz (smul_mem_K hy ha)

end LinearConstraintRelation

/-- Corollary 8.1.2 in the textbook pointwise form: if the feasible region
`{x | ∀ i, β i ≤ ⟪x, b i⟫ₚ}` is nonempty and each indexed pairing evaluation is linear in `x`,
then its recession cone is exactly the homogeneous feasible region
`{y | ∀ i, 0 ≤ ⟪y, b i⟫ₚ}`. -/
theorem recessionCone_setOf_forall_ge_eq_setOf_forall_nonneg_of_forall_isLinear
    (b : I → Y) (β : I → 𝕜)
    (hlin : ∀ i, IsLinearMap 𝕜 (((fun x : X ↦ ⟪x, b i⟫ₚ) : X → 𝕜)))
    (hC : ({x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ}).Nonempty) :
    0⁺[𝕜] ({x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ}) =
      {y : X | ∀ i, (0 : 𝕜) ≤ ⟪y, b i⟫ₚ} := by
  have hβ :
      (LinearConstraintRelation.geFeasible b β : Set X) =
        {x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ} := by
    simpa using (LinearConstraintRelation.geFeasible_eq_setOf (b := b) (β := β))
  have h0 :
      (LinearConstraintRelation.homogeneousGeFeasibleSet 𝕜 b : Set X) =
        {y : X | ∀ i, (0 : 𝕜) ≤ ⟪y, b i⟫ₚ} := by
    simpa using
      (LinearConstraintRelation.homogeneousGeFeasibleSet_eq_setOf
        (𝕜 := 𝕜) (b := b))
  have hC' :
      (LinearConstraintRelation.geFeasible b β : Set X).Nonempty := by
    rw [hβ]
    exact hC
  have hrec :
      0⁺[𝕜] (LinearConstraintRelation.geFeasible b β : Set X) =
        (LinearConstraintRelation.homogeneousGeFeasibleSet 𝕜 b : Set X) :=
    LinearConstraintRelation.recessionCone_geFeasible_eq_homogeneousGeFeasibleSet_of_forall_isLinear
      (X := X) (b := b) (β := β) hlin hC'
  calc
    0⁺[𝕜] ({x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ}) =
        0⁺[𝕜] (LinearConstraintRelation.geFeasible b β : Set X) := by
      rw [← hβ]
    _ = (LinearConstraintRelation.homogeneousGeFeasibleSet 𝕜 b : Set X) := hrec
    _ = {y : X | ∀ i, (0 : 𝕜) ≤ ⟪y, b i⟫ₚ} := h0

end

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort*}

namespace LinearConstraintRelation

/-- Corollary 8.1.2, bridge owner form under a linear pairing owner. -/
theorem recessionCone_geFeasible_eq_homogeneousGeFeasibleSet
    (b : I → Y) (β : I → 𝕜)
    (hC : (geFeasible b β : Set X).Nonempty) :
    0⁺[𝕜] (geFeasible b β : Set X) = (homogeneousGeFeasibleSet 𝕜 b : Set X) := by
  exact recessionCone_geFeasible_eq_homogeneousGeFeasibleSet_of_forall_isLinear
    (X := X) (b := b) (β := β)
    (hlin := fun i ↦ HasLinearPairing.isLinear_pairing_left (b i)) hC

end LinearConstraintRelation

/-- Corollary 8.1.2 in the textbook pointwise form under a linear pairing owner. -/
theorem recessionCone_setOf_forall_ge_eq_setOf_forall_nonneg
    (b : I → Y) (β : I → 𝕜)
    (hC : ({x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ}).Nonempty) :
    0⁺[𝕜] ({x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ}) =
      {y : X | ∀ i, (0 : 𝕜) ≤ ⟪y, b i⟫ₚ} := by
  exact recessionCone_setOf_forall_ge_eq_setOf_forall_nonneg_of_forall_isLinear
    (X := X) (b := b) (β := β)
    (hlin := fun i ↦ HasLinearPairing.isLinear_pairing_left (b i)) hC

end
