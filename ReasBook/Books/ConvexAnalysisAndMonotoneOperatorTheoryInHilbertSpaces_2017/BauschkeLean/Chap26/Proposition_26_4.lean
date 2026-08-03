import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.LpEquiv
import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap08.Proposition_8_17
import BauschkeLean.Chap20.Definition_20_20
import BauschkeLean.Chap23.Proposition_23_18

-- Semantic recall: `lean_leansearch` only surfaced generic orthogonal-projection results here, so
-- this file follows the verified local Chapter 23 owners `SetValuedOperator.familyOperator` and
-- `J[...]`, together with the Chapter 6 normal-cone owner notation `N[C]` and submodule
-- `starProjection`.

open scoped BigOperators InnerProductSpace Pointwise Set SetValuedOperator
open SetValuedOperator
open ERealFunction

universe u

noncomputable section

section Helpers

variable {m : ℕ}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "ProductSpace" => lp (fun _ : Fin m ↦ H) 2

/-- The coordinate projection from the `m`-fold Hilbert direct sum to its `i`-th factor. -/
def coordinateCLM (i : Fin m) : ProductSpace →L[ℝ] H where
  toLinearMap :=
    { toFun := fun z ↦ z i
      map_add' := by
        intro z w
        rfl
      map_smul' := by
        intro a z
        rfl }
  cont := by
    refine (LipschitzWith.mk_one ?_).continuous
    intro z w
    simpa [dist_eq_norm] using
      (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (z - w) i)

@[simp] theorem coordinateCLM_apply (i : Fin m) (z : ProductSpace) :
    coordinateCLM i z = z i :=
  rfl

/-- The constant family `(x, ..., x)` in the `m`-fold Hilbert direct sum. -/
def diagonalPoint (x : H) : ProductSpace :=
  (lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ).symm (WithLp.toLp 2 fun _ : Fin m ↦ x)

/-- Helper for Proposition 26.4: package a coordinate family as a point of the finite Hilbert
product `ProductSpace`. -/
def lpFamily (w : Fin m → H) : ProductSpace :=
  (lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ).symm (WithLp.toLp 2 w)

/-- Helper for Proposition 26.4: the coordinates of `lpFamily w` are exactly `w`. -/
@[simp] theorem lpFamily_apply (w : Fin m → H) (i : Fin m) :
    lpFamily w i = w i := by
  -- Unfold the canonical `lp`/`PiLp` bridge once so later coordinate computations are stable.
  change (((lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ).symm (WithLp.toLp 2 w) : Fin m → H) i = w i)
  rw [coe_lpPiLpₗᵢ_symm]

/-- Every coordinate of `diagonalPoint x` is `x`. -/
@[simp] theorem diagonalPoint_apply (x : H) (i : Fin m) :
    diagonalPoint x i = x := by
  change
    (((lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ).symm
      (WithLp.toLp 2 fun _ : Fin m ↦ x) : Fin m → H) i = x)
  simpa using (congrFun (coe_lpPiLpₗᵢ_symm (WithLp.toLp 2 fun _ : Fin m ↦ x)) i)

/-- The diagonal submodule of the `m`-fold Hilbert direct sum consists of the constant families. -/
def diagonalSubmodule : Submodule ℝ ProductSpace where
  carrier := {x | ∀ i j : Fin m, x i = x j}
  zero_mem' := by
    intro i j
    rfl
  add_mem' := by
    intro x y hx hy i j
    calc
      (x + y) i = x i + y i := rfl
      _ = x j + y j := by rw [hx i j, hy i j]
      _ = (x + y) j := rfl
  smul_mem' := by
    intro a x hx i j
    calc
      (a • x) i = a • x i := rfl
      _ = a • x j := by rw [hx i j]
      _ = (a • x) j := rfl

/-- Membership in `diagonalSubmodule` is equivalent to pairwise coordinate equality. -/
theorem mem_diagonalSubmodule_iff (x : ProductSpace) :
    x ∈ (diagonalSubmodule : Submodule ℝ ProductSpace) ↔ ∀ i j : Fin m, x i = x j :=
  Iff.rfl

/-- Helper for Proposition 26.4: every diagonal point belongs to the diagonal submodule. -/
@[simp] theorem diagonalPoint_mem_diagonalSubmodule (x : H) :
    diagonalPoint x ∈ (diagonalSubmodule : Submodule ℝ ProductSpace) := by
  -- A constant family has equal coordinates by construction.
  rw [mem_diagonalSubmodule_iff]
  intro i j
  simp

/-
The next two additive helper lemmas only use the additive structure on `H`, so we omit the
ambient inner-product instance to avoid unused-section-variable warnings.
-/
omit [InnerProductSpace ℝ H] in
/-- The coordinate sum of the zero family is `0`. -/
private theorem sum_eq_zero_zero_family :
    (∑ i, (0 : ProductSpace) i) = (0 : H) := by
  -- The finite coordinate sum of the zero family is zero.
  change ∑ i : Fin m, (0 : H) = 0
  simp

omit [InnerProductSpace ℝ H] in
/-- Adding two zero-coordinate-sum families preserves the zero coordinate sum. -/
private theorem sum_eq_zero_add
    {u v : ProductSpace} (hu : (∑ i, u i) = (0 : H)) (hv : (∑ i, v i) = (0 : H)) :
    (∑ i, (u + v) i) = (0 : H) := by
  -- Coordinate sums turn pointwise addition into addition in `H`.
  change ∑ i : Fin m, (u i + v i) = 0
  calc
    ∑ i : Fin m, (u i + v i) = (∑ i : Fin m, u i) + ∑ i : Fin m, v i := by
      rw [Finset.sum_add_distrib]
    _ = 0 := by
      simp [hu, hv]

/-- Scalar multiples preserve the zero coordinate sum. -/
private theorem sum_eq_zero_smul
    (a : ℝ) {u : ProductSpace} (hu : (∑ i, u i) = (0 : H)) :
    (∑ i, (a • u) i) = (0 : H) := by
  -- Coordinate sums commute with scalar multiplication.
  change ∑ i : Fin m, a • u i = 0
  calc
    ∑ i : Fin m, a • u i = a • ∑ i : Fin m, u i := by
      rw [Finset.smul_sum]
    _ = 0 := by
      simp [hu]

/-- The sum-zero submodule of the `m`-fold Hilbert direct sum. -/
def sumZeroSubmodule : Submodule ℝ ProductSpace where
  carrier := {u : ProductSpace | ∑ i, u i = 0}
  zero_mem' := sum_eq_zero_zero_family
  add_mem' := by
    intro u v hu hv
    exact sum_eq_zero_add hu hv
  smul_mem' := by
    intro a u hu
    exact sum_eq_zero_smul a hu

end Helpers

section Proposition264

variable {m : ℕ}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "ProductSpace" => lp (fun _ : Fin m ↦ H) 2
local notation "DiagonalSet" =>
  (((diagonalSubmodule : Submodule ℝ ProductSpace) : Set ProductSpace))

/-- The diagonal submodule is closed because it is the intersection of the coordinate equalizers
`{x | x i = x j}`. -/
theorem isClosed_diagonalSubmodule :
    IsClosed ((diagonalSubmodule : Submodule ℝ ProductSpace) : Set ProductSpace) := by
  rw [show ((diagonalSubmodule : Submodule ℝ ProductSpace) : Set ProductSpace) =
      ⋂ i : Fin m, ⋂ j : Fin m, {x : ProductSpace | x i = x j} by
      ext x
      simp [mem_diagonalSubmodule_iff]]
  refine isClosed_iInter fun i ↦ ?_
  refine isClosed_iInter fun j ↦ ?_
  have hcont_i : Continuous fun x : ProductSpace ↦ x i := by
    refine (LipschitzWith.mk_one ?_).continuous
    intro x y
    simpa [dist_eq_norm] using
      (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (x - y) i)
  have hcont_j : Continuous fun x : ProductSpace ↦ x j := by
    refine (LipschitzWith.mk_one ?_).continuous
    intro x y
    simpa [dist_eq_norm] using
      (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (x - y) j)
  exact isClosed_eq
    hcont_i
    hcont_j

/-- Helper for Proposition 26.4: on a submodule, the normal-cone support inequality is equivalent
to orthogonality. -/
private theorem innerSupremumOn_le_zero_iff_mem_orthogonal_of_submodule
    (V : Submodule ℝ ProductSpace) {u : ProductSpace} :
    innerSupremumOn (V : Set ProductSpace) u ≤ 0 ↔ u ∈ Vᗮ := by
  constructor
  · intro hu
    -- Compare against the singleton `{0}` so that the support inequality becomes pointwise.
    have hsep : innerSupremumOn (V : Set ProductSpace) u ≤
        innerInfimumOn ({0} : Set ProductSpace) u := by
      simpa using hu
    have hpoint :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (V : Set ProductSpace) ({0} : Set ProductSpace) u).mp hsep
    rw [V.mem_orthogonal u]
    intro v hv
    have h_nonpos : ⟪v, u⟫_ℝ ≤ 0 := by
      simpa using hpoint v hv 0 (by simp)
    have h_neg_nonpos : ⟪-v, u⟫_ℝ ≤ 0 := by
      simpa using hpoint (-v) (V.neg_mem hv) 0 (by simp)
    have h_nonneg : 0 ≤ ⟪v, u⟫_ℝ := by
      simpa [inner_neg_left] using h_neg_nonpos
    linarith
  · intro hu
    -- Orthogonality forces every support value on the submodule to equal the value at `0`.
    have hpoint : ∀ v ∈ (V : Set ProductSpace), ∀ z ∈ ({0} : Set ProductSpace),
        ⟪v, u⟫_ℝ ≤ ⟪z, u⟫_ℝ := by
      intro v hv z hz
      have hz0 : z = 0 := by
        simpa using hz
      subst z
      have h_zero : ⟪v, u⟫_ℝ = 0 := (V.mem_orthogonal u).mp hu v hv
      simp [h_zero]
    have hsep : innerSupremumOn (V : Set ProductSpace) u ≤
        innerInfimumOn ({0} : Set ProductSpace) u :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (V : Set ProductSpace) ({0} : Set ProductSpace) u).mpr hpoint
    simpa using hsep

/-- Helper for Proposition 26.4: translating the diagonal submodule by a diagonal point returns
the diagonal submodule itself. -/
private theorem diagonalSubmodule_sub_singleton_eq_self {x : ProductSpace}
    (hx : x ∈ (diagonalSubmodule : Submodule ℝ ProductSpace)) :
    DiagonalSet - ({x} : Set ProductSpace) =
      ((diagonalSubmodule : Submodule ℝ ProductSpace) : Set ProductSpace) := by
  -- Reinterpret the diagonal submodule as an affine subspace and invoke its translate API.
  simpa [vsub_eq_sub, Submodule.toAffineSubspace_direction] using
    (AffineSubspace.coe_direction_eq_vsub_set_right
      (s := (diagonalSubmodule : Submodule ℝ ProductSpace).toAffineSubspace)
      ((Submodule.mem_toAffineSubspace).2 hx)).symm

/-- Helper for Proposition 26.4: the coordinate sum of `diagonalPoint x` is `(m : ℝ) • x`. -/
theorem sum_diagonalPoint (x : H) :
    ∑ i : Fin m, diagonalPoint x i = (m : ℝ) • x := by
  -- The diagonal family is constant, so its finite sum is `m` copies of `x`.
  induction m with
  | zero =>
      simp [diagonalPoint]
  | succ m hm =>
      have hm' : ∑ i : Fin m, diagonalPoint x i.succ = (m : ℝ) • x := by
        simpa using hm
      calc
        ∑ i : Fin (m + 1), diagonalPoint x i =
            diagonalPoint x 0 + ∑ i : Fin m, diagonalPoint x i.succ := by
          rw [Fin.sum_univ_succ]
        _ = x + (m : ℝ) • x := by
          rw [diagonalPoint_apply]
          exact congrArg (fun t : H ↦ x + t) hm'
        _ = ((m + 1 : ℕ) : ℝ) • x := by
          simp [add_smul, add_comm]

/-- Helper for Proposition 26.4: pairing a diagonal point with `u` is the same as pairing `x`
with the coordinate sum of `u`. -/
theorem inner_diagonalPoint_eq_inner_sum (x : H) (u : ProductSpace) :
    ⟪diagonalPoint x, u⟫_ℝ = ⟪x, ∑ i : Fin m, u i⟫_ℝ := by
  -- Rewrite the product-space inner product coordinatewise, then reassemble the sum in `H`.
  calc
    ⟪diagonalPoint x, u⟫_ℝ
        = ⟪lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ (diagonalPoint x),
            lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ u⟫_ℝ := by
          symm
          exact (lpPiLpₗᵢ (fun _ : Fin m ↦ H) ℝ).inner_map_map (diagonalPoint x) u
    _ = ∑ i : Fin m, ⟪x, u i⟫_ℝ := by
      rw [PiLp.inner_apply]
      simp [coe_lpPiLpₗᵢ]
    _ = ⟪x, ∑ i : Fin m, u i⟫_ℝ := by
      symm
      rw [inner_sum]

/-- Helper for Proposition 26.4: any element of the diagonal submodule is a diagonal point. -/
theorem exists_eq_diagonalPoint_of_mem_diagonalSubmodule
    (z : ProductSpace) (hz : z ∈ (diagonalSubmodule : Submodule ℝ ProductSpace)) :
    ∃ x : H, z = diagonalPoint x := by
  by_cases hm : m = 0
  · -- On `Fin 0`, the whole product space is a subsingleton, so every point is diagonal.
    subst hm
    refine ⟨0, ?_⟩
    exact Subsingleton.elim _ _
  · -- Otherwise pick one coordinate and use diagonality to show all coordinates match it.
    let i0 : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
    refine ⟨z i0, ?_⟩
    ext i
    have hconst := (mem_diagonalSubmodule_iff z).1 hz i i0
    simpa [diagonalPoint_apply] using hconst

/-- Clause (1) of Proposition 26.4: in the `m`-fold Hilbert direct sum, the orthogonal
complement of the diagonal submodule is exactly the submodule of families whose coordinates
sum to `0`. -/
theorem diagonalSubmodule_orthogonal_eq_sumZeroSubmodule :
    (((diagonalSubmodule : Submodule ℝ ProductSpace)ᗮ : Submodule ℝ ProductSpace)) =
      sumZeroSubmodule := by
  ext u
  constructor
  · intro hu
    change ∑ i, u i = (0 : H)
    -- Test orthogonality against the diagonal point built from the coordinate sum itself.
    have horth :=
      ((diagonalSubmodule : Submodule ℝ ProductSpace).mem_orthogonal' u).1 hu
        (diagonalPoint (∑ i, u i))
        (diagonalPoint_mem_diagonalSubmodule (m := m) (H := H) (∑ i, u i))
    have horth' : ⟪diagonalPoint (∑ i, u i), u⟫_ℝ = 0 := by
      simpa [real_inner_comm] using horth
    have hself : ⟪∑ i, u i, ∑ i, u i⟫_ℝ = 0 := by
      simpa [inner_diagonalPoint_eq_inner_sum] using horth'
    exact inner_self_eq_zero.mp hself
  · intro hu
    -- A zero coordinate sum annihilates every diagonal point, hence every element of `D`.
    rw [Submodule.mem_orthogonal']
    intro v hv
    rcases exists_eq_diagonalPoint_of_mem_diagonalSubmodule (m := m) (H := H) v hv with ⟨x, rfl⟩
    have hdiag : ⟪diagonalPoint x, u⟫_ℝ = 0 := by
      rw [inner_diagonalPoint_eq_inner_sum, hu, inner_zero_right]
    simpa [real_inner_comm] using hdiag

/-- Clause (2) of Proposition 26.4: the normal cone to the diagonal submodule is the
orthogonal-complement fiber when `x` lies on the diagonal and is empty otherwise. -/
theorem normalCone_diagonalSubmodule_eq_orthogonal_or_empty
    (x : ProductSpace) :
    N[DiagonalSet] x =
      (by
        classical
        exact
          if x ∈ (diagonalSubmodule : Submodule ℝ ProductSpace) then
            ((((diagonalSubmodule : Submodule ℝ ProductSpace)ᗮ :
                Submodule ℝ ProductSpace) : Set ProductSpace))
          else
            ∅) := by
  classical
  by_cases hx : x ∈ (diagonalSubmodule : Submodule ℝ ProductSpace)
  · -- On the diagonal, rewrite the translate `D - x` as `D` and read the support inequality.
    rw [if_pos hx, Set.normalCone_of_mem hx, diagonalSubmodule_sub_singleton_eq_self (m := m) hx]
    ext u
    exact
      innerSupremumOn_le_zero_iff_mem_orthogonal_of_submodule
        (V := (diagonalSubmodule : Submodule ℝ ProductSpace)) (u := u)
  · -- Away from the diagonal, the normal cone is empty by definition.
    rw [if_neg hx]
    simpa using Set.normalCone_of_not_mem hx

section Projection

variable [CompleteSpace H]

/-- The diagonal submodule of a finite Hilbert product admits an orthogonal projection. -/
instance diagonalSubmodule_hasOrthogonalProjection :
    (diagonalSubmodule : Submodule ℝ ProductSpace).HasOrthogonalProjection := by
  letI : CompleteSpace (diagonalSubmodule : Submodule ℝ ProductSpace) :=
    isClosed_diagonalSubmodule.completeSpace_coe
  exact inferInstance

/-- Clause (3) of Proposition 26.4: the orthogonal projection onto the diagonal submodule is
the constant family with value `(m : ℝ)⁻¹ • ∑ i, x i`. -/
theorem starProjection_diagonalSubmodule_eq_diagonalPoint_average
    (x : ProductSpace) :
    diagonalSubmodule.starProjection x =
      diagonalPoint ((m : ℝ)⁻¹ • ∑ i, x i) := by
  let p : ProductSpace := diagonalPoint ((m : ℝ)⁻¹ • ∑ i, x i)
  have hp_mem : p ∈ (diagonalSubmodule : Submodule ℝ ProductSpace) := by
    -- The candidate projection is visibly diagonal.
    change diagonalPoint ((m : ℝ)⁻¹ • ∑ i, x i) ∈
      (diagonalSubmodule : Submodule ℝ ProductSpace)
    simp
  have hsum_p : ∑ i, p i = ∑ i, x i := by
    -- The coordinate sum of the diagonal average recovers the original total sum.
    calc
      ∑ i, p i = (m : ℝ) • ((m : ℝ)⁻¹ • ∑ i, x i) := by
        simpa [p] using sum_diagonalPoint (m := m) (H := H) ((m : ℝ)⁻¹ • ∑ i, x i)
      _ = ∑ i, x i := by
        by_cases hm : m = 0
        · subst hm
          simp
        · simp [smul_smul, Nat.cast_ne_zero.mpr hm]
  have hres_orth :
      x - p ∈ (((diagonalSubmodule : Submodule ℝ ProductSpace)ᗮ :
        Submodule ℝ ProductSpace)) := by
    -- The residual has zero coordinate sum, so clause (i) places it in `Dᗮ`.
    have hres_sum : ∑ i, (x - p) i = (0 : H) := by
      change ∑ i : Fin m, (x i - p i) = 0
      calc
        ∑ i : Fin m, (x i - p i) = ∑ i, x i - ∑ i, p i := by
          rw [Finset.sum_sub_distrib]
        _ = 0 := by
          exact sub_eq_zero.mpr hsum_p.symm
    have hsumZero : x - p ∈ sumZeroSubmodule := by
      simpa [sumZeroSubmodule] using hres_sum
    simpa [diagonalSubmodule_orthogonal_eq_sumZeroSubmodule] using hsumZero
  -- Uniqueness of orthogonal projection identifies the diagonal average as `P_D x`.
  simpa [p] using
    (diagonalSubmodule : Submodule ℝ ProductSpace).eq_starProjection_of_mem_orthogonal
      hp_mem hres_orth

/-- Clause (4) of Proposition 26.4: the orthogonal projection onto the orthogonal complement of the
diagonal submodule subtracts the diagonal average from each coordinate. -/
theorem starProjection_orthogonal_diagonalSubmodule_eq_sub_diagonalPoint_average
    (x : ProductSpace) :
    ((((diagonalSubmodule : Submodule ℝ ProductSpace)ᗮ :
        Submodule ℝ ProductSpace)).starProjection x) =
      x - diagonalPoint ((m : ℝ)⁻¹ • ∑ i, x i) := by
  -- The orthogonal-complement projection is the residual after subtracting `P_D x`.
  rw [((diagonalSubmodule : Submodule ℝ ProductSpace).starProjection_orthogonal_val x)]
  simp [starProjection_diagonalSubmodule_eq_diagonalPoint_average]

end Projection

namespace SetValuedOperator

/-- Helper for Proposition 26.4: membership in `zer (∑ i, A i)` is equivalent to the existence
of a coordinate witness family whose sum is `0`. -/
theorem mem_zeros_sum_iff_exists_coordinateWitness
    (A : Fin m → SetValuedOperator H H) (x : H) :
    x ∈ (∑ i, A i).zeros ↔
      ∃ u : ProductSpace, (∀ i, u i ∈ A i x) ∧ ∑ i, u i = 0 := by
  constructor
  · intro hx
    -- Expand `zer` into `0 ∈ ∑ i, A i x`, then package the coordinate witnesses in `lp`.
    rw [SetValuedOperator.mem_zeros_iff] at hx
    have hx' : (0 : H) ∈ ∑ i : Fin m, A i x := by
      simpa using hx
    rcases (Set.mem_fintype_sum (f := fun i : Fin m ↦ A i x) (a := (0 : H))).1 hx' with
      ⟨w, hw, hsum⟩
    refine ⟨lpFamily w, ?_, ?_⟩
    · intro i
      simpa using hw i
    · simpa using hsum
  · rintro ⟨u, hu, hsum⟩
    -- Read the `lp` witness back coordinatewise and rebuild membership in the set sum.
    rw [SetValuedOperator.mem_zeros_iff]
    have hx' : (0 : H) ∈ ∑ i : Fin m, A i x :=
      (Set.mem_fintype_sum (f := fun i : Fin m ↦ A i x) (a := (0 : H))).2
        ⟨fun i ↦ u i, hu, by simpa using hsum⟩
    simpa using hx'

section RecalledProposition2318

variable [CompleteSpace H]

/- Proposition 26.4 (5): this is exactly Proposition 23.18 (1) specialized to the constant family
`K i = H` over `Fin m`. -/
#check
  (SetValuedOperator.familyOperator_maximal_of_maximal :
    ∀ A : Fin m → SetValuedOperator H H,
      (∀ i, Maximal IsMonotone (A i)) → Maximal IsMonotone (familyOperator A))

/- Proposition 26.4 (6): apply Proposition 23.18 (2) to the scaled family
`i ↦ (γ : ℝ) • A i`; the remaining step is the canonical identification of the scaled product
operator with the product of the scaled coordinate operators. -/
#check
  (SetValuedOperator.resolvent_familyOperator_eq_familyOperator_resolvent :
    ∀ A : Fin m → SetValuedOperator H H,
      J[(familyOperator A)] = familyOperator (fun i ↦ J[(A i)]))

end RecalledProposition2318

/-- Clause (7) of Proposition 26.4: the diagonal image of the zero set of the operator sum
`∑ i, A i` coincides with the zero set of the product-space operator `N_D + A`. -/
theorem diagonalPoint_image_zeros_sum_eq_zeros_normalCone_add_familyOperator
    (A : Fin m → SetValuedOperator H H) :
    diagonalPoint '' (∑ i, A i).zeros =
      (N[DiagonalSet] +
        familyOperator A).zeros := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- A zero of the coordinate sum provides an orthogonal normal vector and a family witness.
    rw [mem_zeros_sum_iff_exists_coordinateWitness] at hx
    rcases hx with ⟨u, huA, hu0⟩
    rw [SetValuedOperator.mem_zeros_iff]
    change (0 : ProductSpace) ∈
      N[DiagonalSet] (diagonalPoint x) + familyOperator A (diagonalPoint x)
    rw [Set.mem_add]
    refine ⟨-u, ?_, u, ?_, by simp⟩
    · rw [normalCone_diagonalSubmodule_eq_orthogonal_or_empty]
      rw [if_pos (diagonalPoint_mem_diagonalSubmodule (m := m) (H := H) x)]
      have huSumZero : u ∈ sumZeroSubmodule := by
        simpa [sumZeroSubmodule] using hu0
      have huOrth :
          u ∈ (((diagonalSubmodule : Submodule ℝ ProductSpace)ᗮ :
            Submodule ℝ ProductSpace)) := by
        simpa [diagonalSubmodule_orthogonal_eq_sumZeroSubmodule] using huSumZero
      have huOrth' :
          ∀ w ∈ (diagonalSubmodule : Submodule ℝ ProductSpace), ⟪u, w⟫_ℝ = 0 :=
        ((diagonalSubmodule : Submodule ℝ ProductSpace).mem_orthogonal' u).1 huOrth
      intro w hw
      simpa [real_inner_comm] using huOrth' w hw
    · rw [mem_familyOperator_iff]
      intro i
      simpa using huA i
  · intro hz
    -- Any zero of `N_D + A` must already lie on the diagonal because otherwise `N_D z = ∅`.
    rw [SetValuedOperator.mem_zeros_iff] at hz
    change (0 : ProductSpace) ∈ N[DiagonalSet] z + familyOperator A z at hz
    rw [Set.mem_add] at hz
    rcases hz with ⟨v, hvN, u, huA, hvu⟩
    have hzDiag : z ∈ (diagonalSubmodule : Submodule ℝ ProductSpace) := by
      by_contra hzNot
      rw [normalCone_diagonalSubmodule_eq_orthogonal_or_empty] at hvN
      simp [hzNot] at hvN
    rcases exists_eq_diagonalPoint_of_mem_diagonalSubmodule (m := m) (H := H) z hzDiag with
      ⟨x, rfl⟩
    have huOrth :
        u ∈ (((diagonalSubmodule : Submodule ℝ ProductSpace)ᗮ :
          Submodule ℝ ProductSpace)) := by
      -- The family witness is the negative of the normal vector because their sum is zero.
      have hvOrth :
          ∀ w ∈ (diagonalSubmodule : Submodule ℝ ProductSpace), ⟪v, w⟫_ℝ = 0 := by
        rw [normalCone_diagonalSubmodule_eq_orthogonal_or_empty] at hvN
        simpa [diagonalPoint_mem_diagonalSubmodule, Submodule.mem_orthogonal'] using hvN
      have hu_eq : u = -v := by
        exact eq_neg_of_add_eq_zero_right hvu
      rw [Submodule.mem_orthogonal']
      intro w hw
      have hvw : ⟪v, w⟫_ℝ = 0 := hvOrth w hw
      simpa [hu_eq, inner_neg_left] using hvw
    have hxzero : x ∈ (∑ i, A i).zeros := by
      rw [mem_zeros_sum_iff_exists_coordinateWitness]
      refine ⟨u, ?_, ?_⟩
      · have huFamily := (mem_familyOperator_iff A (diagonalPoint x) u).1 huA
        intro i
        simpa using huFamily i
      · have huSumZero : u ∈ sumZeroSubmodule := by
          simpa [diagonalSubmodule_orthogonal_eq_sumZeroSubmodule] using huOrth
        simpa [sumZeroSubmodule] using huSumZero
    exact ⟨x, hxzero, rfl⟩

/-- Proposition 26.4: clause (8) says that a point `x` solves `0 ∈ ∑ i, A i x` exactly when some
element of the orthogonal complement of the diagonal belongs to `A(j x)`. -/
theorem mem_zeros_sum_iff_exists_mem_familyOperator_diagonalPoint
    (A : Fin m → SetValuedOperator H H) (x : H) :
    x ∈ (∑ i, A i).zeros ↔
      ∃ u ∈ (((diagonalSubmodule : Submodule ℝ ProductSpace)ᗮ : Submodule ℝ ProductSpace)),
        u ∈ familyOperator A (diagonalPoint x) :=
      by
  -- Clause (viii) is the coordinate-witness formulation of clause (vii) with clause (i).
  rw [mem_zeros_sum_iff_exists_coordinateWitness]
  constructor
  · rintro ⟨u, hu, hsum⟩
    have huSumZero : u ∈ sumZeroSubmodule := by
      simpa [sumZeroSubmodule] using hsum
    refine ⟨u, ?_, ?_⟩
    · simpa [diagonalSubmodule_orthogonal_eq_sumZeroSubmodule] using huSumZero
    · rw [mem_familyOperator_iff]
      intro i
      simpa using hu i
  · rintro ⟨u, huOrth, huFamily⟩
    refine ⟨u, ?_, ?_⟩
    · have hu := (mem_familyOperator_iff A (diagonalPoint x) u).1 huFamily
      intro i
      simpa using hu i
    · have huSumZero : u ∈ sumZeroSubmodule := by
        simpa [diagonalSubmodule_orthogonal_eq_sumZeroSubmodule] using huOrth
      simpa [sumZeroSubmodule] using huSumZero

end SetValuedOperator

end Proposition264
