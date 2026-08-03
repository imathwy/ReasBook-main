import Mathlib
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap08.Definition_8_7
import BauschkeLean.Chap06.Fact_6_14
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap09.Example_9_22
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.Proposition_13_12
import BauschkeLean.Chap15.Corollary_15_31

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped EuclideanSpace InnerProductSpace Pointwise

universe u

namespace ERealFunction

section AttouchBrezisTheorem

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- Helper for Remark 15 4: a vector in `ℝ²` is determined by its two coordinates. -/
private theorem euclideanSpace_fin2_eq (x : ℝ²) :
    x = !₂[x 0, x 1] := by
  -- Coordinatewise extensionality reduces equality in `EuclideanSpace ℝ (Fin 2)` to two cases.
  ext i
  fin_cases i <;> simp

/-- The quadrant used in Remark 15.4(1). -/
private abbrev Q : Set ℝ² := {x : ℝ² | 0 ≤ x 0 ∧ 0 ≤ x 1}

/-- The vertical axis used in Remark 15.4(1). -/
private abbrev L : Set ℝ² := {x : ℝ² | x 0 = 0}

/-- The vertical nonnegative ray used in Remark 15.4(1). -/
private abbrev C : Set ℝ² := {x : ℝ² | x 0 = 0 ∧ 0 ≤ x 1}

/-- The closed lower half-space used in Remark 15.4(1). -/
private abbrev Rnonpos : Set ℝ² := {x : ℝ² | x 1 ≤ 0}

/-- The open lower half-space used in Remark 15.4(1). -/
private abbrev Rneg : Set ℝ² := {x : ℝ² | x 1 < 0}

/-- The first explicit function in Remark 15.4(1). -/
private noncomputable def fAB : ℝ² → EReal :=
  fun x : ℝ² ↦
    if x ∈ Q then
      (((-Real.sqrt (x 0 * x 1) : ℝ) : EReal))
    else
      ⊤

/-- The indicator of the vertical axis used as the second function in Remark 15.4(1). -/
private noncomputable def gAB : ℝ² → EReal := ((ι[L]).asEReal : ℝ² → EReal)

/-- Helper for Remark 15 4: the explicit sum `f + g` is the indicator of the vertical ray
`{(0,t) | 0 ≤ t}`. -/
private theorem sum_eq_indicator_vertical_ray :
    -- TODO: finish the source-faithful branch split by showing directly that
    -- `fAB x = 0` on `C`, `gAB x = ⊤` off `L`, and `fAB x = ⊤` off `Q`.
    fAB + gAB = (ι[C]).asEReal := by
  ext x
  by_cases hxC : x ∈ C
  · have hxL : x ∈ L := hxC.1
    have hxQ : x ∈ Q := by
      -- On the ray, the first coordinate is `0` and the second is nonnegative.
      refine ⟨?_, hxC.2⟩
      simpa [hxC.1]
    -- On `C`, both summands vanish, so the sum equals the indicator value `0`.
    simp [fAB, gAB, indicator_apply, hxC, hxL, hxQ, hxC.1]
  · by_cases hxL : x ∈ L
    · have hxQ : x ∉ Q := by
        -- Route correction: off `C` but on the axis, the only failure is the negative
        -- second coordinate, so `fAB` must already be `⊤`.
        intro hxQ
        exact hxC ⟨hxL, hxQ.2⟩
      simp [fAB, gAB, indicator_apply, hxC, hxL, hxQ]
    · by_cases hxQ : x ∈ Q
      · have hf_ne_bot : fAB x ≠ ⊥ := by
          -- The quadrant branch is a real value, hence never `⊥`.
          simp [fAB, hxQ]
        have hg_top : gAB x = ⊤ := by
          -- Off the axis, the indicator of `L` contributes `⊤`.
          simp [gAB, indicator_apply, hxL]
        -- The non-bottom value of `fAB` absorbs the `⊤` from `gAB`, matching the target.
        change fAB x + gAB x = (ι[C]).asEReal x
        rw [hg_top, EReal.add_top_of_ne_bot hf_ne_bot]
        simp [indicator_apply, hxC]
      · simp [fAB, gAB, indicator_apply, hxC, hxL, hxQ]

/-- Helper for Remark 15 4: the vertical ray is a cone in the textbook sense. -/
private theorem vertical_ray_isCone :
    IsCone C := by
  rw [isCone_iff]
  ext x
  constructor
  · intro hx
    -- The unit scalar writes every point of the ray as a positive multiple of itself.
    exact Set.mem_smul.mpr ⟨1, by simp, x, hx, by simp⟩
  · rintro ⟨a, ha, y, hy, rfl⟩
    -- Positive scaling preserves both the vertical-axis equation and second-coordinate
    -- nonnegativity.
    refine ⟨by simpa [hy.1], ?_⟩
    simpa [C, Pi.smul_apply] using mul_nonneg ha.le hy.2

/-- Helper for Remark 15 4: the polar cone of the vertical ray is the closed lower half-space. -/
private theorem vertical_ray_polarCone_eq_nonpositive_halfspace :
    Set.polarCone C = Rnonpos := by
  ext u
  constructor
  · intro hu
    rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hu
    -- Testing the polar inequality on the unit vertical vector isolates the second coordinate.
    have htest : ⟪!₂[(0 : ℝ), 1], u⟫_ℝ ≤ 0 := by
      exact hu !₂[(0 : ℝ), 1] (by simp [C])
    have hcoord : ⟪!₂[(0 : ℝ), 1], u⟫_ℝ = u 1 := by
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      simp
      have hinner : ⟪(1 : ℝ), u 1⟫_ℝ = u 1 * 1 := by
        exact RCLike.inner_apply (1 : ℝ) (u 1)
      rw [hinner]
      ring
    simpa [Rnonpos, hcoord] using htest
  · intro hu
    rw [Set.mem_polarCone_iff_forall_inner_nonpos]
    intro y hy
    rcases hy with ⟨hy0, hy1⟩
    have hy_eq : y = !₂[(0 : ℝ), y 1] := by
      have hy' := euclideanSpace_fin2_eq y
      rw [hy0] at hy'
      simpa using hy'
    have hy_inner : ⟪y, u⟫_ℝ = ⟪!₂[(0 : ℝ), y 1], u⟫_ℝ := by
      exact congrArg (fun z : ℝ² ↦ ⟪z, u⟫_ℝ) hy_eq
    -- Every point of the ray has the form `(0, t)` with `t ≥ 0`, so the inner product is
    -- `t * u₂`.
    calc
      ⟪y, u⟫_ℝ = ⟪!₂[(0 : ℝ), y 1], u⟫_ℝ := hy_inner
      _ = y 1 * u 1 := by
        rw [PiLp.inner_apply, Fin.sum_univ_two]
        simp
        have hinner : ⟪y 1, u 1⟫_ℝ = u 1 * y 1 := by
          exact RCLike.inner_apply (y 1) (u 1)
        rw [hinner]
        ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy1 hu

/-- Helper for Remark 15 4: the conjugate of `fAB + gAB` is the indicator of the nonpositive
half-space. -/
private theorem sum_conjugate_eq_indicator_nonpositive_halfspace :
    (fAB + gAB)∗ = (ι[Rnonpos]).asEReal := by
  -- The previous helper identifies `fAB + gAB` with the indicator of the vertical ray.
  rw [sum_eq_indicator_vertical_ray]
  have hC_nonempty : C.Nonempty := ⟨0, by simp [C]⟩
  rw [conjugate_indicator_eq_indicator_polarCone_of_nonempty_isCone
    C hC_nonempty vertical_ray_isCone]
  exact congrArg (fun S : Set ℝ² ↦ (ι[S]).asEReal)
    vertical_ray_polarCone_eq_nonpositive_halfspace

/-- Helper for Remark 15 4: the domain of the explicit quadrant function is exactly the quadrant
itself. -/
private theorem dom_sqrt_quadrant_eq_quadrant :
    dom fAB = Q := by
  ext x
  constructor
  · intro hx
    by_cases hxQ : x ∈ Q
    · exact hxQ
    · -- Off the quadrant, the defining branch is `⊤`, so the point cannot lie in the domain.
      rw [mem_dom_iff_ne_top] at hx
      simp [fAB, hxQ] at hx
  · intro hxQ
    -- On the quadrant, `fAB` is represented by a real number, hence is finite above.
    rw [mem_dom_iff_ne_top]
    simp [fAB, hxQ]

/-- Helper for Remark 15 4: the domain of the vertical-axis indicator is the vertical axis. -/
private theorem dom_indicator_vertical_axis_eq :
    dom gAB = L := by
  ext x
  constructor
  · intro hx
    by_cases hxL : x ∈ L
    · exact hxL
    · have htop : gAB x = ⊤ := by
        change (((ι[L] x : Set.Ioi (⊥ : EReal)) : EReal)) = ⊤
        rw [indicator_apply]
        simp [hxL]
      exact False.elim (((not_mem_dom_iff gAB x).2 htop) hx)
  · intro hxL
    -- On the axis, the indicator takes the finite value `0`.
    rw [mem_dom_iff_ne_top]
    change (((ι[L] x : Set.Ioi (⊥ : EReal)) : EReal)) ≠ ⊤
    rw [indicator_apply]
    simp [hxL]

/-- Helper for Remark 15 4: subtracting the vertical axis from the quadrant leaves exactly the
closed right half-space. -/
private theorem dom_difference_eq_right_halfspace :
    dom fAB - dom gAB = {x : ℝ² | 0 ≤ x 0} := by
  rw [dom_sqrt_quadrant_eq_quadrant, dom_indicator_vertical_axis_eq]
  ext x
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    -- Subtracting a vertical-axis vector does not change the first coordinate.
    have hv0 : v 0 = 0 := hv
    simpa [Q, L, hv0, sub_eq_add_neg] using hu.1
  · intro hx
    let t : ℝ := max (-x 1) 0
    have hx1_nonneg : 0 ≤ x 1 + t := by
      -- The correction term exactly lifts the second coordinate into the nonnegative half-line.
      dsimp [t]
      have hmax : -x 1 ≤ max (-x 1) 0 := le_max_left _ _
      linarith
    -- Choose a compensating vector on the axis and keep the first coordinate fixed.
    refine Set.mem_sub.mpr ⟨!₂[x 0, x 1 + t], ?_, !₂[0, t], ?_, ?_⟩
    · refine ⟨hx, ?_⟩
      simpa using hx1_nonneg
    · simp [L]
    · rw [euclideanSpace_fin2_eq x]
      ext i <;> fin_cases i <;> simp [t]

/-- Helper for Remark 15 4: the convex cone hull of the closed right half-space is the half-space
itself. -/
private theorem right_halfspace_cone_eq_self :
    cone ({x : ℝ² | 0 ≤ x 0}) = {x : ℝ² | 0 ≤ x 0} := by
  have hconv : Convex ℝ ({x : ℝ² | 0 ≤ x 0} : Set ℝ²) := by
    intro x hx y hy a b ha hb hab
    -- Convex combinations preserve nonnegativity of the first coordinate.
    have hax : 0 ≤ a * x 0 := mul_nonneg ha hx
    have hby : 0 ≤ b * y 0 := mul_nonneg hb hy
    simpa [Pi.add_apply, Pi.smul_apply] using add_nonneg hax hby
  rw [cone_eq_toCone_of_convex hconv]
  ext x
  constructor
  · intro hx
    -- Any point of the cone is a positive multiple of a point already in the half-space.
    rcases (Convex.mem_toCone hconv).1 hx with ⟨a, ha, y, hy, rfl⟩
    simpa [Pi.smul_apply] using mul_nonneg ha.le hy
  · intro hx
    -- Conversely, the scalar `1` realizes each half-space point as a cone element.
    exact (Convex.mem_toCone hconv).2 ⟨1, by simp, x, hx, by simp⟩

/-- Helper for Remark 15 4: adding two indicators gives the indicator of the intersection. -/
lemma indicator_add_eq_indicator_inter
    {H : Type u} [AddCommGroup H] (A B : Set H) :
    (ι[A]).asEReal + (ι[B]).asEReal = (ι[A ∩ B]).asEReal := by
  ext x
  -- The indicator values are determined by the two membership tests.
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
    simp [ERealFunction.indicator, hA, hB]

/-- Helper for Remark 15 4: the infimal convolution of two indicators is the indicator of the
Minkowski sum. -/
lemma indicator_infimalConvolution_eq_indicator_add
    {H : Type u} [AddCommGroup H] (A B : Set H) :
    (ι[A]).asEReal □ (ι[B]).asEReal = (ι[A + B]).asEReal := by
  ext x
  by_cases hx : x ∈ A + B
  · rcases Set.mem_add.mp hx with ⟨y, hy, z, hz, rfl⟩
    -- A concrete decomposition of `x` gives one zero-valued summand in the infimum.
    have hupper :
        (⨅ t : H, ((ι[A] t : EReal) + (ι[B] (y + z - t) : EReal))) ≤ 0 := by
      simpa [indicator_apply, hy, hz] using
        (iInf_le (fun t : H ↦ ((ι[A] t : EReal) + (ι[B] (y + z - t) : EReal))) y)
    have hlower :
        (0 : EReal) ≤ (⨅ t : H, ((ι[A] t : EReal) + (ι[B] (y + z - t) : EReal))) := by
      refine le_iInf ?_
      intro t
      -- Every indicator summand is either `0` or `⊤`, so it is bounded below by `0`.
      by_cases htA : t ∈ A <;> by_cases htB : y + z - t ∈ B <;> simp [htA, htB]
    have hinf :
        (⨅ t : H, ((ι[A] t : EReal) + (ι[B] (y + z - t) : EReal))) = 0 :=
      le_antisymm hupper hlower
    simpa [indicator_apply, hx, infimalConvolution_apply] using hinf
  · -- Off the Minkowski sum, every decomposition forces one indicator summand to be `⊤`.
    have htop :
        (⨅ t : H, ((ι[A] t : EReal) + (ι[B] (x - t) : EReal))) = ⊤ := by
      refine iInf_eq_top.2 ?_
      intro t
      by_cases htA : t ∈ A
      · have htB : x - t ∉ B := by
          intro htB
          exact hx (Set.mem_add.mpr ⟨t, htA, x - t, htB, by abel⟩)
        have hA_ne_bot : ((ι[A] t : Set.Ioi (⊥ : EReal)) : EReal) ≠ ⊥ := by
          exact ne_of_gt (show (⊥ : EReal) < ((ι[A] t : Set.Ioi (⊥ : EReal)) : EReal) from
            (ι[A] t).2)
        simpa [indicator_apply, htA, htB] using EReal.add_top_of_ne_bot hA_ne_bot
      · have hB_ne_bot : ((ι[B] (x - t) : Set.Ioi (⊥ : EReal)) : EReal) ≠ ⊥ := by
          exact ne_of_gt
            (show (⊥ : EReal) < ((ι[B] (x - t) : Set.Ioi (⊥ : EReal)) : EReal) from
              (ι[B] (x - t)).2)
        rw [indicator_apply]
        simp [htA]
        have hB_ne_bot' : Bᶜ.indicator (fun _ : H ↦ (⊤ : EReal)) (x - t) ≠ ⊥ := by
          simpa [indicator_apply] using hB_ne_bot
        exact EReal.top_add_of_ne_bot hB_ne_bot'
    simpa [indicator_apply, hx, infimalConvolution_apply] using htop

/-- Helper for Remark 15 4: the Minkowski sum of two submodules is the set of their supremum. -/
lemma submodule_set_add_eq_sup
    {H : Type u} [AddCommGroup H] [Module ℝ H]
    (U V : Submodule ℝ H) :
    (U : Set H) + (V : Set H) = ((U ⊔ V : Submodule ℝ H) : Set H) := by
  ext x
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    -- A concrete Minkowski-sum decomposition is exactly a `mem_sup` witness.
    exact Submodule.mem_sup.mpr ⟨u, hu, v, hv, rfl⟩
  · intro hx
    -- Conversely, unpacking `mem_sup` gives the required decomposition in the sum set.
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v, hv, rfl⟩

/-- Helper for Remark 15 4: subtracting one submodule from another yields the same set as their
supremum. -/
lemma submodule_set_sub_eq_sup
    {H : Type u} [AddCommGroup H] [Module ℝ H]
    (U V : Submodule ℝ H) :
    (U : Set H) - (V : Set H) = ((U ⊔ V : Submodule ℝ H) : Set H) := by
  ext x
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    -- Rewrite subtraction as addition of the negated second summand to enter the supremum.
    simpa [sub_eq_add_neg] using
      ((Submodule.mem_sup.mpr ⟨u, hu, -v, by simpa using V.neg_mem hv, rfl⟩) :
        u + -v ∈ (U ⊔ V : Submodule ℝ H))
  · intro hx
    -- A supremum decomposition yields a difference decomposition after negating the second term.
    rcases Submodule.mem_sup.mp hx with ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, -v, by simpa using V.neg_mem hv, by abel_nf⟩

/-- Helper for Remark 15 4: for closed subspaces, the orthogonal complement of the intersection is
the closure of the sum of the orthogonal complements. -/
lemma orthogonal_inf_eq_closure_sup_orthogonal
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU_closed : IsClosed (U : Set H)) (hV_closed : IsClosed (V : Set H)) :
    (((U ⊓ V)ᗮ : Submodule ℝ H) : Set H) =
      closure ((((Uᗮ) ⊔ Vᗮ : Submodule ℝ H) : Set H)) := by
  let Uc : ClosedSubmodule ℝ H := ⟨U, hU_closed⟩
  let Vc : ClosedSubmodule ℝ H := ⟨V, hV_closed⟩
  -- The closed-submodule orthogonal formula is exactly the source statement after forgetting
  -- the closed structure.
  have hclosed := congrArg (fun W : ClosedSubmodule ℝ H ↦ (W : Set H))
    (ClosedSubmodule.sup_orthogonal Uc Vc)
  simpa [Uc, Vc] using hclosed.symm

/-- Helper for Remark 15 4: for closed subspaces, closedness of `U ⊔ V` is equivalent to
closedness of `(Uᗮ) ⊔ Vᗮ`. -/
lemma isClosed_sup_iff_isClosed_orthogonal_sup_local
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU_closed : IsClosed (U : Set H)) (hV_closed : IsClosed (V : Set H)) :
    IsClosed (((U ⊔ V : Submodule ℝ H) : Set H)) ↔
      IsClosed ((((Uᗮ) ⊔ Vᗮ : Submodule ℝ H) : Set H)) := by
  let L : H →L[ℝ] H := ContinuousLinearMap.id ℝ H
  constructor
  · intro hsum
    have hsubspace :
        (V : Set H) - L '' (U : Set H) =
          (Submodule.span ℝ ((V : Set H) - L '' (U : Set H)) : Set H) := by
      -- With `L = id`, the source difference set is exactly the supremum submodule.
      rw [show L '' (U : Set H) = (U : Set H) by
            ext x
            simp [L],
        submodule_set_sub_eq_sup V U]
      simp
    have hsub_closed : IsClosed ((V : Set H) - L '' (U : Set H)) := by
      -- The closedness hypothesis on `U ⊔ V` is precisely the closedness of the difference set.
      rw [show L '' (U : Set H) = (U : Set H) by
            ext x
            simp [L],
        submodule_set_sub_eq_sup V U]
      simpa [sup_comm] using hsum
    have hpolar_closed :=
      Set.isClosed_add_adjoint_image_polarCone_of_closed_subspace_sub_image
        (U : Set H) (V : Set H) L
        ⟨0, U.zero_mem⟩
        hU_closed U.convex (Set.submodule_isCone U)
        ⟨0, V.zero_mem⟩
        hV_closed V.convex (Set.submodule_isCone V)
        hsubspace
        hsub_closed
    have hUpolar : Set.polarCone (U : Set H) = (Uᗮ : Set H) := by
      simpa using (Set.polarSet_and_polarCone_eq_orthogonal_of_submodule U).2
    have hVpolar : Set.polarCone (V : Set H) = (Vᗮ : Set H) := by
      simpa using (Set.polarSet_and_polarCone_eq_orthogonal_of_submodule V).2
    -- Rewrite the polar-cone sum back into the orthogonal-complement supremum.
    rw [hUpolar, hVpolar,
      show L.adjoint '' (Vᗮ : Set H) = (Vᗮ : Set H) by
        ext x
        simp [L, ContinuousLinearMap.adjoint_id],
      submodule_set_add_eq_sup Uᗮ Vᗮ] at hpolar_closed
    simpa [sup_comm] using hpolar_closed
  · intro hsum
    have hsubspace :
        (Uᗮ : Set H) - L.adjoint '' (Vᗮ : Set H) =
          (Submodule.span ℝ ((Uᗮ : Set H) - L.adjoint '' (Vᗮ : Set H)) : Set H) := by
      -- Route correction: the reverse implication uses the same source pattern on orthogonals,
      -- then collapses the double orthogonals with closedness.
      rw [show L.adjoint '' (Vᗮ : Set H) = (Vᗮ : Set H) by
            ext x
            simp [L, ContinuousLinearMap.adjoint_id],
        submodule_set_sub_eq_sup Uᗮ Vᗮ]
      simp
    have hsub_closed : IsClosed ((Uᗮ : Set H) - L.adjoint '' (Vᗮ : Set H)) := by
      -- The orthogonal-side closedness again matches the corresponding difference set.
      rw [show L.adjoint '' (Vᗮ : Set H) = (Vᗮ : Set H) by
            ext x
            simp [L, ContinuousLinearMap.adjoint_id],
        submodule_set_sub_eq_sup Uᗮ Vᗮ]
      simpa [sup_comm] using hsum
    have hpolar_closed :=
      Set.isClosed_add_adjoint_image_polarCone_of_closed_subspace_sub_image
        (Vᗮ : Set H) (Uᗮ : Set H) L.adjoint
        ⟨0, (Vᗮ).zero_mem⟩
        V.isClosed_orthogonal Vᗮ.convex (Set.submodule_isCone Vᗮ)
        ⟨0, (Uᗮ).zero_mem⟩
        U.isClosed_orthogonal Uᗮ.convex (Set.submodule_isCone Uᗮ)
        hsubspace
        hsub_closed
    have hUpolar : Set.polarCone (Uᗮ : Set H) = (Uᗮᗮ : Set H) := by
      simpa using (Set.polarSet_and_polarCone_eq_orthogonal_of_submodule Uᗮ).2
    have hVpolar : Set.polarCone (Vᗮ : Set H) = (Vᗮᗮ : Set H) := by
      simpa using (Set.polarSet_and_polarCone_eq_orthogonal_of_submodule Vᗮ).2
    have hU_closed' : Uᗮᗮ = U := by
      calc
        Uᗮᗮ = U.topologicalClosure := Submodule.orthogonal_orthogonal_eq_closure U
        _ = U := hU_closed.submodule_topologicalClosure_eq
    have hV_closed' : Vᗮᗮ = V := by
      calc
        Vᗮᗮ = V.topologicalClosure := Submodule.orthogonal_orthogonal_eq_closure V
        _ = V := hV_closed.submodule_topologicalClosure_eq
    -- After collapsing the double orthogonals, the source theorem returns to `U ⊔ V`.
    rw [hVpolar, hUpolar, hV_closed', hU_closed', ContinuousLinearMap.adjoint_adjoint,
      show L '' (U : Set H) = (U : Set H) by
        ext x
        simp [L],
      submodule_set_add_eq_sup V U] at hpolar_closed
    simpa [sup_comm] using hpolar_closed

/-- Helper for Remark 15 4: if `U + V` is not closed, then the sum of the orthogonal complements
is not closed either. -/
lemma not_isClosed_orthogonal_sup_of_not_isClosed_sup
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U V : Submodule ℝ H)
    (hU_closed : IsClosed (U : Set H)) (hV_closed : IsClosed (V : Set H))
    (hUV_not_closed : ¬ IsClosed ((U ⊔ V : Submodule ℝ H) : Set H)) :
    ¬ IsClosed ((((Uᗮ) ⊔ Vᗮ : Submodule ℝ H) : Set H)) := by
  intro horth_closed
  -- The local closedness bridge lets us push the contradiction back to the original sum.
  exact hUV_not_closed
    ((isClosed_sup_iff_isClosed_orthogonal_sup_local U V hU_closed hV_closed).2 horth_closed)

/-- Helper for Remark 15 4: the conjugate of the vertical-axis indicator is the indicator of the
horizontal axis. -/
private theorem gAB_conjugate_eq_indicator_horizontal_axis :
    gAB∗ = (ι[{u : ℝ² | u 1 = 0}]).asEReal := by
  let V : Submodule ℝ ℝ² :=
    { carrier := L
      zero_mem' := by simp [L]
      add_mem' := by
        intro x y hx hy
        have hx0 : x 0 = 0 := hx
        have hy0 : y 0 = 0 := hy
        calc
          (x + y) 0 = x 0 + y 0 := by simp
          _ = 0 := by simp [hx0, hy0]
      smul_mem' := by
        intro a x hx
        have hx0 : x 0 = 0 := hx
        calc
          (a • x) 0 = a * x 0 := by simp
          _ = 0 := by simp [hx0] }
  have horth : (Vᗮ : Set ℝ²) = {u : ℝ² | u 1 = 0} := by
    ext u
    constructor
    · intro hu
      have hu_test : ⟪!₂[(0 : ℝ), 1], u⟫_ℝ = 0 := by
        -- Testing orthogonality on the unit vertical vector isolates the second coordinate.
        exact (V.mem_orthogonal u).mp hu !₂[(0 : ℝ), 1] (by simp [V, L])
      have hcoord : ⟪!₂[(0 : ℝ), 1], u⟫_ℝ = u 1 := by
        rw [PiLp.inner_apply, Fin.sum_univ_two]
        simp
        have hinner : ⟪(1 : ℝ), u 1⟫_ℝ = u 1 * 1 := by
          exact RCLike.inner_apply (1 : ℝ) (u 1)
        rw [hinner]
        ring
      simpa [hcoord] using hu_test
    · intro hu
      exact (V.mem_orthogonal u).2 <| by
        intro x hx
        have hx0 : x 0 = 0 := hx
        -- On the vertical axis, only the second-coordinate inner product survives.
        rw [PiLp.inner_apply, Fin.sum_univ_two, hx0, hu]
        simp
  calc
    gAB∗ = (((ι[(V : Set ℝ²)]).asEReal)∗) := by rfl
    _ = (ι[(Vᗮ : Set ℝ²)]).asEReal :=
      conjugate_indicator_submodule_eq_indicator_orthogonal (V := V)
    _ = (ι[{u : ℝ² | u 1 = 0}]).asEReal := by
      exact congrArg (fun S : Set ℝ² ↦ (ι[S]).asEReal) horth

/-- Helper for Remark 15 4: the origin gives a zero affine defect, so the explicit conjugate is
never `⊥`. -/
private theorem fAB_conjugate_ne_bot (u : ℝ²) :
    fAB∗ u ≠ ⊥ := by
  have hnonneg : (0 : EReal) ≤ fAB∗ u := by
    -- Evaluating the defining supremum at `x = 0` gives the lower bound `0`.
    rw [conjugate_apply]
    simpa [fAB, Q] using
      (le_iSup (fun x : ℝ² ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - fAB x) (0 : ℝ²))
  exact ne_of_gt (lt_of_lt_of_le (by simp) hnonneg)

/-- Helper for Remark 15 4: when the second dual coordinate is nonnegative, the conjugate of the
explicit square-root example is `⊤`. -/
private theorem fAB_conjugate_eq_top_of_nonneg_second
    (a b : ℝ) (hb : 0 ≤ b) :
    fAB∗ !₂[a, b] = ⊤ := by
  rw [conjugate_apply, EReal.eq_top_iff_forall_lt]
  intro M
  let t : ℝ := |M| + |a| + 1
  let x : ℝ² := !₂[1, t ^ 2]
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  have hxQ : x ∈ Q := by
    -- The witness `x = (1,t²)` stays in the quadrant for every real `t`.
    dsimp [x, Q]
    constructor <;> positivity
  have hsqrt : Real.sqrt (x 0 * x 1) = t := by
    -- On this witness, the square root simplifies to `sqrt (t²) = t` because `t > 0`.
    dsimp [x]
    rw [show (1 : ℝ) * t ^ 2 = t ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hinner_real : ⟪x, !₂[a, b]⟫_ℝ = a + b * t ^ 2 := by
    -- Expanding the two-coordinate inner product gives the affine term `a + b t²`.
    dsimp [x]
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    norm_num
    have h1 : ⟪(1 : ℝ), a⟫_ℝ = a * 1 := by
      exact RCLike.inner_apply (1 : ℝ) a
    have h2 : ⟪t ^ 2, b⟫_ℝ = b * t ^ 2 := by
      exact RCLike.inner_apply (t ^ 2) b
    rw [h1, h2]
    ring
  have hinner :
      ((⟪x, !₂[a, b]⟫_ℝ : ℝ) : EReal) = ((a + b * t ^ 2 : ℝ) : EReal) := by
    exact congrArg (fun r : ℝ ↦ (r : EReal)) hinner_real
  have hxval : fAB x = ((-t : ℝ) : EReal) := by
    -- On the quadrant branch, `fAB` is exactly `-sqrt (x₀ x₁) = -t`.
    simp [fAB, hxQ, hsqrt]
  have hterm :
      ((⟪x, !₂[a, b]⟫_ℝ : ℝ) : EReal) - fAB x = ((a + b * t ^ 2 + t : ℝ) : EReal) := by
    calc
      ((⟪x, !₂[a, b]⟫_ℝ : ℝ) : EReal) - fAB x
          = ((a + b * t ^ 2 : ℝ) : EReal) - ((-t : ℝ) : EReal) := by
              rw [hinner, hxval]
      _ = ((a + b * t ^ 2 + t : ℝ) : EReal) := by
        rw [← EReal.coe_sub]
        ring
  have hM_lt_linear : M < a + t := by
    -- The choice `t = |M| + |a| + 1` makes the linear part already exceed `M`.
    dsimp [t]
    nlinarith [le_abs_self M, neg_abs_le a]
  have hM_lt_term : M < a + b * t ^ 2 + t := by
    have hquad_nonneg : 0 ≤ b * t ^ 2 := mul_nonneg hb (sq_nonneg t)
    linarith
  have hvalue :
      ((M : ℝ) : EReal) <
        (((⟪x, !₂[a, b]⟫_ℝ : ℝ) : EReal) - fAB x) := by
    -- The chosen witness beats the arbitrary finite lower bound `M`.
    have hvalue' : ((M : ℝ) : EReal) < ((a + b * t ^ 2 + t : ℝ) : EReal) := by
      exact_mod_cast hM_lt_term
    simpa [hterm] using hvalue'
  exact lt_of_lt_of_le hvalue
    (le_iSup (fun y : ℝ² ↦ ((⟪y, !₂[a, b]⟫_ℝ : ℝ) : EReal) - fAB y) x)

/-- Helper for Remark 15 4: on the quadrant, the source threshold defect is exactly a negative
multiple of a square. -/
private theorem fAB_threshold_defect_eq_b_mul_sq
    {b : ℝ} (hb : b < 0) {x : ℝ²} (hx : x ∈ Q) :
    (1 / (4 * b)) * x 0 + b * x 1 + Real.sqrt (x 0 * x 1) =
      b * (Real.sqrt (x 1) + Real.sqrt (x 0) / (2 * b)) ^ 2 := by
  have hx0 : 0 ≤ x 0 := hx.1
  have hx1 : 0 ≤ x 1 := hx.2
  have hb0 : b ≠ 0 := ne_of_lt hb
  -- Rewrite the quadrant coordinates and the mixed square root in terms of square roots.
  calc
    (1 / (4 * b)) * x 0 + b * x 1 + Real.sqrt (x 0 * x 1)
        = (1 / (4 * b)) * (Real.sqrt (x 0)) ^ 2 +
            b * (Real.sqrt (x 1)) ^ 2 +
            Real.sqrt (x 0) * Real.sqrt (x 1) := by
            rw [Real.sqrt_mul hx0, Real.sq_sqrt hx0, Real.sq_sqrt hx1]
    _ = b * (Real.sqrt (x 1) + Real.sqrt (x 0) / (2 * b)) ^ 2 := by
      field_simp [hb0]
      ring

/-- Helper for Remark 15 4: the source square-completion makes the threshold defect nonpositive on
the quadrant. -/
private theorem fAB_threshold_defect_nonpos
    {b : ℝ} (hb : b < 0) {x : ℝ²} (hx : x ∈ Q) :
    (1 / (4 * b)) * x 0 + b * x 1 + Real.sqrt (x 0 * x 1) ≤ 0 := by
  -- The exact factorization reduces the sign to `b < 0` times a square.
  rw [fAB_threshold_defect_eq_b_mul_sq hb hx]
  exact mul_nonpos_of_nonpos_of_nonneg hb.le (sq_nonneg _)

/-- Helper for Remark 15 4: at the source threshold point with negative second coordinate, the
explicit conjugate value is exactly `0`. -/
private theorem fAB_conjugate_eq_zero_at_threshold_of_neg_second
    (b : ℝ) (hb : b < 0) :
    fAB∗ !₂[1 / (4 * b), b] = 0 := by
  have hnonneg : (0 : EReal) ≤ fAB∗ !₂[1 / (4 * b), b] := by
    -- Evaluating the conjugate at the origin gives the lower bound `0`.
    rw [conjugate_apply]
    simpa [fAB, Q] using
      (le_iSup
        (fun x : ℝ² ↦ ((⟪x, !₂[1 / (4 * b), b]⟫_ℝ : ℝ) : EReal) - fAB x)
        (0 : ℝ²))
  have hnonpos : fAB∗ !₂[1 / (4 * b), b] ≤ 0 := by
    rw [conjugate_apply]
    refine iSup_le ?_
    intro x
    by_cases hxQ : x ∈ Q
    · have hinner_real :
          ⟪x, !₂[1 / (4 * b), b]⟫_ℝ = (1 / (4 * b)) * x 0 + b * x 1 := by
        -- Expanding the `ℝ²` inner product isolates the two affine coefficients.
        rw [PiLp.inner_apply, Fin.sum_univ_two]
        simp
        have h0 : ⟪x 0, (b⁻¹ * (4⁻¹ : ℝ))⟫_ℝ = (b⁻¹ * (4⁻¹ : ℝ)) * x 0 := by
          exact RCLike.inner_apply (x 0) (b⁻¹ * (4⁻¹ : ℝ))
        have h1 : ⟪x 1, b⟫_ℝ = b * x 1 := by
          exact RCLike.inner_apply (x 1) b
        rw [h0, h1]
      have hdefect :
          ((⟪x, !₂[1 / (4 * b), b]⟫_ℝ : ℝ) : EReal) - fAB x =
            (((1 / (4 * b)) * x 0 + b * x 1 + Real.sqrt (x 0 * x 1) : ℝ) : EReal) := by
        -- On the quadrant branch, subtracting `-√(x₀ x₁)` adds the square-root term.
        rw [show fAB x = ((-Real.sqrt (x 0 * x 1) : ℝ) : EReal) by simp [fAB, hxQ],
          hinner_real, ← EReal.coe_sub]
        ring
      have hreal_nonpos :
          (1 / (4 * b)) * x 0 + b * x 1 + Real.sqrt (x 0 * x 1) ≤ 0 :=
        fAB_threshold_defect_nonpos hb hxQ
      have hcast_nonpos :
          ((((1 / (4 * b)) * x 0 + b * x 1 + Real.sqrt (x 0 * x 1) : ℝ) : EReal) ≤ 0) := by
        exact_mod_cast hreal_nonpos
      rw [hdefect]
      exact hcast_nonpos
    · -- Off the quadrant, `fAB x = ⊤`, so the affine defect is `⊥`.
      simp [fAB, hxQ]
  exact le_antisymm hnonpos hnonneg

/-- Helper for Remark 15 4: the explicit `ℝ²` infimal convolution of the separate conjugates is
the indicator of the open lower half-space. -/
private theorem fAB_conjugate_infimalConvolution_eq_indicator_open_lower_halfspace :
    fAB∗ □ gAB∗ = (ι[Rneg]).asEReal := by
  ext u
  by_cases hu : u 1 < 0
  · have hle : (fAB∗ □ gAB∗) u ≤ 0 := by
      rw [infimalConvolution_apply]
      let t0 : ℝ² := !₂[1 / (4 * u 1), u 1]
      -- The source threshold point gives one decomposition with total value `0`.
      refine le_trans (iInf_le (fun t : ℝ² ↦ fAB∗ t + gAB∗ (u - t)) t0) ?_
      have hf_zero : fAB∗ t0 = 0 := by
        simpa [t0] using fAB_conjugate_eq_zero_at_threshold_of_neg_second (b := u 1) hu
      have hg_zero : gAB∗ (u - t0) = 0 := by
        -- The remaining term lies on the horizontal axis because the second coordinate cancels.
        rw [gAB_conjugate_eq_indicator_horizontal_axis]
        have haxis : (u - t0) 1 = 0 := by
          simp [t0]
        simp [indicator_apply, haxis]
      rw [hf_zero, hg_zero]
      simp
    have hge : 0 ≤ (fAB∗ □ gAB∗) u := by
      rw [infimalConvolution_apply]
      refine le_iInf ?_
      intro t
      have hf_nonneg : (0 : EReal) ≤ fAB∗ t := by
        -- The origin witness keeps every conjugate value above `0`.
        rw [conjugate_apply]
        simpa [fAB, Q] using
          (le_iSup (fun x : ℝ² ↦ ((⟪x, t⟫_ℝ : ℝ) : EReal) - fAB x) (0 : ℝ²))
      have hg_nonneg : (0 : EReal) ≤ gAB∗ (u - t) := by
        -- The indicator formula for `gAB∗` only takes the values `0` and `⊤`.
        rw [gAB_conjugate_eq_indicator_horizontal_axis]
        by_cases haxis : (u - t) 1 = 0
        · simp [indicator_apply, haxis]
        · have haxis' : ¬ (u 1 - t 1 = 0) := by
            simpa using haxis
          simp [indicator_apply, haxis']
      simpa using add_le_add hf_nonneg hg_nonneg
    have hzero : (fAB∗ □ gAB∗) u = 0 := le_antisymm hle hge
    simpa [Rneg, indicator_apply, hu] using hzero
  · have hu_nonneg : 0 ≤ u 1 := le_of_not_gt hu
    have htop : (fAB∗ □ gAB∗) u = ⊤ := by
      rw [infimalConvolution_apply]
      refine iInf_eq_top.2 ?_
      intro t
      by_cases haxis : (u - t) 1 = 0
      · have ht_second : t 1 = u 1 := by
          have hcoord : u 1 - t 1 = 0 := by
            simpa using haxis
          have hu_eq : u 1 = t 1 := sub_eq_zero.mp hcoord
          simpa [eq_comm] using hu_eq
        have ht_nonneg : 0 ≤ t 1 := by
          simpa [ht_second] using hu_nonneg
        have hf_top : fAB∗ t = ⊤ := by
          -- On the horizontal-axis branch, the second coordinate of `t` is nonnegative.
          rw [euclideanSpace_fin2_eq t]
          simpa using fAB_conjugate_eq_top_of_nonneg_second (a := t 0) (b := t 1) ht_nonneg
        have hg_zero : gAB∗ (u - t) = 0 := by
          rw [gAB_conjugate_eq_indicator_horizontal_axis]
          simp [indicator_apply, haxis]
        rw [hf_top, hg_zero]
        simp
      · have hg_top : gAB∗ (u - t) = ⊤ := by
          -- Off the horizontal axis, the indicator formula for `gAB∗` forces `⊤`.
          rw [gAB_conjugate_eq_indicator_horizontal_axis]
          have haxis' : ¬ (u 1 - t 1 = 0) := by
            simpa using haxis
          simp [indicator_apply, haxis']
        rw [hg_top]
        exact EReal.add_top_of_ne_bot (fAB_conjugate_ne_bot t)
    simpa [Rneg, indicator_apply, hu] using htop

/-- Helper for Remark 15 4: a discontinuous linear functional, viewed as an `EReal`-valued map,
admits no continuous affine minorant with any prescribed slope. -/
lemma no_continuous_affine_minorant_with_slope_linear_toEReal_of_not_continuous
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ℓ : H →ₗ[ℝ] ℝ) (hℓ : ¬ Continuous ℓ) :
    ¬ ∃ u : H,
      HasContinuousAffineMinorantWithSlope
        ((fun x : H ↦ (ℓ x : ℝ)).toEReal.asEReal) u := by
  intro hminor
  rcases hminor with ⟨u, hu⟩
  rcases hu with ⟨η, hη⟩
  let g0 : H →ᴬ[ℝ] ℝ :=
    { toAffineMap := (innerSL ℝ u).toLinearMap.toAffineMap
      cont := (innerSL ℝ u).continuous }
  let g : H →ᴬ[ℝ] ℝ := g0 + ContinuousAffineMap.const ℝ H η
  have hg_minor : ∀ x : H, g x ≤ ℓ x := by
    intro x
    have hx : (((⟪x, u⟫_ℝ + η : ℝ) : EReal) ≤ (((fun x : H ↦ (ℓ x : ℝ)).toEReal.asEReal) x)) := by
      simpa using hη x
    have hx_real : ⟪x, u⟫_ℝ + η ≤ ℓ x := by
      exact (EReal.coe_le_coe_iff.1 hx)
    simpa [g, g0, real_inner_comm] using hx_real
  exact (no_continuous_affine_minorant_of_not_continuous ℓ hℓ) ⟨g, hg_minor⟩

/-- Helper for Remark 15 4: a discontinuous linear functional has identically `⊤` conjugate when
viewed as an `EReal`-valued function. -/
lemma conjugate_linear_toEReal_eq_top_of_not_continuous
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (ℓ : H →ₗ[ℝ] ℝ) (hℓ : ¬ Continuous ℓ) :
    (((fun x : H ↦ (ℓ x : ℝ)).toEReal.asEReal)∗) = fun _ ↦ (⊤ : EReal) := by
  -- Proposition 13.12 turns the absence of affine minorants into an everywhere-`⊤` conjugate.
  exact (conjugate_eq_top_iff_no_continuousAffineMinorant
    ((fun x : H ↦ (ℓ x : ℝ)).toEReal.asEReal)).2
      (no_continuous_affine_minorant_with_slope_linear_toEReal_of_not_continuous ℓ hℓ)

/-- Remark 15.4 (1): on the explicit `ℝ²` example, the conjugate-of-a-sum formula from Theorem
15.3 fails even though `cone (dom f - dom g)` is a closed cone; the missing hypothesis is that
this cone be a closed linear subspace. -/
theorem attouchBrezis_counterexample_closedCone_not_closedLinearSubspace :
    ((fAB + gAB)∗ ≠ fAB∗ □ gAB∗) ∧
      (IsClosed (cone (dom fAB - dom gAB)) ∧
        ¬ ∃ V : Submodule ℝ ℝ², cone (dom fAB - dom gAB) = (V : Set ℝ²)) := by
  have hleft0 : ((fAB + gAB)∗) (0 : ℝ²) = 0 := by
    -- The conjugate of `fAB + gAB` is already identified with the lower-halfspace indicator.
    have hsum0 := congrFun sum_conjugate_eq_indicator_nonpositive_halfspace (0 : ℝ²)
    simpa [Rnonpos, indicator_apply] using hsum0
  have hright0 : (fAB∗ □ gAB∗) (0 : ℝ²) = ⊤ := by
    rw [infimalConvolution_apply]
    refine iInf_eq_top.2 ?_
    intro t
    by_cases ht : t 1 = 0
    · have hf_top : fAB∗ t = ⊤ := by
        -- On the horizontal axis, the proved nonnegative branch already forces `fAB∗ = ⊤`.
        rw [euclideanSpace_fin2_eq t]
        have ht_nonneg : 0 ≤ t 1 := by simpa [ht]
        simpa using fAB_conjugate_eq_top_of_nonneg_second (a := t 0) (b := t 1) ht_nonneg
      have hg_zero : gAB∗ (0 - t) = 0 := by
        -- The conjugate of `gAB` vanishes exactly on the horizontal axis.
        rw [show (0 : ℝ²) - t = -t by simp, gAB_conjugate_eq_indicator_horizontal_axis]
        simp [indicator_apply, ht]
      rw [hf_top, hg_zero]
      simp
    · have hg_top : gAB∗ (0 - t) = ⊤ := by
        -- Off the horizontal axis, the indicator formula for `gAB∗` gives `⊤`.
        rw [show (0 : ℝ²) - t = -t by simp, gAB_conjugate_eq_indicator_horizontal_axis]
        simp [indicator_apply]
        exact ht
      rw [hg_top]
      exact EReal.add_top_of_ne_bot (fAB_conjugate_ne_bot t)
  have hneq : (fAB + gAB)∗ ≠ fAB∗ □ gAB∗ := by
    intro hEq
    have hEq0 := congrFun hEq (0 : ℝ²)
    rw [hleft0, hright0] at hEq0
    exact EReal.zero_ne_top hEq0
  have hcone_eq : cone (dom fAB - dom gAB) = {x : ℝ² | 0 ≤ x 0} := by
    -- The domain-difference cone is exactly the closed right half-space.
    rw [dom_difference_eq_right_halfspace, right_halfspace_cone_eq_self]
  have hclosed : IsClosed (cone (dom fAB - dom gAB)) := by
    rw [hcone_eq]
    exact isClosed_le continuous_const
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 ↦ ℝ) 0)
  have hnot_subspace :
      ¬ ∃ V : Submodule ℝ ℝ², cone (dom fAB - dom gAB) = (V : Set ℝ²) := by
    intro hV
    rcases hV with ⟨V, hV⟩
    have hxV : (!₂[(1 : ℝ), 0] : ℝ²) ∈ (V : Set ℝ²) := by
      rw [← hV, hcone_eq]
      simp
    have hnegV : (-(!₂[(1 : ℝ), 0] : ℝ²)) ∈ (V : Set ℝ²) := V.neg_mem hxV
    have hneg_cone : (-(!₂[(1 : ℝ), 0] : ℝ²)) ∈ cone (dom fAB - dom gAB) := by
      simpa [hV] using hnegV
    rw [hcone_eq] at hneg_cone
    simp at hneg_cone
    linarith
  exact ⟨hneq, hclosed, hnot_subspace⟩

/-- Remark 15.4 (2): for closed linear subspaces `U` and `V`, equivalently for indicators
`ι[U], ι[V] ∈ Γ₀(H)`, with nonclosed sum, replacing strong relative interior by relative
interior is not enough in Theorem 15.3: the failure `(f + g)∗ ≠ f∗ □ g∗` occurs even though
`cone (dom f - dom g)` is the nonclosed linear subspace `U + V`, so in particular
`0 ∈ ri (dom f - dom g)`. -/
theorem attouchBrezis_counterexample_relativeInterior_not_enough
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (hH_infinite : ¬ FiniteDimensional ℝ H)
    (U V : Submodule ℝ H)
    (hU_closed : IsClosed (U : Set H)) (hV_closed : IsClosed (V : Set H))
    (hUV_not_closed : ¬ IsClosed ((U ⊔ V : Submodule ℝ H) : Set H)) :
    let f : H → EReal := (ι[(U : Set H)]).asEReal
    let g : H → EReal := (ι[(V : Set H)]).asEReal
    let D : Set H := dom f - dom g
    ((f + g)∗ ≠ (f∗ □ g∗)) ∧
      (cone D = D ∧ (0 : H) ∈ ri D ∧
        D = ((U ⊔ V : Submodule ℝ H) : Set H) ∧ ¬ IsClosed D) := by
  dsimp
  let S : Set H := ((((Uᗮ) ⊔ Vᗮ : Submodule ℝ H) : Set H))
  have hinter :
      ((U : Set H) ∩ (V : Set H)) = (((U ⊓ V : Submodule ℝ H) : Set H)) := by
    ext x
    simp
  have hleft :
      (((ι[(U : Set H)]).asEReal + (ι[(V : Set H)]).asEReal)∗) =
        (ι[closure S]).asEReal := by
    -- The sum of the two indicators is the indicator of the intersection, whose orthogonal is
    -- the closure of `Uᗮ ⊔ Vᗮ`.
    rw [indicator_add_eq_indicator_inter, hinter,
      conjugate_indicator_submodule_eq_indicator_orthogonal (V := U ⊓ V)]
    exact congrArg (fun T : Set H ↦ (ι[T]).asEReal)
      (orthogonal_inf_eq_closure_sup_orthogonal U V hU_closed hV_closed)
  have hright :
      (((ι[(U : Set H)]).asEReal)∗ □ (((ι[(V : Set H)]).asEReal)∗)) =
        (ι[S]).asEReal := by
    -- The separate conjugates are indicators of the orthogonal complements, and their infimal
    -- convolution is the indicator of the Minkowski sum `Uᗮ + Vᗮ = Uᗮ ⊔ Vᗮ`.
    rw [conjugate_indicator_submodule_eq_indicator_orthogonal (V := U),
      conjugate_indicator_submodule_eq_indicator_orthogonal (V := V),
      indicator_infimalConvolution_eq_indicator_add]
    exact congrArg (fun T : Set H ↦ (ι[T]).asEReal) (submodule_set_add_eq_sup Uᗮ Vᗮ)
  have hS_not_closed : ¬ IsClosed S :=
    not_isClosed_orthogonal_sup_of_not_isClosed_sup U V hU_closed hV_closed hUV_not_closed
  have hneq :
      (((ι[(U : Set H)]).asEReal + (ι[(V : Set H)]).asEReal)∗) ≠
        ((((ι[(U : Set H)]).asEReal)∗) □ (((ι[(V : Set H)]).asEReal)∗)) := by
    intro hEq
    have hEq' : (ι[closure S]).asEReal = (ι[S]).asEReal := by
      calc
        (ι[closure S]).asEReal =
            (((ι[(U : Set H)]).asEReal + (ι[(V : Set H)]).asEReal)∗) := by
              symm
              exact hleft
        _ = ((((ι[(U : Set H)]).asEReal)∗) □ (((ι[(V : Set H)]).asEReal)∗)) := hEq
        _ = (ι[S]).asEReal := hright
    have hclosure_subset : closure S ⊆ S := by
      intro x hxclosure
      by_contra hxS
      have hxEq := congrArg (fun F : H → EReal ↦ F x) hEq'
      simp [indicator_apply, hxclosure, hxS] at hxEq
    have hS_closed : IsClosed S := by
      rw [← closure_eq_iff_isClosed]
      exact subset_antisymm hclosure_subset subset_closure
    exact hS_not_closed hS_closed
  have hdomf : dom ((ι[(U : Set H)]).asEReal) = (U : Set H) := by
    ext x
    rw [mem_dom_iff_ne_top]
    by_cases hx : x ∈ (U : Set H)
    · simp [indicator_apply, hx]
    · simp [indicator_apply, hx]
  have hdomg : dom ((ι[(V : Set H)]).asEReal) = (V : Set H) := by
    ext x
    rw [mem_dom_iff_ne_top]
    by_cases hx : x ∈ (V : Set H)
    · simp [indicator_apply, hx]
    · simp [indicator_apply, hx]
  have hD_eq :
      dom ((ι[(U : Set H)]).asEReal) - dom ((ι[(V : Set H)]).asEReal) =
        ((U ⊔ V : Submodule ℝ H) : Set H) := by
    -- The domain difference is exactly the submodule sum, which stays a linear subspace.
    rw [hdomf, hdomg, submodule_set_sub_eq_sup]
  have hcone :
      cone (dom ((ι[(U : Set H)]).asEReal) - dom ((ι[(V : Set H)]).asEReal)) =
        dom ((ι[(U : Set H)]).asEReal) - dom ((ι[(V : Set H)]).asEReal) := by
    rw [hD_eq]
    simpa using cone_eq_self_of_submodule (U ⊔ V : Submodule ℝ H)
  have hri :
      (0 : H) ∈ ri (dom ((ι[(U : Set H)]).asEReal) - dom ((ι[(V : Set H)]).asEReal)) := by
    -- Every submodule equals its relative interior, so the origin lies in `ri D`.
    rw [hD_eq]
    simpa [relativeInterior_submodule_eq_self]
      using (show (0 : H) ∈ (((U ⊔ V : Submodule ℝ H) : Set H)) from Submodule.zero_mem _)
  have hD_not_closed :
      ¬ IsClosed (dom ((ι[(U : Set H)]).asEReal) - dom ((ι[(V : Set H)]).asEReal)) := by
    rwa [hD_eq]
  refine ⟨hneq, ?_⟩
  exact ⟨hcone, hri, hD_eq, hD_not_closed⟩

/-- Remark 15.4 (3): lower semicontinuity is necessary in Theorem 15.3; if `f` is the
Example 9.22 discontinuous linear functional and `g = ι[({(0 : H)} : Set H)]`, then
`(f + g)∗ ≠ f∗ □ g∗` even though `dom f - dom g = H`. -/
theorem attouchBrezis_counterexample_without_lowerSemicontinuity
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (hH_infinite : ¬ FiniteDimensional ℝ H)
    (f : H →ₗ[ℝ] ℝ)
    (hf_not_continuous : ¬ Continuous f) :
    let F : H → EReal := (fun x : H ↦ (f x : ℝ)).toEReal.asEReal
    let g : H → EReal := (ι[({(0 : H)} : Set H)]).asEReal
    ((F + g)∗ ≠ F∗ □ g∗) ∧
      (dom F - dom g) = (Set.univ : Set H) := by
  dsimp
  have hF_conj :
      (((fun x : H ↦ (f x : ℝ)).toEReal.asEReal)∗) = fun _ : H ↦ (⊤ : EReal) :=
    conjugate_linear_toEReal_eq_top_of_not_continuous f hf_not_continuous
  have hg_conj :
      (((ι[({(0 : H)} : Set H)]).asEReal)∗) = fun _ : H ↦ (0 : EReal) := by
    -- The conjugate of the zero-subspace indicator is the indicator of the whole space.
    simpa [ERealFunction.indicator] using
      (conjugate_indicator_submodule_eq_indicator_orthogonal (V := (⊥ : Submodule ℝ H)))
  have hsum_eq :
      (fun x : H ↦ (f x : ℝ)).toEReal.asEReal + (ι[({(0 : H)} : Set H)]).asEReal =
        (ι[({(0 : H)} : Set H)]).asEReal := by
    ext x
    by_cases hx : x = 0
    · -- At the origin, the linear functional vanishes, so the added term is `0`.
      simp [hx]
    · -- Away from the origin, the indicator already equals `⊤`, so the finite linear value is
      -- absorbed.
      simp [indicator_apply, hx]
  have hneq :
      (((fun x : H ↦ (f x : ℝ)).toEReal.asEReal + (ι[({(0 : H)} : Set H)]).asEReal)∗) ≠
        (((fun x : H ↦ (f x : ℝ)).toEReal.asEReal)∗ □
          (((ι[({(0 : H)} : Set H)]).asEReal)∗)) := by
    intro hEq
    have hleft0 :
        (((fun x : H ↦ (f x : ℝ)).toEReal.asEReal + (ι[({(0 : H)} : Set H)]).asEReal)∗)
          (0 : H) = 0 := by
      rw [hsum_eq, hg_conj]
    have hright0 :
        ((((fun x : H ↦ (f x : ℝ)).toEReal.asEReal)∗ □
            (((ι[({(0 : H)} : Set H)]).asEReal)∗)) (0 : H)) = ⊤ := by
      rw [hF_conj, hg_conj, infimalConvolution_apply]
      refine iInf_eq_top.2 ?_
      intro y
      simp
    have hEq0 :
        ((((fun x : H ↦ (f x : ℝ)).toEReal.asEReal + (ι[({(0 : H)} : Set H)]).asEReal)∗))
          (0 : H) =
          ((((fun x : H ↦ (f x : ℝ)).toEReal.asEReal)∗ □
              (((ι[({(0 : H)} : Set H)]).asEReal)∗)) (0 : H)) :=
      congrFun hEq (0 : H)
    rw [hleft0, hright0] at hEq0
    exact EReal.zero_ne_top hEq0
  refine ⟨hneq, ?_⟩
  ext x
  constructor
  · intro hx
    exact Set.mem_univ x
  · intro hx
    -- Subtracting `{0}` from the full domain leaves the whole space.
    refine Set.mem_sub.mpr ⟨x, ?_, 0, by simp, by simp⟩
    rw [mem_dom_iff]
    simp

end AttouchBrezisTheorem

end ERealFunction
