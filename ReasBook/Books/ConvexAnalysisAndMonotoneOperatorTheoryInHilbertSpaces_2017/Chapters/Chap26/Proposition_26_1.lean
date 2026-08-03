import BauschkeLean.Chap06.Example_6_43
import BauschkeLean.Chap23.ResolventRealizer
import BauschkeLean.Chap26.ForwardBackwardSplitting
import BauschkeLean.Chap26.Text_26_0_1

open Function
open scoped InnerProductSpace Pointwise Set SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

-- Semantic recall note: `lean_leansearch` only surfaced generic reflection/projection material for
-- this item, so the file follows the verified local Chapter 26/23/4 owners
-- `primal_inclusion_solution_set`, `dual_inclusion_solution_set`, `resolventMap`,
-- `yosidaApproximationMap`, `douglasRachfordOperator`, `FirmlyNonexpansive`, `Averaged`, and
-- `fixedPoints`.
/- Source/core/bridge triage:
- `source-facing`: Proposition 26.1 records the primal/dual solution-set characterizations and the
  Douglas--Rachford / forward-backward fixed-point descriptions attached to a pair `(A, B)`.
- `core/canonical`: the reusable owners are the Chapter 26 solution sets together with the Chapter
  23 resolvent and Yosida realizers and the Chapter 4 Douglas--Rachford operator.
- `bridge/view`: the chapter-level reusable operators here are
  `reflectedResolventComposition` and `forwardBackwardSplittingOperator`, plus membership and
  fixed-point companion lemmas exposing the source statements in downstream-callable form. -/

noncomputable section

/-- Helper for Proposition 26.1: the Douglas--Rachford combination
`x ↦ T₁ (2 • T₂ x - x) + x - T₂ x` attached to two self-maps. -/
def douglasRachfordOperator
    {H : Type u} [AddCommGroup H] [Module ℝ H] (T₁ T₂ : H → H) : H → H :=
  fun x ↦ T₁ ((2 : ℝ) • T₂ x - x) + x - T₂ x

/-- Helper for Proposition 26.1: `douglasRachfordOperator` acts by the textbook formula. -/
theorem douglasRachfordOperator_apply
    {H : Type u} [AddCommGroup H] [Module ℝ H] (T₁ T₂ : H → H) (x : H) :
    douglasRachfordOperator T₁ T₂ x = T₁ ((2 : ℝ) • T₂ x - x) + x - T₂ x := rfl

/-- Helper for Proposition 26.1: whole-space firm nonexpansiveness is the univ-restriction form
of `FirmlyNonexpansiveOn`. -/
abbrev FirmlyNonexpansive
    {H : Type u} [NormedAddCommGroup H] (T : H → H) : Prop :=
  FirmlyNonexpansiveOn (Set.univ : Set H) T

/-- Helper for Proposition 26.1: a self-map and its reflected map have the same fixed points. -/
private lemma fixedPoints_reflectedMap_eq_fixedPoints
    {H : Type u} [AddCommGroup H] [Module ℝ H] [NoZeroSMulDivisors ℝ H] (T : H → H) :
    Function.fixedPoints (fun x ↦ (2 : ℝ) • T x - x) = Function.fixedPoints T := by
  ext y
  constructor
  · intro hy
    rw [Function.mem_fixedPoints_iff] at hy ⊢
    change (2 : ℝ) • T y - y = y at hy
    have hzero : (2 : ℝ) • (T y - y) = 0 := by
      calc
        (2 : ℝ) • (T y - y) = (2 : ℝ) • T y - (2 : ℝ) • y := by
          rw [smul_sub]
        _ = ((2 : ℝ) • T y - y) - y := by
          simp [two_smul, sub_eq_add_neg, add_assoc]
        _ = 0 := by
          rw [hy, sub_self]
    rcases smul_eq_zero.mp hzero with htwo | hsub
    · norm_num at htwo
    · exact sub_eq_zero.mp hsub
  · intro hy
    rw [Function.mem_fixedPoints_iff] at hy ⊢
    change T y = y at hy
    rw [hy]
    simp [two_smul]

/-- Helper for Proposition 26.1: the fixed points of the Douglas--Rachford combination coincide
with the fixed points of the composed reflected maps. -/
theorem fixedPoints_douglasRachfordOperator_eq_fixedPoints_reflected_comp
    {H : Type u} [AddCommGroup H] [Module ℝ H] [NoZeroSMulDivisors ℝ H] {T₁ T₂ : H → H} :
    Function.fixedPoints (douglasRachfordOperator T₁ T₂) =
      Function.fixedPoints ((fun x ↦ (2 : ℝ) • T₁ x - x) ∘ fun x ↦ (2 : ℝ) • T₂ x - x) := by
  -- Compare fixed points through the common reflected-map presentation.
  calc
    Function.fixedPoints (douglasRachfordOperator T₁ T₂) =
        Function.fixedPoints (fun x ↦ (2 : ℝ) • douglasRachfordOperator T₁ T₂ x - x) := by
          symm
          exact fixedPoints_reflectedMap_eq_fixedPoints _
    _ =
        Function.fixedPoints ((fun x ↦ (2 : ℝ) • T₁ x - x) ∘ fun x ↦ (2 : ℝ) • T₂ x - x) := by
          -- Expand the reflector of the Douglas--Rachford combination pointwise.
          ext x
          rw [Function.mem_fixedPoints_iff, Function.mem_fixedPoints_iff]
          simp [douglasRachfordOperator, two_smul, sub_eq_add_neg, add_assoc, add_left_comm,
            add_comm]

section AddGroup

/-- Part (1) of Proposition 26.1: the primal solution set consists exactly
of those `x` admitting a dual witness `u` with `-u ∈ A x` and `u ∈ B x`. -/
theorem primal_inclusion_solution_set_eq_setOf_exists_mem_dual_inclusion_solution_set
    {H : Type u} [AddGroup H]
    (A B : SetValuedOperator H H) :
    primal_inclusion_solution_set A B =
      {x : H | ∃ u ∈ dual_inclusion_solution_set A B, -u ∈ A x ∧ u ∈ B x} := by
  ext x
  constructor
  · intro hx
    -- Unpack the primal inclusion `0 ∈ A x + B x` into a witness `u ∈ B x`.
    rw [mem_primal_inclusion_solution_set, Set.mem_add] at hx
    rcases hx with ⟨v, hv, u, hu, hvu⟩
    have hv_eq : v = -u := by
      simpa [eq_neg_iff_add_eq_zero] using hvu
    refine ⟨u, ?_, ?_, hu⟩
    · -- The same pair `(x, u)` witnesses membership in the dual inclusion set.
      rw [mem_dual_inclusion_solution_set, Set.mem_add]
      refine ⟨-x, ?_, x, ?_, by simp⟩
      · have hxInv : x ∈ A⁻¹ (-u) := by
          simpa [mem_inverse_iff, hv_eq] using hv
        simpa using hxInv
      · simpa [mem_inverse_iff] using hu
    · simpa [hv_eq] using hv
  · rintro ⟨u, _huD, hAu, hBu⟩
    -- Repackage the dual witness back into `0 ∈ A x + B x`.
    rw [mem_primal_inclusion_solution_set, Set.mem_add]
    exact ⟨-u, hAu, u, hBu, by simp⟩

/-- Membership reformulation of Proposition 26.1 (1). -/
theorem mem_primal_inclusion_solution_set_iff_exists_mem_dual_inclusion_solution_set
    {H : Type u} [AddGroup H] (A B : SetValuedOperator H H) {x : H} :
    x ∈ primal_inclusion_solution_set A B ↔
      ∃ u ∈ dual_inclusion_solution_set A B, -u ∈ A x ∧ u ∈ B x := by
  rw [primal_inclusion_solution_set_eq_setOf_exists_mem_dual_inclusion_solution_set]
  rfl

/-- Part (2) of Proposition 26.1: the dual solution set consists exactly
of those `u` admitting a primal witness `x` with `x ∈ A⁻¹(-u)` and
`x ∈ B⁻¹ u`. -/
theorem dual_inclusion_solution_set_eq_setOf_exists_mem_primal_inclusion_solution_set
    {H : Type u} [AddGroup H]
    (A B : SetValuedOperator H H) :
    dual_inclusion_solution_set A B =
      {u : H |
        ∃ x ∈ primal_inclusion_solution_set A B, x ∈ A⁻¹ (-u) ∧ x ∈ B⁻¹ u} := by
  ext u
  constructor
  · intro hu
    -- Unpack the dual inclusion `0 ∈ -A⁻¹(-u) + B⁻¹ u`.
    rw [mem_dual_inclusion_solution_set, Set.mem_add] at hu
    rcases hu with ⟨y, hy, x, hx, hyx⟩
    have hy_eq : y = -x := by
      simpa [eq_neg_iff_add_eq_zero] using hyx
    refine ⟨x, ?_, ?_, hx⟩
    · -- The same pair `(x, u)` yields a primal solution.
      rw [mem_primal_inclusion_solution_set, Set.mem_add]
      refine ⟨-u, ?_, u, ?_, by simp⟩
      · simpa [mem_inverse_iff, hy_eq] using hy
      · simpa [mem_inverse_iff] using hx
    · simpa [mem_inverse_iff, hy_eq] using hy
  · rintro ⟨x, _hxP, hAx, hBx⟩
    -- Repackage the primal witness into `0 ∈ -A⁻¹(-u) + B⁻¹ u`.
    rw [mem_dual_inclusion_solution_set, Set.mem_add]
    refine ⟨-x, ?_, x, hBx, by simp⟩
    simpa [mem_inverse_iff] using hAx

/-- Membership reformulation of Proposition 26.1 (2). -/
theorem mem_dual_inclusion_solution_set_iff_exists_mem_primal_inclusion_solution_set
    {H : Type u} [AddGroup H] (A B : SetValuedOperator H H) {u : H} :
    u ∈ dual_inclusion_solution_set A B ↔
      ∃ x ∈ primal_inclusion_solution_set A B, x ∈ A⁻¹ (-u) ∧ x ∈ B⁻¹ u := by
  rw [dual_inclusion_solution_set_eq_setOf_exists_mem_primal_inclusion_solution_set]
  rfl

end AddGroup

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Part (3) of Proposition 26.1: when `A` is the normal cone to a closed
affine subspace `C`, the primal solution set is the set of points `x ∈ C`
for which some vector of `B x` lies in `C.directionᗮ`. -/
theorem primal_inclusion_solution_set_normalCone_affine_eq_setOf_exists_mem_orthogonal
    (C : AffineSubspace ℝ H) (B : SetValuedOperator H H) :
    primal_inclusion_solution_set N[(C : Set H)] B =
      {x : H |
        x ∈ (C : Set H) ∧ ∃ u ∈ (C.directionᗮ : Set H), u ∈ B x} := by
  ext x
  constructor
  · intro hx
    -- Unpack the primal inclusion and use the affine normal-cone formula at `x`.
    rw [mem_primal_inclusion_solution_set, Set.mem_add] at hx
    rcases hx with ⟨v, hv, u, hu, hvu⟩
    have hv_eq : v = -u := by
      simpa [eq_neg_iff_add_eq_zero] using hvu
    have hxC : x ∈ (C : Set H) := by
      by_contra hxC
      rw [normalCone_affineSubspace_eq_empty_of_not_mem C hxC] at hv
      exact hv.elim
    have hu_orth : u ∈ (C.directionᗮ : Set H) := by
      have hneg_orth : -u ∈ (C.directionᗮ : Set H) := by
        simpa [normalCone_affineSubspace_eq_direction_orthogonal_of_mem C hxC, hv_eq] using hv
      simpa using Submodule.neg_mem (C.directionᗮ) hneg_orth
    exact ⟨hxC, u, hu_orth, hu⟩
  · rintro ⟨hxC, u, hu_orth, hu⟩
    -- Turn the orthogonality condition back into the normal-cone membership `-u ∈ N_C x`.
    rw [mem_primal_inclusion_solution_set, Set.mem_add]
    refine ⟨-u, ?_, u, hu, by simp⟩
    have hneg_orth : -u ∈ (C.directionᗮ : Set H) := by
      simpa using Submodule.neg_mem (C.directionᗮ) hu_orth
    simpa [normalCone_affineSubspace_eq_direction_orthogonal_of_mem C hxC] using hneg_orth

/-- Membership reformulation of Proposition 26.1 (3). -/
theorem mem_primal_inclusion_solution_set_normalCone_affine_iff_exists_mem_orthogonal
    (C : AffineSubspace ℝ H) (B : SetValuedOperator H H) {x : H} :
    x ∈ primal_inclusion_solution_set N[(C : Set H)] B ↔
      x ∈ (C : Set H) ∧ ∃ u ∈ (C.directionᗮ : Set H), u ∈ B x := by
  rw [primal_inclusion_solution_set_normalCone_affine_eq_setOf_exists_mem_orthogonal]
  rfl

/-- Part (4) of Proposition 26.1: when `A` is the normal cone to a closed
affine subspace `C`, the dual solution set is the set of vectors
`u ∈ C.directionᗮ` for which some point of `C` belongs to `B⁻¹ u`. -/
theorem dual_inclusion_solution_set_normalCone_affine_eq_setOf_exists_mem_orthogonal
    (C : AffineSubspace ℝ H) (B : SetValuedOperator H H) :
    dual_inclusion_solution_set N[(C : Set H)] B =
      {u : H |
        u ∈ (C.directionᗮ : Set H) ∧ ∃ x ∈ (C : Set H), x ∈ B⁻¹ u} := by
  ext u
  constructor
  · intro hu
    -- Use the dual witness characterization and then specialize the normal cone of `C`.
    rcases (mem_dual_inclusion_solution_set_iff_exists_mem_primal_inclusion_solution_set
      N[(C : Set H)] B).1 hu with ⟨x, _hxP, hAx, hBx⟩
    have hneg_mem : -u ∈ N[(C : Set H)] x := by
      simpa [mem_inverse_iff] using hAx
    have hxC : x ∈ (C : Set H) := by
      by_contra hxC
      rw [normalCone_affineSubspace_eq_empty_of_not_mem C hxC] at hneg_mem
      exact hneg_mem.elim
    have hu_orth : u ∈ (C.directionᗮ : Set H) := by
      have hneg_orth : -u ∈ (C.directionᗮ : Set H) := by
        simpa [normalCone_affineSubspace_eq_direction_orthogonal_of_mem C hxC] using hneg_mem
      simpa using Submodule.neg_mem (C.directionᗮ) hneg_orth
    exact ⟨hu_orth, x, hxC, hBx⟩
  · rintro ⟨hu_orth, x, hxC, hBx⟩
    -- Rebuild the dual inclusion from the normal-cone identity at the chosen point `x ∈ C`.
    rw [mem_dual_inclusion_solution_set, Set.mem_add]
    refine ⟨-x, ?_, x, hBx, by simp⟩
    have hneg_orth : -u ∈ (C.directionᗮ : Set H) := by
      simpa using Submodule.neg_mem (C.directionᗮ) hu_orth
    have hAx : x ∈ N[(C : Set H)]⁻¹ (-u) := by
      simpa [mem_inverse_iff, normalCone_affineSubspace_eq_direction_orthogonal_of_mem C hxC]
        using hneg_orth
    simpa using hAx

/-- Membership reformulation of Proposition 26.1 (4). -/
theorem mem_dual_inclusion_solution_set_normalCone_affine_iff_exists_mem_orthogonal
    (C : AffineSubspace ℝ H) (B : SetValuedOperator H H) {u : H} :
    u ∈ dual_inclusion_solution_set N[(C : Set H)] B ↔
      u ∈ (C.directionᗮ : Set H) ∧ ∃ x ∈ (C : Set H), x ∈ B⁻¹ u := by
  rw [dual_inclusion_solution_set_normalCone_affine_eq_setOf_exists_mem_orthogonal]
  rfl

end Hilbert

section HilbertComplete

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The reflected-resolvent composition `R_{γA} ∘ R_{γB}`. -/
def reflectedResolventComposition
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) : H → H :=
  (fun x ↦ (2 : ℝ) • resolventMap A hA γ x - x) ∘
    fun x ↦ (2 : ℝ) • resolventMap B hB γ x - x

/-- The reflected-resolvent composition acts by the explicit two-step reflector formula. -/
theorem reflectedResolventComposition_apply
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (x : H) :
    reflectedResolventComposition A B hA hB γ x =
      (2 : ℝ) • resolventMap A hA γ ((2 : ℝ) • resolventMap B hB γ x - x) -
        ((2 : ℝ) • resolventMap B hB γ x - x) := rfl

/-- The Douglas--Rachford operator built from the two resolvents and the reflected-resolvent
composition have the same fixed-point set. -/
theorem fixedPoints_douglasRachfordOperator_resolvent_eq_fixedPoints_reflectedResolventComposition
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) :
    fixedPoints (douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ)) =
      fixedPoints (reflectedResolventComposition A B hA hB γ) := by
  have hfix :
      fixedPoints (douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ)) =
        fixedPoints
          ((fun x ↦ (2 : ℝ) • resolventMap A hA γ x - x) ∘
            fun x ↦ (2 : ℝ) • resolventMap B hB γ x - x) :=
    fixedPoints_douglasRachfordOperator_eq_fixedPoints_reflected_comp
  simpa [reflectedResolventComposition] using hfix

/-- Helper for Proposition 26.1: `J_{γB} (x + γ • u) = x` exactly when `u ∈ B x`. -/
theorem resolventMap_add_smul_eq_iff_mem
    (B : SetValuedOperator H H) (hB : Maximal IsMonotone B) (γ : PosReal) (x u : H) :
    resolventMap B hB γ (x + (γ : ℝ) • u) = x ↔ u ∈ B x := by
  have hresidual : (x + (γ : ℝ) • u) - x = (γ : ℝ) • u := by
    abel_nf
  constructor
  · intro h
    -- Turn the equality into resolvent membership, then read off the residual.
    have hxmem : x ∈ J[((γ : ℝ) • B)] (x + (γ : ℝ) • u) := by
      rw [resolvent_smul_eq_singleton_resolventMap_of_maximal B hB γ (x + (γ : ℝ) • u)]
      simp [h]
    have hscaled :
        (x + (γ : ℝ) • u) - x ∈ (γ : ℝ) • B x :=
      (mem_resolvent_smul_iff_sub_mem_smul B γ (x + (γ : ℝ) • u) x).1 hxmem
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hscaled
    simpa [hresidual, smul_smul, inv_mul_cancel₀ γ.2.ne'] using hscaled
  · intro hu
    -- Package `u ∈ B x` as the canonical resolvent point `x ∈ J_{γB}(x + γ • u)`.
    have hscaled : (γ : ℝ) • u ∈ (γ : ℝ) • B x := Set.smul_mem_smul_set hu
    have hxmem : x ∈ J[((γ : ℝ) • B)] (x + (γ : ℝ) • u) := by
      refine (mem_resolvent_smul_iff_sub_mem_smul B γ (x + (γ : ℝ) • u) x).2 ?_
      simpa [hresidual] using hscaled
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal B hB γ (x + (γ : ℝ) • u)] at hxmem
    simpa using hxmem.symm

/-- Helper for Proposition 26.1: `J_{γA} (x - γ • u) = x` exactly when `-u ∈ A x`. -/
theorem resolventMap_sub_smul_eq_iff_neg_mem
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal) (x u : H) :
    resolventMap A hA γ (x - (γ : ℝ) • u) = x ↔ -u ∈ A x := by
  have hresidual : (x - (γ : ℝ) • u) - x = (γ : ℝ) • (-u) := by
    rw [smul_neg]
    abel_nf
  constructor
  · intro h
    -- Turn the equality into resolvent membership, then read off the residual.
    have hxmem : x ∈ J[((γ : ℝ) • A)] (x - (γ : ℝ) • u) := by
      rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ (x - (γ : ℝ) • u)]
      simp [h]
    have hscaled :
        (x - (γ : ℝ) • u) - x ∈ (γ : ℝ) • A x :=
      (mem_resolvent_smul_iff_sub_mem_smul A γ (x - (γ : ℝ) • u) x).1 hxmem
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hscaled
    simpa [hresidual, smul_smul, inv_mul_cancel₀ γ.2.ne'] using hscaled
  · intro hu
    -- Package `-u ∈ A x` as the canonical resolvent point `x ∈ J_{γA}(x - γ • u)`.
    have hscaled : (γ : ℝ) • (-u) ∈ (γ : ℝ) • A x := Set.smul_mem_smul_set hu
    have hxmem : x ∈ J[((γ : ℝ) • A)] (x - (γ : ℝ) • u) := by
      refine (mem_resolvent_smul_iff_sub_mem_smul A γ (x - (γ : ℝ) • u) x).2 ?_
      simpa [hresidual] using hscaled
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal A hA γ (x - (γ : ℝ) • u)] at hxmem
    simpa using hxmem.symm

/-- Helper for Proposition 26.1: every point decomposes as
`y = J_{γB} y + γ • {}^γ B y`, realized by the canonical resolvent and Yosida maps. -/
theorem eq_resolventMap_add_smul_yosidaApproximationMap
    (B : SetValuedOperator H H) (hB : Maximal IsMonotone B) (γ : PosReal) (y : H) :
    y = resolventMap B hB γ y + (γ : ℝ) • yosidaApproximationMap B hB γ y := by
  -- Expand the Yosida realizer and simplify the scaled residual.
  rw [yosidaApproximationMap_apply]
  calc
    y = resolventMap B hB γ y + (y - resolventMap B hB γ y) := by
      abel_nf
    _ = resolventMap B hB γ y + (γ : ℝ) • ((γ : ℝ)⁻¹ • (y - resolventMap B hB γ y)) := by
      simp [smul_smul, mul_inv_cancel₀ γ.2.ne']

/-- Helper for Proposition 26.1: the reflected resolvent argument simplifies to
`J_{γB} y - γ • {}^γ B y`. -/
theorem two_smul_resolventMap_sub_eq_sub_smul_yosidaApproximationMap
    (B : SetValuedOperator H H) (hB : Maximal IsMonotone B) (γ : PosReal) (y : H) :
    (2 : ℝ) • resolventMap B hB γ y - y =
      resolventMap B hB γ y - (γ : ℝ) • yosidaApproximationMap B hB γ y := by
  -- Substitute the decomposition `y = J_{γB} y + γ • {}^γ B y` and normalize.
  let x := resolventMap B hB γ y
  let u := yosidaApproximationMap B hB γ y
  have hy : y = x + (γ : ℝ) • u := by
    simpa [x, u] using eq_resolventMap_add_smul_yosidaApproximationMap B hB γ y
  calc
    (2 : ℝ) • resolventMap B hB γ y - y = (2 : ℝ) • x - y := by rfl
    _ = (2 : ℝ) • x - (x + (γ : ℝ) • u) := by rw [hy]
    _ = x - (γ : ℝ) • u := by
      simp [two_smul, sub_eq_add_neg, add_assoc]
    _ = resolventMap B hB γ y - (γ : ℝ) • yosidaApproximationMap B hB γ y := by rfl

/-- Helper for Proposition 26.1: a fixed point of `R_{γA} ∘ R_{γB}` is equivalently a point
where the two canonical resolvent outputs agree. -/
theorem mem_fixedPoints_reflectedResolventComposition_iff_resolventMap_eq
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (y : H) :
    y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ) ↔
      resolventMap A hA γ ((2 : ℝ) • resolventMap B hB γ y - y) =
        resolventMap B hB γ y := by
  -- Normalize the fixed-point equation to the reflected resolvent equality.
  rw [Function.mem_fixedPoints_iff, reflectedResolventComposition_apply]
  let a := resolventMap A hA γ ((2 : ℝ) • resolventMap B hB γ y - y)
  let b := resolventMap B hB γ y
  change (2 : ℝ) • a - ((2 : ℝ) • b - y) = y ↔ a = b
  constructor
  · intro hy
    have hzero : (2 : ℝ) • (a - b) = 0 := by
      have hy' : (2 : ℝ) • a - ((2 : ℝ) • b - y) - y = 0 := by
        rw [hy, sub_self]
      calc
        (2 : ℝ) • (a - b) = (2 : ℝ) • a - ((2 : ℝ) • b - y) - y := by
          rw [smul_sub]
          abel_nf
        _ = 0 := hy'
    rcases smul_eq_zero.mp hzero with htwo | hab
    · norm_num at htwo
    · exact sub_eq_zero.mp hab
  · intro hab
    rw [hab]
    abel_nf

/-- Helper for Proposition 26.1: on the whole space, firm nonexpansiveness is equivalent to the
`LipschitzWith 1` condition for the reflected map `x ↦ 2 • T x - x`. -/
private theorem firmlyNonexpansive_iff_lipschitzWithOne_reflectedMap
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {T : H → H} :
    FirmlyNonexpansive T ↔ LipschitzWith 1 (fun x ↦ (2 : ℝ) • T x - x) := by
  constructor
  · intro hT
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    have hfirm :
        ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 :=
      (firmlyNonexpansiveOn_iff).1 hT x (by simp) y (by simp)
    have hnorm_residual :
        ‖(x - y) - (T x - T y)‖ ^ 2 =
          ‖x - y‖ ^ 2 - 2 * inner ℝ (x - y) (T x - T y) + ‖T x - T y‖ ^ 2 := by
      simpa [sub_eq_add_neg] using norm_sub_sq_real (x - y) (T x - T y)
    have hinner_bound :
        ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y) := by
      have hresidual :
          ‖(x - T x) - (y - T y)‖ ^ 2 = ‖(x - y) - (T x - T y)‖ ^ 2 := by
        congr 1
        abel_nf
      have hinner_comm :
          inner ℝ (x - y) (T x - T y) = inner ℝ (T x - T y) (x - y) := by
        rw [real_inner_comm]
      nlinarith [hfirm, hnorm_residual, hresidual, hinner_comm]
    have hnorm :
        ‖(x - y) - (2 : ℝ) • (T x - T y)‖ ^ 2 =
          ‖x - y‖ ^ 2 - 2 * inner ℝ (x - y) ((2 : ℝ) • (T x - T y)) +
            ‖(2 : ℝ) • (T x - T y)‖ ^ 2 := by
      simpa [sub_eq_add_neg] using norm_sub_sq_real (x - y) ((2 : ℝ) • (T x - T y))
    have hinner_two :
        inner ℝ (x - y) ((2 : ℝ) • (T x - T y)) = 2 * inner ℝ (T x - T y) (x - y) := by
      rw [real_inner_smul_right, real_inner_comm]
    have hnormsmul : ‖(2 : ℝ) • (T x - T y)‖ ^ 2 = 4 * ‖T x - T y‖ ^ 2 := by
      rw [norm_smul, Real.norm_ofNat, pow_two]
      ring
    have hsq :
        ‖(x - y) - (2 : ℝ) • (T x - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      nlinarith [hinner_bound, hnorm, hinner_two, hnormsmul]
    have hreflect :
        ‖(2 : ℝ) • (T x - T y) - (x - y)‖ ≤ ‖x - y‖ := by
      have hsq' :
          ‖(2 : ℝ) • (T x - T y) - (x - y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
        simpa [norm_sub_rev] using hsq
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq'
    simpa [dist_eq_norm, one_mul, sub_eq_add_neg, two_smul, add_assoc, add_left_comm, add_comm]
      using hreflect
  · intro hR
    refine (firmlyNonexpansiveOn_iff).2 ?_
    intro x _hx y _hy
    have hreflect :
        ‖(2 : ℝ) • (T x - T y) - (x - y)‖ ≤ ‖x - y‖ := by
      simpa [dist_eq_norm, one_mul, sub_eq_add_neg, two_smul, add_assoc, add_left_comm, add_comm]
        using hR.dist_le_mul x y
    have hsq :
        ‖(2 : ℝ) • (T x - T y) - (x - y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hreflect
    have hnorm :
        ‖(2 : ℝ) • (T x - T y) - (x - y)‖ ^ 2 =
          ‖x - y‖ ^ 2 - 2 * inner ℝ ((2 : ℝ) • (T x - T y)) (x - y) +
            ‖(2 : ℝ) • (T x - T y)‖ ^ 2 := by
      calc
        ‖(2 : ℝ) • (T x - T y) - (x - y)‖ ^ 2
            = ‖(2 : ℝ) • (T x - T y)‖ ^ 2 -
                2 * inner ℝ ((2 : ℝ) • (T x - T y)) (x - y) + ‖x - y‖ ^ 2 := by
                  simpa [sub_eq_add_neg] using
                    norm_sub_sq_real ((2 : ℝ) • (T x - T y)) (x - y)
        _ = ‖x - y‖ ^ 2 - 2 * inner ℝ ((2 : ℝ) • (T x - T y)) (x - y) +
              ‖(2 : ℝ) • (T x - T y)‖ ^ 2 := by
                ring
    have hinner :
        inner ℝ ((2 : ℝ) • (T x - T y)) (x - y) = 2 * inner ℝ (T x - T y) (x - y) := by
      rw [real_inner_smul_left]
    have hnormsmul : ‖(2 : ℝ) • (T x - T y)‖ ^ 2 = 4 * ‖T x - T y‖ ^ 2 := by
      rw [norm_smul, Real.norm_ofNat, pow_two]
      ring
    have hinner_bound :
        ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y) := by
      nlinarith [hsq, hnorm, hinner, hnormsmul]
    have hnorm_residual :
        ‖(x - y) - (T x - T y)‖ ^ 2 =
          ‖x - y‖ ^ 2 - 2 * inner ℝ (x - y) (T x - T y) + ‖T x - T y‖ ^ 2 := by
      simpa [sub_eq_add_neg] using norm_sub_sq_real (x - y) (T x - T y)
    have hresidual :
        ‖(x - T x) - (y - T y)‖ ^ 2 = ‖(x - y) - (T x - T y)‖ ^ 2 := by
      congr 1
      abel_nf
    have hinner_comm :
        inner ℝ (x - y) (T x - T y) = inner ℝ (T x - T y) (x - y) := by
      rw [real_inner_comm]
    nlinarith [hinner_bound, hnorm_residual, hresidual, hinner_comm]

/-- Helper for Proposition 26.1: the reflector of the local Douglas--Rachford operator is the
composition of the two reflected maps. -/
theorem reflected_douglasRachfordOperator_eq_comp_reflectedMap_local
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {T₁ T₂ : H → H} :
    (fun x ↦ (2 : ℝ) • douglasRachfordOperator T₁ T₂ x - x) =
      (fun x ↦ (2 : ℝ) • T₁ x - x) ∘ fun x ↦ (2 : ℝ) • T₂ x - x := by
  -- Expand the Douglas--Rachford formula and collect terms on both sides.
  funext x
  simp [douglasRachfordOperator, two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Part (5) of Proposition 26.1: if `A` and `B` are maximally monotone, then the Douglas--Rachford
splitting operator `T_{γA,γB}` is firmly nonexpansive. -/
theorem douglasRachfordSplittingOperator_firmlyNonexpansive
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) :
    FirmlyNonexpansive
      (douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ)) := by
  -- Proposition 4.31 applies to the two whole-space resolvent realizers.
  have hresA : FirmlyNonexpansive (resolventMap A hA γ) := by
    simpa using resolventMap_firmlyNonexpansiveOn_univ A hA γ
  have hresB : FirmlyNonexpansive (resolventMap B hB γ) := by
    simpa using resolventMap_firmlyNonexpansiveOn_univ B hB γ
  rw [firmlyNonexpansive_iff_lipschitzWithOne_reflectedMap]
  have hR₁ :
      LipschitzWith 1 (fun x ↦ (2 : ℝ) • resolventMap A hA γ x - x) :=
    firmlyNonexpansive_iff_lipschitzWithOne_reflectedMap.1 hresA
  have hR₂ :
      LipschitzWith 1 (fun x ↦ (2 : ℝ) • resolventMap B hB γ x - x) :=
    firmlyNonexpansive_iff_lipschitzWithOne_reflectedMap.1 hresB
  -- Expand the reflector of the Douglas--Rachford combination pointwise.
  simpa [reflected_douglasRachfordOperator_eq_comp_reflectedMap_local] using hR₁.comp hR₂

/-- Proposition 26.1 (6): if `A` and `B` are maximally monotone, then the primal solution set is
the image of the fixed-point set of `R_{γA} ∘ R_{γB}` under `J_{γB}`. -/
theorem primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) :
    primal_inclusion_solution_set A B =
      resolventMap B hB γ '' fixedPoints (reflectedResolventComposition A B hA hB γ) := by
  ext x
  constructor
  · intro hx
    -- Extract the primal witness `u` and package it as `y = x + γ • u`.
    rcases (mem_primal_inclusion_solution_set_iff_exists_mem_dual_inclusion_solution_set
      A B).1 hx with ⟨u, _huD, hAu, hBu⟩
    let y : H := x + (γ : ℝ) • u
    have hresB : resolventMap B hB γ y = x := by
      simpa [y] using (resolventMap_add_smul_eq_iff_mem B hB γ x u).2 hBu
    have hargA : (2 : ℝ) • resolventMap B hB γ y - y = x - (γ : ℝ) • u := by
      rw [hresB]
      dsimp [y]
      simp [two_smul, sub_eq_add_neg, add_assoc]
    have hyfix :
        y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ) := by
      -- Route correction: normalize the fixed-point condition to the canonical resolvent equality.
      rw [mem_fixedPoints_reflectedResolventComposition_iff_resolventMap_eq A B hA hB γ y]
      calc
        resolventMap A hA γ ((2 : ℝ) • resolventMap B hB γ y - y)
            = resolventMap A hA γ (x - (γ : ℝ) • u) := by rw [hargA]
        _ = x := (resolventMap_sub_smul_eq_iff_neg_mem A hA γ x u).2 hAu
        _ = resolventMap B hB γ y := hresB.symm
    exact ⟨y, hyfix, hresB⟩
  · rintro ⟨y, hyfix, rfl⟩
    -- Read the fixed-point equation through the Yosida witness `u`.
    let x : H := resolventMap B hB γ y
    let u : H := yosidaApproximationMap B hB γ y
    have hu_mem : u ∈ ({}^[γ] B) y := by
      rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal B hB γ y]
      simp [u]
    have hy_decomp : y = x + (γ : ℝ) • u := by
      -- Recover the textbook decomposition `y = x + γ • u`.
      simpa [x, u] using eq_resolventMap_add_smul_yosidaApproximationMap B hB γ y
    have hBu : u ∈ B x := by
      have hBu' : u ∈ B (y - (γ : ℝ) • u) :=
        (mem_yosidaApproximation_iff_mem B γ y u).1 hu_mem
      have hbase : y - (γ : ℝ) • u = x := by
        rw [hy_decomp]
        abel_nf
      simpa [hbase] using hBu'
    have hargA : (2 : ℝ) • x - y = x - (γ : ℝ) • u := by
      simpa [x, u] using
        two_smul_resolventMap_sub_eq_sub_smul_yosidaApproximationMap B hB γ y
    have hAu : -u ∈ A x := by
      have hresA :
          resolventMap A hA γ ((2 : ℝ) • x - y) = x := by
        have hyfix' := (mem_fixedPoints_reflectedResolventComposition_iff_resolventMap_eq
          A B hA hB γ y).1 hyfix
        simpa [x] using hyfix'
      rw [hargA] at hresA
      exact (resolventMap_sub_smul_eq_iff_neg_mem A hA γ x u).1 hresA
    -- Reassemble `0 ∈ A x + B x` from the two witness memberships.
    rw [mem_primal_inclusion_solution_set, Set.mem_add]
    exact ⟨-u, hAu, u, hBu, by simp⟩

/-- Part (7) of Proposition 26.1: if `A` and `B` are maximally monotone,
then the primal solution set is the image of the fixed-point set of the
Douglas--Rachford splitting operator under `J_{γB}`. -/
theorem primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_douglasRachford
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) :
    primal_inclusion_solution_set A B =
      resolventMap B hB γ ''
        fixedPoints (douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ)) :=
          by
  -- Transport the reflected-resolvent image formula across the fixed-point equality.
  have hprimalImage :=
    primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
      A B hA hB γ
  have hfix :=
    fixedPoints_douglasRachfordOperator_resolvent_eq_fixedPoints_reflectedResolventComposition
      A B hA hB γ
  calc
    primal_inclusion_solution_set A B =
        resolventMap B hB γ '' fixedPoints (reflectedResolventComposition A B hA hB γ) := by
          exact hprimalImage
    _ = resolventMap B hB γ ''
        fixedPoints (douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ)) := by
          rw [← hfix]

/-- Part (8) of Proposition 26.1: if `A` and `B` are maximally monotone,
then the dual solution set is the image of the fixed-point set of
`R_{γA} ∘ R_{γB}` under `{}^[γ] B`, realized by `yosidaApproximationMap B γ`. -/
theorem dual_inclusion_solution_set_eq_image_yosida_fixedPoints_reflectedResolventComposition
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) :
    dual_inclusion_solution_set A B =
      yosidaApproximationMap B hB γ '' fixedPoints (reflectedResolventComposition A B hA hB γ) :=
        by
  ext u
  constructor
  · intro hu
    -- Extract the primal witness `x` attached to the dual point `u`.
    rcases (mem_dual_inclusion_solution_set_iff_exists_mem_primal_inclusion_solution_set
      A B).1 hu with ⟨x, _hxP, hAx, hBx⟩
    have hAu : -u ∈ A x := by
      simpa [mem_inverse_iff] using hAx
    have hBu : u ∈ B x := by
      simpa [mem_inverse_iff] using hBx
    let y : H := x + (γ : ℝ) • u
    have hresB : resolventMap B hB γ y = x := by
      simpa [y] using (resolventMap_add_smul_eq_iff_mem B hB γ x u).2 hBu
    have hargA : (2 : ℝ) • resolventMap B hB γ y - y = x - (γ : ℝ) • u := by
      rw [hresB]
      dsimp [y]
      simp [two_smul, sub_eq_add_neg, add_assoc]
    have hyfix :
        y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ) := by
      -- Normalize the fixed-point condition to the canonical resolvent equality.
      rw [mem_fixedPoints_reflectedResolventComposition_iff_resolventMap_eq A B hA hB γ y]
      calc
        resolventMap A hA γ ((2 : ℝ) • resolventMap B hB γ y - y)
            = resolventMap A hA γ (x - (γ : ℝ) • u) := by rw [hargA]
        _ = x := (resolventMap_sub_smul_eq_iff_neg_mem A hA γ x u).2 hAu
        _ = resolventMap B hB γ y := hresB.symm
    have hyos : yosidaApproximationMap B hB γ y = u := by
      -- The Yosida value is the scaled residual `γ⁻¹ • (y - x)`.
      have hresidual : y - x = (γ : ℝ) • u := by
        dsimp [y]
        abel_nf
      calc
        yosidaApproximationMap B hB γ y
            = (γ : ℝ)⁻¹ • (y - resolventMap B hB γ y) := by
                rw [yosidaApproximationMap_apply]
        _ = (γ : ℝ)⁻¹ • ((γ : ℝ) • u) := by rw [hresB, hresidual]
        _ = u := by simp [smul_smul, inv_mul_cancel₀ γ.2.ne']
    exact ⟨y, hyfix, hyos⟩
  · rintro ⟨y, hyfix, rfl⟩
    -- Recover the primal-dual witness pair from the fixed point and its Yosida value.
    let x : H := resolventMap B hB γ y
    let u : H := yosidaApproximationMap B hB γ y
    have hu_mem : u ∈ ({}^[γ] B) y := by
      rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal B hB γ y]
      simp [u]
    have hy_decomp : y = x + (γ : ℝ) • u := by
      simpa [x, u] using eq_resolventMap_add_smul_yosidaApproximationMap B hB γ y
    have hBu : u ∈ B x := by
      have hBu' : u ∈ B (y - (γ : ℝ) • u) :=
        (mem_yosidaApproximation_iff_mem B γ y u).1 hu_mem
      have hbase : y - (γ : ℝ) • u = x := by
        rw [hy_decomp]
        abel_nf
      simpa [hbase] using hBu'
    have hargA : (2 : ℝ) • x - y = x - (γ : ℝ) • u := by
      simpa [x, u] using
        two_smul_resolventMap_sub_eq_sub_smul_yosidaApproximationMap B hB γ y
    have hAu : -u ∈ A x := by
      have hresA :
          resolventMap A hA γ ((2 : ℝ) • x - y) = x := by
        have hyfix' := (mem_fixedPoints_reflectedResolventComposition_iff_resolventMap_eq
          A B hA hB γ y).1 hyfix
        simpa [x] using hyfix'
      rw [hargA] at hresA
      exact (resolventMap_sub_smul_eq_iff_neg_mem A hA γ x u).1 hresA
    have hAinv : x ∈ A⁻¹ (-u) := by
      simpa [mem_inverse_iff] using hAu
    have hBinv : x ∈ B⁻¹ u := by
      simpa [mem_inverse_iff] using hBu
    -- Reassemble `0 ∈ -A⁻¹(-u) + B⁻¹ u` from the same witness `x`.
    rw [mem_dual_inclusion_solution_set, Set.mem_add]
    exact ⟨-x, by simpa using hAinv, x, hBinv, by simp⟩

/-- Part (9) of Proposition 26.1: if `A` and `B` are maximally monotone,
then the dual solution set is the image of the fixed-point set of the
Douglas--Rachford splitting operator under `{}^[γ] B`, realized by
`yosidaApproximationMap B γ`. -/
theorem dual_inclusion_solution_set_eq_image_yosida_fixedPoints_douglasRachford
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) :
    dual_inclusion_solution_set A B =
      yosidaApproximationMap B hB γ ''
        fixedPoints (douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ)) :=
          by
  -- Transport the reflected-resolvent image formula across the fixed-point equality.
  have hdualImage :=
    dual_inclusion_solution_set_eq_image_yosida_fixedPoints_reflectedResolventComposition
      A B hA hB γ
  have hfix :=
    fixedPoints_douglasRachfordOperator_resolvent_eq_fixedPoints_reflectedResolventComposition
      A B hA hB γ
  calc
    dual_inclusion_solution_set A B =
        yosidaApproximationMap B hB γ ''
          fixedPoints (reflectedResolventComposition A B hA hB γ) := by
            exact hdualImage
    _ = yosidaApproximationMap B hB γ ''
        fixedPoints (douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ)) := by
          rw [← hfix]

end HilbertComplete

section AddGroup

variable {H : Type u} [AddGroup H]

-- Textbook typo note: in part `(iii)(d)`, the first nonemptiness condition must be the primal set
-- `𝓟`, consistent with parts `(iii)(b)` and `(iii)(c)`.

/-- Part (10) of Proposition 26.1: the primal and dual inclusion solution sets are simultaneously
nonempty. This equivalence does not depend on the Douglas--Rachford hypotheses. -/
theorem primal_inclusion_solution_set_nonempty_iff_dual_inclusion_solution_set_nonempty
    (A B : SetValuedOperator H H) :
    (primal_inclusion_solution_set A B).Nonempty ↔
      (dual_inclusion_solution_set A B).Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    -- Extract the dual witness supplied by the primal characterization.
    rcases (mem_primal_inclusion_solution_set_iff_exists_mem_dual_inclusion_solution_set
      A B).1 hx with ⟨u, hu, _hAu, _hBu⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    -- Extract the primal witness supplied by the dual characterization.
    rcases (mem_dual_inclusion_solution_set_iff_exists_mem_primal_inclusion_solution_set
      A B).1 hu with ⟨x, hx, _hAx, _hBx⟩
    exact ⟨x, hx⟩

end AddGroup

section HilbertComplete

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Part (11) of Proposition 26.1: in the Douglas--Rachford setting, the
dual solution set is nonempty if and only if the Douglas--Rachford
splitting operator has a fixed point. -/
-- TODO: combine the dual image formula from part (9) with the general primal/dual nonempty
-- equivalence proved above.
theorem dual_nonempty_iff_fixedPoints_douglasRachfordSplittingOperator_nonempty
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) :
    (dual_inclusion_solution_set A B).Nonempty ↔
      (fixedPoints
        (douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ))).Nonempty := by
  constructor
  · intro hdual
    -- Any dual point comes from some Douglas--Rachford fixed point through the Yosida image.
    have hdualImage :=
      dual_inclusion_solution_set_eq_image_yosida_fixedPoints_douglasRachford A B hA hB γ
    rw [hdualImage] at hdual
    rcases hdual with ⟨u, y, hy, rfl⟩
    exact ⟨y, hy⟩
  · intro hfix
    -- Any fixed point yields a dual point by applying the Yosida realizer.
    rw [dual_inclusion_solution_set_eq_image_yosida_fixedPoints_douglasRachford A B hA hB γ]
    rcases hfix with ⟨y, hy⟩
    exact ⟨yosidaApproximationMap B hB γ y, y, hy, rfl⟩

end HilbertComplete

section AddGroup

variable {H : Type u} [AddGroup H]

/-- Part (13) of Proposition 26.1: if `A` is maximally monotone and
`B : H → H` is single-valued, then the dual solution set is the image of
the primal solution set under `B`. -/
theorem dual_inclusion_solution_set_eq_image_primal_inclusion_solution_set_of_forwardBackward
    (A : SetValuedOperator H H) (B : H → H) :
    dual_inclusion_solution_set A B.toSetValuedOperator =
      B '' primal_inclusion_solution_set A B.toSetValuedOperator := by
  ext u
  constructor
  · intro hu
    -- The single-valued inverse condition records exactly `u = B x`.
    rcases (mem_dual_inclusion_solution_set_iff_exists_mem_primal_inclusion_solution_set
      A B.toSetValuedOperator).1 hu with ⟨x, hx, _hAx, hBx⟩
    rw [mem_inverse_iff, Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hBx
    exact ⟨x, hx, hBx.symm⟩
  · rintro ⟨x, hx, rfl⟩
    -- Reuse the primal inclusion to show that `-B x ∈ A x`.
    have hprimal :
        (0 : H) ∈ A x + B.toSetValuedOperator x := by
      exact (mem_primal_inclusion_solution_set A B.toSetValuedOperator x).1 hx
    rw [Function.toSetValuedOperator_apply, Set.mem_add] at hprimal
    rcases hprimal with ⟨v, hv, w, hw, hvw⟩
    rw [Set.mem_singleton_iff] at hw
    subst w
    have hv_eq : v = -B x := by
      simpa [eq_neg_iff_add_eq_zero] using hvw
    rw [mem_dual_inclusion_solution_set, Set.mem_add]
    refine ⟨-x, ?_, x, ?_, by simp⟩
    · have hAinv : x ∈ A⁻¹ (-B x) := by
        simpa [mem_inverse_iff, hv_eq] using hv
      simpa using hAinv
    · rw [mem_inverse_iff, Function.toSetValuedOperator_apply]
      simp

/-- Part (14) of Proposition 26.1: in the forward-backward setting, the
primal and dual solution sets are simultaneously nonempty. -/
theorem primal_nonempty_iff_dual_nonempty_of_forwardBackwardSplittingOperator
    (A : SetValuedOperator H H) (B : H → H) :
    (primal_inclusion_solution_set A B.toSetValuedOperator).Nonempty ↔
      (dual_inclusion_solution_set A B.toSetValuedOperator).Nonempty :=
  primal_inclusion_solution_set_nonempty_iff_dual_inclusion_solution_set_nonempty
    A B.toSetValuedOperator

end AddGroup

section HilbertComplete

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Part (15) of Proposition 26.1: in the forward-backward setting, the
dual solution set is nonempty if and only if the forward-backward
splitting operator has a fixed point. -/
theorem dual_nonempty_iff_fixedPoints_forwardBackwardSplittingOperator_nonempty
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (B : H → H) (γ : PosReal) :
    (dual_inclusion_solution_set A B.toSetValuedOperator).Nonempty ↔
      (fixedPoints (forwardBackwardSplittingOperator A hA B γ)).Nonempty := by
  -- Compare dual nonemptiness with primal nonemptiness, then rewrite the primal set.
  calc
    (dual_inclusion_solution_set A B.toSetValuedOperator).Nonempty ↔
        (primal_inclusion_solution_set A B.toSetValuedOperator).Nonempty := by
          symm
          exact primal_nonempty_iff_dual_nonempty_of_forwardBackwardSplittingOperator A B
    _ ↔ (fixedPoints (forwardBackwardSplittingOperator A hA B γ)).Nonempty := by
          rw [primal_inclusion_solution_set_eq_fixedPoints_forwardBackwardSplittingOperator
            A hA B γ]

/-- Part (17) of Proposition 26.1: if `A` is maximally monotone and `B⁻¹`
is realized by the explicit map `Binv`, then the dual solution set is the
fixed-point set of `u ↦ - {}^[γ] A (Binv u - γu)`, realized by
`yosidaApproximationMap A γ`. -/
theorem dual_inclusion_solution_set_eq_fixedPoints_neg_yosidaApproximationMap_comp_inverse_sub
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (γ : PosReal)
    (Binv : H → H) (hBinv : B⁻¹ = Binv.toSetValuedOperator) :
    dual_inclusion_solution_set A B =
      fixedPoints (fun u : H ↦ -yosidaApproximationMap A hA γ (Binv u - (γ : ℝ) • u)) := by
  ext u
  constructor
  · intro hu
    -- Rewrite the dual inclusion using the singleton model for `B⁻¹`.
    rw [mem_dual_inclusion_solution_set, hBinv, Function.toSetValuedOperator_apply, Set.mem_add]
      at hu
    rcases hu with ⟨y, hy, z, hz, hyz⟩
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hy_eq : y = -Binv u := by
      simpa [eq_neg_iff_add_eq_zero] using hyz
    have hAinv : Binv u ∈ A⁻¹ (-u) := by
      simpa [hy_eq] using hy
    have hAu : -u ∈ A (Binv u) := by
      simpa [mem_inverse_iff] using hAinv
    have harg :
        (Binv u - (γ : ℝ) • u) - (γ : ℝ) • (-u) = Binv u := by
      rw [smul_neg]
      abel_nf
    have hyos_mem : -u ∈ ({}^[γ] A) (Binv u - (γ : ℝ) • u) := by
      refine (mem_yosidaApproximation_iff_mem A γ (Binv u - (γ : ℝ) • u) (-u)).2 ?_
      simpa [harg] using hAu
    have hyos_eq : -u = yosidaApproximationMap A hA γ (Binv u - (γ : ℝ) • u) := by
      rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal
        A hA γ (Binv u - (γ : ℝ) • u)] at hyos_mem
      simpa using hyos_mem
    rw [Function.mem_fixedPoints_iff]
    simpa [eq_comm] using congrArg Neg.neg hyos_eq
  · intro hu
    -- Convert the fixed-point identity back into the Yosida membership formula.
    rw [Function.mem_fixedPoints_iff] at hu
    have hyos_eq :
        yosidaApproximationMap A hA γ (Binv u - (γ : ℝ) • u) = -u := by
      simpa using congrArg Neg.neg hu
    have hyos_mem : -u ∈ ({}^[γ] A) (Binv u - (γ : ℝ) • u) := by
      rw [yosidaApproximation_eq_singleton_yosidaApproximationMap_of_maximal
        A hA γ (Binv u - (γ : ℝ) • u)]
      rw [Set.mem_singleton_iff]
      exact hyos_eq.symm
    have harg :
        (Binv u - (γ : ℝ) • u) - (γ : ℝ) • (-u) = Binv u := by
      rw [smul_neg]
      abel_nf
    have hAu : -u ∈ A (Binv u) := by
      have hAu' :
          -u ∈ A ((Binv u - (γ : ℝ) • u) - (γ : ℝ) • (-u)) :=
        (mem_yosidaApproximation_iff_mem A γ (Binv u - (γ : ℝ) • u) (-u)).1 hyos_mem
      simpa [harg] using hAu'
    have hAinv : Binv u ∈ A⁻¹ (-u) := by
      simpa [mem_inverse_iff] using hAu
    rw [mem_dual_inclusion_solution_set, hBinv, Function.toSetValuedOperator_apply, Set.mem_add]
    refine ⟨-Binv u, ?_, Binv u, by simp, by simp⟩
    simpa using hAinv

end HilbertComplete

section AddGroup

variable {H : Type u} [AddGroup H]

/-- Part (18) of Proposition 26.1: if `A` is maximally monotone and `B⁻¹`
is realized by the explicit map `Binv`, then the primal solution set is
the image of the dual solution set under `Binv`. -/
theorem primal_inclusion_solution_set_eq_image_dual_inclusion_solution_set_of_inverse
    (A B : SetValuedOperator H H) (Binv : H → H) (hBinv : B⁻¹ = Binv.toSetValuedOperator) :
    primal_inclusion_solution_set A B =
      Binv '' dual_inclusion_solution_set A B := by
  ext x
  constructor
  · intro hx
    -- The primal witness characterization identifies `x` with the inverse witness `Binv u`.
    rcases (mem_primal_inclusion_solution_set_iff_exists_mem_dual_inclusion_solution_set
      A B).1 hx with ⟨u, hu, _hAu, hBu⟩
    have hxInv : x ∈ B⁻¹ u := by
      simpa [mem_inverse_iff] using hBu
    rw [hBinv, Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hxInv
    exact ⟨u, hu, hxInv.symm⟩
  · rintro ⟨u, hu, rfl⟩
    -- The dual witness characterization recovers a primal point, and the singleton inverse forces
    -- that point to be `Binv u`.
    rcases (mem_dual_inclusion_solution_set_iff_exists_mem_primal_inclusion_solution_set
      A B).1 hu with ⟨x, hx, _hAx, hBx⟩
    rw [hBinv, Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hBx
    simpa [hBx] using hx

end AddGroup

end

end SetValuedOperator
