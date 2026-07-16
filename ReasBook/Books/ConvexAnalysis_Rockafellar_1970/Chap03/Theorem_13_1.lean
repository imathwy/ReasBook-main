import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_12
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_11_6_2

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

section RclikeClosure

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [Module 𝕜 E]
variable [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [LocallyConvexSpace ℝ E]

local instance instHasPairingStrongDualPrimalRealT131Rclike :
    HasPairing (StrongDual 𝕜 E) E ℝ where
  pairing l x := RCLike.re (l x)

local instance instHasPairingPrimalStrongDualRealT131Rclike :
    HasPairing E (StrongDual 𝕜 E) ℝ where
  pairing x l := RCLike.re (l x)

local instance instHasPairingSwapPrimalStrongDualRealT131Rclike :
    HasPairingSwap E (StrongDual 𝕜 E) ℝ where
  pairing_swap _ _ := rfl

local instance instHasContinuousPairingPrimalStrongDualRealT131Rclike :
    HasContinuousPairing E (StrongDual 𝕜 E) ℝ where
  continuous_pairing_left l := RCLike.continuous_re.comp l.continuous

/-
Source/core/bridge triage:
- `source-facing`: Theorem 13.1 characterizes closure, relative interior, and interior of a convex
  set by inequalities against its support function.
- `core/canonical`: the owner abstractions are the project support function `supportFunction`, the
  closed-convex support cutout theorem
  `setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex`, the relative-boundary owner
  theorem `mem_rb_iff_exists_nonconstant_linearMap_maximizing`, the topological
  closure `closure`, mathlib's relative interior `intrinsicInterior ℝ`, and the ordinary interior
  `interior`.
- `bridge/view`: Rockafellar's `δ*(x⋆ | C)` is represented by `supportFunction C xStar`, while
  `ri C` is represented by `intrinsicInterior ℝ C`.
- Primitive data vs derived API: clause (1) is owned by closed-convex support cutout data, so the
  primitive hypothesis is `Convex ℝ (closure C)`; the source-facing `Convex ℝ C` form is a derived
  bridge. Clauses (2) and (3) keep the source-facing `Convex 𝕜 C` surface, with the primitive
  closure-owner criterion exposed explicitly.
- Domain-style sampling used here: the project declarations `supportFunction` and
  `setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex`, together with the owner
  identities `supportFunction_closure`, `Convex.supportFunction_intrinsicInterior`,
  `mem_rb_iff_exists_nonconstant_linearMap_maximizing`, and the full-dimensional
  bridge `intrinsicInterior_eq_interior_of_affineSpan_eq_top`.
- Layer target: these are `bridge/view` theorems stated directly in the canonical support-function
  language rather than via a new wrapper predicate.
- Ambient refinement: the closure criterion in part (1) is owned by the intrinsic-dual support
  cutout theorem `setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex`, so it is stated on
  the same primal/strong-dual layer as the cutout owner. The relative-interior and interior
  criteria in parts (2) and (3) genuinely use the finite-dimensional owner theorems
  `mem_rb_iff_exists_nonconstant_linearMap_maximizing` and
  `intrinsicInterior_eq_interior_of_affineSpan_eq_top`, so the file is split along those
  canonical ambient levels instead of carrying one stronger shared context. Specializing to
  `EuclideanSpace ℝ (Fin n)` recovers the textbook statement.
-/

variable {C : Set E} {x : E}

/-- Closed-convex support cutout in membership form at the `RCLike` dual layer. -/
private theorem mem_iff_dual_le_supportFunction_of_isClosed_convex_rclike_core
    {D : Set E} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) :
    x ∈ D ↔
      ∀ xStar : StrongDual 𝕜 E,
        (⟪x, xStar⟫ₚ : WithTopBot ℝ) ≤ δᵛ[WithTopBot ℝ](xStar | D) := by
  have hcutout :
      {z : E |
          ∀ xStar : StrongDual 𝕜 E,
            (⟪z, xStar⟫ₚ : WithTopBot ℝ) ≤ δᵛ[WithTopBot ℝ](xStar | D)} = D :=
    setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex
      (𝕜 := 𝕜) hD_closed hD_convex
  exact Iff.of_eq (congrArg (fun s : Set E ↦ x ∈ s) hcutout).symm

/-- Closed-convex support cutout at the `RCLike` dual layer. This is the scalar-general
specialization used by Theorem 13.1 (1) when `𝕜 = ℝ`. -/
theorem mem_iff_dual_le_supportFunction_of_isClosed_convex_rclike
    {D : Set E} (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) :
    x ∈ D ↔
      ∀ xStar : StrongDual 𝕜 E,
        (⟪x, xStar⟫ₚ : WithTopBot ℝ) ≤ δᵛ(xStar | D) :=
  mem_iff_dual_le_supportFunction_of_isClosed_convex_rclike_core
    (x := x) hD_closed hD_convex

/-- Theorem 13.1 (1), primitive closure-owner form: if `closure C` is convex, then membership in
`closure C` is exactly the support cutout inequality against all continuous dual directions. -/
theorem mem_closure_iff_dual_le_supportFunction_of_convex_closure
    (hC_closure : Convex ℝ (closure C)) :
    x ∈ closure C ↔
      ∀ xStar : StrongDual 𝕜 E,
        (⟪x, xStar⟫ₚ : WithTopBot ℝ) ≤ δᵛ(xStar | C) := by
  have hclosure :
      x ∈ closure C ↔
        ∀ xStar : StrongDual 𝕜 E,
          (⟪x, xStar⟫ₚ : WithTopBot ℝ) ≤ δᵛ(xStar | closure C) :=
    mem_iff_dual_le_supportFunction_of_isClosed_convex_rclike
      (x := x) isClosed_closure hC_closure
  have hsupport :
      (δᵛ(· | closure C) : StrongDual 𝕜 E → WithTopBot ℝ) =
        (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot ℝ) :=
    supportFunction_closure
  constructor
  · intro hx xStar
    exact (congrFun hsupport xStar) ▸ (hclosure.mp hx xStar)
  · intro hx
    refine hclosure.mpr ?_
    intro xStar
    exact (congrFun hsupport xStar).symm ▸ (hx xStar)

/-- Theorem 13.1 (1), source-facing convex-set form. -/
theorem mem_closure_iff_dual_le_supportFunction (hC : Convex ℝ C)
    [ContinuousConstSMul ℝ E] :
    x ∈ closure C ↔
      ∀ xStar : StrongDual 𝕜 E,
        (⟪x, xStar⟫ₚ : WithTopBot ℝ) ≤ δᵛ(xStar | C) := by
  exact
    mem_closure_iff_dual_le_supportFunction_of_convex_closure
      (C := C) (x := x) hC.closure

end RclikeClosure

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

local instance instHasPairingStrongDualPrimalT131 : HasPairing (StrongDual 𝕜 E) E 𝕜 where
  pairing l x := l x

local instance instHasPairingPrimalStrongDualT131 : HasPairing E (StrongDual 𝕜 E) 𝕜 where
  pairing x l := l x

local instance instHasPairingSwapPrimalStrongDualT131 :
    HasPairingSwap E (StrongDual 𝕜 E) 𝕜 where
  pairing_swap _ _ := rfl

variable {C : Set E} {x : E}

section

variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜]

private theorem mem_intrinsicInterior_iff_mem_and_lt_of_support_asymmetry_of_isClosed_convex
    {D : Set E} (hD_closed : IsClosed D) (hD : Convex 𝕜 D) :
    x ∈ intrinsicInterior 𝕜 D ↔
      x ∈ D ∧
        ∀ xStar : StrongDual 𝕜 E,
          -δᵛ[WithTopBot 𝕜](-xStar | D) ≠ δᵛ[WithTopBot 𝕜](xStar | D) →
            (⟪x, xStar⟫ₚ : WithTopBot 𝕜) < δᵛ(xStar | D) := by
  constructor
  · intro hxri
    refine ⟨intrinsicInterior_subset hxri, ?_⟩
    intro xStar hAsym
    by_contra hlt
    have hxle : ((xStar x : 𝕜) : WithTopBot 𝕜) ≤ δᵛ[WithTopBot 𝕜](xStar | D) := by
      rw [supportFunction_def]
      exact le_iSup_of_le ⟨x, intrinsicInterior_subset hxri⟩ le_rfl
    have hEq : δᵛ[WithTopBot 𝕜](xStar | D) = ((xStar x : 𝕜) : WithTopBot 𝕜) :=
      le_antisymm (le_of_not_gt hlt) hxle
    let l : E →ₗ[𝕜] 𝕜 := xStar.toLinearMap
    have hmax : ∀ y ∈ D, l y ≤ l x := by
      intro y hyD
      have hy_pair : ((xStar y : 𝕜) : WithTopBot 𝕜) ≤ δᵛ[WithTopBot 𝕜](xStar | D) := by
        rw [supportFunction_def]
        exact le_iSup_of_le ⟨y, hyD⟩ le_rfl
      have hy' : ((l y : 𝕜) : WithTopBot 𝕜) ≤ (l x : WithTopBot 𝕜) := by
        simpa [l, hEq] using hy_pair
      exact (WithTopBot.coe_le_coe).1 hy'
    have hnonconst : ∃ y ∈ D, l y < l x := by
      by_contra hnonconst
      have hEqAll : ∀ y ∈ D, xStar y = xStar x := by
        intro y hyD
        have hy_le : l y ≤ l x := hmax y hyD
        have hy_ge : l x ≤ l y := by
          have hy_not_lt : ¬ l y < l x := fun hy_lt ↦ hnonconst ⟨y, hyD, hy_lt⟩
          exact le_of_not_gt hy_not_lt
        exact le_antisymm (by simpa [l] using hy_le) (by simpa [l] using hy_ge)
      have hAsymFalse : -δᵛ[WithTopBot 𝕜](-xStar | D) = δᵛ[WithTopBot 𝕜](xStar | D) := by
        have hnegEq : δᵛ[WithTopBot 𝕜](-xStar | D) = (((-xStar) x : 𝕜) : WithTopBot 𝕜) := by
          rw [supportFunction_def]
          apply le_antisymm
          · refine iSup_le ?_
            intro y
            have hy_eq : xStar (y : E) = xStar x := hEqAll y y.2
            have hy_eq_neg :
                (((-xStar) (y : E) : 𝕜) : WithTopBot 𝕜) = (((-xStar) x : 𝕜) : WithTopBot 𝕜) := by
              simp [hy_eq]
            exact hy_eq_neg.le
          · exact le_iSup_of_le ⟨x, intrinsicInterior_subset hxri⟩ le_rfl
        calc
          -δᵛ[WithTopBot 𝕜](-xStar | D)
              = -((((-xStar) x : 𝕜) : WithTopBot 𝕜) : WithTopBot 𝕜) := by rw [hnegEq]
          _ = -(-((xStar x : 𝕜) : WithTopBot 𝕜)) := by rfl
          _ = ((xStar x : 𝕜) : WithTopBot 𝕜) := by
            exact neg_neg (((xStar x : 𝕜) : WithTopBot 𝕜))
          _ = δᵛ[WithTopBot 𝕜](xStar | D) := hEq.symm
      exact hAsym hAsymFalse
    have hx_not_frontier : x ∉ intrinsicFrontier 𝕜 D := by
      have hpair : x ∈ closure D \ intrinsicFrontier 𝕜 D := by
        rw [closure_diff_intrinsicFrontier D]
        exact hxri
      exact hpair.2
    have hxbd : x ∈ intrinsicFrontier 𝕜 D :=
      (hD.mem_rb_iff_exists_nonconstant_linearMap_maximizing
        (intrinsicInterior_subset hxri)).2 ⟨l, hmax, hnonconst⟩
    exact False.elim (hx_not_frontier hxbd)
  · rintro ⟨hxD, hstrict⟩
    by_contra hxri
    have hxbd : x ∈ intrinsicFrontier 𝕜 D := by
      rw [← closure_diff_intrinsicInterior D]
      exact ⟨by simpa [hD_closed.closure_eq] using hxD, hxri⟩
    rcases (hD.mem_rb_iff_exists_nonconstant_linearMap_maximizing hxD).1 hxbd with
      ⟨l, hmax, y, hyD, hy_lt⟩
    let xStar : StrongDual 𝕜 E := LinearMap.toContinuousLinearMap l
    have hmax' : ∀ z ∈ D, xStar z ≤ xStar x := by
      intro z hz
      simpa [xStar] using hmax hz
    have hEq : δᵛ[WithTopBot 𝕜](xStar | D) = ((xStar x : 𝕜) : WithTopBot 𝕜) := by
      rw [supportFunction_def]
      apply le_antisymm
      · refine iSup_le ?_
        intro z
        have hz' : ((xStar (z : E) : 𝕜) : WithTopBot 𝕜) ≤ (xStar x : WithTopBot 𝕜) := by
          exact (WithTopBot.coe_le_coe).2 (hmax' z z.2)
        change ((xStar (z : E) : 𝕜) : WithTopBot 𝕜) ≤ ((xStar x : 𝕜) : WithTopBot 𝕜)
        exact hz'
      · have hx_pair :
            ((xStar x : 𝕜) : WithTopBot 𝕜) ≤ ⨆ z : D, ((xStar (z : E) : 𝕜) : WithTopBot 𝕜) := by
          exact le_iSup_of_le ⟨x, hxD⟩ le_rfl
        exact hx_pair
    have hAsym : -δᵛ[WithTopBot 𝕜](-xStar | D) ≠ δᵛ[WithTopBot 𝕜](xStar | D) := by
      have hy_lt' : xStar y < xStar x := by simpa [xStar] using hy_lt
      have hy_neg_lt : (((-xStar) x : 𝕜) : WithTopBot 𝕜) < (((-xStar) y : 𝕜) : WithTopBot 𝕜) := by
        exact (WithTopBot.coe_lt_coe).2 (neg_lt_neg hy_lt')
      have hy_neg_le_sup :
          (((-xStar) y : 𝕜) : WithTopBot 𝕜) ≤ δᵛ[WithTopBot 𝕜](-xStar | D) := by
        rw [supportFunction_def]
        exact le_iSup_of_le ⟨y, hyD⟩ le_rfl
      have hx_neg_lt_sup : (((-xStar) x : 𝕜) : WithTopBot 𝕜) < δᵛ[WithTopBot 𝕜](-xStar | D) :=
        lt_of_lt_of_le hy_neg_lt hy_neg_le_sup
      intro hAsymEq
      have hnegEqFromAsym : δᵛ[WithTopBot 𝕜](-xStar | D) = (((-xStar) x : 𝕜) : WithTopBot 𝕜) := by
        have hminus :
            -δᵛ[WithTopBot 𝕜](-xStar | D) = ((xStar x : 𝕜) : WithTopBot 𝕜) := by
          simpa [hEq] using hAsymEq
        have hneg' : δᵛ[WithTopBot 𝕜](-xStar | D) = -((xStar x : 𝕜) : WithTopBot 𝕜) :=
          (neg_eq_iff_eq_neg.mp hminus)
        simpa using hneg'
      have hcontra :
          (((-xStar) x : 𝕜) : WithTopBot 𝕜) < (((-xStar) x : 𝕜) : WithTopBot 𝕜) := by
        have hx_neg_lt_sup' := hx_neg_lt_sup
        simp [hnegEqFromAsym] at hx_neg_lt_sup'
      exact (lt_irrefl _ hcontra)
    have hx_not_lt : ¬ ((xStar x : 𝕜) : WithTopBot 𝕜) < δᵛ[WithTopBot 𝕜](xStar | D) := by
      simp [hEq]
    have hxlt : (⟪x, xStar⟫ₚ : WithTopBot 𝕜) < δᵛ[WithTopBot 𝕜](xStar | D) :=
      hstrict xStar hAsym
    change ((xStar x : 𝕜) : WithTopBot 𝕜) < δᵛ[WithTopBot 𝕜](xStar | D) at hxlt
    exact hx_not_lt hxlt

/-- Theorem 13.1 (2), primitive closure-owner form: for convex `closure C`, membership in
`ri[𝕜](closure C)` is equivalent to closure membership plus strict support inequality on every
support-asymmetric continuous-dual direction. -/
theorem mem_intrinsicInterior_closure_iff_mem_closure_and_lt_of_support_asymmetry
    (hC_closure : Convex 𝕜 (closure C)) :
    x ∈ ri[𝕜](closure C) ↔
      x ∈ closure C ∧
        ∀ xStar : StrongDual 𝕜 E,
          -δᵛ[WithTopBot 𝕜](-xStar | C) ≠ δᵛ[WithTopBot 𝕜](xStar | C) →
            (⟪x, xStar⟫ₚ : WithTopBot 𝕜) < δᵛ(xStar | C) := by
  have hclosure :
      x ∈ intrinsicInterior 𝕜 (closure C) ↔
        x ∈ closure C ∧
          ∀ xStar : StrongDual 𝕜 E,
            -δᵛ[WithTopBot 𝕜](-xStar | closure C) ≠ δᵛ[WithTopBot 𝕜](xStar | closure C) →
              (⟪x, xStar⟫ₚ : WithTopBot 𝕜) < δᵛ(xStar | closure C) :=
    mem_intrinsicInterior_iff_mem_and_lt_of_support_asymmetry_of_isClosed_convex
      isClosed_closure hC_closure
  have hsupport :
      (δᵛ(· | closure C) : StrongDual 𝕜 E → WithTopBot 𝕜) =
        (δᵛ(· | C) : StrongDual 𝕜 E → WithTopBot 𝕜) :=
    supportFunction_closure
  constructor
  · intro hx
    rcases hclosure.mp hx with ⟨hxcl, hstrict⟩
    refine ⟨hxcl, ?_⟩
    intro xStar hAsym
    have hsupport_x :
        δᵛ[WithTopBot 𝕜](xStar | closure C) = δᵛ[WithTopBot 𝕜](xStar | C) :=
      congrFun hsupport xStar
    have hsupport_neg :
        δᵛ[WithTopBot 𝕜](-xStar | closure C) = δᵛ[WithTopBot 𝕜](-xStar | C) :=
      congrFun hsupport (-xStar)
    have hAsymClosure :
        -δᵛ[WithTopBot 𝕜](-xStar | closure C) ≠
            δᵛ[WithTopBot 𝕜](xStar | closure C) := by
      simpa [hsupport_neg, hsupport_x] using hAsym
    have hxltClosure :
        (⟪x, xStar⟫ₚ : WithTopBot 𝕜) < δᵛ[WithTopBot 𝕜](xStar | closure C) :=
      hstrict xStar hAsymClosure
    rw [hsupport_x] at hxltClosure
    exact hxltClosure
  · rintro ⟨hxcl, hstrict⟩
    refine hclosure.mpr ?_
    refine ⟨hxcl, ?_⟩
    intro xStar hAsymClosure
    have hsupport_x :
        δᵛ[WithTopBot 𝕜](xStar | closure C) = δᵛ[WithTopBot 𝕜](xStar | C) :=
      congrFun hsupport xStar
    have hsupport_neg :
        δᵛ[WithTopBot 𝕜](-xStar | closure C) = δᵛ[WithTopBot 𝕜](-xStar | C) :=
      congrFun hsupport (-xStar)
    have hAsym :
        -δᵛ[WithTopBot 𝕜](-xStar | C) ≠ δᵛ[WithTopBot 𝕜](xStar | C) := by
      simpa [hsupport_neg, hsupport_x] using hAsymClosure
    have hxlt :
        (⟪x, xStar⟫ₚ : WithTopBot 𝕜) < δᵛ[WithTopBot 𝕜](xStar | C) :=
      hstrict xStar hAsym
    rw [hsupport_x]
    exact hxlt

/-- Theorem 13.1 (2), in canonical intrinsic-dual form: a point `x` lies in
`ri[𝕜](C)` iff it lies in `closure C` and the support-function inequality is strict
in every support-asymmetric continuous-dual direction. -/
theorem mem_intrinsicInterior_iff_mem_closure_and_lt_of_support_asymmetry (hC : Convex 𝕜 C) :
    x ∈ ri[𝕜](C) ↔
      x ∈ closure C ∧
        ∀ xStar : StrongDual 𝕜 E,
          -δᵛ[WithTopBot 𝕜](-xStar | C) ≠ δᵛ[WithTopBot 𝕜](xStar | C) →
            (⟪x, xStar⟫ₚ : WithTopBot 𝕜) < δᵛ(xStar | C) := by
  simpa [hC.intrinsicInterior_closure_eq_intrinsicInterior] using
    (mem_intrinsicInterior_closure_iff_mem_closure_and_lt_of_support_asymmetry
      (C := C) (x := x) hC.closure)

/-- Theorem 13.1 (2), intrinsic-topology surface: for convex `C`, `ri[𝕜](C)` membership is
equivalent to intrinsic-closure membership plus strict support inequality in every
support-asymmetric dual direction. -/
theorem mem_intrinsicInterior_iff_mem_intrinsicClosure_and_lt_of_support_asymmetry
    (hC : Convex 𝕜 C) :
    x ∈ ri[𝕜](C) ↔
      x ∈ intrinsicClosure 𝕜 C ∧
        ∀ xStar : StrongDual 𝕜 E,
          -δᵛ[WithTopBot 𝕜](-xStar | C) ≠ δᵛ[WithTopBot 𝕜](xStar | C) →
            (⟪x, xStar⟫ₚ : WithTopBot 𝕜) < δᵛ(xStar | C) := by
  simpa [intrinsicClosure_eq_closure 𝕜 C] using
    (mem_intrinsicInterior_iff_mem_closure_and_lt_of_support_asymmetry
      (C := C) (x := x) hC)

-- Proof sketch: combine Theorem 13.1's intrinsic-interior support criterion with the affine-hull
-- fixed-point condition. For convex `C`, asymmetric support directions force strict inequalities
-- at every point of `intrinsicInterior 𝕜 C`; this becomes vacuous exactly when all asymmetric
-- directions already have support value `⊤`, which is equivalent to `C` being affine.
/-- Theorem 13.1 (affine-hull form), on the intrinsic dual owner layer: for a convex set `C`, the
fixed-point condition `(affineSpan 𝕜 C : Set E) = C` is equivalent to saying that every
support-asymmetric dual direction already has support value `⊤`. -/
private theorem affineSpan_eq_self_iff_supportFunction_eq_top_of_support_asymmetry
    (hC : Convex 𝕜 C) :
    (affineSpan 𝕜 C : Set E) = C ↔
      ∀ xStar : StrongDual 𝕜 E,
        -δᵛ[WithTopBot 𝕜](-xStar | C) ≠ δᵛ[WithTopBot 𝕜](xStar | C) →
          δᵛ[WithTopBot 𝕜](xStar | C) = ⊤ := sorry

/-- Theorem 13.1 (3), in canonical intrinsic-dual form: a point `x` lies in `interior C` if and
only if every nonzero continuous linear functional `xStar` is strictly smaller at `x` than the
support function `δ*(xStar | C) = δᵛ(xStar | C)`. -/
-- Proof sketch: apply part (2) in its closure-based form and then pass from
-- `intrinsicInterior 𝕜 C` to `interior C` through the owner bridge
-- `intrinsicInterior_eq_interior_of_affineSpan_eq_top`, where strict inequalities in every
-- nonzero dual direction force full dimensionality.
theorem mem_interior_iff_forall_ne_zero_dual_lt_supportFunction (hC : Convex 𝕜 C) :
    x ∈ interior C ↔
      ∀ xStar : StrongDual 𝕜 E,
        xStar ≠ 0 → (⟪x, xStar⟫ₚ : WithTopBot 𝕜) < δᵛ(xStar | C) := sorry

section

open scoped RealInnerProductSpace

variable [InnerProductSpace ℝ E]

/-- Inner-product specialization bridge for the affine-hull criterion in Theorem 13.1. -/
private theorem affineSpan_eq_self_iff_supportFunction_eq_top_of_support_asymmetry_primal
    (hC : Convex ℝ C) :
    (affineSpan ℝ C : Set E) = C ↔
      ∀ xStar : E,
        -δᵛ[WithTopBot ℝ](-xStar | C) ≠ δᵛ[WithTopBot ℝ](xStar | C) →
          δᵛ[WithTopBot ℝ](xStar | C) = ⊤ := sorry

/-- Inner-product specialization bridge for Theorem 13.1 (3), stated in primal-vector notation. -/
private theorem mem_interior_iff_forall_ne_zero_primal_lt_supportFunction (hC : Convex ℝ C) :
    x ∈ interior C ↔
      ∀ xStar : E, xStar ≠ 0 → (⟪x, xStar⟫ : WithTopBot ℝ) < δᵛ(xStar | C) := sorry

end

end

end
