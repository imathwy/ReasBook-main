import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_13_1_1 (from Chap03) -/
section

open scoped Rockafellar

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [Module 𝕜 E]
variable [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [LocallyConvexSpace ℝ E]

local instance instHasPairingStrongDualPrimalRealCor1311 :
    HasPairing (StrongDual 𝕜 E) E ℝ where
  pairing l x := RCLike.re (l x)

local instance instHasPairingPrimalStrongDualRealCor1311 :
    HasPairing E (StrongDual 𝕜 E) ℝ where
  pairing x l := RCLike.re (l x)

local instance instHasPairingPrimalStrongDualWithTopBotRealCor1311 :
    HasPairing E (StrongDual 𝕜 E) (WithTopBot ℝ) :=
  instHasPairingWithBotTop

local instance instHasPairingSwapPrimalStrongDualRealCor1311 :
    HasPairingSwap E (StrongDual 𝕜 E) ℝ where
  pairing_swap _ _ := rfl

local instance instHasContinuousPairingPrimalStrongDualRealCor1311 :
    HasContinuousPairing E (StrongDual 𝕜 E) ℝ where
  continuous_pairing_left l := RCLike.continuous_re.comp l.continuous

/-!
Source/core/bridge triage:
- `source-facing`: Corollary 13.1.1 says that for convex sets, inclusion of closures is
  equivalent to the pointwise order relation between their support functions.
- `core/canonical`: the owner abstractions are `closure`, the project support function
  `supportFunction`, and the closed-convex support cutout theorem
  `setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex`.
- `bridge/view`: Rockafellar's `δ*(· | C)` is represented by the chapter notation `δᵛ(· | C)` for
  the owner `supportFunction C`; this file upgrades the evaluation side from self-pairing vectors
  to the intrinsic dual owner `StrongDual 𝕜 E` and reads dual evaluations through `re`, so the
  theorem surface is no longer tied to an inner-product model and keeps the canonical
  `WithTopBot ℝ` support-value codomain instead of a local `EReal` specialization.
- Primitive data vs derived API: the only primitive input is convexity of `closure C₂`; no
  convexity on `C₁` belongs in the statement.

Domain-style sampling used here:
- `supportFunction`;
- `supportFunction_closure`;
- `setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex`.

Layer target: `bridge/view`, stated directly in the canonical closure/support-function API without
introducing any local wrapper notion.
- Ambient refinement: only locally-convex dual half-space separation is used, so the theorem is
  stated on real locally-convex topological modules with an `RCLike` scalar action rather than on
  normed or inner-product specializations.
- Topology abstraction audit: the upstream owner theorem
  `setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex` is an ambient closed-convex cutout
  theorem, so this corollary is canonically about ambient `closure`. An intrinsic/relative-closure
  replacement here would force a stronger finite-dimensional layer (via
  `intrinsicClosure_eq_closure`) that is not primitive to this owner.
-/

/-- Corollary 13.1.1, at the intrinsic dual owner layer: for sets `C₁`, `C₂` with convex
`closure C₂` in a real locally-convex topological module carrying an `RCLike` scalar action, one has
`closure C₁ ⊆ closure C₂` if and only if the support-function inequality on the continuous dual
holds pointwise:
`δᵛ(xStar | C₁) ≤ δᵛ(xStar | C₂)` for all `xStar : StrongDual 𝕜 E`, where support values are in
`WithTopBot ℝ`. -/
theorem closure_subset_closure_iff_supportFunction_le {C₁ C₂ : Set E}
    (hC₂ : Convex ℝ (closure C₂)) :
    closure C₁ ⊆ closure C₂ ↔
      ∀ xStar : StrongDual 𝕜 E,
        (δᵛ(xStar | C₁) : WithTopBot ℝ) ≤ (δᵛ(xStar | C₂) : WithTopBot ℝ) := by
  constructor
  · intro h xStar
    have hClosure :
        (δᵛ(xStar | closure C₁) : WithTopBot ℝ) ≤ (δᵛ(xStar | closure C₂) : WithTopBot ℝ) := by
      rw [supportFunction_def, supportFunction_def]
      refine iSup_le ?_
      intro y
      exact le_iSup_of_le ⟨y, h y.2⟩ le_rfl
    calc
      (δᵛ(xStar | C₁) : WithTopBot ℝ) = (δᵛ(xStar | closure C₁) : WithTopBot ℝ) := by
        simpa using (congrFun (supportFunction_closure (C := C₁)) xStar).symm
      _ ≤ (δᵛ(xStar | closure C₂) : WithTopBot ℝ) := hClosure
      _ = (δᵛ(xStar | C₂) : WithTopBot ℝ) := by
        simpa using congrFun (supportFunction_closure (C := C₂)) xStar
  · intro h x hx
    have hxCutout :
        x ∈ {z : E | ∀ xStar : StrongDual 𝕜 E,
          ⟪z, xStar⟫ₚ ≤ (δᵛ(xStar | closure C₂) : WithTopBot ℝ)} := by
      intro l
      have hxLe :
          ⟪x, l⟫ₚ ≤ (δᵛ(l | closure C₁) : WithTopBot ℝ) := by
        rw [supportFunction_def]
        exact le_iSup (fun y : closure C₁ ↦ (⟪l, (y : E)⟫ₚ : WithTopBot ℝ)) ⟨x, hx⟩
      calc
        ⟪x, l⟫ₚ ≤ (δᵛ(l | closure C₁) : WithTopBot ℝ) := hxLe
        _ = (δᵛ(l | C₁) : WithTopBot ℝ) := by
          simpa using congrFun (supportFunction_closure (C := C₁)) l
        _ ≤ (δᵛ(l | C₂) : WithTopBot ℝ) := h l
        _ = (δᵛ(l | closure C₂) : WithTopBot ℝ) := by
          simpa using (congrFun (supportFunction_closure (C := C₂)) l).symm
    have hcutout :
        {z : E | ∀ xStar : StrongDual 𝕜 E,
          ⟪z, xStar⟫ₚ ≤ (δᵛ(xStar | closure C₂) : WithTopBot ℝ)} =
          closure C₂ :=
      setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex
        (C := closure C₂) isClosed_closure hC₂
    rw [← hcutout]
    exact hxCutout

end

/-! ### Theorem_13_1 (from Chap03) -/
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

/-! ### Text_13_1_2 (from Chap03) -/
noncomputable section

section

open scoped Rockafellar

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [Module 𝕜 E]
variable [IsScalarTower ℝ 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [LocallyConvexSpace ℝ E]

local notation "E⋆" => StrongDual 𝕜 E

local instance instHasPairingPrimalStrongDualReal : HasPairing E E⋆ ℝ where
  pairing x l := RCLike.re (l x)

local instance instHasPairingStrongDualPrimalReal : HasPairing E⋆ E ℝ :=
  HasPairing.swap (X := E) (Y := E⋆) (L := ℝ)

local instance instHasPairingPrimalStrongDualWithTopBotReal :
    HasPairing E E⋆ (WithTopBot ℝ) :=
  instHasPairingWithBotTop

local instance instHasPairingSwapPrimalStrongDualReal :
    HasPairingSwap E E⋆ ℝ where
  pairing_swap _ _ := rfl

local instance instHasContinuousPairingPrimalStrongDualReal :
    HasContinuousPairing E E⋆ ℝ where
  continuous_pairing_left l := RCLike.continuous_re.comp l.continuous

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.1.2 defines
  `D = {x | ∀ xStar, ⟪x, xStar⟫ ≤ δ*(xStar | C)}`
  for a closed convex set `C` and states that `D = C`, so `C` is determined by its support
  function.
- `core/canonical`: the owner abstractions are the project support function `supportFunction`,
  the support-function/half-space bridge
  `subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot`, and the closed-convex half-space
  owner theorem `RCLike.iInter_halfSpaces_eq'`.
- `bridge/view`: Rockafellar's `δ*(xStar | C)` is `supportFunction C xStar`, and the displayed set
  `D` is the source-facing dual-evaluation presentation of the dual-half-space intersection from
  the owner theorem.

Domain-style sampling used here:
- `supportFunction`;
- `subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot`;
- `RCLike.iInter_halfSpaces_eq'`.

Layer target: `bridge/view`, stated directly as the equality between `C` and the support-function
cutout set at the continuous-dual owner layer, with the uniqueness consequence exposed separately
as a thin companion theorem.
- Ambient refinement: only locally-convex dual half-space separation is used, so the primary
  theorem is stated on a real locally convex topological module with an `RCLike` scalar action,
  without adding an inner-product-specialized source-facing duplicate.
-/

-- Proof sketch: the forward implication sends each support-function inequality to the owner
-- dual-half-space intersection from `RCLike.iInter_halfSpaces_eq'`; the reverse implication is
-- immediate from `supportFunction_def` because each `x ∈ C` contributes one value in the defining
-- supremum.
/-- Text 13.1.2 at the intrinsic dual owner layer: for a closed convex set `C`, the set of points
whose dual evaluations are bounded above by the support function of `C` is exactly `C`. -/
theorem setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex {C : Set E}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    {x : E | ∀ xStar : E⋆,
      ⟪x, xStar⟫ₚ ≤ (δᵛ(xStar | C) : WithTopBot ℝ)} = C := by
  ext x
  constructor
  · intro hx
    have hx' :
        x ∈
          ⋂ (l : E⋆) (c : ℝ) (_ : ∀ y ∈ C, RCLike.re (l y) ≤ c),
            {z : E | RCLike.re (l z) ≤ c} := by
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro l c hc
      have hsubset : C ⊆ closedHalfSpaceLE l c := by
        intro y hyC
        exact mem_closedHalfSpaceLE_iff.mpr (hc y hyC)
      have hsupport_le : (δᵛ(l | C) : WithTopBot ℝ) ≤ c :=
        (subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot C l c).1 hsubset
      have hx_le : (⟪x, l⟫ₚ : WithTopBot ℝ) ≤ c :=
        (hx l).trans hsupport_le
      have hxWithBot : ((⟪x, l⟫ₚ : ℝ) : WithBot ℝ) ≤ ((c : ℝ) : WithBot ℝ) :=
        (WithTop.coe_le_coe).1 hx_le
      exact (WithBot.coe_le_coe).1 hxWithBot
    have hhalfspaces :
        ⋂ (l : E⋆) (c : ℝ) (_ : ∀ y ∈ C, RCLike.re (l y) ≤ c),
            {z : E | RCLike.re (l z) ≤ c} =
          C :=
      RCLike.iInter_halfSpaces_eq' (𝕜 := 𝕜) hC_convex hC_closed
    simpa [hhalfspaces] using hx'
  · intro hx xStar
    rw [supportFunction_def]
    exact le_iSup (fun y : C ↦ (⟪xStar, (y : E)⟫ₚ : WithTopBot ℝ)) ⟨x, hx⟩

/-- Closure-owner form of Text 13.1.2: if `closure C` is convex, then the support-function cutout
defined from `C` recovers `closure C`. -/
theorem setOf_forall_dual_le_supportFunction_eq_closure_of_convex_closure {C : Set E}
    (hC_convex : Convex ℝ (closure C)) :
    {x : E | ∀ xStar : E⋆,
      ⟪x, xStar⟫ₚ ≤ (δᵛ(xStar | C) : WithTopBot ℝ)} = closure C := by
  have hsupport_closure :
      (δᵛ(· | closure C) : E⋆ → WithTopBot ℝ) =
        (δᵛ(· | C) : E⋆ → WithTopBot ℝ) :=
    supportFunction_closure (C := C)
  have hcutout_closure :
      {x : E | ∀ xStar : E⋆,
        ⟪x, xStar⟫ₚ ≤ (δᵛ(xStar | closure C) : WithTopBot ℝ)} = closure C :=
    setOf_forall_dual_le_supportFunction_eq_of_isClosed_convex
      (C := closure C) isClosed_closure hC_convex
  rw [← hcutout_closure]
  ext x
  constructor <;> intro hx xStar
  · exact (congrFun hsupport_closure xStar).symm ▸
      (hx xStar : (⟪x, xStar⟫ₚ : WithTopBot ℝ) ≤ (δᵛ(xStar | C) : WithTopBot ℝ))
  · exact (congrFun hsupport_closure xStar) ▸
      (hx xStar : (⟪x, xStar⟫ₚ : WithTopBot ℝ) ≤ (δᵛ(xStar | closure C) : WithTopBot ℝ))

/-- Closure-owner uniqueness form: if `closure C` and `closure D` are convex and their support
functions agree on the continuous dual, then `closure C = closure D`. -/
theorem closure_eq_of_convex_closure_supportFunction_eq {C D : Set E}
    (hC_convex : Convex ℝ (closure C)) (hD_convex : Convex ℝ (closure D))
    (h_support :
      (δᵛ(· | C) : E⋆ → WithTopBot ℝ) =
        (δᵛ(· | D) : E⋆ → WithTopBot ℝ)) :
    closure C = closure D := by
  have hC_cutout :
      {x : E | ∀ xStar : E⋆, ⟪x, xStar⟫ₚ ≤ (δᵛ(xStar | C) : WithTopBot ℝ)} = closure C :=
    setOf_forall_dual_le_supportFunction_eq_closure_of_convex_closure hC_convex
  have hD_cutout :
      {x : E | ∀ xStar : E⋆, ⟪x, xStar⟫ₚ ≤ (δᵛ(xStar | D) : WithTopBot ℝ)} = closure D :=
    setOf_forall_dual_le_supportFunction_eq_closure_of_convex_closure hD_convex
  rw [← hC_cutout, ← hD_cutout]
  ext x
  constructor
  · intro hx xStar
    exact (hx xStar).trans (congrFun h_support xStar).le
  · intro hx xStar
    exact (hx xStar).trans (congrFun h_support xStar).symm.le

-- Proof sketch: first apply the closure-owner uniqueness theorem
-- `closure_eq_of_convex_closure_supportFunction_eq`. The closedness assumptions then identify
-- each closure with the original set.
/-- A closed convex set is uniquely determined by its support function on the continuous dual. -/
theorem eq_of_isClosed_convex_supportFunction_eq {C D : Set E}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (h_support :
      (δᵛ(· | C) : E⋆ → WithTopBot ℝ) =
        (δᵛ(· | D) : E⋆ → WithTopBot ℝ)) :
    C = D := by
  have hC_closure_convex : Convex ℝ (closure C) := by
    simpa [hC_closed.closure_eq] using hC_convex
  have hD_closure_convex : Convex ℝ (closure D) := by
    simpa [hD_closed.closure_eq] using hD_convex
  have hclosure :
      closure C = closure D :=
    closure_eq_of_convex_closure_supportFunction_eq
      (C := C) (D := D) hC_closure_convex hD_closure_convex h_support
  simpa [hC_closed.closure_eq, hD_closed.closure_eq] using hclosure

end

/-! ### Text_13_1_3 (from Chap03) -/
noncomputable section

open scoped Pointwise Rockafellar

section

variable {𝕜 : Type*} [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
variable {X Y : Type*}
variable [Add Y] [HasPairing X Y 𝕜] [HasPairingAddRight X Y 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Text 13.1.3 states the support-function formula for the Minkowski sum
  `C1 + C2`.
- `core/canonical`: the owner abstractions are the project support function `supportFunction` on
  subsets of a pairing space and pointwise set addition.
- `bridge/view`: Rockafellar's notation `δ*(x* | C)` is represented by `δᵛ(xStar | C)`.
- Primitive data vs derived API: both the support function and the pointwise set sum are already
  canonical owners; the item contributes only their interaction theorem. The main declarations use
  the chapter support-function notation `δᵛ(· | C)` on theorem surfaces while
  keeping the same owner-level proof route.

Domain-style sampling used here:
- the project declarations `supportFunction`, `supportFunction_def`, and
  `supportFunction_eq_iSup`;
- the owner expansion `supportFunction_eq_iSup`, which confirms the theorem belongs at the same
  ambient support-function level as `supportFunction` itself, namely the primitive pairing/addition
  owners `[HasPairing X Y 𝕜] [HasPairingAddRight X Y 𝕜]`, rather than the concrete `R^n` model;
- mathlib's pointwise set addition identity `Set.image2_add`;
- mathlib's indexed-supremum witness theorem `lt_iSup_iff`;
- the extended-codomain approximation lemma `WithBotTop.add_le_of_forall_lt`.

Layer target: `source-facing`, stated directly for the support function of the Minkowski sum and
reusing only the canonical owner abstractions already present upstream.

Semantic note:
- the displayed identity already holds for arbitrary subsets `C1` and `C2`; the textbook's
  convexity and nonemptiness assumptions are redundant and are therefore omitted from the Lean
  statement.
- because the owner `supportFunction` is defined on arbitrary pairing spaces, the theorem is
  refined to that ambient owner level instead of the concrete model `EuclideanSpace ℝ (Fin n)`.
- the public codomain surface is the chapter owner `WithTopBot 𝕜`.
-/

-- Proof sketch: expand `supportFunction` using `supportFunction_def`, rewrite the inner-product
-- image of `C1 + C2` as the pointwise sum of the two separate inner-product images, and compare
-- the resulting indexed suprema directly. The upper bound is immediate from `iSup_le`. For the
-- reverse inequality, use `WithBotTop.add_le_of_forall_lt` and `lt_iSup_iff` to approximate each
-- function strictly from below by values attained on `C1` and `C2`.
/-- Text 13.1.3: the support function of the pointwise sum of two sets is the sum of their support
functions. This already holds for arbitrary subsets of a pairing space, so the textbook's
convexity and nonemptiness assumptions are redundant. -/
theorem supportFunction_set_add
    (C1 C2 : Set Y) :
    (δᵛ(· | C1 + C2) : X → WithTopBot 𝕜) =
      (δᵛ(· | C1) : X → WithTopBot 𝕜) + (δᵛ(· | C2) : X → WithTopBot 𝕜) := by
  sorry

/-- Text 13.1.3 in pointwise form: evaluating the support function of a Minkowski sum at `xStar`
gives the sum of the two support values. -/
theorem supportFunction_set_add_apply
    (C1 C2 : Set Y) (xStar : X) :
    (δᵛ(xStar | C1 + C2) : WithTopBot 𝕜) = δᵛ(xStar | C1) + δᵛ(xStar | C2) := by
  simpa using congrFun (supportFunction_set_add C1 C2) xStar

end

-- Proof sketch: expand `supportFunction` using `supportFunction_def`, rewrite the pairing on
-- the dilate by `pairing_smul_right`, and compare the resulting suprema directly. The reverse
-- inequality uses division by the positive scalar `c` to pull a witness in `c • C` back to `C`.
section

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X Y : Type*}
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasPairing X Y 𝕜] [HasPairingSMulRight X Y 𝕜]

local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul := fun c z ↦ (c : WithTopBot 𝕜) * z

/-- Positive dilations scale the support function by the same positive scalar. This is an owner
operation theorem for `supportFunction` on arbitrary subsets of a pairing space. -/
private theorem supportFunction_smul_set_of_pos_withTopBot
    (C : Set Y) {c : 𝕜} (hc : 0 < c) :
    (supportFunction (c • C) : X → WithTopBot 𝕜) =
      c • supportFunction C := by
  sorry

/-- Positive dilations scale the support function by the same positive scalar. This is an owner
operation theorem for `supportFunction` on arbitrary subsets of a pairing space. -/
theorem supportFunction_smul_set_of_pos
    (C : Set Y) {c : 𝕜} (hc : 0 < c) :
    (δᵛ(· | c • C) : X → WithTopBot 𝕜) =
      c • (δᵛ(· | C) : X → WithTopBot 𝕜) := by
  simpa using supportFunction_smul_set_of_pos_withTopBot (C := C) hc

/-- Positive dilations scale the support value at `xStar` by the same scalar. -/
theorem supportFunction_smul_set_of_pos_apply
    (C : Set Y) {c : 𝕜} (hc : 0 < c) (xStar : X) :
    (δᵛ(xStar | c • C) : WithTopBot 𝕜) = c • (δᵛ(xStar | C) : WithTopBot 𝕜) := by
  simpa [Pi.smul_apply] using congrFun (supportFunction_smul_set_of_pos C hc) xStar

-- Proof sketch: split into the existing positive-scalar owner theorem and the endpoint `c = 0`.
-- In the zero case, nonemptiness of `C` gives `0 • C = {0}`, and the support function of `{0}`
-- is the zero function by `supportFunction_def`.
/-- Nonnegative dilations of a nonempty set scale the support function by the same scalar. The
positive case is `supportFunction_smul_set_of_pos`; nonemptiness is needed only for the endpoint
`c = 0`. -/
private theorem supportFunction_smul_set_of_nonempty_withTopBot
    [HasPairingZeroRight X Y 𝕜]
    (C : Set Y) (hC : C.Nonempty) {c : 𝕜} (hc : 0 ≤ c) :
    (supportFunction (c • C) : X → WithTopBot 𝕜) =
      c • supportFunction C := by
  sorry

/-- Nonnegative dilations of a nonempty set scale the support function by the same scalar. The
positive case is `supportFunction_smul_set_of_pos`; nonemptiness is needed only for the endpoint
`c = 0`. -/
theorem supportFunction_smul_set_of_nonempty
    [HasPairingZeroRight X Y 𝕜]
    (C : Set Y) (hC : C.Nonempty) {c : 𝕜} (hc : 0 ≤ c) :
    (δᵛ(· | c • C) : X → WithTopBot 𝕜) =
      c • (δᵛ(· | C) : X → WithTopBot 𝕜) := by
  simpa using
    supportFunction_smul_set_of_nonempty_withTopBot
      (C := C) hC (c := c) hc

/-- Evaluating the support function of the nonnegative dilate `c • C` at `xStar` multiplies the
support value by `c`. -/
theorem supportFunction_smul_set_of_nonempty_apply
    [HasPairingZeroRight X Y 𝕜]
    (C : Set Y) (hC : C.Nonempty) {c : 𝕜} (hc : 0 ≤ c) (xStar : X) :
    (δᵛ(xStar | c • C) : WithTopBot 𝕜) = c • (δᵛ(xStar | C) : WithTopBot 𝕜) := by
  simpa [Pi.smul_apply] using congrFun (supportFunction_smul_set_of_nonempty C hC hc) xStar

end

section

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X Y : Type*}
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul := fun c z ↦ (c : WithTopBot 𝕜) * z

-- Proof sketch: rewriting `δᵛ(c • x⋆ | C)` as `δᵛ(x⋆ | c • C)` is a direct owner-level
-- reindexing of `supportFunction_def`; combine this with
-- `supportFunction_smul_set_of_nonempty_apply`.
/-- Evaluating the support function at a nonnegative scalar multiple of the primal argument scales
the value by the same scalar. -/
theorem supportFunction_smul_left_of_nonempty_apply
    (C : Set Y) (hC : C.Nonempty) {c : 𝕜} (hc : 0 ≤ c) (xStar : X) :
    (δᵛ(c • xStar | C) : WithTopBot 𝕜) = c • (δᵛ(xStar | C) : WithTopBot 𝕜) := by
  have hswap :
      (δᵛ(c • xStar | C) : WithTopBot 𝕜) = δᵛ(xStar | c • C) := by
    rw [supportFunction_def, supportFunction_def]
    apply le_antisymm
    · refine iSup_le fun y ↦ ?_
      refine le_iSup_of_le (⟨c • (y : Y), ⟨(y : Y), y.2, rfl⟩⟩ : {y : Y // y ∈ c • C}) ?_
      change ((⟪c • xStar, (y : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤
        ((⟪xStar, c • (y : Y)⟫ₚ : 𝕜) : WithTopBot 𝕜)
      simp [HasLinearPairing.pairing_eq_pairingLinear]
    · refine iSup_le fun y ↦ ?_
      rcases y.2 with ⟨z, hz, hyz⟩
      refine le_iSup_of_le (⟨z, hz⟩ : C) ?_
      rw [← hyz]
      change ((⟪xStar, c • z⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ ((⟪c • xStar, z⟫ₚ : 𝕜) : WithTopBot 𝕜)
      simp [HasLinearPairing.pairing_eq_pairingLinear]
  rw [hswap]
  simpa using supportFunction_smul_set_of_nonempty_apply C hC hc xStar

end

/-! ### Text_13_1_4 (from Chap03) -/
noncomputable section

open scoped Rockafellar
attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.1.4 identifies the Fenchel conjugate of the indicator `δ(· | C)` with
  the support function of `C`.
- `core/canonical`: the owner abstractions are `indicator`, `convexConjugate`,
  `supportFunction`, and the pairing-orientation bridge owner `HasPairingSwap`.
- `bridge/view`: Rockafellar's `δ(· | C)` is represented by `indicator C`, while the
  source's pointwise value `δ*(x⋆ | C)` is the evaluation of the owner equality at `xStar`.
- Primitive data vs derived API: the main declaration is the owner-level function equality at the
  pairing-swap layer, with pointwise formulas and symmetry-argument variants kept as thin bridges.

Domain-style sampling used here:
- `indicator`;
- `supportFunction` and `supportFunction_def`;
- `convexConjugate`;
- `HasPairingSwap`.
-/

section PairingSwap

variable {E : Type*} {EStar : Type*} {α : Type*}
variable [Add α] [Neg α] [Zero α] [ConditionallyCompleteLattice α]
variable [HasPairing E EStar α] [HasPairing EStar E α] [HasPairingSwap E EStar α]

-- Proof sketch: unfold `convexConjugate` at `indicator C`.
-- For `x ∈ C`, the indicator term is `0`, so the affine defect is `⟪x, xStar⟫`.
-- For `x ∉ C`, the
-- indicator term is `⊤`, so the defect is `⊥` and does not change the supremum. The remaining
-- supremum over `C` is exactly `supportFunction C xStar`, after swapping the pairing arguments
-- by the pairing-swap owner hypothesis.
/-- Text 13.1.4 at the pairing layer: if the two pairing orientations `(E, EStar)` and
`(EStar, E)` agree by `HasPairingSwap`, then the Fenchel conjugate of the indicator `δ(· | C)`
is the support function `δᵛ(· | C)`. -/
theorem convexConjugate_indicator_eq_supportFunction
    (C : Set E) :
    ((δ(· | C))⋆ : EStar → WithTopBot α) =
      (δᵛ(· | C) : EStar → WithTopBot α) := by
  classical
  funext xStar
  rw [convexConjugate_eq_iSup_pairing_sub]
  calc
    (⨆ x : E, (⟪x, xStar⟫ₚ - δ(x | C)))
        = ⨆ x : E, if x ∈ C then (⟪x, xStar⟫ₚ : WithTopBot α) else ⊥ := by
          congr with x
          by_cases hx : x ∈ C
          · simp [hx]
          · simp [hx]
    _ = ⨆ x ∈ C, ⟪x, xStar⟫ₚ := by
          apply le_antisymm
          · refine iSup_le fun x ↦ ?_
            by_cases hx : x ∈ C
            · exact le_iSup_of_le x <| le_iSup_of_le hx <| by simp [hx]
            · simp [hx]
          · refine iSup₂_le fun x hx ↦ ?_
            exact le_iSup_of_le x <| by simp [hx]
    _ = ⨆ x : C, ⟪(x : E), xStar⟫ₚ := by
          rw [← iSup_subtype'' C fun x : E ↦ ⟪x, xStar⟫ₚ]
    _ = δᵛ(xStar | C) := by
          rw [supportFunction_def]
          congr with x
          exact congrArg ((↑) : α → WithTopBot α)
            (HasPairingSwap.pairing_swap (x := (x : E)) (y := xStar))

/- Long-name bridge alias for downstream files still using `indicatorFunction` in theorem names. -/
theorem convexConjugate_indicatorFunction_eq_supportFunction
    (C : Set E) :
    ((δ(· | C))⋆ : EStar → WithTopBot α) =
      (δᵛ(· | C) : EStar → WithTopBot α) := by
  simpa using convexConjugate_indicator_eq_supportFunction (C := C)

/- Text 13.1.4 in pointwise form at the pairing layer with the canonical pairing-swap owner. -/
theorem convexConjugate_indicator_eq_supportFunction_pointwise
    (C : Set E) (xStar : EStar) :
    (δ(· | C))⋆ xStar = (δᵛ(xStar | C) : WithTopBot α) := by
  simpa using congrFun
    (convexConjugate_indicator_eq_supportFunction (C := C)) xStar

/- Long-name bridge alias for downstream files still using `indicatorFunction` in theorem names. -/
theorem convexConjugate_indicatorFunction_eq_supportFunction_pointwise
    (C : Set E) (xStar : EStar) :
    (δ(· | C))⋆ xStar = (δᵛ(xStar | C) : WithTopBot α) := by
  simpa using convexConjugate_indicator_eq_supportFunction_pointwise (C := C) (xStar := xStar)

end PairingSwap

section PairingSymmetric

variable {E : Type*} {α : Type*}
variable [Add α] [Neg α] [Zero α] [ConditionallyCompleteLattice α]
variable [HasPairing E E α]

/-- Text 13.1.4 at the pairing layer: if the self-pairing is symmetric, then the Fenchel conjugate
of the indicator `δ(· | C)` is the support function `δᵛ(· | C)`. -/
theorem convexConjugate_indicator_eq_supportFunction_of_pairing_symm
    (hpair_symm : ∀ x y : E, (⟪x, y⟫ₚ : α) = ⟪y, x⟫ₚ)
    (C : Set E) :
    ((δ(· | C))⋆ : E → WithTopBot α) =
      (δᵛ(· | C) : E → WithTopBot α) := by
  letI : HasPairingSwap E E α := ⟨hpair_symm⟩
  simpa using
    (convexConjugate_indicator_eq_supportFunction (C := C))

/- Long-name bridge alias for downstream files still using `indicatorFunction` in theorem names. -/
theorem convexConjugate_indicatorFunction_eq_supportFunction_of_pairing_symm
    (hpair_symm : ∀ x y : E, (⟪x, y⟫ₚ : α) = ⟪y, x⟫ₚ)
    (C : Set E) :
    ((δ(· | C))⋆ : E → WithTopBot α) =
      (δᵛ(· | C) : E → WithTopBot α) := by
  simpa using convexConjugate_indicator_eq_supportFunction_of_pairing_symm
    (hpair_symm := hpair_symm) (C := C)

/- Text 13.1.4 in pointwise form at the pairing layer. -/
theorem convexConjugate_indicator_eq_supportFunction_pointwise_of_pairing_symm
    (hpair_symm : ∀ x y : E, (⟪x, y⟫ₚ : α) = ⟪y, x⟫ₚ)
    (C : Set E) (xStar : E) :
    (δ(· | C))⋆ xStar = (δᵛ(xStar | C) : WithTopBot α) := by
  letI : HasPairingSwap E E α := ⟨hpair_symm⟩
  simpa using
    (convexConjugate_indicator_eq_supportFunction_pointwise (C := C) (xStar := xStar))

/- Long-name bridge alias for downstream files still using `indicatorFunction` in theorem names. -/
theorem convexConjugate_indicatorFunction_eq_supportFunction_pointwise_of_pairing_symm
    (hpair_symm : ∀ x y : E, (⟪x, y⟫ₚ : α) = ⟪y, x⟫ₚ)
    (C : Set E) (xStar : E) :
    (δ(· | C))⋆ xStar = (δᵛ(xStar | C) : WithTopBot α) := by
  simpa using convexConjugate_indicator_eq_supportFunction_pointwise_of_pairing_symm
    (hpair_symm := hpair_symm) (C := C) (xStar := xStar)

end PairingSymmetric

end

/-! ### Text_13_1_5 (from Chap03) -/
noncomputable section

universe u

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.1.5 identifies the biconjugate of the indicator of a convex set with
  the closure of that indicator, and then identifies that closure with the indicator of the set
  closure.
- `core/canonical`: the owner declarations already present in the project are
  `indicatorFunction`, `supportFunction`, `convexConjugate`, and
  `lowerSemicontinuousHull`.
- `bridge/view`: Rockafellar's `δ^*(· | C)` is the support function `supportFunction C`, while the
  closure `cl δ(· | C)` is represented by `lowerSemicontinuousHull (indicatorFunction C)`.
- `primitive data`: a set `C : Set E`; the convexity hypothesis `Convex 𝕜 C` is needed only for
  the biconjugacy clause, not for the closure-of-indicator clause.
- `derived API`: the owner-level closure theorem
  `lowerSemicontinuousHull (indicatorFunction C) = indicatorFunction (closure C)` (reused from
  Text 7.0.14 as `lowerSemicontinuousHull_indicator_eq_indicator_closure`) and its
  source-facing biconjugacy owner
  `convexConjugate (supportFunction C) = lowerSemicontinuousHull (indicatorFunction C)`, with
  the indicator-of-closure statement kept as a bridge corollary.

Domain-style sampling used here:
- `indicatorFunction`;
- `le_lowerSemicontinuousHull`;
- `LowerSemicontinuous.isClosed_preimage`;
- `convexConjugate_indicatorFunction_eq_supportFunction`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`;
- `lowerSemicontinuousHull`.

Layer target:
- `bridge/view` for the closure theorem from Text 7.0.14
  `lowerSemicontinuousHull (indicatorFunction C) = indicatorFunction (closure C)`, which belongs
  at the generic lower-semicontinuity owner level of a topological space;
- `source-facing` for the support-function biconjugacy clauses, which reuse the chapter Fenchel
  owners on the finite-dimensional scalar-field pairing ambient where Theorem 12.2 lives.
-/

section

variable {E : Type u} {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
  [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
  [HasPairingSwap E E 𝕜]

-- Proof sketch: combine the chapter indicator/support bridge with biconjugacy at the pairing
-- level. The pairing-swap owner identifies the support-function conjugate with the indicator
-- biconjugate, and then Theorem 12.2 identifies that biconjugate with the closure owner
-- `cl(δ(· | C))`.
/-- Pairing-swap owner form of Text 13.1.5: on a finite-dimensional scalar-field space with a
continuous linear self-pairing, the conjugate of the support function of a convex set is the
closure `cl(δ(· | C))` of its indicator. -/
theorem convexConjugate_supportFunction_eq_lowerSemicontinuousHull_indicator
    (C : Set E) (hC : Convex 𝕜 C) :
    ((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆) = cl((δ[𝕜](· | C))) := by
  change convexConjugate (supportFunction C : E → WithBotTop 𝕜) = cl((δ[𝕜](· | C)))
  have hsupport :
      convexConjugate (supportFunction C : E → WithBotTop 𝕜) =
        convexBiconjugate (L := WithBotTop 𝕜) (δ[𝕜](· | C)) := by
    simpa [convexBiconjugate] using
      congrArg (convexConjugate (X := E) (Y := E) (L := WithBotTop 𝕜))
        (convexConjugate_indicatorFunction_eq_supportFunction
          (E := E) (EStar := E) (α := 𝕜) C).symm
  have hbiconj :
      convexBiconjugate (L := WithBotTop 𝕜) (δ[𝕜](· | C)) =
        lowerSemicontinuousHull (δ[𝕜](· | C)) := by
    simpa using
      (((indicator_isConvex_iff (𝕜 := 𝕜) (α := 𝕜) C).2 hC).biconjugate_eq_lowerSemicontinuousHull)
  calc
    convexConjugate (supportFunction C : E → WithBotTop 𝕜) =
        convexBiconjugate (L := WithBotTop 𝕜) (δ[𝕜](· | C)) := hsupport
    _ = lowerSemicontinuousHull (δ[𝕜](· | C)) := hbiconj

-- Proof sketch: apply the owner-level biconjugacy identity above and rewrite `cl(δ(· | C))` as
-- `δ(· | closure C)` using the generic closure-of-indicator theorem.
/-- Pairing-swap owner form of Text 13.1.5: the conjugate of the support function of a convex set
is the indicator of the set closure. -/
theorem convexConjugate_supportFunction_eq_indicatorFunction_closure
    (C : Set E) (hC : Convex 𝕜 C) [ClosedIciTopology 𝕜] :
    ((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆) = (δ[𝕜](· | closure C)) := by
  change convexConjugate (supportFunction C : E → WithBotTop 𝕜) = (δ[𝕜](· | closure C))
  calc
    convexConjugate (supportFunction C : E → WithBotTop 𝕜) = cl((δ[𝕜](· | C))) :=
      convexConjugate_supportFunction_eq_lowerSemicontinuousHull_indicator C hC
    _ = (δ[𝕜](· | closure C)) := by
      simpa using
        (lowerSemicontinuousHull_indicator_eq_indicator_closure (X := E) (𝕜 := 𝕜) C)

end

section

variable {E : Type u} {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
  [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
  [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

-- Proof sketch: this is the pairing-symmetric bridge for the pairing-swap owner theorem above.
theorem convexConjugate_supportFunction_eq_lowerSemicontinuousHull_indicator_of_pairing_symm
    (hpair_symm : ∀ x y : E, (⟪x, y⟫ₚ : 𝕜) = ⟪y, x⟫ₚ)
    (C : Set E) (hC : Convex 𝕜 C) :
    ((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆) = cl((δ[𝕜](· | C))) := by
  letI : HasPairingSwap E E 𝕜 := ⟨hpair_symm⟩
  simpa using
    (convexConjugate_supportFunction_eq_lowerSemicontinuousHull_indicator
      (E := E) C hC)

-- Proof sketch: this is the pairing-symmetric bridge for the pairing-swap owner theorem above.
/-- Pairing-layer bridge form of Text 13.1.5: if the pairing is symmetric, then the conjugate of
the support function of a convex set is the indicator of the set closure. -/
theorem convexConjugate_supportFunction_eq_indicatorFunction_closure_of_pairing_symm
    (hpair_symm : ∀ x y : E, (⟪x, y⟫ₚ : 𝕜) = ⟪y, x⟫ₚ)
    (C : Set E) (hC : Convex 𝕜 C) [ClosedIciTopology 𝕜] :
    ((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆) = (δ[𝕜](· | closure C)) := by
  letI : HasPairingSwap E E 𝕜 := ⟨hpair_symm⟩
  simpa using
    (convexConjugate_supportFunction_eq_indicatorFunction_closure (E := E) C hC)

end
