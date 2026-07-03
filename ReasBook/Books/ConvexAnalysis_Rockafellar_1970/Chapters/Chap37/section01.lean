import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_37_1_1 (from Chap07) -/
noncomputable section

universe u v

open scoped Rockafellar

namespace Bifunction

section

open SaddleFunction

variable {R : Type*} {α : Type*}
variable {U : Type u} {UStar : Type*} {X : Type v} {XStar : Type*}
variable [Ring R] [PartialOrder R]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α]
variable [TopologicalSpace U] [AddCommGroup U] [Module R U]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module R UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module R X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module R XStar]
variable [HasPairing U UStar (WithBotTop α)] [HasPairing X XStar (WithBotTop α)]
variable [SMul R (WithBotTop α)]

local notation "lowerConjugate" =>
  (Bifunction.lowerConjugate : (U → XStar → WithBotTop α) → UStar → X → WithBotTop α)
local notation "upperConjugate" =>
  (Bifunction.upperConjugate : (U → XStar → WithBotTop α) → UStar → X → WithBotTop α)

/-- The lower conjugate of a closed concave-convex saddle-function is itself concave-convex. -/
theorem lowerConjugate_isConcaveConvex
    {K : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    IsConcaveConvex R (lowerConjugate K) := sorry

/-- The lower conjugate of a closed concave-convex saddle-function is lower closed. -/
theorem lowerConjugate_isLowerClosed
    {K : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    IsLowerClosed (lowerConjugate K) := sorry

/-- The upper conjugate of a closed concave-convex saddle-function is itself concave-convex. -/
theorem upperConjugate_isConcaveConvex
    {K : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    IsConcaveConvex R (upperConjugate K) := sorry

/-- The upper conjugate of a closed concave-convex saddle-function is upper closed. -/
theorem upperConjugate_isUpperClosed
    {K : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    IsUpperClosed (upperConjugate K) := sorry

/-- The lower and upper conjugates of a closed concave-convex saddle-function belong to the same
Chapter 34 equivalence class. -/
theorem lowerConjugate_equivalent_upperConjugate
    {K : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    lowerConjugate K ∼ upperConjugate K := sorry

end

section

open SaddleFunction

variable {R : Type*} {α : Type*}
variable {U : Type u} {UStar : Type*} {X : Type v} {XStar : Type*}
variable [Ring R] [PartialOrder R]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α]
variable [TopologicalSpace U] [AddCommGroup U] [Module R U]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module R UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module R X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module R XStar]
variable [HasPairing U UStar (WithBotTop α)] [HasPairing X XStar (WithBotTop α)]
variable [SMul R (WithBotTop α)]

local notation "lowerConjugate" =>
  (Bifunction.lowerConjugate : (U → XStar → WithBotTop α) → UStar → X → WithBotTop α)
local notation "upperConjugate" =>
  (Bifunction.upperConjugate : (U → XStar → WithBotTop α) → UStar → X → WithBotTop α)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 37.1.1 says that conjugation sends a closed concave-convex
  saddle-function to a conjugate equivalence class whose lower and upper representatives are
  respectively lower closed and upper closed, that this conjugate class depends only on the
  original Chapter 34 equivalence class, and that conjugating again returns to the original
  equivalence class. The source surface is the paired-space one from Theorem 37.1:
  `K : U → XStar → WithBotTop α` and conjugates
  `K⋆ : UStar → X → WithBotTop α`.
- `core/canonical`: the owner layer already present in the chapter is `lowerConjugate`,
  `upperConjugate`, the equivalence relation `∼`, and the saddle-function predicates
  `IsConcaveConvex`, `IsClosed`, `IsLowerClosed`, and `IsUpperClosed`.
- `bridge/view`: Theorem 34.2 and Theorem 37.1 identify a closed concave-convex saddle-function
  with a closed convex generator `F` and then identify its conjugates with the canonical lower
  and upper representatives of the conjugate-side generator.

Domain-style sampling used here:
- `Bifunction.lowerConjugate` and `Bifunction.upperConjugate` from `Definition_37_1_1`;
- `Bifunction.lowerConjugate_eq_lowerPairing_inverse_adjointFunction_of_mem_omega` and
  `Bifunction.upperConjugate_eq_lagrangian_of_mem_omega` from `Theorem_37_1`;
- `Bifunction.mem_omega_iff_equivalent_lowerPairing`,
  `Bifunction.isConcaveConvex_of_mem_omega`, and `Bifunction.isClosed_of_mem_omega` from
  `Theorem_34_2`;
- `SaddleFunction.IsLowerClosed` and `SaddleFunction.IsUpperClosed` from
  `Definition33_0_42`.

Primitive data vs derived API:
- primitive source data: a closed concave-convex saddle-function
  `K : U → XStar → WithBotTop α`;
- primitive owner data reused here: `lowerConjugate K`, `upperConjugate K`, and `K ∼ L`;
- derived API recorded here: lower/upper closedness of the two conjugates, equivalence of the
  two conjugate representatives, invariance under passage to an equivalent representative, and
  the return to the original equivalence class after conjugating any representative of the
  conjugate class.

Layer target: `source-facing`, stated directly on the existing Chapter 34 and Chapter 37 owners.
-/

section

-- Proof sketch: use Theorem 34.2 to place `K` and `L` in the same class `Ω(F)` for the closed
-- convex generator `F` of `K`. Theorem 37.1 then identifies the lower conjugates of both
-- representatives with the same canonical lower conjugate-side representative, and likewise for
-- the upper conjugates, so both conjugate assignments are invariant on the Chapter 34
-- equivalence class.
/-- Corollary 37.1.1: the lower conjugate depends only on the Chapter 34 equivalence class of a
closed concave-convex saddle-function. -/
theorem lowerConjugate_equivalent_of_equivalent
    {K L : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K)
    (hKL : K ∼ L) :
    lowerConjugate K ∼ lowerConjugate L := sorry

/-- Corollary 37.1.1: the upper conjugate depends only on the Chapter 34 equivalence class of a
closed concave-convex saddle-function. -/
theorem upperConjugate_equivalent_of_equivalent
    {K L : U → XStar → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K)
    (hKL : K ∼ L) :
    upperConjugate K ∼ upperConjugate L := sorry

end

variable [HasPairing UStar U (WithBotTop α)] [HasPairing XStar X (WithBotTop α)]

section

local notation "lowerConjugate" =>
  (Bifunction.lowerConjugate :
    (UStar → X → WithBotTop α) → U → XStar → WithBotTop α)
local notation "upperConjugate" =>
  (Bifunction.upperConjugate :
    (UStar → X → WithBotTop α) → U → XStar → WithBotTop α)
local notation "sourceLowerConjugate" =>
  (Bifunction.lowerConjugate :
    (U → XStar → WithBotTop α) → UStar → X → WithBotTop α)

-- Proof sketch: the hypothesis places `KStar` in the same conjugate-side class as
-- `lowerConjugate K`, hence also in the class of `upperConjugate K` by the previous theorem.
-- Apply the corresponding lower/upper conjugate invariance theorem on that conjugate class, and
-- then use the converse half of Theorem 37.1 for the common closed convex generator to identify
-- each conjugate of `KStar` with the original class of `K`.
/-- Conjugating any representative of the conjugate equivalence class returns, via lower
conjugation, a representative of the original Chapter 34 equivalence class. -/
theorem lowerConjugate_equivalent_original_of_equivalent_lowerConjugate
    {K : U → XStar → WithBotTop α} {KStar : UStar → X → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K)
    (hKStar : KStar ∼ sourceLowerConjugate K) :
    lowerConjugate KStar ∼ K := sorry

/-- Conjugating any representative of the conjugate equivalence class returns, via upper
conjugation, a representative of the original Chapter 34 equivalence class. -/
theorem upperConjugate_equivalent_original_of_equivalent_lowerConjugate
    {K : U → XStar → WithBotTop α} {KStar : UStar → X → WithBotTop α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K)
    (hKStar : KStar ∼ sourceLowerConjugate K) :
    upperConjugate KStar ∼ K := sorry

end

end

end Bifunction

/-! ### Definition_37_1_1 (from Chap07) -/
noncomputable section

universe u u' v w z

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {UStar : Type u'} {X : Type v} {XStar : Type w} {L : Type z}
variable [HAdd L L L] [HSub L L L]
variable [HasPairing U UStar L] [HasPairing X XStar L]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 37.1.1 introduces the lower and upper conjugates of a
  concave-convex saddle-function.
- `core/canonical`: the Chapter 36 owner layer already contains the relevant minimax operators
  `Bifunction.maximinValueOn` and `Bifunction.minimaxValueOn`.
- `bridge/view`: the source conjugates are exactly those existing owners applied directly in source
  variable order to the affine perturbation kernel
  `(x⋆, u) ↦ ⟪u, u⋆⟫ + ⟪x, x⋆⟫ - K(u, x⋆)`, yielding the textbook order
  `sup_x⋆ inf_u` / `inf_u sup_x⋆` without an extra swap wrapper.

Domain-style sampling used here:
- `Bifunction.maximinValue` from `Chap07.Definition_36_0_1`;
- `Bifunction.minimaxValue` from `Chap07.Definition_36_0_1`;
- `Bifunction.maximin_le_minimax` from the same owner file.

Primitive data vs derived API:
- primitive data: the saddle-function `K` and the evaluation point `(u⋆, x)`;
- primitive source-facing owners introduced here: `lowerConjugate K` and `upperConjugate K`;
- derived API: the explicit `iSup`/`iInf` formulas and the minimax inequality
  `lowerConjugate K ≤ upperConjugate K`.

Layer target: `source-facing`, implemented directly through the existing Chapter 36 owners rather
than a second minimax wrapper.
-/

/-- Definition 37.1.1: the lower conjugate of a concave-convex saddle-function `K`, expressed
as the Chapter 36 maximin value of the affine perturbation kernel. -/
def lowerConjugate [SupSet L] [InfSet L] (K : U → XStar → L) : UStar → X → L :=
  fun uStar x ↦
    maximinValue (fun xStar u ↦
      (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar)

/-- Definition 37.1.1: the upper conjugate of a concave-convex saddle-function `K`, expressed
as the Chapter 36 minimax value of the affine perturbation kernel. -/
def upperConjugate [SupSet L] [InfSet L] (K : U → XStar → L) : UStar → X → L :=
  fun uStar x ↦
    minimaxValue (fun xStar u ↦
      (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar)

/-- Primitive owner-level bridge for Definition 37.1.1: the lower conjugate is the Chapter 36
maximin owner applied to the affine perturbation kernel (in source variable order). -/
theorem lowerConjugate_eq_maximinValue
    [SupSet L] [InfSet L] (K : U → XStar → L) (uStar : UStar) (x : X) :
    lowerConjugate K uStar x = maximinValue (fun xStar u ↦
      (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar) :=
  rfl

/-- Primitive owner-level bridge for Definition 37.1.1: the upper conjugate is the Chapter 36
minimax owner applied to the affine perturbation kernel (in source variable order). -/
theorem upperConjugate_eq_minimaxValue
    [SupSet L] [InfSet L] (K : U → XStar → L) (uStar : UStar) (x : X) :
    upperConjugate K uStar x = minimaxValue (fun xStar u ↦
      (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar) :=
  rfl

/- Textbook pointwise notation for Definition 37.1.1. -/
scoped[Rockafellar] notation:max K " _*(" uStar ", " x ")" =>
  Bifunction.lowerConjugate K uStar x

/- Textbook pointwise notation for Definition 37.1.1. -/
scoped[Rockafellar] notation:max K " ^*(" uStar ", " x ")" =>
  Bifunction.upperConjugate K uStar x

section

variable [CompleteLattice L]

@[simp] theorem lowerConjugate_apply
    (K : U → XStar → L) (uStar : UStar) (x : X) :
    K _*(uStar, x) =
      ⨆ xStar : XStar, ⨅ u : U,
        (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar := by
  simp [lowerConjugate_eq_maximinValue, maximinValue, maximinValueOn]

@[simp] theorem upperConjugate_apply
    (K : U → XStar → L) (uStar : UStar) (x : X) :
    K ^*(uStar, x) =
      ⨅ u : U, ⨆ xStar : XStar,
        (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar := by
  simp [upperConjugate_eq_minimaxValue, minimaxValue, minimaxValueOn]

/-- Proposition 37.1.2, owner form: the lower conjugate is pointwise bounded above by the upper
conjugate. -/
theorem lowerConjugate_le_upperConjugate
    (K : U → XStar → L) (uStar : UStar) (x : X) :
    K _*(uStar, x) ≤ K ^*(uStar, x) := by
  simpa [lowerConjugate, upperConjugate] using
    maximin_le_minimax (fun xStar u ↦ (⟪u, uStar⟫ₚ + ⟪x, xStar⟫ₚ) - K u xStar)

end

end

end Bifunction

/-! ### Theorem_37_1 (from Chap07) -/
noncomputable section

universe u u' v v'

open scoped Rockafellar

namespace Bifunction

section

variable {α : Type*} {U : Type u} {UStar : Type u'} {X : Type v} {XStar : Type v'}
variable [Semiring α]
variable [TopologicalSpace U] [TopologicalSpace X]
variable [AddCommMonoid U] [SMul α U]
variable [AddCommMonoid X] [SMul α X]
variable [Neg UStar]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable [HasPairing U UStar (WithTopBot α)]
variable [HasPairing X XStar (WithTopBot α)]

section Omega

variable (F : U → X → WithTopBot α)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 37.1 identifies the lower and upper conjugates of a representative
  `K ∈ ΩAdj[UStar](F)` with the canonical conjugate-side saddle representatives generated by `F`.
- `core/canonical`: the owner layer already present in the project is
  `Bifunction.omegaAdjoint`, `Bifunction.lowerPairing`, `Bifunction.lagrangian`,
  `Bifunction.adjoint`, and `Bifunction.inverse`.
- `bridge/view`: the lower/upper conjugates introduced in Definition 37.1.1 are the minimax
  transforms of `K`; the mixed-dual interval owner `ΩAdj[UStar](F)` supplies the right
  abstraction boundary for the source-side class, and Theorem 36.5 identifies the upper
  conjugate-side representative as the order-dual Lagrangian `lagrangian (toOrderDual F)`.
  The source's notation `F_*^*` is therefore the existing mixed inverse-adjoint owner, so the theorem
  should reuse those owners rather than introduce a second Chapter 7 conjugate package.

Domain-style sampling used here:
- `Bifunction.lowerConjugate` and `Bifunction.upperConjugate` from `Definition_37_1_1`;
- `Bifunction.lowerPairing`, `Bifunction.upperAdjointPairing`, `Bifunction.omegaAdjoint`, and the
  membership characterization `mem_omegaAdjoint_iff` from `Defn_34_2`;
- `Bifunction.lagrangian` from `Chap06.Definition_6_30_13` together with
  `Bifunction.lagrangian_toOrderDual_eq_iInf_pairing_sub_inverse` from `Theorem_36_5`;
- `Bifunction.inverse_adjoint` from `Definition_36_4_5`.

Primitive data vs derived API:
- primitive source data: a closed-convex bifunction `F` together with a representative
  `K ∈ ΩAdj[UStar](F)`;
- primitive owner objects reused here: `ΩAdj[UStar](F)`, `lagrangian (toOrderDual F)`, and
  `lowerPairing (F _*^*)`;
- derived API: the four source formulas of Theorem 37.1.

Layer target: `source-facing`, stated directly on the existing owner objects rather than through a
parallel “conjugate saddle-function class” wrapper.
-/

/-- Theorem 37.1, upper-conjugate clause: for a closed convex generator `F` and any
representative `K ∈ ΩAdj[UStar](F)`, the upper conjugate of `K` is the existing Lagrangian owner attached
to `F`. This is the source formula
`inf_u sup_x⋆ {⟪u, u⋆⟫ + ⟪x, x⋆⟫ - K(u, x⋆)} = ⟪u⋆, F_* x⟫`, written with the canonical project
owner `lagrangian (toOrderDual F)`. -/
theorem upperConjugate_eq_lagrangian_of_mem_omegaAdj
    (hF : IsClosedConvex F) {K : U → XStar → WithTopBot α} (hK : K ∈ ΩAdj[UStar](F)) :
    upperConjugate K = lagrangian (toOrderDual F) := by
  sorry

/-- Theorem 37.1, lower-conjugate clause: for a closed convex generator `F` and any
representative `K ∈ ΩAdj[UStar](F)`, the lower conjugate of `K` is the lower representative generated by
the canonical conjugate-side owner
`F_*^*`. This is the source formula
`sup_x⋆ inf_u {⟪u, u⋆⟫ + ⟪x, x⋆⟫ - K(u, x⋆)} = ⟪F_*^* u⋆, x⟫`. -/
theorem lowerConjugate_eq_lowerPairing_of_mem_omegaAdj
    [HasPairing XStar X (WithTopBot α)]
    (hF : IsClosedConvex F) {K : U → XStar → WithTopBot α} (hK : K ∈ ΩAdj[UStar](F)) :
    lowerConjugate K = lowerPairing X (F _*^*) := by
  sorry

end Omega

section ConjugateSandwich

variable (F : U → X → WithTopBot α)
variable [Neg U] [HasPairing UStar U (WithTopBot α)] [HasPairing XStar X (WithTopBot α)]

/-- Theorem 37.1, converse upper-conjugate clause: for a closed convex generator `F`, any
conjugate-side representative lying between the canonical lower and upper conjugate
representatives of `F` has upper conjugate equal to the mixed-dual upper representative
generated by `F`. This is the source formula
`inf_u⋆ sup_x {⟪u, u⋆⟫ + ⟪x, x⋆⟫ - K⋆(u⋆, x)} = ⟪u, F* x⋆⟫`. -/
theorem upperConjugate_eq_upperAdjointPairing_of_mem_omegaAdj_adjointInverse
    (hF : IsClosedConvex F)
    {KStar : UStar → X → WithTopBot α}
    (hKStar : KStar ∈ ΩAdj[U](F _*^*)) :
    upperConjugate KStar = upperAdjointPairing XStar UStar F := by
  sorry

/-- Theorem 37.1, converse lower-conjugate clause: for a closed convex generator `F`, any
conjugate-side representative lying between the canonical lower and upper conjugate
representatives of `F` has lower conjugate equal to the canonical lower representative
generated by `F`. This is the source formula
`sup_x inf_u⋆ {⟪u, u⋆⟫ + ⟪x, x⋆⟫ - K⋆(u⋆, x)} = ⟪F u, x⋆⟫`. -/
theorem lowerConjugate_eq_lowerPairing_of_mem_omegaAdj_adjointInverse
    (hF : IsClosedConvex F)
    {KStar : UStar → X → WithTopBot α}
    (hKStar : KStar ∈ ΩAdj[U](F _*^*)) :
    lowerConjugate KStar = lowerPairing XStar F := by
  sorry

end ConjugateSandwich

end

end Bifunction

/-! ### Corollary_37_1_2 (from Chap07) -/
noncomputable section

universe u v

open SaddleFunction
open scoped Rockafellar

namespace Bifunction

section

variable {R : Type*} {α : Type*}
variable {U : Type u} {UStar : Type*} {X : Type v} {XStar : Type*}
variable [Ring R] [PartialOrder R]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module R UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module R X]
variable [HasPairing U UStar (WithTopBot α)] [HasPairing X XStar (WithTopBot α)]
variable [SMul R (WithTopBot α)]

local notation "lowerConjugate" =>
  (Bifunction.lowerConjugate : (U → XStar → WithTopBot α) → UStar → X → WithTopBot α)
local notation "upperConjugate" =>
  (Bifunction.upperConjugate : (U → XStar → WithTopBot α) → UStar → X → WithTopBot α)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 37.1.2 is a pointwise agreement statement for the lower and upper
  conjugates of a closed concave-convex saddle-function.
- `core/canonical`: the existing owners are `lowerConjugate`, `upperConjugate`, `dom₁`, `dom₂`,
  `dom`, `IsClosed`, and the relative-interior notation `ri[R](·)`.
- `bridge/view`: the source phrase "common conjugate-domain factors" is written using the
  Chapter 34 coordinate-domain owners of `lowerConjugate K`.

Domain-style sampling used here:

- `Bifunction.lowerConjugate` and `Bifunction.upperConjugate` from `Definition_37_1_1`;
- `SaddleFunction.IsClosed` and `SaddleFunction.IsConcaveConvex` from `Defn_34_2`;
- `SaddleFunction.dom₁` and `SaddleFunction.dom₂` from `Defn_34_3`;
- `ri[R](·)` from `Chap02.Text_6_8`.

Primitive data vs derived API:

- primitive data: a saddle-function `K : U → XStar → WithTopBot α`;
- primitive hypotheses: `IsConcaveConvex R (lowerConjugate K)`,
  `IsClosed (lowerConjugate K)`, and
  `lowerConjugate K ∼ upperConjugate K`;
- derived API: pointwise equality of `lowerConjugate K` and `upperConjugate K` on the relative
  interior of either coordinate-domain factor, plus the intrinsic-domain reformulation on
  `ri[R](dom (lowerConjugate K))`.

Layer target: `source-facing`.
-/

-- Proof sketch: combine the Chapter 37 equivalence of the two conjugates with the Chapter 34
-- relative-interior agreement theorem for equivalent representatives, applied to the common
-- coordinate domains of the conjugate class.
/-- Core owner form of Corollary 37.1.2: if the lower conjugate of `K` is a closed concave-convex
representative equivalent to the upper conjugate, then the two conjugates agree at `(uStar, x)`
whenever either coordinate lies in the corresponding relative-interior conjugate-domain factor. -/
theorem lowerConjugate_eq_upperConjugate_of_mem_ri_dom₁_or_mem_ri_dom₂
    {K : U → XStar → WithTopBot α}
    (hLower_shape : IsConcaveConvex R (lowerConjugate K))
    (hLower_closed : IsClosed (lowerConjugate K))
    (hLower_equiv_upper : lowerConjugate K ∼ upperConjugate K)
    {uStar : UStar} {x : X}
    (hri :
      uStar ∈ ri[R](dom₁ (lowerConjugate K)) ∨
        x ∈ ri[R](dom₂ (lowerConjugate K))) :
    K _*(uStar, x) = K ^*(uStar, x) := by
  symm
  exact
    SaddleFunction.eq_of_equivalent_of_isConcaveConvex_of_isClosed_of_mem_ri_dom₁_or_mem_ri_dom₂
      hLower_shape hLower_closed hLower_equiv_upper hri

-- Proof sketch: combine the Chapter 37 equivalence of the two conjugates with Corollary 34.2.1's
-- effective-domain invariance on an equivalent closed concave-convex class.
/-- Core owner form of Corollary 37.1.2: equivalent closed concave-convex lower/upper conjugate
representatives have the same Chapter 34 effective domain. -/
theorem dom_upperConjugate_eq_dom_lowerConjugate_of_equivalent_of_isConcaveConvex_of_isClosed
    {K : U → XStar → WithTopBot α}
    (hLower_shape : IsConcaveConvex R (lowerConjugate K))
    (hLower_closed : IsClosed (lowerConjugate K))
    (hLower_equiv_upper : lowerConjugate K ∼ upperConjugate K) :
    dom (upperConjugate K) = dom (lowerConjugate K) := by
  exact
    SaddleFunction.dom_eq_of_equivalent_of_isConcaveConvex_of_isClosed
      hLower_shape hLower_closed hLower_equiv_upper

-- Proof sketch: rewrite `ri[R](dom (lowerConjugate K))` as the product
-- `ri[R](dom₁ (lowerConjugate K)) ×ˢ ri[R](dom₂ (lowerConjugate K))`, then apply the
-- source-facing pointwise corollary at each point of that intrinsic-relative domain.
/-- Intrinsic-domain core owner form: on the relative interior of the common effective domain, the
equivalent closed concave-convex lower/upper conjugate representatives agree pointwise. -/
theorem eqOn_ri_dom_lowerConjugate_upperConjugate_of_equivalent_of_isConcaveConvex_of_isClosed
    {K : U → XStar → WithTopBot α}
    (hLower_shape : IsConcaveConvex R (lowerConjugate K))
    (hLower_closed : IsClosed (lowerConjugate K))
    (hLower_equiv_upper : lowerConjugate K ∼ upperConjugate K) :
    Set.EqOn (Function.uncurry (lowerConjugate K))
      (Function.uncurry (upperConjugate K))
      (ri[R](dom (lowerConjugate K))) := by
  intro p hp
  have hp_fst_snd :
      p.1 ∈ ri[R](dom₁ (lowerConjugate K)) ∧
        p.2 ∈ ri[R](dom₂ (lowerConjugate K)) := by
    simpa [SaddleFunction.dom, ri_prod_eq, Set.mem_prod] using hp
  simpa [Function.uncurry] using
    lowerConjugate_eq_upperConjugate_of_mem_ri_dom₁_or_mem_ri_dom₂
      hLower_shape hLower_closed hLower_equiv_upper (Or.inl hp_fst_snd.1)

end

section

variable [TopologicalSpace U] [AddCommGroup U] [Module R U]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module R XStar]

-- Proof sketch: derive the lower-conjugate closed concave-convex representative data from the
-- source hypotheses on `K` via Corollary 37.1.1, then invoke the core owner theorem above.
/-- Source-facing Corollary 37.1.2 owner form: for a closed concave-convex `K`, the two
conjugates agree at `(uStar, x)` whenever either coordinate lies in the corresponding
relative-interior conjugate-domain factor. -/
theorem lowerConjugate_eq_upperConjugate_of_isConcaveConvex_of_isClosed_of_mem_ri_dom₁_or_mem_ri_dom₂
    {K : U → XStar → WithTopBot α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K)
    {uStar : UStar} {x : X}
    (hri :
      uStar ∈ ri[R](dom₁ (lowerConjugate K)) ∨
        x ∈ ri[R](dom₂ (lowerConjugate K))) :
    K _*(uStar, x) = K ^*(uStar, x) := by
  have hLower_shape : IsConcaveConvex R (lowerConjugate K) :=
    lowerConjugate_isConcaveConvex hK_shape hK_closed
  have hLower_lowerClosed : IsLowerClosed (lowerConjugate K) :=
    lowerConjugate_isLowerClosed hK_shape hK_closed
  have hLower_closed : IsClosed (lowerConjugate K) :=
    SaddleFunction.isClosed_of_isLowerClosed hLower_lowerClosed
  have hLower_equiv_upper : lowerConjugate K ∼ upperConjugate K :=
    lowerConjugate_equivalent_upperConjugate hK_shape hK_closed
  exact
    lowerConjugate_eq_upperConjugate_of_mem_ri_dom₁_or_mem_ri_dom₂
      hLower_shape hLower_closed hLower_equiv_upper hri

-- Proof sketch: derive the conjugate representative hypotheses from Corollary 37.1.1 and
-- delegate to the core effective-domain invariance theorem above.
/-- Source-facing Corollary 37.1.2 owner form: for a closed concave-convex `K`, the lower and
upper conjugates have the same Chapter 34 effective domain. -/
theorem dom_upperConjugate_eq_dom_lowerConjugate_of_isConcaveConvex_of_isClosed
    {K : U → XStar → WithTopBot α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    dom (upperConjugate K) = dom (lowerConjugate K) := by
  have hLower_shape : IsConcaveConvex R (lowerConjugate K) :=
    lowerConjugate_isConcaveConvex hK_shape hK_closed
  have hLower_lowerClosed : IsLowerClosed (lowerConjugate K) :=
    lowerConjugate_isLowerClosed hK_shape hK_closed
  have hLower_closed : IsClosed (lowerConjugate K) :=
    SaddleFunction.isClosed_of_isLowerClosed hLower_lowerClosed
  have hLower_equiv_upper : lowerConjugate K ∼ upperConjugate K :=
    lowerConjugate_equivalent_upperConjugate hK_shape hK_closed
  exact
    dom_upperConjugate_eq_dom_lowerConjugate_of_equivalent_of_isConcaveConvex_of_isClosed
      hLower_shape hLower_closed hLower_equiv_upper

-- Proof sketch: obtain the source-level lower/upper conjugate representative hypotheses from
-- Corollary 37.1.1 and then apply the intrinsic-domain core owner theorem.
/-- Source-facing intrinsic-domain corollary: for a closed concave-convex `K`, the lower and upper
conjugates agree pointwise on `ri[R](dom (lowerConjugate K))`. -/
theorem eqOn_ri_dom_lowerConjugate_upperConjugate_of_isConcaveConvex_of_isClosed
    {K : U → XStar → WithTopBot α}
    (hK_shape : IsConcaveConvex R K)
    (hK_closed : IsClosed K) :
    Set.EqOn (Function.uncurry (lowerConjugate K))
      (Function.uncurry (upperConjugate K))
      (ri[R](dom (lowerConjugate K))) := by
  have hLower_shape : IsConcaveConvex R (lowerConjugate K) :=
    lowerConjugate_isConcaveConvex hK_shape hK_closed
  have hLower_lowerClosed : IsLowerClosed (lowerConjugate K) :=
    lowerConjugate_isLowerClosed hK_shape hK_closed
  have hLower_closed : IsClosed (lowerConjugate K) :=
    SaddleFunction.isClosed_of_isLowerClosed hLower_lowerClosed
  have hLower_equiv_upper : lowerConjugate K ∼ upperConjugate K :=
    lowerConjugate_equivalent_upperConjugate hK_shape hK_closed
  exact
    eqOn_ri_dom_lowerConjugate_upperConjugate_of_equivalent_of_isConcaveConvex_of_isClosed
      hLower_shape hLower_closed hLower_equiv_upper

end

end Bifunction

/-! ### Proposition_37_1_2 (from Chap07) -/
noncomputable section

universe u u' v w z

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {UStar : Type u'} {X : Type v} {XStar : Type w} {L : Type z}
variable [HAdd L L L] [HSub L L L]
variable [HasPairing U UStar L] [HasPairing X XStar L]
variable [CompleteLattice L]

-- Proposition 37.1.2 in textbook pointwise notation on the canonical Chapter 37 owners.
recall lowerConjugate_le_upperConjugate
    (K : U → XStar → L) (uStar : UStar) (x : X) :
    K _*(uStar, x) ≤ K ^*(uStar, x)

end

end Bifunction

/-! ### Corollary_37_1_3 (from Chap07) -/
noncomputable section

universe u u' v v'

open scoped Rockafellar

namespace SaddleFunction

section

open Bifunction

variable {R : Type*} {α : Type*}
variable {U : Type u} {UStar : Type u'} {X : Type v} {XStar : Type v'}
variable [Ring R] [PartialOrder R]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [AddCommGroup α]
variable [IsOrderedAddMonoid α]
variable [TopologicalSpace U] [AddCommGroup U] [Module R U]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module R UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module R X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module R XStar]
variable [HasPairing U UStar (WithBotTop α)] [HasPairing X XStar (WithBotTop α)]
variable [HasPairingZeroRight U UStar (WithBotTop α)]
variable [HasPairingZeroLeft X XStar (WithBotTop α)]
variable [SMul R (WithBotTop α)]

local notation "lowerConjugate" =>
  (Bifunction.lowerConjugate : (U → XStar → WithBotTop α) → UStar → X → WithBotTop α)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 37.1.3 turns origin relative-interior hypotheses on the two
  conjugate-domain factors into existence and finiteness of the ambient saddle value of `K`.
- `core/canonical`: the owner layer already present in the chapter is `HasSaddleValue`,
  `maximinValue`, `lowerConjugate`, `dom₁`, `dom₂`, and `ri[R](·)`.
- `bridge/view`: the source domain symbols `C*` and `D*` are written through the Chapter 37 owner
  `lowerConjugate K` and the Chapter 34 coordinate-domain owners `dom₁` and `dom₂`.

Primary mathematical domain:
- minimax theory for closed concave-convex saddle-functions via conjugate-domain geometry.

Domain-style sampling used here:
- `Bifunction.HasSaddleValue` and `Bifunction.maximinValue` from `Definition_36_0_1`;
- `Bifunction.lowerConjugate` from `Definition_37_1_1`;
- `SaddleFunction.dom₁` and `SaddleFunction.dom₂` from `Defn_34_3`;
- `ri[R](·)` from `Chap02.Text_6_8`;
- `Bifunction.lowerConjugate_eq_upperConjugate_of_isConcaveConvex_of_isClosed_of_mem_ri_dom₁_or_mem_ri_dom₂`
  from
  `Corollary_37_1_2`;
- `Bifunction.minimaxValue_eq_neg_lowerConjugate_zero_zero` and
  `Bifunction.maximinValue_eq_neg_upperConjugate_zero_zero` from `Proposition_37_1_3`.

Primitive data vs derived API:
- primitive data: a saddle kernel `K : U → XStar → WithBotTop α` with hypotheses `IsClosed K`,
  `IsConcaveConvex R K`, together with the canonical zero-pairing owners
  `HasPairingZeroRight U UStar (WithBotTop α)` and
  `HasPairingZeroLeft X XStar (WithBotTop α)` needed to identify the Chapter 36 ambient values
  with the Chapter 37 conjugates at the base point `(0, 0)`;
- derived API: the owner-level saddle-value conclusion `HasSaddleValue K` and the finiteness of
  the resulting ambient saddle value.

Redundant source assumptions:
- the source also lists properness, but these two corollary clauses only use the origin-relative
  interior hypotheses on the conjugate-domain owners themselves, so `IsProper K` is redundant and
  removed from the public API.

Layer target: `source-facing`, but the first conclusion is expressed on the canonical Chapter 36
owner `HasSaddleValue K` rather than by restating its defining equality.
-/

-- Proof sketch: combine Proposition 37.1.3 with the standard minimax qualification coming from
-- the origin lying in the relative interior of one conjugate-domain factor, then rewrite the
-- source domain symbols `C*` and `D*` through the canonical Chapter 37 owner
-- `dom₁ (lowerConjugate K)` and `dom₂ (lowerConjugate K)`.
/-- Corollary 37.1.3 (1): if the origin belongs to the relative interior of either conjugate-domain
factor of a closed concave-convex saddle-function `K`, then the ambient maximin and
minimax values of `K` coincide. Here the common conjugate-domain factors `C*` and `D*` are
written as `dom₁ (lowerConjugate K)` and `dom₂ (lowerConjugate K)`. -/
theorem hasSaddleValue_of_zero_mem_ri_conjugateDom₁_or_zero_mem_ri_conjugateDom₂
    {K : U → XStar → WithBotTop α}
    (hK_closed : IsClosed K)
    (hK_concaveConvex : IsConcaveConvex R K)
    (hri :
      (0 : UStar) ∈ ri[R](dom₁ (lowerConjugate K)) ∨
        (0 : X) ∈ ri[R](dom₂ (lowerConjugate K))) :
    HasSaddleValue K := by
  rw [HasSaddleValue, HasSaddleValueOn]
  calc
    maximinValue K = -(K ^*((0 : UStar), (0 : X))) :=
      maximinValue_eq_neg_upperConjugate_zero_zero K
    _ = -(K _*((0 : UStar), (0 : X))) := by
      rw [← lowerConjugate_eq_upperConjugate_of_isConcaveConvex_of_isClosed_of_mem_ri_dom₁_or_mem_ri_dom₂
        hK_concaveConvex hK_closed hri]
    _ = minimaxValue K := by
      symm
      exact minimaxValue_eq_neg_lowerConjugate_zero_zero K

-- Proof sketch: apply the first clause to obtain the common saddle value, then use Proposition
-- 37.1.3 at the zero base point. When the origin lies in the relative interiors of both
-- conjugate-domain factors, the conjugate value at `(0, 0)` is finite, so the common saddle
-- value is finite as well.
/-- Corollary 37.1.3 (2): if the origin belongs to the relative interiors of both conjugate-domain
factors of `K`, equivalently `((0, 0) : UStar × X)` lies in the relative interior of the effective
domain `dom (lowerConjugate K)`, then the common saddle value of `K` is finite. -/
theorem finite_saddleValue_of_zero_mem_ri_conjugateDom₁_and_zero_mem_ri_conjugateDom₂
    {K : U → XStar → WithBotTop α}
    (hK_closed : IsClosed K)
    (hK_concaveConvex : IsConcaveConvex R K)
    (hri : ((0 : UStar), (0 : X)) ∈ ri[R](dom (lowerConjugate K))) :
    ⊥ < maximinValue K ∧ maximinValue K < ⊤ := by
  have hri_dom :
      (0 : UStar) ∈ ri[R](dom₁ (lowerConjugate K)) ∧
        (0 : X) ∈ ri[R](dom₂ (lowerConjugate K)) := by
    simpa [SaddleFunction.dom, ri_prod_eq, Set.mem_prod] using hri
  have hri_dom₁ : (0 : UStar) ∈ ri[R](dom₁ (lowerConjugate K)) := hri_dom.1
  have hri_dom₂ : (0 : X) ∈ ri[R](dom₂ (lowerConjugate K)) := hri_dom.2
  have hmax :
      maximinValue K = -(K _*((0 : UStar), (0 : X))) := by
    calc
      maximinValue K = -(K ^*((0 : UStar), (0 : X))) :=
        maximinValue_eq_neg_upperConjugate_zero_zero K
      _ = -(K _*((0 : UStar), (0 : X))) := by
        rw [← lowerConjugate_eq_upperConjugate_of_isConcaveConvex_of_isClosed_of_mem_ri_dom₁_or_mem_ri_dom₂
          hK_concaveConvex hK_closed (Or.inl hri_dom₁)]
  have hdom₁_zero : (0 : UStar) ∈ dom₁ (lowerConjugate K) :=
    intrinsicInterior_subset hri_dom₁
  have hdom₂_zero : (0 : X) ∈ dom₂ (lowerConjugate K) :=
    intrinsicInterior_subset hri_dom₂
  have hbot_lower : ⊥ < K _*((0 : UStar), (0 : X)) :=
    (mem_dom₁.mp hdom₁_zero) 0
  have htop_lower : K _*((0 : UStar), (0 : X)) < ⊤ :=
    (mem_dom₂.mp hdom₂_zero) 0
  constructor
  · rw [hmax]
    simpa using (WithBotTop.neg_lt_neg_iff).2 htop_lower
  · rw [hmax]
    simpa using (WithBotTop.neg_lt_neg_iff).2 hbot_lower

end

end SaddleFunction

/-! ### Proposition_37_1_3 (from Chap07) -/
noncomputable section

universe u u' v w z

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {UStar : Type u'} {X : Type v} {XStar : Type w} {α : Type z}
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α]
variable [Zero UStar] [Zero X]
variable [HasPairing U UStar (WithTopBot α)] [HasPairing X XStar (WithTopBot α)]
variable [HasPairingZeroRight U UStar (WithTopBot α)]
variable [HasPairingZeroLeft X XStar (WithTopBot α)]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 37.1.3 identifies the ambient minimax and maximin values of a
  saddle kernel `K` with the negatives of the lower and upper conjugates at the base point
  `(0, 0)`.
- `core/canonical`: the owner layer already present in the project is
  `Bifunction.minimaxValue`, `Bifunction.maximinValue`, `Bifunction.lowerConjugate`, and
  `Bifunction.upperConjugate`.
- `bridge/view`: evaluating the Chapter 37 conjugates at `(0, 0)` is exactly the source formula
  once the canonical zero-pairing owners are available, because the affine perturbation in
  Definition 37.1.1 then reduces to `-K` at that base point, and the chapter's canonical codomain
  owner `WithTopBot.negOrderIso` transports the resulting `iSup`/`iInf` values across negation.

Primary mathematical domain:
- conjugate saddle-functions and minimax values.

Domain-style sampling used here:
- `Bifunction.lowerConjugate` from `Definition_37_1_1`;
- `Bifunction.upperConjugate` from `Definition_37_1_1`;
- `Bifunction.maximinValue` from `Definition_36_0_1`;
- `Bifunction.minimaxValue` from `Definition_36_0_1`;
- `WithTopBot.negOrderIso` from `Chap01.EOrder.Operations`.

Primitive data vs derived API:
- primitive data: the saddle kernel `K` and the two zero-pairing owners
  `HasPairingZeroRight U UStar (WithTopBot α)` / `HasPairingZeroLeft X XStar (WithTopBot α)`;
- primitive owner objects reused here: the ambient maximin/minimax values and the lower/upper
  conjugates of `K`;
- derived API: the two zero-basepoint value identities recorded by Proposition 37.1.3.

Layer target: `source-facing`, stated directly on the existing Chapter 36 and Chapter 37 owners
on the chapter's canonical ordered-extended codomain layer `WithTopBot α`, rather than through a
new saddle-value wrapper.
-/

private theorem neg_iSup_eq_iInf_neg {ι : Sort*} (f : ι → WithTopBot α) :
    -(⨆ i, f i) = ⨅ i, -f i := by
  exact congrArg OrderDual.ofDual (WithTopBot.negOrderIso.map_iSup f)

private theorem neg_iInf_eq_iSup_neg {ι : Sort*} (f : ι → WithTopBot α) :
    -(⨅ i, f i) = ⨆ i, -f i := by
  exact congrArg OrderDual.ofDual (WithTopBot.negOrderIso.map_iInf f)

omit [ConditionallyCompleteLinearOrder α] [IsOrderedAddMonoid α] in
private theorem neg_zeroBase_perturbation
    (K : U → XStar → WithTopBot α) (u : U) (xStar : XStar) :
    -((⟪u, (0 : UStar)⟫ₚ + ⟪(0 : X), xStar⟫ₚ) - K u xStar) = K u xStar := by
  calc
    -((⟪u, (0 : UStar)⟫ₚ + ⟪(0 : X), xStar⟫ₚ) - K u xStar)
        = -((0 : WithTopBot α) - K u xStar) := by
            simp [pairing_zero_right, pairing_zero_left]
    _ = -(0 : WithTopBot α) + K u xStar := by
          exact
            WithBotTop.neg_sub
              (Or.inl WithBotTop.zero_ne_bot) (Or.inl WithBotTop.zero_ne_top)
    _ = K u xStar := by simp

local notation:max K " _*₀" => K _*((0 : UStar), (0 : X))
local notation:max K " ^*₀" => K ^*((0 : UStar), (0 : X))

/-- Proposition 37.1.3 (1): the whole-space minimax value of `K` is the negative of its lower
conjugate at the base point `(0, 0)`. -/
theorem minimaxValue_eq_neg_lowerConjugate_zero_zero
    (K : U → XStar → WithTopBot α) :
    minimaxValue K = -(K _*₀) := by
  calc
    minimaxValue K = ⨅ xStar : XStar, ⨆ u : U, K u xStar := by
      simp [minimaxValue, minimaxValueOn]
    _ = ⨅ xStar : XStar,
          -(⨅ u : U, ((⟪u, (0 : UStar)⟫ₚ + ⟪(0 : X), xStar⟫ₚ) - K u xStar)) := by
          refine iInf_congr fun xStar ↦ ?_
          rw [neg_iInf_eq_iSup_neg]
          refine iSup_congr fun u ↦ ?_
          exact (neg_zeroBase_perturbation K u xStar).symm
    _ = -(⨆ xStar : XStar, ⨅ u : U,
          ((⟪u, (0 : UStar)⟫ₚ + ⟪(0 : X), xStar⟫ₚ) - K u xStar)) := by
          symm
          exact neg_iSup_eq_iInf_neg _
    _ = -(K _*₀) := by
          simp [lowerConjugate_apply]

/-- Proposition 37.1.3 (2): the whole-space maximin value of `K` is the negative of its upper
conjugate at the base point `(0, 0)`. -/
theorem maximinValue_eq_neg_upperConjugate_zero_zero
    (K : U → XStar → WithTopBot α) :
    maximinValue K = -(K ^*₀) := by
  calc
    maximinValue K = ⨆ u : U, ⨅ xStar : XStar, K u xStar := by
      simp [maximinValue, maximinValueOn]
    _ = ⨆ u : U,
          -(⨆ xStar : XStar, ((⟪u, (0 : UStar)⟫ₚ + ⟪(0 : X), xStar⟫ₚ) - K u xStar)) := by
          refine iSup_congr fun u ↦ ?_
          rw [neg_iSup_eq_iInf_neg]
          refine iInf_congr fun xStar ↦ ?_
          exact (neg_zeroBase_perturbation K u xStar).symm
    _ = -(⨅ u : U, ⨆ xStar : XStar,
          ((⟪u, (0 : UStar)⟫ₚ + ⟪(0 : X), xStar⟫ₚ) - K u xStar)) := by
          symm
          exact neg_iInf_eq_iSup_neg _
    _ = -(K ^*₀) := by
          simp [upperConjugate_apply]

end

end Bifunction
