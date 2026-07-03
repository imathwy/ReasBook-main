import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_6_30_4 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.4 compares the Chapter 6 concave conjugate of `g` with the
  Chapter 12 Fenchel conjugate of the negated function `-g`.
- `core/canonical`: the owner declarations are already `concaveConjugate` and `convexConjugate`
  (notation `(·)⋆`) on the pairing-based `WithBotTop α` layer.
- `bridge/view`: this file contributes only the sign-duality comparison theorem between those two
  existing owners; it does not introduce a new conjugation wrapper.

Domain-style sampling:
- `concaveConjugate` and `concaveConjugate_eq_iInf_pairing_sub` from
  `Chap06.Definition_6_30_4`;
- `convexConjugate`, notation `(·)⋆`, and
  `convexConjugate_eq_neg_iInf_sub_pairing` from `Chap03.Defn_12_2`.

Primitive data vs derived API:
- primitive owners already upstream: `concaveConjugate` and `convexConjugate`;
- derived API here: the sign-twisted bridge
  `g* = (fun y ↦ - ((-g)⋆ (-y)))`, with a pointwise corollary.

Layer target: `bridge/view`. The properness and concavity hypotheses from the textbook are
redundant for this algebraic identity, so the theorem is stated at the weaker canonical
pairing-and-order layer actually used by the formula.
-/

section

variable {X : Type u} {Y : Type v} {α : Type w}
variable [AddCommGroup α] [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]
variable [Neg Y] [HasPairing X Y α] [HasPairingNegRight X Y α]

-- Proof sketch: rewrite `concaveConjugate g y` by its defining `iInf` formula and rewrite
-- `-((-g)⋆ (-y))` using `convexConjugate_eq_neg_iInf_sub_pairing`. The owner
-- `HasPairingNegRight` converts the pairing term at `-y`, and the remaining pointwise integrands
-- agree by commutativity of addition in `WithBotTop α`.
/-- Theorem 6.30.4: the concave conjugate of `g` at `y` is the negative of the Fenchel conjugate
of the negated function `-g` evaluated at `-y`, stated at the function-owner layer. -/
theorem concaveConjugate_eq_neg_convexConjugate_neg
    (g : X → WithBotTop α) :
    g∗ = fun y ↦ -((-g)⋆ (-y)) := by
  ext y
  rw [concaveConjugate_eq_iInf_pairing_sub, convexConjugate_eq_neg_iInf_sub_pairing]
  simp only [neg_neg]
  refine iInf_congr fun x ↦ ?_
  have hpair :
      (((⟪x, -y⟫ₚ : α) : WithBotTop α)) = -(((⟪x, y⟫ₚ : α) : WithBotTop α)) := by
    exact
      congrArg ((↑) : α → WithBotTop α)
        (HasPairingNegRight.pairing_neg_right (x := x) (y := y))
  change (((⟪x, y⟫ₚ : α) : WithBotTop α) + -g x) =
    (-g x + -(((⟪x, -y⟫ₚ : α) : WithBotTop α)))
  rw [hpair]
  simp [add_comm]

/-- Pointwise companion of Theorem 6.30.4. -/
theorem concaveConjugate_eq_neg_convexConjugate_neg_apply
    (g : X → WithBotTop α)
    (y : Y) :
    g∗ y = -((-g)⋆ (-y)) := by
  simpa using congrFun (concaveConjugate_eq_neg_convexConjugate_neg g) y

end

section

variable {X : Type u} {Y : Type v} {α : Type w}
variable [Field α] [ConditionallyCompleteLinearOrder α] [IsStrictOrderedRing α]
variable [MulAction α X]
variable [Neg Y] [HasPairing X Y α] [HasPairingNegRight X Y α]

/-- Positive-scalar companion of Theorem 6.30.4: when `λ > 0`, the concave conjugate of `g λ`
is the pointwise left scalar multiple `λ g*`. -/
theorem concaveConjugate_rightScalarMul_eq_left_smul_of_pos
    (g : X → WithBotTop α) {lam : α} (hlam : (0 : α) < lam) :
    ((⟨lam, hlam.le⟩ : Set.Ici (0 : α)) •ʳ g)∗ =
      (lam : WithBotTop α) • g∗ := by
  let lamNN : Set.Ici (0 : α) := ⟨lam, hlam.le⟩
  have hneg_rightScalarMul :
      ((lamNN •ʳ (-g) : X → WithBotTop α)) =
        -((lamNN •ʳ g) : X → WithBotTop α) := by
    ext x
    have hleft :
        (lamNN •ʳ (-g)) x =
          ((lam : WithBotTop α) * (-g (lam⁻¹ • x))) := by
      simpa using
        (rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos (f := -g) (a := lam) hlam x)
    have hright :
        (lamNN •ʳ g) x =
          ((lam : WithBotTop α) * (g (lam⁻¹ • x))) := by
      simpa using
        (rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos (f := g) (a := lam) hlam x)
    calc
      (lamNN •ʳ (-g)) x = ((lam : WithBotTop α) * (-g (lam⁻¹ • x))) := hleft
      _ = -((lam : WithBotTop α) * (g (lam⁻¹ • x))) := by
            simp [WithBotTop.mul_neg]
      _ = -((lamNN •ʳ g) x) := by rw [hright]
  have hconv :
      (((lamNN •ʳ (-g))⋆ : Y → WithBotTop α)) =
        ((lam : WithBotTop α) • (((-g)⋆ : Y → WithBotTop α))) := by
    simpa using
      (convexConjugate_rightScalarMul_eq_left_smul_of_pos (f := -g) (lam := lam) hlam)
  ext y
  have hbase :
      (((lamNN •ʳ g)∗ : Y → WithBotTop α) y) =
        -(((-(lamNN •ʳ g : X → WithBotTop α))⋆ :
          Y → WithBotTop α) (-y)) := by
    simpa using
      (concaveConjugate_eq_neg_convexConjugate_neg_apply
        (g := ((lamNN •ʳ g) : X → WithBotTop α)) (y := y))
  calc
    (((lamNN •ʳ g)∗) : Y → WithBotTop α) y
        = -(((-(lamNN •ʳ g : X → WithBotTop α))⋆ :
          Y → WithBotTop α) (-y)) := hbase
    _ = -(((lamNN •ʳ (-g))⋆ : Y → WithBotTop α) (-y)) := by
          rw [← hneg_rightScalarMul]
    _ = -(((lam : WithBotTop α) • (((-g)⋆ : Y → WithBotTop α))) (-y)) := by
          rw [hconv]
    _ = ((lam : WithBotTop α) • (g∗ : Y → WithBotTop α)) y := by
          rw [Pi.smul_apply, Pi.smul_apply,
            concaveConjugate_eq_neg_convexConjugate_neg_apply (g := g) (y := y)]
          simp [WithBotTop.mul_neg]

end

/-! ### Corollary_6_30_5 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 6.30.5 says that for a closed convex bifunction `F`, consistency of
  one side together with strong consistency of the other side forces attainment of the optimal
  value on the merely consistent side.
- `core/canonical`: the existing Chapter 6 owners are `IsConsistent`, `IsStronglyConsistent`,
  `objective`, `adjoint`, `IsDualKuhnTuckerVector`, the normality theorems from
  `Theorem_6_30_17`, and the optimizer/Kuhn--Tucker bridge theorems from `Theorem_6_30_19`.
- `bridge/view`: the source phrase “has an optimal solution” is rendered canonically by the
  optimizer owners `IsMinOn` and `IsMaxOn` for the primal zero-slice objective `(F)₀` and the
  dual zero-slice objective `(F⋆)₀`.

Primary mathematical domain:
- convex duality for closed convex bifunctions on paired scalar-parametric spaces.

Domain-style sampling used here:
- `IsStronglyConsistent` from Definition 6.29.10;
- `IsDualKuhnTuckerVector` from Definition 6.30.17;
- `primalNormal_and_dualNormal_of_sufficientNormalityHypothesis` from Theorem 6.30.17.
- `adjoint` / notation `(·)⋆` from Definition 6.30.14;
- `isDualKuhnTuckerVector_iff_isMinOn_objective_of_normality` and
  `isKuhnTuckerVector_iff_isMaxOn_dualObjective_of_normality` from
  Theorem 6.30.19.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owners already upstream: primal consistency `IsConsistent F`, dual consistency
  `IsConsistent (F⋆)`, primal strong consistency `IsStronglyConsistent 𝕜 F`, and dual strong
  consistency `IsStronglyConsistent 𝕜 (F⋆)`;
- derived API added here: the two source attainment conclusions, split atomically.

Layer target: `source-facing`, stated directly on the established Chapter 6 owner vocabulary and
the same scalar-parametric pairing ambient layer already used by the Chapter 6 normality and
optimality bridge theorems, with no extra primal-dual program package.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [AddCommGroup XStar] [Module 𝕜 XStar] [TopologicalSpace XStar]
variable [Neg UStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => ((adjoint XStar UStar F) : XStar → UStar → WithBotTop 𝕜)

-- Proof sketch: dual strong consistency is one of the sufficient normality hypotheses in
-- Theorem 6.30.17, so both primal and dual normality hold. Strong consistency also implies dual
-- consistency, while the assumed primal consistency rules out the exceptional infinite common
-- value. A dual Kuhn--Tucker vector then exists by the chapter's Kuhn--Tucker existence route,
-- and the Chapter 6 primal-optimality bridge
-- `isDualKuhnTuckerVector_iff_isMinOn_objective_of_normality` identifies that vector
-- with a primal minimizer of `(F)₀`.
/-- Corollary 6.30.5 (1): if `F` is a closed convex bifunction, the primal program `(P)` is
consistent, and the adjoint dual program `(P*)` is strongly consistent, then `(P)` has an
optimal solution, rendered canonically as a minimizer of the primal zero-slice objective
`(F)₀`. -/
theorem exists_isMinOn_objective_of_isConsistent_of_isStronglyConsistent_adjoint
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F))
    (hP_consistent : IsConsistent F)
    (hPstar_strong : IsStronglyConsistent 𝕜 F⋆) :
    ∃ x : X, IsMinOn ((F)₀ : X → WithBotTop 𝕜) Set.univ x := sorry

-- Proof sketch: primal strong consistency gives the sufficient normality hypothesis from
-- Theorem 6.30.17, hence both normality identities at `0`. Strong consistency also implies
-- primal consistency, and the assumed dual consistency makes the common primal-dual value finite.
-- A primal Kuhn--Tucker vector then exists by the chapter's Kuhn--Tucker existence route, and
-- the Chapter 6 dual-optimality bridge
-- `isKuhnTuckerVector_iff_isMaxOn_dualObjective_of_normality` identifies such a
-- vector with a maximizer of the dual zero-slice objective `(F⋆)₀`.
/-- Corollary 6.30.5 (2): if `F` is a closed convex bifunction, the primal program `(P)` is
strongly consistent, and the adjoint dual program `(P*)` is consistent, then `(P*)` has an
optimal solution, rendered canonically as a maximizer of the dual zero-slice objective
`(F⋆)₀`. -/
theorem
    exists_isMaxOn_objective_adjoint_of_isStronglyConsistent_of_isConsistent_adjoint
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F))
    (hP_strong : IsStronglyConsistent 𝕜 F)
    (hPstar_consistent : IsConsistent F⋆) :
    ∃ uStar : UStar, IsMaxOn ((F⋆)₀ : UStar → WithBotTop 𝕜) Set.univ uStar := sorry

end

end Bifunction

/-! ### Definition_6_30_5 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w

section

variable {𝕜 : Type w} [Add 𝕜] [LE 𝕜]
variable {E : Type u} [Sub E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 6.30.5 introduces the subdifferential of a concave function `g`,
  i.e. the affine majorants of `g`.
- `core/canonical`: the chapter owner for subdifferentials is already `_root_.subdifferentialAt`,
  defined by the supporting-affine inequality in Chapter 23.
- `bridge/view`: the concave owner here should expose the same primitive pairing inequality data as
  the Chapter 23 owner, while the relation to `_root_.subdifferentialAt (-g)` is a theorem-level
  bridge rather than owner data.

Domain-style sampling used here:
- `_root_.subdifferentialAt` and `_root_.mem_subdifferentialAt` from
  `Chap05.Definition_23_0_6`;
- `Function.subdifferentialAt` from the same file, which gives the inner-product vector-valued
  bridge;
- `WithTopBot.negOrderIso` from `Chap01.EOrder.Operations`, which gives the sign transport to
  the Chapter 23 convex owner on `-g`;
- the project pairing owner `HasPairing`, so the concave bridge owner is not frozen to one concrete
  dual model.

Primitive data vs derived API:
- primitive owner data: the concave affine-majorant inequality in pairing form;
- derived bridge API: characterizations that compare this owner to
  `_root_.subdifferentialAt (-g)` by negating the dual variable.

Layer target: `source-facing` owner with intrinsic pairing data.

Notation evaluation:
- this file introduces parser-safe concave notation `∂⁺[Y]g(x)` and `∂⁺ g at x`.
- the plain textbook symbol `∂g(x)` is intentionally avoided on the concave side to prevent
  collision with the convex owner notation `∂[Y]f(x)` and Lean's existing differential surfaces.
-/

/-- Definition 6.30.5: the subdifferential of a concave function at `x` is the set of dual
elements that globally majorize `g` by affine support at `x`, in any paired dual carrier `Y`. -/
def concaveSubdifferentialAt (g : E → WithTopBot 𝕜) (x : E)
    {Y : Type v} [HasPairing E Y 𝕜] : Set Y :=
  {xStar | ∀ z, g z ≤ g x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)}

scoped[Rockafellar] notation "∂⁺ " g " at " x => concaveSubdifferentialAt g x
scoped[Rockafellar] notation "∂⁺[" Y "]" g "(" x ")" =>
  concaveSubdifferentialAt (Y := Y) g x

/-- Pairing-level membership form of `concaveSubdifferentialAt`. -/
@[simp] theorem mem_concaveSubdifferentialAt_pairing
    {g : E → WithTopBot 𝕜} {x : E} {Y : Type v} [HasPairing E Y 𝕜] {xStar : Y} :
    xStar ∈ (∂⁺[Y]g(x)) ↔
      ∀ z, g z ≤ g x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  Iff.rfl

end

section

variable {𝕜 : Type w} [AddCommGroup 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable {E : Type u} [Sub E]

/-- Pairing-level sign bridge to the Chapter 23 owner: in any dual carrier whose pairing is
compatible with right negation, a concave subgradient of `g` is exactly the negative of a convex
subgradient of `-g`. -/
@[simp] theorem mem_concaveSubdifferentialAt_pairing_iff_neg_mem_subdifferentialAt_neg
    {g : E → WithTopBot 𝕜} {x : E} {Y : Type (max u w)} [Neg Y] [HasPairing E Y 𝕜]
    [HasPairingNegRight E Y 𝕜] {xStar : Y} :
    xStar ∈ (∂⁺[Y]g(x)) ↔
      -xStar ∈ (∂[Y] (-g)(x)) := by
  have hneg_add_coe (x0 : WithTopBot 𝕜) (t0 : 𝕜) :
      -(x0 + ((t0 : 𝕜) : WithTopBot 𝕜)) = -x0 + -((t0 : 𝕜) : WithTopBot 𝕜) := by
    cases x0 using WithBotTop.rec with
    | bot =>
        rfl
    | top =>
        rfl
    | coe a =>
        change (((-(a + t0) : 𝕜) : 𝕜) : WithTopBot 𝕜) =
          (((-a + -t0 : 𝕜) : 𝕜) : WithTopBot 𝕜)
        exact
          congrArg (fun u : 𝕜 => (u : WithTopBot 𝕜)) <|
            by
              calc
                (-(a + t0) : 𝕜) = -t0 + -a := _root_.neg_add_rev a t0
                _ = -a + -t0 := by rw [add_comm]
  constructor
  · intro hx
    rw [mem_concaveSubdifferentialAt_pairing] at hx
    rw [_root_.mem_subdifferentialAt_pairing]
    intro z
    have hz := hx z
    let a : WithTopBot 𝕜 := ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)
    have hpair : (((⟪z - x, -xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) = -a := by
      exact
        congrArg ((↑) : 𝕜 → WithTopBot 𝕜)
          (HasPairingNegRight.pairing_neg_right (x := z - x) (y := xStar))
    have hzneg : -(g x + a) ≤ -g z := by
      simpa [a] using
        ((WithTopBot.negOrderIso (α := 𝕜)).monotone hz)
    have hnegadd : -(g x + a) = -g x + -a := by
      simpa [a] using
        hneg_add_coe (x0 := g x) (t0 := (⟪z - x, xStar⟫ₚ : 𝕜))
    calc
      (-g) z = -g z := rfl
      _ ≥ -(g x + a) := hzneg
      _ = -g x + -a := hnegadd
      _ = -g x + (((⟪z - x, -xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) := by rw [← hpair]
      _ = (-g) x + (((⟪z - x, -xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) := by rfl
  · intro hx
    rw [_root_.mem_subdifferentialAt_pairing] at hx
    rw [mem_concaveSubdifferentialAt_pairing]
    intro z
    have hz : (-g) x + (((⟪z - x, -xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) ≤ (-g) z := hx z
    let a : WithTopBot 𝕜 := ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)
    have hpair : (((⟪z - x, -xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) = -a := by
      exact
        congrArg ((↑) : 𝕜 → WithTopBot 𝕜)
          (HasPairingNegRight.pairing_neg_right (x := z - x) (y := xStar))
    have hzneg : g z ≤ -((-g) x + (((⟪z - x, -xStar⟫ₚ : 𝕜) : WithTopBot 𝕜))) := by
      simpa using
        ((WithTopBot.negOrderIso (α := 𝕜)).monotone hz)
    have hnegadd :
        -((-g) x + (((⟪z - x, -xStar⟫ₚ : 𝕜) : WithTopBot 𝕜))) =
          -(-g x) + -(((⟪z - x, -xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) := by
      simpa using
        hneg_add_coe (x0 := (-g) x) (t0 := (⟪z - x, -xStar⟫ₚ : 𝕜))
    calc
      g z ≤ -((-g) x + (((⟪z - x, -xStar⟫ₚ : 𝕜) : WithTopBot 𝕜))) := hzneg
      _ = -(-g x) + -(((⟪z - x, -xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) := hnegadd
      _ = g x + -(((⟪z - x, -xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) := by simp
      _ = g x + a := by
            rw [hpair]
            simp

/-- Pairing-level owner bridge to Chapter 23: `concaveSubdifferentialAt` is the pullback of the
convex subdifferential of the negated function along negation on any compatible dual carrier. -/
theorem concaveSubdifferentialAt_eq_preimage_neg_subdifferentialAt_neg_pairing
    {Y : Type (max u w)} [Neg Y] [HasPairing E Y 𝕜] [HasPairingNegRight E Y 𝕜]
    (g : E → WithTopBot 𝕜) (x : E) :
    (∂⁺[Y]g(x)) = Neg.neg ⁻¹' (∂[Y] (-g)(x)) := by
  ext xStar
  exact
    (mem_concaveSubdifferentialAt_pairing_iff_neg_mem_subdifferentialAt_neg
      (g := g) (x := x) (xStar := xStar) (Y := Y))

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [LE 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A functional belongs to the concave subdifferential at `x` exactly when it globally
majorizes `g` by its affine support at `x`. -/
@[simp] theorem mem_concaveSubdifferentialAt {g : E → WithTopBot 𝕜} {x : E}
    {xStar : StrongDual 𝕜 E} :
    xStar ∈ (∂⁺ g at x) ↔
      ∀ z, g z ≤ g x + ((xStar (z - x) : 𝕜) : WithTopBot 𝕜) := by
  rw [mem_concaveSubdifferentialAt_pairing (Y := StrongDual 𝕜 E)]
  change
      (∀ z, g z ≤ g x + (((HasLinearPairing.pairingLinear (z - x)) xStar : 𝕜) :
        WithTopBot 𝕜)) ↔
      ∀ z, g z ≤ g x + ((xStar (z - x) : 𝕜) : WithTopBot 𝕜)
  rfl

end

section

variable {𝕜 : Type w} [NormedField 𝕜] [PartialOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Bridge to the Chapter 23 convex owner: a concave subgradient of `g` at `x` is exactly the
negative of a convex subgradient of `-g` at `x`. -/
@[simp] theorem mem_concaveSubdifferentialAt_iff_neg_mem_subdifferentialAt_neg
    {g : E → WithTopBot 𝕜} {x : E} {xStar : StrongDual 𝕜 E} :
    xStar ∈ (∂⁺ g at x) ↔
      -xStar ∈ (∂ (-g) at x) := by
  exact
    (mem_concaveSubdifferentialAt_pairing_iff_neg_mem_subdifferentialAt_neg
      (Y := StrongDual 𝕜 E) (g := g) (x := x) (xStar := xStar))

/-- Owner-level bridge to Chapter 23: the concave subdifferential is the pullback of the convex
subdifferential of the negated function along negation on the dual. -/
theorem concaveSubdifferentialAt_eq_preimage_neg_subdifferentialAt_neg
    (g : E → WithTopBot 𝕜) (x : E) :
    (∂⁺ g at x : Set (StrongDual 𝕜 E)) =
      Neg.neg ⁻¹' (∂ (-g) at x) := by
  exact
    (concaveSubdifferentialAt_eq_preimage_neg_subdifferentialAt_neg_pairing
      (Y := StrongDual 𝕜 E) g x)

/-- The intrinsic dual-valued concave subdifferential is always a closed convex subset of the
dual. -/
theorem isClosed_and_convex_concaveSubdifferentialAt
    (g : E → WithTopBot 𝕜) (x : E) :
    IsClosed (∂⁺ g at x : Set (StrongDual 𝕜 E)) ∧
      Convex 𝕜 (∂⁺ g at x : Set (StrongDual 𝕜 E)) := by
  sorry

theorem concaveSubdifferentialAt_isClosed (g : E → WithTopBot 𝕜) (x : E) :
    IsClosed (∂⁺ g at x : Set (StrongDual 𝕜 E)) :=
  (isClosed_and_convex_concaveSubdifferentialAt g x).1

theorem concaveSubdifferentialAt_convex (g : E → WithTopBot 𝕜) (x : E) :
    Convex 𝕜 (∂⁺ g at x : Set (StrongDual 𝕜 E)) :=
  (isClosed_and_convex_concaveSubdifferentialAt g x).2

end

section

variable {𝕜 : Type w} [RCLike 𝕜] [Preorder 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Function

/-!
Source/core/bridge triage for the inner-product specialization.

- `source-facing`: Section 6.30 uses vector subgradients in an ambient inner-product model.
- `core/canonical`: the owner remains `_root_.concaveSubdifferentialAt`, pairing-based over an
  arbitrary dual carrier.
- `bridge/view`: `Function.concaveSubdifferentialAt` is the Fréchet-Riesz transport of that owner,
  while the sign bridge to `Function.subdifferentialAt (-g)` is inherited from the dual owner.
-/

/-- In an ordered inner-product space, the source's vector-valued concave subdifferential is the
pullback of `_root_.concaveSubdifferentialAt` along `InnerProductSpace.toDualMap`. -/
abbrev concaveSubdifferentialAt (g : E → WithTopBot 𝕜) (x : E) : Set E :=
  (InnerProductSpace.toDualMap 𝕜 E) ⁻¹' (∂⁺ g at x)

scoped[Rockafellar] notation "∂ᵥ⁺" g "(" x ")" => Function.concaveSubdifferentialAt g x

@[simp] theorem mem_concaveSubdifferentialAt {g : E → WithTopBot 𝕜} {x xStar : E} :
    xStar ∈ (∂ᵥ⁺ g(x)) ↔
      ∀ z, g z ≤ g x + ((inner 𝕜 xStar (z - x) : 𝕜) : WithTopBot 𝕜) := by
  change InnerProductSpace.toDualMap 𝕜 E xStar ∈ (∂⁺ g at x) ↔
      ∀ z, g z ≤ g x + ((inner 𝕜 xStar (z - x) : 𝕜) : WithTopBot 𝕜)
  rw [_root_.mem_concaveSubdifferentialAt]
  simp [InnerProductSpace.toDualMap_apply_apply]

end Function

end

section

variable {𝕜 : Type w} [RCLike 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Function

/-- Inner-product bridge to the Chapter 23 vector owner: a concave subgradient of `g` is exactly
the negative of a convex subgradient of `-g`. -/
@[simp] theorem mem_concaveSubdifferentialAt_iff_neg_mem_subdifferentialAt_neg
    {g : E → WithTopBot 𝕜} {x xStar : E} :
    xStar ∈ (∂ᵥ⁺ g(x)) ↔ -xStar ∈ (∂ᵥ(-g)(x)) := by
  change InnerProductSpace.toDualMap 𝕜 E xStar ∈ (∂⁺ g at x) ↔
      InnerProductSpace.toDualMap 𝕜 E (-xStar) ∈ (∂ (-g) at x)
  rw [map_neg]
  exact
    (_root_.mem_concaveSubdifferentialAt_iff_neg_mem_subdifferentialAt_neg
      (g := g) (x := x) (xStar := InnerProductSpace.toDualMap 𝕜 E xStar))

/-- Inner-product owner-level bridge to Chapter 23: the source's vector-valued concave
subdifferential is the pullback of the vector-valued convex subdifferential of `-g` along
negation. -/
theorem concaveSubdifferentialAt_eq_preimage_neg_subdifferentialAt_neg
    (g : E → WithTopBot 𝕜) (x : E) :
    (∂ᵥ⁺ g(x)) = Neg.neg ⁻¹' (∂ᵥ(-g)(x)) := by
  ext xStar
  change xStar ∈ (∂ᵥ⁺ g(x)) ↔ -xStar ∈ (∂ᵥ(-g)(x))
  exact
    (mem_concaveSubdifferentialAt_iff_neg_mem_subdifferentialAt_neg
      (g := g) (x := x) (xStar := xStar))

/-- The vector-valued concave subdifferential is always a closed convex subset of the ambient
inner-product space. -/
theorem isClosed_and_convex_concaveSubdifferentialAt
    (g : E → WithTopBot 𝕜) (x : E) :
    IsClosed (∂ᵥ⁺ g(x)) ∧ Convex 𝕜 (∂ᵥ⁺ g(x)) := by
  sorry

theorem concaveSubdifferentialAt_isClosed (g : E → WithTopBot 𝕜) (x : E) :
    IsClosed (∂ᵥ⁺ g(x)) :=
  (isClosed_and_convex_concaveSubdifferentialAt g x).1

theorem concaveSubdifferentialAt_convex (g : E → WithTopBot 𝕜) (x : E) :
    Convex 𝕜 (∂ᵥ⁺ g(x)) :=
  (isClosed_and_convex_concaveSubdifferentialAt g x).2

end Function

end

/-! ### Theorem_6_30_5 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: the Chapter 6 item at `6.30.5` is the concave-side subdifferential notion and
  its pointwise affine-majorant membership criterion.
- `core/canonical`: the owner abstraction for subdifferentials in this chapter is already
  `_root_.subdifferentialAt` from Chapter 23; on the concave side this is exposed by
  `_root_.concaveSubdifferentialAt`, on the canonical extended codomain layer `WithTopBot`.
- `bridge/view`: `Definition_6_30_5` also provides stronger-model bridge views (`StrongDual` and
  inner-product transport), but this source-facing theorem file keeps the intrinsic pairing layer
  as primary.

Domain-style sampling:
- `_root_.subdifferentialAt` and `_root_.mem_subdifferentialAt` from
  `Chap05.Definition_23_0_6`;
- `_root_.concaveSubdifferentialAt` and
  `_root_.mem_concaveSubdifferentialAt_pairing` from
  `Chap06.Definition_6_30_5`.

Primitive data vs derived API:
- primitive owner data for this item already lives in `Definition_6_30_5`;
- the intrinsic source-facing pointwise inequality is
  `_root_.mem_concaveSubdifferentialAt_pairing`; concrete bridge formulations are derived views.

Layer target: `bridge/view`. This theorem-shaped file adds no new mathematics beyond the owner and
its intrinsic membership specification already introduced in `Definition_6_30_5`, so the faithful
refinement is direct recall rather than a parallel wrapper.
-/

/- The concave-side subdifferential at `x` is already owned by the Chapter 6 bridge declaration
`concaveSubdifferentialAt`; this file reuses that owner directly instead of introducing a second
theorem-level alias. -/
recall concaveSubdifferentialAt

/- The source affine-majorant characterization is already the canonical companion theorem
`mem_concaveSubdifferentialAt_pairing` at the intrinsic pairing layer. -/
recall mem_concaveSubdifferentialAt_pairing

/- The canonical sign bridge is exposed directly on notation surfaces
`x⋆ ∈ ∂⁺[Y]g(x) ↔ -x⋆ ∈ ∂[Y](-g)(x)`, avoiding raw `(Y := Y)` owner noise. -/
recall mem_concaveSubdifferentialAt_pairing_iff_neg_mem_subdifferentialAt_neg

/- Owner-level sign bridge at the same canonical notation surface. -/
recall concaveSubdifferentialAt_eq_preimage_neg_subdifferentialAt_neg_pairing

/-! ### Definition_6_30_6 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.6 introduces the terminology that a vector `x*` is a
  subgradient of a concave function `g` at `x` when it satisfies the global affine-support
  inequality.
- `core/canonical`: the chapter owner for this notion is the pairing-level set
  `_root_.concaveSubdifferentialAt`, with primitive pairing membership criterion
  `_root_.mem_concaveSubdifferentialAt_pairing`.
- `bridge/view`: the Euclidean vector statement is the Fréchet-Riesz specialization
  `Function.mem_concaveSubdifferentialAt`.

Domain-style sampling:
- `_root_.concaveSubdifferentialAt`,
  `_root_.mem_concaveSubdifferentialAt_pairing`,
  `_root_.mem_concaveSubdifferentialAt` from `Chap06.Definition_6_30_5`;
- `Function.concaveSubdifferentialAt` and `Function.mem_concaveSubdifferentialAt`, the Euclidean
  bridge specializations from the same file.

Primitive data vs derived API:
- primitive owner data already exist upstream as `_root_.concaveSubdifferentialAt g x`;
- derived source-facing `StrongDual` and Euclidean APIs are obtained by specialization.

Abstraction audit for this file:
- codomain/scalar/model-owner specialization (`EReal`, `ℝ`, default `StrongDual`) is inherited from
  the upstream owner in `Definition_6_30_5` and its Chapter 23 root owner
  `_root_.subdifferentialAt`; this file is not the first owner source for those parameters.
- therefore this item keeps a pure recall surface and exposes the pairing theorem first.
- any migration toward a more general codomain/scalar/pairing layer must start upstream from those
  owner declarations, then propagate to this recall-only file.

Layer target: `source-facing` recall of the intrinsic pairing membership theorem, followed by the
`StrongDual` and Euclidean bridge recalls. Introducing a new `IsSubgradientAt` alias here would
duplicate canonical owners without adding new mathematics.
-/

/- Definition 6.30.6, intrinsic owner form: for any pairing codomain, a functional is a subgradient
at `x` exactly when it belongs to the concave subdifferential at `x`, equivalently when it
satisfies the global affine-support inequality. -/
recall mem_concaveSubdifferentialAt_pairing

/- Definition 6.30.6, default dual-model bridge: the same criterion specialized to the chapter's
canonical default model `StrongDual ℝ E`. -/
recall mem_concaveSubdifferentialAt

namespace Function

/- Definition 6.30.6, Euclidean bridge form: in `ℝ^n`-style inner-product form, vectors satisfy
the same subgradient criterion via Fréchet-Riesz identification with the dual. -/
recall mem_concaveSubdifferentialAt

end Function

/-! ### Theorem_6_30_6 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u

section

variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace Function.IsClosedProperConvex

variable {f : E → WithTopBot 𝕜} {x : E} {xStar : StrongDual 𝕜 E}

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.6 is the Fenchel-conjugate symmetry of the subdifferential
  relation for a closed proper convex function.
- `core/canonical`: the owner-level statement is intrinsically relation-theoretic on
  `_root_.subdifferentialGraph`, namely `subdifferentialGraph_convexConjugate_eq_inv`.
- `bridge/view`: the Euclidean same-carrier statement
  `Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff` remains available
  upstream as a Fréchet-Riesz bridge; this file keeps the intrinsic owner surface only.

Domain-style sampling used here:
- `_root_.subdifferentialAt` and `_root_.subdifferentialGraph` from
  `Chap05.Definition_23_0_6` / `Chap05.Definition_5_24_3`;
- `subdifferentialGraph_convexConjugate_eq_inv` from `Chap05.Text_26_0_1`;
- `SetRel.mem_inv` from mathlib `Data.Rel`;
- convex conjugation notation `(·)⋆`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`.

Primitive data vs derived API:
- primitive owner inputs: a function `g : E → WithTopBot 𝕜`, primal point `x : E`,
  dual point `xStar : StrongDual 𝕜 E`, and `g.IsClosedProperConvex`;
- derived bridge API (upstream): the Euclidean same-carrier subgradient equivalence in
  Corollary 23.5.1.

Layer target: expose Theorem 6.30.6 on the intrinsic pairing/graph owner layer.

Scalar/ambient check:
- this declaration no longer uses `InnerProductSpace` or `CompleteSpace`;
- the scalar is generalized from `ℝ` to a conditionally complete ordered normed field `𝕜`,
  matching the primitive owner theorem `subdifferentialGraph_convexConjugate_eq_inv`.
-/

-- Proof sketch: `subdifferentialGraph_convexConjugate_eq_inv` gives graph-level inversion for
-- closed proper convex `f`. Evaluating that relation identity at the pair `(xStar, x)` and
-- rewriting membership in an inverse relation with `SetRel.mem_inv` gives exactly the two
-- owner-level subdifferential membership clauses.
/-- Theorem 6.30.6, intrinsic owner form on the strong-dual bridge: for a closed proper convex
function, subgradient membership for the conjugate at `xStar : StrongDual 𝕜 E` is equivalent to
primal-side subgradient membership at `x`. -/
theorem mem_subdifferentialAt_convexConjugate_iff_strongDual
    (hf : IsClosedProperConvex[𝕜] f) :
    x ∈ (∂[E](f⋆)(xStar)) ↔ xStar ∈ (∂ f at x) := by
  have hgraphEq :
      gph∂[E](f⋆) = (gph∂(f)).inv :=
    _root_.subdifferentialGraph_convexConjugate_eq_inv (f := f) hf
  have hpair :
      (xStar, x) ∈ gph∂[E](f⋆) ↔
        (xStar, x) ∈ (gph∂(f)).inv :=
    Iff.of_eq (congrArg (fun R => (xStar, x) ∈ R) hgraphEq)
  change
      (xStar, x) ∈ gph∂[E](f⋆) ↔
        (x, xStar) ∈ gph∂(f)
  exact hpair.trans (SetRel.mem_inv (R := gph∂(f)) (a := x) (b := xStar))

end Function.IsClosedProperConvex

end

/-! ### Definition_6_30_7 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.7 introduces the terminology that the set-valued map
  `x ↦ ∂g(x)` is the subdifferential of `g`.
- `core/canonical`: the chapter's intrinsic owner for this map is
  `_root_.concaveSubdifferentialAt` from `Definition_6_30_5`.
- `bridge/view`: `Function.concaveSubdifferentialAt` is the Fréchet-Riesz Euclidean
  specialization of that intrinsic owner.
- this item adds no new mathematical data beyond those existing owners, so the correct
  statement-stage entry is direct recall rather than a fresh alias.

Domain-style sampling:
- `_root_.concaveSubdifferentialAt` and `_root_.mem_concaveSubdifferentialAt` from
  `Definition_6_30_5`;
- `Function.concaveSubdifferentialAt`, the Euclidean bridge owner from the same file.

Layer target: `source-facing` terminology recall of the intrinsic owner, together with its
Euclidean bridge recall.
-/

/- Definition 6.30.7, intrinsic owner form: the set-valued mapping
`x ↦ _root_.concaveSubdifferentialAt g x` is called the subdifferential of `g`. -/
recall concaveSubdifferentialAt

namespace Function

/- Definition 6.30.7, Euclidean bridge form: in inner-product coordinates, the source's
set-valued map is `x ↦ Function.concaveSubdifferentialAt g x`. -/
recall concaveSubdifferentialAt

end Function

/-! ### Theorem_6_30_7 (from Chap06) -/
noncomputable section

universe u v w z

open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.7 says that for a concave bifunction `G`, the perturbation
  function `sup G` is concave and its effective domain is exactly the set of parameters whose
  slices are not identically `-∞`.
- `core/canonical`: the chapter owners already present are `concᵇ[𝕜](G)` for the
  bifunction hypothesis, `upperPerturbationFunction G` for the perturbation function, and the
  Chapter 1 concave-side effective-domain owner `dom(-f)` for a function `f`.
- `bridge/view`: the textbook phrase “`G u` is not identically `-∞`” is rendered directly by the
  slice-wise existence condition `∃ x, ⊥ < G u x`, rather than by reusing the convex-side
  bifunction-domain owner `dom G`, whose meaning is tied to the `+∞` / infimum orientation.

Domain-style sampling used here:
- `concᵇ[𝕜](G)` from `Definition_6_30_8`;
- `Bifunction.upperPerturbationFunction` from `Definition_6_30_11`;
- `Function.IsConcave` from `Definition_6_30_2`, which is the owner of the conclusion in part
  (1);
- `dom(-f)` and `mem_dom_neg_iff` from `Definition_6_30_1`, which give the canonical
  effective-domain surface for concave functions.

Primitive data vs derived API:
- primitive source data: a bifunction `G : U → X → WithBotTop α`;
- primitive owner hypothesis: `concᵇ[𝕜](G)`;
- derived owner in part (1): `(supᵇ(G)).IsConcave 𝕜`;
- derived owner in part (2): `dom(- supᵇ(G))`, with the source-facing slice
  criterion `∃ x, ⊥ < G u x`.

Layer target:
- part (1): `source-facing`, stated directly on the canonical upper-perturbation owner;
- part (2): `bridge/view`, expressing the textbook `dom(sup G) = dom G` as the canonical
  effective-domain equality for `supᵇ(G)` and the source slice criterion.
-/

section

variable {𝕜 : Type z} [Semiring 𝕜] [PartialOrder 𝕜]
variable {U : Type u} [AddCommMonoid U] [SMul 𝕜 U]
variable {X : Type v} [AddCommMonoid X] [SMul 𝕜 X]
variable {α : Type w} [AddCommGroup α] [SMul 𝕜 α]
variable [ConditionallyCompleteLattice α] [IsOrderedAddMonoid α]

/-- Theorem 6.30.7 (1): if `G` is a concave bifunction, then its perturbation function `sup G`,
rendered canonically as `supᵇ(G)`, is concave on the parameter space. -/
theorem upperPerturbationFunction_isConcave_of_isConcave
    (G : U → X → WithBotTop α) (hG : concᵇ[𝕜](G)) :
    (supᵇ(G)).IsConcave 𝕜 := by
  sorry

end

-- Proof sketch: use the Chapter 6 domain bridge `u ∈ dom(-f) ↔ ⊥ < f u` with
-- `f := supᵇ(G)`, then rewrite
-- `supᵇ(G) u = ⨆ x, G u x`. The indexed supremum is strictly above `⊥`
-- exactly when some slice value is strictly above `⊥`, which is the source condition that
-- `G u` is not identically `-∞`.
/- Theorem 6.30.7 (2): the effective domain of `sup G`, rendered canonically as
`dom(- supᵇ(G))`, is exactly the set of parameters `u` for which the slice
`G u` is not identically `-∞`, i.e. for which some `x` satisfies `⊥ < G u x`. This is the
source equality `dom(sup G) = dom G`.

This clause only uses the order and negation structure on the codomain together with the base
types `U` and `X`, so the additive/module hypotheses from part `(1)` are intentionally omitted
here. -/
section

variable {α : Type w} [ConditionallyCompleteLattice α]
variable {U : Type u} {X : Type v}

theorem bot_lt_upperPerturbationFunction_iff_exists_bot_lt
    (G : U → X → WithBotTop α) (u : U) :
    ⊥ < supᵇ(G) u ↔ ∃ x : X, ⊥ < G u x := by
  rw [upperPerturbationFunction_apply]
  exact (bot_lt_iSup : (⊥ < ⨆ x : X, G u x) ↔ ∃ x : X, ⊥ < G u x)

variable [Neg α]

theorem effectiveDomain_neg_upperPerturbationFunction_eq_setOf_exists_bot_lt
    (G : U → X → WithBotTop α) :
    dom(- supᵇ(G)) = {u : U | ∃ x : X, ⊥ < G u x} := by
  rw [dom_neg_eq_setOf_bot_lt (supᵇ(G))]
  ext u
  exact bot_lt_upperPerturbationFunction_iff_exists_bot_lt (G := G) (u := u)

end

end Bifunction

/-! ### Definition_6_30_8 (from Chap06) -/
universe u v w z

namespace Rockafellar

/-- Source-facing notation for Definition 6.30.8: a bifunction is concave exactly when its graph
function is concave. -/
scoped[Rockafellar] notation:70 "concᵇ[" 𝕜 "](" G ")" =>
  (Function.uncurry G).IsConcave 𝕜

end Rockafellar

namespace Bifunction

section

open scoped Rockafellar

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.8 introduces the phrase “concave bifunction” by requiring the
  graph function of a bifunction to be concave on the product space.
- `core/canonical`: the chapter concavity owner is already `Function.IsConcave` from
  Definition 6.30.2, and the graph function of a bifunction is canonically the uncurried map
  `Function.uncurry G`.
- `bridge/view`: no extra bifunction owner is needed; the source notion is exactly the canonical
  graph-function owner `(Function.uncurry G).IsConcave 𝕜`, with shorthand notation
  `concᵇ[𝕜](G)`.

Domain-style sampling used here:
- `Function.IsConcave` from `Definition_6_30_2`;
- the canonical product-view operators `Function.uncurry` and `Function.curry_uncurry`,
  recalled upstream in Definition 6.29.2.

Primitive data vs derived API:
- primitive data: a bifunction `G : U → X → WithTopBot α`;
- canonical owner expression: `(Function.uncurry G).IsConcave 𝕜`;
- source-facing notation surface: `concᵇ[𝕜](G)`.
- the ambient structure is the canonical componentwise product structure induced from `U` and `X`,
  so the owner assumptions are stated on the two variable spaces rather than on an arbitrary
  externally supplied structure on `U × X`.

Layer target: `source-facing` theorem surface on the canonical owner.
-/

variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommGroup α] [SMul 𝕜 α] [LE α]

recall Function.IsConcave

/-- Definition 6.30.8, source-facing owner equation:
a bifunction is concave exactly when its graph function is concave. -/
@[simp] theorem conc_iff_uncurry_isConcave
    (G : U → X → WithTopBot α) :
    concᵇ[𝕜](G) ↔ (Function.uncurry G).IsConcave 𝕜 :=
  Iff.rfl

end

end Bifunction

/-! ### Theorem_6_30_8 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w z

namespace Bifunction

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type z}
variable [Add 𝕜] [Neg 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [Zero U] [Sub U] [Neg UStar]
variable [HasPairing U UStar 𝕜] [HasPairingNegRight U UStar 𝕜]

variable (G : U → X → WithBotTop 𝕜)

local notation "h" => upperPerturbationFunction G

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.8 characterizes Kuhn--Tucker vectors for the concave program
  attached to `G` by a superdifferential condition on the upper perturbation function
  `h := upperPerturbationFunction G`.
- `core/canonical`: the owner declarations already present are
  `Bifunction.upperPerturbationFunction`, `Bifunction.IsConcaveKuhnTuckerVector`, and the
  Chapter 6 owner `_root_.concaveSubdifferentialAt`.
- `bridge/view`: the theorem is the direct source-facing bridge between the Chapter 6
  Kuhn--Tucker owner and the Chapter 6 concave-subdifferential condition at the origin; the
  pairing inequality from Definition 6.30.5 is a derived membership criterion rather than a
  second public owner.

Domain-style sampling used here:
- `Bifunction.upperPerturbationFunction` from Definition 6.30.11;
- `Bifunction.IsConcaveKuhnTuckerVector` and its finiteness/supporting-hyperplane API from
  Definition 6.30.12;
- `_root_.concaveSubdifferentialAt` and
  `_root_.mem_concaveSubdifferentialAt_pairing` from Definition 6.30.5;
- the primal-side Kuhn--Tucker/subdifferential bridge from Theorem 6.29.1.

Primitive data vs derived API:
- primitive inputs: a bifunction `G` and a dual vector `u⋆`;
- primitive owners already upstream: `h := upperPerturbationFunction G`,
  `IsConcaveKuhnTuckerVector G u⋆`, and `concaveSubdifferentialAt h 0`;
- derived bridge API in this file: the source iff-characterization of concave Kuhn--Tucker
  vectors by finiteness of `h 0` together with the origin supergradient condition, expressed on
  the canonical owner `concaveSubdifferentialAt h 0`.

Layer target: `source-facing`, expressed directly in the canonical owner language already present
in the project.
-/

-- Proof sketch: if `u⋆` is a concave Kuhn--Tucker vector, the theorem
-- `IsConcaveKuhnTuckerVector.upperPerturbationFunction_zero_finite` gives finiteness of `h 0`,
-- and the owner inequality
-- `⟪u, u⋆⟫ₚ + h u ≤ h 0`, together with `HasPairingNegRight.pairing_neg_right`, is exactly the
-- pairing membership criterion for `-u⋆ ∈ concaveSubdifferentialAt h 0`. Conversely, finiteness
-- of `h 0` and that supergradient condition give `h u ≤ h 0 - ⟪u, u⋆⟫ₚ` for all `u`, hence
-- `⟪u, u⋆⟫ₚ + h u ≤ h 0`; evaluating at `u = 0` forces the defining shifted supremum to equal
-- `h 0`, and the finiteness of `h 0` supplies the two finiteness fields of
-- `IsConcaveKuhnTuckerVector G u⋆`.
/-- Theorem 6.30.8: a dual vector `u⋆` is a Kuhn--Tucker vector for the concave program attached
to `G` exactly when the unperturbed upper perturbation value `h 0` is finite and `-u⋆` belongs to
the concave subdifferential of `h := upperPerturbationFunction G` at `0`, under the canonical
right-negation compatibility `⟪u, -u⋆⟫ₚ = -⟪u, u⋆⟫ₚ`. -/
theorem isConcaveKuhnTuckerVector_iff_zero_finite_and_neg_mem_concaveSubdifferentialAt_zero
    (uStar : UStar) :
    IsConcaveKuhnTuckerVector G uStar ↔
      h 0 ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤ ∧
        -uStar ∈ concaveSubdifferentialAt h 0 := sorry

end

end Bifunction

/-! ### Definition_6_30_9 (from Chap06) -/
noncomputable section

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.9 introduces the adjoint bifunction `F⋆` attached to a
  bifunction `F`, given by the sign-twisted conjugate formula
  `F⋆ x⋆ u⋆ = - ((Function.uncurry F)⋆ (-u⋆, x⋆))`.
- `core/canonical`: the graph function is already owned by `Function.uncurry`, conjugation is
  already owned by `convexConjugate` with notation `(·)⋆`, and the Chapter 6 owner abstraction is
  already `Bifunction.adjoint`.
- `bridge/view`: the pointwise sign-twisted formula, the source-facing notation `F⋆`, and the
  zero-slice companion API are already exposed by `Definition_6_30_14`, so no parallel local copy
  belongs here.

Domain-style sampling used here:
- `Function.uncurry` from `Definition_6_29_2`;
- `convexConjugate` and postfix notation `(·)⋆` from `Chap03.Defn_12_2`;
- `Bifunction.adjoint` from `Definition_6_30_14`;
- `Bifunction.adjoint_apply` and `Bifunction.objective_adjoint_apply` from
  `Definition_6_30_14`, confirming that the pointwise and zero-slice surfaces are already owned in
  Chapter 6.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → L`;
- primitive owner: `Bifunction.adjoint XStar UStar F`, written source-facing as `F⋆` in
  `open scoped Rockafellar`;
- derived API: the pointwise evaluation formula and zero-slice formula for this owner.

Layer target: `core/canonical recall/use`. No convexity assumption is primitive for this owner:
the source item is definition-level, so the main entry in this file should be the owner
`Bifunction.adjoint` itself rather than a parallel local formula theorem.
-/

/- Definition 6.30.9: the adjoint bifunction of `F` is the Chapter 6 owner
`Bifunction.adjoint`, used source-facing as `F⋆` in `open scoped Rockafellar`, with its
defining pointwise and zero-slice companion API already provided in `Definition_6_30_14`. -/
recall Bifunction.adjoint

/-! ### Theorem_6_30_9 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.9 identifies the adjoint bifunction of a convex bifunction with
  the negative Fenchel conjugate of its graph function, evaluated at the sign-twisted dual pair
  `(-u⋆, x⋆)`.
- `core/canonical`: the graph function is already owned by `Function.uncurry`, the conjugate is
  already owned by `convexConjugate` with notation `(·)⋆`, and the adjoint bifunction is already
  owned by `Bifunction.adjoint`.
- `bridge/view`: the theorem is exactly the immediate pointwise companion theorem
  `Bifunction.adjoint_apply` from `Definition_6_30_14`; no second wrapper theorem is
  mathematically needed here.

Domain-style sampling used here:
- `Function.uncurry` from `Definition_6_29_2`;
- `convexConjugate` and postfix notation `(·)⋆` from `Chap03.Defn_12_2`;
- `Bifunction.adjoint` and `Bifunction.adjoint_apply` from
  `Definition_6_30_14`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → L`;
- primitive owner: `Bifunction.adjoint F`;
- derived API: the pointwise evaluation formula identifying this owner with the negative conjugate
  of the graph function.

Layer target: `core/canonical recall/use`. The source convexity and Euclidean-space assumptions are
redundant for this identity itself, so the faithful Lean formalization reuses the existing
pairing-level theorem directly.
-/

/- Theorem 6.30.9: for the adjoint bifunction `F*` of a bifunction `F`, the value at `(x⋆, u⋆)`
is the negative Fenchel conjugate of the graph function `Function.uncurry F`, evaluated at
`(-u⋆, x⋆)`. This numbered item is exactly the existing pointwise owner theorem
`Bifunction.adjoint_apply`, so the faithful refinement is a direct recall. -/
recall Bifunction.adjoint_apply

/-! ### Definition_6_30_10 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.10 says that the concave program attached to a concave
  bifunction `G` maximizes the zero slice `G₀`, and that its perturbations are obtained by
  replacing `G₀` with the slices `Gᵤ`.
- `core/canonical`: the zero-slice owner is already `Bifunction.objective` from
  Definition 6.29.12, while the perturbation family is just the given bifunction `G` itself.
- `bridge/view`: no new program wrapper or maximization-objective alias should be introduced
  here; the source notion is exactly the existing zero-slice owner together with the existing
  family of slices.

Domain-style sampling used here:
- `concᵇ[𝕜](G)` from `Definition_6_30_8`;
- `Bifunction.objective`;
- `Bifunction.objective_apply`;
- the generic bifunction-slice surface `G u`.

Primitive data vs derived API:
- primitive source data: a concave bifunction `G : U → X → WithBotTop α` with owner
  `concᵇ[𝕜](G)`;
- canonical owner for the unperturbed objective: `objective G`;
- perturbations: the existing functions `G u`.

Layer target: `core/canonical recall/use`.
-/

namespace Bifunction

open scoped Rockafellar

/- Definition 6.30.10: the source hypothesis is that `G` is a concave bifunction, expressed on the
canonical Chapter 6 owner surface `concᵇ[𝕜](G)` from `Definition_6_30_8`. -/
recall Function.IsConcave

/- Definition 6.30.10: the associated concave program uses the existing zero-slice owner `(G)₀`
as its unperturbed objective, while perturbation objectives stay at the primitive slice surface
`G u` with no extra wrapper owner. -/
recall objective
recall objective_eq
recall objective_apply

end Bifunction

/-! ### Theorem_6_30_10 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.10 says that the adjoint bifunction `F⋆` of a convex bifunction
  has a closed concave graph function `g(x⋆, u⋆) = (F⋆ x⋆) u⋆`, now recalled on the
  codomain-generic pairing layer.
- `core/canonical`: the graph function is already owned by `Function.uncurry`, the adjoint
  bifunction is already owned by `Bifunction.adjoint`, and the chapter already exposes the
  canonical closed-concavity theorem `Bifunction.adjointFunction_isClosedConcave`.
- `bridge/view`: the source’s explicit graph function `g(x⋆, u⋆) = (F⋆ x⋆) u⋆` is exactly
  `Function.uncurry (F⋆ : XStar → UStar → WithBotTop 𝕜)`, so no second graph-function owner
  belongs in
  this file.

Domain-style sampling used here:
- `Bifunction.adjoint` from `Definition_6_30_14`;
- `Function.uncurry` as the graph-function owner;
- `Bifunction.adjointFunction_isClosedConcave` from `Theorem_6_30_11`;
- `LowerSemicontinuous` as the closedness surface.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owner: `F⋆`;
- derived API: the graph-function view
  `Function.uncurry (F⋆ : XStar → UStar → WithBotTop 𝕜)` and its
  closed-concavity theorem, with chapter-facing `EReal`/`ℝ` use recovered by specialization.

Layer target: `core/canonical recall/use`.
-/

/- Theorem 6.30.10 is exactly the canonical graph-function closed-concavity theorem already owned
by `Bifunction.adjointFunction_isClosedConcave`; the source’s named graph function
`g(x⋆, u⋆) = (F⋆ x⋆) u⋆` is just `Function.uncurry (F⋆ : XStar → UStar → WithBotTop 𝕜)`. -/
recall Bifunction.adjointFunction_isClosedConcave

/-! ### Definition_6_30_11 (from Chap06) -/
noncomputable section

open Function
open scoped Rockafellar

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.11 introduces the perturbation function of the concave
  program associated with a bifunction `G`, namely the slice-wise supremum `u ↦ sup_x G(u, x)`.
- `core/canonical`: the neighboring Chapter 6 owner pattern is the infimum-side
  `Bifunction.perturbationFunction` from Definition 6.29.1, which itself is the curried
  specialization of the Chapter 1 owner `Function.partialInfimum`. The supremum-side dual should
  therefore reuse the matching Chapter 1 owner `Function.partialSupremum`.
- `bridge/view`: the source formulas are exactly the range-supremum expression
  `sSup (Set.range (G u))` and its indexed form `⨆ x, G u x`; no wrapper around the same
  bifunction data is needed.

Domain-style sampling used here:
- `Function.partialSupremum` from `Chap01.Text_5_7_2` as the intrinsic owner for slice-wise
  supremum on product functions;
- `Bifunction.perturbationFunction` from Definition 6.29.1 as the infimum-side owner pattern;
- `Bifunction.objective` from Definition 6.29.12 as the zero-slice owner pattern;
- `Bifunction.maximinValueOn` / `Bifunction.minimaxValueOn` from Definition 36.0.1 as the
  chapter's canonical complete-lattice supremum/infimum surface for bifunction aggregates.

Primitive data vs derived API:
- primitive source data: a bifunction `G : U → X → α`;
- source-facing owner introduced here: `upperPerturbationFunction G`;
- core owner reused upstream: `partialSupremum (Function.uncurry G)`;
- derived API: the pointwise formulas `sSup (Set.range (G u))` and `⨆ x, G u x`.

Ambient minimization:
- the slice-supremum construction itself only uses the supremum-of-sets structure on
  the codomain, so the owner lives over general `α`;
- the Chapter 6 extended-value specialization `WithBotTop α` is recovered by instantiation in
  later duality statements.

Redundant-source-assumption elimination:
- although the source phrases the item for a concave bifunction, the slice-supremum construction
  depends only on the values of `G`; concavity belongs to later theorems, not to this definition.

Layer target: `source-facing`, dual to the infimum-side owner
`Bifunction.perturbationFunction`.
-/

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [SupSet α]

/-- Definition 6.30.11: the perturbation function of the concave program associated with a
bifunction `G` is the pointwise supremum of its slices, i.e. the source object `sup G`. -/
abbrev upperPerturbationFunction (G : U → X → α) : U → α :=
  partialSupremum (Function.uncurry G)

/-- Rockafellar's source-facing notation for the upper perturbation function `sup G`. -/
scoped[Rockafellar] notation "supᵇ(" G ")" => Bifunction.upperPerturbationFunction G

-- Proof sketch: unfold `upperPerturbationFunction`; the right-hand side is exactly the defining
-- slice supremum.
/-- Evaluating `upperPerturbationFunction G` at `u` gives the supremum of the slice `G u` over the
`X`-variable, written as the supremum of its range. -/
@[simp] theorem upperPerturbationFunction_apply_eq_sSup_range
    (G : U → X → α) (u : U) :
    supᵇ(G) u = sSup (Set.range (G u)) := by
  simp [upperPerturbationFunction]

-- Proof sketch: start from `upperPerturbationFunction_apply_eq_sSup_range` and rewrite the range
-- supremum as the indexed supremum with `sSup_range`.
/-- Evaluating `upperPerturbationFunction G` at `u` is the indexed supremum `sup_x G(u, x)`. -/
@[simp] theorem upperPerturbationFunction_apply
    (G : U → X → α) (u : U) :
    supᵇ(G) u = ⨆ x, G u x := by
  rw [upperPerturbationFunction_apply_eq_sSup_range, ← sSup_range]

end

section

variable [Zero U] [SupSet α]

/-- The unperturbed upper perturbation value is the supremum of the objective range. -/
@[simp] theorem upperPerturbationFunction_zero_eq_sSup_range_objective
    (G : U → X → α) :
    supᵇ(G) 0 = sSup (Set.range ((G)₀)) := by
  change supᵇ(G) 0 = sSup (Set.range (G 0))
  rw [upperPerturbationFunction_apply_eq_sSup_range G 0]

/-- The unperturbed upper perturbation value is the indexed supremum of the objective. -/
@[simp] theorem upperPerturbationFunction_zero_eq_iSup_objective
    (G : U → X → α) :
    supᵇ(G) 0 = ⨆ x, (G)₀ x := by
  change supᵇ(G) 0 = ⨆ x, G 0 x
  rw [upperPerturbationFunction_apply G 0]

end

end Bifunction

/-! ### Theorem_6_30_11 (from Chap06) -/
noncomputable section

universe u v u' v'

open Function
open scoped Rockafellar

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.11 studies the adjoint bifunction `F⋆` and its biconjugate `F⋆⋆`,
  together with the closure/properness consequences of Fenchel duality for bifunctions.
- `core/canonical`: the relevant upstream owners are the Chapter 6 adjoint owner `adjoint`
  with notation `F⋆`, the Chapter 6 concave-bifunction notation `concᵇ[𝕜](F)`, the
  bifunction closure owner `cl F`, the Chapter 12 owners `f.IsClosedProperConvex` and
  `g.IsClosedProperConcave`, and the Chapter 19 owner `f.HasPolyhedralEpigraph`.
- `bridge/view`: this file should therefore stay on the bifunction surface, but phrase its public
  API through those owners and the graph-function bridge `uncurry F`, rather than through parallel
  local wrapper names.

Domain-style sampling used here:
- `Bifunction.adjoint` and the scoped notation `F⋆` from `Definition_6_30_14`;
- the scoped biconjugate notation `F⋆⋆` from `Definition_6_30_14`, with type ascriptions where
  needed for disambiguation;
- `concᵇ[𝕜](F)` from `Definition_6_30_8`;
- `Bifunction.closure` from `Definition_6_29_24`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `Function.IsClosedProperConcave` from `Definition_6_30_2`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`,
  `Function.IsClosedProperConvex.biconjugate_eq`, and
  `Function.HasPolyhedralEpigraph.convexConjugate` from the Chapter 12 and Chapter 19 closure.

Primitive data vs derived API:
- primitive data for the closed-concavity owner theorem:
  a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive source-facing owners reused directly: `F⋆`, `F⋆⋆`, and `cl F`;
- derived API in this file: closed-concavity, properness equivalence, closed-proper-concavity,
  biconjugacy, and the resulting bijection/polyhedrality statements.

Layer target: `bridge/view`, stated directly on the canonical chapter owners.
-/

section ClosedConcave

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [TopologicalSpace U] [TopologicalSpace X]
variable [TopologicalSpace UStar] [TopologicalSpace XStar]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasLinearPairing X XStar 𝕜]
variable [HasContinuousPairing U UStar 𝕜] [HasContinuousPairing X XStar 𝕜]

-- Proof sketch: identify `Function.uncurry (F⋆)` with the sign-twisted conjugate
-- of `Function.uncurry F`, then apply the Chapter 12 theorem that conjugates of convex functions
-- are closed and convex after negation.
/-- The adjoint of a convex bifunction is closed of the opposite type, rendered on the graph
function as bifunction concavity together with lower semicontinuity of the negated adjoint
graph. -/
theorem adjointFunction_isClosedConcave
    (F : U → X → WithBotTop 𝕜) (hF_convex : (uncurry F).IsConvex 𝕜) :
    concᵇ[𝕜]((F⋆ : XStar → UStar → WithBotTop 𝕜)) ∧
      LowerSemicontinuous (-uncurry (F⋆ : XStar → UStar → WithBotTop 𝕜)) := sorry

end ClosedConcave

section ClosedProperAndBiconjugacy

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [IsTopologicalAddGroup UStar] [ContinuousSMul 𝕜 UStar]
variable [FiniteDimensional 𝕜 UStar] [T2Space UStar]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousSMul 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar] [T2Space XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

local instance : HasPairing XStar X 𝕜 :=
  HasPairing.swap (X := X) (Y := XStar) (L := 𝕜)

local instance : HasPairing UStar U 𝕜 :=
  HasPairing.swap (X := U) (Y := UStar) (L := 𝕜)

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "IsClosedProperConcave[" 𝕜 "]" => Function.IsClosedProperConcave (𝕜 := 𝕜)
local postfix:max "⋆⋆" =>
  fun F : U → X → WithBotTop 𝕜 ↦
    (Bifunction.adjoint (F⋆ : XStar → UStar → WithBotTop 𝕜) : U → X → WithBotTop 𝕜)

-- Proof sketch: the graph function of `adjoint F` is obtained from the Fenchel conjugate
-- of `uncurry F` by the sign-twisted swap map, so Chapter 12 properness preservation for
-- convex conjugates gives the equivalence.
/-- The adjoint bifunction is proper on the opposite, concave side exactly when the original
convex bifunction is proper on the graph-function side. -/
theorem adjointFunction_isProper_iff
    (F : U → X → WithBotTop 𝕜) (hF_convex : (uncurry F).IsConvex 𝕜) :
    (-uncurry (F⋆ : XStar → UStar → WithBotTop 𝕜)).IsProper ↔ (uncurry F).IsProper := sorry

-- Proof sketch: combine `adjointFunction_isClosedConcave` with
-- `adjointFunction_isProper_iff`, then package the three fields of
-- `Function.IsClosedProperConvex` for the negated graph function of `F⋆`.
/-- If the graph function of `F` is closed proper convex, then the graph function of its adjoint
is closed proper concave. -/
theorem adjointFunction_isClosedProperConcave
    (F : U → X → WithBotTop 𝕜)
    (hF : IsClosedProperConvex[𝕜] (uncurry F)) :
    IsClosedProperConcave[𝕜]
      (uncurry (show XStar → UStar → WithBotTop 𝕜 from F⋆)) := sorry

-- Proof sketch: pass from the bifunction `F` to its graph function `uncurry F`, apply
-- the Chapter 12 biconjugacy theorem `f⋆⋆ = cl(f)` for convex functions on the product space, and
-- identify the resulting graph closure with the source-facing bifunction owner `cl F`.
/-- Theorem 6.30.11: for a convex bifunction `F`, the paired-space biconjugate owner
`F⋆⋆` recovers the canonical bifunction closure `cl F`, i.e. the bifunction form of the source
identity `F⋆⋆ = cl F`. -/
theorem biadjointFunction_eq_closure
    (F : U → X → WithBotTop 𝕜) (hF_convex : (uncurry F).IsConvex 𝕜) :
    (F⋆⋆ : U → X → WithBotTop 𝕜) = cl F := sorry

-- Proof sketch: combine `biadjointFunction_eq_closure` with the assumed fixed-point
-- identity for the canonical closure owner.
/-- If a convex bifunction already equals its closure, then the paired-space bifunction biconjugate
`F⋆⋆` reduces back to `F`; this is the source involutivity statement `F⋆⋆ = F`. -/
theorem biadjointFunction_eq_self_of_closure_eq_self
    (F : U → X → WithBotTop 𝕜) (hF_convex : (uncurry F).IsConvex 𝕜)
    (hF_closed : cl F = F) :
    (F⋆⋆ : U → X → WithBotTop 𝕜) = F := sorry

-- Proof sketch: `adjointFunction_isClosedProperConcave` gives the forward maps-to statement, and
-- `biadjointFunction_eq_closure` together with the fixed-point identity for closed
-- proper convex bifunctions gives the inverse-on-class relation, hence a bijection.
/-- Fenchel adjunction gives a one-to-one correspondence between closed proper convex bifunctions
and closed proper concave bifunctions, with the source and target spaces exchanged. -/
theorem adjointFunction_bijOn_closedProperConvex_bifunctions :
    Set.BijOn
      (fun F : U → X → WithBotTop 𝕜 ↦
        (((F : U → X → WithBotTop 𝕜)⋆) : XStar → UStar → WithBotTop 𝕜))
      {F : U → X → WithBotTop 𝕜 |
        IsClosedProperConvex[𝕜] (uncurry F)}
      {G : XStar → UStar → WithBotTop 𝕜 | IsClosedProperConcave[𝕜] (uncurry G)} := sorry

end ClosedProperAndBiconjugacy

section PolyhedralAdjoint

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [IsTopologicalAddGroup UStar] [ContinuousSMul 𝕜 UStar]
variable [FiniteDimensional 𝕜 UStar] [T2Space UStar]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousSMul 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar] [T2Space XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

-- Proof sketch: identify the negated adjoint graph with the Fenchel conjugate of `uncurry F`
-- on the explicit dual product `UStar × XStar`, then apply the Chapter 19 conjugate-polyhedral
-- owner theorem and the linear sign/swap change of variables on the product space.
/-- If the graph function of a convex bifunction has polyhedral epigraph, then the negated graph
function of its adjoint bifunction also has polyhedral epigraph. The owner is stated on explicit
dual spaces `XStar` and `UStar`, using the chapter's source-facing notation `F⋆`. -/
theorem adjointFunction_hasPolyhedralEpigraph
    (F : U → X → WithBotTop 𝕜)
    (hF_poly : (uncurry F).HasPolyhedralEpigraph) :
    (-uncurry (F⋆ : XStar → UStar → WithBotTop 𝕜)).HasPolyhedralEpigraph := sorry

end PolyhedralAdjoint

end Bifunction
