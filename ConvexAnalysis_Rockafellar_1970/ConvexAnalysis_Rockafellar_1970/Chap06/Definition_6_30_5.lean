import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

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
