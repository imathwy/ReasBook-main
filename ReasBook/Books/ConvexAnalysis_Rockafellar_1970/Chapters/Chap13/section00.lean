import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_13_0_1 (from Chap03) -/
universe u v w

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 13.0.1 introduces the support function `δ*(· | C)` by its supremum formula.
- `core/canonical`: the project owner abstraction is the function `supportFunction` attached
  directly to a subset `C`.
- `bridge/view`: the textbook formula is the existing specification theorem `supportFunction_def`.
- Primitive data vs derived API: the support function itself is the core notion; the displayed
  supremum identity is its defining specification. The source's convexity hypothesis is redundant
  for the bare definition, since the same formula makes sense for any subset.

Domain-style sampling used here:
- the existing project owner `supportFunction`;
- its specification theorem `supportFunction_def`;
- the function-valued bridge `supportFunction_eq_iSup`;
- and the pointwise bridge companion `supportFunction_eq_iSup_apply`.
-/

/-!
Canonicalization checklist for this item:

- Codomain layer: keep the declaration at arbitrary `L` with only `[SupSet L]`; no `EReal`,
  `WithBotTop α`, or concrete linear order is required for the defining supremum identity.
- Scalar/ambient structure: no scalar field or module data is part of the primitive statement.
- Model owner: keep the pairing-level owner `[HasPairing X Y L]`; no inner-product/strong-dual
  specialization belongs in the source item.
- Topology: no closure/interior/relative-topology owner is present in Text 13.0.1, so no ambient
  topological assumptions should appear here.
- Theorem surface: use textbook support-function notation `δᵛ` as the primary public statement,
  with `supportFunction` remaining the canonical underlying owner; use `δᵛ[L](x | C)` when the
  codomain must be fixed explicitly.
-/

/- Text 13.0.1: the support function `δ*(· | C)` is the canonical project function
`supportFunction`, defined on any set `C` by taking the supremum of the pairings `⟪x, x⋆⟫` over
`x ∈ C`. -/
recall supportFunction {X : Type u} {Y : Type v} {L : Type w}
    [SupSet L] [HasPairing X Y L] (C : Set Y) : X → L

/- The textbook supremum formula for the support function is the existing project specification
theorem `supportFunction_def`. -/
recall supportFunction_def {X : Type u} {Y : Type v} {L : Type w}
    [SupSet L] [HasPairing X Y L] (C : Set Y) (x : X) :
    δᵛ(x | C) = (⨆ y : C, (⟪x, (y : Y)⟫ₚ : L))

/- Function-valued bridge form used for rewriting under function operators. -/
recall supportFunction_eq_iSup {X : Type u} {Y : Type v} {L : Type w}
    [SupSet L] [HasPairing X Y L] (C : Set Y) :
    (δᵛ(· | C) : X → L) = (⨆ y : C, (⟪·, (y : Y)⟫ₚ : X → L))

/- Pointwise companion of `supportFunction_eq_iSup` for direct pointwise rewrites. -/
recall supportFunction_eq_iSup_apply {X : Type u} {Y : Type v} {L : Type w}
    [SupSet L] [HasPairing X Y L] (C : Set Y) (x : X) :
    δᵛ(x | C) = (⨆ y : C, (⟪x, (y : Y)⟫ₚ : L))

/- Set-image bridge form of Text 13.0.1 at the primitive `SupSet` owner layer. -/
recall supportFunction_eq_sSup_image {X : Type u} {Y : Type v} {L : Type w}
    [SupSet L] [HasPairing X Y L] (C : Set Y) (x : X) :
    δᵛ(x | C) = sSup ((fun y : Y ↦ (⟪x, y⟫ₚ : L)) '' C)

/-! ### Text_13_0_2 (from Chap03) -/
noncomputable section

open scoped Pointwise Rockafellar

section Pairing

variable {X : Type*} [Neg X]
variable {Y : Type*}
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLattice α]
variable [IsOrderedAddMonoid α] [HasPairing X Y α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.0.2 rewrites an infimum pairing formula as the negative of a support
  function at `-x⋆`.
- `core/canonical`: the owner abstraction is the chapter support function `supportFunction C`,
  together with the order-reversing isomorphism `WithTopBot` negation duality.
- `bridge/view`: the source infimum formula is obtained from
  `supportFunction_eq_sSup_image` by order
  duality plus the primitive neg-left rule of the pairing.
- Primitive data vs derived API: the only primitive bridge data are a set `C`, a point `xStar`,
  and the pairing neg-left identity; the displayed infimum identity is derived API.

Domain-style sampling used here:
- `supportFunction`;
- `supportFunction_eq_sSup_image`;
- `WithTopBot.negOrderIso`, the canonical `WithTopBot` negation order isomorphism;
- `OrderIso.map_sSup_eq_sSup_symm_preimage`, the lattice bridge used to transport the support
  function's supremum formula across that order duality.

Layer target: `bridge/view`, stated directly as the support-function infimum companion while
reusing the canonical support-function owner.

Ambient assumptions in theorem headers:
- `[ConditionallyCompleteLattice α]` is used only to supply `sSup`/`sInf` on `WithTopBot α`;
- `[AddCommGroup α] [IsOrderedAddMonoid α]` are exactly the assumptions required by the canonical
  order-duality bridge `WithTopBot.negOrderIso`.
- No ad-hoc local `Neg`/`InvolutiveNeg` scaffolding is introduced: this item relies on the
  canonical `WithTopBot` instances from `Chap01.EOrder.Operations`.
-/

-- Proof sketch: rewrite `supportFunction C (-xStar)` by `supportFunction_eq_sSup_image`, transport
-- the resulting supremum through `WithTopBot.negOrderIso`, and rewrite the negated image
-- set using the pairing neg-left identity.
/-- Text 13.0.2 at the pairing layer: under the canonical left-negation pairing owner,
`-δᵛ(-xStar | C)` is the infimum of the pairing values with `xStar` on `C`. -/
theorem neg_supportFunction_neg_eq_sInf_image_pairing
    [HasPairingNegLeft X Y α]
    (C : Set Y) (xStar : X) :
    (-(δᵛ(-xStar | C) : WithTopBot α)) = sInf ((fun y ↦ ⟪xStar, y⟫ₚ) '' C) := by
  rw [supportFunction_eq_sSup_image (C := C) (x := -xStar)]
  let A : Set (WithTopBot α) := ((fun y ↦ ⟪-xStar, y⟫ₚ) '' C)
  have hnegneg : ∀ t : WithTopBot α, -(-t) = t := by
    intro t
    cases t using WithBotTop.rec with
    | bot => rfl
    | top => rfl
    | coe a =>
        change (((-(-a) : α) : α) : WithTopBot α) = (a : WithTopBot α)
        rw [neg_neg]
  have hneg : -sSup A = sInf (-A) := by
    have h0 :
        -sSup A =
          ((WithTopBot.negOrderIso (α := α)) (sSup A) : OrderDual (WithTopBot α)) := by
      simpa using (WithTopBot.negOrderIso_apply (α := α) (x := sSup A)).symm
    have h1 :
        ((WithTopBot.negOrderIso (α := α)) (sSup A) : OrderDual (WithTopBot α)) =
          sSup (((WithTopBot.negOrderIso (α := α)).symm ⁻¹' A) :
            Set (OrderDual (WithTopBot α))) :=
      OrderIso.map_sSup_eq_sSup_symm_preimage (WithTopBot.negOrderIso (α := α)) A
    have h2 :
        sSup (((WithTopBot.negOrderIso (α := α)).symm ⁻¹' A) :
          Set (OrderDual (WithTopBot α))) =
            sInf (((WithTopBot.negOrderIso (α := α)).symm ⁻¹' A) :
              Set (WithTopBot α)) := rfl
    have h3 :
        sInf (((WithTopBot.negOrderIso (α := α)).symm ⁻¹' A) :
          Set (WithTopBot α)) = sInf (-A) := by
      congr 1
      ext z
      simp [Set.mem_preimage]
    exact h0.trans (h1.trans (h2.trans h3))
  have hA : -A = ((fun y ↦ -⟪-xStar, y⟫ₚ) '' C : Set (WithTopBot α)) := by
    dsimp [A]
    ext z
    constructor
    · intro hz
      rcases Set.mem_neg.mp hz with ⟨y, hy, hyz⟩
      refine ⟨y, hy, ?_⟩
      calc
        -⟪-xStar, y⟫ₚ = -(-z : WithTopBot α) := by simp [hyz]
        _ = z := hnegneg z
    · rintro ⟨y, hy, hyz⟩
      refine Set.mem_neg.mpr ?_
      refine ⟨y, hy, ?_⟩
      calc
        (⟪-xStar, y⟫ₚ : WithTopBot α) = -(-⟪-xStar, y⟫ₚ : WithTopBot α) :=
          (hnegneg (⟪-xStar, y⟫ₚ : WithTopBot α)).symm
        _ = -z := by simp [hyz]
  have himage' :
      ((fun y ↦ -⟪-xStar, y⟫ₚ) '' C : Set (WithTopBot α)) =
        ((fun y ↦ ⟪xStar, y⟫ₚ) '' C : Set (WithTopBot α)) := by
    refine Set.image_congr ?_
    intro y hy
    have hα : (-(⟪-xStar, y⟫ₚ : α)) = (⟪xStar, y⟫ₚ : α) := by
      simpa using congrArg (fun t : α ↦ -t) (HasPairingNegLeft.pairing_neg_left xStar y)
    simpa [WithTopBot.coe_neg] using congrArg (fun t : α ↦ (t : WithTopBot α)) hα
  calc
    -sSup A = sInf (-A) := hneg
    _ = sInf (((fun y ↦ -⟪-xStar, y⟫ₚ) '' C) : Set (WithTopBot α)) := by rw [hA]
    _ = sInf (((fun y ↦ ⟪xStar, y⟫ₚ) '' C) : Set (WithTopBot α)) := by rw [himage']

/-- Pairing-level support-function infimum bridge in swapped orientation: if the pairing is
swap-compatible and the swapped orientation is right-neg compatible, then
`-δᵛ(-xStar | C)` is the infimum of the pairing values `⟪y, xStar⟫ₚ` on `C`. -/
theorem neg_supportFunction_neg_eq_sInf_image_pairing_swap
    [HasPairing Y X α] [HasPairingSwap X Y α] [HasPairingNegRight Y X α]
    (C : Set Y) (xStar : X) :
    (-(δᵛ(-xStar | C) : WithTopBot α)) = sInf ((fun y ↦ ⟪y, xStar⟫ₚ) '' C) := by
  have hpair :
      (-(δᵛ(-xStar | C) : WithTopBot α)) = sInf ((fun y ↦ ⟪xStar, y⟫ₚ) '' C) :=
    neg_supportFunction_neg_eq_sInf_image_pairing C xStar
  have himage_swap :
      ((fun y ↦ ⟪xStar, y⟫ₚ) '' C : Set (WithTopBot α)) =
        ((fun y ↦ ⟪y, xStar⟫ₚ) '' C : Set (WithTopBot α)) := by
    refine Set.image_congr ?_
    intro y hy
    simpa using congrArg (fun t : α ↦ (t : WithTopBot α))
      (HasPairingSwap.pairing_swap xStar y)
  simpa [himage_swap] using hpair

end Pairing

end

/-! ### Text_13_0_3 (from Chap03) -/
noncomputable section

open scoped Rockafellar

variable {X : Type*} {Y : Type*} {α : Type*}
variable [ConditionallyCompleteLattice α]
variable [HasPairing X Y α]

-- Canonical swapped pairing view used by support-function owners on the dual side.
local instance instHasPairingYX : HasPairing Y X α :=
  HasPairing.swap (X := X) (Y := Y) (L := α)

/-
Source/core/bridge triage:
- `source-facing`: Text 13.0.3 characterizes when a set is contained in a closed half-space
  defined by one evaluation functional.
- `core/canonical`: the owner abstractions are the chapter half-space
  `closedHalfSpaceLE xStar β`
  and the project support function `supportFunction C xStar`.
- `bridge/view`: the textbook inequality `β ≥ δ*(xStar | C)` is rendered through
  `δᵛ[WithTopBot α](xStar | C) ≤ β`, while the set inclusion side remains the chapter half-space
  owner.
- Primitive data vs derived API: this item is a direct theorem about existing owners. Convexity is
  not part of the primitive data for this equivalence.
- Domain-style sampling used here: `supportFunction`, `supportFunction_def`, `closedHalfSpaceLE`,
  and `mem_closedHalfSpaceLE_iff`.
- Layer target: `bridge/view`, at the pairing layer with support-function values in the chapter's
  extended codomain `WithTopBot α`.
-/

-- Proof sketch: unfold `supportFunction C xStar` as the supremum of the values `⟪xStar, x⟫` for
-- `x ∈ C`. Under the canonical swapped pairing instance this is exactly `⟪x, xStar⟫`, so each
-- pointwise half-space bound compares directly with the support supremum.
/-- Text 13.0.3 at the canonical extended-codomain layer: containment in the closed half-space cut
out at level `β : WithTopBot α` is equivalent
to the support-function bound `δᵛ(xStar | C) ≤ β`. -/
theorem subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le
    (C : Set X) (xStar : Y) (β : WithTopBot α) :
    C ⊆ closedHalfSpaceLE xStar β ↔ δᵛ(xStar | C) ≤ β := by
  rw [supportFunction_def]
  constructor
  · intro h
    refine iSup_le fun x : C ↦ ?_
    change (⟪(x : X), xStar⟫ₚ : WithTopBot α) ≤ β
    exact (mem_closedHalfSpaceLE_iff (X := X)).mp (h x.2)
  · intro h y hyC
    rw [mem_closedHalfSpaceLE_iff (X := X)]
    change (⟪xStar, y⟫ₚ : WithTopBot α) ≤ β
    exact (le_iSup (fun z : C ↦ (⟪xStar, (z : X)⟫ₚ : WithTopBot α)) ⟨y, hyC⟩).trans h

/-- Text 13.0.3, canonical threshold specialization in `WithTopBot α`: for `β : α`, a set `C` is
contained in `{x | ⟪x, xStar⟫ₚ ≤ β}` iff `δᵛ(xStar | C) ≤ (β : WithTopBot α)`. -/
theorem subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot
    (C : Set X) (xStar : Y) (β : α) :
    C ⊆ closedHalfSpaceLE xStar β ↔ δᵛ(xStar | C) ≤ (β : WithTopBot α) := by
  constructor
  · intro h
    exact
      (subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le
        C xStar (β : WithTopBot α)).1 <|
        by
          intro x hx
          have hx' : (⟪x, xStar⟫ₚ : α) ≤ β :=
            (mem_closedHalfSpaceLE_iff (X := X)).mp (h hx)
          change ((⟪x, xStar⟫ₚ : WithTopBot α) ≤ (β : WithTopBot α))
          exact
            (WithTop.coe_le_coe).2 <|
              (WithBot.coe_le_coe).2 hx'
  · intro h
    have hWithTop :
        C ⊆ closedHalfSpaceLE xStar (β : WithTopBot α) :=
      (subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le
        C xStar (β : WithTopBot α)).2 h
    intro x hx
    have hxWithTop : (⟪x, xStar⟫ₚ : WithTopBot α) ≤ (β : WithTopBot α) :=
      (mem_closedHalfSpaceLE_iff (X := X)).mp (hWithTop hx)
    have hxWithBot : ((⟪x, xStar⟫ₚ : α) : WithBot α) ≤ (β : WithBot α) :=
      (WithTop.coe_le_coe).1 hxWithTop
    have hx' : (⟪x, xStar⟫ₚ : α) ≤ β :=
      (WithBot.coe_le_coe).1 hxWithBot
    exact (mem_closedHalfSpaceLE_iff (X := X)).2 hx'

/-- Text 13.0.3, source-facing threshold specialization at the canonical owner layer: for
`β : α`, a set `C` is contained in the closed half-space `{x | ⟪x, xStar⟫ₚ ≤ β}` if and only if
`δᵛ(xStar | C) ≤ β`, equivalently `β ≥ δ*(xStar | C)` in source notation. -/
theorem subset_closedHalfSpaceLE_iff_supportFunction_le
    (C : Set X) (xStar : Y) (β : α) :
    C ⊆ closedHalfSpaceLE xStar β ↔ δᵛ(xStar | C) ≤ (β : WithTopBot α) := by
  simpa using
    (subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot C xStar β)

end

/-! ### Text_13_0_4 (from Chap03) -/
noncomputable section

open scoped Rockafellar

universe u v w

variable {R : Type w} [ConditionallyCompleteLattice R]
variable {X : Type u} {Y : Type v}
variable [HasPairing X Y R]

local instance instHasPairingYX : HasPairing Y X R :=
  HasPairing.swap (X := X) (Y := Y) (L := R)

local instance instHasPairingYXWithTopBot : HasPairing Y X (WithTopBot R) :=
  (show HasPairing Y X (WithBotTop R) from inferInstance)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.0.4 names the barrier cone of `C` and identifies it with the effective
  domain of the support function `δᵛ(· | C)`.
- `core/canonical`: the owner abstractions are the existing declarations `barr[R](C)` on the
  primal/dual pairing layer and the effective-domain owner
  `dom((δᵛ(· | C) : Y → WithTopBot R))`.
- `bridge/view`: finiteness of the codomain-lifted support value
  `(δᵛ(xStar | C) : WithTopBot R)` is the companion pointwise form of membership in
  `dom((δᵛ(· | C) : Y → WithTopBot R))`.

Domain-style sampling used here:
- the existing project owner `barrierCone`;
- the set-level membership theorem `mem_barrier_iff`;
- the support-function owner `supportFunction`;
- the specification theorem `supportFunction_def`;
- the effective-domain bridge `mem_effectiveDomain`.

Primitive data vs derived API:
- primitive objects: the subset `(barr[R](C) : Set Y)` and the effective-domain owner
  `dom((δᵛ(· | C) : Y → WithTopBot R))`;
- derived bridge: the pointwise finiteness criterion
  `(δᵛ(xStar | C) : WithTopBot R) < ⊤`.

This file uses one primitive pairing orientation `HasPairing X Y R`; the reverse orientation
needed by `supportFunction` is the canonical swapped view `HasPairing.swap`.

The source's convexity and nonemptiness hypotheses are redundant for this definition-level item:
both sides of the displayed equality make sense for an arbitrary subset of a primal space paired
with a dual space.
-/

/- Text 13.0.4: the barrier cone of a subset `C` is the canonical project declaration
`barr[R](C)`, and it is exactly the effective domain
`dom((δᵛ(· | C) : Y → WithTopBot R))`. -/
recall barrierCone

/-- A functional belongs to the barrier cone exactly when it belongs to the effective domain of
the support function. -/
theorem mem_barrierCone_iff_mem_effectiveDomain_supportFunction
    {C : Set X} {xStar : Y} :
    xStar ∈ barr[R](C) ↔ xStar ∈ dom((δᵛ(· | C) : Y → WithTopBot R)) := by
  rw [mem_effectiveDomain]
  rw [mem_barrier_iff_exists_bound, supportFunction_def]
  constructor
  · rintro ⟨β, hβ⟩
    have hβ_top : ((β : WithTopBot R) : WithTopBot R) < (⊤ : WithTopBot R) := by
      change (((β : WithBot R) : WithTop (WithBot R)) < (⊤ : WithTop (WithBot R)))
      exact WithTop.coe_lt_top (β : WithBot R)
    refine lt_of_le_of_lt (iSup_le ?_) hβ_top
    intro y
    have hyβ : (⟪xStar, y.1⟫ₚ : R) ≤ β := hβ y.1 y.2
    change (((⟪xStar, y.1⟫ₚ : R) : WithTopBot R) ≤ (β : WithTopBot R))
    exact (WithTop.coe_le_coe).2 ((WithBot.coe_le_coe).2 hyβ)
  · intro hfinite
    by_cases hC_nonempty : C.Nonempty
    · rcases hC_nonempty with ⟨x0, hx0⟩
      let s : WithTopBot R := (⨆ y : C, ((⟪xStar, y.1⟫ₚ : R) : WithTopBot R))
      have hs_finite : s < (⊤ : WithTopBot R) := by
        change (⨆ y : C, ((⟪xStar, y.1⟫ₚ : R) : WithTopBot R)) < (⊤ : WithTopBot R)
        exact hfinite
      have hbot_lt :
          (⊥ : WithTopBot R) < s := by
        have hbot_lt_x0 :
            (⊥ : WithTopBot R) < ((⟪xStar, x0⟫ₚ : R) : WithTopBot R) := by
          change ((⊥ : WithTop (WithBot R)) <
              (((⟪xStar, x0⟫ₚ : R) : WithBot R) : WithTop (WithBot R)))
          exact (WithTop.coe_lt_coe).2 (WithBot.bot_lt_coe (⟪xStar, x0⟫ₚ : R))
        exact
          lt_of_lt_of_le hbot_lt_x0
            (by
              change
                ((⟪xStar, x0⟫ₚ : R) : WithTopBot R) ≤
                  (⨆ y : C, ((⟪xStar, y.1⟫ₚ : R) : WithTopBot R))
              exact
                le_iSup (f := fun y : C ↦ ((⟪xStar, y.1⟫ₚ : R) : WithTopBot R)) ⟨x0, hx0⟩)
      have hs_ne_top : s ≠ (⊤ : WithTopBot R) := ne_of_lt hs_finite
      rcases
          (CanLift.prf (x := s) hs_ne_top :
            ∃ s' : WithBot R, ((s' : WithTopBot R) = s)) with
        ⟨s', hs'⟩
      have hs'_ne_bot : s' ≠ (⊥ : WithBot R) := by
        intro hs'_bot
        apply (bot_lt_iff_ne_bot.mp hbot_lt)
        calc
          s = (s' : WithTopBot R) := hs'.symm
          _ = (⊥ : WithTopBot R) := by simp [hs'_bot]
      rcases
          (CanLift.prf (x := s') hs'_ne_bot :
            ∃ β : R, ((β : WithBot R) = s')) with
        ⟨β, hβ⟩
      refine ⟨β, fun x hxC ↦ ?_⟩
      have hx_le :
          ((⟪xStar, x⟫ₚ : R) : WithTopBot R) ≤
            s := by
        change
          ((⟪xStar, x⟫ₚ : R) : WithTopBot R) ≤
            (⨆ y : C, ((⟪xStar, y.1⟫ₚ : R) : WithTopBot R))
        exact
          le_iSup (f := fun y : C ↦ ((⟪xStar, y.1⟫ₚ : R) : WithTopBot R)) ⟨x, hxC⟩
      have hs'_eq_β :
          (s' : WithTopBot R) = (β : WithTopBot R) := by
        simpa using congrArg (fun t : WithBot R ↦ (t : WithTopBot R)) hβ.symm
      have hxβ :
          ((⟪xStar, x⟫ₚ : R) : WithTopBot R) ≤ (β : WithTopBot R) := by
        calc
          ((⟪xStar, x⟫ₚ : R) : WithTopBot R) ≤ s := hx_le
          _ = (s' : WithTopBot R) := hs'.symm
          _ = (β : WithTopBot R) := hs'_eq_β
      have hxβ' :
          ((⟪xStar, x⟫ₚ : R) : WithBot R) ≤ (β : WithBot R) :=
        (WithTop.coe_le_coe).1 hxβ
      exact (WithBot.coe_le_coe).1 hxβ'
    · classical
      let β : R := Classical.choice (inferInstance : Nonempty R)
      refine ⟨β, fun x hxC ↦ ?_⟩
      exact (hC_nonempty ⟨x, hxC⟩).elim

/-- A functional belongs to the barrier cone exactly when the support function is finite there. -/
theorem mem_barrierCone_iff_supportFunction_lt_top
    {C : Set X} {xStar : Y} :
    xStar ∈ barr[R](C) ↔ (δᵛ(xStar | C) : WithTopBot R) < (⊤ : WithTopBot R) := by
  exact
    (mem_barrierCone_iff_mem_effectiveDomain_supportFunction (C := C) (xStar := xStar)).trans
      mem_effectiveDomain

/-- The barrier cone is exactly the effective domain of the support function. -/
theorem barrierCone_eq_effectiveDomain_supportFunction
    (C : Set X) :
    (barr[R](C) : Set Y) = dom((δᵛ(· | C) : Y → WithTopBot R)) := by
  ext xStar
  exact mem_barrierCone_iff_mem_effectiveDomain_supportFunction (C := C) (xStar := xStar)

section SelfPairing

variable {Z : Type*} [HasPairing Z Z R]

/-- In the self-pairing setting, barrier-cone membership is equivalent to effective-domain
membership for the source-facing support function owner `δᵛ(· | C)`. -/
theorem mem_barrierCone_iff_mem_effectiveDomain_supportFunction_self
    {C : Set Z} {zStar : Z} :
    zStar ∈ barr[R](C) ↔ zStar ∈ dom((δᵛ(· | C) : Z → WithTopBot R)) := by
  simpa using
    (mem_barrierCone_iff_mem_effectiveDomain_supportFunction
      (R := R) (X := Z) (Y := Z) (C := C) (xStar := zStar))

/-- Self-pairing set-level form of
`mem_barrierCone_iff_mem_effectiveDomain_supportFunction_self`. -/
theorem barrierCone_eq_effectiveDomain_supportFunction_self
    (C : Set Z) :
    (barr[R](C) : Set Z) = dom((δᵛ(· | C) : Z → WithTopBot R)) := by
  refine Set.ext ?_
  intro zStar
  exact mem_barrierCone_iff_mem_effectiveDomain_supportFunction_self
    (R := R) (C := C) (zStar := zStar)

end SelfPairing

end

/-! ### Text_13_0_5 (from Chap03) -/
noncomputable section

open scoped Rockafellar

section

variable {X Y α : Type*} [TopologicalSpace X]
variable [ConditionallyCompleteLattice α] [TopologicalSpace α] [OrderClosedTopology α]
variable [HasPairing X Y α] [HasContinuousPairing X Y α]

-- Canonical swapped pairing view used by support-function owners on the dual side.
local instance : HasPairing Y X α :=
  HasPairing.swap (X := X) (Y := Y) (L := α)
local instance : HasPairingSwap X Y α where
  pairing_swap _ _ := rfl
local instance : HasPairing X Y (WithTopBot α) := instHasPairingWithBotTop
local instance : HasPairing Y X (WithTopBot α) := instHasPairingWithBotTop

/-
Source/core/bridge triage:
- `source-facing`: Text 13.0.5 states that the support function of a convex set is unchanged by
  passing either to its closure or to its relative interior.
- `core/canonical`: the owner abstractions are the project support function `supportFunction`, the
  closure operator `closure`, and (for the second theorem) the convexity/relative-interior owners.
- `bridge/view`: Rockafellar's `δ*(x⋆ | C)` is represented by `supportFunction C xStar`.
- Primitive data vs derived API: the closure identity is derived directly from the owner set
  `C : Set X`, so its public API should not store a redundant convexity hypothesis.
- Domain-style sampling used here: `supportFunction`,
  `subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le`, and
  `closedHalfSpaceLE_closed` (used through a `WithTopBot` bridge lemma).
- Layer target: the closure form is the pairing/topological owner statement, not an
  inner-product-space specialization.
-/

/-- Closedness bridge for `WithTopBot` thresholds: the half-space cut
by `⟪x, xStar⟫ₚ ≤ β` is closed for every `β : WithTopBot α`. -/
theorem closedHalfSpaceLE_closed_withTopBot (xStar : Y) (β : WithTopBot α) :
    IsClosed (closedHalfSpaceLE (X := X) xStar β) := by
  cases β with
  | none =>
      change IsClosed (closedHalfSpaceLE (X := X) xStar (⊤ : WithTopBot α))
      have hEq : closedHalfSpaceLE (X := X) xStar (⊤ : WithTopBot α) = (Set.univ : Set X) := by
        ext x
        constructor
        · intro _
          trivial
        · intro _
          exact (mem_closedHalfSpaceLE_iff (X := X)).2 le_top
      simp [hEq]
  | some β' =>
      cases β' with
      | bot =>
          change IsClosed (closedHalfSpaceLE (X := X) xStar (⊥ : WithTopBot α))
          have hEq : closedHalfSpaceLE (X := X) xStar (⊥ : WithTopBot α) = (∅ : Set X) := by
            ext x
            constructor
            · intro hx
              have hxTop : (⟪x, xStar⟫ₚ : WithTopBot α) ≤ (⊥ : WithTopBot α) :=
                (mem_closedHalfSpaceLE_iff (X := X)).1 hx
              have hxBot : ((⟪x, xStar⟫ₚ : α) : WithBot α) ≤ (⊥ : WithBot α) :=
                (WithTop.coe_le_coe).1 hxTop
              exact (WithBot.not_coe_le_bot (⟪x, xStar⟫ₚ) hxBot).elim
            · intro hx
              exact False.elim hx
          simp [hEq]
      | coe a =>
          change IsClosed (closedHalfSpaceLE (X := X) xStar (((a : α) : WithBot α) : WithTopBot α))
          have hEq :
              closedHalfSpaceLE (X := X) xStar (((a : α) : WithBot α) : WithTopBot α) =
                closedHalfSpaceLE (X := X) (Y := Y) (R := α) xStar a := by
            ext x
            constructor
            · intro hx
              have hxTop : (⟪x, xStar⟫ₚ : WithTopBot α) ≤ (((a : α) : WithBot α) : WithTopBot α) :=
                (mem_closedHalfSpaceLE_iff (X := X)).1 hx
              have hxBot : ((⟪x, xStar⟫ₚ : α) : WithBot α) ≤ ((a : α) : WithBot α) :=
                (WithTop.coe_le_coe).1 hxTop
              have hxα : (⟪x, xStar⟫ₚ : α) ≤ a := (WithBot.coe_le_coe).1 hxBot
              exact (mem_closedHalfSpaceLE_iff (X := X)).2 hxα
            · intro hx
              have hxα : (⟪x, xStar⟫ₚ : α) ≤ a := (mem_closedHalfSpaceLE_iff (X := X)).1 hx
              have hxBot : ((⟪x, xStar⟫ₚ : α) : WithBot α) ≤ ((a : α) : WithBot α) :=
                (WithBot.coe_le_coe).2 hxα
              have hxTop :
                  (((⟪x, xStar⟫ₚ : α) : WithBot α) : WithTopBot α) ≤
                    ((((a : α) : WithBot α) : WithTopBot α)) :=
                (WithTop.coe_le_coe).2 hxBot
              exact (mem_closedHalfSpaceLE_iff (X := X)).2 hxTop
          simpa [hEq] using (closedHalfSpaceLE_closed (X := X) (Y := Y) (R := α) xStar a)

/-- Text 13.0.5 (closure form): passing from a set `C` to `closure C` does not change its support
function. -/

-- Proof sketch: monotonicity gives `supportFunction C ≤ supportFunction (closure C)`. For the
-- reverse inequality, apply Text 13.0.3 at threshold
-- `β := δᵛ[WithTopBot α](xStar | C)`, which gives `C ⊆ closedHalfSpaceLE xStar β`. Since that
-- half-space is closed, `closure C` is still inside it, and Text 13.0.3 again yields
-- `δᵛ[WithTopBot α](xStar | closure C) ≤ β`.
theorem supportFunction_closure {C : Set X} :
    (δᵛ(· | closure C) : Y → WithTopBot α) =
      (δᵛ(· | C) : Y → WithTopBot α) := by
  ext xStar
  refine le_antisymm ?_ ?_
  · have hCsubset : C ⊆ closedHalfSpaceLE xStar ((δᵛ(xStar | C) : WithTopBot α)) :=
      (subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le
        C xStar ((δᵛ(xStar | C) : WithTopBot α))).2 le_rfl
    have hclosureSubset :
        closure C ⊆ closedHalfSpaceLE xStar ((δᵛ(xStar | C) : WithTopBot α)) :=
      closure_minimal hCsubset
        (closedHalfSpaceLE_closed_withTopBot xStar ((δᵛ(xStar | C) : WithTopBot α)))
    exact
      (subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le
        (closure C) xStar ((δᵛ(xStar | C) : WithTopBot α))).1 hclosureSubset
  · rw [supportFunction_def, supportFunction_def]
    refine iSup_le ?_
    intro y
    exact le_iSup_of_le ⟨y, subset_closure y.2⟩ le_rfl

/-- Primitive closure bridge: if two sets have the same closure, then they have the same support
function. -/
theorem supportFunction_eq_of_closure_eq {C D : Set X} (hCD : closure C = closure D) :
    (δᵛ(· | C) : Y → WithTopBot α) =
      (δᵛ(· | D) : Y → WithTopBot α) := by
  calc
    (δᵛ(· | C) : Y → WithTopBot α) =
        (δᵛ(· | closure C) : Y → WithTopBot α) := by
      simpa using (supportFunction_closure (C := C)).symm
    _ = (δᵛ(· | closure D) : Y → WithTopBot α) := by
      rw [hCD]
    _ = (δᵛ(· | D) : Y → WithTopBot α) := supportFunction_closure (C := D)

end

section

variable {𝕜 X Y α : Type*}
variable [Ring 𝕜]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [ConditionallyCompleteLattice α] [TopologicalSpace α] [OrderClosedTopology α]
variable [HasPairing X Y α] [HasContinuousPairing X Y α]

-- Canonical swapped pairing view used by support-function owners on the dual side.
local instance : HasPairing Y X α :=
  HasPairing.swap (X := X) (Y := Y) (L := α)
local instance : HasPairingSwap X Y α where
  pairing_swap _ _ := rfl
local instance : HasPairing X Y (WithTopBot α) := instHasPairingWithBotTop
local instance : HasPairing Y X (WithTopBot α) := instHasPairingWithBotTop

/-- Primitive relative-interior bridge for Text 13.0.5: if `closure (ri[𝕜](C)) = closure C`,
then passing from `C` to `ri[𝕜](C)` does not change the support function. -/
theorem supportFunction_ri_of_closure_eq
    {C : Set X} (hri : closure (ri[𝕜](C)) = closure C) :
    (δᵛ(· | ri[𝕜](C)) : Y → WithTopBot α) =
      (δᵛ(· | C) : Y → WithTopBot α) := by
  exact supportFunction_eq_of_closure_eq hri

end

section

variable {𝕜 X Y α : Type*}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace 𝕜]
variable [ConditionallyCompleteLattice α] [TopologicalSpace α] [OrderClosedTopology α]
variable [HasPairing X Y α] [HasContinuousPairing X Y α]
variable [FiniteDimensional 𝕜 X]

-- Canonical swapped pairing view used by support-function owners on the dual side.
local instance : HasPairing Y X α :=
  HasPairing.swap (X := X) (Y := Y) (L := α)
local instance : HasPairingSwap X Y α where
  pairing_swap _ _ := rfl
local instance : HasPairing X Y (WithTopBot α) := instHasPairingWithBotTop
local instance : HasPairing Y X (WithTopBot α) := instHasPairingWithBotTop

omit [LinearOrder 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Finite-dimensional intrinsic bridge: equality of intrinsic closures of `ri[𝕜](C)` and `C`
implies support-function equality between those sets. -/
theorem supportFunction_ri_of_intrinsicClosure_eq {C : Set X}
    (hri : intrinsicClosure 𝕜 (ri[𝕜](C)) = intrinsicClosure 𝕜 C) :
    (δᵛ(· | ri[𝕜](C)) : Y → WithTopBot α) =
      (δᵛ(· | C) : Y → WithTopBot α) := by
  apply supportFunction_ri_of_closure_eq (C := C)
  simpa [intrinsicClosure_eq_closure 𝕜 (ri[𝕜](C)),
    intrinsicClosure_eq_closure 𝕜 C] using hri

namespace Convex

/-- Text 13.0.5 (relative-interior form): for a convex set `C`, passing from `C` to
`intrinsicInterior 𝕜 C` does not change its support function, with values in
`WithTopBot α`. -/
-- Proof sketch: use the intrinsic-closure form from Theorem 6.3,
-- `Convex.intrinsicClosure_ri_eq_intrinsicClosure hC`, then apply the finite-dimensional
-- owner-level bridge `supportFunction_ri_of_intrinsicClosure_eq`.
theorem supportFunction_intrinsicInterior {C : Set X} (hC : Convex 𝕜 C) :
    (δᵛ(· | ri[𝕜](C)) : Y → WithTopBot α) =
      (δᵛ(· | C) : Y → WithTopBot α) := by
  exact
    supportFunction_ri_of_intrinsicClosure_eq
      (C := C) hC.intrinsicClosure_ri_eq_intrinsicClosure

end Convex

end
