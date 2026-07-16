import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {X : Type*} {Y : Type*} {R : Type*}

/-
Source/core/bridge triage:
  half-spaces in finite-dimensional coordinate models, cut out by one nontrivial linear
  inequality. The owner layer here keeps
  only the primitive pairing data needed for those inequalities, rather than fixing an
  inner-product-space realization from the start.
- `core/canonical`: the owner abstractions are the interval preimages of the pairing functional
  `fun x ↦ ⟪x, b⟫ₚ`, equivalently of `HasLinearPairing.pairingLinear.flip b` in the linear layer.
- `bridge/view`: the four subset constructors `closedHalfSpaceLE`, `closedHalfSpaceGE`,
  `openHalfSpaceLT`, and `openHalfSpaceGT` are thin source-facing names for those interval
  preimages, while `Set.IsClosedHalfSpace Y 𝕜 s` and `Set.IsOpenHalfSpace Y 𝕜 s` classify subsets
  cut out by one nontrivial pairing functional in either textbook orientation.
- `intrinsic owner`: `Set.IsClosedLinearHalfSpace 𝕜 s` and
  `Set.IsOpenLinearHalfSpace 𝕜 s` are the pairing-free linear-functional owners (witnessed by
  `X →ₗ[𝕜] 𝕜`), with pairing-side predicates treated as bridge views into this intrinsic layer.
- Primitive data vs derived API: the primitive half-space data are the interval-preimage owner
  subsets, and the four named constructors are the source-facing bridge to that owner layer. The
  predicates saying that a set is a closed or open half-space are derived API. Their witness data
  should bundle a pairing functional that is genuinely
  nontrivial, because at the primitive pairing layer the mathematically relevant side condition is
  not `b ≠ 0` by itself but that the induced inequality is cut out by a nonconstant pairing
  functional.
- Domain-style sampling:
  `HasPairing` from `HasPairing.lean` isolates the primitive bilinear/evaluation data used by
  support-function and conjugate constructions later in the chapter, while `HasLinearPairing`
  is the canonical owner for genuinely linear-functional notions. Accordingly, the primitive set
  constructors stay at the raw pairing layer, but the textbook predicates `IsClosedHalfSpace` and
  `IsOpenHalfSpace` live on `HasLinearPairing`, with the pairing-side parameter `Y` and scalar
  parameter `𝕜` explicit in the owner surface and inner-product-space nonzero-normal bridges added
  only as companion theorems.
-/

section ClosedPrimitive

variable [LE R]
variable [HasPairing X Y R]
/-- The closed half-space `{x | ⟪x, b⟫ₚ ≤ β}` cut out by one pairing inequality. Specializing to
the inner-product pairing recovers the textbook coordinate form. -/
def closedHalfSpaceLE (b : Y) (β : R) : Set X :=
  {x : X | ⟪x, b⟫ₚ ≤ β}

/-- Membership in `closedHalfSpaceLE b β` is the inequality `⟪x, b⟫ₚ ≤ β`. -/
@[simp]
theorem mem_closedHalfSpaceLE_iff {b : Y} {x : X} {β : R} :
    x ∈ closedHalfSpaceLE b β ↔ ⟪x, b⟫ₚ ≤ β :=
  Iff.rfl

/-- The closed half-space `{x | β ≤ ⟪x, b⟫ₚ}` cut out by a pairing superlevel inequality. -/
abbrev closedHalfSpaceGE (b : Y) (β : R) : Set X :=
  {x : X | β ≤ ⟪x, b⟫ₚ}

/-- Membership in `closedHalfSpaceGE b β` is the inequality `β ≤ ⟪x, b⟫ₚ`. -/
@[simp]
theorem mem_closedHalfSpaceGE_iff {b : Y} {x : X} {β : R} :
    x ∈ closedHalfSpaceGE b β ↔ β ≤ ⟪x, b⟫ₚ :=
  Iff.rfl

end ClosedPrimitive

section ClosedOrder

variable [Preorder R]
variable [HasPairing X Y R]

/-- `closedHalfSpaceLE b β` is the `β`-sublevel preimage of the pairing functional
`x ↦ ⟪x, b⟫ₚ`. -/
theorem closedHalfSpaceLE_eq_preimage (b : Y) (β : R) :
    closedHalfSpaceLE b β = (fun x : X ↦ ⟪x, b⟫ₚ) ⁻¹' Set.Iic β :=
  by
    ext x
    rfl

/-- `closedHalfSpaceGE b β` is the `β`-superlevel preimage of the pairing functional
`x ↦ ⟪x, b⟫ₚ`. -/
theorem closedHalfSpaceGE_eq_preimage (b : Y) (β : R) :
    closedHalfSpaceGE b β = (fun x : X ↦ ⟪x, b⟫ₚ) ⁻¹' Set.Ici β :=
  by
    ext x
    rfl

end ClosedOrder

section OpenPrimitive

variable [LT R]
variable [HasPairing X Y R]

/-- The open half-space `{x | ⟪x, b⟫ₚ < β}` cut out by one pairing inequality. -/
def openHalfSpaceLT (b : Y) (β : R) : Set X :=
  {x : X | ⟪x, b⟫ₚ < β}

/-- Membership in `openHalfSpaceLT b β` is the inequality `⟪x, b⟫ₚ < β`. -/
@[simp]
theorem mem_openHalfSpaceLT_iff {b : Y} {x : X} {β : R} :
    x ∈ openHalfSpaceLT b β ↔ ⟪x, b⟫ₚ < β :=
  Iff.rfl

/-- The open half-space `{x | β < ⟪x, b⟫ₚ}` cut out by a pairing superlevel inequality. -/
abbrev openHalfSpaceGT (b : Y) (β : R) : Set X :=
  {x : X | β < ⟪x, b⟫ₚ}

/-- Membership in `openHalfSpaceGT b β` is the inequality `β < ⟪x, b⟫ₚ`. -/
@[simp]
theorem mem_openHalfSpaceGT_iff {b : Y} {x : X} {β : R} :
    x ∈ openHalfSpaceGT b β ↔ β < ⟪x, b⟫ₚ :=
  Iff.rfl

end OpenPrimitive

section OpenOrder

variable [Preorder R]
variable [HasPairing X Y R]

/-- `openHalfSpaceLT b β` is the strict `β`-sublevel preimage of the pairing functional
`x ↦ ⟪x, b⟫ₚ`. -/
theorem openHalfSpaceLT_eq_preimage (b : Y) (β : R) :
    openHalfSpaceLT b β = (fun x : X ↦ ⟪x, b⟫ₚ) ⁻¹' Set.Iio β :=
  by
    ext x
    rfl

/-- `openHalfSpaceGT b β` is the strict `β`-superlevel preimage of the pairing functional
`x ↦ ⟪x, b⟫ₚ`. -/
theorem openHalfSpaceGT_eq_preimage (b : Y) (β : R) :
    openHalfSpaceGT b β = (fun x : X ↦ ⟪x, b⟫ₚ) ⁻¹' Set.Ioi β :=
  by
    ext x
    rfl

end OpenOrder

namespace Set

section ClosedLinear

variable {𝕜 : Type*}
variable [LE 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable (Y) (𝕜)

/-- Definition 2.0.3: a subset is a closed half-space when it is cut out by one nontrivial
linear inequality, in either textbook orientation `⟪x, b⟫ₚ ≤ β` or `β ≤ ⟪x, b⟫ₚ`. The witness
normal stores the nontriviality of the induced linear functional
`HasLinearPairing.pairingLinear.flip b : X →ₗ[𝕜] 𝕜`. -/
def IsClosedHalfSpace (s : Set X) : Prop :=
  ∃ b : Y, ∃ β : 𝕜, HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
    (s = closedHalfSpaceLE b β ∨ s = closedHalfSpaceGE b β)

variable {Y} {𝕜}

/-- The canonical linear half-space `closedHalfSpaceLE b β` is a closed half-space whenever the
cutting linear functional is nontrivial. -/
theorem closedHalfSpaceLE_isClosedHalfSpace {b : Y} {β : 𝕜}
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    Set.IsClosedHalfSpace Y 𝕜 (closedHalfSpaceLE b β : Set X) :=
  ⟨b, β, hb, Or.inl rfl⟩

/-- The canonical linear half-space `closedHalfSpaceGE b β` is a closed half-space whenever the
cutting linear functional is nontrivial. -/
theorem closedHalfSpaceGE_isClosedHalfSpace {b : Y} {β : 𝕜}
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    Set.IsClosedHalfSpace Y 𝕜 (closedHalfSpaceGE b β : Set X) :=
  ⟨b, β, hb, Or.inr rfl⟩

end ClosedLinear

section OpenLinear

variable {𝕜 : Type*}
variable [LT 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable (Y) (𝕜)

/-- Definition 2.0.3: a subset is an open half-space when it is cut out by one nontrivial linear
inequality, in either textbook orientation `⟪x, b⟫ₚ < β` or `β < ⟪x, b⟫ₚ`. -/
def IsOpenHalfSpace (s : Set X) : Prop :=
  ∃ b : Y, ∃ β : 𝕜, HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
    (s = openHalfSpaceLT b β ∨ s = openHalfSpaceGT b β)

variable {Y} {𝕜}

/-- The canonical linear half-space `openHalfSpaceLT b β` is an open half-space whenever the
cutting linear functional is nontrivial. -/
theorem openHalfSpaceLT_isOpenHalfSpace {b : Y} {β : 𝕜}
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    Set.IsOpenHalfSpace Y 𝕜 (openHalfSpaceLT b β : Set X) :=
  ⟨b, β, hb, Or.inl rfl⟩

/-- The canonical linear half-space `openHalfSpaceGT b β` is an open half-space whenever the
cutting linear functional is nontrivial. -/
theorem openHalfSpaceGT_isOpenHalfSpace {b : Y} {β : 𝕜}
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    Set.IsOpenHalfSpace Y 𝕜 (openHalfSpaceGT b β : Set X) :=
  ⟨b, β, hb, Or.inr rfl⟩

end OpenLinear

section Linear

variable {𝕜 : Type*}
variable [LE 𝕜] [LT 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable (Y) (𝕜)

scoped[Rockafellar] notation3:max "closedHalfSpace[" Y "," 𝕜 "] " s =>
  Set.IsClosedHalfSpace Y 𝕜 s
scoped[Rockafellar] notation3:max "openHalfSpace[" Y "," 𝕜 "] " s =>
  Set.IsOpenHalfSpace Y 𝕜 s

/-- A subset is a half-space when it is either a closed half-space or an open half-space cut out
by one nontrivial linear inequality. This is the canonical source-facing owner for textbook
half-space statements that are independent of closed/open orientation. -/
def IsHalfSpace (s : Set X) : Prop :=
  Set.IsClosedHalfSpace Y 𝕜 s ∨ Set.IsOpenHalfSpace Y 𝕜 s

scoped[Rockafellar] notation3:max "halfSpace[" Y "," 𝕜 "] " s =>
  Set.IsHalfSpace Y 𝕜 s

variable {Y} {𝕜}

end Linear

section LinearFunctionalOwner

variable {𝕜 : Type*}
variable [Preorder 𝕜] [Semiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable (𝕜)

/-- Intrinsic linear-functional owner: a subset is a closed half-space when it is cut out by one
nonzero scalar-valued linear functional, in either orientation `f x ≤ β` or `β ≤ f x`. -/
def IsClosedLinearHalfSpace (s : Set X) : Prop :=
  ∃ f : X →ₗ[𝕜] 𝕜, ∃ β : 𝕜, f ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
    (s = f ⁻¹' Set.Iic β ∨ s = f ⁻¹' Set.Ici β)

/-- Intrinsic linear-functional owner: a subset is an open half-space when it is cut out by one
nonzero scalar-valued linear functional, in either orientation `f x < β` or `β < f x`. -/
def IsOpenLinearHalfSpace (s : Set X) : Prop :=
  ∃ f : X →ₗ[𝕜] 𝕜, ∃ β : 𝕜, f ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
    (s = f ⁻¹' Set.Iio β ∨ s = f ⁻¹' Set.Ioi β)

/-- Intrinsic linear-functional owner for half-spaces independent of closed/open orientation. -/
def IsLinearHalfSpace (s : Set X) : Prop :=
  IsClosedLinearHalfSpace 𝕜 s ∨ IsOpenLinearHalfSpace 𝕜 s

scoped[Rockafellar] notation3:max "closedLinearHalfSpace[" 𝕜 "] " s =>
  Set.IsClosedLinearHalfSpace 𝕜 s
scoped[Rockafellar] notation3:max "openLinearHalfSpace[" 𝕜 "] " s =>
  Set.IsOpenLinearHalfSpace 𝕜 s
scoped[Rockafellar] notation3:max "linearHalfSpace[" 𝕜 "] " s =>
  Set.IsLinearHalfSpace 𝕜 s

end LinearFunctionalOwner

section LinearFunctionalPairingBridge

variable {𝕜 : Type*}
variable [Preorder 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]

/-- Pairing-owner closed half-spaces are intrinsic linear-functional closed half-spaces. -/
theorem IsClosedHalfSpace.toClosedLinearHalfSpace {Y : Type*}
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    {s : Set X} (hs : closedHalfSpace[Y,𝕜] s) :
    closedLinearHalfSpace[𝕜] s := by
  rcases hs with ⟨b, β, hb, hs | hs⟩
  · refine ⟨HasLinearPairing.pairingLinear.flip b, β, hb, Or.inl ?_⟩
    calc
      s = closedHalfSpaceLE b β := hs
      _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iic β := by
        ext x
        simp [closedHalfSpaceLE, HasLinearPairing.pairing_eq_pairingLinear]
  · refine ⟨HasLinearPairing.pairingLinear.flip b, β, hb, Or.inr ?_⟩
    calc
      s = closedHalfSpaceGE b β := hs
      _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ici β := by
        ext x
        simp [closedHalfSpaceGE, HasLinearPairing.pairing_eq_pairingLinear]

/-- Pairing-owner open half-spaces are intrinsic linear-functional open half-spaces. -/
theorem IsOpenHalfSpace.toOpenLinearHalfSpace {Y : Type*}
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    {s : Set X} (hs : openHalfSpace[Y,𝕜] s) :
    openLinearHalfSpace[𝕜] s := by
  rcases hs with ⟨b, β, hb, hs | hs⟩
  · refine ⟨HasLinearPairing.pairingLinear.flip b, β, hb, Or.inl ?_⟩
    calc
      s = openHalfSpaceLT b β := hs
      _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iio β := by
        ext x
        simp [openHalfSpaceLT, HasLinearPairing.pairing_eq_pairingLinear]
  · refine ⟨HasLinearPairing.pairingLinear.flip b, β, hb, Or.inr ?_⟩
    calc
      s = openHalfSpaceGT b β := hs
      _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ioi β := by
        ext x
        simp [openHalfSpaceGT, HasLinearPairing.pairing_eq_pairingLinear]

/-- Pairing-owner half-spaces are intrinsic linear-functional half-spaces. -/
theorem IsHalfSpace.toLinearHalfSpace {Y : Type*}
    [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    {s : Set X} (hs : halfSpace[Y,𝕜] s) :
    linearHalfSpace[𝕜] s := by
  rcases hs with hs | hs
  · exact Or.inl hs.toClosedLinearHalfSpace
  · exact Or.inr hs.toOpenLinearHalfSpace

/-- Under surjectivity of `HasLinearPairing.pairingLinear.flip`, every intrinsic closed linear
half-space admits a pairing-owner witness. -/
theorem IsClosedLinearHalfSpace.toClosedHalfSpace_of_surjective_pairingLinear_flip
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (hflip : Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → X →ₗ[𝕜] 𝕜))
    {s : Set X} (hs : closedLinearHalfSpace[𝕜] s) :
    closedHalfSpace[Y,𝕜] s := by
  rcases hs with ⟨f, β, hf, hs | hs⟩
  · rcases hflip f with ⟨b, rfl⟩
    refine ⟨b, β, ?_, Or.inl ?_⟩
    · simpa using hf
    · calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iic β := hs
        _ = closedHalfSpaceLE b β := by
          ext x
          simp [closedHalfSpaceLE, HasLinearPairing.pairing_eq_pairingLinear]
  · rcases hflip f with ⟨b, rfl⟩
    refine ⟨b, β, ?_, Or.inr ?_⟩
    · simpa using hf
    · calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ici β := hs
        _ = closedHalfSpaceGE b β := by
          ext x
          simp [closedHalfSpaceGE, HasLinearPairing.pairing_eq_pairingLinear]

/-- Under surjectivity of `HasLinearPairing.pairingLinear.flip`, every intrinsic open linear
half-space admits a pairing-owner witness. -/
theorem IsOpenLinearHalfSpace.toOpenHalfSpace_of_surjective_pairingLinear_flip
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (hflip : Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → X →ₗ[𝕜] 𝕜))
    {s : Set X} (hs : openLinearHalfSpace[𝕜] s) :
    openHalfSpace[Y,𝕜] s := by
  rcases hs with ⟨f, β, hf, hs | hs⟩
  · rcases hflip f with ⟨b, rfl⟩
    refine ⟨b, β, ?_, Or.inl ?_⟩
    · simpa using hf
    · calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iio β := hs
        _ = openHalfSpaceLT b β := by
          ext x
          simp [openHalfSpaceLT, HasLinearPairing.pairing_eq_pairingLinear]
  · rcases hflip f with ⟨b, rfl⟩
    refine ⟨b, β, ?_, Or.inr ?_⟩
    · simpa using hf
    · calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ioi β := hs
        _ = openHalfSpaceGT b β := by
          ext x
          simp [openHalfSpaceGT, HasLinearPairing.pairing_eq_pairingLinear]

/-- Under surjectivity of `HasLinearPairing.pairingLinear.flip`, intrinsic linear half-spaces and
pairing-owner half-spaces coincide. -/
theorem IsLinearHalfSpace.toHalfSpace_of_surjective_pairingLinear_flip
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (hflip : Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → X →ₗ[𝕜] 𝕜))
    {s : Set X} (hs : linearHalfSpace[𝕜] s) :
    halfSpace[Y,𝕜] s := by
  rcases hs with hs | hs
  · exact Or.inl (hs.toClosedHalfSpace_of_surjective_pairingLinear_flip (Y := Y) hflip)
  · exact Or.inr (hs.toOpenHalfSpace_of_surjective_pairingLinear_flip (Y := Y) hflip)

/-- Under surjectivity of `HasLinearPairing.pairingLinear.flip`, pairing-owner and intrinsic
closed-half-space owners are equivalent. -/
theorem isClosedHalfSpace_iff_closedLinearHalfSpace_of_surjective_pairingLinear_flip
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (hflip : Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → X →ₗ[𝕜] 𝕜))
    {s : Set X} :
    IsClosedHalfSpace Y 𝕜 s ↔ IsClosedLinearHalfSpace 𝕜 s := by
  constructor
  · intro hs
    exact hs.toClosedLinearHalfSpace
  · intro hs
    exact hs.toClosedHalfSpace_of_surjective_pairingLinear_flip (Y := Y) hflip

/-- Under surjectivity of `HasLinearPairing.pairingLinear.flip`, pairing-owner and intrinsic
open-half-space owners are equivalent. -/
theorem isOpenHalfSpace_iff_openLinearHalfSpace_of_surjective_pairingLinear_flip
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (hflip : Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → X →ₗ[𝕜] 𝕜))
    {s : Set X} :
    IsOpenHalfSpace Y 𝕜 s ↔ IsOpenLinearHalfSpace 𝕜 s := by
  constructor
  · intro hs
    exact hs.toOpenLinearHalfSpace
  · intro hs
    exact hs.toOpenHalfSpace_of_surjective_pairingLinear_flip (Y := Y) hflip

/-- Under surjectivity of `HasLinearPairing.pairingLinear.flip`, pairing-owner and intrinsic
half-space owners are equivalent. -/
theorem isHalfSpace_iff_linearHalfSpace_of_surjective_pairingLinear_flip
    {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing X Y 𝕜]
    (hflip : Function.Surjective (HasLinearPairing.pairingLinear.flip : Y → X →ₗ[𝕜] 𝕜))
    {s : Set X} :
    IsHalfSpace Y 𝕜 s ↔ IsLinearHalfSpace 𝕜 s := by
  constructor
  · intro hs
    exact hs.toLinearHalfSpace
  · intro hs
    exact hs.toHalfSpace_of_surjective_pairingLinear_flip (Y := Y) hflip

end LinearFunctionalPairingBridge

section ClosedLinearFunctionalCharacterization

variable {𝕜 : Type*}
variable [Preorder 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable {s : Set X}

/-- `IsClosedHalfSpace` is equivalent to a preimage description by the scalar-valued linear
functional `HasLinearPairing.pairingLinear.flip b`. -/
theorem isClosedHalfSpace_iff_exists_pairingLinear_preimage :
    (closedHalfSpace[Y,𝕜] s) ↔
      ∃ b : Y, ∃ β : 𝕜,
        HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
          (s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iic β ∨
            s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ici β) := by
  constructor
  · intro hs
    rcases hs with ⟨b, β, hb, hs | hs⟩
    · refine ⟨b, β, hb, Or.inl ?_⟩
      calc
        s = closedHalfSpaceLE b β := hs
        _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iic β := by
          ext x
          simp [closedHalfSpaceLE, HasLinearPairing.pairing_eq_pairingLinear]
    · refine ⟨b, β, hb, Or.inr ?_⟩
      calc
        s = closedHalfSpaceGE b β := hs
        _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ici β := by
          ext x
          simp [closedHalfSpaceGE, HasLinearPairing.pairing_eq_pairingLinear]
  · intro hs
    rcases hs with ⟨b, β, hb, hs | hs⟩
    · refine ⟨b, β, hb, Or.inl ?_⟩
      calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iic β := hs
        _ = closedHalfSpaceLE b β := by
          ext x
          simp [closedHalfSpaceLE, HasLinearPairing.pairing_eq_pairingLinear]
    · refine ⟨b, β, hb, Or.inr ?_⟩
      calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ici β := hs
        _ = closedHalfSpaceGE b β := by
          ext x
          simp [closedHalfSpaceGE, HasLinearPairing.pairing_eq_pairingLinear]

end ClosedLinearFunctionalCharacterization

section OpenLinearFunctionalCharacterization

variable {𝕜 : Type*}
variable [Preorder 𝕜] [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]
variable {s : Set X}

/-- `IsOpenHalfSpace` is equivalent to a strict-preimage description by the scalar-valued linear
functional `HasLinearPairing.pairingLinear.flip b`. -/
theorem isOpenHalfSpace_iff_exists_pairingLinear_preimage :
    (openHalfSpace[Y,𝕜] s) ↔
      ∃ b : Y, ∃ β : 𝕜,
        HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜) ∧
          (s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iio β ∨
            s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ioi β) := by
  constructor
  · intro hs
    rcases hs with ⟨b, β, hb, hs | hs⟩
    · refine ⟨b, β, hb, Or.inl ?_⟩
      calc
        s = openHalfSpaceLT b β := hs
        _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iio β := by
          ext x
          simp [openHalfSpaceLT, HasLinearPairing.pairing_eq_pairingLinear]
    · refine ⟨b, β, hb, Or.inr ?_⟩
      calc
        s = openHalfSpaceGT b β := hs
        _ = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ioi β := by
          ext x
          simp [openHalfSpaceGT, HasLinearPairing.pairing_eq_pairingLinear]
  · intro hs
    rcases hs with ⟨b, β, hb, hs | hs⟩
    · refine ⟨b, β, hb, Or.inl ?_⟩
      calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Iio β := hs
        _ = openHalfSpaceLT b β := by
          ext x
          simp [openHalfSpaceLT, HasLinearPairing.pairing_eq_pairingLinear]
    · refine ⟨b, β, hb, Or.inr ?_⟩
      calc
        s = (HasLinearPairing.pairingLinear.flip b) ⁻¹' Set.Ioi β := hs
        _ = openHalfSpaceGT b β := by
          ext x
          simp [openHalfSpaceGT, HasLinearPairing.pairing_eq_pairingLinear]

end OpenLinearFunctionalCharacterization

section LinearPairingNontrivial

variable {𝕜 : Type*}
variable [CommSemiring 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-- In any linear-pairing ambient layer, a nonzero scalar-valued functional witness
`HasLinearPairing.pairingLinear.flip b ≠ 0` forces the normal parameter to be nonzero. -/
theorem ne_zero_of_pairingLinear_flip_ne_zero {b : Y}
    (hb : HasLinearPairing.pairingLinear.flip b ≠ (0 : X →ₗ[𝕜] 𝕜)) :
    b ≠ 0 := by
  intro hb0
  apply hb
  ext x
  simp [hb0]

end LinearPairingNontrivial

end Set

end
