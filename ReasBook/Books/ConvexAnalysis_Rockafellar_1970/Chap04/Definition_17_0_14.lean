import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

section

variable {𝕜 : Type*} [Ring 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {P : Type*} [AddTorsor E P]

/-
Source/core/bridge triage:
- `source-facing`: Definition 17.0.14 introduces skew orthants as injective affine images of a
  canonical nonnegative cone.
- `core/canonical`: the owner is `Set.IsOrthant`, parameterized by the ordered source module `M`
  and expressed at the intrinsic order layer `Set.Ici (0 : M)` (no ordered-scalar cone API needed
  in the primitive statement).
- `bridge/view`: when the source module is an ordered module in the Chapter 1 sense, the same
  statement is surfaced via notation `orthant[𝕜](M)`.
- Primitive data vs derived API: primitive data are the source ordered additive module, an
  injective affine map `M →ᵃ[𝕜] P`, and the image identity on `Set.Ici (0 : M)`; orthant-notation
  and subtype-range views are bridge APIs.
- Domain-style sampling used here: `Set.Ici`, `orthant[𝕜](M)`, `orthant_eq_Ici`, and
  `Set.image_eq_range`.
- Layer target: `source-facing`; no coordinate-model owner (`EuclideanSpace`, `Fin`) is kept, and
  scalar-order assumptions are only required on orthant-notation bridge surfaces.
-/

namespace Set

variable (𝕜) in
/-- Definition 17.0.14: a skew orthant in an affine `𝕜`-space `P` is the image of a canonical
nonnegative cone under an injective affine map from an ordered source module `M`. -/
def IsOrthant (s : Set P) (M : Type*) [AddCommGroup M] [Preorder M] [Module 𝕜 M] : Prop :=
  ∃ f : M →ᵃ[𝕜] P,
    Function.Injective f ∧ s = f '' (Set.Ici (0 : M))

section

variable {M : Type*} [AddCommGroup M] [Preorder M] [Module 𝕜 M]

variable (𝕜) in
/-- Intrinsic owner surface: a skew orthant is exactly an injective affine image of `Set.Ici 0`
in its source ordered additive module. -/
theorem isOrthant_iff_exists_image_Ici {s : Set P} :
    s.IsOrthant 𝕜 M ↔
      ∃ f : M →ᵃ[𝕜] P,
        Function.Injective f ∧ s = f '' (Set.Ici (0 : M)) :=
  Iff.rfl

variable (𝕜) in
/-- Intrinsic bridge: a skew orthant is equivalently the range of the affine map restricted to
the nonnegative subtype `Set.Ici (0 : M)`. -/
theorem isOrthant_iff_exists_range_IciSubtype {s : Set P} :
    s.IsOrthant 𝕜 M ↔
      ∃ f : M →ᵃ[𝕜] P,
        Function.Injective f ∧
          s = range (fun x : Set.Ici (0 : M) ↦ f x) := by
  constructor
  · rintro ⟨f, hf, hs⟩
    refine ⟨f, hf, hs.trans ?_⟩
    simpa using (Set.image_eq_range (f := f) (s := Set.Ici (0 : M)))
  · rintro ⟨f, hf, hs⟩
    refine ⟨f, hf, hs.trans ?_⟩
    simpa using (Set.image_eq_range (f := f) (s := Set.Ici (0 : M))).symm

end

section OrthantNotationBridge

variable {M : Type*} [AddCommGroup M] [Module 𝕜 M]
variable [PartialOrder 𝕜] [PartialOrder M] [IsOrderedAddMonoid M] [PosSMulMono 𝕜 M]

variable (𝕜) in
/-- Orthant-notation bridge: under the Chapter 1 ordered-module assumptions, a skew orthant is
exactly an injective affine image of `orthant[𝕜](M)`. -/
theorem isOrthant_iff_exists_image_orthant {s : Set P} :
    s.IsOrthant 𝕜 M ↔
      ∃ f : M →ᵃ[𝕜] P,
        Function.Injective f ∧ s = f '' orthant[𝕜](M) := by
  simpa [orthant_eq_Ici (𝕜 := 𝕜) (M := M)] using
    (isOrthant_iff_exists_image_Ici (𝕜 := 𝕜) (M := M) (s := s))

end OrthantNotationBridge

namespace IsOrthant

section

variable {M : Type*} [AddCommGroup M] [Preorder M] [Module 𝕜 M]

/-- Owner-forward bridge: unpack an `IsOrthant` witness into an injective affine image of
`Set.Ici (0 : M)` without unfolding the owner definition at call sites. -/
theorem exists_image_Ici {s : Set P} (hs : s.IsOrthant 𝕜 M) :
    ∃ f : M →ᵃ[𝕜] P,
      Function.Injective f ∧ s = f '' (Set.Ici (0 : M)) :=
  (isOrthant_iff_exists_image_Ici (𝕜 := 𝕜) (M := M) (s := s)).1 hs

/-- Owner-forward bridge to the subtype-range formulation of `Set.Ici (0 : M)`. -/
theorem exists_range_IciSubtype {s : Set P} (hs : s.IsOrthant 𝕜 M) :
    ∃ f : M →ᵃ[𝕜] P,
      Function.Injective f ∧
        s = range (fun x : Set.Ici (0 : M) ↦ f x) :=
  (isOrthant_iff_exists_range_IciSubtype (𝕜 := 𝕜) (M := M) (s := s)).1 hs

end

section OrthantNotationBridge

variable {M : Type*} [AddCommGroup M] [Module 𝕜 M]
variable [PartialOrder 𝕜] [PartialOrder M] [IsOrderedAddMonoid M] [PosSMulMono 𝕜 M]

/-- Owner-forward orthant-notation bridge: unpack an `IsOrthant` witness directly on
`orthant[𝕜](M)`. -/
theorem exists_image_orthant {s : Set P} (hs : s.IsOrthant 𝕜 M) :
    ∃ f : M →ᵃ[𝕜] P,
      Function.Injective f ∧ s = f '' orthant[𝕜](M) :=
  (isOrthant_iff_exists_image_orthant (𝕜 := 𝕜) (M := M) (s := s)).1 hs

end OrthantNotationBridge

end IsOrthant

end Set

end
