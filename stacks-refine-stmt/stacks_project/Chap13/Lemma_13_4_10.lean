import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace CategoryTheory

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive]

/- Domain-style sampling for Lemma 13.4.10:
- primary domain: distinguished triangles in a pretriangulated category and their behavior under
  binary direct sums/products;
- sampled core/canonical declarations:
  `CategoryTheory.productTriangle`,
  `CategoryTheory.Pretriangulated.productTriangle_distinguished`,
  `CategoryTheory.Pretriangulated.distinguished_iff_of_iso`,
  `CategoryTheory.Limits.pairFunction`;
- best owner abstraction: the canonical owner for the forward implication is the generic
  `productTriangle` of a family of triangles, specialized here to the binary family
  `Limits.pairFunction T₁ T₂`; the source-facing direct sum of two triangles should therefore be
  treated as a bridge/view to that owner rather than as an isolated local product API, and this
  bridge itself lives already in the additive-plus-shift layer before distinguished triangles enter;
- primitive-vs-derived split:
  primitive data are the two triangles `T₁`, `T₂` and their source-facing direct-sum triangle;
  derived API is the comparison with the canonical product owner and the distinguishedness
  consequences obtained from `productTriangle_distinguished`.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the direct sum of two triangles is distinguished iff
  both summands are distinguished;
- `core/canonical`: `productTriangle` in the basic triangle layer and
  `productTriangle_distinguished` in the pretriangulated layer;
- `bridge/view`: the source-facing direct-sum triangle `T₁ ⊞ T₂` and its comparison theorem with
  the binary `productTriangle` owner. -/

section

variable [HasBinaryBiproducts D]

namespace Triangle

/-- Internal bridge from a binary biproduct to the generic product over the walking pair. -/
private def biprodIsoPairProduct (X Y : D) : X ⊞ Y ≅ ∏ᶜ pairFunction X Y := by
  let fan : Fan (pairFunction X Y) :=
    Fan.mk (X ⊞ Y) (fun j ↦ WalkingPair.casesOn j biprod.fst biprod.snd)
  let hfan : IsLimit fan := by
    refine mkFanLimit _ (fun s ↦ biprod.lift (s.proj WalkingPair.left) (s.proj WalkingPair.right))
      ?_ ?_
    · intro s j
      cases j <;> simp [fan]
    · intro s m hm
      apply BinaryFan.IsLimit.hom_ext (BinaryBiproduct.isLimit X Y)
      · simpa [fan] using hm WalkingPair.left
      · simpa [fan] using hm WalkingPair.right
  exact (limit.isoLimitCone ⟨fan, hfan⟩).symm

/-- The biproduct of two triangles, formed by taking the biproduct of each object and the direct
sum of each structure morphism. -/
abbrev biprod (T₁ T₂ : Triangle D) : Triangle D :=
  Triangle.mk
    (biprod.map T₁.mor₁ T₂.mor₁)
    (biprod.map T₁.mor₂ T₂.mor₂)
    (biprod.map T₁.mor₃ T₂.mor₃ ≫
      Functor.biprodComparison' (shiftFunctor D (1 : ℤ)) T₁.obj₁ T₂.obj₁)

infixl:70 " ⊞ " => biprod

/-- The canonical comparison isomorphism from the source-facing binary biproduct triangle to the
canonical binary `productTriangle` on the family `(T₁, T₂)`. -/
def biprodIsoProductTrianglePair (T₁ T₂ : Triangle D) :
    T₁ ⊞ T₂ ≅ productTriangle (pairFunction T₁ T₂) := by
  let e₁ : (T₁ ⊞ T₂).obj₁ ≅ (productTriangle (pairFunction T₁ T₂)).obj₁ :=
    (biprodIsoPairProduct T₁.obj₁ T₂.obj₁) ≪≫
      Pi.mapIso (fun j ↦ by cases j <;> exact Iso.refl _)
  let e₂ : (T₁ ⊞ T₂).obj₂ ≅ (productTriangle (pairFunction T₁ T₂)).obj₂ :=
    (biprodIsoPairProduct T₁.obj₂ T₂.obj₂) ≪≫
      Pi.mapIso (fun j ↦ by cases j <;> exact Iso.refl _)
  let e₃ : (T₁ ⊞ T₂).obj₃ ≅ (productTriangle (pairFunction T₁ T₂)).obj₃ :=
    (biprodIsoPairProduct T₁.obj₃ T₂.obj₃) ≪≫
      Pi.mapIso (fun j ↦ by cases j <;> exact Iso.refl _)
  refine Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_
  · sorry
  · sorry
  · sorry

end Triangle

end

section

variable [Pretriangulated D]

-- Proof sketch: identify each binary biproduct object with the corresponding binary product via
-- the universal property of the exact binary product fan on each component; the resulting
-- comparison isomorphism is `Triangle.biprodIsoProductTrianglePair`.
/-- Companion to `Triangle.biprodIsoProductTrianglePair`: the source-facing direct-sum triangle is
distinguished exactly when the canonical binary `productTriangle` on the pair `(T₁, T₂)` is
distinguished. -/
theorem triangle_biprod_distinguished_iff_productTriangle_pair {T₁ T₂ : Triangle D} :
    (T₁ ⊞ T₂) ∈ distTriang D ↔
      productTriangle (pairFunction T₁ T₂) ∈ distTriang D := by
  simpa using distinguished_iff_of_iso (Triangle.biprodIsoProductTrianglePair T₁ T₂)

-- Proof sketch: for the forward direction, complete `T₁.mor₁ ⊞ T₂.mor₁` to a distinguished
-- triangle using TR1, extend the summand inclusions by TR3, and apply Remark 13.4.4 to show the
-- induced map from `T₁ ⊞ T₂` is an isomorphism. For the reverse direction, first
-- pass to the canonical owner `productTriangle (pairFunction T₁ T₂)` via the bridge theorem
-- above and then apply `productTriangle_distinguished`; for the forward direction, view each
-- summand triangle as a direct summand of the distinguished biproduct triangle and apply the same
-- special-triangle two-out-of-three argument.
/-- Lemma 13.4.10: for triangles `T₁` and `T₂` in a pretriangulated category, the direct-sum
triangle `(X ⊕ X', Y ⊕ Y', Z ⊕ Z', f ⊕ f', g ⊕ g', h ⊕ h')` is distinguished if and only if both
summand triangles are distinguished. -/
theorem triangle_biprod_distinguished_iff {T₁ T₂ : Triangle D} :
    (T₁ ⊞ T₂) ∈ distTriang D ↔ T₁ ∈ distTriang D ∧ T₂ ∈ distTriang D := by
  constructor
  · intro h
    sorry
  · rintro ⟨h₁, h₂⟩
    rw [triangle_biprod_distinguished_iff_productTriangle_pair]
    exact productTriangle_distinguished (pairFunction T₁ T₂) <| by
      intro j
      cases j <;> assumption

end

end CategoryTheory
