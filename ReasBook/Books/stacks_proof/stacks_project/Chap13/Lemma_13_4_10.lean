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
  · -- TODO: compare the first biproduct structure map with the walking-pair product map.
    sorry
  · -- TODO: compare the second biproduct structure map with the walking-pair product map.
    sorry
  · -- TODO: compare the shifted third biproduct structure map with the product-triangle third map.
    sorry

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

/-- Helper for Lemma 13.4.10: the first two morphisms of the left summand still compose to zero,
because they are obtained by projecting the zero composite in the distinguished biproduct
triangle. -/
lemma triangle_biprod_zero₁₂_left {T₁ T₂ : Triangle D} (h : (T₁ ⊞ T₂) ∈ distTriang D) :
    T₁.mor₁ ≫ T₁.mor₂ = 0 := by
  -- TODO: project the vanishing composite from the distinguished biproduct triangle to the left
  -- summand using `biprod.inl_map` and `biprod.map_fst`.
  sorry

/-- Helper for Lemma 13.4.10: the first two morphisms of the right summand still compose to zero,
because they are obtained by projecting the zero composite in the distinguished biproduct
triangle. -/
lemma triangle_biprod_zero₁₂_right {T₁ T₂ : Triangle D} (h : (T₁ ⊞ T₂) ∈ distTriang D) :
    T₂.mor₁ ≫ T₂.mor₂ = 0 := by
  -- TODO: project the vanishing composite from the distinguished biproduct triangle to the right
  -- summand using `biprod.inr_map` and `biprod.map_snd`.
  sorry

/-- Helper for Lemma 13.4.10: the second unshifted covariant Hom exactness of the distinguished
biproduct triangle restricts to the left summand. -/
lemma triangle_biprod_coyoneda_exact₃_left {T₁ T₂ : Triangle D}
    (h : (T₁ ⊞ T₂) ∈ distTriang D) {W : D} {f : W ⟶ T₁.obj₃} (hf : f ≫ T₁.mor₃ = 0) :
    ∃ g : W ⟶ T₁.obj₂, f = g ≫ T₁.mor₂ := by
  let f' : W ⟶ (T₁ ⊞ T₂).obj₃ := f ≫ biprod.inl
  have hf' : f' ≫ (T₁ ⊞ T₂).mor₃ = 0 := by
    -- Embed the source morphism into the biproduct triangle and use the left inclusion formula.
    calc
      f' ≫ (T₁ ⊞ T₂).mor₃ = f ≫ (biprod.inl ≫ (T₁ ⊞ T₂).mor₃) := by
        simp [f', Category.assoc]
      _ = f ≫ (T₁.mor₃ ≫ (shiftFunctor D (1 : ℤ)).map biprod.inl) := by
        simp [Triangle.biprod, Category.assoc, Functor.inl_biprodComparison', biprod.inl_map]
      _ = (f ≫ T₁.mor₃) ≫ (shiftFunctor D (1 : ℤ)).map biprod.inl := by
        simp [Category.assoc]
      _ = 0 := by simp [hf]
  obtain ⟨g', hg'⟩ := Triangle.coyoneda_exact₃ (T := T₁ ⊞ T₂) h f' hf'
  refine ⟨g' ≫ biprod.fst, ?_⟩
  -- Project the factorization back to the left summand.
  calc
    f = f' ≫ biprod.fst := by simp [f', Category.assoc]
    _ = (g' ≫ (T₁ ⊞ T₂).mor₂) ≫ biprod.fst := by rw [hg']
    _ = g' ≫ biprod.fst ≫ T₁.mor₂ := by
      simp [Triangle.biprod, Category.assoc, biprod.map_fst]
    _ = (g' ≫ biprod.fst) ≫ T₁.mor₂ := by simp [Category.assoc]

/-- Helper for Lemma 13.4.10: the second unshifted covariant Hom exactness of the distinguished
biproduct triangle restricts to the right summand. -/
lemma triangle_biprod_coyoneda_exact₃_right {T₁ T₂ : Triangle D}
    (h : (T₁ ⊞ T₂) ∈ distTriang D) {W : D} {f : W ⟶ T₂.obj₃} (hf : f ≫ T₂.mor₃ = 0) :
    ∃ g : W ⟶ T₂.obj₂, f = g ≫ T₂.mor₂ := by
  let f' : W ⟶ (T₁ ⊞ T₂).obj₃ := f ≫ biprod.inr
  have hf' : f' ≫ (T₁ ⊞ T₂).mor₃ = 0 := by
    -- Embed the source morphism into the biproduct triangle and use the right inclusion formula.
    calc
      f' ≫ (T₁ ⊞ T₂).mor₃ = f ≫ (biprod.inr ≫ (T₁ ⊞ T₂).mor₃) := by
        simp [f', Category.assoc]
      _ = f ≫ (T₂.mor₃ ≫ (shiftFunctor D (1 : ℤ)).map biprod.inr) := by
        simp [Triangle.biprod, Category.assoc, Functor.inr_biprodComparison', biprod.inr_map]
      _ = (f ≫ T₂.mor₃) ≫ (shiftFunctor D (1 : ℤ)).map biprod.inr := by
        simp [Category.assoc]
      _ = 0 := by simp [hf]
  obtain ⟨g', hg'⟩ := Triangle.coyoneda_exact₃ (T := T₁ ⊞ T₂) h f' hf'
  refine ⟨g' ≫ biprod.snd, ?_⟩
  -- Project the factorization back to the right summand.
  calc
    f = f' ≫ biprod.snd := by simp [f', Category.assoc]
    _ = (g' ≫ (T₁ ⊞ T₂).mor₂) ≫ biprod.snd := by rw [hg']
    _ = g' ≫ biprod.snd ≫ T₂.mor₂ := by
      simp [Triangle.biprod, Category.assoc, biprod.map_snd]
    _ = (g' ≫ biprod.snd) ≫ T₂.mor₂ := by simp [Category.assoc]

/-- Helper for Lemma 13.4.10: the third unshifted covariant Hom exactness of the distinguished
biproduct triangle restricts to the left summand. -/
lemma triangle_biprod_coyoneda_exact₁_left {T₁ T₂ : Triangle D}
    (h : (T₁ ⊞ T₂) ∈ distTriang D) {W : D} {f : W ⟶ T₁.obj₁⟦(1 : ℤ)⟧}
    (hf : f ≫ (T₁.mor₁⟦(1 : ℤ)⟧') = 0) :
    ∃ g : W ⟶ T₁.obj₃, f = g ≫ T₁.mor₃ := by
  -- TODO: this is the remaining transport-heavy direct-summand exactness statement for the third
  -- Hom pair; it needs the shifted biproduct comparison to be normalized explicitly.
  sorry

/-- Helper for Lemma 13.4.10: the third unshifted covariant Hom exactness of the distinguished
biproduct triangle restricts to the right summand. -/
lemma triangle_biprod_coyoneda_exact₁_right {T₁ T₂ : Triangle D}
    (h : (T₁ ⊞ T₂) ∈ distTriang D) {W : D} {f : W ⟶ T₂.obj₁⟦(1 : ℤ)⟧}
    (hf : f ≫ (T₂.mor₁⟦(1 : ℤ)⟧') = 0) :
    ∃ g : W ⟶ T₂.obj₃, f = g ≫ T₂.mor₃ := by
  -- TODO: this is the symmetric transport-heavy direct-summand exactness statement for the third
  -- Hom pair.
  sorry

-- Proof sketch: for the forward direction, complete `T₁.mor₁ ⊞ T₂.mor₁` to a distinguished
-- triangle using TR1, extend the summand inclusions by TR3, and apply Remark 13.4.4 to show the
-- induced map from `T₁ ⊞ T₂` is an isomorphism. For the reverse direction, first
-- pass to the canonical owner `productTriangle (pairFunction T₁ T₂)` via the bridge theorem
-- above and then apply `productTriangle_distinguished`; for the forward direction, view each
-- summand triangle as a direct summand of the distinguished biproduct triangle and apply the same
-- special-triangle two-out-of-three argument.
/-- Helper for Lemma 13.4.10: if the biproduct triangle is distinguished, then its left summand is
distinguished. -/
lemma triangle_distinguished_of_biprod_distinguished_left {T₁ T₂ : Triangle D}
    (h : (T₁ ⊞ T₂) ∈ distTriang D) :
    T₁ ∈ distTriang D := by
  -- TODO: choose a distinguished completion of `T₁.mor₁`, compare it to the left summand by a
  -- morphism with identity first two components, then finish by the local Yoneda diagram chase.
  sorry

/-- Helper for Lemma 13.4.10: if the biproduct triangle is distinguished, then its right summand
is distinguished. -/
lemma triangle_distinguished_of_biprod_distinguished_right {T₁ T₂ : Triangle D}
    (h : (T₁ ⊞ T₂) ∈ distTriang D) :
    T₂ ∈ distTriang D := by
  -- TODO: symmetric to the left summand argument.
  sorry

/-- Lemma 13.4.10: for triangles `T₁` and `T₂` in a pretriangulated category, the direct-sum
triangle `(X ⊕ X', Y ⊕ Y', Z ⊕ Z', f ⊕ f', g ⊕ g', h ⊕ h')` is distinguished if and only if both
summand triangles are distinguished. -/
@[stacks 05QS]
theorem triangle_biprod_distinguished_iff {T₁ T₂ : Triangle D} :
    (T₁ ⊞ T₂) ∈ distTriang D ↔ T₁ ∈ distTriang D ∧ T₂ ∈ distTriang D := by
  constructor
  · intro h
    -- Recover distinguishedness of each summand by comparing it with a distinguished completion
    -- of its first morphism.
    exact ⟨triangle_distinguished_of_biprod_distinguished_left h,
      triangle_distinguished_of_biprod_distinguished_right h⟩
  · rintro ⟨h₁, h₂⟩
    rw [triangle_biprod_distinguished_iff_productTriangle_pair]
    exact productTriangle_distinguished (pairFunction T₁ T₂) <| by
      intro j
      cases j <;> assumption

end

end CategoryTheory
