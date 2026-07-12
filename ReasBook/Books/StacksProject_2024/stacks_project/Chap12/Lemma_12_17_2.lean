import Mathlib
import StacksProject_2024.Chap04.Remark_4_43_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v u

namespace CategoryTheory

open Limits MonoidalCategory

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
variable [HasFiniteBiproducts C]
variable [MonoidalPreadditive C]
variable {X₁ Y₁ X₂ Y₂ : C} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂]

local notation "X" => X₁ ⊞ X₂
local notation "Y" => Y₁ ⊞ Y₂

/-
Domain-style sampling for Lemma 12.17.2:
- primary domain: rigid monoidal category theory in a preadditive monoidal category with finite
  biproducts
- core/canonical declarations inspected:
  - `CategoryTheory.ExactPairing`
  - `CategoryTheory.HasLeftDual`
  - `CategoryTheory.Retract.hasLeftDual` from `Lemma_12_17_3`
  - `Limits.hasBinaryBiproducts_of_finite_biproducts` as the ambient biproduct bridge actually
    used by the construction
- best owner abstraction: `ExactPairing`
- primitive data: explicit exact pairings `X₁ ⊣ Y₁` and `X₂ ⊣ Y₂`
- derived API: the chosen-left-dual owner `HasLeftDual (Y₁ ⊞ Y₂)` when `Xᵢ = ᘁYᵢ`
- source/core/bridge triage:
  - source-facing: the direct sums of two explicit dual pairs again form an explicit dual pair
  - core/canonical: `ExactPairing`
- bridge/view: `HasLeftDual.biprod` obtained by specializing to the chosen left duals
-/

omit [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] in
/-- Helper for Lemma 12.17.2: after transporting a biproduct through tensoring on the right,
precomposing with the first inclusion is just the functorial image of that inclusion. -/
private theorem tensorRight_mapBiprod_inv_inl {A B D : C} :
    biprod.inl ≫ ((tensorRight D).mapBiprod A B).inv =
      (tensorRight D).map biprod.inl := by
  -- Expand the inverse biproduct comparison and keep the first summand.
  rw [Functor.mapBiprod_inv]
  simp

omit [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] in
/-- Helper for Lemma 12.17.2: after transporting a biproduct through tensoring on the right,
precomposing with the second inclusion is just the functorial image of that inclusion. -/
private theorem tensorRight_mapBiprod_inv_inr {A B D : C} :
    biprod.inr ≫ ((tensorRight D).mapBiprod A B).inv =
      (tensorRight D).map biprod.inr := by
  -- Expand the inverse biproduct comparison and keep the second summand.
  rw [Functor.mapBiprod_inv]
  simp

omit [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] in
/-- Helper for Lemma 12.17.2: after transporting a biproduct through tensoring on the left,
precomposing with the first inclusion is just the functorial image of that inclusion. -/
private theorem tensorLeft_mapBiprod_inv_inl {A B D : C} :
    biprod.inl ≫ ((tensorLeft D).mapBiprod A B).inv =
      (tensorLeft D).map biprod.inl := by
  -- Expand the inverse biproduct comparison and keep the first summand.
  rw [Functor.mapBiprod_inv]
  simp

omit [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] in
/-- Helper for Lemma 12.17.2: after transporting a biproduct through tensoring on the left,
precomposing with the second inclusion is just the functorial image of that inclusion. -/
private theorem tensorLeft_mapBiprod_inv_inr {A B D : C} :
    biprod.inr ≫ ((tensorLeft D).mapBiprod A B).inv =
      (tensorLeft D).map biprod.inr := by
  -- Expand the inverse biproduct comparison and keep the second summand.
  rw [Functor.mapBiprod_inv]
  simp

omit [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] in
/-- Helper for Lemma 12.17.2: after transporting a biproduct through tensoring on the right,
postcomposing with the first projection is just the functorial image of that projection. -/
private theorem tensorRight_mapBiprod_hom_fst {A B D : C} :
    ((tensorRight D).mapBiprod A B).hom ≫ biprod.fst =
      (tensorRight D).map biprod.fst := by
  -- Expand the forward biproduct comparison and project to the first summand.
  rw [Functor.mapBiprod_hom]
  simp

omit [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] in
/-- Helper for Lemma 12.17.2: after transporting a biproduct through tensoring on the right,
postcomposing with the second projection is just the functorial image of that projection. -/
private theorem tensorRight_mapBiprod_hom_snd {A B D : C} :
    ((tensorRight D).mapBiprod A B).hom ≫ biprod.snd =
      (tensorRight D).map biprod.snd := by
  -- Expand the forward biproduct comparison and project to the second summand.
  rw [Functor.mapBiprod_hom]
  simp

omit [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] in
/-- Helper for Lemma 12.17.2: after transporting a biproduct through tensoring on the left,
postcomposing with the first projection is just the functorial image of that projection. -/
private theorem tensorLeft_mapBiprod_hom_fst {A B D : C} :
    ((tensorLeft D).mapBiprod A B).hom ≫ biprod.fst =
      (tensorLeft D).map biprod.fst := by
  -- Expand the forward biproduct comparison and project to the first summand.
  rw [Functor.mapBiprod_hom]
  simp

omit [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] in
/-- Helper for Lemma 12.17.2: after transporting a biproduct through tensoring on the left,
postcomposing with the second projection is just the functorial image of that projection. -/
private theorem tensorLeft_mapBiprod_hom_snd {A B D : C} :
    ((tensorLeft D).mapBiprod A B).hom ≫ biprod.snd =
      (tensorLeft D).map biprod.snd := by
  -- Expand the forward biproduct comparison and project to the second summand.
  rw [Functor.mapBiprod_hom]
  simp

/-- Helper for Lemma 12.17.2: tensoring on the left preserves the identity on the first biproduct
branch. -/
private theorem tensorLeft_map_inl_fst {A B D : C} :
    (tensorLeft D).map (biprod.inl : A ⟶ A ⊞ B) ≫ (tensorLeft D).map biprod.fst = 𝟙 (D ⊗ A) := by
  -- Functoriality reduces the composite to the image of `biprod.inl ≫ biprod.fst = 𝟙`.
  calc
    (tensorLeft D).map (biprod.inl : A ⟶ A ⊞ B) ≫ (tensorLeft D).map biprod.fst
        = (tensorLeft D).map ((biprod.inl : A ⟶ A ⊞ B) ≫ biprod.fst) := by
            rw [← Functor.map_comp]
    _ = 𝟙 (D ⊗ A) := by simp

/-- Helper for Lemma 12.17.2: tensoring on the left preserves the vanishing of the off-diagonal
first-projection branch. -/
private theorem tensorLeft_map_inr_fst {A B D : C} :
    (tensorLeft D).map (biprod.inr : B ⟶ A ⊞ B) ≫ (tensorLeft D).map biprod.fst = 0 := by
  -- Functoriality reduces the composite to the image of `biprod.inr ≫ biprod.fst = 0`.
  calc
    (tensorLeft D).map (biprod.inr : B ⟶ A ⊞ B) ≫ (tensorLeft D).map biprod.fst
        = (tensorLeft D).map ((biprod.inr : B ⟶ A ⊞ B) ≫ biprod.fst) := by
            rw [← Functor.map_comp]
    _ = (tensorLeft D).map (0 : B ⟶ A) := by simp
    _ = 0 := by simpa using (Functor.map_zero (tensorLeft D) B A)

/-- Helper for Lemma 12.17.2: tensoring on the left preserves the vanishing of the off-diagonal
second-projection branch. -/
private theorem tensorLeft_map_inl_snd {A B D : C} :
    (tensorLeft D).map (biprod.inl : A ⟶ A ⊞ B) ≫ (tensorLeft D).map biprod.snd = 0 := by
  -- Functoriality reduces the composite to the image of `biprod.inl ≫ biprod.snd = 0`.
  calc
    (tensorLeft D).map (biprod.inl : A ⟶ A ⊞ B) ≫ (tensorLeft D).map biprod.snd
        = (tensorLeft D).map ((biprod.inl : A ⟶ A ⊞ B) ≫ biprod.snd) := by
            rw [← Functor.map_comp]
    _ = (tensorLeft D).map (0 : A ⟶ B) := by simp
    _ = 0 := by simpa using (Functor.map_zero (tensorLeft D) A B)

/-- Helper for Lemma 12.17.2: tensoring on the left preserves the identity on the second biproduct
branch. -/
private theorem tensorLeft_map_inr_snd {A B D : C} :
    (tensorLeft D).map (biprod.inr : B ⟶ A ⊞ B) ≫ (tensorLeft D).map biprod.snd = 𝟙 (D ⊗ B) := by
  -- Functoriality reduces the composite to the image of `biprod.inr ≫ biprod.snd = 𝟙`.
  calc
    (tensorLeft D).map (biprod.inr : B ⟶ A ⊞ B) ≫ (tensorLeft D).map biprod.snd
        = (tensorLeft D).map ((biprod.inr : B ⟶ A ⊞ B) ≫ biprod.snd) := by
            rw [← Functor.map_comp]
    _ = 𝟙 (D ⊗ B) := by simp

/-- Helper for Lemma 12.17.2: the source proof works with the explicit pointwise biproduct of the
two tensor-right functors, so we package that functor directly instead of using the chosen
functor-category biproduct object. -/
private noncomputable def pointwiseTensorRightBiprod (A B : C) : C ⥤ C where
  obj Z := (Z ⊗ A) ⊞ (Z ⊗ B)
  map f := biprod.map (f ▷ A) (f ▷ B)
  map_id Z := by
    -- Compare the two candidate identities after postcomposing with the biproduct projections.
    apply biprod.hom_ext
    · simp
    · simp
  map_comp f g := by
    -- The pointwise biproduct map is componentwise functorial in the two summands.
    apply biprod.hom_ext
    · simp [Category.assoc]
    · simp [Category.assoc]

/-- Helper for Lemma 12.17.2: the left-tensor biproduct comparison is natural in the tensoring
object. -/
private theorem tensorLeft_mapBiprod_naturality {A B Z W : C} (f : Z ⟶ W) :
    (f ▷ (A ⊞ B)) ≫ ((tensorLeft W).mapBiprod A B).hom =
      ((tensorLeft Z).mapBiprod A B).hom ≫ biprod.map (f ▷ A) (f ▷ B) := by
  -- Compare the two candidate maps after projecting to the two biproduct summands.
  apply biprod.hom_ext
  · calc
      ((f ▷ (A ⊞ B)) ≫ ((tensorLeft W).mapBiprod A B).hom) ≫ biprod.fst
          = (f ▷ (A ⊞ B)) ≫ (tensorLeft W).map biprod.fst := by
              simp [Category.assoc]
      _ = (tensorLeft Z).map biprod.fst ≫ (f ▷ A) := by
            simpa using
              (MonoidalCategory.whisker_exchange_assoc f biprod.fst (𝟙 (W ⊗ A))).symm
      _ = (((tensorLeft Z).mapBiprod A B).hom ≫ biprod.map (f ▷ A) (f ▷ B)) ≫ biprod.fst := by
            simp [Category.assoc, biprod.map_fst]
  · calc
      ((f ▷ (A ⊞ B)) ≫ ((tensorLeft W).mapBiprod A B).hom) ≫ biprod.snd
          = (f ▷ (A ⊞ B)) ≫ (tensorLeft W).map biprod.snd := by
              simp [Category.assoc]
      _ = (tensorLeft Z).map biprod.snd ≫ (f ▷ B) := by
            simpa using
              (MonoidalCategory.whisker_exchange_assoc f biprod.snd (𝟙 (W ⊗ B))).symm
      _ = (((tensorLeft Z).mapBiprod A B).hom ≫ biprod.map (f ▷ A) (f ▷ B)) ≫ biprod.snd := by
            simp [Category.assoc, biprod.map_snd]

/-- Helper for Lemma 12.17.2: the remaining step for the comparison isomorphism is a transport
normalization through the explicit biproduct comparison of `tensorLeft`. -/
private theorem nonempty_tensorRight_biprod_iso (A B : C) :
    Nonempty (tensorRight (A ⊞ B) ≅ pointwiseTensorRightBiprod A B) := by
  -- Route correction: keep the Remark 4.43.7 adjunction route and make the comparison isomorphism
  -- explicit on the `.hom` side, where the biproduct projection formulas normalize cleanly.
  refine ⟨NatIso.ofComponents (fun Z ↦ (tensorLeft Z).mapBiprod A B) ?_⟩
  -- Naturality is exactly the left-tensor transport identity proved above.
  intro Z W f
  exact tensorLeft_mapBiprod_naturality (A := A) (B := B) f

/-- Helper for Lemma 12.17.2: tensoring on the right by a biproduct is canonically isomorphic to
the explicit pointwise biproduct of the two tensor-right functors. -/
private noncomputable def tensorRightBiprodIso (A B : C) :
    tensorRight (A ⊞ B) ≅ pointwiseTensorRightBiprod A B :=
  NatIso.ofComponents (fun Z ↦ (tensorLeft Z).mapBiprod A B)
    (fun {Z W} f ↦ tensorLeft_mapBiprod_naturality (A := A) (B := B) (Z := Z) (W := W) f)

/-- Helper for Lemma 12.17.2: the pointwise biproduct adjunction is the direct-sum packaging of
the two input tensor-right adjunctions. -/
private noncomputable def pointwise_tensorRight_biprod_forward {Z W : C}
    (h : ((Z ⊗ X₁) ⊞ (Z ⊗ X₂) ⟶ W)) : Z ⟶ (W ⊗ Y₁) ⊞ (W ⊗ Y₂) :=
  biprod.lift
    ((tensorRightAdjunction X₁ Y₁).homEquiv Z W (biprod.inl ≫ h))
    ((tensorRightAdjunction X₂ Y₂).homEquiv Z W (biprod.inr ≫ h))

/-- Helper for Lemma 12.17.2: the inverse transpose for the pointwise biproduct Hom-equivalence
is computed by descending from the two component inverse transposes. -/
private noncomputable def pointwise_tensorRight_biprod_backward {Z W : C}
    (h : Z ⟶ (W ⊗ Y₁) ⊞ (W ⊗ Y₂)) : ((Z ⊗ X₁) ⊞ (Z ⊗ X₂) ⟶ W) :=
  biprod.desc
    (((tensorRightAdjunction X₁ Y₁).homEquiv Z W).symm (h ≫ biprod.fst))
    (((tensorRightAdjunction X₂ Y₂).homEquiv Z W).symm (h ≫ biprod.snd))

/-- Helper for Lemma 12.17.2: the pointwise forward and backward transposes are inverse on maps
out of the source biproduct. -/
private theorem pointwise_tensorRight_biprod_left_inv {Z W : C}
    (h : ((Z ⊗ X₁) ⊞ (Z ⊗ X₂) ⟶ W)) :
    pointwise_tensorRight_biprod_backward
        (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)
        (pointwise_tensorRight_biprod_forward
          (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂) h) =
      h := by
  -- Precompose with the two biproduct inclusions and reduce each branch by `apply_symm_apply`.
  apply biprod.hom_ext'
  · simpa [pointwise_tensorRight_biprod_backward, pointwise_tensorRight_biprod_forward] using
      (((tensorRightAdjunction X₁ Y₁).homEquiv Z W).symm_apply_apply (biprod.inl ≫ h))
  · simpa [pointwise_tensorRight_biprod_backward, pointwise_tensorRight_biprod_forward] using
      (((tensorRightAdjunction X₂ Y₂).homEquiv Z W).symm_apply_apply (biprod.inr ≫ h))

/-- Helper for Lemma 12.17.2: the pointwise forward and backward transposes are inverse on maps
into the target biproduct. -/
private theorem pointwise_tensorRight_biprod_right_inv {Z W : C}
    (h : Z ⟶ (W ⊗ Y₁) ⊞ (W ⊗ Y₂)) :
    pointwise_tensorRight_biprod_forward
        (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)
        (pointwise_tensorRight_biprod_backward
          (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂) h) =
      h := by
  -- Postcompose with the two biproduct projections and reduce each branch by `symm_apply_apply`.
  apply biprod.hom_ext
  · simpa [pointwise_tensorRight_biprod_backward, pointwise_tensorRight_biprod_forward] using
      (((tensorRightAdjunction X₁ Y₁).homEquiv Z W).apply_symm_apply (h ≫ biprod.fst))
  · simpa [pointwise_tensorRight_biprod_backward, pointwise_tensorRight_biprod_forward] using
      (((tensorRightAdjunction X₂ Y₂).homEquiv Z W).apply_symm_apply (h ≫ biprod.snd))

/-- Helper for Lemma 12.17.2: the inverse transpose for the pointwise biproduct Hom-equivalence
is natural in the source variable. -/
private theorem pointwise_tensorRight_biprod_homEquiv_naturality_left_symm {Z' Z W : C}
    (f : Z' ⟶ Z) (g : Z ⟶ (W ⊗ Y₁) ⊞ (W ⊗ Y₂)) :
    pointwise_tensorRight_biprod_backward
        (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂) (f ≫ g) =
      biprod.map (f ▷ X₁) (f ▷ X₂) ≫
        pointwise_tensorRight_biprod_backward
          (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂) g := by
  -- Compare the two candidate morphisms after restricting to the two source summands.
  apply biprod.hom_ext'
  · simpa [pointwise_tensorRight_biprod_backward, Category.assoc] using
      (Adjunction.homEquiv_naturality_left_symm (tensorRightAdjunction X₁ Y₁) f
        (g ≫ biprod.fst))
  · simpa [pointwise_tensorRight_biprod_backward, Category.assoc] using
      (Adjunction.homEquiv_naturality_left_symm (tensorRightAdjunction X₂ Y₂) f
        (g ≫ biprod.snd))

/-- Helper for Lemma 12.17.2: the forward transpose for the pointwise biproduct Hom-equivalence
is natural in the target variable. -/
private theorem pointwise_tensorRight_biprod_homEquiv_naturality_right {Z W W' : C}
    (g : ((Z ⊗ X₁) ⊞ (Z ⊗ X₂) ⟶ W)) (f : W ⟶ W') :
    pointwise_tensorRight_biprod_forward
        (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂) (g ≫ f) =
      pointwise_tensorRight_biprod_forward
          (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂) g ≫
        biprod.map (f ▷ Y₁) (f ▷ Y₂) := by
  -- Compare the two candidate morphisms after projecting to the two target summands.
  apply biprod.hom_ext
  · simpa [pointwise_tensorRight_biprod_forward, Category.assoc] using
      (Adjunction.homEquiv_naturality_right (tensorRightAdjunction X₁ Y₁)
        (biprod.inl ≫ g) f)
  · simpa [pointwise_tensorRight_biprod_forward, Category.assoc] using
      (Adjunction.homEquiv_naturality_right (tensorRightAdjunction X₂ Y₂)
        (biprod.inr ≫ g) f)

/-- Helper for Lemma 12.17.2: the pointwise biproduct Hom-equivalence obtained by packaging the
two component tensor-right Hom-equivalences. -/
private noncomputable def pointwise_tensorRight_biprod_homEquiv (Z W : C) :
    (((pointwiseTensorRightBiprod X₁ X₂).obj Z) ⟶ W) ≃
      (Z ⟶ (pointwiseTensorRightBiprod Y₁ Y₂).obj W) where
  toFun := pointwise_tensorRight_biprod_forward
    (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)
  invFun := pointwise_tensorRight_biprod_backward
    (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)
  left_inv := pointwise_tensorRight_biprod_left_inv
    (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂) (Z := Z) (W := W)
  right_inv := pointwise_tensorRight_biprod_right_inv
    (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂) (Z := Z) (W := W)

/-- Helper for Lemma 12.17.2: the core Hom-equivalence data for the pointwise biproduct
adjunction. -/
private noncomputable def pointwise_tensorRight_biprod_core :
    Adjunction.CoreHomEquiv (pointwiseTensorRightBiprod X₁ X₂)
      (pointwiseTensorRightBiprod Y₁ Y₂) where
  homEquiv := pointwise_tensorRight_biprod_homEquiv
    (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)
  homEquiv_naturality_left_symm := pointwise_tensorRight_biprod_homEquiv_naturality_left_symm
    (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)
  homEquiv_naturality_right := pointwise_tensorRight_biprod_homEquiv_naturality_right
    (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)

private theorem nonempty_tensorRight_biprod_adjunction_pointwise :
    Nonempty (pointwiseTensorRightBiprod X₁ X₂ ⊣ pointwiseTensorRightBiprod Y₁ Y₂) := by
  -- Package the explicit pointwise Hom-equivalence as an adjunction.
  exact ⟨Adjunction.mkOfHomEquiv
    (pointwise_tensorRight_biprod_core
      (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂))⟩

/-- Helper for Lemma 12.17.2: the pointwise biproduct of the two tensor-right adjunctions. -/
private noncomputable def tensorRightBiprodAdjunctionPointwise :
    pointwiseTensorRightBiprod X₁ X₂ ⊣ pointwiseTensorRightBiprod Y₁ Y₂ :=
  Adjunction.mkOfHomEquiv
    (pointwise_tensorRight_biprod_core
      (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂))

/-- Helper for Lemma 12.17.2: transport the explicit pointwise biproduct adjunction back to the
actual tensor-right functors of `X₁ ⊞ X₂` and `Y₁ ⊞ Y₂`. -/
private noncomputable def tensorRightBiprodAdjunction :
    tensorRight X ⊣ tensorRight Y :=
  (tensorRightBiprodAdjunctionPointwise
      (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)).ofNatIsoLeft
    (tensorRightBiprodIso X₁ X₂).symm |>.ofNatIsoRight (tensorRightBiprodIso Y₁ Y₂).symm

/-- Helper for Lemma 12.17.2: this is the compatibility condition from Remark 4.43.7, kept local
because the compiled remark artifact is not available in the current proof environment. -/
private def compatible_with_left_tensoring {A B : C} (adj : tensorRight A ⊣ tensorRight B) : Prop :=
  adj.CompatibleWithLeftTensoring

/-- Helper for Lemma 12.17.2: a tensor-right adjunction compatible with left tensoring recovers
the corresponding exact pairing. -/
private theorem nonempty_exactPairingOfCompatibleTensorRightAdjunction {A B : C}
    (adj : tensorRight A ⊣ tensorRight B) (hcompat : compatible_with_left_tensoring adj) :
    Nonempty (ExactPairing A B) := by
  -- The imported Remark 4.43.7 reconstruction applies verbatim to the local compatibility alias.
  exact ⟨adj.toExactPairing hcompat⟩

/-- Helper for Lemma 12.17.2: transporting an adjunction across a left natural isomorphism
precomposes the source morphism in the induced Hom-equivalence. -/
private theorem ofNatIsoLeft_homEquiv_apply {D : Type*} [Category D]
    {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) {Z : C} {W : D}
    (g : G.obj Z ⟶ W) :
    ((adj.ofNatIsoLeft iso).homEquiv Z W) g =
      adj.homEquiv Z W (iso.hom.app Z ≫ g) := by
  -- Expand the transported unit and regroup the functorial image into the original Hom-equivalence.
  simp [Adjunction.homEquiv, Adjunction.ofNatIsoLeft, Category.assoc]

/-- Helper for Lemma 12.17.2: transporting an adjunction across a right natural isomorphism
postcomposes the target morphism in the induced Hom-equivalence. -/
private theorem ofNatIsoRight_homEquiv_apply {D : Type*} [Category D]
    {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) {Z : C} {W : D}
    (g : F.obj Z ⟶ W) :
    ((adj.ofNatIsoRight iso).homEquiv Z W) g =
      adj.homEquiv Z W g ≫ iso.hom.app W := by
  -- Expand the transported unit and use naturality of the right comparison isomorphism.
  simp [Adjunction.homEquiv, Adjunction.ofNatIsoRight, Category.assoc]

namespace Adjunction

/-- Helper for Lemma 12.17.2: the adjunction built from `CoreHomEquiv` uses exactly the supplied
Hom-equivalence on each pair of objects. -/
theorem mkOfHomEquiv_homEquiv_apply {D : Type*} [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (core : Adjunction.CoreHomEquiv F G)
    {Z : C} {W : D} (g : F.obj Z ⟶ W) :
    ((Adjunction.mkOfHomEquiv core).homEquiv Z W) g = core.homEquiv Z W g := by
  -- `mkOfHomEquiv` packages the given bijection without changing its objectwise action.
  simpa using (core.homEquiv_naturality_right (𝟙 (F.obj Z)) g).symm

end Adjunction

/-- Helper for Lemma 12.17.2: the transported biproduct adjunction acts on Hom-sets by first
moving the source map into the pointwise biproduct model and then transporting the target back out
through the right comparison isomorphism. -/
private theorem tensorRight_biprod_adjunction_homEquiv_apply {Z W : C}
    (g : Z ⊗ X ⟶ W) :
    ((tensorRightBiprodAdjunction (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)).homEquiv Z W) g =
      pointwise_tensorRight_biprod_forward
          (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)
          (((tensorLeft Z).mapBiprod X₁ X₂).inv ≫ g) ≫
        ((tensorLeft W).mapBiprod Y₁ Y₂).inv := by
  -- Unfold the two natural-isomorphism transports and then expose the chosen pointwise
  -- Hom-equivalence.
  rw [tensorRightBiprodAdjunction]
  rw [ofNatIsoRight_homEquiv_apply, ofNatIsoLeft_homEquiv_apply]
  rw [tensorRightBiprodAdjunctionPointwise]
  rw [Adjunction.mkOfHomEquiv_homEquiv_apply]
  rfl

/-- Helper for Lemma 12.17.2: precomposing the transported source map with the first biproduct
inclusion isolates the `X₁` branch after the associator. -/
private theorem tensorLeft_mapBiprod_inv_associator_whisker_inl {W Z Z' : C}
    (f : Z' ⊗ X ⟶ Z) :
    biprod.inl ≫ ((tensorLeft (W ⊗ Z')).mapBiprod X₁ X₂).inv ≫
        (α_ W Z' X).hom ≫ W ◁ f =
      (α_ W Z' X₁).hom ≫
        W ◁ (biprod.inl ≫ ((tensorLeft Z').mapBiprod X₁ X₂).inv ≫ f) := by
  -- Reduce the transported inclusion to the functorial image of `biprod.inl`, then use
  -- associator naturality to move it across the left whiskering.
  calc
    biprod.inl ≫ ((tensorLeft (W ⊗ Z')).mapBiprod X₁ X₂).inv ≫
        (α_ W Z' X).hom ≫ W ◁ f
        =
          (tensorLeft (W ⊗ Z')).map biprod.inl ≫
            (α_ W Z' X).hom ≫ W ◁ f := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫ (α_ W Z' X).hom ≫ W ◁ f)
                  (tensorLeft_mapBiprod_inv_inl (A := X₁) (B := X₂) (D := W ⊗ Z'))
    _ = (α_ W Z' X₁).hom ≫
          W ◁ ((tensorLeft Z').map biprod.inl) ≫ W ◁ f := by
            have h :
                (tensorLeft (W ⊗ Z')).map biprod.inl ≫
                    (α_ W Z' X).hom ≫ W ◁ f =
                  (α_ W Z' X₁).hom ≫
                    W ◁ ((tensorLeft Z').map biprod.inl) ≫ W ◁ f := by
              simpa using
                (MonoidalCategory.associator_naturality_assoc
                  (𝟙 W) (𝟙 Z') biprod.inl (W ◁ f))
            exact h
    _ = (α_ W Z' X₁).hom ≫
          W ◁ (biprod.inl ≫ ((tensorLeft Z').mapBiprod X₁ X₂).inv ≫ f) := by
            symm
            simpa [Functor.map_comp, Category.assoc] using
              congrArg
                (fun k ↦ (α_ W Z' X₁).hom ≫ W ◁ (k ≫ f))
                (tensorLeft_mapBiprod_inv_inl (A := X₁) (B := X₂) (D := Z'))

/-- Helper for Lemma 12.17.2: precomposing the transported source map with the second biproduct
inclusion isolates the `X₂` branch after the associator. -/
private theorem tensorLeft_mapBiprod_inv_associator_whisker_inr {W Z Z' : C}
    (f : Z' ⊗ X ⟶ Z) :
    biprod.inr ≫ ((tensorLeft (W ⊗ Z')).mapBiprod X₁ X₂).inv ≫
        (α_ W Z' X).hom ≫ W ◁ f =
      (α_ W Z' X₂).hom ≫
        W ◁ (biprod.inr ≫ ((tensorLeft Z').mapBiprod X₁ X₂).inv ≫ f) := by
  -- Reduce the transported inclusion to the functorial image of `biprod.inr`, then use
  -- associator naturality to move it across the left whiskering.
  calc
    biprod.inr ≫ ((tensorLeft (W ⊗ Z')).mapBiprod X₁ X₂).inv ≫
        (α_ W Z' X).hom ≫ W ◁ f
        =
          (tensorLeft (W ⊗ Z')).map biprod.inr ≫
            (α_ W Z' X).hom ≫ W ◁ f := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫ (α_ W Z' X).hom ≫ W ◁ f)
                  (tensorLeft_mapBiprod_inv_inr (A := X₁) (B := X₂) (D := W ⊗ Z'))
    _ = (α_ W Z' X₂).hom ≫
          W ◁ ((tensorLeft Z').map biprod.inr) ≫ W ◁ f := by
            have h :
                (tensorLeft (W ⊗ Z')).map biprod.inr ≫
                    (α_ W Z' X).hom ≫ W ◁ f =
                  (α_ W Z' X₂).hom ≫
                    W ◁ ((tensorLeft Z').map biprod.inr) ≫ W ◁ f := by
              simpa using
                (MonoidalCategory.associator_naturality_assoc
                  (𝟙 W) (𝟙 Z') biprod.inr (W ◁ f))
            exact h
    _ = (α_ W Z' X₂).hom ≫
          W ◁ (biprod.inr ≫ ((tensorLeft Z').mapBiprod X₁ X₂).inv ≫ f) := by
            symm
            simpa [Functor.map_comp, Category.assoc] using
              congrArg
                (fun k ↦ (α_ W Z' X₂).hom ≫ W ◁ (k ≫ f))
                (tensorLeft_mapBiprod_inv_inr (A := X₁) (B := X₂) (D := Z'))

/-- Helper for Lemma 12.17.2: precomposing the transported `Y`-side comparison with the first
outer source inclusion collapses the outer biproduct transport. -/
private theorem tensorLeft_mapBiprod_inv_outer_inl_inner_inv {W Z : C} :
    biprod.inl ≫ ((tensorLeft W).mapBiprod (Z ⊗ Y₁) (Z ⊗ Y₂)).inv ≫
        W ◁ ((tensorLeft Z).mapBiprod Y₁ Y₂).inv =
      (tensorLeft W).map biprod.inl ≫ W ◁ ((tensorLeft Z).mapBiprod Y₁ Y₂).inv := by
  -- This is the first stable prefix in the branchwise normalization.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ k ≫ W ◁ ((tensorLeft Z).mapBiprod Y₁ Y₂).inv)
      (tensorLeft_mapBiprod_inv_inl (A := Z ⊗ Y₁) (B := Z ⊗ Y₂) (D := W))

/-- Helper for Lemma 12.17.2: precomposing the transported `Y`-side comparison with the second
outer source inclusion collapses the outer biproduct transport. -/
private theorem tensorLeft_mapBiprod_inv_outer_inr_inner_inv {W Z : C} :
    biprod.inr ≫ ((tensorLeft W).mapBiprod (Z ⊗ Y₁) (Z ⊗ Y₂)).inv ≫
        W ◁ ((tensorLeft Z).mapBiprod Y₁ Y₂).inv =
      (tensorLeft W).map biprod.inr ≫ W ◁ ((tensorLeft Z).mapBiprod Y₁ Y₂).inv := by
  -- This is the symmetric stable prefix for the second source summand.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ k ≫ W ◁ ((tensorLeft Z).mapBiprod Y₁ Y₂).inv)
      (tensorLeft_mapBiprod_inv_inr (A := Z ⊗ Y₁) (B := Z ⊗ Y₂) (D := W))

/-- Helper for Lemma 12.17.2: after postcomposing the transported right-hand side with the first
biproduct projection, only the `Y₁` branch remains. -/
private theorem tensorLeft_mapBiprod_inv_associator_postcompose_fst {W Z : C} :
    W ◁ ((tensorLeft Z).mapBiprod Y₁ Y₂).inv ≫
        (α_ W Z Y).inv ≫
        ((tensorLeft (W ⊗ Z)).mapBiprod Y₁ Y₂).hom ≫
        biprod.fst =
      W ◁ biprod.fst ≫ (α_ W Z Y₁).inv := by
  -- TODO: combine the two proved branch normalizations above with the corresponding precomposed
  -- right-hand side reductions after `cancel_epi ((tensorLeft W).mapBiprod ...).inv`.
  sorry

/-- Helper for Lemma 12.17.2: after postcomposing the transported right-hand side with the second
biproduct projection, only the `Y₂` branch remains. -/
private theorem tensorLeft_mapBiprod_inv_associator_postcompose_snd {W Z : C} :
    W ◁ ((tensorLeft Z).mapBiprod Y₁ Y₂).inv ≫
        (α_ W Z Y).inv ≫
        ((tensorLeft (W ⊗ Z)).mapBiprod Y₁ Y₂).hom ≫
        biprod.snd =
      W ◁ biprod.snd ≫ (α_ W Z Y₂).inv := by
  -- TODO: combine the two symmetric branch normalizations above with the precomposed right-hand
  -- side reductions after cancelling the left biproduct comparison.
  sorry

/-- Helper for Lemma 12.17.2: after postcomposing the transported right-hand side with the first
biproduct projection, only the `Y₁` branch remains. -/
private theorem tensorRight_biprod_postcompose_fst {W Z Z' : C}
    (f : Z' ⊗ X ⟶ Z) :
    (W ◁
          (pointwise_tensorRight_biprod_forward
              (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)
              (((tensorLeft Z').mapBiprod X₁ X₂).inv ≫ f) ≫
            ((tensorLeft Z).mapBiprod Y₁ Y₂).inv) ≫
        (α_ W Z Y).inv ≫
        ((tensorLeft (W ⊗ Z)).mapBiprod Y₁ Y₂).hom ≫
        biprod.fst) =
      W ◁ ((tensorRightAdjunction X₁ Y₁).homEquiv Z' Z
          (biprod.inl ≫ ((tensorLeft Z').mapBiprod X₁ X₂).inv ≫ f)) ≫
        (α_ W Z Y₁).inv := by
  let pf :=
    pointwise_tensorRight_biprod_forward
      (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)
      (((tensorLeft Z').mapBiprod X₁ X₂).inv ≫ f)
  -- First isolate the `Y`-side transport from the left whiskering of the forward map.
  calc
    (W ◁
          (pf ≫ ((tensorLeft Z).mapBiprod Y₁ Y₂).inv) ≫
        (α_ W Z Y).inv ≫
        ((tensorLeft (W ⊗ Z)).mapBiprod Y₁ Y₂).hom ≫
        biprod.fst)
        = (W ◁ pf) ≫
            (W ◁ ((tensorLeft Z).mapBiprod Y₁ Y₂).inv ≫
              (α_ W Z Y).inv ≫
              ((tensorLeft (W ⊗ Z)).mapBiprod Y₁ Y₂).hom ≫ biprod.fst) := by
                simp [pf, Functor.map_comp, Category.assoc]
    -- Replace the transported `Y`-side comparison by the first branch projection.
    _ = (W ◁ pf) ≫ (W ◁ biprod.fst ≫ (α_ W Z Y₁).inv) := by
          exact congrArg
            (fun k ↦ (W ◁ pf) ≫ k)
            (tensorLeft_mapBiprod_inv_associator_postcompose_fst (W := W) (Z := Z))
    -- Combine the two whiskerings and project the explicit biproduct lift to its first summand.
    _ = (W ◁ (pf ≫ biprod.fst)) ≫ (α_ W Z Y₁).inv := by
          simp [Functor.map_comp, Category.assoc]
    _ =
        W ◁ ((tensorRightAdjunction X₁ Y₁).homEquiv Z' Z
            (biprod.inl ≫ ((tensorLeft Z').mapBiprod X₁ X₂).inv ≫ f)) ≫
          (α_ W Z Y₁).inv := by
            simp [pf, pointwise_tensorRight_biprod_forward]

/-- Helper for Lemma 12.17.2: after postcomposing the transported right-hand side with the second
biproduct projection, only the `Y₂` branch remains. -/
private theorem tensorRight_biprod_postcompose_snd {W Z Z' : C}
    (f : Z' ⊗ X ⟶ Z) :
    (W ◁
          (pointwise_tensorRight_biprod_forward
              (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)
              (((tensorLeft Z').mapBiprod X₁ X₂).inv ≫ f) ≫
            ((tensorLeft Z).mapBiprod Y₁ Y₂).inv) ≫
        (α_ W Z Y).inv ≫
        ((tensorLeft (W ⊗ Z)).mapBiprod Y₁ Y₂).hom ≫
        biprod.snd) =
      W ◁ ((tensorRightAdjunction X₂ Y₂).homEquiv Z' Z
          (biprod.inr ≫ ((tensorLeft Z').mapBiprod X₁ X₂).inv ≫ f)) ≫
        (α_ W Z Y₂).inv := by
  let pf :=
    pointwise_tensorRight_biprod_forward
      (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)
      (((tensorLeft Z').mapBiprod X₁ X₂).inv ≫ f)
  -- First isolate the `Y`-side transport from the left whiskering of the forward map.
  calc
    (W ◁
          (pf ≫ ((tensorLeft Z).mapBiprod Y₁ Y₂).inv) ≫
        (α_ W Z Y).inv ≫
        ((tensorLeft (W ⊗ Z)).mapBiprod Y₁ Y₂).hom ≫
        biprod.snd)
        = (W ◁ pf) ≫
            (W ◁ ((tensorLeft Z).mapBiprod Y₁ Y₂).inv ≫
              (α_ W Z Y).inv ≫
              ((tensorLeft (W ⊗ Z)).mapBiprod Y₁ Y₂).hom ≫ biprod.snd) := by
                simp [pf, Functor.map_comp, Category.assoc]
    -- Replace the transported `Y`-side comparison by the second branch projection.
    _ = (W ◁ pf) ≫ (W ◁ biprod.snd ≫ (α_ W Z Y₂).inv) := by
          exact congrArg
            (fun k ↦ (W ◁ pf) ≫ k)
            (tensorLeft_mapBiprod_inv_associator_postcompose_snd (W := W) (Z := Z))
    -- Combine the two whiskerings and project the explicit biproduct lift to its second summand.
    _ = (W ◁ (pf ≫ biprod.snd)) ≫ (α_ W Z Y₂).inv := by
          simp [Functor.map_comp, Category.assoc]
    _ =
        W ◁ ((tensorRightAdjunction X₂ Y₂).homEquiv Z' Z
            (biprod.inr ≫ ((tensorLeft Z').mapBiprod X₁ X₂).inv ≫ f)) ≫
          (α_ W Z Y₂).inv := by
            simp [pf, pointwise_tensorRight_biprod_forward]

/-- Helper for Lemma 12.17.2: the only remaining source-faithful step is to identify the
transported biproduct adjunction with the standard compatibility condition from Remark 4.43.7. -/
private theorem tensorRight_biprod_adjunction_compatible :
    compatible_with_left_tensoring
      (tensorRightBiprodAdjunction (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂)) := by
  -- Route correction: the main skeleton is fixed, but the final closure still needs the two
  -- `tensorLeft_mapBiprod_inv_associator_postcompose_*` transport normalizations to reduce the
  -- branchwise postcomposition to the component compatibility theorems.
  -- TODO: after rewriting with `tensorRight_biprod_adjunction_homEquiv_apply`, cancel the final
  -- right biproduct comparison, apply `biprod.hom_ext`, and close the two branches by combining
  -- the component compatibilities with the off-diagonal vanishing terms.
  sorry

namespace ExactPairing

/-- If `X₁ ⊣ Y₁` and `X₂ ⊣ Y₂`, then their binary direct sums again form an exact pairing. -/
instance biprod : ExactPairing X Y :=
  Classical.choice <|
    nonempty_exactPairingOfCompatibleTensorRightAdjunction
      (tensorRightBiprodAdjunction (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂))
      (tensorRight_biprod_adjunction_compatible
        (X₁ := X₁) (X₂ := X₂) (Y₁ := Y₁) (Y₂ := Y₂))

end ExactPairing

namespace HasLeftDual

/-- If two objects have chosen left duals, then their direct sum has the direct sum of those
chosen left duals as a chosen left dual. -/
instance biprod {A B : C} [HasLeftDual A] [HasLeftDual B] : HasLeftDual (A ⊞ B) where
  leftDual := (ᘁA : C) ⊞ (ᘁB : C)
  exact := inferInstance

end HasLeftDual

end CategoryTheory
