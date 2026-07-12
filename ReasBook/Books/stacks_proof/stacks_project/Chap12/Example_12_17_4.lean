import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GradedObject
open CategoryTheory.GradedObject.Monoidal
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace CategoryTheory

variable {F : Type u} [Field F]

namespace GradedObject.Monoidal

/- Source/core/bridge triage:
- `source-facing`: the Koszul-signed commutativity constraint on graded `F`-vector spaces.
- `core/canonical`: there is no exact upstream owner for the Koszul-signed braiding in
  `GradedObject ℤ (ModuleCat F)`. The canonical infrastructure this file should reuse is the graded
  tensor API `tensorObjDesc`/`ιTensorObj`, with nearby domain samples
  `GradedObject.Monoidal.braiding`, `TensorProduct.gradedComm`, and
  `CategoryTheory.CatCenter.app_neg_one_zpow`.
- `bridge/view`: the summandwise restriction theorem `koszulBraiding_hom_app`.

Primitive data are only the degreewise signed swaps; naturality, hexagon identities, and symmetry
are derived theorem-level API used to package the symmetric structure. -/

/-- The degreewise Koszul-signed swap on the `(p, q)`-summand of a tensor product of graded
`F`-vector spaces. -/
def koszulBraidingComponent (V W : GradedObject ℤ (ModuleCat F)) (p q : ℤ) :
    V p ⊗ W q ⟶ W q ⊗ V p :=
  ((p * q).negOnePow : F) • (β_ (V p) (W q)).hom

private abbrev koszulBraidingHom (V W : GradedObject ℤ (ModuleCat F)) :
    V ⊗ W ⟶ W ⊗ V :=
  fun n ↦
    tensorObjDesc
      (fun p q h ↦
        koszulBraidingComponent V W p q ≫
          ιTensorObj W V q p n (Eq.trans (add_comm q p) h))

/-- Helper for Example 12.17.4: restricting the descended Koszul-signed swap to a fixed
`(p, q)`-summand recovers the degreewise signed braiding component. -/
@[reassoc]
private theorem koszulBraidingHom_app
    (V W : GradedObject ℤ (ModuleCat F)) (p q n : ℤ) (h : p + q = n) :
    ιTensorObj V W p q n h ≫ koszulBraidingHom V W n =
      koszulBraidingComponent V W p q ≫
        ιTensorObj W V q p n (Eq.trans (add_comm q p) h) := by
  -- The descended map is defined by the universal property of the graded tensor sum.
  simp [koszulBraidingHom, ι_tensorObjDesc]

/-- Helper for Example 12.17.4: the field-valued Koszul sign squares to `1`. -/
private theorem field_negOnePow_mul_self (n : ℤ) :
    ((n.negOnePow : F) * (n.negOnePow : F)) = (1 : F) := by
  -- The only possibilities are the even sign `1` and the odd sign `-1`.
  rcases Int.even_or_odd n with hEven | hOdd
  · rw [Int.negOnePow_even _ hEven]
    norm_num
  · rw [Int.negOnePow_odd _ hOdd]
    norm_num

/-- Helper for Example 12.17.4: a scalar on the middle morphism of a triple composite factors
out to the front. -/
private theorem middle_smul_comp
    {A B C D : ModuleCat F} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (a : F) :
    f ≫ (a • g) ≫ h = a • (f ≫ g ≫ h) := by
  -- First expose the middle scalar on `f ≫ g`, then move it across the last composition.
  calc
    f ≫ (a • g) ≫ h = (f ≫ (a • g)) ≫ h := by
      simp [Category.assoc]
    _ = (a • (f ≫ g)) ≫ h := by
      refine congrArg (fun u ↦ u ≫ h) ?_
      exact CategoryTheory.Linear.comp_smul (R := F) (X := A) (Y := B) (Z := C) f a g
    _ = a • (f ≫ g ≫ h) := by
      exact CategoryTheory.Linear.smul_comp (R := F) (X := A) (Y := C) (Z := D) a (f ≫ g) h

/-- Helper for Example 12.17.4: scalar multiples on the outer factors of a triple composite
combine into one scalar multiple of the whole composite. -/
private theorem smul_comp_comp_smul
    {A B C D : ModuleCat F} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (a b : F) :
    (a • f) ≫ g ≫ (b • h) = (a * b) • (f ≫ g ≫ h) := by
  -- Move the left scalar through the first composition and the right scalar through the second,
  -- then combine the two scalar factors.
  calc
    (a • f) ≫ g ≫ (b • h) = a • (f ≫ (g ≫ (b • h))) := by
      exact CategoryTheory.Linear.smul_comp (R := F) (X := A) (Y := B) (Z := D) a f
        (g ≫ (b • h))
    _ = a • (b • (f ≫ g ≫ h)) := by
      refine congrArg (fun u ↦ a • u) ?_
      calc
        f ≫ (g ≫ (b • h)) = (f ≫ g) ≫ (b • h) := by
          simp [Category.assoc]
        _ = b • ((f ≫ g) ≫ h) := by
          exact CategoryTheory.Linear.comp_smul (R := F) (X := A) (Y := C) (Z := D) (f ≫ g)
            b h
        _ = b • (f ≫ g ≫ h) := by
          simp [Category.assoc]
    _ = (a * b) • (f ≫ g ≫ h) := by
      simp [smul_smul]

/-- Helper for Example 12.17.4: the two Koszul-signed component swaps on a fixed
`(p, q)`-summand compose to the identity. -/
private theorem koszulBraidingComponent_comp_id
    (V W : GradedObject ℤ (ModuleCat F)) (p q : ℤ) :
    koszulBraidingComponent V W p q ≫ koszulBraidingComponent W V q p =
      𝟙 (V p ⊗ W q) := by
  -- Route correction: normalize both signed braidings to one scalar multiple of the ordinary
  -- symmetry composite, then use symmetry plus `field_negOnePow_mul_self`.
  calc
    koszulBraidingComponent V W p q ≫ koszulBraidingComponent W V q p =
      (((p * q).negOnePow : F) * ((q * p).negOnePow : F)) •
        (((β_ (V p) (W q)).hom) ≫ (β_ (W q) (V p)).hom) := by
          rw [koszulBraidingComponent, koszulBraidingComponent]
          calc
            (((p * q).negOnePow : F) • (β_ (V p) (W q)).hom) ≫
                (((q * p).negOnePow : F) • (β_ (W q) (V p)).hom) =
              (((p * q).negOnePow : F) • (β_ (V p) (W q)).hom) ≫
                  (𝟙 (W q ⊗ V p)) ≫
                    (((q * p).negOnePow : F) • (β_ (W q) (V p)).hom) := by
                      simp
            _ = ((((p * q).negOnePow : F) * ((q * p).negOnePow : F)) •
                  (((β_ (V p) (W q)).hom) ≫ 𝟙 (W q ⊗ V p) ≫
                    ((β_ (W q) (V p)).hom))) := by
                  simpa using
                    smul_comp_comp_smul ((β_ (V p) (W q)).hom) (𝟙 (W q ⊗ V p))
                      ((β_ (W q) (V p)).hom) ((p * q).negOnePow : F)
                      ((q * p).negOnePow : F)
            _ = (((p * q).negOnePow : F) * ((q * p).negOnePow : F)) •
                  (((β_ (V p) (W q)).hom) ≫ ((β_ (W q) (V p)).hom)) := by
                  simp
    _ = (((p * q).negOnePow : F) * ((q * p).negOnePow : F)) • (𝟙 (V p ⊗ W q)) := by
      rw [SymmetricCategory.symmetry]
    _ = 𝟙 (V p ⊗ W q) := by
      rw [mul_comm q p, field_negOnePow_mul_self (p * q)]
      simp

-- Proof sketch: compute both composites degreewise. On the summand `V^p ⊗ W^q`, the two signed
-- swaps contribute the scalar `(-1)^(pq) * (-1)^(qp) = 1`, and the remaining map is the ordinary
-- symmetry of the tensor product in `ModuleCat F`, which is involutive.
private theorem koszulBraiding_hom_inv_id (V W : GradedObject ℤ (ModuleCat F)) :
    koszulBraidingHom V W ≫ koszulBraidingHom W V = 𝟙 (V ⊗ W) := by
  -- Restrict to a `(p, q)`-summand, rewrite the two descended braidings, and then collapse the
  -- middle composite with the component involutivity lemma.
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  calc
    ιTensorObj V W p q n h ≫ (koszulBraidingHom V W ≫ koszulBraidingHom W V) n =
      koszulBraidingComponent V W p q ≫
        ιTensorObj W V q p n (by simpa [add_comm] using h) ≫ koszulBraidingHom W V n := by
          simp [Category.assoc]
    _ =
      koszulBraidingComponent V W p q ≫
        koszulBraidingComponent W V q p ≫ ιTensorObj V W p q n h := by
          simpa [Category.assoc] using congrArg
            (fun u ↦ koszulBraidingComponent V W p q ≫ u)
            (koszulBraidingHom_app W V q p n (Eq.trans (add_comm q p) h))
    _ = ιTensorObj V W p q n h := by
      simpa [Category.assoc] using congrArg
        (fun u ↦ u ≫ ιTensorObj V W p q n h)
        (koszulBraidingComponent_comp_id V W p q)
    _ = ιTensorObj V W p q n h ≫ (𝟙 (V ⊗ W)) n := by
      symm
      exact Category.comp_id _

/-- The Koszul-signed braiding on graded `F`-vector spaces. -/
noncomputable def koszulBraiding (V W : GradedObject ℤ (ModuleCat F)) :
    V ⊗ W ≅ W ⊗ V where
  hom := koszulBraidingHom V W
  inv := koszulBraidingHom W V
  hom_inv_id := koszulBraiding_hom_inv_id V W
  inv_hom_id := koszulBraiding_hom_inv_id W V

/-- Helper for Example 12.17.4: on a fixed `(p, q)`-summand, left-variable naturality reduces to
ordinary braiding naturality because the Koszul sign is unchanged. -/
private theorem koszulBraidingComponent_naturality_left
    {V W X : GradedObject ℤ (ModuleCat F)} (f : V ⟶ W) (p q : ℤ) :
    (f p ⊗ₘ 𝟙 (X q)) ≫ koszulBraidingComponent W X p q =
      koszulBraidingComponent V X p q ≫ (𝟙 (X q) ⊗ₘ f p) := by
  -- The Koszul sign is unchanged, so this is ordinary braiding naturality with one scalar
  -- moved across the composite.
  calc
    (f p ⊗ₘ 𝟙 (X q)) ≫ koszulBraidingComponent W X p q =
      ((p * q).negOnePow : F) • (((f p ⊗ₘ 𝟙 (X q)) ≫ (β_ (W p) (X q)).hom)) := by
        rw [koszulBraidingComponent]
        exact CategoryTheory.Linear.comp_smul (R := F) (X := V p ⊗ X q) (Y := W p ⊗ X q)
          (Z := X q ⊗ W p) (f p ⊗ₘ 𝟙 (X q)) ((p * q).negOnePow : F)
          (β_ (W p) (X q)).hom
    _ = ((p * q).negOnePow : F) • (((β_ (V p) (X q)).hom) ≫ (𝟙 (X q) ⊗ₘ f p)) := by
      refine congrArg (fun u ↦ ((p * q).negOnePow : F) • u) ?_
      exact BraidedCategory.braiding_naturality_left (f p) (X q)
    _ = koszulBraidingComponent V X p q ≫ (𝟙 (X q) ⊗ₘ f p) := by
      rw [koszulBraidingComponent]
      exact (CategoryTheory.Linear.smul_comp (R := F) (X := V p ⊗ X q) (Y := X q ⊗ V p)
        (Z := X q ⊗ W p) ((p * q).negOnePow : F) (β_ (V p) (X q)).hom
        (𝟙 (X q) ⊗ₘ f p)).symm

/-- Helper for Example 12.17.4: on a fixed `(p, q)`-summand, right-variable naturality reduces to
ordinary braiding naturality because the Koszul sign is unchanged. -/
private theorem koszulBraidingComponent_naturality_right
    (V : GradedObject ℤ (ModuleCat F)) {W X : GradedObject ℤ (ModuleCat F)}
    (f : W ⟶ X) (p q : ℤ) :
    (𝟙 (V p) ⊗ₘ f q) ≫ koszulBraidingComponent V X p q =
      koszulBraidingComponent V W p q ≫ (f q ⊗ₘ 𝟙 (V p)) := by
  -- The right-variable case is the same scalar bookkeeping applied to right naturality.
  calc
    (𝟙 (V p) ⊗ₘ f q) ≫ koszulBraidingComponent V X p q =
      ((p * q).negOnePow : F) • (((𝟙 (V p) ⊗ₘ f q) ≫ (β_ (V p) (X q)).hom)) := by
        rw [koszulBraidingComponent]
        exact CategoryTheory.Linear.comp_smul (R := F) (X := V p ⊗ W q) (Y := V p ⊗ X q)
          (Z := X q ⊗ V p) (𝟙 (V p) ⊗ₘ f q) ((p * q).negOnePow : F)
          (β_ (V p) (X q)).hom
    _ = ((p * q).negOnePow : F) • (((β_ (V p) (W q)).hom) ≫ (f q ⊗ₘ 𝟙 (V p))) := by
      refine congrArg (fun u ↦ ((p * q).negOnePow : F) • u) ?_
      exact BraidedCategory.braiding_naturality_right (V p) (f q)
    _ = koszulBraidingComponent V W p q ≫ (f q ⊗ₘ 𝟙 (V p)) := by
      rw [koszulBraidingComponent]
      exact (CategoryTheory.Linear.smul_comp (R := F) (X := V p ⊗ W q) (Y := W q ⊗ V p)
        (Z := X q ⊗ V p) ((p * q).negOnePow : F) (β_ (V p) (W q)).hom
        (f q ⊗ₘ 𝟙 (V p))).symm

/-- Helper for Example 12.17.4: the Koszul sign is multiplicative in the right variable. -/
private theorem koszul_sign_add_right (p q r : ℤ) :
    (((p * (q + r)).negOnePow : F)) = ((p * q).negOnePow : F) * ((p * r).negOnePow : F) := by
  -- Expand the product in the exponent, split `negOnePow` over the sum, and cast the product.
  calc
    (((p * (q + r)).negOnePow : F)) = (((p * q + p * r).negOnePow : F)) := by
      congr 1
      ring_nf
    _ = ((p * q).negOnePow : F) * ((p * r).negOnePow : F) := by
      rw [Int.negOnePow_add]
      change ((↑(((p * q).negOnePow * (p * r).negOnePow : ℤ)) : F)) =
        ((p * q).negOnePow : F) * ((p * r).negOnePow : F)
      rw [Int.cast_mul]

/-- Helper for Example 12.17.4: the Koszul sign is multiplicative in the left variable. -/
private theorem koszul_sign_add_left (p q r : ℤ) :
    ((((p + q) * r).negOnePow : F)) = ((p * r).negOnePow : F) * ((q * r).negOnePow : F) := by
  -- This is the left-variable analogue of `koszul_sign_add_right`.
  calc
    ((((p + q) * r).negOnePow : F)) = (((p * r + q * r).negOnePow : F)) := by
      congr 1
      ring_nf
    _ = ((p * r).negOnePow : F) * ((q * r).negOnePow : F) := by
      rw [Int.negOnePow_add]
      change ((↑(((p * r).negOnePow * (q * r).negOnePow : ℤ)) : F)) =
        ((p * r).negOnePow : F) * ((q * r).negOnePow : F)
      rw [Int.cast_mul]

/-- Helper for Example 12.17.4: the graded associator on a fixed triple summand rewrites to the
ordinary associator on the component modules. -/
@[reassoc]
private theorem graded_associator_hom_component
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r k : ℤ) (h : p + q + r = k) :
    ιTensorObj₃' V W X p q r k h ≫ (α_ V W X).hom k =
      (α_ (V p) (W q) (X r)).hom ≫ ιTensorObj₃ V W X p q r k h := by
  -- This is exactly the owner API for the graded associator component.
  exact ιTensorObj₃'_associator_hom V W X p q r k h

/-- Helper for Example 12.17.4: the inverse graded associator on a fixed triple summand rewrites
to the ordinary inverse associator on the component modules. -/
@[reassoc]
private theorem graded_associator_inv_component
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r k : ℤ) (h : p + q + r = k) :
    ιTensorObj₃ V W X p q r k h ≫ (α_ V W X).inv k =
      (α_ (V p) (W q) (X r)).inv ≫ ιTensorObj₃' V W X p q r k h := by
  -- This is exactly the owner API for the inverse graded associator component.
  exact ιTensorObj₃_associator_inv V W X p q r k h

/-- Helper for Example 12.17.4: right whiskering preserves the already computed degree-`p + q`
component of the descended Koszul braiding. -/
private theorem koszulBraidingHom_app_whisker_right
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r : ℤ) :
    ((ιTensorObj V W p q (p + q) rfl ≫ koszulBraidingHom V W (p + q)) ▷ X r) =
      ((koszulBraidingComponent V W p q ≫
          ιTensorObj W V q p (p + q) (Eq.trans (add_comm q p) rfl)) ▷ X r) := by
  -- Right whiskering preserves the degree-`p + q` component identity.
  simpa using congrArg (fun u ↦ u ▷ X r) (koszulBraidingHom_app V W p q (p + q) rfl)

/-- Helper for Example 12.17.4: reassociating the whiskered degree-`p + q` component exposes the
tensor-product component needed inside the forward and reverse hexagon computations. -/
@[reassoc]
private theorem koszulBraidingHom_app_whisker_right_assoc
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r : ℤ) :
    (ιTensorObj V W p q (p + q) rfl ▷ X r) ≫
        ((koszulBraiding V W).hom (p + q) ⊗ₘ 𝟙 (X r)) =
      (koszulBraidingComponent V W p q ⊗ₘ 𝟙 (X r)) ≫
        (ιTensorObj W V q p (p + q) (Eq.trans (add_comm q p) rfl) ▷ X r) := by
  -- Reassociate the whiskered component formula into the exact outer-inclusion shape.
  simpa only [koszulBraiding, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.tensorHom_id] using koszulBraidingHom_app_whisker_right V W X p q r

/-- Helper for Example 12.17.4: left whiskering preserves the already computed degree-`q + r`
component of the descended Koszul braiding. -/
private theorem koszulBraidingHom_app_whisker_left
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r : ℤ) :
    (V p ◁ (ιTensorObj W X q r (q + r) rfl ≫ koszulBraidingHom W X (q + r))) =
      (V p ◁ (koszulBraidingComponent W X q r ≫
          ιTensorObj X W r q (q + r) (Eq.trans (add_comm r q) rfl))) := by
  -- Left whiskering preserves the degree-`q + r` component identity.
  simpa using congrArg (fun u ↦ V p ◁ u) (koszulBraidingHom_app W X q r (q + r) rfl)

/-- Helper for Example 12.17.4: reassociating the whiskered degree-`q + r` component exposes the
tensor-product component needed inside the forward and reverse hexagon computations. -/
@[reassoc]
private theorem koszulBraidingHom_app_whisker_left_assoc
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r : ℤ) :
    (V p ◁ ιTensorObj W X q r (q + r) rfl) ≫
        (𝟙 (V p) ⊗ₘ (koszulBraiding W X).hom (q + r)) =
      (𝟙 (V p) ⊗ₘ koszulBraidingComponent W X q r) ≫
        (V p ◁ ιTensorObj X W r q (q + r) (Eq.trans (add_comm r q) rfl)) := by
  -- Reassociate the whiskered component formula into the exact outer-inclusion shape.
  simpa only [koszulBraiding, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.id_tensorHom] using koszulBraidingHom_app_whisker_left V W X p q r

/-- Helper for Example 12.17.4: opening the outer `(p + q, r)` inclusion and then postcomposing
with a right-whiskered morphism matches direct postcomposition on the opened summand. -/
private theorem iTensorObj₃'_tensorHom_postcompose_whisker_right
    (V W H X : GradedObject ℤ (ModuleCat F)) (φ : V ⊗ W ⟶ H) (p q r k : ℤ)
    (h : p + q + r = k) :
    (ιTensorObj V W p q (p + q) rfl ▷ X r) ≫
        (φ (p + q) ⊗ₘ 𝟙 (X r)) ≫
          ιTensorObj H X (p + q) r k (by simpa [add_assoc] using h) =
      ιTensorObj₃' V W X p q r k h ≫ (φ ▷ X) k := by
  have hsum : p + q + r = k := h
  have houter : p + q + r = k := h
  have hpq : p + q = p + q := rfl
  -- First move the whiskered morphism across the inner summand inclusion.
  calc
    (ιTensorObj V W p q (p + q) rfl ▷ X r) ≫
          (φ (p + q) ⊗ₘ 𝟙 (X r)) ≫
            ιTensorObj H X (p + q) r k (by simpa [add_assoc] using h) =
      (ιTensorObj V W p q (p + q) rfl ▷ X r) ≫
          ιTensorObj (V ⊗ W) X (p + q) r k (by simpa [add_assoc] using h) ≫
            (φ ▷ X) k := by
              simpa only [Category.assoc, whiskerRight] using congrArg
                (fun u ↦ (ιTensorObj V W p q (p + q) rfl ▷ X r) ≫ u)
                ((ι_tensorHom_assoc φ (𝟙 X) (p + q) r k
                  (by simpa [add_assoc] using h) (𝟙 _)).symm)
    _ = ιTensorObj₃' V W X p q r k h ≫ (φ ▷ X) k := by
      -- Then refold the outer inclusion with the chosen postcomposition in place.
      simpa only [Category.assoc] using
        (ιTensorObj₃'_eq_assoc V W X p q r k h (p + q) hpq ((φ ▷ X) k)).symm

/-- Helper for Example 12.17.4: opening the outer `(p, q + r)` inclusion and then postcomposing
with a left-whiskered morphism matches direct postcomposition on the opened summand. -/
private theorem iTensorObj₃_tensorHom_postcompose_whisker_left
    (V W X H : GradedObject ℤ (ModuleCat F)) (ψ : W ⊗ X ⟶ H) (p q r k : ℤ)
    (h : p + q + r = k) :
    (V p ◁ ιTensorObj W X q r (q + r) rfl) ≫
        (𝟙 (V p) ⊗ₘ ψ (q + r)) ≫
          ιTensorObj V H p (q + r) k (by simpa [add_assoc] using h) =
      ιTensorObj₃ V W X p q r k h ≫ (V ◁ ψ) k := by
  have hqr : q + r = q + r := rfl
  -- First move the whiskered morphism across the inner summand inclusion.
  calc
    (V p ◁ ιTensorObj W X q r (q + r) rfl) ≫
          (𝟙 (V p) ⊗ₘ ψ (q + r)) ≫
            ιTensorObj V H p (q + r) k (by simpa [add_assoc] using h) =
      (V p ◁ ιTensorObj W X q r (q + r) rfl) ≫
          ιTensorObj V (W ⊗ X) p (q + r) k (by simpa [add_assoc] using h) ≫
            (V ◁ ψ) k := by
              simpa only [Category.assoc, whiskerLeft] using congrArg
                (fun u ↦ (V p ◁ ιTensorObj W X q r (q + r) rfl) ≫ u)
                ((ι_tensorHom_assoc (𝟙 V) ψ p (q + r) k
                  (by simpa [add_assoc] using h) (𝟙 _)).symm)
    _ = ιTensorObj₃ V W X p q r k h ≫ (V ◁ ψ) k := by
      -- Then refold the outer inclusion with the chosen postcomposition in place.
      simpa only [Category.assoc] using
        (ιTensorObj₃_eq_assoc V W X p q r k h (q + r) hqr ((V ◁ ψ) k)).symm

/-- Helper for Example 12.17.4: precomposing a triple-summand inclusion with the whiskered Koszul
braiding on the first two factors exposes the explicit signed `(p, q)`-component. -/
@[reassoc]
private theorem koszulBraiding_whisker_right_component
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r k : ℤ) (h : p + q + r = k) :
    ιTensorObj₃' V W X p q r k h ≫ ((koszulBraiding V W).hom ▷ X) k =
      (koszulBraidingComponent V W p q ⊗ₘ 𝟙 (X r)) ≫
        ιTensorObj₃' W V X q p r k (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
  have hqp : q + p + r = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  have hpq : q + p = p + q := by
    simpa [add_comm] using (show p + q = p + q from rfl)
  -- Route correction: first expose the inner degree-`p + q` component, then refold the outer sum.
  calc
    ιTensorObj₃' V W X p q r k h ≫ ((koszulBraiding V W).hom ▷ X) k =
      (ιTensorObj V W p q (p + q) rfl ▷ X r) ≫
          ((koszulBraiding V W).hom (p + q) ⊗ₘ 𝟙 (X r)) ≫
            ιTensorObj (W ⊗ V) X (p + q) r k (by simpa [add_assoc] using h) := by
            simpa using
              (iTensorObj₃'_tensorHom_postcompose_whisker_right
                V W (W ⊗ V) X (koszulBraiding V W).hom p q r k h).symm
    _ =
      (koszulBraidingComponent V W p q ⊗ₘ 𝟙 (X r)) ≫
          (ιTensorObj W V q p (p + q) (Eq.trans (add_comm q p) rfl) ▷ X r) ≫
            ιTensorObj (W ⊗ V) X (p + q) r k (by simpa [add_assoc] using h) := by
            rw [koszulBraidingHom_app_whisker_right_assoc_assoc]
    _ =
      (koszulBraidingComponent V W p q ⊗ₘ 𝟙 (X r)) ≫
          ιTensorObj₃' W V X q p r k hqp := by
            simpa only [Category.assoc] using congrArg
              (fun u ↦ (koszulBraidingComponent V W p q ⊗ₘ 𝟙 (X r)) ≫ u)
              ((ιTensorObj₃'_eq_assoc W V X q p r k hqp (p + q) hpq (𝟙 _)).symm)

/-- Helper for Example 12.17.4: precomposing a triple-summand inclusion with the whiskered Koszul
braiding on the last two factors exposes the explicit signed `(q, r)`-component. -/
@[reassoc]
private theorem koszulBraiding_whisker_left_component
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r k : ℤ) (h : p + q + r = k) :
    ιTensorObj₃ V W X p q r k h ≫ (V ◁ (koszulBraiding W X).hom) k =
      (𝟙 (V p) ⊗ₘ koszulBraidingComponent W X q r) ≫
        ιTensorObj₃ V X W p r q k (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
  have hrq : r + q = q + r := by
    simpa [add_comm] using (show q + r = q + r from rfl)
  have hprq : p + r + q = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- Route correction: first expose the inner degree-`q + r` component, then refold the outer sum.
  calc
    ιTensorObj₃ V W X p q r k h ≫ (V ◁ (koszulBraiding W X).hom) k =
      (V p ◁ ιTensorObj W X q r (q + r) rfl) ≫
          (𝟙 (V p) ⊗ₘ (koszulBraiding W X).hom (q + r)) ≫
            ιTensorObj V (X ⊗ W) p (q + r) k (by simpa [add_assoc] using h) := by
            simpa using
              (iTensorObj₃_tensorHom_postcompose_whisker_left
                V W X (X ⊗ W) (koszulBraiding W X).hom p q r k h).symm
    _ =
      (𝟙 (V p) ⊗ₘ koszulBraidingComponent W X q r) ≫
          (V p ◁ ιTensorObj X W r q (q + r) (Eq.trans (add_comm r q) rfl)) ≫
            ιTensorObj V (X ⊗ W) p (q + r) k (by simpa [add_assoc] using h) := by
            rw [koszulBraidingHom_app_whisker_left_assoc_assoc]
    _ =
      (𝟙 (V p) ⊗ₘ koszulBraidingComponent W X q r) ≫
          ιTensorObj₃ V X W p r q k hprq := by
            simpa only [Category.assoc] using congrArg
              (fun u ↦ (𝟙 (V p) ⊗ₘ koszulBraidingComponent W X q r) ≫ u)
              ((ιTensorObj₃_eq_assoc V X W p r q k hprq (q + r) hrq (𝟙 _)).symm)

/-- Helper for Example 12.17.4: right whiskering a Koszul component keeps the same scalar and
right-whiskers the underlying ordinary braiding. -/
private theorem koszulBraidingComponent_whisker_right_eq
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r : ℤ) :
    koszulBraidingComponent V W p q ⊗ₘ 𝟙 (X r) =
      ((p * q).negOnePow : F) • (((β_ (V p) (W q)).hom) ▷ X r) := by
  -- Right whiskering preserves the scalar and only whiskers the underlying braiding map.
  rw [koszulBraidingComponent, tensorHom_id]
  exact MonoidalLinear.smul_whiskerRight (R := F) ((p * q).negOnePow : F)
    (β_ (V p) (W q)).hom (X r)

/-- Helper for Example 12.17.4: left whiskering a Koszul component keeps the same scalar and
left-whiskers the underlying ordinary braiding. -/
private theorem koszulBraidingComponent_whisker_left_eq
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r : ℤ) :
    𝟙 (W q) ⊗ₘ koszulBraidingComponent V X p r =
      ((p * r).negOnePow : F) • (W q ◁ ((β_ (V p) (X r)).hom)) := by
  -- Left whiskering preserves the scalar and only whiskers the underlying braiding map.
  rw [koszulBraidingComponent, id_tensorHom]
  exact MonoidalLinear.whiskerLeft_smul (R := F) (W q) ((p * r).negOnePow : F)
    (β_ (V p) (X r)).hom

/-- Helper for Example 12.17.4: the ordinary forward hexagon in `ModuleCat F` remains valid after
scaling the three braiding terms by compatible Koszul signs. -/
private theorem scaled_braiding_hexagon_forward
    (X Y Z : ModuleCat F) (a b c : F) (ha : a = b * c) :
    (α_ X Y Z).hom ≫ (a • (β_ X (Y ⊗ Z)).hom) ≫ (α_ Y Z X).hom =
      (b • (((β_ X Y).hom) ▷ Z)) ≫ (α_ Y X Z).hom ≫ (c • (Y ◁ (β_ X Z).hom)) := by
  -- Route correction: factor the middle scalar once, use the ordinary forward hexagon, and then
  -- expand the compatible product scalar back to the two outer Koszul factors.
  subst ha
  calc
    (α_ X Y Z).hom ≫ ((b * c) • (β_ X (Y ⊗ Z)).hom) ≫ (α_ Y Z X).hom =
      (b * c) • ((α_ X Y Z).hom ≫ (β_ X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom) := by
        exact middle_smul_comp (α_ X Y Z).hom (β_ X (Y ⊗ Z)).hom (α_ Y Z X).hom (b * c)
    _ = (b * c) • ((((β_ X Y).hom) ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (β_ X Z).hom)) := by
      refine congrArg (fun u ↦ (b * c) • u) ?_
      simpa [Category.assoc] using BraidedCategory.hexagon_forward (X := X) (Y := Y) (Z := Z)
    _ = (b • (((β_ X Y).hom) ▷ Z)) ≫ (α_ Y X Z).hom ≫ (c • (Y ◁ (β_ X Z).hom)) := by
      symm
      exact smul_comp_comp_smul (((β_ X Y).hom) ▷ Z) (α_ Y X Z).hom (Y ◁ (β_ X Z).hom) b c

/-- Helper for Example 12.17.4: the ordinary reverse hexagon in `ModuleCat F` remains valid after
scaling the three braiding terms by compatible Koszul signs. -/
private theorem scaled_braiding_hexagon_reverse
    (X Y Z : ModuleCat F) (a b c : F) (ha : a = b * c) :
    (α_ X Y Z).inv ≫ (a • (β_ (X ⊗ Y) Z).hom) ≫ (α_ Z X Y).inv =
      (b • (X ◁ (β_ Y Z).hom)) ≫ (α_ X Z Y).inv ≫ (c • (((β_ X Z).hom) ▷ Y)) := by
  -- The reverse hexagon is the same scalar factoring argument applied to the inverse associator.
  subst ha
  calc
    (α_ X Y Z).inv ≫ ((b * c) • (β_ (X ⊗ Y) Z).hom) ≫ (α_ Z X Y).inv =
      (b * c) • ((α_ X Y Z).inv ≫ (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv) := by
        exact middle_smul_comp (α_ X Y Z).inv (β_ (X ⊗ Y) Z).hom (α_ Z X Y).inv (b * c)
    _ = (b * c) • ((X ◁ (β_ Y Z).hom) ≫ (α_ X Z Y).inv ≫ (((β_ X Z).hom) ▷ Y)) := by
      refine congrArg (fun u ↦ (b * c) • u) ?_
      simpa [Category.assoc] using BraidedCategory.hexagon_reverse (X := X) (Y := Y) (Z := Z)
    _ = (b • (X ◁ (β_ Y Z).hom)) ≫ (α_ X Z Y).inv ≫ (c • (((β_ X Z).hom) ▷ Y)) := by
      symm
      exact smul_comp_comp_smul (X ◁ (β_ Y Z).hom) (α_ X Z Y).inv (((β_ X Z).hom) ▷ Y) b c

private theorem koszulBraiding_naturality_left
    {V W X : GradedObject ℤ (ModuleCat F)} (f : V ⟶ W) :
    f ▷ X ≫ (koszulBraiding W X).hom =
      (koszulBraiding V X).hom ≫ X ◁ f := by
  -- Restrict to each `(p, q)`-summand and use the component naturality just proved above.
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  calc
    ιTensorObj V X p q n h ≫
        (GradedObject.Monoidal.whiskerRight f X ≫ (koszulBraiding W X).hom) n =
      (f p ⊗ₘ 𝟙 (X q)) ≫ ιTensorObj W X p q n h ≫ (koszulBraiding W X).hom n := by
          simpa [Category.assoc] using congrArg
            (fun u ↦ u ≫ (koszulBraiding W X).hom n)
            (GradedObject.Monoidal.ι_tensorHom f (𝟙 X) p q n h)
    _ =
      (f p ⊗ₘ 𝟙 (X q)) ≫ koszulBraidingComponent W X p q ≫
        ιTensorObj X W q p n (by simpa [add_comm] using h) := by
          simpa [Category.assoc, koszulBraiding] using congrArg
            (fun u ↦ (f p ⊗ₘ 𝟙 (X q)) ≫ u)
            (koszulBraidingHom_app W X p q n h)
    _ =
      koszulBraidingComponent V X p q ≫ (𝟙 (X q) ⊗ₘ f p) ≫
        ιTensorObj X W q p n (by simpa [add_comm] using h) := by
          simpa [Category.assoc] using congrArg
            (fun u ↦ u ≫ ιTensorObj X W q p n (by simpa [add_comm] using h))
            (koszulBraidingComponent_naturality_left (f := f) p q)
    _ =
      koszulBraidingComponent V X p q ≫
        ιTensorObj X V q p n (by simpa [add_comm] using h) ≫
          (GradedObject.Monoidal.whiskerLeft X f) n := by
          simpa [Category.assoc] using congrArg
            (fun u ↦ koszulBraidingComponent V X p q ≫ u)
            (GradedObject.Monoidal.ι_tensorHom (𝟙 X) f q p n
              (Eq.trans (add_comm q p) h)).symm
    _ =
      ιTensorObj V X p q n h ≫
        ((koszulBraiding V X).hom ≫ GradedObject.Monoidal.whiskerLeft X f) n := by
          simpa [Category.assoc, koszulBraiding] using congrArg
            (fun u ↦ u ≫ (GradedObject.Monoidal.whiskerLeft X f) n)
            (koszulBraidingHom_app V X p q n h)

private theorem koszulBraiding_naturality_right
    (V : GradedObject ℤ (ModuleCat F)) {W X : GradedObject ℤ (ModuleCat F)} (f : W ⟶ X) :
    V ◁ f ≫ (koszulBraiding V X).hom =
      (koszulBraiding V W).hom ≫ f ▷ V := by
  -- Restrict to each `(p, q)`-summand and use the component naturality just proved above.
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  calc
    ιTensorObj V W p q n h ≫
        (GradedObject.Monoidal.whiskerLeft V f ≫ (koszulBraiding V X).hom) n =
      (𝟙 (V p) ⊗ₘ f q) ≫ ιTensorObj V X p q n h ≫ (koszulBraiding V X).hom n := by
          simpa [Category.assoc] using congrArg
            (fun u ↦ u ≫ (koszulBraiding V X).hom n)
            (GradedObject.Monoidal.ι_tensorHom (𝟙 V) f p q n h)
    _ =
      (𝟙 (V p) ⊗ₘ f q) ≫ koszulBraidingComponent V X p q ≫
        ιTensorObj X V q p n (by simpa [add_comm] using h) := by
          simpa [Category.assoc, koszulBraiding] using congrArg
            (fun u ↦ (𝟙 (V p) ⊗ₘ f q) ≫ u)
            (koszulBraidingHom_app V X p q n h)
    _ =
      koszulBraidingComponent V W p q ≫ (f q ⊗ₘ 𝟙 (V p)) ≫
        ιTensorObj X V q p n (by simpa [add_comm] using h) := by
          simpa [Category.assoc] using congrArg
            (fun u ↦ u ≫ ιTensorObj X V q p n (by simpa [add_comm] using h))
            (koszulBraidingComponent_naturality_right V f p q)
    _ =
      koszulBraidingComponent V W p q ≫
        ιTensorObj W V q p n (by simpa [add_comm] using h) ≫
          (GradedObject.Monoidal.whiskerRight f V) n := by
          simpa [Category.assoc] using congrArg
            (fun u ↦ koszulBraidingComponent V W p q ≫ u)
            (GradedObject.Monoidal.ι_tensorHom f (𝟙 V) q p n
              (Eq.trans (add_comm q p) h)).symm
    _ =
      ιTensorObj V W p q n h ≫
        ((koszulBraiding V W).hom ≫ GradedObject.Monoidal.whiskerRight f V) n := by
          simpa [Category.assoc, koszulBraiding] using congrArg
            (fun u ↦ u ≫ (GradedObject.Monoidal.whiskerRight f V) n)
            (koszulBraidingHom_app V W p q n h)

/-- Helper for Example 12.17.4: after opening the first associator in the forward hexagon, the
left-hand side normalizes to the common `(q, r, p)` triple summand. -/
@[reassoc]
private theorem koszulBraiding_tensor_right_total_component
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r k : ℤ) (h : p + q + r = k) :
    ιTensorObj₃ V W X p q r k h ≫
      (koszulBraiding V (W ⊗ X)).hom k ≫ (α_ W X V).hom k =
        ((((p * (q + r)).negOnePow : F)) • (β_ (V p) (W q ⊗ X r)).hom) ≫
          (α_ (W q) (X r) (V p)).hom ≫
            ιTensorObj₃ W X V q r p k
              (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
  let inner :
      W q ⊗ X r ⟶ (W ⊗ X) (q + r) :=
    ιTensorObj W X q r (q + r) rfl
  let h₁ : p + (q + r) = k := by
    simpa [add_assoc] using h
  let hswap : q + r + p = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- Route correction: follow the source proof literally by opening the outer summand, moving the
  -- inner inclusion across the ordinary braiding by naturality, and then refolding.
  calc
    ιTensorObj₃ V W X p q r k h ≫
        (koszulBraiding V (W ⊗ X)).hom k ≫ (α_ W X V).hom k =
      (V p ◁ inner) ≫
          ιTensorObj V (W ⊗ X) p (q + r) k h₁ ≫
            (koszulBraiding V (W ⊗ X)).hom k ≫ (α_ W X V).hom k := by
            simpa only [inner, Category.assoc] using
              (ιTensorObj₃_eq_assoc V W X p q r k h (q + r) rfl
                ((koszulBraiding V (W ⊗ X)).hom k ≫ (α_ W X V).hom k))
    _ =
      (V p ◁ inner) ≫
          ((((p * (q + r)).negOnePow : F)) •
            (β_ (V p) ((W ⊗ X) (q + r))).hom) ≫
            ιTensorObj (W ⊗ X) V (q + r) p k
              (by simpa [add_assoc, add_comm] using h₁) ≫
              (α_ W X V).hom k := by
            -- The component formula for the Koszul braiding already exposes the scalar layer.
            simpa only [inner, koszulBraiding, koszulBraidingComponent, Category.assoc] using
              congrArg
                (fun u ↦ (V p ◁ inner) ≫ u)
                (koszulBraidingHom_app_assoc V (W ⊗ X) p (q + r) k h₁ ((α_ W X V).hom k))
    _ =
      ((((p * (q + r)).negOnePow : F)) • (β_ (V p) (W q ⊗ X r)).hom) ≫
          (inner ▷ V p) ≫
            ιTensorObj (W ⊗ X) V (q + r) p k
              (by simpa [add_assoc, add_comm] using h₁) ≫
              (α_ W X V).hom k := by
            -- Move the inner inclusion through the ordinary braiding while keeping the scalar fixed.
            calc
              (V p ◁ inner) ≫
                  ((((p * (q + r)).negOnePow : F)) •
                    (β_ (V p) ((W ⊗ X) (q + r))).hom) ≫
                    ιTensorObj (W ⊗ X) V (q + r) p k
                      (by simpa [add_assoc, add_comm] using h₁) ≫
                      (α_ W X V).hom k =
                (((p * (q + r)).negOnePow : F)) •
                  (((V p ◁ inner) ≫ (β_ (V p) ((W ⊗ X) (q + r))).hom) ≫
                    ιTensorObj (W ⊗ X) V (q + r) p k
                      (by simpa [add_assoc, add_comm] using h₁) ≫
                        (α_ W X V).hom k) := by
                          exact middle_smul_comp (V p ◁ inner)
                            (β_ (V p) ((W ⊗ X) (q + r))).hom
                            (ιTensorObj (W ⊗ X) V (q + r) p k
                              (by simpa [add_assoc, add_comm] using h₁) ≫
                                (α_ W X V).hom k)
                            (((p * (q + r)).negOnePow : F))
              _ =
                (((p * (q + r)).negOnePow : F)) •
                  (((β_ (V p) (W q ⊗ X r)).hom ≫ (inner ▷ V p)) ≫
                    ιTensorObj (W ⊗ X) V (q + r) p k
                      (by simpa [add_assoc, add_comm] using h₁) ≫
                        (α_ W X V).hom k) := by
                          refine congrArg (fun u ↦
                            (((p * (q + r)).negOnePow : F)) •
                              (u ≫ ιTensorObj (W ⊗ X) V (q + r) p k
                                (by simpa [add_assoc, add_comm] using h₁) ≫
                                  (α_ W X V).hom k)) ?_
                          simpa only [inner, Category.assoc, MonoidalCategory.whiskerLeft,
                            MonoidalCategory.whiskerRight] using
                            (BraidedCategory.braiding_naturality_right (X := V p) (f := inner))
              _ =
                ((((p * (q + r)).negOnePow : F)) • (β_ (V p) (W q ⊗ X r)).hom) ≫
                    (inner ▷ V p) ≫
                      ιTensorObj (W ⊗ X) V (q + r) p k
                        (by simpa [add_assoc, add_comm] using h₁) ≫
                          (α_ W X V).hom k := by
                            simpa [Category.assoc] using
                              (smul_comp_comp_smul
                                ((β_ (V p) (W q ⊗ X r)).hom)
                                (inner ▷ V p)
                                (ιTensorObj (W ⊗ X) V (q + r) p k
                                  (by simpa [add_assoc, add_comm] using h₁) ≫
                                    (α_ W X V).hom k)
                                (((p * (q + r)).negOnePow : F)) (1 : F)).symm
    _ =
      ((((p * (q + r)).negOnePow : F)) • (β_ (V p) (W q ⊗ X r)).hom) ≫
          ιTensorObj₃' W X V q r p k hswap ≫
            (α_ W X V).hom k := by
            -- Refold the swapped outer inclusion before rewriting the associator component.
            simpa only [inner, Category.assoc] using congrArg
              (fun u ↦
                ((((p * (q + r)).negOnePow : F)) • (β_ (V p) (W q ⊗ X r)).hom) ≫ u)
              ((ιTensorObj₃'_eq_assoc W X V q r p k hswap (q + r) rfl
                ((α_ W X V).hom k)).symm)
    _ =
      ((((p * (q + r)).negOnePow : F)) • (β_ (V p) (W q ⊗ X r)).hom) ≫
          (α_ (W q) (X r) (V p)).hom ≫
            ιTensorObj₃ W X V q r p k hswap := by
            -- The last reassociation is the graded associator component formula.
            simpa only [Category.assoc] using congrArg
              (fun u ↦
                ((((p * (q + r)).negOnePow : F)) • (β_ (V p) (W q ⊗ X r)).hom) ≫ u)
              (graded_associator_hom_component W X V q r p k hswap)

/-- Helper for Example 12.17.4: the right-hand side of the forward hexagon normalizes to the
same `(q, r, p)` summand target before invoking the ordinary forward hexagon. -/
private theorem koszulBraiding_forward_rhs_total_component
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r k : ℤ) (h : p + q + r = k) :
    ιTensorObj₃' V W X p q r k h ≫
      (((koszulBraiding V W).hom ▷ X) ≫ (α_ W V X).hom ≫ W ◁ (koszulBraiding V X).hom) k =
        ((((p * q).negOnePow : F)) • (((β_ (V p) (W q)).hom) ▷ X r)) ≫
          (α_ (W q) (V p) (X r)).hom ≫
            ((((p * r).negOnePow : F)) • (W q ◁ (β_ (V p) (X r)).hom)) ≫
              ιTensorObj₃ W X V q r p k
                (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
  let hqp : q + p + r = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  let hswap : q + r + p = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- Route correction: expose the two whiskered Koszul components in sequence, then rewrite each
  -- to a scalar-separated ordinary braiding term.
  calc
    ιTensorObj₃' V W X p q r k h ≫
        (((koszulBraiding V W).hom ▷ X) ≫ (α_ W V X).hom ≫ W ◁ (koszulBraiding V X).hom) k =
      (koszulBraidingComponent V W p q ⊗ₘ 𝟙 (X r)) ≫
          ιTensorObj₃' W V X q p r k hqp ≫
            (α_ W V X).hom k ≫ (W ◁ (koszulBraiding V X).hom) k := by
            simpa only [Category.assoc] using
              (koszulBraiding_whisker_right_component_assoc V W X p q r k h
                ((α_ W V X).hom k ≫ (W ◁ (koszulBraiding V X).hom) k))
    _ =
      (koszulBraidingComponent V W p q ⊗ₘ 𝟙 (X r)) ≫
          (α_ (W q) (V p) (X r)).hom ≫
            ιTensorObj₃ W V X q p r k hqp ≫
              (W ◁ (koszulBraiding V X).hom) k := by
            simpa only [Category.assoc] using congrArg
              (fun u ↦ (koszulBraidingComponent V W p q ⊗ₘ 𝟙 (X r)) ≫ u)
              (graded_associator_hom_component_assoc W V X q p r k hqp
                ((W ◁ (koszulBraiding V X).hom) k))
    _ =
      (koszulBraidingComponent V W p q ⊗ₘ 𝟙 (X r)) ≫
          (α_ (W q) (V p) (X r)).hom ≫
            (𝟙 (W q) ⊗ₘ koszulBraidingComponent V X p r) ≫
              ιTensorObj₃ W X V q r p k hswap := by
            simpa only [Category.assoc] using congrArg
              (fun u ↦
                (koszulBraidingComponent V W p q ⊗ₘ 𝟙 (X r)) ≫
                  (α_ (W q) (V p) (X r)).hom ≫ u)
              (koszulBraiding_whisker_left_component W V X q p r k hqp)
    _ =
      ((((p * q).negOnePow : F)) • (((β_ (V p) (W q)).hom) ▷ X r)) ≫
          (α_ (W q) (V p) (X r)).hom ≫
            ((((p * r).negOnePow : F)) • (W q ◁ (β_ (V p) (X r)).hom)) ≫
              ιTensorObj₃ W X V q r p k hswap := by
            rw [koszulBraidingComponent_whisker_right_eq,
              koszulBraidingComponent_whisker_left_eq]

private theorem koszulBraiding_hexagon_forward
    (V W X : GradedObject ℤ (ModuleCat F)) :
    (α_ V W X).hom ≫ (koszulBraiding V (W ⊗ X)).hom ≫ (α_ W X V).hom =
      (koszulBraiding V W).hom ▷ X ≫ (α_ W V X).hom ≫
        W ◁ (koszulBraiding V X).hom := by
  -- Restrict to each degree and then to each triple summand, where the source proof has already
  -- normalized both sides to the same `(q,r,p)` target.
  funext k
  apply tensorObj₃'_ext
  intro p q r h
  let hswap : q + r + p = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- Route correction: rewrite the first associator componentwise, normalize the total component,
  -- apply the ordinary forward hexagon with the split Koszul signs, then fold back.
  calc
    ιTensorObj₃' V W X p q r k h ≫
        ((α_ V W X).hom ≫ (koszulBraiding V (W ⊗ X)).hom ≫
          (α_ W X V).hom) k =
      (α_ (V p) (W q) (X r)).hom ≫
          (ιTensorObj₃ V W X p q r k h ≫
            (koszulBraiding V (W ⊗ X)).hom k ≫ (α_ W X V).hom k) := by
            simpa only [Category.assoc] using
              (graded_associator_hom_component_assoc V W X p q r k h
                ((koszulBraiding V (W ⊗ X)).hom k ≫ (α_ W X V).hom k))
    _ =
      (α_ (V p) (W q) (X r)).hom ≫
          ((((p * (q + r)).negOnePow : F)) • (β_ (V p) (W q ⊗ X r)).hom) ≫
            (α_ (W q) (X r) (V p)).hom ≫
              ιTensorObj₃ W X V q r p k hswap := by
            rw [koszulBraiding_tensor_right_total_component V W X p q r k h]
    _ =
      ((((p * q).negOnePow : F)) • (((β_ (V p) (W q)).hom) ▷ X r)) ≫
          (α_ (W q) (V p) (X r)).hom ≫
            ((((p * r).negOnePow : F)) • (W q ◁ (β_ (V p) (X r)).hom)) ≫
              ιTensorObj₃ W X V q r p k hswap := by
            simpa only [Category.assoc] using congrArg
              (fun u ↦ u ≫ ιTensorObj₃ W X V q r p k hswap)
              (scaled_braiding_hexagon_forward (V p) (W q) (X r)
                ((((p * (q + r)).negOnePow : F)))
                ((((p * q).negOnePow : F)))
                ((((p * r).negOnePow : F)))
                (koszul_sign_add_right p q r))
    _ =
      ιTensorObj₃' V W X p q r k h ≫
        (((koszulBraiding V W).hom ▷ X) ≫ (α_ W V X).hom ≫
          W ◁ (koszulBraiding V X).hom) k := by
            simpa only [Category.assoc] using
              (koszulBraiding_forward_rhs_total_component V W X p q r k h).symm

/-- Helper for Example 12.17.4: after opening the first inverse associator in the reverse
hexagon, the left-hand side normalizes to the common `(r, p, q)` triple summand. -/
@[reassoc]
private theorem koszulBraiding_tensor_left_total_component
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r k : ℤ) (h : p + q + r = k) :
    ιTensorObj₃' V W X p q r k h ≫
      (koszulBraiding (V ⊗ W) X).hom k ≫ (α_ X V W).inv k =
        ((((p + q) * r).negOnePow : F) • (β_ (V p ⊗ W q) (X r)).hom) ≫
          (α_ (X r) (V p) (W q)).inv ≫
            ιTensorObj₃' X V W r p q k
              (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
  let inner :
      V p ⊗ W q ⟶ (V ⊗ W) (p + q) :=
    ιTensorObj V W p q (p + q) rfl
  let h₁ : p + q + r = k := h
  let hswap : r + p + q = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- Route correction: mirror the forward transport proof, now opening the left tensor summand
  -- and moving the inner inclusion across the ordinary braiding by left naturality.
  calc
    ιTensorObj₃' V W X p q r k h ≫
        (koszulBraiding (V ⊗ W) X).hom k ≫ (α_ X V W).inv k =
      (inner ▷ X r) ≫
          ιTensorObj (V ⊗ W) X (p + q) r k h₁ ≫
            (koszulBraiding (V ⊗ W) X).hom k ≫
              (α_ X V W).inv k := by
            simpa only [inner, Category.assoc] using
              (ιTensorObj₃'_eq_assoc V W X p q r k h (p + q) rfl
                ((koszulBraiding (V ⊗ W) X).hom k ≫ (α_ X V W).inv k))
    _ =
      (inner ▷ X r) ≫
          ((((p + q) * r).negOnePow : F) •
            (β_ ((V ⊗ W) (p + q)) (X r)).hom) ≫
              ιTensorObj X (V ⊗ W) r (p + q) k
                (by simpa [add_assoc, add_comm] using h₁) ≫
                  (α_ X V W).inv k := by
            -- The component formula for the Koszul braiding already exposes the scalar layer.
            simpa only [inner, koszulBraiding, koszulBraidingComponent, Category.assoc] using
              congrArg
                (fun u ↦ (inner ▷ X r) ≫ u)
                (koszulBraidingHom_app_assoc (V ⊗ W) X (p + q) r k h₁ ((α_ X V W).inv k))
    _ =
      ((((p + q) * r).negOnePow : F) • (β_ (V p ⊗ W q) (X r)).hom) ≫
          (X r ◁ inner) ≫
            ιTensorObj X (V ⊗ W) r (p + q) k
              (by simpa [add_assoc, add_comm] using h₁) ≫
                (α_ X V W).inv k := by
            -- Move the inner inclusion through the ordinary braiding while keeping the scalar fixed.
            calc
              (inner ▷ X r) ≫
                  ((((p + q) * r).negOnePow : F) •
                    (β_ ((V ⊗ W) (p + q)) (X r)).hom) ≫
                      ιTensorObj X (V ⊗ W) r (p + q) k
                        (by simpa [add_assoc, add_comm] using h₁) ≫
                          (α_ X V W).inv k =
                ((((p + q) * r).negOnePow : F)) •
                  (((inner ▷ X r) ≫ (β_ ((V ⊗ W) (p + q)) (X r)).hom) ≫
                    ιTensorObj X (V ⊗ W) r (p + q) k
                      (by simpa [add_assoc, add_comm] using h₁) ≫
                        (α_ X V W).inv k) := by
                          exact middle_smul_comp (inner ▷ X r)
                            (β_ ((V ⊗ W) (p + q)) (X r)).hom
                            (ιTensorObj X (V ⊗ W) r (p + q) k
                              (by simpa [add_assoc, add_comm] using h₁) ≫
                                (α_ X V W).inv k)
                            ((((p + q) * r).negOnePow : F))
              _ =
                ((((p + q) * r).negOnePow : F)) •
                  (((β_ (V p ⊗ W q) (X r)).hom ≫ (X r ◁ inner)) ≫
                    ιTensorObj X (V ⊗ W) r (p + q) k
                      (by simpa [add_assoc, add_comm] using h₁) ≫
                        (α_ X V W).inv k) := by
                          refine congrArg (fun u ↦
                            ((((p + q) * r).negOnePow : F)) •
                              (u ≫ ιTensorObj X (V ⊗ W) r (p + q) k
                                (by simpa [add_assoc, add_comm] using h₁) ≫
                                  (α_ X V W).inv k)) ?_
                          simpa only [inner, Category.assoc, MonoidalCategory.whiskerLeft,
                            MonoidalCategory.whiskerRight] using
                            (BraidedCategory.braiding_naturality_left (f := inner) (Z := X r))
              _ =
                ((((p + q) * r).negOnePow : F) • (β_ (V p ⊗ W q) (X r)).hom) ≫
                    (X r ◁ inner) ≫
                      ιTensorObj X (V ⊗ W) r (p + q) k
                        (by simpa [add_assoc, add_comm] using h₁) ≫
                          (α_ X V W).inv k := by
                            simpa [Category.assoc] using
                              (smul_comp_comp_smul
                                ((β_ (V p ⊗ W q) (X r)).hom)
                                (X r ◁ inner)
                                (ιTensorObj X (V ⊗ W) r (p + q) k
                                  (by simpa [add_assoc, add_comm] using h₁) ≫
                                    (α_ X V W).inv k)
                                ((((p + q) * r).negOnePow : F)) (1 : F)).symm
    _ =
      ((((p + q) * r).negOnePow : F) • (β_ (V p ⊗ W q) (X r)).hom) ≫
          ιTensorObj₃ X V W r p q k hswap ≫
            (α_ X V W).inv k := by
            -- Refold the swapped outer inclusion before rewriting the inverse associator component.
            simpa only [inner, Category.assoc] using congrArg
              (fun u ↦
                ((((p + q) * r).negOnePow : F) • (β_ (V p ⊗ W q) (X r)).hom) ≫ u)
              ((ιTensorObj₃_eq_assoc X V W r p q k hswap (p + q) rfl
                ((α_ X V W).inv k)).symm)
    _ =
      ((((p + q) * r).negOnePow : F) • (β_ (V p ⊗ W q) (X r)).hom) ≫
          (α_ (X r) (V p) (W q)).inv ≫
            ιTensorObj₃' X V W r p q k hswap := by
            -- The last reassociation is the inverse graded associator component formula.
            simpa only [Category.assoc] using congrArg
              (fun u ↦
                ((((p + q) * r).negOnePow : F) • (β_ (V p ⊗ W q) (X r)).hom) ≫ u)
              (graded_associator_inv_component X V W r p q k hswap)

/-- Helper for Example 12.17.4: the right-hand side of the reverse hexagon normalizes to the
same `(r, p, q)` summand target before invoking the ordinary reverse hexagon. -/
private theorem koszulBraiding_reverse_rhs_total_component
    (V W X : GradedObject ℤ (ModuleCat F)) (p q r k : ℤ) (h : p + q + r = k) :
    ιTensorObj₃ V W X p q r k h ≫
      ((V ◁ (koszulBraiding W X).hom) ≫ (α_ V X W).inv ≫ (koszulBraiding V X).hom ▷ W) k =
        ((((q * r).negOnePow : F)) • (V p ◁ (β_ (W q) (X r)).hom)) ≫
          (α_ (V p) (X r) (W q)).inv ≫
            ((((p * r).negOnePow : F)) • (((β_ (V p) (X r)).hom) ▷ W q)) ≫
              ιTensorObj₃' X V W r p q k
                (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
  let hprq : p + r + q = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  let hswap : r + p + q = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- Route correction: expose the two whiskered Koszul components in sequence, then rewrite each
  -- to a scalar-separated ordinary braiding term on the common `(r,p,q)` summand.
  calc
    ιTensorObj₃ V W X p q r k h ≫
        ((V ◁ (koszulBraiding W X).hom) ≫ (α_ V X W).inv ≫
          (koszulBraiding V X).hom ▷ W) k =
      (𝟙 (V p) ⊗ₘ koszulBraidingComponent W X q r) ≫
          ιTensorObj₃ V X W p r q k hprq ≫
            (α_ V X W).inv k ≫ ((koszulBraiding V X).hom ▷ W) k := by
            simpa only [Category.assoc] using
              (koszulBraiding_whisker_left_component_assoc V W X p q r k h
                ((α_ V X W).inv k ≫ ((koszulBraiding V X).hom ▷ W) k))
    _ =
      (𝟙 (V p) ⊗ₘ koszulBraidingComponent W X q r) ≫
          (α_ (V p) (X r) (W q)).inv ≫
            ιTensorObj₃' V X W p r q k hprq ≫
              ((koszulBraiding V X).hom ▷ W) k := by
            simpa only [Category.assoc] using congrArg
              (fun u ↦ (𝟙 (V p) ⊗ₘ koszulBraidingComponent W X q r) ≫ u)
              (graded_associator_inv_component_assoc V X W p r q k hprq
                (((koszulBraiding V X).hom ▷ W) k))
    _ =
      (𝟙 (V p) ⊗ₘ koszulBraidingComponent W X q r) ≫
          (α_ (V p) (X r) (W q)).inv ≫
            (koszulBraidingComponent V X p r ⊗ₘ 𝟙 (W q)) ≫
              ιTensorObj₃' X V W r p q k hswap := by
            simpa only [Category.assoc] using congrArg
              (fun u ↦
                (𝟙 (V p) ⊗ₘ koszulBraidingComponent W X q r) ≫
                  (α_ (V p) (X r) (W q)).inv ≫ u)
              (koszulBraiding_whisker_right_component V X W p r q k hprq)
    _ =
      ((((q * r).negOnePow : F)) • (V p ◁ (β_ (W q) (X r)).hom)) ≫
          (α_ (V p) (X r) (W q)).inv ≫
            ((((p * r).negOnePow : F)) • (((β_ (V p) (X r)).hom) ▷ W q)) ≫
              ιTensorObj₃' X V W r p q k hswap := by
            rw [koszulBraidingComponent_whisker_left_eq W V X q p r,
              koszulBraidingComponent_whisker_right_eq V X W p r q]

private theorem koszulBraiding_hexagon_reverse
    (V W X : GradedObject ℤ (ModuleCat F)) :
    (α_ V W X).inv ≫ (koszulBraiding (V ⊗ W) X).hom ≫ (α_ X V W).inv =
      V ◁ (koszulBraiding W X).hom ≫ (α_ V X W).inv ≫
        (koszulBraiding V X).hom ▷ W := by
  -- Restrict to each degree and then to each triple summand, where the source proof has already
  -- normalized both sides to the same `(r,p,q)` target.
  funext k
  apply tensorObj₃_ext
  intro p q r h
  let hswap : r + p + q = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- Route correction: rewrite the first inverse associator componentwise, normalize the total
  -- component, apply the ordinary reverse hexagon with the split Koszul signs, then fold back.
  calc
    ιTensorObj₃ V W X p q r k h ≫
        ((α_ V W X).inv ≫ (koszulBraiding (V ⊗ W) X).hom ≫
          (α_ X V W).inv) k =
      (α_ (V p) (W q) (X r)).inv ≫
          (ιTensorObj₃' V W X p q r k h ≫
            (koszulBraiding (V ⊗ W) X).hom k ≫ (α_ X V W).inv k) := by
            simpa only [Category.assoc] using
              (graded_associator_inv_component_assoc V W X p q r k h
                ((koszulBraiding (V ⊗ W) X).hom k ≫ (α_ X V W).inv k))
    _ =
      (α_ (V p) (W q) (X r)).inv ≫
          ((((p + q) * r).negOnePow : F) • (β_ (V p ⊗ W q) (X r)).hom) ≫
            (α_ (X r) (V p) (W q)).inv ≫
              ιTensorObj₃' X V W r p q k hswap := by
            rw [koszulBraiding_tensor_left_total_component V W X p q r k h]
    _ =
      ((((q * r).negOnePow : F)) • (V p ◁ (β_ (W q) (X r)).hom)) ≫
          (α_ (V p) (X r) (W q)).inv ≫
            ((((p * r).negOnePow : F)) • (((β_ (V p) (X r)).hom) ▷ W q)) ≫
              ιTensorObj₃' X V W r p q k hswap := by
            simpa only [Category.assoc] using congrArg
              (fun u ↦ u ≫ ιTensorObj₃' X V W r p q k hswap)
              (scaled_braiding_hexagon_reverse (V p) (W q) (X r)
                ((((p + q) * r).negOnePow : F))
                ((((q * r).negOnePow : F)))
                ((((p * r).negOnePow : F)))
                (by simpa [mul_comm] using koszul_sign_add_left p q r))
    _ =
      ιTensorObj₃ V W X p q r k h ≫
        ((V ◁ (koszulBraiding W X).hom) ≫ (α_ V X W).inv ≫
          (koszulBraiding V X).hom ▷ W) k := by
            simpa only [Category.assoc] using
              (koszulBraiding_reverse_rhs_total_component V W X p q r k h).symm

/-- The symmetric-category package whose braiding is `koszulBraiding`. -/
noncomputable abbrev koszulSymmetricCategory :
    SymmetricCategory (GradedObject ℤ (ModuleCat F)) where
  toBraidedCategory :=
    { braiding := koszulBraiding
      braiding_naturality_left := by
        intro V W f X
        simpa using koszulBraiding_naturality_left f
      braiding_naturality_right := by
        intro X V W f
        simpa using koszulBraiding_naturality_right X f
      hexagon_forward := by
        intro V W X
        simpa using koszulBraiding_hexagon_forward V W X
      hexagon_reverse := by
        intro V W X
        simpa using koszulBraiding_hexagon_reverse V W X }
  symmetry V W := (koszulBraiding V W).hom_inv_id

-- Proof sketch: unfold `koszulBraiding`; its degree-`n` component is defined by
-- descending the signed swaps on the summands `V^p ⊗ W^q`, so restricting along the canonical
-- inclusion of the `(p, q)`-summand gives exactly that signed swap.
/-- Example 12.17.4. The signed commutativity constraint restricts on each `(p, q)`-summand to
the Koszul-signed swap map. -/
@[stacks 0FFX, reassoc]
theorem koszulBraiding_hom_app
    (V W : GradedObject ℤ (ModuleCat F)) (p q n : ℤ) (h : p + q = n) :
    ιTensorObj V W p q n h ≫ (koszulBraiding V W).hom n =
      koszulBraidingComponent V W p q ≫
        ιTensorObj W V q p n (Eq.trans (add_comm q p) h) := by
  -- The public component formula is the same as the already proved formula for `koszulBraidingHom`.
  simpa [koszulBraiding] using koszulBraidingHom_app V W p q n h

end GradedObject.Monoidal

end CategoryTheory
