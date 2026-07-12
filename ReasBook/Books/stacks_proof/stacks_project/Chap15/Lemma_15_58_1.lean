import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.BifunctorFlip
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.GradedObject.Braiding
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u

section

variable {C : Type u} [Category C] [Preadditive C] [HasZeroObject C]
variable [MonoidalCategory C] [SymmetricCategory C]
variable [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ X : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X)]
variable [∀ X : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X)]

local notation "Cpx" => CochainComplex C ℤ

/- Domain-style sampling for Lemma 15.58.1:
- primary domain: symmetric monoidal structures on cochain complexes, with tensor symmetry given
  by the canonical total-complex flip;
- sampled owner declarations:
  `mapBifunctorFlipIso`,
  `mapBifunctorFlipIso_hom_naturality`,
  `BraidedCategory.curriedBraidingNatIso`,
  `HomologicalComplex₂.total.mapIso`,
  `BraidedCategory`,
  `SymmetricCategory`;
- best owner abstraction: the public owner layer is the braided/symmetric typeclass structure on
  cochain complexes; the concrete bridge data are the total-complex flip
  `mapBifunctorFlipIso` and the pointwise tensor braiding induced from
  `BraidedCategory.curriedBraidingNatIso`;
- primitive vs derived:
  primitive data are the pointwise braiding on bicomplexes and the total-complex flip;
  the braided and symmetric instances on cochain complexes are derived packaging;
- source/core/bridge triage:
  `source-facing`: the symmetric monoidal structure on cochain complexes from the Stacks lemma;
  `core/canonical`: the typeclass owners `BraidedCategory` and `SymmetricCategory`;
  `bridge/view`: the bicomplex pointwise braiding and the canonical flip
  `mapBifunctorFlipIso _ _ (curriedTensor C) (up ℤ)`.
-/

private abbrev forgetGraded : Cpx ⥤ GradedObject ℤ C :=
  HomologicalComplex.forget C (up ℤ)

/-- Helper for Lemma 15.58.1: the Koszul-signed swap on the `(p,q)`-summand of a graded tensor
product. -/
private abbrev signedGradedBraidingComponent
    (G₁ G₂ : GradedObject ℤ C) (p q : ℤ) :
    G₁ p ⊗ G₂ q ⟶ G₂ q ⊗ G₁ p :=
  ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q • (β_ (G₁ p) (G₂ q)).hom

/-- Helper for Lemma 15.58.1: descending the signed swaps on each summand gives a graded map
`G₁ ⊗ G₂ ⟶ G₂ ⊗ G₁`. -/
private abbrev signedGradedBraidingHom
    (G₁ G₂ : GradedObject ℤ C) :
    G₁ ⊗ G₂ ⟶ G₂ ⊗ G₁ :=
  fun n ↦
    GradedObject.Monoidal.tensorObjDesc
      (fun p q h ↦
        signedGradedBraidingComponent G₁ G₂ p q ≫
          GradedObject.Monoidal.ιTensorObj G₂ G₁ q p n (by simpa [add_comm] using h))

/-- Helper for Lemma 15.58.1: restricting the descended signed graded swap to a `(p,q)`-summand
recovers the expected Koszul-signed braiding component. -/
@[reassoc]
private theorem signedGradedBraiding_hom_app
    (G₁ G₂ : GradedObject ℤ C) (p q n : ℤ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj G₁ G₂ p q n h ≫ signedGradedBraidingHom G₁ G₂ n =
      signedGradedBraidingComponent G₁ G₂ p q ≫
        GradedObject.Monoidal.ιTensorObj G₂ G₁ q p n (by simpa [add_comm] using h) := by
  -- The descended map is defined by the universal property of the graded tensor sum.
  simp [signedGradedBraidingHom, signedGradedBraidingComponent,
    GradedObject.Monoidal.ι_tensorObjDesc]

/-- Helper for Lemma 15.58.1: the flipped pointwise tensor bicomplex on `L` and `K`. -/
private abbrev pointwiseTensorBicomplexSource
    (K L : Cpx) :=
  (((curriedTensor C).flip.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj L).obj K

/-- Helper for Lemma 15.58.1: the ordinary pointwise tensor bicomplex on `L` and `K`. -/
private abbrev pointwiseTensorBicomplexTarget
    (K L : Cpx) :=
  (((curriedTensor C).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj L).obj K

/-- Helper for Lemma 15.58.1: the component of the pointwise braiding on the `(q,p)`-entry of the
tensor bicomplex. -/
private abbrev pointwiseTensorBicomplexBraidingComponent
    (K L : Cpx) (q p : ℤ) :
    (pointwiseTensorBicomplexSource (C := C) K L).toGradedObject ⟨q, p⟩ ⟶
      (pointwiseTensorBicomplexTarget (C := C) K L).toGradedObject ⟨q, p⟩ :=
  (((BraidedCategory.curriedBraidingNatIso C).app (K.X p)).app (L.X q)).hom

/-- Helper for Lemma 15.58.1: at fixed `q`, the pointwise braiding intertwines the `K`
differentials in the tensor bicomplex. -/
private theorem pointwiseTensorBicomplexBraiding_inner_comm
    (K L : Cpx) (q p p' : ℤ) (_hp : (up ℤ).Rel p p') :
    pointwiseTensorBicomplexBraidingComponent (C := C) K L q p ≫
        ((pointwiseTensorBicomplexTarget (C := C) K L).X q).d p p' =
      ((pointwiseTensorBicomplexSource (C := C) K L).X q).d p p' ≫
        pointwiseTensorBicomplexBraidingComponent (C := C) K L q p' := by
  -- The inner differential tensors the differential of `K`, and braiding naturality moves it
  -- across the fixed factor `L.X q`.
  dsimp [pointwiseTensorBicomplexBraidingComponent,
    pointwiseTensorBicomplexSource, pointwiseTensorBicomplexTarget]
  simpa using
    (BraidedCategory.braiding_naturality_left (f := K.d p p') (Z := L.X q)).symm

/-- Helper for Lemma 15.58.1: for fixed `q`, the pointwise braiding gives an isomorphism of the
`q`-th columns of the two tensor bicomplexes. -/
private noncomputable abbrev pointwiseTensorBicomplexColumnBraidingIso
    (K L : Cpx) (q : ℤ) :
    (pointwiseTensorBicomplexSource (C := C) K L).X q ≅
      (pointwiseTensorBicomplexTarget (C := C) K L).X q :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ ((BraidedCategory.curriedBraidingNatIso C).app (K.X p)).app (L.X q))
    (pointwiseTensorBicomplexBraiding_inner_comm (C := C) K L q)

/-- Helper for Lemma 15.58.1: as `q` varies, the pointwise braiding also intertwines the `L`
differentials, so the column isomorphisms assemble to a bicomplex isomorphism. -/
private theorem pointwiseTensorBicomplexBraiding_outer_comm
    (K L : Cpx) (q q' : ℤ) (_hq : (up ℤ).Rel q q') :
    (pointwiseTensorBicomplexColumnBraidingIso (C := C) K L q).hom ≫
        (pointwiseTensorBicomplexTarget (C := C) K L).d q q' =
      (pointwiseTensorBicomplexSource (C := C) K L).d q q' ≫
        (pointwiseTensorBicomplexColumnBraidingIso (C := C) K L q').hom := by
  -- The outer differential tensors the differential of `L`, and right-variable braiding
  -- naturality moves it across the fixed factor `K.X p`.
  ext p
  simp only [pointwiseTensorBicomplexColumnBraidingIso]
  simpa using
    (BraidedCategory.braiding_naturality_right (X := K.X p) (f := L.d q q')).symm

/-- Helper for Lemma 15.58.1: the pointwise braiding turns the flipped tensor bicomplex back into
the ordinary tensor bicomplex. -/
private noncomputable def pointwiseTensorBicomplexBraidingIso
    (K L : Cpx) :
    (((curriedTensor C).flip.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj L).obj K ≅
      (((curriedTensor C).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj L).obj K :=
  -- The bicomplex isomorphism is assembled columnwise from the ordinary braiding in `C`.
  HomologicalComplex.Hom.isoOfComponents
    (pointwiseTensorBicomplexColumnBraidingIso (C := C) K L)
    (pointwiseTensorBicomplexBraiding_outer_comm (C := C) K L)

/-- Helper for Lemma 15.58.1: after the total flip swaps the indices, the pointwise braiding
reorders the tensor factors to the ordinary tensor bicomplex. -/
private noncomputable def pointwiseTensorBraidingIso
    (K L : Cpx) :
    HomologicalComplex.mapBifunctor L K (curriedTensor C).flip (up ℤ) ≅ L ⊗ K :=
  HomologicalComplex₂.total.mapIso (pointwiseTensorBicomplexBraidingIso K L) (up ℤ)

/-- Helper for Lemma 15.58.1: on each `(q,p)`-summand of the flipped tensor bicomplex, the
pointwise braiding is the ordinary tensor braiding in `C`. -/
@[reassoc]
private theorem pointwiseTensorBraiding_hom_app
    (K L : Cpx) (q p n : ℤ) (h : q + p = n) :
    HomologicalComplex.ιMapBifunctor L K (curriedTensor C).flip (up ℤ) q p n h ≫
        (pointwiseTensorBraidingIso K L).hom.f n =
      (((BraidedCategory.curriedBraidingNatIso C).app (K.X p)).app (L.X q)).hom ≫
        HomologicalComplex.ιTensorObj L K q p n h := by
  -- Passing the bicomplex braiding to the total complex preserves the `(q,p)`-summand formula.
  simpa [pointwiseTensorBraidingIso, pointwiseTensorBicomplexBraidingIso,
    pointwiseTensorBicomplexColumnBraidingIso, pointwiseTensorBicomplexBraidingComponent]
    using
      (HomologicalComplex₂.ιTotal_map
        (K := pointwiseTensorBicomplexSource (C := C) K L)
        (L := pointwiseTensorBicomplexTarget (C := C) K L)
        (φ := (pointwiseTensorBicomplexBraidingIso (C := C) K L).hom)
        (c₁₂ := up ℤ) q p n h)

/-- Helper for Lemma 15.58.1: applying the signed graded braiding twice is the identity. -/
private theorem signedGradedBraidingComponent_comp_id
    (G₁ G₂ : GradedObject ℤ C) (p q : ℤ) :
    signedGradedBraidingComponent G₁ G₂ p q ≫
        signedGradedBraidingComponent G₂ G₁ q p =
      𝟙 (G₁ p ⊗ G₂ q) := by
  -- The two Koszul signs agree after swapping `p` and `q`, so they square to `1`.
  -- The remaining composite is the ordinary symmetry in `C`.
  rw [signedGradedBraidingComponent, signedGradedBraidingComponent, Linear.units_smul_comp,
    Linear.comp_units_smul, smul_smul, SymmetricCategory.symmetry]
  simp [mul_comm]

/-- Helper for Lemma 15.58.1: applying the signed graded braiding twice is the identity. -/
private theorem signedGradedBraiding_hom_inv_id
    (G₁ G₂ : GradedObject ℤ C) :
    signedGradedBraidingHom G₁ G₂ ≫ signedGradedBraidingHom G₂ G₁ = 𝟙 (G₁ ⊗ G₂) := by
  -- Restrict to each `(p,q)`-summand of degree `n`, rewrite both descended braidings, and then
  -- collapse the middle composite with the summandwise symmetry calculation.
  ext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  calc
    GradedObject.Monoidal.ιTensorObj G₁ G₂ p q n h ≫
        (signedGradedBraidingHom G₁ G₂ ≫ signedGradedBraidingHom G₂ G₁) n =
      signedGradedBraidingComponent G₁ G₂ p q ≫
        GradedObject.Monoidal.ιTensorObj G₂ G₁ q p n (by simpa [add_comm] using h) ≫
          signedGradedBraidingHom G₂ G₁ n := by
            simp [Category.assoc, signedGradedBraiding_hom_app, mul_comm]
    _ =
      signedGradedBraidingComponent G₁ G₂ p q ≫
        signedGradedBraidingComponent G₂ G₁ q p ≫
          GradedObject.Monoidal.ιTensorObj G₁ G₂ p q n h := by
            simpa [Category.assoc] using congrArg
              (fun u ↦ signedGradedBraidingComponent G₁ G₂ p q ≫ u)
              (signedGradedBraiding_hom_app G₂ G₁ q p n (by simpa [add_comm] using h))
    _ = GradedObject.Monoidal.ιTensorObj G₁ G₂ p q n h := by
      simpa [Category.assoc] using congrArg
        (fun u ↦ u ≫ GradedObject.Monoidal.ιTensorObj G₁ G₂ p q n h)
        (signedGradedBraidingComponent_comp_id G₁ G₂ p q)
    _ = GradedObject.Monoidal.ιTensorObj G₁ G₂ p q n h ≫ (𝟙 (G₁ ⊗ G₂)) n := by
      symm
      exact Category.comp_id _

/-- Helper for Lemma 15.58.1: the signed graded braiding is the canonical braiding on
graded objects relevant for the cochain-complex symmetry. -/
private noncomputable def signedGradedBraiding
    (G₁ G₂ : GradedObject ℤ C) :
    G₁ ⊗ G₂ ≅ G₂ ⊗ G₁ where
  hom := signedGradedBraidingHom G₁ G₂
  inv := signedGradedBraidingHom G₂ G₁
  hom_inv_id := signedGradedBraiding_hom_inv_id G₁ G₂
  inv_hom_id := signedGradedBraiding_hom_inv_id G₂ G₁

/-- Helper for Lemma 15.58.1: on each `(p,q)`-summand, left-variable naturality reduces to the
ordinary braiding naturality because the Koszul sign is fixed. -/
private theorem signedGradedBraidingComponent_naturality_left
    {G₁ G₂ G₃ : GradedObject ℤ C} (f : G₁ ⟶ G₂) (p q : ℤ) :
    (f p ⊗ₘ 𝟙 (G₃ q)) ≫ signedGradedBraidingComponent G₂ G₃ p q =
      signedGradedBraidingComponent G₁ G₃ p q ≫ (𝟙 (G₃ q) ⊗ₘ f p) := by
  -- Unfold the signed component once: the common scalar factors out, leaving the ordinary
  -- left-variable braiding naturality in `C`.
  rw [signedGradedBraidingComponent, signedGradedBraidingComponent, Linear.comp_units_smul,
    Linear.units_smul_comp]
  simpa using BraidedCategory.braiding_naturality_left (f := f p) (Z := G₃ q)

/-- Helper for Lemma 15.58.1: on each `(p,q)`-summand, right-variable naturality reduces to the
ordinary braiding naturality because the Koszul sign is fixed. -/
private theorem signedGradedBraidingComponent_naturality_right
    (G₁ : GradedObject ℤ C) {G₂ G₃ : GradedObject ℤ C} (f : G₂ ⟶ G₃) (p q : ℤ) :
    (𝟙 (G₁ p) ⊗ₘ f q) ≫ signedGradedBraidingComponent G₁ G₃ p q =
      signedGradedBraidingComponent G₁ G₂ p q ≫ (f q ⊗ₘ 𝟙 (G₁ p)) := by
  -- Unfold the signed component once: the common scalar factors out, leaving the ordinary
  -- right-variable braiding naturality in `C`.
  rw [signedGradedBraidingComponent, signedGradedBraidingComponent, Linear.comp_units_smul,
    Linear.units_smul_comp]
  simpa using BraidedCategory.braiding_naturality_right (X := G₁ p) (f := f q)

/-- Helper for Lemma 15.58.1: the signed graded braiding is natural in the left argument. -/
private theorem signedGradedBraiding_naturality_left
    {G₁ G₂ G₃ : GradedObject ℤ C} (f : G₁ ⟶ G₂) :
    GradedObject.Monoidal.whiskerRight f G₃ ≫ (signedGradedBraiding G₂ G₃).hom =
      (signedGradedBraiding G₁ G₃).hom ≫ GradedObject.Monoidal.whiskerLeft G₃ f := by
  -- Restrict to a `(p,q)`-summand, rewrite the two descended braidings, and use the component
  -- naturality lemma to move `f p` across the signed swap.
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  calc
    GradedObject.Monoidal.ιTensorObj G₁ G₃ p q n h ≫
        (GradedObject.Monoidal.whiskerRight f G₃ ≫ (signedGradedBraiding G₂ G₃).hom) n =
      (f p ⊗ₘ 𝟙 (G₃ q)) ≫ GradedObject.Monoidal.ιTensorObj G₂ G₃ p q n h ≫
        (signedGradedBraiding G₂ G₃).hom n := by
          simpa [Category.assoc] using congrArg
            (fun u ↦ u ≫ (signedGradedBraiding G₂ G₃).hom n)
            (GradedObject.Monoidal.ι_tensorHom f (𝟙 G₃) p q n h)
    _ =
      (f p ⊗ₘ 𝟙 (G₃ q)) ≫ signedGradedBraidingComponent G₂ G₃ p q ≫
        GradedObject.Monoidal.ιTensorObj G₃ G₂ q p n (by simpa [add_comm] using h) := by
          simpa [Category.assoc, signedGradedBraiding] using congrArg
            (fun u ↦ (f p ⊗ₘ 𝟙 (G₃ q)) ≫ u)
            (signedGradedBraiding_hom_app G₂ G₃ p q n h)
    _ =
      signedGradedBraidingComponent G₁ G₃ p q ≫ (𝟙 (G₃ q) ⊗ₘ f p) ≫
        GradedObject.Monoidal.ιTensorObj G₃ G₂ q p n (by simpa [add_comm] using h) := by
          simpa [Category.assoc] using congrArg
            (fun u ↦ u ≫ GradedObject.Monoidal.ιTensorObj G₃ G₂ q p n
              (by simpa [add_comm] using h))
            (signedGradedBraidingComponent_naturality_left (f := f) p q)
    _ =
      signedGradedBraidingComponent G₁ G₃ p q ≫
        GradedObject.Monoidal.ιTensorObj G₃ G₁ q p n (by simpa [add_comm] using h) ≫
          (GradedObject.Monoidal.whiskerLeft G₃ f) n := by
            simpa [Category.assoc] using congrArg
              (fun u ↦ signedGradedBraidingComponent G₁ G₃ p q ≫ u)
              (GradedObject.Monoidal.ι_tensorHom (𝟙 G₃) f q p n (by simpa [add_comm] using h)).symm
    _ =
      GradedObject.Monoidal.ιTensorObj G₁ G₃ p q n h ≫
        ((signedGradedBraiding G₁ G₃).hom ≫ GradedObject.Monoidal.whiskerLeft G₃ f) n := by
          simpa [Category.assoc, signedGradedBraiding] using congrArg
            (fun u ↦ u ≫ (GradedObject.Monoidal.whiskerLeft G₃ f) n)
            (signedGradedBraiding_hom_app G₁ G₃ p q n h)

/-- Helper for Lemma 15.58.1: the signed graded braiding is natural in the right argument. -/
private theorem signedGradedBraiding_naturality_right
    (G₁ : GradedObject ℤ C) {G₂ G₃ : GradedObject ℤ C} (f : G₂ ⟶ G₃) :
    GradedObject.Monoidal.whiskerLeft G₁ f ≫ (signedGradedBraiding G₁ G₃).hom =
      (signedGradedBraiding G₁ G₂).hom ≫ GradedObject.Monoidal.whiskerRight f G₁ := by
  -- Restrict to a `(p,q)`-summand, rewrite the two descended braidings, and use the ordinary
  -- right-variable braiding naturality in `C` because the sign does not change.
  funext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  calc
    GradedObject.Monoidal.ιTensorObj G₁ G₂ p q n h ≫
        (GradedObject.Monoidal.whiskerLeft G₁ f ≫ (signedGradedBraiding G₁ G₃).hom) n =
      (𝟙 (G₁ p) ⊗ₘ f q) ≫ GradedObject.Monoidal.ιTensorObj G₁ G₃ p q n h ≫
        (signedGradedBraiding G₁ G₃).hom n := by
          simpa [Category.assoc] using congrArg
            (fun u ↦ u ≫ (signedGradedBraiding G₁ G₃).hom n)
            (GradedObject.Monoidal.ι_tensorHom (𝟙 G₁) f p q n h)
    _ =
      (𝟙 (G₁ p) ⊗ₘ f q) ≫ signedGradedBraidingComponent G₁ G₃ p q ≫
        GradedObject.Monoidal.ιTensorObj G₃ G₁ q p n (by simpa [add_comm] using h) := by
          simpa [Category.assoc, signedGradedBraiding] using congrArg
            (fun u ↦ (𝟙 (G₁ p) ⊗ₘ f q) ≫ u)
            (signedGradedBraiding_hom_app G₁ G₃ p q n h)
    _ =
      signedGradedBraidingComponent G₁ G₂ p q ≫ (f q ⊗ₘ 𝟙 (G₁ p)) ≫
        GradedObject.Monoidal.ιTensorObj G₃ G₁ q p n (by simpa [add_comm] using h) := by
          simpa [Category.assoc] using congrArg
            (fun u ↦ u ≫ GradedObject.Monoidal.ιTensorObj G₃ G₁ q p n
              (by simpa [add_comm] using h))
            (signedGradedBraidingComponent_naturality_right G₁ f p q)
    _ =
      signedGradedBraidingComponent G₁ G₂ p q ≫
        GradedObject.Monoidal.ιTensorObj G₂ G₁ q p n (by simpa [add_comm] using h) ≫
          (GradedObject.Monoidal.whiskerRight f G₁) n := by
            simpa [Category.assoc] using congrArg
              (fun u ↦ signedGradedBraidingComponent G₁ G₂ p q ≫ u)
              (GradedObject.Monoidal.ι_tensorHom f (𝟙 G₁) q p n
                (by simpa [add_comm] using h)).symm
    _ =
      GradedObject.Monoidal.ιTensorObj G₁ G₂ p q n h ≫
        ((signedGradedBraiding G₁ G₂).hom ≫ GradedObject.Monoidal.whiskerRight f G₁) n := by
          simpa [Category.assoc, signedGradedBraiding] using congrArg
            (fun u ↦ u ≫ (GradedObject.Monoidal.whiskerRight f G₁) n)
            (signedGradedBraiding_hom_app G₁ G₂ p q n h)

/-- Helper for Lemma 15.58.1: the Koszul sign on `up ℤ` is multiplicative in the right variable. -/
private theorem complexShape_sigma_add_right (p q r : ℤ) :
    ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) =
      ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q *
        ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r := by
  -- Unfold the sign to `(-1)^(p * (q + r))` and split the exponent with distributivity.
  simpa [ComplexShape.σ, mul_add] using Int.negOnePow_add (p * q) (p * r)

/-- Helper for Lemma 15.58.1: the Koszul sign on `up ℤ` is multiplicative in the left variable. -/
private theorem complexShape_sigma_add_left (p q r : ℤ) :
    ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r =
      ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r *
        ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) q r := by
  -- Unfold the sign to `(-1)^((p + q) * r)` and split the exponent with distributivity.
  simpa [ComplexShape.σ, add_mul] using Int.negOnePow_add (p * r) (q * r)

/-- Helper for Lemma 15.58.1: the graded associator on a fixed triple summand can be rewritten in
the direct componentwise form needed for the forward hexagon computation. -/
@[reassoc]
private theorem graded_associator_hom_component
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r k : ℤ) (h : p + q + r = k) :
    GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫ (α_ G₁ G₂ G₃).hom k =
      (α_ (G₁ p) (G₂ q) (G₃ r)).hom ≫
        GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h := by
  -- Route correction: package the existing graded associator rewrite into the exact component
  -- shape used by the hexagon proof, so later rewrites do not depend on identity-postcomposition.
  exact GradedObject.Monoidal.ιTensorObj₃'_associator_hom G₁ G₂ G₃ p q r k h

/-- Helper for Lemma 15.58.1: the inverse graded associator on a fixed triple summand can be
rewritten in the direct componentwise form needed for the reverse hexagon computation. -/
@[reassoc]
private theorem graded_associator_inv_component
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r k : ℤ) (h : p + q + r = k) :
    GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫ (α_ G₁ G₂ G₃).inv k =
      (α_ (G₁ p) (G₂ q) (G₃ r)).inv ≫
        GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h := by
  -- Route correction: package the inverse graded associator rewrite into the same stable
  -- component shape, avoiding later proof-order mismatches between equal sum witnesses.
  exact GradedObject.Monoidal.ιTensorObj₃_associator_inv G₁ G₂ G₃ p q r k h

/-- Helper for Lemma 15.58.1: right whiskering preserves the signed `(p,q)` component formula at
total degree `p + q`. -/
private theorem signedGradedBraiding_hom_app_whisker_right
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r : ℤ) :
    ((GradedObject.Monoidal.ιTensorObj G₁ G₂ p q (p + q) rfl ≫
        signedGradedBraidingHom G₁ G₂ (p + q)) ▷ G₃ r) =
      ((signedGradedBraidingComponent G₁ G₂ p q ≫
          GradedObject.Monoidal.ιTensorObj G₂ G₁ q p (p + q)
            (by simpa [add_comm] using (rfl : p + q = p + q))) ▷ G₃ r) := by
  -- Right whiskering preserves the degree-`p + q` component identity already proved above.
  simpa using congrArg (fun u ↦ u ▷ G₃ r)
    (signedGradedBraiding_hom_app G₁ G₂ p q (p + q) rfl)

/-- Helper for Lemma 15.58.1: reassociating the whiskered signed `(p,q)` component on the right
isolates the tensor-product component needed by the outer triple inclusion rewrite. -/
@[reassoc]
private theorem signedGradedBraiding_hom_app_whisker_right_assoc
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r : ℤ) :
    (GradedObject.Monoidal.ιTensorObj G₁ G₂ p q (p + q) rfl ▷ G₃ r) ≫
        (((signedGradedBraiding G₁ G₂).hom) (p + q) ⊗ₘ 𝟙 (G₃ r)) =
      (signedGradedBraidingComponent G₁ G₂ p q ⊗ₘ 𝟙 (G₃ r)) ≫
        (GradedObject.Monoidal.ιTensorObj G₂ G₁ q p (p + q)
          (by simpa [add_comm] using (rfl : p + q = p + q)) ▷ G₃ r) := by
  -- Reassociate the whiskered component identity into the exact outer-inclusion shape.
  simpa only [signedGradedBraiding, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.tensorHom_id] using
    signedGradedBraiding_hom_app_whisker_right G₁ G₂ G₃ p q r

/-- Helper for Lemma 15.58.1: left whiskering preserves the signed `(q,r)` component formula at
total degree `q + r`. -/
private theorem signedGradedBraiding_hom_app_whisker_left
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r : ℤ) :
    (G₁ p ◁ (GradedObject.Monoidal.ιTensorObj G₂ G₃ q r (q + r) rfl ≫
        signedGradedBraidingHom G₂ G₃ (q + r))) =
      (G₁ p ◁ (signedGradedBraidingComponent G₂ G₃ q r ≫
          GradedObject.Monoidal.ιTensorObj G₃ G₂ r q (q + r)
            (by simpa [add_comm] using (rfl : q + r = q + r)))) := by
  -- Left whiskering preserves the degree-`q + r` component identity already proved above.
  simpa using congrArg (fun u ↦ G₁ p ◁ u)
    (signedGradedBraiding_hom_app G₂ G₃ q r (q + r) rfl)

/-- Helper for Lemma 15.58.1: reassociating the whiskered signed `(q,r)` component on the left
isolates the tensor-product component needed by the outer triple inclusion rewrite. -/
@[reassoc]
private theorem signedGradedBraiding_hom_app_whisker_left_assoc
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r : ℤ) :
    (G₁ p ◁ GradedObject.Monoidal.ιTensorObj G₂ G₃ q r (q + r) rfl) ≫
        (𝟙 (G₁ p) ⊗ₘ ((signedGradedBraiding G₂ G₃).hom) (q + r)) =
      (𝟙 (G₁ p) ⊗ₘ signedGradedBraidingComponent G₂ G₃ q r) ≫
        (G₁ p ◁ GradedObject.Monoidal.ιTensorObj G₃ G₂ r q (q + r)
          (by simpa [add_comm] using (rfl : q + r = q + r))) := by
  -- Reassociate the whiskered component identity into the exact outer-inclusion shape.
  simpa only [signedGradedBraiding, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.id_tensorHom] using
    signedGradedBraiding_hom_app_whisker_left G₁ G₂ G₃ p q r

/-- Helper for Lemma 15.58.1: opening the outer `(p + q, r)` inclusion and then postcomposing
with a right-whiskered morphism matches direct postcomposition on the opened summand. -/
private theorem iTensorObj₃'_tensorHom_postcompose_whisker_right
    (G₁ G₂ H G₃ : GradedObject ℤ C) (φ : G₁ ⊗ G₂ ⟶ H) (p q r k : ℤ)
    (h : p + q + r = k) :
    (GradedObject.Monoidal.ιTensorObj G₁ G₂ p q (p + q) rfl ▷ G₃ r) ≫
        (φ (p + q) ⊗ₘ 𝟙 (G₃ r)) ≫
          GradedObject.Monoidal.ιTensorObj H G₃ (p + q) r k
            (by simpa [add_assoc] using h) =
      GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫ (φ ▷ G₃) k := by
  -- First move the whiskered morphism across the inner summand inclusion.
  calc
    (GradedObject.Monoidal.ιTensorObj G₁ G₂ p q (p + q) rfl ▷ G₃ r) ≫
          (φ (p + q) ⊗ₘ 𝟙 (G₃ r)) ≫
            GradedObject.Monoidal.ιTensorObj H G₃ (p + q) r k
              (by simpa [add_assoc] using h) =
      (GradedObject.Monoidal.ιTensorObj G₁ G₂ p q (p + q) rfl ▷ G₃ r) ≫
          GradedObject.Monoidal.ιTensorObj (G₁ ⊗ G₂) G₃ (p + q) r k
            (by simpa [add_assoc] using h) ≫
            (φ ▷ G₃) k := by
              simpa only [Category.assoc, GradedObject.Monoidal.whiskerRight] using congrArg
                (fun u ↦ (GradedObject.Monoidal.ιTensorObj G₁ G₂ p q (p + q) rfl ▷ G₃ r) ≫ u)
                (by
                  simpa only [Category.assoc, Category.comp_id,
                    GradedObject.Monoidal.whiskerRight] using
                    (GradedObject.Monoidal.ι_tensorHom_assoc φ (𝟙 G₃) (p + q) r k
                      (by simpa [add_assoc] using h) (𝟙 _)).symm)
    _ = GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫ (φ ▷ G₃) k := by
      -- Then refold the outer inclusion with the chosen postcomposition in place.
      simpa only [Category.assoc] using
        (GradedObject.Monoidal.ιTensorObj₃'_eq_assoc G₁ G₂ G₃ p q r k h (p + q) rfl
          ((φ ▷ G₃) k)).symm

/-- Helper for Lemma 15.58.1: opening the outer `(p, q + r)` inclusion and then postcomposing
with a left-whiskered morphism matches direct postcomposition on the opened summand. -/
private theorem iTensorObj₃_tensorHom_postcompose_whisker_left
    (G₁ G₂ G₃ H : GradedObject ℤ C) (ψ : G₂ ⊗ G₃ ⟶ H) (p q r k : ℤ)
    (h : p + q + r = k) :
    (G₁ p ◁ GradedObject.Monoidal.ιTensorObj G₂ G₃ q r (q + r) rfl) ≫
        (𝟙 (G₁ p) ⊗ₘ ψ (q + r)) ≫
          GradedObject.Monoidal.ιTensorObj G₁ H p (q + r) k
            (by simpa [add_assoc] using h) =
      GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫ (G₁ ◁ ψ) k := by
  -- First move the whiskered morphism across the inner summand inclusion.
  calc
    (G₁ p ◁ GradedObject.Monoidal.ιTensorObj G₂ G₃ q r (q + r) rfl) ≫
          (𝟙 (G₁ p) ⊗ₘ ψ (q + r)) ≫
            GradedObject.Monoidal.ιTensorObj G₁ H p (q + r) k
              (by simpa [add_assoc] using h) =
      (G₁ p ◁ GradedObject.Monoidal.ιTensorObj G₂ G₃ q r (q + r) rfl) ≫
          GradedObject.Monoidal.ιTensorObj G₁ (G₂ ⊗ G₃) p (q + r) k
            (by simpa [add_assoc] using h) ≫
            (G₁ ◁ ψ) k := by
              simpa only [Category.assoc, GradedObject.Monoidal.whiskerLeft] using congrArg
                (fun u ↦ (G₁ p ◁ GradedObject.Monoidal.ιTensorObj G₂ G₃ q r (q + r) rfl) ≫ u)
                (by
                  simpa only [Category.assoc, Category.comp_id,
                    GradedObject.Monoidal.whiskerLeft] using
                    (GradedObject.Monoidal.ι_tensorHom_assoc (𝟙 G₁) ψ p (q + r) k
                      (by simpa [add_assoc] using h) (𝟙 _)).symm)
    _ = GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫ (G₁ ◁ ψ) k := by
      -- Then refold the outer inclusion with the chosen postcomposition in place.
      simpa only [Category.assoc] using
        (GradedObject.Monoidal.ιTensorObj₃_eq_assoc G₁ G₂ G₃ p q r k h (q + r) rfl
          ((G₁ ◁ ψ) k)).symm

/-- Helper for Lemma 15.58.1: precomposing a triple-summand inclusion with the whiskered signed
braiding on the first two factors yields the explicit signed component on `(p,q)`. -/
@[reassoc]
private theorem signedGradedBraiding_whisker_right_component
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r k : ℤ) (h : p + q + r = k) :
    GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫
      ((signedGradedBraiding G₁ G₂).hom ▷ G₃) k =
        (signedGradedBraidingComponent G₁ G₂ p q ⊗ₘ 𝟙 (G₃ r)) ≫
          GradedObject.Monoidal.ιTensorObj₃' G₂ G₁ G₃ q p r k
            (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
  -- Route correction: separate the inner whiskered component rewrite from the outer
  -- `(p + q, r)` inclusion refold, exactly as in the graded braiding source proof.
  calc
    GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫
        ((signedGradedBraiding G₁ G₂).hom ▷ G₃) k =
      (GradedObject.Monoidal.ιTensorObj G₁ G₂ p q (p + q) rfl ▷ G₃ r) ≫
          (((signedGradedBraiding G₁ G₂).hom) (p + q) ⊗ₘ 𝟙 (G₃ r)) ≫
            GradedObject.Monoidal.ιTensorObj (G₂ ⊗ G₁) G₃ (p + q) r k
              (by simpa [add_assoc] using h) := by
            simpa using
              (iTensorObj₃'_tensorHom_postcompose_whisker_right
                G₁ G₂ (G₂ ⊗ G₁) G₃ (signedGradedBraiding G₁ G₂).hom p q r k h).symm
    _ =
      (signedGradedBraidingComponent G₁ G₂ p q ⊗ₘ 𝟙 (G₃ r)) ≫
          (GradedObject.Monoidal.ιTensorObj G₂ G₁ q p (p + q)
              (by simpa [add_comm] using (rfl : p + q = p + q)) ▷ G₃ r) ≫
            GradedObject.Monoidal.ιTensorObj (G₂ ⊗ G₁) G₃ (p + q) r k
              (by simpa [add_assoc] using h) := by
            -- Rewrite the inner degree-`p + q` braiding component before refolding.
            rw [signedGradedBraiding_hom_app_whisker_right_assoc_assoc]
    _ =
      (signedGradedBraidingComponent G₁ G₂ p q ⊗ₘ 𝟙 (G₃ r)) ≫
          GradedObject.Monoidal.ιTensorObj₃' G₂ G₁ G₃ q p r k
            (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
            -- Refold the swapped outer inclusion after the inner whisker rewrite is exposed.
            simpa only [Category.assoc] using congrArg
              (fun u ↦ (signedGradedBraidingComponent G₁ G₂ p q ⊗ₘ 𝟙 (G₃ r)) ≫ u)
              (by
                simpa only [Category.comp_id, Category.assoc] using
                  (GradedObject.Monoidal.ιTensorObj₃'_eq_assoc G₂ G₁ G₃ q p r k
                    (by simpa [add_assoc, add_comm, add_left_comm] using h) (p + q)
                    (by simpa [add_comm] using (show q + p = p + q from add_comm q p))
                    (𝟙 _)).symm)

/-- Helper for Lemma 15.58.1: precomposing a triple-summand inclusion with the whiskered signed
braiding on the last two factors yields the explicit signed component on `(q,r)`. -/
@[reassoc]
private theorem signedGradedBraiding_whisker_left_component
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r k : ℤ) (h : p + q + r = k) :
    GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫
      (G₁ ◁ (signedGradedBraiding G₂ G₃).hom) k =
        (𝟙 (G₁ p) ⊗ₘ signedGradedBraidingComponent G₂ G₃ q r) ≫
          GradedObject.Monoidal.ιTensorObj₃ G₁ G₃ G₂ p r q k
            (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
  -- Route correction: separate the inner whiskered component rewrite from the outer
  -- `(p, q + r)` inclusion refold, exactly as in the graded braiding source proof.
  calc
    GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫
        (G₁ ◁ (signedGradedBraiding G₂ G₃).hom) k =
      (G₁ p ◁ GradedObject.Monoidal.ιTensorObj G₂ G₃ q r (q + r) rfl) ≫
          (𝟙 (G₁ p) ⊗ₘ ((signedGradedBraiding G₂ G₃).hom) (q + r)) ≫
            GradedObject.Monoidal.ιTensorObj G₁ (G₃ ⊗ G₂) p (q + r) k
              (by simpa [add_assoc] using h) := by
            simpa using
              (iTensorObj₃_tensorHom_postcompose_whisker_left
                G₁ G₂ G₃ (G₃ ⊗ G₂) (signedGradedBraiding G₂ G₃).hom p q r k h).symm
    _ =
      (𝟙 (G₁ p) ⊗ₘ signedGradedBraidingComponent G₂ G₃ q r) ≫
          (G₁ p ◁ GradedObject.Monoidal.ιTensorObj G₃ G₂ r q (q + r)
              (by simpa [add_comm] using (rfl : q + r = q + r))) ≫
            GradedObject.Monoidal.ιTensorObj G₁ (G₃ ⊗ G₂) p (q + r) k
              (by simpa [add_assoc] using h) := by
            -- Rewrite the inner degree-`q + r` braiding component before refolding.
            rw [signedGradedBraiding_hom_app_whisker_left_assoc_assoc]
    _ =
      (𝟙 (G₁ p) ⊗ₘ signedGradedBraidingComponent G₂ G₃ q r) ≫
          GradedObject.Monoidal.ιTensorObj₃ G₁ G₃ G₂ p r q k
            (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
            -- Refold the swapped outer inclusion after the inner whisker rewrite is exposed.
            simpa only [Category.assoc] using congrArg
              (fun u ↦ (𝟙 (G₁ p) ⊗ₘ signedGradedBraidingComponent G₂ G₃ q r) ≫ u)
              (by
                simpa only [Category.comp_id, Category.assoc] using
                  (GradedObject.Monoidal.ιTensorObj₃_eq_assoc G₁ G₃ G₂ p r q k
                    (by simpa [add_assoc, add_comm, add_left_comm] using h) (q + r)
                    (by simpa [add_comm] using (show r + q = q + r from add_comm r q))
                    (𝟙 _)).symm)

/-- Helper for Lemma 15.58.1: right whiskering a signed braiding component is just right
whiskering the underlying braiding and keeping the same Koszul sign. -/
private theorem signedGradedBraidingComponent_whisker_right_eq
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r : ℤ) :
    signedGradedBraidingComponent G₁ G₂ p q ⊗ₘ 𝟙 (G₃ r) =
      ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
        (((β_ (G₁ p) (G₂ q)).hom) ▷ G₃ r) := by
  -- View right whiskering as the additive functor `tensorRight (G₃ r)` applied to the signed
  -- component, and then move the scalar through that functor.
  let F : C ⥤ C := (curriedTensor C).flip.obj (G₃ r)
  letI : F.Additive := {
    map_add := by
      intro X Y f g
      -- Right whiskering is the component at `G₃ r` of the additive functor `curriedTensor C`.
      change (((curriedTensor C).map (f + g)).app (G₃ r)) =
        (((curriedTensor C).map f).app (G₃ r) + ((curriedTensor C).map g).app (G₃ r))
      exact congrArg (fun η ↦ η.app (G₃ r))
        (Functor.map_add (F := curriedTensor C) (f := f) (g := g))
  }
  have hF :
      F.map ((((ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q : ℤˣ) : ℤ) •
        ((β_ (G₁ p) (G₂ q)).hom))) =
        (((ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q : ℤˣ) : ℤ) •
          F.map ((β_ (G₁ p) (G₂ q)).hom)) := by
    simpa using F.mapAddHom.map_zsmul ((β_ (G₁ p) (G₂ q)).hom)
      (((ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q : ℤˣ) : ℤ))
  simpa only [F, signedGradedBraidingComponent, Units.smul_def, MonoidalCategory.tensorHom_id]
    using hF

/-- Helper for Lemma 15.58.1: left whiskering a signed braiding component is just left
whiskering the underlying braiding and keeping the same Koszul sign. -/
private theorem signedGradedBraidingComponent_whisker_left_eq
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r : ℤ) :
    𝟙 (G₂ q) ⊗ₘ signedGradedBraidingComponent G₁ G₃ p r =
      ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r •
        (G₂ q ◁ ((β_ (G₁ p) (G₃ r)).hom)) := by
  -- View left whiskering as the additive functor `tensorLeft (G₂ q)` applied to the signed
  -- component, and then move the scalar through that functor.
  let F : C ⥤ C := (curriedTensor C).obj (G₂ q)
  letI : F.Additive := by
    dsimp [F]
    infer_instance
  have hF :
      F.map ((((ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r : ℤˣ) : ℤ) •
        ((β_ (G₁ p) (G₃ r)).hom))) =
        (((ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r : ℤˣ) : ℤ) •
          F.map ((β_ (G₁ p) (G₃ r)).hom)) := by
    simpa using F.mapAddHom.map_zsmul ((β_ (G₁ p) (G₃ r)).hom)
      (((ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r : ℤˣ) : ℤ))
  simpa only [F, signedGradedBraidingComponent, Units.smul_def, MonoidalCategory.id_tensorHom]
    using hF

/-- Helper for Lemma 15.58.1: unit scalars on the outer factors of a triple composite combine
into the product scalar on the full composite. -/
private theorem units_smul_comp_comp_units_smul
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (a b : ℤˣ) :
    (a • f) ≫ g ≫ (b • h) = (a * b) • (f ≫ g ≫ h) := by
  -- Push the right scalar leftward across the last composition, then do the same for the left
  -- scalar and combine the two scalars.
  calc
    (a • f) ≫ g ≫ (b • h) = b • (((a • f) ≫ g) ≫ h) := by
      rw [← Category.assoc, Linear.comp_units_smul]
    _ = b • (a • (f ≫ g ≫ h)) := by
      refine congrArg (fun u ↦ b • u) ?_
      rw [Linear.units_smul_comp]
      simp [Category.assoc]
    _ = (a * b) • (f ≫ g ≫ h) := by
      simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Lemma 15.58.1: the ordinary forward hexagon in `C` remains valid after inserting
the compatible Koszul-sign scalars on the three braiding terms. -/
private theorem scaled_braiding_hexagon_forward
    (X Y Z : C) (a b c : ℤˣ) (ha : a = b * c) :
    (α_ X Y Z).hom ≫ (a • (β_ X (Y ⊗ Z)).hom) ≫ (α_ Y Z X).hom =
      (b • (((β_ X Y).hom) ▷ Z)) ≫ (α_ Y X Z).hom ≫ (c • (Y ◁ (β_ X Z).hom)) := by
  -- Rewrite the left-hand side to a single scalar multiple of the ordinary forward hexagon,
  -- use that hexagon, and then expand the right-hand side back into two scalar factors.
  subst ha
  calc
    (α_ X Y Z).hom ≫ ((b * c) • (β_ X (Y ⊗ Z)).hom) ≫ (α_ Y Z X).hom =
      (b * c) • ((α_ X Y Z).hom ≫ (β_ X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom) := by
        rw [← Category.assoc, Linear.comp_units_smul, Linear.units_smul_comp]
        rw [Category.assoc]
    _ = (b * c) • ((((β_ X Y).hom) ▷ Z) ≫ (α_ Y X Z).hom ≫ (Y ◁ (β_ X Z).hom)) := by
        simpa [Category.assoc] using congrArg
          (fun u ↦ (b * c) • u)
          (BraidedCategory.hexagon_forward (X := X) (Y := Y) (Z := Z))
    _ = (b • (((β_ X Y).hom) ▷ Z)) ≫ (α_ Y X Z).hom ≫ (c • (Y ◁ (β_ X Z).hom)) := by
        symm
        exact units_smul_comp_comp_units_smul
          (((β_ X Y).hom) ▷ Z) (α_ Y X Z).hom (Y ◁ (β_ X Z).hom) b c

/-- Helper for Lemma 15.58.1: the ordinary reverse hexagon in `C` remains valid after inserting
the compatible Koszul-sign scalars on the three braiding terms. -/
private theorem scaled_braiding_hexagon_reverse
    (X Y Z : C) (a b c : ℤˣ) (ha : a = b * c) :
    (α_ X Y Z).inv ≫ (a • (β_ (X ⊗ Y) Z).hom) ≫ (α_ Z X Y).inv =
      (b • (X ◁ ((β_ Y Z).hom))) ≫ (α_ X Z Y).inv ≫ (c • (((β_ X Z).hom) ▷ Y)) := by
  -- Rewrite the left-hand side to a single scalar multiple of the ordinary reverse hexagon,
  -- use that hexagon, and then expand the right-hand side back into two scalar factors.
  subst ha
  calc
    (α_ X Y Z).inv ≫ ((b * c) • (β_ (X ⊗ Y) Z).hom) ≫ (α_ Z X Y).inv =
      (b * c) • ((α_ X Y Z).inv ≫ (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv) := by
        rw [← Category.assoc, Linear.comp_units_smul, Linear.units_smul_comp]
        rw [Category.assoc]
    _ = (b * c) • ((X ◁ (β_ Y Z).hom) ≫ (α_ X Z Y).inv ≫ (((β_ X Z).hom) ▷ Y)) := by
        simpa [Category.assoc] using congrArg
          (fun u ↦ (b * c) • u)
          (BraidedCategory.hexagon_reverse (X := X) (Y := Y) (Z := Z))
    _ = (b • (X ◁ ((β_ Y Z).hom))) ≫ (α_ X Z Y).inv ≫ (c • (((β_ X Z).hom) ▷ Y)) := by
        symm
        exact units_smul_comp_comp_units_smul
          (X ◁ (β_ Y Z).hom) (α_ X Z Y).inv (((β_ X Z).hom) ▷ Y) b c

/-- Helper for Lemma 15.58.1: after opening the first associator in the forward hexagon, the
remaining total-component composite refolds to the common `(q,r,p)` triple summand. -/
@[reassoc]
private theorem signedGradedBraiding_tensor_right_total_component
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r k : ℤ) (h : p + q + r = k) :
    GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫
      (signedGradedBraiding G₁ (G₂ ⊗ G₃)).hom k ≫ (α_ G₂ G₃ G₁).hom k =
        (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
          (β_ (G₁ p) (G₂ q ⊗ G₃ r)).hom) ≫
          (α_ (G₂ q) (G₃ r) (G₁ p)).hom ≫
            GradedObject.Monoidal.ιTensorObj₃ G₂ G₃ G₁ q r p k
              (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
  let inner :
      G₂ q ⊗ G₃ r ⟶ (G₂ ⊗ G₃) (q + r) :=
    GradedObject.Monoidal.ιTensorObj G₂ G₃ q r (q + r) rfl
  let h₁ : p + (q + r) = k := by
    simpa [add_assoc] using h
  let hswap : q + r + p = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- Open the outer `(p, q + r)` summand, rewrite the graded braiding on that degree, and then
  -- move the inner inclusion across the ordinary braiding by naturality.
  calc
    GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫
        (signedGradedBraiding G₁ (G₂ ⊗ G₃)).hom k ≫ (α_ G₂ G₃ G₁).hom k =
      (G₁ p ◁ inner) ≫
          GradedObject.Monoidal.ιTensorObj G₁ (G₂ ⊗ G₃) p (q + r) k h₁ ≫
            (signedGradedBraiding G₁ (G₂ ⊗ G₃)).hom k ≫ (α_ G₂ G₃ G₁).hom k := by
            simpa only [inner, Category.assoc] using
              (GradedObject.Monoidal.ιTensorObj₃_eq_assoc G₁ G₂ G₃ p q r k h (q + r) rfl
                ((signedGradedBraiding G₁ (G₂ ⊗ G₃)).hom k ≫ (α_ G₂ G₃ G₁).hom k))
    _ =
      (G₁ p ◁ inner) ≫
          (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
            (β_ (G₁ p) ((G₂ ⊗ G₃) (q + r))).hom) ≫
            GradedObject.Monoidal.ιTensorObj (G₂ ⊗ G₃) G₁ (q + r) p k
              (by simpa [add_assoc, add_comm] using h₁) ≫
              (α_ G₂ G₃ G₁).hom k := by
            -- The signed braiding component on degree `p + (q + r)` is already known.
            simpa only [inner, signedGradedBraiding, signedGradedBraidingComponent,
              Category.assoc] using congrArg
              (fun u ↦ (G₁ p ◁ inner) ≫ u)
              (signedGradedBraiding_hom_app_assoc G₁ (G₂ ⊗ G₃) p (q + r) k h₁
                ((α_ G₂ G₃ G₁).hom k))
    _ =
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
        (β_ (G₁ p) (G₂ q ⊗ G₃ r)).hom) ≫
          (inner ▷ G₁ p) ≫
            GradedObject.Monoidal.ιTensorObj (G₂ ⊗ G₃) G₁ (q + r) p k
              (by simpa [add_assoc, add_comm] using h₁) ≫
              (α_ G₂ G₃ G₁).hom k := by
            -- Move the inner inclusion through the ordinary braiding, keeping the scalar fixed.
            calc
              (G₁ p ◁ inner) ≫
                  (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
                    (β_ (G₁ p) ((G₂ ⊗ G₃) (q + r))).hom) ≫
                    GradedObject.Monoidal.ιTensorObj (G₂ ⊗ G₃) G₁ (q + r) p k
                      (by simpa [add_assoc, add_comm] using h₁) ≫
                      (α_ G₂ G₃ G₁).hom k =
                ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
                  (((G₁ p ◁ inner) ≫ (β_ (G₁ p) ((G₂ ⊗ G₃) (q + r))).hom) ≫
                    GradedObject.Monoidal.ιTensorObj (G₂ ⊗ G₃) G₁ (q + r) p k
                      (by simpa [add_assoc, add_comm] using h₁) ≫
                        (α_ G₂ G₃ G₁).hom k) := by
                          rw [← Category.assoc, Linear.comp_units_smul,
                            Linear.units_smul_comp]
              _ =
                ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
                  (((β_ (G₁ p) (G₂ q ⊗ G₃ r)).hom ≫ (inner ▷ G₁ p)) ≫
                    GradedObject.Monoidal.ιTensorObj (G₂ ⊗ G₃) G₁ (q + r) p k
                      (by simpa [add_assoc, add_comm] using h₁) ≫
                        (α_ G₂ G₃ G₁).hom k) := by
                          refine congrArg (fun u ↦
                            ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
                              (u ≫ GradedObject.Monoidal.ιTensorObj (G₂ ⊗ G₃) G₁ (q + r) p k
                                (by simpa [add_assoc, add_comm] using h₁) ≫
                                  (α_ G₂ G₃ G₁).hom k)) ?_
                          simpa only [inner, Category.assoc, MonoidalCategory.whiskerLeft,
                            MonoidalCategory.whiskerRight] using
                            (BraidedCategory.braiding_naturality_right (X := G₁ p) (f := inner))
              _ =
                (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
                  (β_ (G₁ p) (G₂ q ⊗ G₃ r)).hom) ≫
                    (inner ▷ G₁ p) ≫
                      GradedObject.Monoidal.ιTensorObj (G₂ ⊗ G₃) G₁ (q + r) p k
                        (by simpa [add_assoc, add_comm] using h₁) ≫
                          (α_ G₂ G₃ G₁).hom k := by
                            rw [Linear.units_smul_comp]
                            simp only [Category.assoc]
    _ =
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
        (β_ (G₁ p) (G₂ q ⊗ G₃ r)).hom) ≫
          GradedObject.Monoidal.ιTensorObj₃' G₂ G₃ G₁ q r p k hswap ≫
            (α_ G₂ G₃ G₁).hom k := by
            -- Refold the swapped outer inclusion before the final associator component rewrite.
            simpa only [inner, Category.assoc] using congrArg
              (fun u ↦
                (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
                  (β_ (G₁ p) (G₂ q ⊗ G₃ r)).hom) ≫ u)
              ((GradedObject.Monoidal.ιTensorObj₃'_eq_assoc G₂ G₃ G₁ q r p k hswap (q + r) rfl
                ((α_ G₂ G₃ G₁).hom k)).symm)
    _ =
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
        (β_ (G₁ p) (G₂ q ⊗ G₃ r)).hom) ≫
          (α_ (G₂ q) (G₃ r) (G₁ p)).hom ≫
            GradedObject.Monoidal.ιTensorObj₃ G₂ G₃ G₁ q r p k hswap := by
            -- The last reassociation is exactly the graded associator component formula.
            simpa only [Category.assoc] using congrArg
              (fun u ↦
                (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
                  (β_ (G₁ p) (G₂ q ⊗ G₃ r)).hom) ≫ u)
              (graded_associator_hom_component G₂ G₃ G₁ q r p k hswap)

/-- Helper for Lemma 15.58.1: the right-hand side of the forward hexagon normalizes to the
common `(q,r,p)` summand target before applying the ordinary hexagon in `C`. -/
private theorem signedGradedBraiding_forward_rhs_total_component
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r k : ℤ) (h : p + q + r = k) :
    GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫
      (((signedGradedBraiding G₁ G₂).hom ▷ G₃) ≫ (α_ G₂ G₁ G₃).hom ≫
        G₂ ◁ (signedGradedBraiding G₁ G₃).hom) k =
        (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
          (((β_ (G₁ p) (G₂ q)).hom) ▷ G₃ r)) ≫
            (α_ (G₂ q) (G₁ p) (G₃ r)).hom ≫
              (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r •
                (G₂ q ◁ (β_ (G₁ p) (G₃ r)).hom)) ≫
                  GradedObject.Monoidal.ιTensorObj₃ G₂ G₃ G₁ q r p k
                    (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
  let hqp : q + p + r = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  let hswap : q + r + p = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- First expose the `(p,q)` signed braiding on the left, then reassociate and expose the
  -- `(p,r)` signed braiding on the right so both scalars are visible explicitly.
  calc
    GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫
        (((signedGradedBraiding G₁ G₂).hom ▷ G₃) ≫ (α_ G₂ G₁ G₃).hom ≫
          G₂ ◁ (signedGradedBraiding G₁ G₃).hom) k =
      (signedGradedBraidingComponent G₁ G₂ p q ⊗ₘ 𝟙 (G₃ r)) ≫
          GradedObject.Monoidal.ιTensorObj₃' G₂ G₁ G₃ q p r k hqp ≫
            (α_ G₂ G₁ G₃).hom k ≫ (G₂ ◁ (signedGradedBraiding G₁ G₃).hom) k := by
            simpa only [Category.assoc] using
              (signedGradedBraiding_whisker_right_component_assoc G₁ G₂ G₃ p q r k h
                ((α_ G₂ G₁ G₃).hom k ≫ (G₂ ◁ (signedGradedBraiding G₁ G₃).hom) k))
    _ =
      (signedGradedBraidingComponent G₁ G₂ p q ⊗ₘ 𝟙 (G₃ r)) ≫
          (α_ (G₂ q) (G₁ p) (G₃ r)).hom ≫
            GradedObject.Monoidal.ιTensorObj₃ G₂ G₁ G₃ q p r k hqp ≫
              (G₂ ◁ (signedGradedBraiding G₁ G₃).hom) k := by
            simpa only [Category.assoc] using congrArg
              (fun u ↦ (signedGradedBraidingComponent G₁ G₂ p q ⊗ₘ 𝟙 (G₃ r)) ≫ u)
              (graded_associator_hom_component_assoc G₂ G₁ G₃ q p r k hqp
                ((G₂ ◁ (signedGradedBraiding G₁ G₃).hom) k))
    _ =
      (signedGradedBraidingComponent G₁ G₂ p q ⊗ₘ 𝟙 (G₃ r)) ≫
          (α_ (G₂ q) (G₁ p) (G₃ r)).hom ≫
            (𝟙 (G₂ q) ⊗ₘ signedGradedBraidingComponent G₁ G₃ p r) ≫
              GradedObject.Monoidal.ιTensorObj₃ G₂ G₃ G₁ q r p k hswap := by
            simpa only [Category.assoc] using congrArg
              (fun u ↦
                (signedGradedBraidingComponent G₁ G₂ p q ⊗ₘ 𝟙 (G₃ r)) ≫
                  (α_ (G₂ q) (G₁ p) (G₃ r)).hom ≫ u)
              (signedGradedBraiding_whisker_left_component G₂ G₁ G₃ q p r k hqp)
    _ =
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
        (((β_ (G₁ p) (G₂ q)).hom) ▷ G₃ r)) ≫
          (α_ (G₂ q) (G₁ p) (G₃ r)).hom ≫
            (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r •
              (G₂ q ◁ (β_ (G₁ p) (G₃ r)).hom)) ≫
                GradedObject.Monoidal.ιTensorObj₃ G₂ G₃ G₁ q r p k hswap := by
            rw [signedGradedBraidingComponent_whisker_right_eq,
              signedGradedBraidingComponent_whisker_left_eq]

/-- Helper for Lemma 15.58.1: on a fixed `(p,q,r)`-summand, the forward hexagon for the signed
graded braiding reduces to the ordinary braided hexagon together with the multiplicativity of the
Koszul sign in the right variable. -/
@[reassoc]
private theorem signedGradedBraiding_hexagon_forward_component
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r k : ℤ) (h : p + q + r = k) :
    GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫
      ((α_ G₁ G₂ G₃).hom ≫ (signedGradedBraiding G₁ (G₂ ⊗ G₃)).hom ≫
        (α_ G₂ G₃ G₁).hom) k =
    GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫
      (((signedGradedBraiding G₁ G₂).hom ▷ G₃) ≫ (α_ G₂ G₁ G₃).hom ≫
        G₂ ◁ (signedGradedBraiding G₁ G₃).hom) k := by
  let hswap : q + r + p = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- Route correction: normalize both sides to the same `(q,r,p)` summand target, then apply the
  -- ordinary forward hexagon in `C` with the two separated Koszul signs.
  calc
    GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫
        ((α_ G₁ G₂ G₃).hom ≫ (signedGradedBraiding G₁ (G₂ ⊗ G₃)).hom ≫
          (α_ G₂ G₃ G₁).hom) k =
      (α_ (G₁ p) (G₂ q) (G₃ r)).hom ≫
          (GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫
            (signedGradedBraiding G₁ (G₂ ⊗ G₃)).hom k ≫ (α_ G₂ G₃ G₁).hom k) := by
            -- Rewrite the first associator componentwise before touching the signed braiding.
            simpa only [Category.assoc] using
              (graded_associator_hom_component_assoc G₁ G₂ G₃ p q r k h
                ((signedGradedBraiding G₁ (G₂ ⊗ G₃)).hom k ≫ (α_ G₂ G₃ G₁).hom k))
    _ =
      (α_ (G₁ p) (G₂ q) (G₃ r)).hom ≫
          (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r) •
            (β_ (G₁ p) (G₂ q ⊗ G₃ r)).hom) ≫
              (α_ (G₂ q) (G₃ r) (G₁ p)).hom ≫
                GradedObject.Monoidal.ιTensorObj₃ G₂ G₃ G₁ q r p k hswap := by
            -- Then apply the total-component normalization for the braiding with tensor on the right.
            rw [signedGradedBraiding_tensor_right_total_component G₁ G₂ G₃ p q r k h]
    _ =
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
        (((β_ (G₁ p) (G₂ q)).hom) ▷ G₃ r)) ≫
          (α_ (G₂ q) (G₁ p) (G₃ r)).hom ≫
            (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r •
              (G₂ q ◁ (β_ (G₁ p) (G₃ r)).hom)) ≫
                GradedObject.Monoidal.ιTensorObj₃ G₂ G₃ G₁ q r p k hswap := by
            -- Now the ordinary forward hexagon in `C` applies directly to the exposed summand.
            simpa only [Category.assoc] using congrArg
              (fun u ↦ u ≫ GradedObject.Monoidal.ιTensorObj₃ G₂ G₃ G₁ q r p k hswap)
              (scaled_braiding_hexagon_forward (G₁ p) (G₂ q) (G₃ r)
                (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p (q + r))
                (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q)
                (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r)
                (complexShape_sigma_add_right p q r))
    _ =
      GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫
        (((signedGradedBraiding G₁ G₂).hom ▷ G₃) ≫ (α_ G₂ G₁ G₃).hom ≫
          G₂ ◁ (signedGradedBraiding G₁ G₃).hom) k := by
            -- Finally fold the normalized right-hand side back into the graded-hexagon target.
            simpa only [Category.assoc] using
              (signedGradedBraiding_forward_rhs_total_component G₁ G₂ G₃ p q r k h).symm

/-- Helper for Lemma 15.58.1: after opening the first associator in the reverse hexagon, the
remaining total-component composite refolds to the common `(r,p,q)` triple summand. -/
@[reassoc]
private theorem signedGradedBraiding_tensor_left_total_component
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r k : ℤ) (h : p + q + r = k) :
    GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫
      (signedGradedBraiding (G₁ ⊗ G₂) G₃).hom k ≫ (α_ G₃ G₁ G₂).inv k =
        (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
          (β_ (G₁ p ⊗ G₂ q) (G₃ r)).hom) ≫
            (α_ (G₃ r) (G₁ p) (G₂ q)).inv ≫
              GradedObject.Monoidal.ιTensorObj₃' G₃ G₁ G₂ r p q k
                (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
  let inner :
      G₁ p ⊗ G₂ q ⟶ (G₁ ⊗ G₂) (p + q) :=
    GradedObject.Monoidal.ιTensorObj G₁ G₂ p q (p + q) rfl
  let h₁ : p + q + r = k := h
  let hswap : r + p + q = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- Open the outer `(p + q, r)` summand, rewrite the graded braiding on that degree, and then
  -- move the inner inclusion across the ordinary braiding by left naturality.
  calc
    GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫
        (signedGradedBraiding (G₁ ⊗ G₂) G₃).hom k ≫ (α_ G₃ G₁ G₂).inv k =
      (inner ▷ G₃ r) ≫
          GradedObject.Monoidal.ιTensorObj (G₁ ⊗ G₂) G₃ (p + q) r k h₁ ≫
            (signedGradedBraiding (G₁ ⊗ G₂) G₃).hom k ≫
              (α_ G₃ G₁ G₂).inv k := by
            simpa only [inner, Category.assoc] using
              (GradedObject.Monoidal.ιTensorObj₃'_eq_assoc G₁ G₂ G₃ p q r k h (p + q) rfl
                ((signedGradedBraiding (G₁ ⊗ G₂) G₃).hom k ≫ (α_ G₃ G₁ G₂).inv k))
    _ =
      (inner ▷ G₃ r) ≫
          (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
            (β_ ((G₁ ⊗ G₂) (p + q)) (G₃ r)).hom) ≫
              GradedObject.Monoidal.ιTensorObj G₃ (G₁ ⊗ G₂) r (p + q) k
                (by simpa [add_assoc, add_comm] using h₁) ≫
                  (α_ G₃ G₁ G₂).inv k := by
            -- The signed braiding component on degree `(p + q) + r` is already known.
            simpa only [inner, signedGradedBraiding, signedGradedBraidingComponent,
              Category.assoc] using congrArg
              (fun u ↦ (inner ▷ G₃ r) ≫ u)
              (signedGradedBraiding_hom_app_assoc (G₁ ⊗ G₂) G₃ (p + q) r k h₁
                ((α_ G₃ G₁ G₂).inv k))
    _ =
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
        (β_ (G₁ p ⊗ G₂ q) (G₃ r)).hom) ≫
          (G₃ r ◁ inner) ≫
            GradedObject.Monoidal.ιTensorObj G₃ (G₁ ⊗ G₂) r (p + q) k
              (by simpa [add_assoc, add_comm] using h₁) ≫
                (α_ G₃ G₁ G₂).inv k := by
            -- Move the inner inclusion through the ordinary braiding, keeping the scalar fixed.
            calc
              (inner ▷ G₃ r) ≫
                  (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
                    (β_ ((G₁ ⊗ G₂) (p + q)) (G₃ r)).hom) ≫
                      GradedObject.Monoidal.ιTensorObj G₃ (G₁ ⊗ G₂) r (p + q) k
                        (by simpa [add_assoc, add_comm] using h₁) ≫
                          (α_ G₃ G₁ G₂).inv k =
                ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
                  (((inner ▷ G₃ r) ≫ (β_ ((G₁ ⊗ G₂) (p + q)) (G₃ r)).hom) ≫
                    GradedObject.Monoidal.ιTensorObj G₃ (G₁ ⊗ G₂) r (p + q) k
              (by simpa [add_assoc, add_comm] using h₁) ≫
                          (α_ G₃ G₁ G₂).inv k) := by
                          rw [← Category.assoc, Linear.comp_units_smul,
                            Linear.units_smul_comp]
              _ =
                ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
                  (((β_ (G₁ p ⊗ G₂ q) (G₃ r)).hom ≫ (G₃ r ◁ inner)) ≫
                    GradedObject.Monoidal.ιTensorObj G₃ (G₁ ⊗ G₂) r (p + q) k
                      (by simpa [add_assoc, add_comm] using h₁) ≫
                        (α_ G₃ G₁ G₂).inv k) := by
                          refine congrArg (fun u ↦
                            ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
                              (u ≫ GradedObject.Monoidal.ιTensorObj G₃ (G₁ ⊗ G₂) r (p + q) k
                                (by simpa [add_assoc, add_comm] using h₁) ≫
                                  (α_ G₃ G₁ G₂).inv k)) ?_
                          simpa only [inner, Category.assoc, MonoidalCategory.whiskerLeft,
                            MonoidalCategory.whiskerRight] using
                            (BraidedCategory.braiding_naturality_left (f := inner) (Z := G₃ r))
              _ =
                (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
                  (β_ (G₁ p ⊗ G₂ q) (G₃ r)).hom) ≫
                    (G₃ r ◁ inner) ≫
                      GradedObject.Monoidal.ιTensorObj G₃ (G₁ ⊗ G₂) r (p + q) k
                        (by simpa [add_assoc, add_comm] using h₁) ≫
                          (α_ G₃ G₁ G₂).inv k := by
                            rw [Linear.units_smul_comp]
                            simp only [Category.assoc]
    _ =
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
        (β_ (G₁ p ⊗ G₂ q) (G₃ r)).hom) ≫
          GradedObject.Monoidal.ιTensorObj₃ G₃ G₁ G₂ r p q k hswap ≫
            (α_ G₃ G₁ G₂).inv k := by
            -- Refold the swapped outer inclusion before the final associator component rewrite.
            simpa only [inner, Category.assoc] using congrArg
              (fun u ↦
                (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
                  (β_ (G₁ p ⊗ G₂ q) (G₃ r)).hom) ≫ u)
              ((GradedObject.Monoidal.ιTensorObj₃_eq_assoc G₃ G₁ G₂ r p q k hswap (p + q) rfl
                ((α_ G₃ G₁ G₂).inv k)).symm)
    _ =
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
        (β_ (G₁ p ⊗ G₂ q) (G₃ r)).hom) ≫
          (α_ (G₃ r) (G₁ p) (G₂ q)).inv ≫
            GradedObject.Monoidal.ιTensorObj₃' G₃ G₁ G₂ r p q k hswap := by
            -- The last reassociation is exactly the inverse graded associator component formula.
            simpa only [Category.assoc] using congrArg
              (fun u ↦
                (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
                  (β_ (G₁ p ⊗ G₂ q) (G₃ r)).hom) ≫ u)
              (graded_associator_inv_component G₃ G₁ G₂ r p q k hswap)

/-- Helper for Lemma 15.58.1: the right-hand side of the reverse hexagon normalizes to the
common `(r,p,q)` summand target before applying the ordinary reverse hexagon in `C`. -/
private theorem signedGradedBraiding_reverse_rhs_total_component
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r k : ℤ) (h : p + q + r = k) :
    GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫
      ((G₁ ◁ (signedGradedBraiding G₂ G₃).hom) ≫ (α_ G₁ G₃ G₂).inv ≫
        (signedGradedBraiding G₁ G₃).hom ▷ G₂) k =
        (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) q r •
          (G₁ p ◁ (β_ (G₂ q) (G₃ r)).hom)) ≫
            (α_ (G₁ p) (G₃ r) (G₂ q)).inv ≫
              (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r •
                (((β_ (G₁ p) (G₃ r)).hom) ▷ G₂ q)) ≫
                  GradedObject.Monoidal.ιTensorObj₃' G₃ G₁ G₂ r p q k
                    (by simpa [add_assoc, add_comm, add_left_comm] using h) := by
  let hprq : p + r + q = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  let hswap : r + p + q = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- First expose the `(q,r)` signed braiding on the left, then reassociate and expose the
  -- `(p,r)` signed braiding on the right so both scalars are visible explicitly.
  calc
    GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫
        ((G₁ ◁ (signedGradedBraiding G₂ G₃).hom) ≫ (α_ G₁ G₃ G₂).inv ≫
          (signedGradedBraiding G₁ G₃).hom ▷ G₂) k =
      (𝟙 (G₁ p) ⊗ₘ signedGradedBraidingComponent G₂ G₃ q r) ≫
          GradedObject.Monoidal.ιTensorObj₃ G₁ G₃ G₂ p r q k hprq ≫
            (α_ G₁ G₃ G₂).inv k ≫ ((signedGradedBraiding G₁ G₃).hom ▷ G₂) k := by
            simpa only [Category.assoc] using
              (signedGradedBraiding_whisker_left_component_assoc G₁ G₂ G₃ p q r k h
                ((α_ G₁ G₃ G₂).inv k ≫ ((signedGradedBraiding G₁ G₃).hom ▷ G₂) k))
    _ =
      (𝟙 (G₁ p) ⊗ₘ signedGradedBraidingComponent G₂ G₃ q r) ≫
          (α_ (G₁ p) (G₃ r) (G₂ q)).inv ≫
            GradedObject.Monoidal.ιTensorObj₃' G₁ G₃ G₂ p r q k hprq ≫
              ((signedGradedBraiding G₁ G₃).hom ▷ G₂) k := by
            simpa only [Category.assoc] using congrArg
              (fun u ↦ (𝟙 (G₁ p) ⊗ₘ signedGradedBraidingComponent G₂ G₃ q r) ≫ u)
              (graded_associator_inv_component_assoc G₁ G₃ G₂ p r q k hprq
                (((signedGradedBraiding G₁ G₃).hom ▷ G₂) k))
    _ =
      (𝟙 (G₁ p) ⊗ₘ signedGradedBraidingComponent G₂ G₃ q r) ≫
          (α_ (G₁ p) (G₃ r) (G₂ q)).inv ≫
            (signedGradedBraidingComponent G₁ G₃ p r ⊗ₘ 𝟙 (G₂ q)) ≫
              GradedObject.Monoidal.ιTensorObj₃' G₃ G₁ G₂ r p q k hswap := by
            simpa only [Category.assoc] using congrArg
              (fun u ↦
                (𝟙 (G₁ p) ⊗ₘ signedGradedBraidingComponent G₂ G₃ q r) ≫
                  (α_ (G₁ p) (G₃ r) (G₂ q)).inv ≫ u)
              (signedGradedBraiding_whisker_right_component G₁ G₃ G₂ p r q k hprq)
    _ =
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) q r •
        (G₁ p ◁ (β_ (G₂ q) (G₃ r)).hom)) ≫
          (α_ (G₁ p) (G₃ r) (G₂ q)).inv ≫
            (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r •
              (((β_ (G₁ p) (G₃ r)).hom) ▷ G₂ q)) ≫
                GradedObject.Monoidal.ιTensorObj₃' G₃ G₁ G₂ r p q k hswap := by
            rw [signedGradedBraidingComponent_whisker_left_eq G₂ G₁ G₃ q p r,
              signedGradedBraidingComponent_whisker_right_eq G₁ G₃ G₂ p r q]

/-- Helper for Lemma 15.58.1: the signed graded braiding satisfies the forward hexagon. -/
private theorem signedGradedBraiding_hexagon_forward
    (G₁ G₂ G₃ : GradedObject ℤ C) :
    (α_ G₁ G₂ G₃).hom ≫ (signedGradedBraiding G₁ (G₂ ⊗ G₃)).hom ≫ (α_ G₂ G₃ G₁).hom =
      (signedGradedBraiding G₁ G₂).hom ▷ G₃ ≫ (α_ G₂ G₁ G₃).hom ≫
        G₂ ◁ (signedGradedBraiding G₁ G₃).hom := by
  -- Restrict to each degree and then to each triple summand, where the statement becomes the
  -- component calculation proved just above.
  funext k
  apply GradedObject.Monoidal.tensorObj₃'_ext
  intro p q r h
  simpa [Category.assoc] using
    signedGradedBraiding_hexagon_forward_component G₁ G₂ G₃ p q r k h

/-- Helper for Lemma 15.58.1: on a fixed `(p,q,r)`-summand, the reverse hexagon for the signed
graded braiding reduces to the ordinary braided hexagon together with the multiplicativity of the
Koszul sign in the left variable. -/
@[reassoc]
private theorem signedGradedBraiding_hexagon_reverse_component
    (G₁ G₂ G₃ : GradedObject ℤ C) (p q r k : ℤ) (h : p + q + r = k) :
    GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫
      ((α_ G₁ G₂ G₃).inv ≫ (signedGradedBraiding (G₁ ⊗ G₂) G₃).hom ≫
        (α_ G₃ G₁ G₂).inv) k =
    GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫
      ((G₁ ◁ (signedGradedBraiding G₂ G₃).hom) ≫ (α_ G₁ G₃ G₂).inv ≫
        (signedGradedBraiding G₁ G₃).hom ▷ G₂) k := by
  let hswap : r + p + q = k := by
    simpa [add_assoc, add_comm, add_left_comm] using h
  -- Route correction: normalize both sides to the same `(r,p,q)` summand target, then apply the
  -- ordinary reverse hexagon in `C` with the two separated Koszul signs.
  calc
    GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫
        ((α_ G₁ G₂ G₃).inv ≫ (signedGradedBraiding (G₁ ⊗ G₂) G₃).hom ≫
          (α_ G₃ G₁ G₂).inv) k =
      (α_ (G₁ p) (G₂ q) (G₃ r)).inv ≫
          (GradedObject.Monoidal.ιTensorObj₃' G₁ G₂ G₃ p q r k h ≫
            (signedGradedBraiding (G₁ ⊗ G₂) G₃).hom k ≫ (α_ G₃ G₁ G₂).inv k) := by
            -- Rewrite the first inverse associator componentwise before touching the signed braiding.
            simpa only [Category.assoc] using
              (graded_associator_inv_component_assoc G₁ G₂ G₃ p q r k h
                ((signedGradedBraiding (G₁ ⊗ G₂) G₃).hom k ≫ (α_ G₃ G₁ G₂).inv k))
    _ =
      (α_ (G₁ p) (G₂ q) (G₃ r)).inv ≫
          (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r •
            (β_ (G₁ p ⊗ G₂ q) (G₃ r)).hom) ≫
              (α_ (G₃ r) (G₁ p) (G₂ q)).inv ≫
                GradedObject.Monoidal.ιTensorObj₃' G₃ G₁ G₂ r p q k hswap := by
            -- Then apply the total-component normalization for the braiding with tensor on the left.
            rw [signedGradedBraiding_tensor_left_total_component G₁ G₂ G₃ p q r k h]
    _ =
      (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) q r •
        (G₁ p ◁ (β_ (G₂ q) (G₃ r)).hom)) ≫
          (α_ (G₁ p) (G₃ r) (G₂ q)).inv ≫
            (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r •
              (((β_ (G₁ p) (G₃ r)).hom) ▷ G₂ q)) ≫
                GradedObject.Monoidal.ιTensorObj₃' G₃ G₁ G₂ r p q k hswap := by
            -- Now the ordinary reverse hexagon in `C` applies directly to the exposed summand.
            simpa only [Category.assoc] using congrArg
              (fun u ↦ u ≫ GradedObject.Monoidal.ιTensorObj₃' G₃ G₁ G₂ r p q k hswap)
              (scaled_braiding_hexagon_reverse (G₁ p) (G₂ q) (G₃ r)
                (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) (p + q) r)
                (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) q r)
                (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p r)
                (by simpa [mul_comm] using complexShape_sigma_add_left p q r))
    _ =
      GradedObject.Monoidal.ιTensorObj₃ G₁ G₂ G₃ p q r k h ≫
        ((G₁ ◁ (signedGradedBraiding G₂ G₃).hom) ≫ (α_ G₁ G₃ G₂).inv ≫
          (signedGradedBraiding G₁ G₃).hom ▷ G₂) k := by
            -- Finally fold the normalized right-hand side back into the graded-hexagon target.
            simpa only [Category.assoc] using
              (signedGradedBraiding_reverse_rhs_total_component G₁ G₂ G₃ p q r k h).symm

/-- Helper for Lemma 15.58.1: the signed graded braiding satisfies the reverse hexagon. -/
private theorem signedGradedBraiding_hexagon_reverse
    (G₁ G₂ G₃ : GradedObject ℤ C) :
    (α_ G₁ G₂ G₃).inv ≫ (signedGradedBraiding (G₁ ⊗ G₂) G₃).hom ≫ (α_ G₃ G₁ G₂).inv =
      G₁ ◁ (signedGradedBraiding G₂ G₃).hom ≫ (α_ G₁ G₃ G₂).inv ≫
        (signedGradedBraiding G₁ G₃).hom ▷ G₂ := by
  -- Restrict to each degree and then to each triple summand, where the statement becomes the
  -- component calculation proved just above.
  funext k
  apply GradedObject.Monoidal.tensorObj₃_ext
  intro p q r h
  simpa [Category.assoc] using
    signedGradedBraiding_hexagon_reverse_component G₁ G₂ G₃ p q r k h

/-- Helper for Lemma 15.58.1: the signed graded braiding packages a braided structure on graded
objects, which is the faithful target for the cochain-complex braiding. -/
private noncomputable abbrev signedGradedBraidedCategory :
    BraidedCategory (GradedObject ℤ C) where
  braiding := signedGradedBraiding
  braiding_naturality_left := by
    intro G₁ G₂ f G₃
    simpa using signedGradedBraiding_naturality_left (G₃ := G₃) f
  braiding_naturality_right := by
    intro G₁ G₂ G₃ f
    simpa using signedGradedBraiding_naturality_right G₁ f
  hexagon_forward := by
    intro G₁ G₂ G₃
    simpa using signedGradedBraiding_hexagon_forward G₁ G₂ G₃
  hexagon_reverse := by
    intro G₁ G₂ G₃
    simpa using signedGradedBraiding_hexagon_reverse G₁ G₂ G₃

/-- Helper for Lemma 15.58.1: the signed graded braiding is symmetric. -/
private noncomputable abbrev signedGradedSymmetricCategory :
    SymmetricCategory (GradedObject ℤ C) where
  toBraidedCategory := signedGradedBraidedCategory
  symmetry G₁ G₂ := signedGradedBraiding_hom_inv_id G₁ G₂

attribute [local instance] signedGradedBraidedCategory signedGradedSymmetricCategory

/-- The tensor braiding on cochain complexes induced by the pointwise braiding and the canonical
total-complex flip. -/
noncomputable def tensorBraiding
    (K L : Cpx) :
    K ⊗ L ≅ L ⊗ K :=
  (HomologicalComplex.mapBifunctorFlipIso K L (curriedTensor C) (up ℤ)).symm ≪≫
    pointwiseTensorBraidingIso K L

/-- Helper for Lemma 15.58.1: the total-complex flip rewrites a `(p,q)`-summand inclusion written
with `ιTensorObj`, and the rewritten form is stable under an arbitrary postcomposition. -/
@[reassoc]
private theorem iTensorObj_mapBifunctorFlipIso_inv_postcomp
    (K L : Cpx) (p q n : ℤ) (h : p + q = n) {Z : C}
    (u : (HomologicalComplex.mapBifunctor L K (curriedTensor C).flip (up ℤ)).X n ⟶ Z) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        (HomologicalComplex.mapBifunctorFlipIso K L (curriedTensor C) (up ℤ)).inv.f n ≫ u =
      ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
        (HomologicalComplex.ιMapBifunctor L K (curriedTensor C).flip (up ℤ) q p n
          (by simpa [add_comm] using h) ≫ u) := by
  -- The owner theorem is stated on `ιMapBifunctor`; we cross the `ιTensorObj` abbrev once here.
  calc
    HomologicalComplex.ιTensorObj K L p q n h ≫
        (HomologicalComplex.mapBifunctorFlipIso K L (curriedTensor C) (up ℤ)).inv.f n ≫ u
      =
        (ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
          HomologicalComplex.ιMapBifunctor L K (curriedTensor C).flip (up ℤ) q p n
            (by simpa [add_comm] using h)) ≫ u := by
          simpa only [HomologicalComplex.ιTensorObj] using
            (HomologicalComplex.ι_mapBifunctorFlipIso_inv_assoc
              K L (curriedTensor C) (up ℤ) p q n h u)
    _ =
        ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q •
          (HomologicalComplex.ιMapBifunctor L K (curriedTensor C).flip (up ℤ) q p n
            (by simpa [add_comm] using h) ≫ u) := by
          rw [Linear.units_smul_comp]

/-- Helper for Lemma 15.58.1: on each `(p,q)`-summand, the cochain-complex braiding is the
expected Koszul-signed swap. -/
@[reassoc]
private theorem tensorBraiding_hom_app
    (K L : Cpx) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ (tensorBraiding K L).hom.f n =
      signedGradedBraidingComponent K.X L.X p q ≫
        HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h) := by
  -- Route correction: the missing step is the explicit reassociation across
  -- `mapBifunctorFlipIso`, not a new transport target.
  let σ : ℤˣ := ComplexShape.σ (up ℤ) (up ℤ) (up ℤ) p q
  let i :
      K.X p ⊗ L.X q ⟶
        (HomologicalComplex.mapBifunctor L K (curriedTensor C).flip (up ℤ)).X n :=
    HomologicalComplex.ιMapBifunctor L K (curriedTensor C).flip (up ℤ) q p n
      (by simpa [add_comm] using h)
  let g :
      (HomologicalComplex.mapBifunctor L K (curriedTensor C).flip (up ℤ)).X n ⟶
        (L ⊗ K).X n :=
    (pointwiseTensorBraidingIso K L).hom.f n
  have hflip :
      HomologicalComplex.ιTensorObj K L p q n h ≫
          (HomologicalComplex.mapBifunctorFlipIso K L (curriedTensor C) (up ℤ)).inv.f n ≫ g =
        σ • (i ≫ g) := by
    calc
      HomologicalComplex.ιTensorObj K L p q n h ≫
          (HomologicalComplex.mapBifunctorFlipIso K L (curriedTensor C) (up ℤ)).inv.f n ≫ g =
        (σ • i) ≫ g := by
          simpa [σ, i] using
            (iTensorObj_mapBifunctorFlipIso_inv_postcomp (C := C) K L p q n h g)
      _ = σ • (i ≫ g) := by
        exact Linear.units_smul_comp σ i g
  have hpoint :
      σ • (i ≫ g) =
        signedGradedBraidingComponent K.X L.X p q ≫
          HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h) := by
    have hbase :
        σ • (i ≫ g) =
          σ • ((((BraidedCategory.curriedBraidingNatIso C).app (K.X p)).app (L.X q)).hom ≫
            HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h)) :=
      congrArg (fun f ↦ σ • f) <|
        pointwiseTensorBraiding_hom_app (C := C) K L q p n (by simpa [add_comm] using h)
    have hsmul :
        σ • ((((BraidedCategory.curriedBraidingNatIso C).app (K.X p)).app (L.X q)).hom ≫
          HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h)) =
        signedGradedBraidingComponent K.X L.X p q ≫
          HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h) := by
      rw [← Linear.units_smul_comp]
      rfl
    exact hbase.trans hsmul
  simpa [tensorBraiding, σ, i, g, signedGradedBraidingComponent] using hflip.trans hpoint

private lemma forget_map_tensorBraiding
    (K L : Cpx) :
    forgetGraded.map (tensorBraiding K L).hom = (signedGradedBraiding K.X L.X).hom := by
  -- Both graded maps are determined by their restrictions to the `(p,q)`-summands.
  ext n
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q h
  -- The complex braiding and the signed graded braiding induce the same signed swap on each
  -- summand, so the descended degree-`n` maps coincide.
  calc
    GradedObject.Monoidal.ιTensorObj K.X L.X p q n h ≫ (forgetGraded.map (tensorBraiding K L).hom) n =
        signedGradedBraidingComponent K.X L.X p q ≫
          GradedObject.Monoidal.ιTensorObj L.X K.X q p n (by simpa [add_comm] using h) := by
      simpa [forgetGraded] using tensorBraiding_hom_app (C := C) K L p q n h
    _ =
        GradedObject.Monoidal.ιTensorObj K.X L.X p q n h ≫
          (signedGradedBraiding K.X L.X).hom n := by
      symm
      simpa [signedGradedBraiding] using
        signedGradedBraiding_hom_app (G₁ := K.X) (G₂ := L.X) p q n h

/-- Helper for Lemma 15.58.1: the induced monoidal comparison on the forgetful functor to graded
objects is the identity on tensor products. -/
@[simp]
private theorem forgetGraded_mu_eq_id
    (K L : Cpx) :
    Functor.LaxMonoidal.μ forgetGraded K L =
      𝟙 ((forgetGraded.obj K) ⊗ (forgetGraded.obj L)) :=
  rfl

/-- Helper for Lemma 15.58.1: the forgetful functor sends the cochain-complex braiding to the
signed graded braiding with its induced monoidal comparison inserted. -/
private theorem forgetGraded_mu_tensorBraiding
    (K L : Cpx) :
    Functor.LaxMonoidal.μ forgetGraded K L ≫ forgetGraded.map (tensorBraiding K L).hom =
      (signedGradedBraiding K.X L.X).hom ≫ Functor.LaxMonoidal.μ forgetGraded L K := by
  -- The induced monoidal structure on `forgetGraded` has identity tensor comparisons, so this is
  -- exactly the already-proved summandwise comparison.
  convert forget_map_tensorBraiding (C := C) K L using 1
  · rw [forgetGraded_mu_eq_id]
    exact Category.id_comp _
  · rw [forgetGraded_mu_eq_id]
    exact Category.comp_id _

/-- Helper for Lemma 15.58.1: the forgetful functor to graded objects is braided for the signed
graded symmetry. -/
noncomputable instance : BraidedCategory Cpx := by
  -- Route correction: the remaining faithful pullback witness is the explicit `μ forgetGraded`
  -- comparison, not a new transport argument on cochain complexes.
  exact BraidedCategory.ofFaithful forgetGraded tensorBraiding
    (forgetGraded_mu_tensorBraiding (C := C))

-- The induced monoidal forgetful functor is braided because it preserves the chosen braidings up
-- to the identity tensor comparison computed above.
noncomputable instance : (HomologicalComplex.forget C (up ℤ)).Braided := by
  refine
    { braided := ?_ }
  intro X Y
  simpa [forgetGraded] using forgetGraded_mu_tensorBraiding (C := C) X Y

/-- The canonical symmetric monoidal structure on cochain complexes extending the totalized
tensor product. -/
noncomputable instance cochainComplexSymmetricCategory : SymmetricCategory Cpx :=
  by
    -- After packaging the faithful braided pullback, symmetry descends formally from the signed
    -- graded target because `forgetGraded` is now a faithful braided functor.
    let _ : (HomologicalComplex.forget C (up ℤ)).Braided := inferInstance
    exact SymmetricCategory.ofFaithful (HomologicalComplex.forget C (up ℤ))

/-- Lemma 15.58.1: cochain complexes, endowed with the totalized tensor product and the induced
Koszul-signed symmetry, form a symmetric monoidal category; this specializes to `Comp(R)` for
modules over a commutative ring. -/
@[stacks 0FNI]
abbrev cochainComplex_symmetricCategory : SymmetricCategory Cpx :=
  cochainComplexSymmetricCategory

end
