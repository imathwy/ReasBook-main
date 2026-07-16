import stacks_proof.stacks_project.Chap04.Lemma_4_35_17
import stacks_proof.stacks_project.Chap04.Lemma_4_2_18
import stacks_proof.stacks_project.Chap04.Definition_4_2_17
import stacks_proof.stacks_project.Chap04.Definition_4_35_1
import stacks_proof.stacks_project.Chap04.Lemma_4_33_3
import stacks_proof.stacks_project.Chap04.Lemma_4_33_7
import stacks_proof.stacks_project.Chap04.Lemma_4_33_8
import stacks_proof.stacks_project.Chap07.Definition_7_13_1
import stacks_proof.stacks_project.Chap08.Definition_8_2_2
import stacks_proof.stacks_project.Chap08.Definition_8_3_5
import stacks_proof.stacks_project.Chap08.Definition_8_5_5
import stacks_proof.stacks_project.Chap08.Lemma_8_5_3_PullbackNaturality
import stacks_proof.stacks_project.Chap08.Lemma_8_4_2
import stacks_proof.stacks_project.Chap08.Lemma_8_10_1
import stacks_proof.stacks_project.Chap08.Lemma_8_10_4
import stacks_proof.stacks_project.Chap08.Lemma_8_10_5.LiteralBaseReindex

universe uC uX vC vX

namespace CategoryTheory

open FibredCategoryMor
open FibredCategoryOver
open Functor IsStronglyCartesian
open Opposite
open StackInGroupoidsOver.Hom

section

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver J}

/-- Helper for Lemma 8.10.5: the counit-transported literal-base overlap map is the identity on
equal legs after the same reindex-and-pullback normalization. -/
theorem inherited_basis_forget_to_source_descent_hom_self
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i : ι}
    (f : Z ⟶ Yₛ.p.obj (Y i)) (hf : f ≫ Yₛ.p.map (g i) = q := by cat_disch) :
    inherited_basis_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f f hf hf = 𝟙 _ := by
  let ρ :=
    inherited_basis_target_slice_inverse_base_reindex_iso
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (Y := Y) (g := g) D q f hf
  have hρ : ρ.inv ≫ 𝟙 _ ≫ ρ.hom = 𝟙 _ := by
    simp [ρ, Category.assoc]
  rw [inherited_basis_forget_to_source_descent_hom]
  rw [inherited_basis_descent_hom_self_normalize
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) D
    (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
    (inherited_basis_target_slice_inverse_leg
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f hf)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f hf)]
  change
    (((canonicalFiberPseudofunctor Xₛ.p).mapId' (𝟙 Z).op.toLoc).inv.toNatTrans.app
        (((canonicalFiberPseudofunctor Xₛ.p).map f.op.toLoc).toFunctor.obj
          (inherited_source_fiber_obj (F := F) (D.obj i)))) ≫
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (ρ.inv ≫ 𝟙 _ ≫ ρ.hom) _ (𝟙 Z) (𝟙 Z) _ _ ≫
      (((canonicalFiberPseudofunctor Xₛ.p).mapId' (𝟙 Z).op.toLoc).hom.toNatTrans.app
        (((canonicalFiberPseudofunctor Xₛ.p).map f.op.toLoc).toFunctor.obj
        (inherited_source_fiber_obj (F := F) (D.obj i)))) =
    𝟙 _
  erw [hρ]
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  erw [((canonicalFiberPseudofunctor Xₛ.p).map
    (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q)).inv.left).op.toLoc).toFunctor.map_id]
  set M :=
    (((canonicalFiberPseudofunctor Xₛ.p).map f.op.toLoc).toFunctor.obj
      (inherited_source_fiber_obj (F := F) (D.obj i)))
  set ε := ((canonicalFiberPseudofunctor Xₛ.p).mapId' (𝟙 Z).op.toLoc
    (id (Eq.refl (𝟙 Z).op.toLoc)))
  let W : C :=
    (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).inverse ⋙
      (inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).functor).obj
      (Over.mk q)).left
  let c : W ⟶ Z :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q)).hom.left
  let cInv : Z ⟶ W :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q)).inv.left
  have hc_base : cInv ≫ c = 𝟙 Z := by
    simpa [c, cInv] using
      target_slice_counit_inv_left_comp (J := J) (Yₛ := Yₛ) q (𝟙 Z)
  have hc_comp : c.op.toLoc ≫ cInv.op.toLoc = (𝟙 Z).op.toLoc :=
    base_comp_toLoc_eq c cInv (𝟙 Z) hc_base
  have hA
      (h₁ h₂ : c.op.toLoc ≫ cInv.op.toLoc = (𝟙 Z).op.toLoc) :
      (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
            c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc h₁).hom.toNatTrans.app M) ≫
      (
        𝟙 (((canonicalFiberPseudofunctor Xₛ.p).map cInv.op.toLoc).toFunctor.obj
          (((canonicalFiberPseudofunctor Xₛ.p).map c.op.toLoc).toFunctor.obj M)) ≫
        (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
            c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc h₂).inv.toNatTrans.app M)) =
        𝟙 _ := by
    have hh : h₂ = h₁ := Subsingleton.elim _ _
    cases hh
    let A := ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
      c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc h₁)
    calc
      A.hom.toNatTrans.app M ≫ (𝟙 _ ≫ A.inv.toNatTrans.app M) =
          A.hom.toNatTrans.app M ≫ A.inv.toNatTrans.app M := by
            simp only [Category.id_comp]
      _ = 𝟙 _ := by
            simpa [A] using (Iso.hom_inv_id_app (Cat.Hom.toNatIso A) M)
  have hε : ε.inv.toNatTrans.app M ≫ ε.hom.toNatTrans.app M = 𝟙 M := by
    change (ε.inv ≫ ε.hom).toNatTrans.app M = 𝟙 M
    rw [ε.inv_hom_id]
    rfl
  change
    ε.inv.toNatTrans.app M ≫
      ((((canonicalFiberPseudofunctor Xₛ.p).mapComp'
          c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc _).hom.toNatTrans.app M) ≫
        (𝟙 (((canonicalFiberPseudofunctor Xₛ.p).map cInv.op.toLoc).toFunctor.obj
          (((canonicalFiberPseudofunctor Xₛ.p).map c.op.toLoc).toFunctor.obj M)) ≫
          (((canonicalFiberPseudofunctor Xₛ.p).mapComp'
            c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc _).inv.toNatTrans.app M))) ≫
      ε.hom.toNatTrans.app M =
    𝟙 M
  conv_lhs =>
    arg 2
    arg 1
    rw [hA]
  simpa [Category.assoc] using hε

/-- Helper for Lemma 8.10.5: before the outer literal-base pullback shell is reassembled, the
lifted source overlap maps already satisfy the source cocycle relation on the chosen upstairs
overlap object over `q`. -/
theorem inherited_basis_forget_to_source_descent_hom_comp_middle
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ i₃ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (f₃ : Z ⟶ Yₛ.p.obj (Y i₃))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch)
    (hf₃ : f₃ ≫ Yₛ.p.map (g i₃) = q := by cat_disch) :
    inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D
        (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
        (inherited_basis_target_slice_inverse_leg
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
        (inherited_basis_target_slice_inverse_leg
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂) ≫
      inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D
        (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
        (inherited_basis_target_slice_inverse_leg
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
        (inherited_basis_target_slice_inverse_leg
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃) =
      inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D
        (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
        (inherited_basis_target_slice_inverse_leg
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
        (inherited_basis_target_slice_inverse_leg
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃) := by
  -- The chosen lifted overlap legs all live over the same upstairs overlap object, so the
  -- source-side cocycle theorem applies before any literal-base transport is reintroduced.
  simpa only using
    inherited_basis_descent_hom_comp_normalize
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) D
      (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
      (inherited_basis_target_slice_inverse_leg
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
      (inherited_basis_target_slice_inverse_leg
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
      (inherited_basis_target_slice_inverse_leg
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃)
      (inherited_basis_target_slice_inverse_leg_w
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
      (inherited_basis_target_slice_inverse_leg_w
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
      (inherited_basis_target_slice_inverse_leg_w
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃)

/-- Helper for Lemma 8.10.5: composing two morphisms wrapped by the same identity-pullback and
counit-reindexing shell cancels the middle shell, reducing the statement to the middle maps. -/
theorem conjugated_iso_shell_comp
    {𝒟 : Type*} [Category 𝒟]
    {M₁ M₂ M₃ I₁ I₂ I₃ B₁ B₂ B₃ S₁ S₂ S₃ : 𝒟}
    (ε₁ : I₁ ≅ M₁) (ε₂ : I₂ ≅ M₂) (ε₃ : I₃ ≅ M₃)
    (A₁ : I₁ ≅ B₁) (A₂ : I₂ ≅ B₂) (A₃ : I₃ ≅ B₃)
    (ρ₁ : S₁ ≅ B₁) (ρ₂ : S₂ ≅ B₂) (ρ₃ : S₃ ≅ B₃)
    (u₁₂ : S₁ ⟶ S₂) (u₂₃ : S₂ ⟶ S₃) (u₁₃ : S₁ ⟶ S₃)
    (hmid : u₁₂ ≫ u₂₃ = u₁₃) :
    (ε₁.inv ≫ A₁.hom ≫ ρ₁.inv ≫ u₁₂ ≫ ρ₂.hom ≫ A₂.inv ≫ ε₂.hom) ≫
      (ε₂.inv ≫ A₂.hom ≫ ρ₂.inv ≫ u₂₃ ≫ ρ₃.hom ≫ A₃.inv ≫ ε₃.hom) =
    ε₁.inv ≫ A₁.hom ≫ ρ₁.inv ≫ u₁₃ ≫ ρ₃.hom ≫ A₃.inv ≫ ε₃.hom := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hmid]

/-- Helper for Lemma 8.10.5: the same shell cancellation, in the unassociated form produced by
expanding the two transported overlap maps before cancelling the middle identity-pullback shell. -/
theorem conjugated_iso_shell_comp_expanded
    {𝒟 : Type*} [Category 𝒟]
    {M₁ M₂ M₃ I₁ I₂ I₃ B₁ B₂ B₃ S₁ S₂ S₃ : 𝒟}
    (ε₁ : I₁ ≅ M₁) (ε₂ : I₂ ≅ M₂) (ε₃ : I₃ ≅ M₃)
    (A₁ : I₁ ≅ B₁) (A₂ : I₂ ≅ B₂) (A₃ : I₃ ≅ B₃)
    (ρ₁ : S₁ ≅ B₁) (ρ₂ : S₂ ≅ B₂) (ρ₃ : S₃ ≅ B₃)
    (u₁₂ : S₁ ⟶ S₂) (u₂₃ : S₂ ⟶ S₃) (u₁₃ : S₁ ⟶ S₃)
    (hmid : u₁₂ ≫ u₂₃ = u₁₃) :
    ε₁.inv ≫ (A₁.hom ≫ (ρ₁.inv ≫ u₁₂ ≫ ρ₂.hom) ≫ A₂.inv) ≫
          ε₂.hom ≫
        ε₂.inv ≫ (A₂.hom ≫ (ρ₂.inv ≫ u₂₃ ≫ ρ₃.hom) ≫ A₃.inv) ≫ ε₃.hom =
      ε₁.inv ≫ (A₁.hom ≫ (ρ₁.inv ≫ u₁₃ ≫ ρ₃.hom) ≫ A₃.inv) ≫ ε₃.hom := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hmid]

/-- Helper for Lemma 8.10.5: shell cancellation when the functor image of each conjugated
middle map has already been expanded as three mapped factors. -/
theorem conjugated_iso_shell_comp_mapped
    {𝒟 : Type*} [Category 𝒟]
    {M₁ M₂ M₃ I₁ I₂ I₃ B₁ B₂ B₃ S₁ S₂ S₃ : 𝒟}
    (ε₁ : I₁ ≅ M₁) (ε₂ : I₂ ≅ M₂) (ε₃ : I₃ ≅ M₃)
    (A₁ : I₁ ≅ B₁) (A₂ : I₂ ≅ B₂) (A₃ : I₃ ≅ B₃)
    (ρ₁ : S₁ ≅ B₁) (ρ₂ : S₂ ≅ B₂) (ρ₃ : S₃ ≅ B₃)
    (u₁₂ : S₁ ⟶ S₂) (u₂₃ : S₂ ⟶ S₃) (u₁₃ : S₁ ⟶ S₃)
    (hmid : u₁₂ ≫ u₂₃ = u₁₃) :
    ε₁.inv ≫
        (A₁.hom ≫ (ρ₁.inv ≫ u₁₂ ≫ ρ₂.hom) ≫ A₂.inv) ≫
          ε₂.hom ≫
            ε₂.inv ≫
              (A₂.hom ≫ (ρ₂.inv ≫ u₂₃ ≫ ρ₃.hom) ≫ A₃.inv) ≫ ε₃.hom =
      ε₁.inv ≫
        (A₁.hom ≫ (ρ₁.inv ≫ u₁₃ ≫ ρ₃.hom) ≫ A₃.inv) ≫ ε₃.hom := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hmid]

/-- Helper for Lemma 8.10.5: an equality of middle morphisms remains true after wrapping both
sides in the identity-pullback and counit-reindexing shell used by the literal-base forgetful
overlap maps. -/
theorem conjugated_iso_shell_eq
    {𝒟 : Type*} [Category 𝒟]
    {M₁ M₂ I₁ I₂ B₁ B₂ S₁ S₂ : 𝒟}
    (ε₁ : I₁ ≅ M₁) (ε₂ : I₂ ≅ M₂)
    (A₁ : I₁ ≅ B₁) (A₂ : I₂ ≅ B₂)
    (ρ₁ : S₁ ≅ B₁) (ρ₂ : S₂ ≅ B₂)
    (u v : S₁ ⟶ S₂) (hmid : u = v) :
    ε₁.inv ≫ (A₁.hom ≫ (ρ₁.inv ≫ u ≫ ρ₂.hom) ≫ A₂.inv) ≫ ε₂.hom =
      ε₁.inv ≫ (A₁.hom ≫ (ρ₁.inv ≫ v ≫ ρ₂.hom) ≫ A₂.inv) ≫ ε₂.hom := by
  -- The outer shell is functorial in the middle arrow, so the refinement step can be
  -- rewritten before the expensive literal-base normal form is expanded.
  rw [hmid]

/-- Helper for Lemma 8.10.5: a componentwise naturality square remains commutative after the
same identity-pullback and counit-reindexing shell used for literal-base overlap maps. -/
theorem conjugated_iso_shell_comm_mapped
    {𝒟 : Type*} [Category 𝒟]
    {M₁ M₂ N₁ N₂ I₁ I₂ J₁ J₂ B₁ B₂ C₁ C₂ S₁ S₂ T₁ T₂ : 𝒟}
    (εM₁ : I₁ ≅ M₁) (εM₂ : I₂ ≅ M₂) (εN₁ : J₁ ≅ N₁) (εN₂ : J₂ ≅ N₂)
    (AM₁ : I₁ ≅ B₁) (AM₂ : I₂ ≅ B₂) (AN₁ : J₁ ≅ C₁) (AN₂ : J₂ ≅ C₂)
    (ρM₁ : S₁ ≅ B₁) (ρM₂ : S₂ ≅ B₂) (ρN₁ : T₁ ≅ C₁) (ρN₂ : T₂ ≅ C₂)
    (αS₁ : S₁ ⟶ T₁) (αS₂ : S₂ ⟶ T₂)
    (uM : S₁ ⟶ S₂) (uN : T₁ ⟶ T₂)
    (hmid : αS₁ ≫ uN = uM ≫ αS₂) :
    εM₁.inv ≫
        (AM₁.hom ≫ (ρM₁.inv ≫ αS₁ ≫ ρN₁.hom) ≫ AN₁.inv) ≫
          εN₁.hom ≫
            εN₁.inv ≫
              (AN₁.hom ≫ (ρN₁.inv ≫ uN ≫ ρN₂.hom) ≫ AN₂.inv) ≫ εN₂.hom =
      εM₁.inv ≫
        (AM₁.hom ≫ (ρM₁.inv ≫ uM ≫ ρM₂.hom) ≫ AM₂.inv) ≫
          εM₂.hom ≫
            εM₂.inv ≫
              (AM₂.hom ≫ (ρM₂.inv ≫ αS₂ ≫ ρN₂.hom) ≫ AN₂.inv) ≫ εN₂.hom := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hmid]

/-- Helper for Lemma 8.10.5: if the two outer component maps commute through the
identity-pullback, `mapComp'`, and reindexing shells, then the transported square is reduced to
the middle naturality square. -/
theorem conjugated_iso_shell_comm_outer
    {𝒟 : Type*} [Category 𝒟]
    {M₁ M₂ N₁ N₂ I₁ I₂ J₁ J₂ B₁ B₂ C₁ C₂ S₁ S₂ T₁ T₂ : 𝒟}
    (εM₁ : I₁ ≅ M₁) (εM₂ : I₂ ≅ M₂) (εN₁ : J₁ ≅ N₁) (εN₂ : J₂ ≅ N₂)
    (AM₁ : I₁ ≅ B₁) (AM₂ : I₂ ≅ B₂) (AN₁ : J₁ ≅ C₁) (AN₂ : J₂ ≅ C₂)
    (ρM₁ : S₁ ≅ B₁) (ρM₂ : S₂ ≅ B₂) (ρN₁ : T₁ ≅ C₁) (ρN₂ : T₂ ≅ C₂)
    (αM₁ : M₁ ⟶ N₁) (αM₂ : M₂ ⟶ N₂)
    (αS₁ : S₁ ⟶ T₁) (αS₂ : S₂ ⟶ T₂)
    (uM : S₁ ⟶ S₂) (uN : T₁ ⟶ T₂)
    (hleft :
      αM₁ ≫ εN₁.inv ≫ AN₁.hom ≫ ρN₁.inv =
        εM₁.inv ≫ AM₁.hom ≫ ρM₁.inv ≫ αS₁)
    (hright :
      αS₂ ≫ ρN₂.hom ≫ AN₂.inv ≫ εN₂.hom =
        ρM₂.hom ≫ AM₂.inv ≫ εM₂.hom ≫ αM₂)
    (hmid : αS₁ ≫ uN = uM ≫ αS₂) :
    αM₁ ≫ εN₁.inv ≫ AN₁.hom ≫ ρN₁.inv ≫ uN ≫ ρN₂.hom ≫ AN₂.inv ≫
        εN₂.hom =
      εM₁.inv ≫ AM₁.hom ≫ ρM₁.inv ≫ uM ≫ ρM₂.hom ≫ AM₂.inv ≫
        εM₂.hom ≫ αM₂ := by
  calc
    αM₁ ≫ εN₁.inv ≫ AN₁.hom ≫ ρN₁.inv ≫ uN ≫ ρN₂.hom ≫ AN₂.inv ≫
        εN₂.hom =
      (αM₁ ≫ εN₁.inv ≫ AN₁.hom ≫ ρN₁.inv) ≫ uN ≫ ρN₂.hom ≫ AN₂.inv ≫
          εN₂.hom := by
        simp only [Category.assoc]
    _ = (εM₁.inv ≫ AM₁.hom ≫ ρM₁.inv ≫ αS₁) ≫ uN ≫
          ρN₂.hom ≫ AN₂.inv ≫ εN₂.hom := by
        rw [hleft]
    _ = εM₁.inv ≫ AM₁.hom ≫ ρM₁.inv ≫ (αS₁ ≫ uN) ≫
          ρN₂.hom ≫ AN₂.inv ≫ εN₂.hom := by
        simp only [Category.assoc]
    _ = εM₁.inv ≫ AM₁.hom ≫ ρM₁.inv ≫ (uM ≫ αS₂) ≫
          ρN₂.hom ≫ AN₂.inv ≫ εN₂.hom := by
        rw [hmid]
    _ = εM₁.inv ≫ AM₁.hom ≫ ρM₁.inv ≫ uM ≫
          (αS₂ ≫ ρN₂.hom ≫ AN₂.inv ≫ εN₂.hom) := by
        simp only [Category.assoc]
    _ = εM₁.inv ≫ AM₁.hom ≫ ρM₁.inv ≫ uM ≫
          (ρM₂.hom ≫ AM₂.inv ≫ εM₂.hom ≫ αM₂) := by
        rw [hright]
    _ = εM₁.inv ≫ AM₁.hom ≫ ρM₁.inv ≫ uM ≫ ρM₂.hom ≫ AM₂.inv ≫
        εM₂.hom ≫ αM₂ := by
        simp only [Category.assoc]

/-- Helper for Lemma 8.10.5: the same outer naturality shell with the parenthesization produced
by unfolding `pullHom`. -/
theorem conjugated_iso_shell_comm_outer_expanded
    {𝒟 : Type*} [Category 𝒟]
    {M₁ M₂ N₁ N₂ I₁ I₂ J₁ J₂ B₁ B₂ C₁ C₂ S₁ S₂ T₁ T₂ : 𝒟}
    (εM₁ : I₁ ≅ M₁) (εM₂ : I₂ ≅ M₂) (εN₁ : J₁ ≅ N₁) (εN₂ : J₂ ≅ N₂)
    (AM₁ : I₁ ≅ B₁) (AM₂ : I₂ ≅ B₂) (AN₁ : J₁ ≅ C₁) (AN₂ : J₂ ≅ C₂)
    (ρM₁ : S₁ ≅ B₁) (ρM₂ : S₂ ≅ B₂) (ρN₁ : T₁ ≅ C₁) (ρN₂ : T₂ ≅ C₂)
    (αM₁ : M₁ ⟶ N₁) (αM₂ : M₂ ⟶ N₂)
    (αS₁ : S₁ ⟶ T₁) (αS₂ : S₂ ⟶ T₂)
    (uM : S₁ ⟶ S₂) (uN : T₁ ⟶ T₂)
    (hleft :
      αM₁ ≫ εN₁.inv ≫ AN₁.hom ≫ ρN₁.inv =
        εM₁.inv ≫ AM₁.hom ≫ ρM₁.inv ≫ αS₁)
    (hright :
      αS₂ ≫ ρN₂.hom ≫ AN₂.inv ≫ εN₂.hom =
        ρM₂.hom ≫ AM₂.inv ≫ εM₂.hom ≫ αM₂)
    (hmid : αS₁ ≫ uN = uM ≫ αS₂) :
    αM₁ ≫ εN₁.inv ≫
        ((AN₁.hom ≫ ((ρN₁.inv ≫ uN ≫ ρN₂.hom) ≫ AN₂.inv)) ≫ εN₂.hom) =
      εM₁.inv ≫
        ((AM₁.hom ≫ ((ρM₁.inv ≫ uM ≫ ρM₂.hom) ≫ AM₂.inv)) ≫ εM₂.hom) ≫
        αM₂ := by
  simpa only [Category.assoc] using
    conjugated_iso_shell_comm_outer
      εM₁ εM₂ εN₁ εN₂ AM₁ AM₂ AN₁ AN₂ ρM₁ ρM₂ ρN₁ ρN₂
      αM₁ αM₂ αS₁ αS₂ uM uN hleft hright hmid

/-- Helper for Lemma 8.10.5: the same expanded shell with the right boundary grouped as it is
produced by unfolding `inherited_basis_forget_to_source_descent_hom`. -/
theorem conjugated_iso_shell_comm_outer_pullHom_grouped
    {𝒟 : Type*} [Category 𝒟]
    {M₁ M₂ N₁ N₂ I₁ I₂ J₁ J₂ B₁ B₂ C₁ C₂ S₁ S₂ T₁ T₂ : 𝒟}
    (εM₁ : I₁ ≅ M₁) (εM₂ : I₂ ≅ M₂) (εN₁ : J₁ ≅ N₁) (εN₂ : J₂ ≅ N₂)
    (AM₁ : I₁ ≅ B₁) (AM₂ : I₂ ≅ B₂) (AN₁ : J₁ ≅ C₁) (AN₂ : J₂ ≅ C₂)
    (ρM₁ : S₁ ≅ B₁) (ρM₂ : S₂ ≅ B₂) (ρN₁ : T₁ ≅ C₁) (ρN₂ : T₂ ≅ C₂)
    (αM₁ : M₁ ⟶ N₁) (αM₂ : M₂ ⟶ N₂)
    (αS₁ : S₁ ⟶ T₁) (αS₂ : S₂ ⟶ T₂)
    (uM : S₁ ⟶ S₂) (uN : T₁ ⟶ T₂)
    (hleft :
      αM₁ ≫ εN₁.inv ≫ AN₁.hom ≫ ρN₁.inv =
        εM₁.inv ≫ AM₁.hom ≫ ρM₁.inv ≫ αS₁)
    (hright :
      αS₂ ≫ ρN₂.hom ≫ AN₂.inv ≫ εN₂.hom =
        ρM₂.hom ≫ AM₂.inv ≫ εM₂.hom ≫ αM₂)
    (hmid : αS₁ ≫ uN = uM ≫ αS₂) :
    αM₁ ≫ εN₁.inv ≫
        ((AN₁.hom ≫ ((ρN₁.inv ≫ uN ≫ ρN₂.hom) ≫ AN₂.inv)) ≫ εN₂.hom) =
      (εM₁.inv ≫
        ((AM₁.hom ≫ ((ρM₁.inv ≫ uM ≫ ρM₂.hom) ≫ AM₂.inv)) ≫ εM₂.hom)) ≫
        αM₂ := by
  simpa only [Category.assoc] using
    conjugated_iso_shell_comm_outer
      εM₁ εM₂ εN₁ εN₂ AM₁ AM₂ AN₁ AN₂ ρM₁ ρM₂ ρN₁ ρN₂
      αM₁ αM₂ αS₁ αS₂ uM uN hleft hright hmid

/-- Helper for Lemma 8.10.5: paste three consecutive naturality squares in a boundary shell. -/
theorem three_square_boundary_paste
    {𝒟 : Type*} [Category 𝒟]
    {A I J B C S T : 𝒟}
    (x : A ⟶ J) (e : A ⟶ I) (m : I ⟶ J)
    (AN : J ⟶ C) (AM : I ⟶ B) (n : B ⟶ C)
    (ρN : C ⟶ T) (ρM : B ⟶ S) (α : S ⟶ T)
    (h₁ : x = e ≫ m) (h₂ : m ≫ AN = AM ≫ n) (h₃ : n ≫ ρN = ρM ≫ α) :
    x ≫ AN ≫ ρN = e ≫ AM ≫ ρM ≫ α := by
  calc
    x ≫ AN ≫ ρN = (e ≫ m) ≫ AN ≫ ρN := by
      rw [h₁]
    _ = e ≫ (m ≫ AN) ≫ ρN := by
      simp only [Category.assoc]
    _ = e ≫ (AM ≫ n) ≫ ρN := by
      rw [h₂]
    _ = e ≫ AM ≫ (n ≫ ρN) := by
      simp only [Category.assoc]
    _ = e ≫ AM ≫ (ρM ≫ α) := by
      rw [h₃]
    _ = e ≫ AM ≫ ρM ≫ α := by
      simp only [Category.assoc]

/-- Helper for Lemma 8.10.5: paste three consecutive naturality squares in the opposite boundary
orientation. -/
theorem three_square_boundary_paste_right
    {𝒟 : Type*} [Category 𝒟]
    {A I J B C S T : 𝒟}
    (α : A ⟶ S) (ρN : S ⟶ C) (ρM : A ⟶ B)
    (n : B ⟶ C) (AN : C ⟶ J) (AM : B ⟶ I)
    (m : I ⟶ J) (e : J ⟶ T) (x : I ⟶ T)
    (h₁ : α ≫ ρN = ρM ≫ n) (h₂ : n ≫ AN = AM ≫ m) (h₃ : m ≫ e = x) :
    α ≫ ρN ≫ AN ≫ e = ρM ≫ AM ≫ x := by
  calc
    α ≫ ρN ≫ AN ≫ e = (α ≫ ρN) ≫ AN ≫ e := by
      simp only [Category.assoc]
    _ = (ρM ≫ n) ≫ AN ≫ e := by
      rw [h₁]
    _ = ρM ≫ (n ≫ AN) ≫ e := by
      simp only [Category.assoc]
    _ = ρM ≫ (AM ≫ m) ≫ e := by
      rw [h₂]
    _ = ρM ≫ AM ≫ (m ≫ e) := by
      simp only [Category.assoc]
    _ = ρM ≫ AM ≫ x := by
      rw [h₃]

/-- Helper for Lemma 8.10.5: the counit-transported literal-base overlap maps satisfy the cocycle
relation after the same normalization. -/
theorem inherited_basis_forget_to_source_descent_hom_comp
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    (D : ((canonicalFiberPseudofunctor (G F)).DescentData g))
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ i₃ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (f₃ : Z ⟶ Yₛ.p.obj (Y i₃))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch)
    (hf₃ : f₃ ≫ Yₛ.p.map (g i₃) = q := by cat_disch) :
    inherited_basis_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ hf₁ hf₂ ≫
      inherited_basis_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₂ f₃ hf₂ hf₃ =
    inherited_basis_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₃ hf₁ hf₃ := by
  have hmid :=
    inherited_basis_forget_to_source_descent_hom_comp_middle
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D q f₁ f₂ f₃ hf₁ hf₂ hf₃
  let W : C :=
    (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).inverse ⋙
      (inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).functor).obj
      (Over.mk q)).left
  let c : W ⟶ Z :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q)).hom.left
  let cInv : Z ⟶ W :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q)).inv.left
  have hc_base : cInv ≫ c = 𝟙 Z := by
    simpa [c, cInv] using
      target_slice_counit_inv_left_comp (J := J) (Yₛ := Yₛ) q (𝟙 Z)
  have hc_comp : c.op.toLoc ≫ cInv.op.toLoc = (𝟙 Z).op.toLoc :=
    base_comp_toLoc_eq c cInv (𝟙 Z) hc_base
  have hc_comp_raw :
      (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
          (Over.mk q)).hom.left).op.toLoc ≫
        (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
          (Over.mk q)).inv.left).op.toLoc =
        (𝟙 Z).op.toLoc := by
    simpa [c, cInv] using hc_comp
  let T := ((canonicalFiberPseudofunctor Xₛ.p).map cInv.op.toLoc).toFunctor
  let ε := ((canonicalFiberPseudofunctor Xₛ.p).mapId' (𝟙 Z).op.toLoc)
  let M₁ :=
    (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.obj
      (inherited_source_fiber_obj (F := F) (D.obj i₁)))
  let M₂ :=
    (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.obj
      (inherited_source_fiber_obj (F := F) (D.obj i₂)))
  let M₃ :=
    (((canonicalFiberPseudofunctor Xₛ.p).map f₃.op.toLoc).toFunctor.obj
      (inherited_source_fiber_obj (F := F) (D.obj i₃)))
  let A₁ := (Cat.Hom.toNatIso
    ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
      c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc (by aesop))).app M₁
  let A₂ := (Cat.Hom.toNatIso
    ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
      c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc (by aesop))).app M₂
  let A₃ := (Cat.Hom.toNatIso
    ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
      c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc (by aesop))).app M₃
  let ρ₁ := T.mapIso
    (inherited_basis_target_slice_inverse_base_reindex_iso
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (Y := Y) (g := g) D q f₁ hf₁)
  let ρ₂ := T.mapIso
    (inherited_basis_target_slice_inverse_base_reindex_iso
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (Y := Y) (g := g) D q f₂ hf₂)
  let ρ₃ := T.mapIso
    (inherited_basis_target_slice_inverse_base_reindex_iso
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (Y := Y) (g := g) D q f₃ hf₃)
  let d₁₂ := inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D
    (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
    (inherited_basis_target_slice_inverse_leg
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
  let d₂₃ := inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D
    (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
    (inherited_basis_target_slice_inverse_leg
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
    (inherited_basis_target_slice_inverse_leg
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃)
  let d₁₃ := inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D
    (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
    (inherited_basis_target_slice_inverse_leg
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₃ hf₃)
  have hmapComp
      (h : c.op.toLoc ≫ cInv.op.toLoc = (𝟙 Z).op.toLoc) :
      ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
        c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc h) =
      ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
        c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc hc_comp_raw) := by
    have hh : h = hc_comp_raw := Subsingleton.elim _ _
    cases hh
    rfl
  have hmapCompAny
      {U V W0 : LocallyDiscrete Cᵒᵖ}
      (a : U ⟶ V) (b : V ⟶ W0) (ab : U ⟶ W0)
      (h h' : a ≫ b = ab) :
      ((canonicalFiberPseudofunctor Xₛ.p).mapComp' a b ab h) =
        ((canonicalFiberPseudofunctor Xₛ.p).mapComp' a b ab h') := by
    have hh : h = h' := Subsingleton.elim _ _
    cases hh
    rfl
  have hmidT : T.map d₁₂ ≫ T.map d₂₃ = T.map d₁₃ := by
    dsimp [d₁₂, d₂₃, d₁₃]
    rw [← T.map_comp]
    exact congrArg T.map hmid
  simp only [inherited_basis_forget_to_source_descent_hom,
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Functor.map_comp,
    T, ε, M₁, M₂, M₃, A₁, A₂, A₃, ρ₁, ρ₂, ρ₃, d₁₂, d₂₃, d₁₃,
    Category.assoc]
  convert
    (conjugated_iso_shell_comp_mapped
      ((Cat.Hom.toNatIso ε).app M₁) ((Cat.Hom.toNatIso ε).app M₂)
      ((Cat.Hom.toNatIso ε).app M₃) A₁ A₂ A₃ ρ₁ ρ₂ ρ₃
      (T.map d₁₂) (T.map d₂₃) (T.map d₁₃) hmidT)
    using 1 <;>
    simp [T, ε, M₁, M₂, M₃, A₁, A₂, A₃, ρ₁, ρ₂, ρ₃, d₁₂, d₂₃, d₁₃,
      W, c, cInv, Category.assoc]

/-- Helper for Lemma 8.10.5: before the outer literal-base pullback shell is reassembled, the
lifted source overlap maps already satisfy the source componentwise compatibility relation on the
chosen upstairs overlap object over `q`. -/
theorem inherited_basis_forget_to_source_descent_literal_comm_middle
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    {D₁ D₂ : ((canonicalFiberPseudofunctor (G F)).DescentData g)}
    (φ : D₁ ⟶ D₂)
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Xₛ.p).map
        (Yₛ.p.map
          (inherited_basis_target_slice_inverse_leg
            (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)).op.toLoc).toFunctor.map
        ((inherited_source_fiber_forget (F := F) (Y i₁)).map (φ.hom i₁))) ≫
      inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D₂
        (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
        (inherited_basis_target_slice_inverse_leg
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
        (inherited_basis_target_slice_inverse_leg
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂) =
    inherited_basis_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D₁
        (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
        (inherited_basis_target_slice_inverse_leg
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
        (inherited_basis_target_slice_inverse_leg
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
        (inherited_basis_target_slice_inverse_leg_w
          (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂) ≫
      (((canonicalFiberPseudofunctor Xₛ.p).map
        (Yₛ.p.map
          (inherited_basis_target_slice_inverse_leg
            (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)).op.toLoc).toFunctor.map
        ((inherited_source_fiber_forget (F := F) (Y i₂)).map (φ.hom i₂))) := by
  -- The lifted overlap object over `q` is exactly an overlap in `Yₛ.S`, so the source-side
  -- compatibility theorem applies before the reindex isomorphisms and literal-base pullback shell.
  simpa only using
    inherited_basis_forget_to_source_descent_comm
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) φ
      (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
      (inherited_basis_target_slice_inverse_leg
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
      (inherited_basis_target_slice_inverse_leg
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
      (inherited_basis_target_slice_inverse_leg_w
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
      (inherited_basis_target_slice_inverse_leg_w
        (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)

/-- Helper for Lemma 8.10.5: componentwise morphisms of `G F` descent data remain compatible
with the counit-transported literal-base overlap maps in `Xₛ`. -/
theorem inherited_basis_forget_to_source_descent_literal_comm
    (F : Xₛ ⟶ Yₛ)
    [IsFibredInGroupoids (G F)]
    {ι : Type*} {y : Yₛ.S} {Y : ι → Yₛ.S} {g : ∀ i, Y i ⟶ y}
    {D₁ D₂ : ((canonicalFiberPseudofunctor (G F)).DescentData g)}
    (φ : D₁ ⟶ D₂)
    {Z : C} (q : Z ⟶ Yₛ.p.obj y) {i₁ i₂ : ι}
    (f₁ : Z ⟶ Yₛ.p.obj (Y i₁)) (f₂ : Z ⟶ Yₛ.p.obj (Y i₂))
    (hf₁ : f₁ ≫ Yₛ.p.map (g i₁) = q := by cat_disch)
    (hf₂ : f₂ ≫ Yₛ.p.map (g i₂) = q := by cat_disch) :
    (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map
        ((inherited_source_fiber_forget (F := F) (Y i₁)).map (φ.hom i₁))) ≫
      inherited_basis_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D₂ q f₁ f₂ hf₁ hf₂ =
    inherited_basis_forget_to_source_descent_hom
        (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D₁ q f₁ f₂ hf₁ hf₂ ≫
      (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map
        ((inherited_source_fiber_forget (F := F) (Y i₂)).map (φ.hom i₂))) := by
  let W : C :=
    (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).inverse ⋙
      (inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).functor).obj
      (Over.mk q)).left
  let c : W ⟶ Z :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q)).hom.left
  let cInv : Z ⟶ W :=
    ((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
      (Over.mk q)).inv.left
  have hc_base : cInv ≫ c = 𝟙 Z := by
    simpa [c, cInv] using
      target_slice_counit_inv_left_comp (J := J) (Yₛ := Yₛ) q (𝟙 Z)
  have hc_comp : c.op.toLoc ≫ cInv.op.toLoc = (𝟙 Z).op.toLoc :=
    base_comp_toLoc_eq c cInv (𝟙 Z) hc_base
  have hc_comp_raw :
      (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
          (Over.mk q)).hom.left).op.toLoc ≫
        (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
          (Over.mk q)).inv.left).op.toLoc =
        (𝟙 Z).op.toLoc := by
    simpa [c, cInv] using hc_comp
  have hmapComp
      (h : c.op.toLoc ≫ cInv.op.toLoc = (𝟙 Z).op.toLoc) :
      ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
        c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc h) =
      ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
        c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc hc_comp_raw) := by
    have hh : h = hc_comp_raw := Subsingleton.elim _ _
    cases hh
    rfl
  let T := ((canonicalFiberPseudofunctor Xₛ.p).map cInv.op.toLoc).toFunctor
  let ε := ((canonicalFiberPseudofunctor Xₛ.p).mapId' (𝟙 Z).op.toLoc
    (id (Eq.refl (𝟙 Z).op.toLoc)))
  let M₁ :=
    (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.obj
      (inherited_source_fiber_obj (F := F) (D₁.obj i₁)))
  let M₂ :=
    (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.obj
      (inherited_source_fiber_obj (F := F) (D₁.obj i₂)))
  let N₁ :=
    (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.obj
      (inherited_source_fiber_obj (F := F) (D₂.obj i₁)))
  let N₂ :=
    (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.obj
      (inherited_source_fiber_obj (F := F) (D₂.obj i₂)))
  let AM₁ := (Cat.Hom.toNatIso
    ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
      c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc (by aesop))).app M₁
  let AM₂ := (Cat.Hom.toNatIso
    ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
      c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc (by aesop))).app M₂
  let AN₁ := (Cat.Hom.toNatIso
    ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
      c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc (by aesop))).app N₁
  let AN₂ := (Cat.Hom.toNatIso
    ((canonicalFiberPseudofunctor Xₛ.p).mapComp'
      c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc (by aesop))).app N₂
  let ρM₁ := T.mapIso
    (inherited_basis_target_slice_inverse_base_reindex_iso
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (Y := Y) (g := g) D₁ q f₁ hf₁)
  let ρM₂ := T.mapIso
    (inherited_basis_target_slice_inverse_base_reindex_iso
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (Y := Y) (g := g) D₁ q f₂ hf₂)
  let ρN₁ := T.mapIso
    (inherited_basis_target_slice_inverse_base_reindex_iso
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (Y := Y) (g := g) D₂ q f₁ hf₁)
  let ρN₂ := T.mapIso
    (inherited_basis_target_slice_inverse_base_reindex_iso
      (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (Y := Y) (g := g) D₂ q f₂ hf₂)
  let αM₁ :=
    (((canonicalFiberPseudofunctor Xₛ.p).map f₁.op.toLoc).toFunctor.map
      ((inherited_source_fiber_forget (F := F) (Y i₁)).map (φ.hom i₁)))
  let αM₂ :=
    (((canonicalFiberPseudofunctor Xₛ.p).map f₂.op.toLoc).toFunctor.map
      ((inherited_source_fiber_forget (F := F) (Y i₂)).map (φ.hom i₂)))
  let αS₁ :=
    T.map
      ((((canonicalFiberPseudofunctor Xₛ.p).map
          (Yₛ.p.map
            (inherited_basis_target_slice_inverse_leg
              (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)).op.toLoc).toFunctor.map
          ((inherited_source_fiber_forget (F := F) (Y i₁)).map (φ.hom i₁))))
  let αS₂ :=
    T.map
      ((((canonicalFiberPseudofunctor Xₛ.p).map
          (Yₛ.p.map
            (inherited_basis_target_slice_inverse_leg
              (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)).op.toLoc).toFunctor.map
          ((inherited_source_fiber_forget (F := F) (Y i₂)).map (φ.hom i₂))))
  let uM := T.map <| inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D₁
    (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
    (inherited_basis_target_slice_inverse_leg
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
  let uN := T.map <| inherited_basis_descent_hom
    (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) F D₂
    (inherited_basis_target_slice_inverse_obj (J := J) (Yₛ := Yₛ) q).hom
    (inherited_basis_target_slice_inverse_leg
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
    (inherited_basis_target_slice_inverse_leg_w
      (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
  have hmid : αS₁ ≫ uN = uM ≫ αS₂ := by
    dsimp [αS₁, αS₂, uM, uN]
    exact ((T.map_comp _ _).symm).trans
      ((congrArg T.map
        (inherited_basis_forget_to_source_descent_literal_comm_middle
          (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) φ q f₁ f₂ hf₁ hf₂)).trans
        (T.map_comp _ _))
  have hleft :
      αM₁ ≫ ((Cat.Hom.toNatIso ε).app N₁).inv ≫ AN₁.hom ≫ ρN₁.inv =
        ((Cat.Hom.toNatIso ε).app M₁).inv ≫ AM₁.hom ≫ ρM₁.inv ≫ αS₁ := by
    let P := canonicalFiberPseudofunctor Xₛ.p
    have hid :
        αM₁ ≫ ((Cat.Hom.toNatIso ε).app N₁).inv =
          ((Cat.Hom.toNatIso ε).app M₁).inv ≫
            (P.map (𝟙 Z).op.toLoc).toFunctor.map αM₁ := by
      dsimp [P, ε]
      simpa using
        ((canonicalFiberPseudofunctor Xₛ.p).mapId'_inv_naturality
          (𝟙 Z).op.toLoc (by cat_disch) αM₁).symm
    have hcomp :
        (P.map (𝟙 Z).op.toLoc).toFunctor.map αM₁ ≫ AN₁.hom =
          AM₁.hom ≫ T.map ((P.map c.op.toLoc).toFunctor.map αM₁) := by
      dsimp [P, AM₁, AN₁, T]
      simpa using
        ((canonicalFiberPseudofunctor Xₛ.p).mapComp'_hom_naturality
          c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc (by aesop) αM₁)
    have hρraw :
        ((P.map c.op.toLoc).toFunctor.map αM₁) ≫
            (inherited_basis_target_slice_inverse_base_reindex_iso
              (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (Y := Y) (g := g)
              D₂ q f₁ hf₁).inv =
          (inherited_basis_target_slice_inverse_base_reindex_iso
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (Y := Y) (g := g)
            D₁ q f₁ hf₁).inv ≫
            (((canonicalFiberPseudofunctor Xₛ.p).map
              (Yₛ.p.map
                (inherited_basis_target_slice_inverse_leg
                  (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)).op.toLoc).toFunctor.map
              ((inherited_source_fiber_forget (F := F) (Y i₁)).map (φ.hom i₁))) := by
      dsimp [P, αM₁, inherited_basis_target_slice_inverse_base_reindex_iso, c]
      simpa using
        ((canonicalFiberPseudofunctor Xₛ.p).mapComp'_inv_naturality
          f₁.op.toLoc
          (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
            (Over.mk q)).hom.left).op.toLoc
          (Yₛ.p.map
            (inherited_basis_target_slice_inverse_leg
              (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)).op.toLoc
          (inherited_basis_target_slice_inverse_leg_base_toLoc
            (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₁ hf₁)
          ((inherited_source_fiber_forget (F := F) (Y i₁)).map (φ.hom i₁)))
    have hρ :
        T.map ((P.map c.op.toLoc).toFunctor.map αM₁) ≫ ρN₁.inv =
          ρM₁.inv ≫ αS₁ := by
      dsimp [ρM₁, ρN₁, αS₁]
      exact ((T.map_comp _ _).symm).trans
        ((congrArg T.map hρraw).trans (T.map_comp _ _))
    simpa only [Category.assoc] using
      three_square_boundary_paste
        (αM₁ ≫ ((Cat.Hom.toNatIso ε).app N₁).inv)
        (((Cat.Hom.toNatIso ε).app M₁).inv)
        ((P.map (𝟙 Z).op.toLoc).toFunctor.map αM₁)
        AN₁.hom AM₁.hom (T.map ((P.map c.op.toLoc).toFunctor.map αM₁))
        ρN₁.inv ρM₁.inv αS₁
        hid hcomp hρ
  have hright :
      αS₂ ≫ ρN₂.hom ≫ AN₂.inv ≫ ((Cat.Hom.toNatIso ε).app N₂).hom =
        ρM₂.hom ≫ AM₂.inv ≫ ((Cat.Hom.toNatIso ε).app M₂).hom ≫ αM₂ := by
    let P := canonicalFiberPseudofunctor Xₛ.p
    have hρraw :
        (((canonicalFiberPseudofunctor Xₛ.p).map
          (Yₛ.p.map
            (inherited_basis_target_slice_inverse_leg
              (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)).op.toLoc).toFunctor.map
          ((inherited_source_fiber_forget (F := F) (Y i₂)).map (φ.hom i₂))) ≫
            (inherited_basis_target_slice_inverse_base_reindex_iso
              (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (Y := Y) (g := g)
              D₂ q f₂ hf₂).hom =
          (inherited_basis_target_slice_inverse_base_reindex_iso
            (J := J) (Xₛ := Xₛ) (Yₛ := Yₛ) (F := F) (Y := Y) (g := g)
            D₁ q f₂ hf₂).hom ≫
            ((P.map c.op.toLoc).toFunctor.map αM₂) := by
      dsimp [P, αM₂, inherited_basis_target_slice_inverse_base_reindex_iso, c]
      simpa using
        ((canonicalFiberPseudofunctor Xₛ.p).mapComp'_hom_naturality
          f₂.op.toLoc
          (((inherited_basis_target_slice_equivalence (J := J) (Yₛ := Yₛ) y).counitIso.app
            (Over.mk q)).hom.left).op.toLoc
          (Yₛ.p.map
            (inherited_basis_target_slice_inverse_leg
              (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)).op.toLoc
          (inherited_basis_target_slice_inverse_leg_base_toLoc
            (J := J) (Yₛ := Yₛ) (y := y) (Y := Y) (g := g) q f₂ hf₂)
          ((inherited_source_fiber_forget (F := F) (Y i₂)).map (φ.hom i₂)))
    have hρ :
        αS₂ ≫ ρN₂.hom =
          ρM₂.hom ≫ T.map ((P.map c.op.toLoc).toFunctor.map αM₂) := by
      dsimp [ρM₂, ρN₂, αS₂]
      exact ((T.map_comp _ _).symm).trans
        ((congrArg T.map hρraw).trans (T.map_comp _ _))
    have hcomp :
        T.map ((P.map c.op.toLoc).toFunctor.map αM₂) ≫ AN₂.inv =
          AM₂.inv ≫ (P.map (𝟙 Z).op.toLoc).toFunctor.map αM₂ := by
      dsimp [P, AM₂, AN₂, T]
      exact
        ((canonicalFiberPseudofunctor Xₛ.p).mapComp'_inv_naturality
          c.op.toLoc cInv.op.toLoc (𝟙 Z).op.toLoc (by aesop) αM₂)
    have hid :
        (P.map (𝟙 Z).op.toLoc).toFunctor.map αM₂ ≫
            ((Cat.Hom.toNatIso ε).app N₂).hom =
          ((Cat.Hom.toNatIso ε).app M₂).hom ≫ αM₂ := by
      dsimp [P, ε]
      simpa using
        ((canonicalFiberPseudofunctor Xₛ.p).mapId'_hom_naturality
          (𝟙 Z).op.toLoc (by cat_disch) αM₂)
    simpa only [Category.assoc] using
      three_square_boundary_paste_right
        αS₂ ρN₂.hom ρM₂.hom
        (T.map ((P.map c.op.toLoc).toFunctor.map αM₂))
        AN₂.inv AM₂.inv
        ((P.map (𝟙 Z).op.toLoc).toFunctor.map αM₂)
        ((Cat.Hom.toNatIso ε).app N₂).hom
        (((Cat.Hom.toNatIso ε).app M₂).hom ≫ αM₂)
        hρ hcomp hid
  simpa only [inherited_basis_forget_to_source_descent_hom,
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Functor.map_comp,
    T, ε, M₁, M₂, N₁, N₂, AM₁, AM₂, AN₁, AN₂, ρM₁, ρM₂, ρN₁, ρN₂,
    αM₁, αM₂, αS₁, αS₂, uM, uN, W, c, cInv,
    Cat.Hom.toNatIso, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv] using
    (conjugated_iso_shell_comm_outer_pullHom_grouped
      ((Cat.Hom.toNatIso ε).app M₁) ((Cat.Hom.toNatIso ε).app M₂)
      ((Cat.Hom.toNatIso ε).app N₁) ((Cat.Hom.toNatIso ε).app N₂)
      AM₁ AM₂ AN₁ AN₂ ρM₁ ρM₂ ρN₁ ρN₂
      αM₁ αM₂ αS₁ αS₂ uM uN hleft hright hmid)

/-- Helper for Lemma 8.10.5: an object in a fiber of `G F` carries its tautological local target
identification after forgetting to the source fiber. -/
noncomputable def inherited_basis_local_target_iso
    (F : Xₛ ⟶ Yₛ)
    {y : Yₛ.S} (x : (G F).Fiber y) :
    (fiberFunctor F (Yₛ.p.obj y)).obj (inherited_source_fiber_obj (F := F) x) ≅
      (Functor.Fiber.mk (a := y) rfl : Yₛ.p.Fiber (Yₛ.p.obj y)) :=
  eqToIso (Subtype.ext x.2)

/-- Helper for Lemma 8.10.5: pulling the target object `y` back along a leg `f : yi ⟶ y`
recovers the target-leg object `yi` in the corresponding fiber. -/
noncomputable def inherited_basis_target_pullback_leg_iso
    {y yi : Yₛ.S} (f : yi ⟶ y) :
    (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.obj
      (Functor.Fiber.mk (a := y) rfl)) ≅
    (Functor.Fiber.mk (a := yi) rfl : Yₛ.p.Fiber (Yₛ.p.obj yi)) := by
  let yPull : Yₛ.p.Fiber (Yₛ.p.obj yi) :=
    (((canonicalFiberPseudofunctor Yₛ.p).map (Yₛ.p.map f).op.toLoc).toFunctor.obj
      (Functor.Fiber.mk (a := y) rfl))
  let φ : yPull.1 ⟶ y :=
    (canonicalPullbackChoice Yₛ.p).map (Yₛ.p.map f) (Functor.Fiber.mk (a := y) rfl)
  let ψ : yi ⟶ y := f
  have hφ : Yₛ.p.IsStronglyCartesian (Yₛ.p.map f) φ := by
    simpa [φ, yPull] using
      (canonicalPullbackChoice Yₛ.p).isStronglyCartesian (Yₛ.p.map f)
        (Functor.Fiber.mk (a := y) rfl)
  have hψ : Yₛ.p.IsStronglyCartesian (Yₛ.p.map f) ψ := by
    dsimp [ψ]
    infer_instance
  have hf : Yₛ.p.map f = (Iso.refl (Yₛ.p.obj yi)).hom ≫ Yₛ.p.map f := by simp
  let e0 : yi ≅ yPull.1 :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso Yₛ.p hf φ ψ
  have he0Hom : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj yi)) e0.hom := by
    change Yₛ.p.IsHomLift (Iso.refl (Yₛ.p.obj yi)).hom e0.hom
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift Yₛ.p hf φ ψ
  have he0Inv : Yₛ.p.IsHomLift (𝟙 (Yₛ.p.obj yi)) e0.inv := by
    change Yₛ.p.IsHomLift (Iso.refl (Yₛ.p.obj yi)).inv e0.inv
    exact Functor.IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift Yₛ.p hf φ ψ
  exact
    { hom := Functor.Fiber.homMk Yₛ.p (Yₛ.p.obj yi) e0.inv
      inv := Functor.Fiber.homMk Yₛ.p (Yₛ.p.obj yi) e0.hom
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        change e0.inv ≫ e0.hom = 𝟙 _
        exact e0.inv_hom_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        change e0.hom ≫ e0.inv = 𝟙 _
        exact e0.hom_inv_id }

/-- Helper for Lemma 8.10.5: for a stack in groupoids, the isomorphism subfunctor is the whole
Hom presheaf. -/
theorem inherited_basis_fiberIsomorphismSubfunctor_eq_top
    {U : C} (x y : Yₛ.p.Fiber U) :
    fiberIsomorphismSubfunctor Yₛ.p x y = ⊤ := by
  ext A φ
  constructor
  · intro _
    trivial
  · intro _
    exact IsFibredInGroupoids.hom_isIso _ φ

/-- Helper for Lemma 8.10.5: target isomorphism presheaves are sheaves on the base slice because
`Yₛ` is a stack in groupoids. -/
theorem inherited_basis_fiberIsomorphismSubfunctor_isSheaf
    {U : C} (x y : Yₛ.p.Fiber U) :
    Presheaf.IsSheaf (J.over U) ((fiberIsomorphismSubfunctor Yₛ.p x y).toFunctor) := by
  have htop : fiberIsomorphismSubfunctor Yₛ.p x y = ⊤ :=
    inherited_basis_fiberIsomorphismSubfunctor_eq_top (J := J) (Yₛ := Yₛ) x y
  have hIso : IsIso (Subfunctor.ι (fiberIsomorphismSubfunctor Yₛ.p x y)) :=
    (Subfunctor.eq_top_iff_isIso (G := fiberIsomorphismSubfunctor Yₛ.p x y)).1 htop
  let e : (fiberIsomorphismSubfunctor Yₛ.p x y).toFunctor ≅
      (canonicalFiberPseudofunctor Yₛ.p).presheafHom x y :=
    asIso (Subfunctor.ι _)
  exact
    (Presheaf.isSheaf_of_iso_iff e).2
      (Pseudofunctor.IsPrestack.isSheaf
        (F := canonicalFiberPseudofunctor Yₛ.p) (J := J) x y)

end

end CategoryTheory
