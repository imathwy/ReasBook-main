import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open BraidedCategory

universe v u

section

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

private lemma tensoringLeft_map_comp_tensorLeftIso {M N : C} (f : M ⟶ N) :
    (tensoringLeft C).map f ≫ (tensorLeftIsoTensorRight N).hom =
      (tensorLeftIsoTensorRight M).hom ≫ (tensoringRight C).map f := by
  ext X
  simpa using braiding_naturality_left f X

private lemma tensoringRight_map_comp_tensorLeftIso_inv {M N : C} (f : M ⟶ N) :
    (tensoringRight C).map f ≫ (tensorLeftIsoTensorRight N).inv =
      (tensorLeftIsoTensorRight M).inv ≫ (tensoringLeft C).map f := by
  ext X
  simpa using braiding_inv_naturality_left f X

end

section

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C] [HasProjectiveResolutions C]

private noncomputable def torFlipComponentIso (i : ℕ) (M : C) :
    ((Tor C i).obj M) ≅ ((Functor.flip (Tor' C i)).obj M) where
  hom := by
    simpa [Tor'] using (NatTrans.leftDerived ((tensorLeftIsoTensorRight M).hom) i)
  inv := by
    simpa [Tor'] using (NatTrans.leftDerived ((tensorLeftIsoTensorRight M).inv) i)
  hom_inv_id := by
    ext X
    change ((NatTrans.leftDerived ((tensorLeftIsoTensorRight M).hom) i) ≫
        NatTrans.leftDerived ((tensorLeftIsoTensorRight M).inv) i).app X =
      𝟙 _
    rw [← NatTrans.leftDerived_comp]
    simp
  inv_hom_id := by
    ext X
    change ((NatTrans.leftDerived ((tensorLeftIsoTensorRight M).inv) i) ≫
        NatTrans.leftDerived ((tensorLeftIsoTensorRight M).hom) i).app X =
      𝟙 _
    rw [← NatTrans.leftDerived_comp]
    simp

/-- Lemma 10.75.5: for every `i ≥ 0`, the bifunctors
`(M, N) ↦ Tor_i(M, N)` and `(M, N) ↦ Tor_i(N, M)` on a braided monoidal abelian category are
canonically isomorphic. -/
noncomputable def tor_flip_iso (i : ℕ) :
    Tor C i ≅ Functor.flip (Tor' C i) where
  hom :=
    { app := fun M ↦ (torFlipComponentIso C i M).hom
      naturality := by
        intro M N f
        ext X
        change ((NatTrans.leftDerived ((tensoringLeft C).map f) i) ≫
              NatTrans.leftDerived ((tensorLeftIsoTensorRight N).hom) i).app X =
          ((NatTrans.leftDerived ((tensorLeftIsoTensorRight M).hom) i) ≫
                NatTrans.leftDerived ((tensoringRight C).map f) i).app X
        rw [← NatTrans.leftDerived_comp, ← NatTrans.leftDerived_comp,
          tensoringLeft_map_comp_tensorLeftIso] }
  inv :=
    { app := fun M ↦ (torFlipComponentIso C i M).inv
      naturality := by
        intro M N f
        ext X
        change ((NatTrans.leftDerived ((tensoringRight C).map f) i) ≫
              NatTrans.leftDerived ((tensorLeftIsoTensorRight N).inv) i).app X =
          ((NatTrans.leftDerived ((tensorLeftIsoTensorRight M).inv) i) ≫
                NatTrans.leftDerived ((tensoringLeft C).map f) i).app X
        rw [← NatTrans.leftDerived_comp, ← NatTrans.leftDerived_comp,
          tensoringRight_map_comp_tensorLeftIso_inv] }
  hom_inv_id := by
    ext M X
    exact (torFlipComponentIso C i M).hom_inv_id_app X
  inv_hom_id := by
    ext M X
    exact (torFlipComponentIso C i M).inv_hom_id_app X

/-- The component of `tor_flip_iso` at a pair `(M, N)` is an isomorphism. -/
theorem isIso_tor_flip_iso_app_app (i : ℕ) (M N : C) :
    IsIso (((tor_flip_iso C i).app M).hom.app N) := by
  infer_instance

end
