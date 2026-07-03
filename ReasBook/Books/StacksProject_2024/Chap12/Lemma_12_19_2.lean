import StacksProject_2024.Chap12.Definition_12_19_1

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace FilteredObject

/- Source/core/bridge triage for Lemma 12.19.2:
- source-facing: the textbook statement that filtered objects form a preadditive category.
- core/canonical owners: `FilteredObject.Hom`, `FilteredObject.forget`, and `CategoryTheory.Preadditive`.
- primitive data: a filtered morphism is an ambient morphism together with stagewise factorization
  through the target filtration.
- derived API: additive operations on filtered morphisms, the induced `Hom.hom` simp lemmas, the
  additive forgetful functor, and the `Preadditive (FilteredObject C)` instance.
- domain-style sampling:
  * `FilteredObject.Hom` and the faithful owner functor `FilteredObject.forget` in
    `Definition_12_19_1`;
  * `CategoryTheory.Preadditive` in mathlib;
  * `Function.Injective.addCommGroup` together with the owner-side `Hom.hom` projection pattern in
    mathlib categories such as `ModuleCat` and `HomologicalComplex`.

The canonical owner stays `FilteredObject.Hom`: the additive structure is not recalled from a
fully faithful transport theorem, but induced from the ambient preadditive hom-group along the
injective projection `Hom.hom`. -/

variable {X Y : FilteredObject C}

private theorem add_preserves (f g : X ⟶ Y) :
    ∀ i : ℤ, (Y.filtration i).Factors ((X.filtration i).arrow ≫ (f.hom + g.hom)) := sorry

private theorem neg_preserves (f : X ⟶ Y) :
    ∀ i : ℤ, (Y.filtration i).Factors ((X.filtration i).arrow ≫ (-f.hom)) := sorry

private theorem sub_preserves (f g : X ⟶ Y) :
    ∀ i : ℤ, (Y.filtration i).Factors ((X.filtration i).arrow ≫ (f.hom - g.hom)) := sorry

private theorem zsmul_preserves (n : ℤ) (f : X ⟶ Y) :
    ∀ i : ℤ, (Y.filtration i).Factors ((X.filtration i).arrow ≫ (n • f.hom)) := sorry

private theorem nsmul_preserves (n : ℕ) (f : X ⟶ Y) :
    ∀ i : ℤ, (Y.filtration i).Factors ((X.filtration i).arrow ≫ (n • f.hom)) := sorry

instance : Add (X ⟶ Y) where
  add f g :=
    { hom := f.hom + g.hom
      preserves := add_preserves f g }

instance : Neg (X ⟶ Y) where
  neg f :=
    { hom := -f.hom
      preserves := neg_preserves f }

instance : Sub (X ⟶ Y) where
  sub f g :=
    { hom := f.hom - g.hom
      preserves := sub_preserves f g }

instance : SMul ℕ (X ⟶ Y) where
  smul n f :=
    { hom := n • f.hom
      preserves := nsmul_preserves n f }

instance : SMul ℤ (X ⟶ Y) where
  smul n f :=
    { hom := n • f.hom
      preserves := zsmul_preserves n f }

@[simp] theorem add_hom (f g : X ⟶ Y) :
    (f + g).hom = f.hom + g.hom := rfl

@[simp] theorem neg_hom (f : X ⟶ Y) :
    (-f).hom = -f.hom := rfl

@[simp] theorem sub_hom (f g : X ⟶ Y) :
    (f - g).hom = f.hom - g.hom := rfl

@[simp] theorem nsmul_hom (n : ℕ) (f : X ⟶ Y) :
    (n • f).hom = n • f.hom := rfl

@[simp] theorem zsmul_hom (n : ℤ) (f : X ⟶ Y) :
    (n • f).hom = n • f.hom := rfl

omit [Preadditive C] in
theorem hom_injective : Function.Injective (Hom.hom : (X ⟶ Y) → (X.obj ⟶ Y.obj)) := by
  intro f g h
  exact FilteredObject.forget.map_injective h

instance : AddCommGroup (X ⟶ Y) :=
  Function.Injective.addCommGroup (Hom.hom : (X ⟶ Y) → (X.obj ⟶ Y.obj)) hom_injective
    rfl
    (fun _ _ ↦ rfl)
    (fun _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)

variable {P Q R : FilteredObject C}

/-- Lemma 12.19.2: in the textbook abelian setting the category of filtered objects is
preadditive; the construction only uses the stagewise factorization owner and `[Preadditive C]`. -/
instance filteredObject_preadditive : Preadditive (FilteredObject C) where
  add_comp P Q R f f' g := by
    apply hom_injective
    change (f.hom + f'.hom) ≫ g.hom = f.hom ≫ g.hom + f'.hom ≫ g.hom
    exact Preadditive.add_comp P.obj Q.obj R.obj f.hom f'.hom g.hom
  comp_add P Q R f g g' := by
    apply hom_injective
    change f.hom ≫ (g.hom + g'.hom) = f.hom ≫ g.hom + f.hom ≫ g'.hom
    exact Preadditive.comp_add P.obj Q.obj R.obj f.hom g.hom g'.hom

instance : (FilteredObject.forget : FilteredObject C ⥤ C).Additive where
  map_add := by
    intro _ _ f g
    rfl

end FilteredObject

end CategoryTheory
