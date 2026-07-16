import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Functor.Basic
import StacksProject_2024.stacks_project.Chap22.Definition_22_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v w

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {C : Type v}

open scoped DifferentialGradedCategory

/-- Definition 22.26.3: the object type of `Comp(𝒜)`. -/
@[stacks 09L7]
structure Comp (R : Type u) [CommRing R] (C : Type v) where
  obj : C
namespace Comp

/-- A `Comp(𝒜)` object can be used as its underlying object of the differential graded category. -/
instance : CoeTC (Comp R C) C where
  coe X := X.obj

@[simp] theorem coe_mk (X : C) : ((⟨X⟩ : Comp R C) : C) = X := rfl

end Comp

/-- The category with the same objects as a differential graded category `𝒜` and with all
degree-`0` morphisms `X ⟶[0] Y`. -/
structure DegreeZero (R : Type u) [CommRing R] (C : Type v) where
  obj : C

namespace DegreeZero

/-- A `DegreeZero` object can be used as its underlying object of the differential graded
category. -/
instance : CoeTC (DegreeZero R C) C where
  coe X := X.obj

@[simp] theorem coe_mk (X : C) : ((⟨X⟩ : DegreeZero R C) : C) = X := rfl

end DegreeZero

variable [D : DifferentialGradedCategory R C]

namespace DegreeZero

instance : Category (DegreeZero R C) where
  Hom X Y := ((X : C) ⟶[0] (Y : C))
  id X := D.id X
  comp f g := D.comp g f
  id_comp f := D.comp_id f
  comp_id f := D.id_comp f
  assoc f g h := D.comp_assoc_zero h g f

end DegreeZero

/-- The closed degree-`0` morphisms form a submodule of the degree-`0` hom-space. -/
def compHomSubmodule (X Y : C) : Submodule R (X ⟶[0] Y) where
  carrier := { f | D.d 0 f = 0 }
  zero_mem' := by
    simpa using (D.d_zero 0 : D.d 0 (0 : X ⟶[0] Y) = 0)
  add_mem' := by
    intro f g hf hg
    change D.d 0 (f + g) = 0
    rw [D.d_add, hf, hg]
    exact zero_add 0
  smul_mem' := by
    intro r f hf
    change D.d 0 (r • f) = 0
    rw [D.d_smul, hf]
    exact smul_zero r

/-- Closed degree-`0` morphisms in a differential graded category, viewed canonically as the
closed-element submodule of the degree-`0` hom-space. -/
abbrev CompHom (X Y : C) : Type w :=
  compHomSubmodule X Y

namespace CompHom

/-- A `CompHom` is closed by definition. -/
@[simp] theorem closed {X Y : C} (f : CompHom X Y) : D.d 0 (f : X ⟶[0] Y) = 0 :=
  f.property

end CompHom

@[simp] theorem CompHom.coe_mk {X Y : C} (f : X ⟶[0] Y) (hf) :
    ((⟨f, hf⟩ : CompHom X Y) : X ⟶[0] Y) = f := rfl

@[ext] theorem CompHom.ext {X Y : C} {f g : CompHom X Y} (h : f.val = g.val) : f = g := by
  exact Subtype.ext h

@[simp] theorem CompHom.zero_val {X Y : C} :
    ((0 : CompHom X Y) : X ⟶[0] Y) = 0 :=
  rfl

@[simp] theorem CompHom.add_val {X Y : C} (f g : CompHom X Y) :
    ((f + g : CompHom X Y) : X ⟶[0] Y) = (f : X ⟶[0] Y) + (g : X ⟶[0] Y) :=
  rfl

@[simp] theorem CompHom.neg_val {X Y : C} (f : CompHom X Y) :
    ((-f : CompHom X Y) : X ⟶[0] Y) = -(f : X ⟶[0] Y) :=
  rfl

@[simp] theorem CompHom.sub_val {X Y : C} (f g : CompHom X Y) :
    ((f - g : CompHom X Y) : X ⟶[0] Y) = (f : X ⟶[0] Y) - (g : X ⟶[0] Y) :=
  rfl

@[simp] theorem CompHom.smul_val {X Y : C} (r : R) (f : CompHom X Y) :
    ((r • f : CompHom X Y) : X ⟶[0] Y) = r • (f : X ⟶[0] Y) :=
  rfl

/-- The identity morphism in `Comp(𝒜)` is closed. -/
theorem compHom_id_closed (X : C) : D.d 0 (D.id X) = 0 :=
  D.d_id X

/-- The composite of closed degree-`0` morphisms is closed. -/
theorem compHom_comp_closed {X Y Z : C} (f : CompHom X Y) (g : CompHom Y Z) :
    D.d 0 (D.comp g.val f.val) = 0 := by
  calc
    D.d 0 (D.comp g.val f.val) =
        castHom zero_add_zero_succ_eq (D.comp (D.d 0 g.val) f.val) +
          castHom zero_succ_add_zero_eq (D.comp g.val (D.d 0 f.val)) := by
      simpa using D.d_comp_zero_zero g.val f.val
    _ = castHom zero_add_zero_succ_eq (D.comp 0 f.val) +
          castHom zero_succ_add_zero_eq (D.comp g.val 0) := by
      rw [g.closed, f.closed]
    _ = castHom zero_add_zero_succ_eq 0 + castHom zero_succ_add_zero_eq 0 := by
      rw [comp_zero_left, comp_zero_right]
    _ = 0 := by
      exact zero_add 0

/-- The identity closed degree-`0` morphism. -/
def CompHom.id (X : C) : CompHom X X :=
  ⟨D.id X, compHom_id_closed X⟩

/-- The underlying degree-`0` morphism of `CompHom.id`. -/
@[simp] theorem CompHom.id_val (X : C) : (CompHom.id X).val = D.id X := rfl

/-- The composite of two closed degree-`0` morphisms. -/
def CompHom.comp {X Y Z : C} (f : CompHom X Y) (g : CompHom Y Z) : CompHom X Z :=
  ⟨D.comp g.val f.val, compHom_comp_closed f g⟩

/-- The underlying degree-`0` morphism of `CompHom.comp`. -/
@[simp] theorem CompHom.comp_val {X Y Z : C} (f : CompHom X Y) (g : CompHom Y Z) :
    (CompHom.comp f g).val = D.comp g.val f.val := rfl

/-- Left identity for the category `Comp(𝒜)`. -/
private theorem compCategory_id_comp {X Y : Comp R C} (f : CompHom X.obj Y.obj) :
    CompHom.comp (CompHom.id X.obj) f = f := by
  ext
  exact D.comp_id f.val

/-- Right identity for the category `Comp(𝒜)`. -/
private theorem compCategory_comp_id {X Y : Comp R C} (f : CompHom X.obj Y.obj) :
    CompHom.comp f (CompHom.id Y.obj) = f := by
  ext
  exact D.id_comp f.val

/-- Associativity in the category `Comp(𝒜)`. -/
private theorem compCategory_assoc {W X Y Z : Comp R C} (f : CompHom W.obj X.obj)
    (g : CompHom X.obj Y.obj) (h : CompHom Y.obj Z.obj) :
    CompHom.comp (CompHom.comp f g) h = CompHom.comp f (CompHom.comp g h) := by
  ext
  exact D.comp_assoc_zero h.val g.val f.val

/-- The category `Comp(𝒜)` of objects of `𝒜` with closed degree-`0` morphisms. -/
instance compCategory : Category (Comp R C) where
  Hom X Y := CompHom X.obj Y.obj
  id X := CompHom.id X.obj
  comp f g := CompHom.comp f g
  id_comp := compCategory_id_comp
  comp_id := compCategory_comp_id
  assoc := compCategory_assoc

instance compPreadditive : Preadditive (Comp R C) where
  homGroup X Y := by
    change AddCommGroup (CompHom X.obj Y.obj)
    infer_instance
  add_comp X Y Z f f' g := by
    apply CompHom.ext
    exact D.comp_add_right g.val f.val f'.val
  comp_add X Y Z f g g' := by
    apply CompHom.ext
    exact D.comp_add_left g.val g'.val f.val

section

variable {R : Type u} [CommRing R]
variable {C : Type v}

/-- The object type of `K(𝒜)`. -/
structure K (R : Type u) [CommRing R] (C : Type v) where
  obj : C

namespace K

/-- A `K(𝒜)` object can be used as its underlying object of the differential graded category. -/
instance : CoeTC (K R C) C where
  coe X := X.obj

@[simp] theorem coe_mk (X : C) : ((⟨X⟩ : K R C) : C) = X := rfl

end K

end

/-- Two closed degree-`0` morphisms are homotopic when they differ by a boundary. -/
def Homotopic (X Y : C) (f g : CompHom X Y) : Prop :=
  ∃ h : X ⟶[-1] Y, f.val - g.val = D.d (-1) h

@[refl] theorem Homotopic.refl {X Y : C} (f : CompHom X Y) : Homotopic X Y f f := by
  refine ⟨0, ?_⟩
  calc
    f.val - f.val = 0 := sub_self f.val
    _ = D.d (-1) (0 : X ⟶[-1] Y) := by
      rw [← zero_smul R (0 : X ⟶[-1] Y), D.d_smul, zero_smul]
      rfl

@[symm] theorem Homotopic.symm {X Y : C} {f g : CompHom X Y}
    (hfg : Homotopic X Y f g) :
    Homotopic X Y g f := by
  rcases hfg with ⟨h, hh⟩
  refine ⟨-h, ?_⟩
  have hneg := congrArg Neg.neg hh
  simpa [Homotopic, sub_eq_add_neg, d_neg] using hneg

@[trans] theorem Homotopic.trans {X Y : C} {f g h : CompHom X Y}
    (hfg : Homotopic X Y f g)
    (hgh : Homotopic X Y g h) : Homotopic X Y f h := by
  rcases hfg with ⟨hfg', hhfg⟩
  rcases hgh with ⟨hgh', hhgh⟩
  refine ⟨hfg' + hgh', ?_⟩
  calc
    f.val - h.val = (f.val - g.val) + (g.val - h.val) := by
      abel
    _ = D.d (-1) hfg' + D.d (-1) hgh' := by
      rw [hhfg, hhgh]
      rfl
    _ = D.d (-1) (hfg' + hgh') := by
      exact (D.d_add (-1) hfg' hgh').symm

/-- The homotopy relation is an equivalence relation on closed degree-`0` morphisms. -/
theorem homotopy_equivalence (X Y : C) : Equivalence (Homotopic X Y) where
  refl := Homotopic.refl
  symm := Homotopic.symm
  trans := Homotopic.trans

/-- The homotopy relation on closed degree-`0` morphisms: two morphisms differ by a boundary. -/
def homotopySetoid (X Y : C) : Setoid (CompHom X Y) where
  r := Homotopic X Y
  iseqv := homotopy_equivalence X Y

/-- The canonical setoid on closed degree-`0` morphisms identifies homotopic morphisms. -/
instance instSetoidCompHom (X Y : C) : Setoid (CompHom X Y) :=
  homotopySetoid X Y

/-- The homotopy class of a closed degree-`0` morphism. -/
abbrev HomotopyClass (X Y : C) :=
  _root_.Quotient (homotopySetoid X Y)

namespace CompHom

/-- A closed degree-`0` morphism in `Comp(𝒜)` is homotopic to zero exactly when its underlying
degree-`0` morphism is the differential of a degree-`-1` morphism. -/
theorem homotopic_zero_iff {X Y : C} (f : CompHom X Y) :
    Homotopic X Y f 0 ↔ ∃ h : X ⟶[-1] Y, f.val = D.d (-1) h := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, by simpa using hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨h, by simpa using hh⟩

/-- The class of a closed degree-`0` morphism in the homotopy category. -/
def toHomotopyClass {X Y : C} (f : CompHom X Y) : HomotopyClass X Y :=
  _root_.Quotient.mk (homotopySetoid X Y) f

@[simp] theorem toHomotopyClass_eq_toHomotopyClass_iff {X Y : C} {f g : CompHom X Y} :
    f.toHomotopyClass = g.toHomotopyClass ↔ Homotopic X Y f g :=
  _root_.Quotient.eq

/-- Homotopic closed degree-`0` morphisms define the same morphism in `K(𝒜)`. -/
theorem toHomotopyClass_eq_of_homotopic {X Y : C} {f g : CompHom X Y}
    (hfg : Homotopic X Y f g) :
    f.toHomotopyClass = g.toHomotopyClass :=
  _root_.Quotient.sound hfg

/-- Equality in the homotopy category is exactly homotopy of closed degree-`0` morphisms. -/
theorem homotopic_of_toHomotopyClass_eq {X Y : C} {f g : CompHom X Y}
    (hfg : f.toHomotopyClass = g.toHomotopyClass) :
    Homotopic X Y f g :=
  toHomotopyClass_eq_toHomotopyClass_iff.mp hfg

end CompHom

/-- The identity morphism in the homotopy category `K(𝒜)`. -/
private def kId (X : K R C) : HomotopyClass X.obj X.obj :=
  (CompHom.id X.obj).toHomotopyClass

/-- Compatibility of composition in `Comp(𝒜)` with homotopy classes. -/
private theorem homotopy_comp_sound {X Y Z : C}
    {f₁ f₂ : CompHom X Y} {g₁ g₂ : CompHom Y Z}
    (hf : (homotopySetoid X Y).r f₁ f₂) (hg : (homotopySetoid Y Z).r g₁ g₂) :
    (homotopySetoid X Z).r (CompHom.comp f₁ g₁) (CompHom.comp f₂ g₂) := by
  rcases hf with ⟨hf', hhf⟩
  rcases hg with ⟨hg', hhg⟩
  refine ⟨castHom negOne_add_zero_eq (D.comp g₁.val hf') +
      castHom zero_add_negOne_eq (D.comp hg' f₂.val), ?_⟩
  have hzero₁ :
      D.comp (0 : Y ⟶[(0 : ℤ) + 1] Z) hf' = (0 : X ⟶[(-1 : ℤ) + (0 + 1)] Z) := by
    rw [← zero_smul R (0 : Y ⟶[(0 : ℤ) + 1] Z), D.comp_smul_left, zero_smul]
  have hd₁ :
      D.d (-1) (castHom negOne_add_zero_eq (D.comp g₁.val hf')) =
        D.comp g₁.val (D.d (-1) hf') := by
    have hcalc :
        D.d (-1) (castHom negOne_add_zero_eq (D.comp g₁.val hf')) =
          castHom negOne_add_zero_succ_eq_zero (D.comp (0 : Y ⟶[(0 : ℤ) + 1] Z) hf') +
            castHom negOne_succ_add_zero_eq_zero (D.comp g₁.val (D.d (-1) hf')) := by
      calc
        D.d (-1) (castHom negOne_add_zero_eq (D.comp g₁.val hf')) =
            D.d (-1) (D.comp g₁.val hf') := by
          simp
        _ =
            castHom negOne_add_zero_succ_eq_zero (D.comp (D.d 0 g₁.val) hf') +
              castHom negOne_succ_add_zero_eq_zero (D.comp g₁.val (D.d (-1) hf')) := by
          simpa using D.d_comp_zero_negOne g₁.val hf'
        _ =
            castHom negOne_add_zero_succ_eq_zero (D.comp (0 : Y ⟶[(0 : ℤ) + 1] Z) hf') +
              castHom negOne_succ_add_zero_eq_zero (D.comp g₁.val (D.d (-1) hf')) := by
          rw [g₁.closed]
    rw [hzero₁, castHom_zero] at hcalc
    simpa using hcalc
  have hzero₂ :
      D.comp hg' (0 : X ⟶[(0 : ℤ) + 1] Y) = (0 : X ⟶[((0 : ℤ) + 1) + -1] Z) := by
    rw [← zero_smul R (0 : X ⟶[(0 : ℤ) + 1] Y), D.comp_smul_right, zero_smul]
  have hd₂ :
      D.d (-1) (castHom zero_add_negOne_eq (D.comp hg' f₂.val)) =
        D.comp (D.d (-1) hg') f₂.val := by
    have hcalc :
        D.d (-1) (castHom zero_add_negOne_eq (D.comp hg' f₂.val)) =
          castHom zero_add_negOne_succ_eq_zero (D.comp (D.d (-1) hg') f₂.val) -
            castHom zero_succ_add_negOne_eq_zero (D.comp hg' 0) := by
      calc
        D.d (-1) (castHom zero_add_negOne_eq (D.comp hg' f₂.val)) =
            D.d (-1) (D.comp hg' f₂.val) := by
          simp
        _ =
            castHom zero_add_negOne_succ_eq_zero (D.comp (D.d (-1) hg') f₂.val) -
              castHom zero_succ_add_negOne_eq_zero (D.comp hg' (D.d 0 f₂.val)) := by
          simpa using D.d_comp_negOne_zero hg' f₂.val
        _ =
            castHom zero_add_negOne_succ_eq_zero (D.comp (D.d (-1) hg') f₂.val) -
              castHom zero_succ_add_negOne_eq_zero (D.comp hg' 0) := by
          rw [f₂.closed]
    rw [hzero₂, castHom_zero] at hcalc
    simpa using hcalc
  have hcomp₁ :
      D.comp g₁.val (f₁.val - f₂.val) =
        D.d (-1) (castHom negOne_add_zero_eq (D.comp g₁.val hf')) := by
    rw [hhf]
    symm
    exact hd₁
  have hcomp₂ :
      D.comp (g₁.val - g₂.val) f₂.val =
        D.d (-1) (castHom zero_add_negOne_eq (D.comp hg' f₂.val)) := by
    rw [hhg]
    symm
    exact hd₂
  have hsplit :
      (CompHom.comp f₁ g₁).val - (CompHom.comp f₂ g₂).val =
        D.comp g₁.val (f₁.val - f₂.val) + D.comp (g₁.val - g₂.val) f₂.val := by
    calc
      (CompHom.comp f₁ g₁).val - (CompHom.comp f₂ g₂).val =
          (D.comp g₁.val f₁.val - D.comp g₁.val f₂.val) +
            (D.comp g₁.val f₂.val - D.comp g₂.val f₂.val) := by
        simp [CompHom.comp_val]
        abel
      _ = D.comp g₁.val (f₁.val - f₂.val) + D.comp (g₁.val - g₂.val) f₂.val := by
        rw [← comp_sub_right, ← comp_sub_left]
  rw [hcomp₁, hcomp₂] at hsplit
  calc
    (CompHom.comp f₁ g₁).val - (CompHom.comp f₂ g₂).val =
        D.d (-1) (castHom negOne_add_zero_eq (D.comp g₁.val hf')) +
          D.d (-1) (castHom zero_add_negOne_eq (D.comp hg' f₂.val)) := hsplit
    _ = D.d (-1) (castHom negOne_add_zero_eq (D.comp g₁.val hf') +
          castHom zero_add_negOne_eq (D.comp hg' f₂.val)) := by
      symm
      exact D.d_add (-1) _ _

/-- Composition of homotopy classes in `K(𝒜)`. -/
private def kComp {X Y Z : K R C} (f : HomotopyClass X.obj Y.obj)
    (g : HomotopyClass Y.obj Z.obj) : HomotopyClass X.obj Z.obj :=
  _root_.Quotient.map₂
    (fun f' g' ↦ CompHom.comp f' g')
    (fun _ _ hf _ _ hg ↦ homotopy_comp_sound hf hg)
    f g

/-- Left identity in the homotopy category `K(𝒜)`. -/
private theorem kCategory_id_comp {X Y : K R C} (f : HomotopyClass X.obj Y.obj) :
    kComp (kId X) f = f := by
  refine _root_.Quotient.inductionOn f ?_
  intro f
  change (CompHom.comp (CompHom.id X.obj) f).toHomotopyClass = f.toHomotopyClass
  have h : CompHom.comp (CompHom.id X.obj) f = f := by
    ext
    exact D.comp_id f.val
  simpa using congrArg CompHom.toHomotopyClass h

/-- Right identity in the homotopy category `K(𝒜)`. -/
private theorem kCategory_comp_id {X Y : K R C} (f : HomotopyClass X.obj Y.obj) :
    kComp f (kId Y) = f := by
  refine _root_.Quotient.inductionOn f ?_
  intro f
  change (CompHom.comp f (CompHom.id Y.obj)).toHomotopyClass = f.toHomotopyClass
  have h : CompHom.comp f (CompHom.id Y.obj) = f := by
    ext
    exact D.id_comp f.val
  simpa using congrArg CompHom.toHomotopyClass h

/-- Associativity in the homotopy category `K(𝒜)`. -/
private theorem kCategory_assoc {W X Y Z : K R C}
    (f : HomotopyClass W.obj X.obj)
    (g : HomotopyClass X.obj Y.obj)
    (h : HomotopyClass Y.obj Z.obj) :
    kComp (kComp f g) h = kComp f (kComp g h) := by
  refine _root_.Quotient.inductionOn₃ f g h ?_
  intro f g h
  change (CompHom.comp (CompHom.comp f g) h).toHomotopyClass =
    (CompHom.comp f (CompHom.comp g h)).toHomotopyClass
  have h_assoc : CompHom.comp (CompHom.comp f g) h = CompHom.comp f (CompHom.comp g h) := by
    ext
    exact D.comp_assoc_zero h.val g.val f.val
  simpa using congrArg CompHom.toHomotopyClass h_assoc

/-- The homotopy category `K(𝒜)` of a differential graded category. -/
instance kCategory : Category (K R C) where
  Hom X Y := HomotopyClass X.obj Y.obj
  id X := kId X
  comp f g := kComp f g
  id_comp := kCategory_id_comp
  comp_id := kCategory_comp_id
  assoc := kCategory_assoc

namespace Comp

/-- A `Comp(𝒜)` object viewed in the homotopy category `K(𝒜)`. -/
abbrev inK (X : Comp R C) : K R C :=
  ⟨X.obj⟩

omit D in
@[simp] theorem inK_obj (X : Comp R C) : (X.inK : C) = X.obj :=
  rfl

/-- The canonical quotient functor `Comp(𝒜) ⥤ K(𝒜)` sending a closed degree-`0` morphism to its
homotopy class. -/
abbrev inKFunctor : Comp R C ⥤ K R C where
  obj X := X.inK
  map f := f.toHomotopyClass
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical morphism property on `Comp(𝒜)` given by becoming an isomorphism in `K(𝒜)`. -/
def homotopyEquivalences : MorphismProperty (Comp R C) :=
  fun _ _ f ↦ IsIso (inKFunctor.map f)

end Comp

namespace CompHom

/-- A morphism in `Comp(𝒜)` viewed in the homotopy category `K(𝒜)`. -/
abbrev inK {X Y : Comp R C} (f : X ⟶ Y) : X.inK ⟶ Y.inK :=
  f.toHomotopyClass

@[simp] theorem inK_eq_toHomotopyClass {X Y : Comp R C} (f : X ⟶ Y) :
    f.inK = f.toHomotopyClass :=
  rfl

end CompHom

section

variable (R : Type u) [CommRing R]
variable (A : Type v) [DifferentialGradedCategory.{u, v, w} R A]
variable (X Y : A)

#check (Comp R A)
#check (CompHom X Y)
#check (K R A)
#check (HomotopyClass X Y)

end

end DifferentialGradedCategory
