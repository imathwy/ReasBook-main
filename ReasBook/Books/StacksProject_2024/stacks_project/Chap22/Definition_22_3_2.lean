import StacksProject_2024.stacks_project.Chap22.Definition_22_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

section

variable {R : Type u} [CommRing R]

/-- Definition 22.3.2: a homomorphism `f : (A, d) → (B, d)` of cochain differential graded
`R`-algebras is a morphism of the underlying cochain complexes that preserves the unit and the
homogeneous multiplication. On the canonical Chapter 22 owner `CochainDGAlgebra R`, the condition
that `f` commute with the differentials is encoded by the cochain-map field
`toCochainMap`. -/
@[stacks 061X]
structure CochainDGAlgebra.Hom (A B : CochainDGAlgebra R) where
  /-- The underlying morphism of cochain complexes. -/
  toCochainMap : A.toCochainComplex ⟶ B.toCochainComplex
  /-- The unit is preserved. -/
  map_one : toCochainMap.f 0 A.one = B.one
  /-- The multiplication is preserved on homogeneous elements. -/
  map_mul (n m : ℤ) (a : A.X n) (b : A.X m) :
    toCochainMap.f (n + m) (A.mul n m a b) =
      B.mul n m (toCochainMap.f n a) (toCochainMap.f m b)

namespace CochainDGAlgebra.Hom

variable {A B C : CochainDGAlgebra R}

/-- The identity homomorphism of a cochain differential graded algebra. -/
def id (A : CochainDGAlgebra R) : Hom A A where
  toCochainMap := 𝟙 A.toCochainComplex
  map_one := rfl
  map_mul _ _ _ _ := rfl

/-- Composition of cochain differential graded algebra homomorphisms. -/
def comp (g : Hom B C) (f : Hom A B) : Hom A C where
  toCochainMap := f.toCochainMap ≫ g.toCochainMap
  map_one := by
    change g.toCochainMap.f 0 (f.toCochainMap.f 0 A.one) = C.one
    rw [f.map_one, g.map_one]
  map_mul n m a b := by
    change
      g.toCochainMap.f (n + m) (f.toCochainMap.f (n + m) (A.mul n m a b)) =
        C.mul n m (g.toCochainMap.f n (f.toCochainMap.f n a))
          (g.toCochainMap.f m (f.toCochainMap.f m b))
    rw [f.map_mul, g.map_mul]

@[simp] theorem id_toCochainMap (A : CochainDGAlgebra R) :
    (id A).toCochainMap = 𝟙 A.toCochainComplex :=
  rfl

@[simp] theorem comp_toCochainMap (g : Hom B C) (f : Hom A B) :
    (comp g f).toCochainMap = f.toCochainMap ≫ g.toCochainMap :=
  rfl

/-- Extensionality for cochain differential graded algebra homomorphisms reduces to the
underlying cochain-complex map. -/
theorem ext_toCochainMap {f g : Hom A B} (h : f.toCochainMap = g.toCochainMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

end CochainDGAlgebra.Hom

namespace CochainDGAlgebra

/-- A cochain differential graded algebra homomorphism can be used as its underlying cochain map. -/
instance {A B : CochainDGAlgebra R} :
    Coe (Hom A B) (A.toCochainComplex ⟶ B.toCochainComplex) where
  coe f := f.toCochainMap

/-- A cochain differential graded algebra homomorphism can be applied degreewise to homogeneous
elements. -/
instance {A B : CochainDGAlgebra R} :
    CoeFun (Hom A B) (fun _ ↦ ∀ n : ℤ, A.X n → B.X n) where
  coe f := fun n a ↦ f.toCochainMap.f n a

/-- Coercing a cochain differential graded algebra homomorphism to a function recovers the
degreewise action of the underlying cochain map. -/
@[simp] theorem coe_apply {A B : CochainDGAlgebra R} (f : Hom A B) (n : ℤ) (a : A.X n) :
    f n a = f.toCochainMap.f n a :=
  rfl

/-- A cochain differential graded algebra homomorphism commutes with the differentials because its
underlying cochain map does. -/
@[simp] theorem map_d_apply {A B : CochainDGAlgebra R} (f : Hom A B) (n : ℤ) (a : A.X n) :
    f (n + 1) (A.d n a) = B.d n (f n a) := by
  change (f.toCochainMap.f (n + 1)).hom ((A.toCochainComplex.d n (n + 1)).hom a) =
      (B.toCochainComplex.d n (n + 1)).hom ((f.toCochainMap.f n).hom a)
  exact (LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (f.toCochainMap.comm n (n + 1))) a).symm

/-- A cochain differential graded algebra homomorphism preserves the unit. -/
@[simp] theorem map_one_apply {A B : CochainDGAlgebra R} (f : Hom A B) :
    f 0 A.one = B.one :=
  f.map_one

/-- A cochain differential graded algebra homomorphism preserves homogeneous multiplication. -/
@[simp] theorem map_mul_apply {A B : CochainDGAlgebra R} (f : Hom A B)
    (n m : ℤ) (a : A.X n) (b : A.X m) :
    f (n + m) (A.mul n m a b) = B.mul n m (f n a) (f m b) :=
  f.map_mul n m a b

/-- Composition acts degreewise by composing the underlying maps on each homogeneous piece. -/
@[simp] theorem comp_apply {A B C : CochainDGAlgebra R} (g : Hom B C) (f : Hom A B)
    (n : ℤ) (a : A.X n) :
    Hom.comp g f n a = g n (f n a) :=
  rfl

/-- Extensionality for cochain differential graded algebra homomorphisms can be checked
degreewise on homogeneous elements. -/
@[ext] theorem hom_ext
    {A B : CochainDGAlgebra R}
    {f g : Hom A B}
    (h : ∀ n : ℤ, ∀ a : A.X n, f n a = g n a) : f = g := by
  apply Hom.ext_toCochainMap
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  ext a
  exact h n a

/-- Cochain differential graded algebras over `R` form a category with the homomorphisms from
Definition `22.3.2` as morphisms. -/
instance instCategory : Category (CochainDGAlgebra R) where
  Hom A B := Hom A B
  id A := Hom.id A
  comp f g := Hom.comp g f
  id_comp := by
    intro A B f
    ext n a
    rfl
  comp_id := by
    intro A B f
    ext n a
    rfl
  assoc := by
    intro A B C D f g h
    ext n a
    rfl

end CochainDGAlgebra

end
