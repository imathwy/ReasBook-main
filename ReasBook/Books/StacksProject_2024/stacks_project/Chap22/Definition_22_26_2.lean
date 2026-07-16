import StacksProject_2024.stacks_project.Chap22.Definition_22_26_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace DifferentialGradedCategory

open scoped DifferentialGradedCategory

/-- Definition 22.26.2: a functor of differential graded categories over `R`. It consists of an
object map and graded `R`-linear maps on morphism groups, compatible with the differential,
identities, and graded composition. -/
@[stacks 09L6]
structure DgFunctor (R : Type u) [CommRing R] (A : Type v) (B : Type w)
    [DA : DifferentialGradedCategory R A] [DB : DifferentialGradedCategory R B] where
  obj : A → B
  map {X Y : A} {n : ℤ} : (X ⟶[n] Y) → (obj X) ⟶[n] (obj Y)
  map_add {X Y : A} {n : ℤ} (f g : X ⟶[n] Y) : map (f + g) = map f + map g
  map_smul {X Y : A} {n : ℤ} (r : R) (f : X ⟶[n] Y) : map (r • f) = r • map f
  map_d {X Y : A} {n : ℤ} (f : X ⟶[n] Y) : map (DA.d n f) = DB.d n (map f)
  map_id (X : A) : map (DA.id X) = DB.id (obj X)
  map_comp {X Y Z : A} {i j : ℤ} (g : Y ⟶[j] Z) (f : X ⟶[i] Y) :
    map (DA.comp g f) = DB.comp (map g) (map f)

namespace DgFunctor

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w}
variable [DA : DifferentialGradedCategory R A] [DB : DifferentialGradedCategory R B]

attribute [simp] DgFunctor.map_add DgFunctor.map_smul DgFunctor.map_d
  DgFunctor.map_id DgFunctor.map_comp

/-- The degree-`n` morphism map of a DG functor as an `R`-linear map. -/
def mapLinear (F : DgFunctor R A B) {X Y : A} (n : ℤ) :
    (X ⟶[n] Y) →ₗ[R] ((F.obj X) ⟶[n] (F.obj Y)) where
  toFun := F.map
  map_add' := F.map_add
  map_smul' := F.map_smul

@[simp] theorem mapLinear_apply (F : DgFunctor R A B) {X Y : A} (n : ℤ) (f : X ⟶[n] Y) :
    F.mapLinear n f = F.map f :=
  rfl

theorem map_zero (F : DgFunctor R A B) {X Y : A} (n : ℤ) :
    F.map (0 : X ⟶[n] Y) = (0 : (F.obj X) ⟶[n] (F.obj Y)) := by
  simpa using (F.mapLinear n).map_zero

theorem map_neg (F : DgFunctor R A B) {X Y : A} (n : ℤ) (f : X ⟶[n] Y) :
    F.map (-f) = -F.map f := by
  simpa using (F.mapLinear n).map_neg f

theorem map_sub (F : DgFunctor R A B) {X Y : A} (n : ℤ) (f g : X ⟶[n] Y) :
    F.map (f - g) = F.map f - F.map g := by
  simp [sub_eq_add_neg, F.map_add, F.map_neg]

end DgFunctor

section

variable (R : Type u) [CommRing R]
variable (A : Type v) (B : Type w)
variable [DifferentialGradedCategory R A]
variable [DifferentialGradedCategory R B]

#check (DgFunctor R A B)

end

end DifferentialGradedCategory
