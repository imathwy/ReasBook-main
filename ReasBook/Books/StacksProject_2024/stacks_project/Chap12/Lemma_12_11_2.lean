import StacksProject_2024.stacks_project.Chap12.Definition_12_11_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace AbelianK0

section

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]

/- Lemma 12.11.2 sits in the Grothendieck-group/exact-functor domain for abelian categories.

Domain-style sampling:
- sampled owner declarations: `AbelianK0.lift`, `AbelianK0.of_shortExact`,
  `ShortComplex.ShortExact.map_of_exact`;
- owner abstraction: the induced additive map on `K₀` is a quotient lift from the object-level map
  `X ↦ [F(X)]`;
- primitive data: only the exact functor `F : A ⥤ₑ B`;
- derived API: the descended homomorphism `mapExactFunctor` and its value on generators.

Source/core/bridge triage:
- `source-facing`: the induced map on Grothendieck groups from an exact functor;
- `core/canonical`: `AbelianK0.lift` together with `AbelianK0.of_shortExact`;
- `bridge/view`: `ShortComplex.ShortExact.map_of_exact` transfers the defining relations along the
  underlying functor `F.obj`.
-/

-- Proof sketch: a generator of `AbelianK0.relations A` comes from a short exact sequence in `A`.
-- Map that sequence along `F`, use `ShortExact.map_of_exact` to retain
-- short exactness, rewrite the resulting generator using
-- `AbelianK0.sub_mem_relations_of_shortExact`, and then apply `AbelianK0.of_shortExact` in the
-- target category.
private theorem relations_le_ker_mapExactFunctor (F : A ⥤ₑ B) :
    relations A ≤
      (FreeAbelianGroup.lift fun X ↦ K₀[F.obj.obj X]).ker := by
  rw [AbelianK0.relations, AddSubgroup.closure_le]
  rintro _ ⟨S, rfl⟩
  rcases S with ⟨S, hS⟩
  change
    (FreeAbelianGroup.lift fun X ↦ K₀[F.obj.obj X])
        (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    sub_eq_zero.mpr (of_shortExact (S.map F.obj) (hS.map_of_exact F.obj))

/-- Lemma 12.11.2: an exact functor between abelian categories induces a homomorphism on
Grothendieck groups by sending `[X]` to `[F(X)]`. -/
def mapExactFunctor (F : A ⥤ₑ B) :
    AbelianK0 A →+ AbelianK0 B :=
  AbelianK0.lift (fun X ↦ K₀[F.obj.obj X]) (relations_le_ker_mapExactFunctor F)

-- Proof sketch: `mapExactFunctor` is `AbelianK0.lift` applied to `X ↦ [F(X)]`, so evaluation on
-- `AbelianK0.of X` is the owner lemma `AbelianK0.lift_of`.
/-- The induced morphism on `K₀` sends the class of `X` to the class of its image under the
exact functor `F`. -/
@[simp] theorem mapExactFunctor_apply_of (F : A ⥤ₑ B) (X : A) :
    mapExactFunctor F K₀[X] = K₀[F.obj.obj X] := by
  simpa using AbelianK0.lift_of
    (fun X : A ↦ K₀[F.obj.obj X])
    (relations_le_ker_mapExactFunctor F)
    X

end

end AbelianK0

end CategoryTheory
