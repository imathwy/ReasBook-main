import Mathlib.CategoryTheory.Abelian.Subobject
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits Opposite Preadditive

variable {C : Type u} [Category.{v} C]
variable {X Y : C}

/- Domain-style sampling for Definition 12.5.3:
- primary domain: kernel/cokernel criteria for morphisms, together with subobjects and quotient
  objects in an abelian category;
- inspected canonical declarations:
  `mono_iff_isZero_kernel`,
  `epi_iff_isZero_cokernel`,
  `Subobject`,
  `Abelian.subobjectIsoSubobjectOp`;
- best owner abstraction:
  source-facing `IsInjective f`, `IsSurjective f`, and `IsSubobject X Y`;
  core/canonical `Mono f`, `Epi f`, and `Subobject Y`;
  bridge/view `IsQuotient Y X := IsSubobject (op Y) (op X)`.

Primitive-vs-derived split:
- primitive data for the source-facing morphism notions: the kernel and cokernel objects of `f`;
- derived API: the canonical bridge theorems `isInjective_iff_mono` and
  `isSurjective_iff_epi`;
- primitive data for subobjects: a canonical subobject `P : Subobject Y`;
- derived API: the source-facing relation “`X` is a subobject of `Y`”, expressed by asking for an
  isomorphism from `X` to the underlying object of some `P`, and the opposite-category bridge
  `IsQuotient`.
-/

abbrev IsInjective (f : X ⟶ Y) [HasZeroMorphisms C] [HasKernel f] : Prop :=
  IsZero (kernel f)

abbrev IsSurjective (f : X ⟶ Y) [HasZeroMorphisms C] [HasCokernel f] : Prop :=
  IsZero (cokernel f)

/- Companion canonical owner for Definition 12.5.3 (injective). -/
recall CategoryTheory.Mono

/- Companion canonical owner for Definition 12.5.3 (surjective). -/
recall CategoryTheory.Epi

section

variable [Preadditive C] (f : X ⟶ Y)

/-- Definition 12.5.3, canonical bridge: the source-facing injective condition is equivalent to
the owner predicate `Mono f`. -/
theorem isInjective_iff_mono [HasKernel f] :
    IsInjective f ↔ Mono f := by
  simpa [IsInjective] using (mono_iff_isZero_kernel f).symm

/-- Definition 12.5.3, canonical bridge: the source-facing surjective condition is equivalent to
the owner predicate `Epi f`. -/
theorem isSurjective_iff_epi [HasCokernel f] :
    IsSurjective f ↔ Epi f := by
  simpa [IsSurjective] using (epi_iff_isZero_cokernel f).symm

end

/- Definition 12.5.3 (subobjects): the owner notion of subobjects of `Y` is `Subobject Y`. -/
recall CategoryTheory.Subobject
recall CategoryTheory.Subobject.mk
recall CategoryTheory.Subobject.underlyingIso

section

variable [Abelian C]

/- Definition 12.5.3 (quotient objects): mathlib represents quotient objects of `Y` by
`Subobject (op Y)`, and in an abelian category `Abelian.subobjectIsoSubobjectOp Y` identifies
them with the ordinary subobjects of `Y`. -/
recall CategoryTheory.Abelian.subobjectIsoSubobjectOp

end

/-- Source-facing bridge/view: `X` is a subobject of `Y` when it is isomorphic to the underlying
object of some canonical subobject of `Y`. -/
def IsSubobject (X Y : C) : Prop :=
  ∃ P : Subobject Y, Nonempty (X ≅ P)

infix:50 " ⊂ " => IsSubobject

/-- Source-facing dual bridge/view: `Y` is a quotient of `X` when `op Y` is a subobject of
`op X`. -/
abbrev IsQuotient (Y X : C) : Prop :=
  IsSubobject (op Y) (op X)

namespace ObjectProperty

/-- An object property has epi covers if every object receives an epimorphism from an object
satisfying the property. -/
class HasEpiCover (P : ObjectProperty C) : Prop where
  exists_epi : ∀ X : C, ∃ Y : C, P Y ∧ ∃ f : Y ⟶ X, Epi f

/-- Helper for Definition 12.5.3: the top object property covers each object by its identity
epimorphism. -/
theorem top_objectProperty_has_self_epi_cover (X : C) :
    ∃ Y : C, (⊤ : ObjectProperty C) Y ∧ ∃ f : Y ⟶ X, Epi f := by
  -- Choose the object itself as the covering object for the top property.
  refine ⟨X, ?_, 𝟙 X, inferInstance⟩
  -- Membership in the top object property is definitionally trivial.
  simp

/-- The maximal object property has epi covers, using the identity epimorphism of each object. -/
instance instHasEpiCoverTop : HasEpiCover (⊤ : ObjectProperty C) :=
  ⟨top_objectProperty_has_self_epi_cover⟩

end ObjectProperty

/-- Companion canonical bridge: `X` is a subobject of `Y` exactly when there exists a
monomorphism `X ⟶ Y`. -/
theorem isSubobject_iff_exists_mono :
    X ⊂ Y ↔ ∃ f : X ⟶ Y, Mono f := by
  constructor
  · rintro ⟨P, ⟨e⟩⟩
    exact ⟨e.hom ≫ P.arrow, inferInstance⟩
  · rintro ⟨f, hf⟩
    letI : Mono f := hf
    exact ⟨Subobject.mk f, ⟨(Subobject.underlyingIso f).symm⟩⟩

/-- Source-facing bridge to the textbook wording: `X` is a subobject of `Y` exactly when there
exists an injective morphism `X ⟶ Y`, with injective understood as `IsZero (kernel f)`. -/
theorem isSubobject_iff_exists_isInjective [Preadditive C] [HasKernels C] :
    X ⊂ Y ↔ ∃ f : X ⟶ Y, IsInjective f := by
  rw [isSubobject_iff_exists_mono]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (isInjective_iff_mono f).2 hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, (isInjective_iff_mono f).1 hf⟩

/-- Companion canonical bridge: `Y` is a quotient of `X` exactly when there exists an
epimorphism `X ⟶ Y`. -/
theorem isQuotient_iff_exists_epi :
    IsQuotient Y X ↔ ∃ f : X ⟶ Y, Epi f := by
  rw [IsQuotient, isSubobject_iff_exists_mono]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.unop, by
      letI : Mono f := hf
      infer_instance⟩
  · rintro ⟨f, hf⟩
    exact ⟨f.op, by
      letI : Epi f := hf
      infer_instance⟩

/-- Source-facing dual bridge to the textbook wording: `Y` is a quotient of `X` exactly when there
exists a surjective morphism `X ⟶ Y`, with surjective understood as `IsZero (cokernel f)`. -/
theorem isQuotient_iff_exists_isSurjective [Preadditive C] [HasCokernels C] :
    IsQuotient Y X ↔ ∃ f : X ⟶ Y, IsSurjective f := by
  rw [isQuotient_iff_exists_epi]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (isSurjective_iff_epi f).2 hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, (isSurjective_iff_epi f).1 hf⟩

end CategoryTheory
