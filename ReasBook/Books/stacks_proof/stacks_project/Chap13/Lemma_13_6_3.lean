import Mathlib
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts

noncomputable section

universe v₁ u₁ v₂ u₂

section

variable {D : Type u₁} [Category.{v₁} D] [HasShift D ℤ]
variable {A : Type u₂} [Category.{v₂} A] [HasZeroMorphisms A]
variable (H : D ⥤ A)

/- Domain-style sampling for Lemma 13.6.3:
- primary domain: homological functors and the object property cut out by the vanishing of all
  shifted values;
- sampled owner declarations:
  `Functor.homologicalKernel`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left` / `of_biprod_right`;
- best owner abstraction: the canonical object property `H.homologicalKernel`;
- primitive data: only the functor `H`;
- derived API: closure under isomorphisms, retract-stability/direct-summand closure, and the
  induced pretriangulated/triangulated structures on the full subcategory once `H` is assumed
  homological.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that the homological-kernel subcategory is saturated under
  direct summands;
- `core/canonical`: `Functor.homologicalKernel`;
- `bridge/view`: the direct-summand theorem for the specific biproduct presentation.

The mathematically essential extra owner fact here is retract-stability of
`H.homologicalKernel`; this does not actually use homologicality of `H`, and once it is
available the biproduct statement is just the generic direct-summand API. -/

/-- The object property `H.homologicalKernel` is stable under retracts. -/
instance : IsStableUnderRetracts H.homologicalKernel where
  of_retract r hY n := by
    let F := shiftFunctor D n ⋙ H
    letI : IsSplitMono (F.map r.i) := ⟨⟨(r.map F).splitMono⟩⟩
    exact (IsZero.iff_isSplitMono_eq_zero (F.map r.i)).2 ((hY n).eq_of_tgt _ _)

/- Companion recall: the full subcategory cut out by the vanishing conditions
`H.obj (X⟦n⟧)` for all `n : ℤ` is strictly full. This is exactly the canonical instance
`H.homologicalKernel.IsClosedUnderIsomorphisms`. -/
#check (inferInstance : H.homologicalKernel.IsClosedUnderIsomorphisms)

end

section

variable {D : Type u₁} [Category.{v₁} D] [HasShift D ℤ] [HasZeroMorphisms D]
variable {A : Type u₂} [Category.{v₂} A] [HasZeroMorphisms A]
variable (H : D ⥤ A)

-- Proof sketch: view the statement as one about the owner object property
-- `H.homologicalKernel`, note that it is stable under retracts, and then apply the generic
-- direct-summand lemmas `of_biprod_left` and `of_biprod_right`.
/-- Lemma 13.6.3: if `X ⊞ Y` lies in the homological kernel of `H`, then both `X` and `Y`
lie in the kernel; equivalently, the associated full subcategory is saturated in the Stacks
sense. -/
@[stacks 05RD]
theorem homologicalKernel_of_biprod
    {X Y : D} [HasBinaryBiproduct X Y] (hXY : H.homologicalKernel (X ⊞ Y)) :
    H.homologicalKernel X ∧ H.homologicalKernel Y :=
  ⟨of_biprod_left H.homologicalKernel hXY, of_biprod_right H.homologicalKernel hXY⟩

end

section

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [(n : ℤ) → (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable (H : D ⥤ A) [Functor.IsHomological H]

/- Companion recall: the full subcategory defined by the homological kernel carries the canonical
pretriangulated structure induced from the ambient pretriangulated category. This is exactly the
canonical instance `Pretriangulated H.homologicalKernel.FullSubcategory`. -/
#check (inferInstance : Pretriangulated H.homologicalKernel.FullSubcategory)

variable [IsTriangulated D]

/- Companion recall: if the ambient category `D` is triangulated, then the full subcategory
defined by the homological kernel is triangulated. This is exactly the canonical instance
`IsTriangulated H.homologicalKernel.FullSubcategory`. -/
#check (inferInstance : IsTriangulated H.homologicalKernel.FullSubcategory)

end
