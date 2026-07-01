import stacks_project.Chap13.Lemma_13_6_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.MorphismProperty

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable (H : D ⥤ A) [Functor.IsHomological H]

local notation "W" => H.homologicalKernel.trW

/- Domain-style sampling for Lemma 13.6.11:
- primary domain: homological functors and Verdier localization by the triangulated subcategory
  `H.homologicalKernel`;
- sampled owner declarations:
  `Functor.homologicalKernel`,
  `Functor.mem_homologicalKernel_trW_iff`,
  `ObjectProperty.IsStableUnderRetracts`,
  `Localization.Construction.lift`,
  `Localization.Construction.fac`,
  `Localization.Construction.uniq`;
- best owner abstraction: the canonical homological-kernel owner together with the strict
  localization lift through `W = H.homologicalKernel.trW`;
- primitive data: the homological functor `H`;
- derived API: `H.homologicalKernel`, its retract-stability instance, the Verdier morphism
  property `H.homologicalKernel.trW`, and the canonical lift/factorization/uniqueness package
  for `Q W`.

Source/core/bridge triage:
- `source-facing`: the homological kernel of `H` and the quotient by it;
- `core/canonical`: `Functor.homologicalKernel`, `Localization.Construction.lift`,
  `Localization.Construction.fac`, and `Localization.Construction.uniq`;
- `bridge/view`: the proof that `W` is inverted by `H`, extracted from
  `Functor.mem_homologicalKernel_trW_iff`.
-/

omit [IsTriangulated D] in
private theorem homologicalKernel_trW_isInvertedBy :
    H.homologicalKernel.trW.IsInvertedBy H := by
  letI := Functor.ShiftSequence.tautological H ℤ
  have hShift : H.homologicalKernel.trW.IsInvertedBy (H.shift (0 : ℤ)) := by
    intro X Y f hf
    exact ((Functor.mem_homologicalKernel_trW_iff (F := H) f).1 hf) 0
  rw [← MorphismProperty.IsInvertedBy.iff_of_iso H.homologicalKernel.trW (H.isoShiftZero ℤ)]
  exact hShift

/- Companion recall: the homological kernel is strictly full, i.e. closed under isomorphisms. -/
#check (inferInstance : ObjectProperty.IsClosedUnderIsomorphisms H.homologicalKernel)

/- Companion recall: the homological kernel is stable under retracts/direct summands. This is the
owner-level instance established in Lemma 13.6.3. -/
#check (inferInstance : ObjectProperty.IsStableUnderRetracts H.homologicalKernel)

/- Companion recall: the homological kernel is a triangulated object property. -/
#check (inferInstance : ObjectProperty.IsTriangulated H.homologicalKernel)

/- Lemma 13.6.11 recalls directly that, for a homological functor `H`, the class of morphisms
`f` such that every shifted morphism `(H.shift n).map f` is an isomorphism is the canonical
Verdier morphism property `H.homologicalKernel.trW`. -/
#check Functor.mem_homologicalKernel_trW_iff

/- Lemma 13.6.11: if `S` is the class of morphisms of `D` whose images under every shifted
functor `H^n` are isomorphisms, then the factorization of `H` through the localization
`Q : D ⥤ S.Localization` is the canonical strict localization lift, and uniqueness is given by
the strict universal property of `Q`. Via `Functor.mem_homologicalKernel_trW_iff`, this is the
owner-level specialization to `S = H.homologicalKernel.trW`. -/
#check
  (Localization.Construction.lift H (homologicalKernel_trW_isInvertedBy H) :
    Localization (H.homologicalKernel.trW) ⥤ A)

#check
  Localization.Construction.fac H (homologicalKernel_trW_isInvertedBy H)

#check
  Localization.Construction.uniq

end

end CategoryTheory
