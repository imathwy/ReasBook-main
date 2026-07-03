import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_6_1 (from Chap13) -/
namespace CategoryTheory.ObjectProperty

universe v u

/- Domain-style sampling for Definition 13.6.1:
- primary domain: saturated full subcategories of pretriangulated/triangulated categories,
  expressed as retract-stable object properties;
- inspected owner/bridge declarations:
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.prop_of_retract`,
  `ObjectProperty.retractClosure`,
  `CategoryTheory.trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts`;
- best owner abstraction: `ObjectProperty.IsStableUnderRetracts`;
- primitive-vs-derived split:
  primitive data: the retract-closure axiom `of_retract`;
  derived API: closure under isomorphisms, biproduct/direct-summand closure in additive settings,
    the retract-closure owner `P.retractClosure`, and the Chapter 13 comparison with saturated
    multiplicative systems.

Source/core/bridge triage:
- `source-facing`: the Stacks notion that a full pretriangulated subcategory is saturated, i.e.
  closed under direct summands;
- `core/canonical`: `ObjectProperty.IsStableUnderRetracts`;
- `bridge/view`: downstream equivalences such as
  `trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts`. -/

/- Definition 13.6.1: for an object property `P`, the textbook saturation condition on the
corresponding full pretriangulated subcategory is the canonical owner predicate
`P.IsStableUnderRetracts`; in additive/pretriangulated settings this is the same direct-summand
closure condition used in the source. -/
recall IsStableUnderRetracts

section

variable {C : Type u} [Category.{v} C] {P Q : ObjectProperty C}

/-- The intersection of retract-stable object properties is retract-stable. -/
instance [P.IsStableUnderRetracts] [Q.IsStableUnderRetracts] :
    (P ⊓ Q).IsStableUnderRetracts where
  of_retract r h := ⟨P.prop_of_retract r h.1, Q.prop_of_retract r h.2⟩

end

end CategoryTheory.ObjectProperty

/-! ### Lemma_13_6_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.6.2:
- primary domain: kernels of exact functors between pretriangulated categories, expressed as
  object properties and their induced full subcategories;
- sampled owner declarations:
  `Functor.kernel`,
  `ObjectProperty.inverseImage`,
  `ObjectProperty.IsTriangulated`,
  `IsTriangulated P.FullSubcategory`;
- best owner abstraction: `Functor.kernel F`, i.e. the inverse image of the owner property
  `IsZero` along `F`;
- primitive data: only the object property `IsZero` on the target category and the inverse-image
  construction along `F`;
- derived API: closure under isomorphisms, stability under retracts, triangulatedity of the
  kernel object property, and the induced triangulated structure on its full subcategory;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma that the kernel of an exact functor is strictly full,
    saturated, and triangulated;
  `core/canonical`: `Functor.kernel F` together with the owner predicates on object properties;
  `bridge/view`: the full-subcategory realization `(Functor.kernel F).FullSubcategory`.

The only missing reusable owner facts are that `IsZero` is stable under retracts and
triangulated, plus that retract-stability is preserved by inverse image. Closure under
isomorphisms is then inherited from the generic retract-stability API.
Once those owner instances are present, all four statements of the lemma are direct recalls.
-/

namespace ObjectProperty

instance isZero_isStableUnderRetracts {C : Type u} [Category.{v₁} C] :
    IsStableUnderRetracts (IsZero : ObjectProperty C) where
  of_retract r hY := by
    refine ⟨?_, ?_⟩
    · intro Z
      refine ⟨⟨⟨r.i ≫ hY.to_ Z⟩, ?_⟩⟩
      intro f
      calc
        f = (r.i ≫ r.r) ≫ f := by simp [r.retract]
        _ = r.i ≫ (r.r ≫ f) := by simp
        _ = r.i ≫ hY.to_ Z := by rw [hY.eq_to (r.r ≫ f)]
    · intro Z
      refine ⟨⟨⟨hY.from_ Z ≫ r.r⟩, ?_⟩⟩
      intro f
      calc
        f = f ≫ (r.i ≫ r.r) := by simp [r.retract]
        _ = (f ≫ r.i) ≫ r.r := by simp
        _ = hY.from_ Z ≫ r.r := by rw [hY.eq_from (f ≫ r.i)]

instance inverseImage_isStableUnderRetracts
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty D) [P.IsStableUnderRetracts] (F : C ⥤ D) :
    (P.inverseImage F).IsStableUnderRetracts where
  of_retract r hY := P.prop_of_retract (r.map F) hY

instance isZero_isStableUnderShift
    {C : Type u} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    IsStableUnderShift (IsZero : ObjectProperty C) ℤ where
  isStableUnderShiftBy n := ⟨fun _ hX ↦ Functor.map_isZero (shiftFunctor C n) hX⟩

instance isZero_isTriangulated
    {C : Type u} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] :
    ObjectProperty.IsTriangulated (IsZero : ObjectProperty C) where
  exists_zero := ⟨0, isZero_zero C, isZero_zero C⟩
  toIsStableUnderShift := inferInstance
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦ T.isZero₂_of_isZero₁₃ hT h₁ h₃)

end ObjectProperty

section StrictlyFull

variable {D : Type u₁} [Category.{v₁} D]
variable {D' : Type u₂} [Category.{v₂} D']
variable (F : D ⥤ D')

/- Lemma 13.6.2 (1): the objects of `D` sent to zero by `F` are closed under isomorphisms. This
is exactly the canonical instance on `Functor.kernel F`. -/
#check (inferInstance : ObjectProperty.IsClosedUnderIsomorphisms (Functor.kernel F))

end StrictlyFull

section KernelTriangulated

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type u₂} [Category.{v₂} D'] [HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
variable (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/- Lemma 13.6.2 (2): the kernel object property is stable under retracts. This is the canonical
inverse-image instance, specialized to the owner property `IsZero`. -/
#check (inferInstance : ObjectProperty.IsStableUnderRetracts (Functor.kernel F))

/- Lemma 13.6.2 (3): the kernel object property is triangulated. This is the canonical inverse
image of the triangulated owner property `IsZero`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (Functor.kernel F))

section

variable [CategoryTheory.IsTriangulated D]

/- Lemma 13.6.2 (4): if the ambient category is triangulated, then the full subcategory cut out by
`Functor.kernel F` is triangulated. This is the generic full-subcategory instance. -/
#check (inferInstance : CategoryTheory.IsTriangulated (Functor.kernel F).FullSubcategory)

end

end KernelTriangulated

end CategoryTheory

/-! ### Lemma_13_6_3 (from Chap13) -/
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
instance homologicalKernel_isStableUnderRetracts :
    IsStableUnderRetracts H.homologicalKernel where
  of_retract r hY n := by
    letI : IsSplitMono ((shiftFunctor D n ⋙ H).map r.i) :=
      ⟨⟨(r.map (shiftFunctor D n ⋙ H)).splitMono⟩⟩
    exact (Limits.IsZero.iff_isSplitMono_eq_zero ((shiftFunctor D n ⋙ H).map r.i)).2
      ((hY n).eq_of_tgt _ _)

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

/-! ### Lemma_13_6_4 (from Chap13) -/
universe v₁ v₂ u₁ u₂

open CategoryTheory

namespace CategoryTheory

open Limits ObjectProperty Pretriangulated
open scoped ZeroObject

namespace Functor

/-
Domain-style sampling for Lemma 13.6.4:
- primary domain: full triangulated subcategories cut out by eventual vanishing of the shifted
  values of a homological functor;
- sampled owner declarations:
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsTriangulated`,
  `Functor.homologicalKernel`;
- best owner abstraction: the source-facing owners are the three Stacks full subcategories
  `D_H^+`, `D_H^-`, and `D_H^b`, each presented as a full subcategory cut out by a canonical
  `ObjectProperty`;
- primitive data: the one-sided eventual-vanishing predicates on the shifted values
  `H.obj (X⟦n⟧)`;
- derived API: the two-sided bounded owner as the intersection of the one-sided owners, together
  with retract stability, triangulatedity, and the induced triangulated structures on the full
  subcategories;
- source/core/bridge triage:
  `source-facing`: the full subcategories
    `H.shiftVanishingPlus.FullSubcategory`,
    `H.shiftVanishingMinus.FullSubcategory`, and
    `H.shiftVanishingBounded.FullSubcategory`;
  `core/canonical`: the owner predicates `H.shiftVanishingPlus`, `H.shiftVanishingMinus`,
    `H.shiftVanishingBounded`;
  `bridge/view`: the `_iff` lemmas translating those owners into the textbook eventual-vanishing
    conditions.

The refinement therefore keeps the object-property layer as the canonical core, and the public
theorem surface uses the corresponding full subcategories directly.
-/

private inductive ShiftVanishingDirection where
  | plus
  | minus

section Basic

variable {D : Type u₁} [Category.{v₁} D] [HasShift D ℤ]
variable {A : Type u₂} [Category.{v₂} A] [HasZeroMorphisms A]

private def oneSidedShiftVanishing (H : D ⥤ A) (direction : ShiftVanishingDirection) :
    ObjectProperty D :=
  fun X ↦
    match direction with
    | .plus =>
        ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero (H.obj (X⟦n⟧))
    | .minus =>
        ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (H.obj (X⟦n⟧))

/-- The source-facing object property defining the Stacks subcategory `D_H^+`: the shifted values
`H(X[n])` vanish for all sufficiently negative shifts `n`. -/
def shiftVanishingPlus (H : D ⥤ A) : ObjectProperty D :=
  oneSidedShiftVanishing H .plus

/-- The source-facing object property defining the Stacks subcategory `D_H^-`: the shifted values
`H(X[n])` vanish for all sufficiently positive shifts `n`. -/
def shiftVanishingMinus (H : D ⥤ A) : ObjectProperty D :=
  oneSidedShiftVanishing H .minus

/-- The source-facing object property defining the Stacks subcategory `D_H^b`: the shifted values
`H(X[n])` vanish for all shifts `n` of sufficiently large absolute value. -/
def shiftVanishingBounded (H : D ⥤ A) : ObjectProperty D :=
  H.shiftVanishingPlus ⊓ H.shiftVanishingMinus

scoped[ShiftVanishingSubcategory] notation3:max "D⁺_{" H "}" =>
  (Functor.shiftVanishingPlus H).FullSubcategory
scoped[ShiftVanishingSubcategory] notation3:max "D⁻_{" H "}" =>
  (Functor.shiftVanishingMinus H).FullSubcategory
scoped[ShiftVanishingSubcategory] notation3:max "Dᵇ_{" H "}" =>
  (Functor.shiftVanishingBounded H).FullSubcategory

/-- The source-facing object property of objects `X` whose shifted `H`-values vanish outside the
interval `[a, b]`. -/
def shiftVanishingIn (H : D ⥤ A) [H.ShiftSequence ℤ] (a b : ℤ) : ObjectProperty D :=
  fun X ↦ ∀ n : ℤ, n ∉ Set.Icc a b → IsZero ((H.shift n).obj X)

omit [HasZeroMorphisms A] in
/-- Unfolding `shiftVanishingPlus` recovers the textbook definition of the full subcategory
`D_H^+`. -/
theorem mem_shiftVanishingPlus_iff (H : D ⥤ A) (X : D) :
    H.shiftVanishingPlus X ↔
      ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero (H.obj (X⟦n⟧)) :=
  Iff.rfl

omit [HasZeroMorphisms A] in
/-- Unfolding `shiftVanishingMinus` recovers the textbook definition of the full subcategory
`D_H^-`. -/
theorem mem_shiftVanishingMinus_iff (H : D ⥤ A) (X : D) :
    H.shiftVanishingMinus X ↔
      ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (H.obj (X⟦n⟧)) :=
  Iff.rfl

omit [HasZeroMorphisms A] in
/-- Unfolding `shiftVanishingBounded` recovers the textbook definition of the full subcategory
`D_H^b`. -/
theorem mem_shiftVanishingBounded_iff (H : D ⥤ A) (X : D) :
    H.shiftVanishingBounded X ↔
      ∃ N : ℕ, ∀ n : ℤ, N ≤ Int.natAbs n → IsZero (H.obj (X⟦n⟧)) := by
  constructor
  · rintro ⟨⟨Nplus, hplus⟩, ⟨Nminus, hminus⟩⟩
    refine ⟨max Nplus.natAbs Nminus.natAbs, fun n hn ↦ ?_⟩
    by_cases hnn : n < 0
    · apply hplus n
      have hnatAbs : Nplus.natAbs ≤ Int.natAbs n := le_trans (le_max_left _ _) hn
      omega
    · apply hminus n
      have hnatAbs : Nminus.natAbs ≤ Int.natAbs n := le_trans (le_max_right _ _) hn
      omega
  · rintro ⟨N, hN⟩
    refine ⟨⟨-(N : ℤ), ?_⟩, ⟨(N : ℤ), ?_⟩⟩
    · intro n hn
      exact hN n <| by
        have hn0 : n ≤ 0 := by omega
        have hnatAbs : (N : ℤ) ≤ (n.natAbs : ℤ) := by
          rw [Int.ofNat_natAbs_of_nonpos hn0]
          omega
        exact_mod_cast hnatAbs
    · intro n hn
      exact hN n <| by
        have hn0 : 0 ≤ n := by omega
        have hnatAbs : (N : ℤ) ≤ (n.natAbs : ℤ) := by
          simpa [Int.natAbs_of_nonneg hn0] using hn
        exact_mod_cast hnatAbs

omit [HasZeroMorphisms A] in
/-- Unfolding `shiftVanishingIn` recovers the exact interval-vanishing condition on shifted
values of `H`. -/
theorem mem_shiftVanishingIn_iff (H : D ⥤ A) [H.ShiftSequence ℤ] (a b : ℤ) (X : D) :
    H.shiftVanishingIn a b X ↔
      ∀ n : ℤ, n ∉ Set.Icc a b → IsZero ((H.shift n).obj X) :=
  Iff.rfl

private lemma isZero_obj_shift_of_retract (H : D ⥤ A) {X Y : D} (r : Retract X Y) (n : ℤ)
    (hY : IsZero (H.obj (Y⟦n⟧))) : IsZero (H.obj (X⟦n⟧)) := by
  letI : IsSplitMono ((shiftFunctor D n ⋙ H).map r.i) :=
    ⟨⟨(r.map (shiftFunctor D n ⋙ H)).splitMono⟩⟩
  exact (IsZero.iff_isSplitMono_eq_zero ((shiftFunctor D n ⋙ H).map r.i)).2
    (hY.eq_of_tgt _ _)

omit [HasZeroMorphisms A] in
private lemma isZero_obj_shift_of_isZero_obj_add_shift (H : D ⥤ A) (X : D) (a n : ℤ)
    (h : IsZero (H.obj (X⟦a + n⟧))) : IsZero (H.obj ((X⟦a⟧)⟦n⟧)) :=
  h.of_iso (H.mapIso ((shiftFunctorAdd D a n).app X).symm)

private theorem oneSidedShiftVanishing_isStableUnderRetracts
    (H : D ⥤ A) (direction : ShiftVanishingDirection) :
    (oneSidedShiftVanishing H direction).IsStableUnderRetracts where
  of_retract r hY := by
    cases direction with
    | plus =>
        rcases hY with ⟨N, hN⟩
        exact ⟨N, fun n hn ↦ isZero_obj_shift_of_retract H r n (hN n hn)⟩
    | minus =>
        rcases hY with ⟨N, hN⟩
        exact ⟨N, fun n hn ↦ isZero_obj_shift_of_retract H r n (hN n hn)⟩

/-- Eventual negative-shift vanishing is stable under retracts. -/
instance shiftVanishingPlus_isStableUnderRetracts (H : D ⥤ A) :
    H.shiftVanishingPlus.IsStableUnderRetracts := by
  simpa [shiftVanishingPlus, oneSidedShiftVanishing] using
    oneSidedShiftVanishing_isStableUnderRetracts H .plus

/-- Eventual positive-shift vanishing is stable under retracts. -/
instance shiftVanishingMinus_isStableUnderRetracts (H : D ⥤ A) :
    H.shiftVanishingMinus.IsStableUnderRetracts := by
  simpa [shiftVanishingMinus, oneSidedShiftVanishing] using
    oneSidedShiftVanishing_isStableUnderRetracts H .minus

/-- Eventual two-sided shift vanishing is stable under retracts. -/
instance shiftVanishingBounded_isStableUnderRetracts (H : D ⥤ A) :
    H.shiftVanishingBounded.IsStableUnderRetracts := by
  simpa [shiftVanishingBounded] using
    (inferInstance :
      (H.shiftVanishingPlus ⊓ H.shiftVanishingMinus).IsStableUnderRetracts)

end Basic

section Triangulated

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]

private lemma isZero_obj₂_of_distinguished (H : D ⥤ A) [H.IsHomological] {T : Triangle D}
    (hT : T ∈ distTriang D) (n : ℤ) (h₁ : IsZero (H.obj (T.obj₁⟦n⟧)))
    (h₃ : IsZero (H.obj (T.obj₃⟦n⟧))) : IsZero (H.obj (T.obj₂⟦n⟧)) :=
  (H.map_distinguished_exact _ (Triangle.shift_distinguished T hT n)).isZero_of_both_zeros
    (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

private theorem oneSidedShiftVanishing_isTriangulated
    (H : D ⥤ A) [H.IsHomological] (direction : ShiftVanishingDirection) :
    (oneSidedShiftVanishing H direction).IsTriangulated := by
  letI : (oneSidedShiftVanishing H direction).IsStableUnderRetracts :=
    oneSidedShiftVanishing_isStableUnderRetracts H direction
  refine
    { exists_zero := ?_
      toIsStableUnderShift := ?_
      toIsTriangulatedClosed₂ := ?_ }
  · refine ⟨0, isZero_zero D, ?_⟩
    cases direction with
    | plus =>
        exact ⟨0, fun n _ ↦ (shiftFunctor D n ⋙ H).map_isZero (isZero_zero D)⟩
    | minus =>
        exact ⟨0, fun n _ ↦ (shiftFunctor D n ⋙ H).map_isZero (isZero_zero D)⟩
  · exact ⟨fun a ↦ ⟨fun X hX ↦ by
      cases direction with
      | plus =>
          rcases hX with ⟨N, hN⟩
          refine ⟨N - a, fun n hn ↦ ?_⟩
          exact isZero_obj_shift_of_isZero_obj_add_shift H X a n (hN (a + n) (by omega))
      | minus =>
          rcases hX with ⟨N, hN⟩
          refine ⟨N - a, fun n hn ↦ ?_⟩
          exact isZero_obj_shift_of_isZero_obj_add_shift H X a n (hN (a + n) (by omega))⟩⟩
  · exact .mk' <| by
      intro T hT h₁ h₃
      cases direction with
      | plus =>
          rcases h₁ with ⟨N₁, h₁⟩
          rcases h₃ with ⟨N₃, h₃⟩
          refine ⟨min N₁ N₃, fun n hn ↦ ?_⟩
          exact isZero_obj₂_of_distinguished H hT n
            (h₁ n (le_trans hn (min_le_left _ _)))
            (h₃ n (le_trans hn (min_le_right _ _)))
      | minus =>
          rcases h₁ with ⟨N₁, h₁⟩
          rcases h₃ with ⟨N₃, h₃⟩
          refine ⟨max N₁ N₃, fun n hn ↦ ?_⟩
          exact isZero_obj₂_of_distinguished H hT n
            (h₁ n (le_trans (le_max_left _ _) hn))
            (h₃ n (le_trans (le_max_right _ _) hn))

/-- The object property defining `D_H^+` is triangulated. -/
instance shiftVanishingPlus_isTriangulated (H : D ⥤ A) [H.IsHomological] :
    H.shiftVanishingPlus.IsTriangulated := by
  simpa [shiftVanishingPlus, oneSidedShiftVanishing] using
    oneSidedShiftVanishing_isTriangulated H .plus

/-- The object property defining `D_H^-` is triangulated. -/
instance shiftVanishingMinus_isTriangulated (H : D ⥤ A) [H.IsHomological] :
    H.shiftVanishingMinus.IsTriangulated := by
  simpa [shiftVanishingMinus, oneSidedShiftVanishing] using
    oneSidedShiftVanishing_isTriangulated H .minus

/-- The object property defining `D_H^b` is triangulated. -/
instance shiftVanishingBounded_isTriangulated (H : D ⥤ A) [H.IsHomological] :
    H.shiftVanishingBounded.IsTriangulated := by
  simpa [shiftVanishingBounded] using
    (inferInstance : (H.shiftVanishingPlus ⊓ H.shiftVanishingMinus).IsTriangulated)

section

variable (H : D ⥤ A) [H.IsHomological] [CategoryTheory.IsTriangulated D]

open scoped ShiftVanishingSubcategory

/- Lemma 13.6.4, source-facing `D_H^+` form: the full subcategory `D⁺_{H}` is triangulated. -/
#check (inferInstance : CategoryTheory.IsTriangulated D⁺_{H})

/- Lemma 13.6.4, source-facing `D_H^-` form: the full subcategory `D⁻_{H}` is triangulated. -/
#check (inferInstance : CategoryTheory.IsTriangulated D⁻_{H})

/- Lemma 13.6.4, source-facing `D_H^b` form: the full subcategory `Dᵇ_{H}` is triangulated. -/
#check (inferInstance : CategoryTheory.IsTriangulated Dᵇ_{H})

end

end Triangulated

end Functor

end CategoryTheory

/-! ### Definition_13_6_5 (from Chap13) -/
open CategoryTheory

universe v₁ v₂ u₁ u₂

/-
Domain-style sampling for Definition 13.6.5:
- primary domain: strictly full triangulated subcategories cut out as kernels of exact or
  homological functors;
- sampled owner declarations:
  `Functor.kernel`,
  `Functor.homologicalKernel`,
  `ObjectProperty.IsTriangulated`,
  `Pretriangulated P.FullSubcategory`;
- best owner abstraction: the kernel object property attached to the functor itself, namely
  `Functor.kernel` in the exact-functor case and `Functor.homologicalKernel` in the homological
  case;
- primitive data:
  for `Functor.kernel`, only the functor `F : D ⥤ D'`;
  for `Functor.homologicalKernel`, only the functor `H : D ⥤ A` together with the shift on the
  source category;
- derived API: closure under isomorphisms, stability under retracts, triangulated structure on the
  object property, and the induced pretriangulated/triangulated structures on the full
  subcategory.

Source/core/bridge triage:
- `source-facing`: the kernel subcategory attached to an exact functor, and the vanishing
  subcategory attached to a homological functor;
- `core/canonical`: `Functor.kernel` and `Functor.homologicalKernel`;
- `bridge/view`: the corresponding full subcategories
  `F.kernel.FullSubcategory` and `H.homologicalKernel.FullSubcategory`, together with their
  induced triangulated structures.

No local wrapper is needed here: Definition 13.6.5 is a pure recall of the canonical owner
declarations already used by Lemmas 13.6.2 and 13.6.3.
-/

section

variable {D : Type u₁} [Category.{v₁} D]
variable {D' : Type u₂} [Category.{v₂} D']
variable (F : D ⥤ D')

/- Definition 13.6.5: for an exact functor `F : D ⥤ D'`, the kernel subcategory is the canonical
object property `F.kernel`, and its source-facing realization is the full subcategory
`F.kernel.FullSubcategory`; the exactness hypotheses only enter the derived triangulated closure
results of Lemma 13.6.2. -/
recall Functor.kernel
#check F.kernel.FullSubcategory

end

section

variable {D : Type u₁} [Category.{v₁} D] [HasShift D ℤ]
variable {A : Type u₂} [Category.{v₂} A]
variable (H : D ⥤ A)

/- Companion recall: for a homological functor `H : D ⥤ A`, the kernel subcategory is the
canonical object property `H.homologicalKernel`, and its source-facing realization is the full
subcategory `H.homologicalKernel.FullSubcategory`; the homological and abelian hypotheses only
enter the derived closure results recalled in Lemma 13.6.3. -/
recall Functor.homologicalKernel
#check H.homologicalKernel.FullSubcategory

end

/-! ### Lemma_13_6_6 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.MorphismProperty

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]
  (P : ObjectProperty D) [ObjectProperty.IsTriangulated P]

/- Domain-style sampling for Lemma `13.6.6`.
- primary domain: saturated compatible multiplicative systems arising from triangulated object
  properties in a triangulated category;
- sampled owner declarations:
  `P.isoClosure.trW`,
  `P.trW`,
  `P.trW_isoClosure`,
  `P.isoClosure.IsTriangulated`,
  `ObjectProperty.IsClosedUnderIsomorphisms`,
  `P.IsStableUnderRetracts`,
  `P.trW.IsMultiplicative`,
  `P.trW.IsCompatibleWithTriangulation`;
- best owner abstraction: the source-facing morphism-property owner is `P.isoClosure.trW`,
  attached to the strictly full triangulated subcategory `P.isoClosure`; `P.trW` is only the
  bridge view provided by `P.trW_isoClosure`;
- source/core/bridge triage:
  `source-facing`: the Stacks saturation condition for the strictly full triangulated subcategory
    attached to `P`, i.e. `P.isoClosure`, together with its canonical Verdier morphism property
    `P.isoClosure.trW`;
  `core/canonical`: the owners `P.isoClosure.trW`, `ObjectProperty.isoClosure`, and
    `ObjectProperty.IsStableUnderRetracts`;
  `bridge/view`: the comparison `P.trW_isoClosure` and the derived reformulation using `P.trW`,
    with the iso-closed specialization as a companion.
- primitive data: the triangulated object property `P`;
- derived API: the multiplicative-system and triangulation-compatibility instances on `P.trW`,
  the iso-closure `P.isoClosure`, the owner theorem on `P.isoClosure.trW`, and its iso-closed
  specialization on `P.trW`.

No extra local wrapper is needed here: the owner-level theorem should use `P.isoClosure.trW`
directly, and the iso-closed `P.trW` formulation should be derived from it rather than exposed
through an extra intermediate bridge theorem.
-/

/- Companion recall: for a triangulated object property `P`, the cone-defined morphism property
`P.trW` is already a multiplicative system by the canonical `trW` instance. -/
#check (inferInstance : MorphismProperty.IsMultiplicative P.trW)

/- Companion recall: for a triangulated object property `P`, the cone-defined morphism property
`P.trW` is already compatible with the triangulated structure by the canonical `trW` instance. -/
#check (inferInstance : MorphismProperty.IsCompatibleWithTriangulation P.trW)

-- Proof sketch: for the forward implication, use the saturation axiom for `P.isoClosure.trW` on
-- the standard distinguished triangles attached to a biproduct decomposition to show that
-- `P.isoClosure` is stable under retracts. For the reverse implication, follow the octahedral
-- argument from the text: if `f ≫ g` and `g ≫ h` lie in `P.isoClosure.trW`, then the cones of
-- these composites lie in `P.isoClosure`; use the octahedron to relate these cones to a cone of
-- `g`, and apply retract stability to conclude that the cone of `g` also lies in `P.isoClosure`.
/-- Lemma 13.6.6: for a triangulated object property `P` on a triangulated category `D`, the
canonical Verdier morphism property attached to the strictly full triangulated subcategory
`P.isoClosure`, namely `P.isoClosure.trW`, is a saturated multiplicative system if and only if
`P.isoClosure` is stable under retracts. -/
theorem isoClosure_trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts :
    IsSaturatedMultiplicativeSystem P.isoClosure.trW ↔ P.isoClosure.IsStableUnderRetracts := sorry

/-- If `P` is already closed under isomorphisms, Lemma 13.6.6 specializes to retract stability of
`P` itself. -/
theorem trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts
    [P.IsClosedUnderIsomorphisms] :
    IsSaturatedMultiplicativeSystem P.trW ↔ P.IsStableUnderRetracts := by
  simpa only [P.trW_isoClosure, P.isoClosure_eq_self] using
    (isoClosure_trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts P)

/-- If `P` is stable under retracts, then the cone-defined morphism property `P.trW` is a
saturated multiplicative system. -/
theorem trW_isSaturatedMultiplicativeSystem [P.IsStableUnderRetracts] :
    IsSaturatedMultiplicativeSystem P.trW :=
  (trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts P).2 inferInstance

instance [P.IsStableUnderRetracts] : IsSaturatedMultiplicativeSystem P.trW :=
  trW_isSaturatedMultiplicativeSystem P

end

end CategoryTheory

/-! ### Definition_13_6_7 (from Chap13) -/
open CategoryTheory
open scoped CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CategoryTheory.ObjectProperty

/-
Domain-style sampling for Definition `13.6.7`:
- primary domain: Verdier localization of a triangulated category by the cone-defined morphism
  property attached to a triangulated object property;
- sampled owner declarations:
  `ObjectProperty.trW`,
  `MorphismProperty.Localization`,
  `MorphismProperty.Q`,
  `Functor.IsLocalization`;
- best owner abstraction: for a triangulated object property `P`, the quotient is owned by the
  canonical localization API of the morphism property `P.trW`, while the source-facing bridge
  layer should expose the standard Verdier quotient notation `D / P` and quotient functor
  `P.trW.Q`;
- primitive data: the object property `P`, from which the Verdier morphism property `P.trW` is
  derived;
- derived API: the quotient category `D / P`, the quotient functor `P.trW.Q`, and the owner fact
  that `P.trW.Q` localizes at `P.trW`;
- source/core/bridge triage:
  `source-facing`: the textbook quotient category `D / P` of `D` by the triangulated
    subcategory `P`, together with the quotient functor `P.trW.Q`;
  `core/canonical`: `P.trW.Localization`, `P.trW.Q`, and `Functor.IsLocalization`;
  `bridge/view`: the identification of the textbook quotient with localization at the cone-defined
    morphism property `P.trW`.

Definition `13.6.7` is therefore a `bridge/view` item: it should recall the canonical
localization owner through the source-facing Verdier quotient surface rather than introduce
parallel local owners.
-/

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The Verdier quotient `D / P` is the canonical localization `P.trW.Localization`. -/
scoped instance verdierQuotientHDiv : HDiv (Type u) (ObjectProperty D) (Type u) where
  hDiv _ P := P.trW.Localization

scoped instance verdierQuotientCategory (P : ObjectProperty D) : Category (D / P) :=
  inferInstanceAs (Category P.trW.Localization)

end

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]
  (P : ObjectProperty D) [P.IsTriangulated]

instance verdierQuotientFunctorIsLocalization :
    (P.trW.Q : D ⥤ D / P).IsLocalization P.trW := by
  exact Functor.q_isLocalization P.trW

noncomputable instance verdierQuotientPreadditive : Preadditive (D / P) := by
  change Preadditive P.trW.Localization
  infer_instance

noncomputable instance verdierQuotientFunctorAdditive : (P.trW.Q : D ⥤ D / P).Additive := by
  infer_instance

noncomputable instance verdierQuotientHasZeroObject : Limits.HasZeroObject (D / P) := by
  change Limits.HasZeroObject P.trW.Localization
  infer_instance

noncomputable instance verdierQuotientHasShift : HasShift (D / P) ℤ := by
  change HasShift P.trW.Localization ℤ
  infer_instance

noncomputable instance verdierQuotientFunctorCommShift : (P.trW.Q : D ⥤ D / P).CommShift ℤ := by
  infer_instance

noncomputable instance verdierQuotientShiftAdditive (n : ℤ) :
    Functor.Additive (shiftFunctor (D / P) n) := by
  change Functor.Additive (shiftFunctor P.trW.Localization n)
  infer_instance

noncomputable instance verdierQuotientPretriangulated : Pretriangulated (D / P) := by
  change Pretriangulated P.trW.Localization
  infer_instance

noncomputable instance verdierQuotientFunctorIsTriangulated :
    (P.trW.Q : D ⥤ D / P).IsTriangulated := by
  infer_instance

noncomputable instance verdierQuotientIsTriangulated : IsTriangulated (D / P) := by
  change IsTriangulated P.trW.Localization
  infer_instance

/- Definition 13.6.7: the source-facing Verdier quotient of `D` by `P` is the canonical
localization `P.trW.Localization` of the cone-defined morphism property `P.trW`. -/
#check (D / P)

/- Companion recall: the quotient functor to this Verdier quotient is the canonical localization
functor on `P.trW`. -/
#check
  (P.trW.Q : D ⥤ D / P)

/- Companion recall: the quotient functor on `P.trW` localizes at the Verdier morphism
property `P.trW`. -/
#check (Functor.q_isLocalization P.trW)

end

end CategoryTheory.ObjectProperty

/-! ### Lemma_13_6_8 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.MorphismProperty
open CategoryTheory.MorphismProperty.IsInvertedBy
open scoped CategoryTheory.ObjectProperty

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

section

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (P : ObjectProperty D) [P.IsTriangulated]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable {D' : Type u₃} [Category.{v₃} D'] [Limits.HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

local instance trWQ_isLocalization : P.trW.Q.IsLocalization P.trW :=
  Functor.q_isLocalization P.trW

/-- Helper for Lemma 13.6.8: the Verdier quotient carries the canonical shift structure coming
from the localization `P.trW.Localization`. -/
local instance verdierQuotientHasShift : HasShift (D / P) ℤ := by
  change HasShift P.trW.Localization ℤ
  infer_instance

/-- Helper for Lemma 13.6.8: the Verdier quotient functor commutes with the canonical shift on the
quotient category. -/
local instance verdierQuotientFunctorCommShift : (P.trW.Q : D ⥤ D / P).CommShift ℤ := by
  infer_instance

/-- Helper for Lemma 13.6.8: the Verdier quotient carries the canonical pretriangulated structure
induced by localization. -/
local instance verdierQuotientPretriangulated : Pretriangulated (D / P) := by
  change Pretriangulated P.trW.Localization
  infer_instance

/-- Helper for Lemma 13.6.8: all shift functors on the Verdier quotient are additive because the
localized shifts on `P.trW.Localization` are additive. -/
local instance verdierQuotientShiftAdditive :
    ∀ n : ℤ, Functor.Additive (shiftFunctor (D / P) n) := by
  intro n
  change Functor.Additive (shiftFunctor P.trW.Localization n)
  infer_instance

/-- Helper for Lemma 13.6.8: the localization model `P.trW.Localization` carries additive shift
functors in the bundled `∀ n` form expected by the triangulated owner API. -/
local instance verdierLocalizationShiftAdditive :
    ∀ n : ℤ, Functor.Additive (shiftFunctor P.trW.Localization n) := by
  intro n
  infer_instance

/-- Helper for Lemma 13.6.8: the Verdier quotient is triangulated because `D` is triangulated and
`P` is a triangulated subcategory. -/
local instance verdierQuotientIsTriangulated : IsTriangulated (D / P) := by
  change IsTriangulated P.trW.Localization
  infer_instance

/-- Helper for Lemma 13.6.8: the Verdier quotient functor is triangulated with respect to the
canonical triangulated structure on the quotient. -/
local instance verdierQuotientFunctorIsTriangulated :
    (P.trW.Q : D ⥤ D / P).IsTriangulated := by
  letI : ∀ n : ℤ, Functor.Additive (shiftFunctor P.trW.Localization n) :=
    verdierLocalizationShiftAdditive P
  change (P.trW.Q : D ⥤ P.trW.Localization).IsTriangulated
  infer_instance

omit [IsTriangulated D] [P.IsTriangulated] in
/-- Helper for Lemma 13.6.8: if a homological functor vanishes on `P`, then it inverts every
morphism in the Verdier class `P.trW`. -/
private theorem trW_isInvertedBy_of_le_homologicalKernel
    (H : D ⥤ A) [H.IsHomological] (hP : P ≤ H.homologicalKernel) :
    IsInvertedBy P.trW H := by
  letI := Functor.ShiftSequence.tautological H ℤ
  -- First pass to the shift-zero companion, where `mem_homologicalKernel_trW_iff` applies
  -- directly to the source hypothesis `P ≤ H.homologicalKernel`.
  have hShift : IsInvertedBy P.trW (H.shift (0 : ℤ)) := by
    intro X Y f hf
    have hf' : H.homologicalKernel.trW f := by
      rcases hf with ⟨Z, g, h, hT, hZ⟩
      exact ⟨Z, g, h, hT, hP _ hZ⟩
    exact ((H.mem_homologicalKernel_trW_iff f).1 hf') 0
  -- The shift-zero functor is canonically isomorphic to `H`, so invertedness transfers back.
  rw [← MorphismProperty.IsInvertedBy.iff_of_iso P.trW (H.isoShiftZero ℤ)]
  exact hShift

omit [IsTriangulated D] [P.IsTriangulated] in
/-- Helper for Lemma 13.6.8: if an exact functor vanishes on `P`, then it inverts every morphism
in the Verdier class `P.trW`. -/
private theorem trW_isInvertedBy_of_le_kernel
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (hP : P ≤ F.kernel) :
    IsInvertedBy P.trW F := by
  -- Route correction: avoid proving exactness of the quotient lift directly; first identify the
  -- larger kernel-generated Verdier class that `F` already inverts.
  have hkernel : IsInvertedBy F.kernel.trW F := by
    intro X Y f hf
    simpa [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor F,
      MorphismProperty.inverseImage_iff, isomorphisms.iff] using hf
  refine of_le P.trW F.kernel.trW F hkernel ?_
  intro _ _ f hf
  rcases hf with ⟨Z, g, h, hT, hZ⟩
  exact ⟨Z, g, h, hT, hP _ hZ⟩

/-- Helper for Lemma 13.6.8: a strict quotient factorization of a homological functor is
homological. -/
private theorem strict_homological_factorization_isHomological
    (H : D ⥤ A) [H.IsHomological] (H' : D / P ⥤ A)
    (hfac : (P.trW.Q : D ⥤ D / P) ⋙ H' = H) :
    H'.IsHomological := by
  -- The quotient functor is essentially surjective on arrows, so homologicality descends.
  letI : Functor.EssSurj ((P.trW.Q).mapArrow) := Localization.essSurj_mapArrow P.trW.Q P.trW
  exact Functor.isHomological_of_localization P.trW.Q H' H (eqToIso hfac)

/-- Helper for Lemma 13.6.8: a strict quotient factorization of an exact functor carries the
canonical exact structure induced from localization. -/
private theorem strict_exact_factorization_has_exact_structure
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (F' : D / P ⥤ D')
    (hfac : (P.trW.Q : D ⥤ D / P) ⋙ F' = F) :
    ∃ hcomm : F'.CommShift ℤ, letI : F'.CommShift ℤ := hcomm; F'.IsTriangulated := by
  -- Route correction: package the strict factorization as a localization lifting and use the
  -- canonical shift structure produced by `Functor.commShiftOfLocalization`.
  letI : HasShift (D / P) ℤ := verdierQuotientHasShift P
  letI : (P.trW.Q : D ⥤ D / P).CommShift ℤ := verdierQuotientFunctorCommShift P
  letI : Pretriangulated (D / P) := verdierQuotientPretriangulated P
  letI : IsTriangulated (D / P) := verdierQuotientIsTriangulated P
  letI : Localization.Lifting P.trW.Q P.trW F F' := ⟨eqToIso hfac⟩
  let hcomm : F'.CommShift ℤ :=
    Functor.commShiftOfLocalization (P.trW.Q : D ⥤ D / P) P.trW ℤ F F'
  refine ⟨hcomm, ?_⟩
  letI : F'.CommShift ℤ := hcomm
  -- Exactness then descends along the quotient functor once the localization comparison iso is
  -- known to commute with shifts and the quotient is essentially surjective on arrows.
  letI : Functor.EssSurj ((P.trW.Q).mapArrow) := Localization.essSurj_mapArrow P.trW.Q P.trW
  letI : NatTrans.CommShift (Localization.Lifting.iso P.trW.Q P.trW F F').hom ℤ :=
    by
      -- With the canonical localization-induced `CommShift`, shift compatibility of the
      -- comparison isomorphism is already packaged by mathlib.
      exact inferInstanceAs (NatTrans.CommShift
        (Localization.Lifting.iso P.trW.Q P.trW F F').hom ℤ)
  letI : ∀ n : ℤ, Functor.Additive (shiftFunctor P.trW.Localization n) :=
    verdierLocalizationShiftAdditive P
  letI : Pretriangulated P.trW.Localization := by
    simpa using (verdierQuotientPretriangulated (P := P) : Pretriangulated (D / P))
  letI : IsTriangulated P.trW.Localization := by
    simpa using (verdierQuotientIsTriangulated (P := P) : IsTriangulated (D / P))
  -- Isolate the final owner theorem in a smaller subproof so elaboration sees the local exact
  -- structure on the quotient functor directly.
  let htri : F'.IsTriangulated := by
    letI : (P.trW.Q : D ⥤ D / P).IsTriangulated := by
      exact Triangulated.Localization.isTriangulated_functor (L := P.trW.Q) (W := P.trW)
    exact Functor.isTriangulated_of_precomp_iso
      (F := (P.trW.Q : D ⥤ D / P)) (G := F') (H := F)
      (Localization.Lifting.iso P.trW.Q P.trW F F')
  exact htri

/- Domain-style sampling for Lemma `13.6.8`.
- primary domain: Verdier localization of triangulated categories and factorization of functors
  through the quotient by a triangulated subcategory;
- sampled owner declarations:
  `Localization.Construction.lift`,
  `Localization.Construction.fac`,
  `Localization.liftNatIso`,
  `homological_factorization_isHomological`,
  `exact_factorization_isTriangulated`;
- best owner abstraction: the quotient functor `P.trW.Q` together with its canonical
  localization lifts; the source-facing theorem here needs the strict construction
  lift `Localization.Construction.lift` because the statement asks for literal equality
  `P.trW.Q ⋙ H' = H`, while homologicality and exactness should still be imported from the
  canonical localization-lift theorems rather than reproved locally;
- primitive data: a functor `H` or `F` together with the source-faithful hypothesis that `P`
  lies in its homological kernel or ordinary kernel, equivalently that `P.trW` is inverted;
- derived API: the lifted functor through `P.trW.Q`, its factorization equality, uniqueness, and
  the induced homological / triangulated structure.

Source/core/bridge triage:
- `source-facing`: the two existence-and-uniqueness statements below, matching the textbook lemma;
- `core/canonical`: `Localization.Construction.lift` / `fac` / `uniq`,
  `Localization.liftNatIso`, and the owner theorems
  `homological_factorization_isHomological` / `exact_factorization_isTriangulated`;
- `bridge/view`: the passage from the source hypothesis `P ≤ H.homologicalKernel` or
  `P ≤ F.kernel` to the inverted-morphism hypothesis needed by the localization owner,
  and then from the strict construction lift to the canonical localization lift up to iso.

Accordingly, this file keeps the source-facing existential statements, while direct downstream use
should prefer the canonical localization lift itself rather than re-extracting a witness from
`∃!`. -/

-- Proof sketch: the hypothesis `P ≤ H.homologicalKernel` implies that every morphism in `P.trW`
-- is inverted by `H`. The source-facing statement asks for a strict factorization equality, so we
-- take the strict construction lift `Localization.Construction.lift H hH`. To import the
-- homological structure canonically, compare this strict lift with the canonical localization lift
-- `Localization.lift H hH P.trW.Q` via `Localization.liftNatIso`, and transfer the owner theorem
-- `homological_factorization_isHomological`.
/-- Lemma 13.6.8 (1): if a homological functor `H : D ⥤ A` vanishes on the full triangulated
subcategory `P`, then there exists a unique factorization of `H` through the Verdier quotient
functor `P.trW.Q : D ⥤ D / P`, and the factor functor is homological. -/
theorem existsUnique_homological_factorization_through_triangulated_quotient
    (H : D ⥤ A) [H.IsHomological] (hP : P ≤ H.homologicalKernel) :
    ∃! H' : D / P ⥤ A, P.trW.Q ⋙ H' = H ∧ H'.IsHomological := by
  -- The source hypothesis identifies the exact morphism property needed by localization.
  have hH : P.trW.IsInvertedBy H := trW_isInvertedBy_of_le_homologicalKernel P H hP
  let hQ := Localization.strictUniversalPropertyFixedTargetQ P.trW A
  let H' : D / P ⥤ A := hQ.lift H hH
  refine ⟨H', ?_, ?_⟩
  · refine ⟨hQ.fac H hH, ?_⟩
    -- The strict lift is homological by the localization descent helper.
    exact strict_homological_factorization_isHomological P H H' (hQ.fac H hH)
  · intro H'' hH''
    -- Uniqueness is the strict universal property of the quotient functor.
    exact hQ.uniq _ _ (hH''.1.trans (hQ.fac H hH).symm)

-- Proof sketch: since `P ≤ F.kernel`, every morphism in `P.trW` is sent by `F` to an
-- isomorphism, so the strict construction lift gives the required literal factorization. The
-- exact structure on this strict lift comes from the owner API for localization lifts:
-- `Functor.commShiftOfLocalization` provides the induced `CommShift ℤ` structure, and
-- `Functor.isTriangulated_of_precomp_iso` upgrades it to a triangulated functor.
/-- Lemma 13.6.8 (2): if an exact functor `F : D ⥤ D'` vanishes on the full triangulated
subcategory `P`, then there exists a unique factorization of `F` through the Verdier quotient
functor `P.trW.Q : D ⥤ D / P`, and the factor functor is exact; in Lean, exactness is encoded by
the existence of a `CommShift ℤ` structure together with `Functor.IsTriangulated`. -/
theorem existsUnique_exact_factorization_through_triangulated_quotient
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (hP : P ≤ F.kernel) :
    ∃! F' : D / P ⥤ D',
      (P.trW.Q ⋙ F' = F) ∧
        ∃ hcomm : F'.CommShift ℤ, letI : F'.CommShift ℤ := hcomm; F'.IsTriangulated := by
  let hF : P.trW.IsInvertedBy F := trW_isInvertedBy_of_le_kernel P F hP
  let hQ := Localization.strictUniversalPropertyFixedTargetQ P.trW D'
  let F' : D / P ⥤ D' := hQ.lift F hF
  refine ⟨F', ?_, ?_⟩
  · refine ⟨hQ.fac F hF, ?_⟩
    -- The strict lift inherits its exact structure from the canonical localization lifting data.
    exact strict_exact_factorization_has_exact_structure P F F' (hQ.fac F hF)
  · intro F'' hF''
    -- Again, strict uniqueness comes from the localization universal property.
    exact hQ.uniq _ _ (hF''.1.trans (hQ.fac F hF).symm)

end

end CategoryTheory

/-! ### Lemma_13_6_9 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ObjectProperty.IsStableUnderRetracts
open CategoryTheory.Pretriangulated
open scoped ZeroObject CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
variable (P : ObjectProperty D) [P.IsTriangulated]

/- Domain-style sampling for Lemma 13.6.9:
- primary domain: Verdier localization of a triangulated category by the cone-defined morphism
  property of a triangulated object property, together with retract closure on the object-property
  side;
- sampled owner declarations:
  `Functor.kernel P.trW.Q`,
  `ObjectProperty.retractClosure`,
  `ObjectProperty.prop_retractClosure_iff`,
  `ObjectProperty.retractClosure_le_iff`,
  `CategoryTheory.Retract`,
  `localization_object_isZero_tfae_of_compatibleWithTriangulation`,
  `trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts`;
- best owner abstraction: the core object-property owner is `P.retractClosure`; the kernel
  `Functor.kernel P.trW.Q` is the Verdier-localization view on that owner, while the intrinsic
  source-facing direct-summand witness is `Retract`;
- primitive-vs-derived split:
  primitive data: the triangulated object property `P`;
  derived API: the kernel/retract-closure identification, its source-facing direct-summand
    consequence, and the initiality statement against retract-stable triangulated object
    properties.

Source/core/bridge triage:
- `source-facing`: the kernel of the quotient by `P` and its direct-summand characterization;
- `core/canonical`: `P.retractClosure`, `Functor.kernel P.trW.Q`, and `Retract`;
- `bridge/view`: the identification of those two object properties together with the biproduct
  presentation of a retract/direct summand. -/

-- Proof sketch: apply Lemma 13.5.9 to the localization functor `P.trW.Q`. An object is in the
-- kernel exactly when it becomes a direct summand of the cone term of a distinguished triangle
-- whose first morphism lies in `P.trW`; by `trW_iff_of_distinguished`, that cone term lies in
-- `P.isoClosure`, and the direct-summand clause is already expressed by the canonical retract
-- owner, so retract stability puts the object in `P.retractClosure`. The converse follows by
-- reversing this characterization and using that retracts become zero in the quotient.
/-- Lemma 13.6.9: the kernel of the quotient functor by a full triangulated subcategory `P` is
exactly the retract closure of `P`. Equivalently, this kernel is the smallest strictly full
saturated triangulated subcategory containing `P`. -/
theorem kernel_triangulatedLocalization_eq_retractClosure :
    Functor.kernel P.trW.Q = P.retractClosure := by
  let F : D ⥤ MorphismProperty.Localization P.trW := MorphismProperty.Q P.trW
  ext Z
  constructor
  · intro hZ
    have hzeroTfae :
        List.TFAE
          [ IsZero (F.obj Z)
          , ∃ Z' : D, P.trW (0 : Z ⟶ Z')
          , ∃ Z' : D, P.trW (0 : Z' ⟶ Z)
          , ∃ T : Triangle D,
              T ∈ distTriang D ∧ P.trW T.mor₁ ∧ Nonempty (Retract Z T.obj₃)
          ] := by
      simpa [F] using localization_object_isZero_tfae_of_compatibleWithTriangulation P.trW Z
    have hZ' : IsZero (F.obj Z) := by
      simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hZ
    obtain ⟨T, hT, hmor, ⟨r⟩⟩ :=
      (hzeroTfae.out 0 3).mp (by simpa using hZ')
    have hTobj : P.isoClosure T.obj₃ := by
      exact ((P.isoClosure).trW_iff_of_distinguished T hT).mp
        (by simpa [P.trW_isoClosure] using hmor)
    have hRetract : (P.isoClosure).retractClosure Z := by
      exact ((P.isoClosure).retractClosure).prop_of_retract r
        (P.isoClosure.le_retractClosure _ hTobj)
    simpa [P.retractClosure_isoClosure] using hRetract
  · rintro ⟨Y, hY, ⟨r⟩⟩
    have hZeroMor : ∃ Z' : D, P.trW (0 : Y ⟶ Z') := by
      exact ⟨0, trW.mk' P (contractible_distinguished Y) hY⟩
    have hzeroTfae :
        List.TFAE
          [ IsZero (F.obj Y)
          , ∃ Z' : D, P.trW (0 : Y ⟶ Z')
          , ∃ Z' : D, P.trW (0 : Z' ⟶ Y)
          , ∃ T : Triangle D,
              T ∈ distTriang D ∧ P.trW T.mor₁ ∧ Nonempty (Retract Y T.obj₃)
          ] := by
      simpa [F] using localization_object_isZero_tfae_of_compatibleWithTriangulation P.trW Y
    have hYzero : IsZero (F.obj Y) := (hzeroTfae.out 1 0).mp hZeroMor
    let hmap : Retract (F.obj Z) (F.obj Y) := Retract.map r F
    let e : F.obj Z ≅ F.obj Y :=
      { hom := hmap.i
        inv := hmap.r
        hom_inv_id := hmap.retract
        inv_hom_id := IsZero.eq_of_src hYzero _ _ }
    have hZzero : IsZero (F.obj Z) := hYzero.of_iso e
    simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hZzero

-- Proof sketch: rewrite the kernel using `kernel_triangulatedLocalization_eq_retractClosure` and
-- then unfold the owner `P.retractClosure`: membership means exactly being a retract of an object
-- of `P`, i.e. the intrinsic direct-summand condition.
/-- An object lies in the kernel of the quotient functor by `P` exactly when it becomes a direct
summand of some object of `P`, expressed canonically by a retract witness. -/
theorem mem_kernel_triangulatedLocalization_iff
    (Z : D) :
    Functor.kernel P.trW.Q Z ↔ ∃ Y : D, P Y ∧ Nonempty (Retract Z Y) := by
  rw [kernel_triangulatedLocalization_eq_retractClosure P]
  simpa [and_left_comm, and_assoc] using P.prop_retractClosure_iff Z

-- Proof sketch: this is the biproduct-model companion to
-- `mem_kernel_triangulatedLocalization_iff`; in a preadditive category, a retract is equivalently
-- a direct summand, encoded by the canonical split-triangle owner
-- `exists_iso_binaryBiproduct_of_distTriang`.
/-- Biproduct-model companion to `mem_kernel_triangulatedLocalization_iff`. -/
theorem mem_kernel_triangulatedLocalization_iff_biprod
    (Z : D) :
    Functor.kernel P.trW.Q Z ↔ ∃ (Z' Y : D), P Y ∧ Nonempty (Z ⊞ Z' ≅ Y) := by
  constructor
  · rintro hZ
    rcases (mem_kernel_triangulatedLocalization_iff P Z).mp hZ with ⟨Y, hY, ⟨r⟩⟩
    obtain ⟨Z', f, h, hT⟩ := distinguished_cocone_triangle₁ r.r
    let T : Triangle D := Triangle.mk f r.r h
    have hT' : T ∈ distTriang D := hT
    haveI : IsSplitEpi T.mor₂ := IsSplitEpi.mk' { section_ := r.i, id := r.retract }
    have hzero : T.mor₃ = 0 := Triangle.mor₃_eq_zero_of_epi₂ _ hT' (inferInstance : Epi T.mor₂)
    obtain ⟨e, _, _⟩ := exists_iso_binaryBiproduct_of_distTriang T hT' hzero
    exact ⟨Z', Y, hY, ⟨biprod.braiding Z Z' ≪≫ e.symm⟩⟩
  · rintro ⟨Z', Y, hY, ⟨e⟩⟩
    have hY' : P.retractClosure Y := P.le_retractClosure _ hY
    have hBiprod : P.retractClosure (Z ⊞ Z') := (P.retractClosure).prop_of_iso e.symm hY'
    have hZ' : P.retractClosure Z :=
      of_biprod_left P.retractClosure hBiprod
    rw [kernel_triangulatedLocalization_eq_retractClosure P]
    exact hZ'

-- Proof sketch: rewrite the kernel using `kernel_triangulatedLocalization_eq_retractClosure` and
-- apply the canonical owner theorem `ObjectProperty.retractClosure_le_iff`.
/-- The kernel of the quotient functor by `P` is initial among retract-stable object properties
containing `P`. -/
theorem kernel_triangulatedLocalization_le_iff
    (R : ObjectProperty D) [R.IsStableUnderRetracts] :
    Functor.kernel P.trW.Q ≤ R ↔ P ≤ R := by
  simpa [kernel_triangulatedLocalization_eq_retractClosure P] using P.retractClosure_le_iff R

end

end CategoryTheory

/-! ### Lemma_13_6_10 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.ObjectProperty
open CategoryTheory.MorphismProperty
open scoped CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]

/-
Domain-style sampling for Lemma `13.6.10`:
- primary domain: Verdier localization of a triangulated category and the correspondence between
  saturated triangulated subcategories and saturated multiplicative systems;
- sampled owner declarations:
  `kernel_triangulatedLocalization_eq_retractClosure`,
  `ObjectProperty.retractClosure_eq_self`,
  `kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor`,
  `MorphismProperty.saturatedClosure_le_iff`;
- best owner abstraction: on the morphism-property side, the canonical owner is
  `S.saturatedClosure`, so the kernel-induced class `(Functor.kernel S.Q).trW` should appear as a
  bridge to that owner rather than as a second parallel "smallest saturated system" API; on the
  object-property side, the canonical intrinsic owner is `P.retractClosure`, with the quotient
  kernel `Functor.kernel P.trW.Q` only the Verdier-localization view on that owner;
- primitive data: an object property `P` or a morphism property `S`;
- derived API: the fixed-point statements for retract-stable triangulated `P` and saturated
  compatible `S`;
- source/core/bridge triage:
  `source-facing`: `kernel_trW_eq_self` and `trW_functorKernel_eq_self`;
  `core/canonical`: `P.retractClosure`, `Functor.kernel`, `ObjectProperty.trW`, and
    `S.saturatedClosure`;
  `bridge/view`: `kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor S.Q` together with the
    owner definition of `S.saturatedClosure`.
-/

-- Proof sketch: apply `kernel_triangulatedLocalization_eq_retractClosure` from Lemma 13.6.9 and
-- then use the owner theorem `ObjectProperty.retractClosure_eq_self`.
section

variable (P : ObjectProperty D) [P.IsTriangulated] [P.IsStableUnderRetracts]

/-- Passing from a saturated triangulated subcategory `P` to its cone-defined multiplicative
system and then back to the kernel subcategory recovers `P`. -/
theorem kernel_trW_eq_self : kernel P.trW.Q = P := by
  rw [kernel_triangulatedLocalization_eq_retractClosure P]
  simpa using P.retractClosure_eq_self

end
end

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable (S : MorphismProperty D) [S.IsCompatibleWithTriangulation]

-- Proof sketch: rewrite `(Functor.kernel S.Q).trW` through the exact-functor bridge
-- `kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor S.Q`, identify the resulting
-- inverse-image class with the owner `S.saturatedClosure`, and then apply the canonical
-- fixed-point inequalities for saturated closure.
/-- Lemma 13.6.10: if `S` is a saturated multiplicative system compatible with the triangulated
structure on `D`, then passing to the kernel of the localization functor `S.Q` and then taking
the associated cone-defined morphism property recovers `S`. Together with `kernel_trW_eq_self`,
this is the mutually inverse correspondence between saturated compatible multiplicative systems
and strictly full saturated triangulated subcategories. -/
theorem trW_functorKernel_eq_self
    [IsSaturatedMultiplicativeSystem S] :
    (kernel S.Q).trW = S := by
  rw [kernel_trW_eq_inverseImage_isomorphisms_of_exactFunctor S.Q]
  exact le_antisymm
    (saturatedClosure_le S le_rfl)
    ((IsInvertedBy.iff_le_inverseImage_isomorphisms S S.Q).1 S.Q_inverts)

end

end CategoryTheory

/-! ### Lemma_13_6_11 (from Chap13) -/
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
