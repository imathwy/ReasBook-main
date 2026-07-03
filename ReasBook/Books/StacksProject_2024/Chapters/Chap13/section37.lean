import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_37_1 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite
open scoped ZeroObject

universe w v u

namespace CategoryTheory

section

/- Domain-style sampling for Definition 13.37.1:
- primary domain: object predicates in preadditive categories defined through the represented
  functor `Hom(K,-)`, together with the full subcategories cut out by such predicates;
- sampled owner declarations:
  `HasCoproducts`,
  `preadditiveCoyoneda.obj`,
  `preservesColimitsOfShape_of_equiv`,
  `preservesColimitsOfShape_of_isZero`,
  `ObjectProperty.FullSubcategory`;
- best owner abstraction: the source-facing owner is the reusable object predicate
  `IsCompactObject`, while the compact subcategory `D_c` should be only the direct full
  subcategory attached to that predicate, matching the existing project pattern where source
  predicates own the mathematics and full subcategories are derived views;
  `preadditiveCoyoneda.obj (op K)` together with preservation of ambient
  `Type (max u v)`-indexed discrete coproduct shapes in a category with arbitrary coproducts;
  preservation for smaller discrete shapes via `Shrink`/equivalence, and the source-facing
  full-subcategory notation `D_c(D)`;
- source/core/bridge triage:
  `source-facing`: `IsCompactObject K`;
  `core/canonical`: `PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op K))`;
  `bridge/view`: the direct full subcategory `(IsCompactObject : ObjectProperty D).FullSubcategory`,
    used with the source notation `D_c(D)`.

There is no need for a second public owner-level wrapper `compactObjectProperty`, `compactObjects`,
or any other owner parallel to `IsCompactObject`: the predicate `IsCompactObject` is the owner,
and the compact subcategory is only its direct object-property full subcategory bridge/view. -/

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{max u v} D]

/-- Definition 13.37.1: in the source setting of an additive category with arbitrary direct sums,
an object `K` is compact when the preadditive Hom functor `Hom(K, -)` preserves arbitrary
coproducts. In Lean, the owner is phrased through preservation of `Type (max u v)`-indexed
discrete colimits by `preadditiveCoyoneda.obj (op K)`, with smaller shapes recovered by shrink. -/
@[mk_iff isCompactObject_iff]
class IsCompactObject (K : D) : Prop where
  preservesCoproducts (I : Type (max u v)) :
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op K))

/-- A compact object represents a functor preserving coproducts of any fixed small shape. -/
instance (K : D) [hK : IsCompactObject K] (I : Type w) [UnivLE.{w, max u v}] :
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op K)) :=
  by
    let h :
        PreservesColimitsOfShape (Discrete (Shrink.{max u v} I))
          (preadditiveCoyoneda.obj (op K)) :=
      hK.preservesCoproducts (Shrink.{max u v} I)
    exact
      preservesColimitsOfShape_of_equiv
        (Discrete.equivalence (equivShrink.{max u v} I)).symm
        (preadditiveCoyoneda.obj (op K))

/-- The source notation `D_c(D)` for the full subcategory of compact objects. -/
scoped notation "D_c(" D:arg ")" =>
  ObjectProperty.FullSubcategory (IsCompactObject : ObjectProperty D)

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasCoproducts.{max u v} D]

/-- The zero object is a compact object. -/
instance isCompactObject_zero : IsCompactObject (0 : D) where
  preservesCoproducts I := by
    let F := preadditiveCoyoneda.obj (op (0 : D))
    have hzero : IsZero F := by
      dsimp [F]
      exact Functor.map_isZero preadditiveCoyoneda (IsZero.op (isZero_zero D))
    simpa using
      F.preservesColimitsOfShape_of_isZero hzero (Discrete I)

end

end CategoryTheory

/-! ### Lemma_13_37_2 (from Chap13) -/
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

section

/-
Domain-style sampling for Lemma 13.37.2:
- primary domain: compact objects in triangulated categories, expressed as an object property and
  its induced full subcategory;
- sampled owner declarations:
  `IsCompactObject`,
  `ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsTriangulated`,
  `IsTriangulated P.FullSubcategory`;
- best owner abstraction: the source-facing owner remains `IsCompactObject`, while saturation and
  triangulatedity are expressed through the canonical object-property owners
  `ObjectProperty.IsStableUnderRetracts` and `ObjectProperty.IsTriangulated`; the compact
  subcategory is the direct bridge/view `D_c(D)`;
- primitive data: the compactness predicate `IsCompactObject`;
- derived API: closure under isomorphisms from retract stability and triangulatedity of `D_c(D)`
  from the generic full-subcategory instance;
- source/core/bridge triage:
  `source-facing`: the compact-object predicate `IsCompactObject`;
  `core/canonical`: the owner predicates `ObjectProperty.IsStableUnderRetracts` and
    `ObjectProperty.IsTriangulated`;
  `bridge/view`: the full subcategory `D_c(D)`.

This file is therefore the owner only of the two missing compact-object instances; strict-fullness
and the triangulated structure on `D_c(D)` remain derived recall/view API from the generic
object-property machinery. -/

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{max u v} D]

/-- The compact-object property is saturated, i.e. stable under retracts/direct summands. -/
-- Proof sketch: if `K` is a retract of `L`, then `Hom_D(K,-)` is a retract of `Hom_D(L,-)` in the
-- functor category; a retract of a coproduct-preserving additive functor again preserves the same
-- coproducts.
instance isCompactObject_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts (IsCompactObject : ObjectProperty D) := sorry

/- Companion recall: retract-stable object properties are automatically strictly full, so the
compact-object property is canonically closed under isomorphisms. -/
#check (inferInstance :
  ObjectProperty.IsClosedUnderIsomorphisms (IsCompactObject : ObjectProperty D))

variable [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-- The compact-object property is triangulated in the object-property sense. -/
-- Proof sketch: represented functors are homological in a pretriangulated category. For a
-- distinguished triangle, if two terms are compact then applying `Hom_D(-,-)` to any coproduct
-- yields a morphism of long exact sequences; Lemma `12.5.20` gives the third compactness
-- condition, while zero objects and shifts are formal.
instance isCompactObject_isTriangulated :
    ObjectProperty.IsTriangulated (IsCompactObject : ObjectProperty D) := sorry

variable [IsTriangulated D]

/- Lemma 13.37.2: in a triangulated category `D` with direct sums, the compact objects form a
strictly full saturated triangulated subcategory `D_c ⊆ D`. Once
`ObjectProperty.IsTriangulated (IsCompactObject : ObjectProperty D)` is available, the
triangulated structure on `D_c(D)` is the canonical full-subcategory instance. -/
#check (inferInstance : IsTriangulated (D_c(D)))

end

end CategoryTheory

/-! ### Lemma_13_37_3 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe w v u

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{max u v w} D]
variable {I : Type w} (E : I → D)

/-- The object property of objects that are isomorphic to a coproduct of shifts of the family
`E : I → D`. -/
def IsDirectSumOfShifts : ObjectProperty D := fun A ↦
  ∃ (J : Type (max u v w)) (ι : J → I) (shift : J → ℤ),
    Nonempty ((∐ fun j : J ↦ E (ι j)⟦shift j⟧) ≅ A)

instance isDirectSumOfShifts_isClosedUnderIsomorphisms :
    (IsDirectSumOfShifts E).IsClosedUnderIsomorphisms where
  of_iso e hA := by
    rcases hA with ⟨J, ι, shift, ⟨h⟩⟩
    exact ⟨J, ι, shift, ⟨h.trans e⟩⟩

/-- A recursive generating-family approximation tower by direct sums of shifts of the family `E`.
The natural-number index `0` corresponds to the textbook term `X₁`. -/
def IsGeneratingFamilyApproximation
    (X : ℕ → D) (map : ∀ n : ℕ, X n ⟶ X (n + 1))
    (Y : ℕ → D) (triangleHom : ∀ n : ℕ, Y n ⟶ X n)
    (triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧) : Prop :=
  IsDirectSumOfShifts E (X 0) ∧
    (∀ n : ℕ, IsDirectSumOfShifts E (Y n)) ∧
    (∀ n : ℕ, Triangle.mk (triangleHom n) (map n) (triangleConnecting n) ∈ distTriang D)

namespace IsGeneratingFamilyApproximation

omit [IsTriangulated D] in
theorem initial {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (h :
      IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) :
    IsDirectSumOfShifts E (X 0) :=
  h.1

omit [IsTriangulated D] in
theorem pieces {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (h :
      IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) (n : ℕ) :
    IsDirectSumOfShifts E (Y n) :=
  h.2.1 n

omit [IsTriangulated D] in
theorem triangleDistinguished {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (h :
      IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) (n : ℕ) :
    Triangle.mk (triangleHom n) (map n) (triangleConnecting n) ∈ distTriang D :=
  h.2.2 n

end IsGeneratingFamilyApproximation

-- Proof sketch: choose the canonical approximation tower built from all maps from shifts of the
-- compact generators into `X` and into the successive kernels of the maps to `X`. Lemma 13.33.9
-- identifies maps from each compact generator into the homotopy colimit with the colimit of maps
-- into the stages, so the cone of the comparison map to `X` is right-orthogonal to all shifts of
-- the family. The generating hypothesis then forces that cone to be zero.
/-- Lemma 13.37.3: if each `E i` is compact and the shifts of the family `E` generate `D`, then
every object `X` admits a sequential resolution whose initial term and successive cones are direct
sums of shifts of the `E i`, and whose chosen homotopy colimit is equipped with an isomorphism to
`X`. The index `0` of the resolution corresponds to the textbook term `X₁`. -/
theorem exists_generating_family_resolution
    (hcompact : ∀ i : I, IsCompactObject (E i)) (hgenerate : IsGeneratingFamily E) (A : D) :
    ∃ (X : ℕ → D) (map : ∀ n : ℕ, X n ⟶ X (n + 1))
      (Y : ℕ → D) (triangleHom : ∀ n : ℕ, Y n ⟶ X n)
      (triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧) (Khocolim : D)
      (e : Khocolim ≅ A),
        IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting ∧
          IsHomotopyColimitOf (Functor.ofSequence map) Khocolim := sorry

end

/-! ### Lemma_13_37_4 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Opposite
open scoped CategoryTheory.ObjectProperty.GeneratedNotation

noncomputable section

universe w v u

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{max u v w} D]
variable {I : Type w} (E : I → D)

/- Domain-style sampling for Lemma 13.37.4:
- primary domain: compact objects and finitely generated extension stages in a triangulated
  category, expressed through `ObjectProperty`;
- sampled owner declarations:
  `ObjectProperty.objectGeneratedProperty`,
  `ObjectProperty.objectGeneratedProperty_le_iff`,
  `ObjectProperty.objectGeneratedStage`,
  `ObjectProperty.additiveExtensionStage`,
  `CategoryTheory.ObjectProperty.GeneratedNotation`;
- best owner abstraction: the source-facing statement should express the factor object as lying in
  the generated triangulated subcategory `⟨∐ fun j ↦ E (ι j)⟩` attached to a finite coproduct of
  generators, and the stronger stage-level statement should use the canonical coproduct stage
  `⟨∐ fun j ↦ E (ι j)⟩_m`; any finite-family additive-extension presentation is a derived bridge,
  not the public owner;
- primitive-vs-derived split:
  primitive data are the finite index type `J`, the chosen subfamily `ι : J → I`, and the finite
  coproduct `∐ fun j ↦ E (ι j)`;
  derived API is the stage-level witness `⟨∐ fun j ↦ E (ι j)⟩_m A`, whose internal description is
  `additiveExtensionStage ((singleton (∐ fun j ↦ E (ι j))).shiftClosure ℤ) m A`.

Source/core/bridge triage:
- `source-facing`: the compact-factorization theorem for a finite subfamily of generators;
- `core/canonical`: `objectGeneratedProperty` with the textbook notation `⟨-⟩`;
- `bridge/view`: the companion theorem below retains the stronger finite-coproduct stage witness
  `⟨∐ fun j ↦ E (ι j)⟩_m`. -/

-- Proof sketch: first prove the stronger stage-level statement below, producing a factor object in
-- a canonical generated stage `⟨∐ fun j ↦ E (ι j)⟩_m` attached to finitely many chosen generators.
-- Then pass from that stage witness to membership in the generated triangulated subcategory of the
-- same finite coproduct, since `⟨∐ fun j ↦ E (ι j)⟩` is the supremum of its positive stages.
/-- A stage-level strengthening of Lemma 13.37.4: the factor object can be placed in an explicit
generated stage attached to a finite coproduct of chosen generators. -/
theorem compact_factors_through_finite_generator_coproduct_stage
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) {C : D}
    (hC : IsCompactObject C) (n : ℕ) (f : C ⟶ X n) :
    ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I) (m : ℕ+),
        (⟨∐ fun j : J ↦ E (ι j)⟩_m) A ∧
        ∃ (g : C ⟶ A) (h : A ⟶ X n), g ≫ h = f := sorry

/-- Lemma 13.37.4: let
`X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯`
be a generating-family approximation as in Lemma `13.37.3`, and let `C` be a compact object.
Then any morphism from `C` to the stage `X n` factors through an object of the generated
triangulated subcategory `⟨E_{i₁} ⊕ ⋯ ⊕ E_{i_t}⟩` for some finite subfamily of the generators.
Here `X 0` corresponds to the textbook object `X₁`. -/
theorem compact_factors_through_finite_generator_stage
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) {C : D}
    (hC : IsCompactObject C) (n : ℕ) (f : C ⟶ X n) :
    ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I),
        ⟨∐ fun j : J ↦ E (ι j)⟩ A ∧
        ∃ (g : C ⟶ A) (h : A ⟶ X n), g ≫ h = f := by
  rcases compact_factors_through_finite_generator_coproduct_stage E hR hC n f with
    ⟨A, J, hJ, ι, m, hA, g, h, hgf⟩
  refine ⟨A, J, hJ, ι, ?_, g, h, hgf⟩
  rw [objectGeneratedProperty, prop_iSup_iff]
  exact ⟨m, hA⟩

end

/-! ### Definition_13_37_5 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe w v u

namespace CategoryTheory

/-
Domain-style sampling for Definition 13.37.5:
- primary domain: compact generation of triangulated categories via compact objects and generating
  families;
- sampled owner declarations:
  `IsCompactObject`,
  `D_c(D)`,
  `IsWeakGenerator`,
  `IsGeneratingFamily`,
  `ObjectProperty.ofObj`,
  `ObjectProperty.shiftClosure`,
  `isWeakGenerator_iff_rightOrthogonal_shifts_eq_isZero`;
- best upstream owner abstractions:
  `IsCompactObject` for the compactness predicate on each generator and
  `IsGeneratingFamily E` for the family-level generation statement;
- source-facing reformulation for this item: the coproduct weak-generator statement
  `IsWeakGenerator (∐ E)`;
- primitive data: a family `E : I → D` together with the compactness owner
  `∀ i, IsCompactObject (E i)` and the source coproduct-generation condition
  `IsWeakGenerator (∐ E)`;
- derived API: the canonical generation-family bridge
  `isCompactlyGenerated_iff_exists_compact_generatingFamily`, obtained from
  `isWeakGenerator_coproduct_iff_isGeneratingFamily`, and the bundled compact-subcategory bridge
  `isCompactlyGenerated_iff_exists_compactSubcategory_generatingFamily`;
- source/core/bridge triage:
  `source-facing`: `IsCompactlyGenerated D`;
  `core/canonical`: `IsCompactObject` and `IsGeneratingFamily E`;
  `bridge/view`: the equivalences
  `IsWeakGenerator (∐ E) ↔ IsGeneratingFamily E` via the singleton shift-closure owner for
  `∐ E`, the family shift-closure owner for `E`, and the coproduct/shift comparison
  `Limits.PreservesCoproduct.iso (shiftFunctor D n) E`, together with the equivalent
  `D_c(D)`-family packaging of the compactness data.

The source notion is not a new owner parallel to `IsCompactObject` or `IsGeneratingFamily`; it is
the existential compact-generation wrapper built directly from those owners, with the
canonical generation-family reformulation and compact-subcategory packaging retained as bridge
views. -/

section

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasShift D ℤ]

omit [HasZeroMorphisms D] in
private theorem hasCoproduct_shift {I : Type w} (E : I → D) [HasCoproduct E] (n : ℤ) :
    HasCoproduct (fun i ↦ (shiftFunctor D n).obj (E i)) := by
  change HasColimit (Discrete.functor fun i ↦ (shiftFunctor D n).obj (E i))
  letI : HasColimit (Discrete.functor E ⋙ shiftFunctor D n) := inferInstance
  let e :
      Discrete.functor (fun i ↦ (shiftFunctor D n).obj (E i)) ≅
        Discrete.functor E ⋙ shiftFunctor D n :=
    Discrete.natIso fun i ↦ Iso.refl _
  exact hasColimit_of_iso e

omit [HasZeroMorphisms D] in
private def coproductShiftIso {I : Type w} (E : I → D) [HasCoproduct E] (n : ℤ)
    [HasCoproduct (fun i ↦ (shiftFunctor D n).obj (E i))] :
    (∐ fun i ↦ E i⟦n⟧) ≅ (∐ E)⟦n⟧ :=
  (PreservesCoproduct.iso (shiftFunctor D n) E).symm

/-- A family generates exactly when its coproduct is a weak generator. -/
theorem isWeakGenerator_coproduct_iff_isGeneratingFamily {I : Type w} (E : I → D)
    [HasCoproduct E] :
    IsWeakGenerator (∐ E) ↔ IsGeneratingFamily E := by
  rw [isWeakGenerator_iff_rightOrthogonal_shifts_eq_isZero, IsGeneratingFamily]
  suffices
      ((singleton (∐ E)).shiftClosure ℤ).rightOrthogonal =
        ((ofObj E).shiftClosure ℤ).rightOrthogonal by
    rw [this]
  ext K
  constructor
  · intro hK X f hX
    rcases hX with ⟨Y, n, eX, hY⟩
    rcases hY with ⟨i⟩
    letI : HasCoproduct (fun j ↦ (shiftFunctor D n).obj (E j)) := hasCoproduct_shift E n
    let e := coproductShiftIso E n
    classical
    let g : (j : I) → E j⟦n⟧ ⟶ K := fun j ↦ by
      by_cases h : j = i
      · subst h
        exact eX.inv ≫ f
      · exact 0
    let φ : (∐ fun j ↦ E j⟦n⟧) ⟶ K := Limits.Sigma.desc g
    have hφ : e.inv ≫ φ = 0 := hK (e.inv ≫ φ) ⟨∐ E, n, Iso.refl _, by simp⟩
    have hφ' : φ = 0 := by
      simpa [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k) hφ
    have hι : Limits.Sigma.ι (fun j ↦ E j⟦n⟧) i ≫ φ = eX.inv ≫ f := by
      rw [show φ = Limits.Sigma.desc g by rfl, Limits.Sigma.ι_desc]
      simp [g]
    calc
      f = eX.hom ≫ (eX.inv ≫ f) := by simp
      _ = eX.hom ≫ (Limits.Sigma.ι (fun j ↦ E j⟦n⟧) i ≫ φ) := by
            simpa using congrArg (eX.hom ≫ ·) hι.symm
      _ = 0 := by simp [hφ']
  · intro hK X f hX
    rcases hX with ⟨Y, n, eX, hY⟩
    rw [singleton_iff] at hY
    subst Y
    letI : HasCoproduct (fun j ↦ (shiftFunctor D n).obj (E j)) := hasCoproduct_shift E n
    let e := coproductShiftIso E n
    have hg : e.hom ≫ eX.inv ≫ f = 0 := by
      apply Limits.Sigma.hom_ext
      intro j
      simpa using hK (Limits.Sigma.ι (fun j ↦ E j⟦n⟧) j ≫ e.hom ≫ eX.inv ≫ f)
        ⟨E j, n, Iso.refl _, ofObj_apply E j⟩
    calc
      f = eX.hom ≫ (e.inv ≫ (e.hom ≫ eX.inv ≫ f)) := by simp
      _ = 0 := by simp [hg]

end

section

variable (D : Type u) [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [HasCoproducts.{max u v} D]

/-- Definition 13.37.5: in the source triangulated setting, compact generation is the existence of
a family of compact objects whose coproduct is a weak generator. The canonical family-level
reformulation is `isCompactlyGenerated_iff_exists_compact_generatingFamily`, and the compact
subcategory packaging is
`isCompactlyGenerated_iff_exists_compactSubcategory_generatingFamily`. -/
def IsCompactlyGenerated : Prop :=
  ∃ (I : Type (max u v)) (E : I → D), (∀ i, IsCompactObject (E i)) ∧ IsWeakGenerator (∐ E)

/-- Canonical bridge: compact generation is equivalently the existence of a compact generating
family. -/
theorem isCompactlyGenerated_iff_exists_compact_generatingFamily :
    IsCompactlyGenerated D ↔
      ∃ (I : Type (max u v)) (E : I → D), (∀ i, IsCompactObject (E i)) ∧ IsGeneratingFamily E := by
  constructor
  · rintro ⟨I, E, hcompact, hweak⟩
    exact ⟨I, E, hcompact, (isWeakGenerator_coproduct_iff_isGeneratingFamily E).1 hweak⟩
  · rintro ⟨I, E, hcompact, hgenerate⟩
    exact ⟨I, E, hcompact, (isWeakGenerator_coproduct_iff_isGeneratingFamily E).2 hgenerate⟩

/-- Compact generation is equivalently the existence of a generating family valued in the compact
subcategory `D_c(D)`. This is the thin bridge from the canonical generation-family reformulation
to the full-subcategory view. -/
theorem isCompactlyGenerated_iff_exists_compactSubcategory_generatingFamily :
    IsCompactlyGenerated D ↔
      ∃ (I : Type (max u v)) (E : I → D_c(D)), IsGeneratingFamily (fun i ↦ (E i).obj) := by
  rw [isCompactlyGenerated_iff_exists_compact_generatingFamily]
  constructor
  · rintro ⟨I, E, hcompact, hE⟩
    exact ⟨I, fun i ↦ ⟨E i, hcompact i⟩, hE⟩
  · rintro ⟨I, E, hE⟩
    exact ⟨I, fun i ↦ (E i).obj, fun i ↦ (E i).property, hE⟩

end

end CategoryTheory

/-! ### Proposition_13_37_6 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe v u

namespace CategoryTheory

/-
Domain-style sampling for Proposition 13.37.6:
- primary domain: compact objects and generation in triangulated categories with coproducts;
- sampled owner declarations:
  `IsWeakGenerator`,
  `IsClassicalGenerator`,
  `IsCompactObject`,
  `IsCompactlyGenerated`,
  `D_c(D)`,
  `isCompactlyGenerated_iff_exists_compactSubcategory_generatingFamily`;
- best owner abstraction:
  the proposition is a `bridge/view` statement relating the ambient weak-generator owner
  `IsWeakGenerator E` to the compact-subcategory owner
  `IsClassicalGenerator (⟨E, hE⟩ : D_c(D))` together with the ambient compact-generation owner
  `IsCompactlyGenerated D`;
- primitive data:
  the compact object `E` together with its compactness witness `hE : IsCompactObject E`;
- derived API:
  the two directional bridge theorems below, one extracting compact generation from a compact weak
  generator and the other upgrading compact-subcategory classical generation back to weak
  generation in `D`.

There is no new owner to define here: the file should reuse the Chapter 13 owners directly and
keep this proposition as a thin bridge theorem between them. -/

section

variable {D : Type u} [Category.{v} D] [HasShift D ℤ] [Preadditive D]
  [HasCoproducts.{max u v} D]

-- Proof sketch: a compact weak generator already gives the compact-generation witness with the
-- singleton family `fun _ : Unit ↦ E`.
/-- A compact weak generator compactly generates the ambient triangulated category. -/
theorem isCompactlyGenerated_of_isWeakGenerator
    (E : D) (hE : IsCompactObject E) (hweak : IsWeakGenerator E) :
    IsCompactlyGenerated D := by
  rw [isCompactlyGenerated_iff_exists_compact_generatingFamily]
  refine ⟨ULift.{max u v, 0} PUnit, fun _ ↦ E, ?_, ?_⟩
  · intro _
    simpa using hE
  · rw [IsGeneratingFamily]
    have hweak' : ((singleton E).shiftClosure ℤ).rightOrthogonal = IsZero :=
      (isWeakGenerator_iff_rightOrthogonal_shifts_eq_isZero E).1 hweak
    have hofObj :
        ofObj (fun _ : ULift.{max u v, 0} PUnit ↦ E) = singleton E := by
      ext X
      rw [ofObj_iff, singleton_iff]
      constructor
      · rintro ⟨i, hi⟩
        simpa using hi
      · intro hX
        exact ⟨⟨PUnit.unit⟩, hX⟩
    simpa [hofObj] using hweak'

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [HasCoproducts.{max u v} D]
  [IsTriangulated D]

-- Proof sketch: for the forward implication, combine compact generation with the passage from
-- classical generation on `D_c` to weak generation in `D`. For the reverse implication, resolve a
-- compact object `X` by the singleton family `{E}`; compactness of `X` forces the comparison map
-- to factor through a finite stage, and that stage lies in the thick subcategory generated by
-- `E`, so `E` classically generates `D_c`.
/-- If a compact object is a weak generator of `D`, then it classically generates the compact
subcategory `D_c(D)`. -/
theorem isClassicalGenerator_on_compactObjects_of_isWeakGenerator
    (E : D) (hE : IsCompactObject E) (hweak : IsWeakGenerator E) :
    IsClassicalGenerator (⟨E, hE⟩ : D_c(D)) := sorry

/-- If a compact object classically generates the compact subcategory and the ambient category is
compactly generated, then it is a weak generator of the ambient category. -/
theorem isWeakGenerator_of_isClassicalGenerator_on_compactObjects_and_isCompactlyGenerated
    (E : D) (hE : IsCompactObject E)
    (hclass : IsClassicalGenerator (⟨E, hE⟩ : D_c(D))) (hD : IsCompactlyGenerated D) :
    IsWeakGenerator E := sorry

/-- Proposition 13.37.6: for a compact object `E` of a triangulated category with direct sums,
`E` is a weak generator of `D` if and only if `E`, viewed as an object of the compact subcategory
`D_c`, is a classical generator of `D_c` and `D` is compactly generated. -/
theorem weak_generator_iff_classical_generator_on_compactObjects_and_compactly_generated
    (E : D) (hE : IsCompactObject E) :
    IsWeakGenerator E ↔
      (IsClassicalGenerator (⟨E, hE⟩ : D_c(D)) ∧ IsCompactlyGenerated D) := by
  constructor
  · intro hweak
    exact
      ⟨isClassicalGenerator_on_compactObjects_of_isWeakGenerator E hE hweak,
        isCompactlyGenerated_of_isWeakGenerator E hE hweak⟩
  · rintro ⟨hclass, hD⟩
    exact
      isWeakGenerator_of_isClassicalGenerator_on_compactObjects_and_isCompactlyGenerated
        E hE hclass hD

end

end CategoryTheory
