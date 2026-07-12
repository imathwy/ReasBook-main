import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 12.19.1:
- primary domain: filtered objects in a category, expressed through decreasing filtrations by
  subobjects;
- sampled core/canonical declarations in this domain:
  `OrderHom`,
  `Subobject.Factors`,
  `Subobject.factorThru`,
  `Subobject.«exists»`,
  `GradedObject`,
  `cokernel`;
- best owner abstraction: `DecreasingFiltration A := ℤᵒᵈ →o Subobject A`, with `FilteredObject C`
  bundling an ambient object together with that owner filtration;
- primitive data: an object `A : C` and the monotone map `ℤᵒᵈ →o Subobject A`;
- derived API: stage inclusions, graded pieces, associated graded objects, induced and quotient
  filtrations, and the category of filtration-preserving morphisms;
- source/core/bridge triage:
  `source-facing`: filtered objects and filtration-preserving maps;
  `core/canonical`: the `OrderHom` owner into `Subobject`;
  `bridge/view`: pullback-induced filtrations, pullback reformulations of stagewise preservation,
  image/quotient filtrations, and associated graded objects.

The source mathematics really does add content beyond the bare owner `OrderHom`, so the main
public entry remains the source-facing structure `FilteredObject`; the order-hom owner is the
canonical core from which the rest of the API is derived. -/

/-- A decreasing filtration on an object is a `ℤ`-indexed antitone family of subobjects,
recorded canonically as a bundled monotone map `ℤᵒᵈ →o Subobject A`. -/
abbrev DecreasingFiltration (A : C) := ℤᵒᵈ →o Subobject A

namespace DecreasingFiltration

variable {A : C}

/-- The `n`-th stage of the filtration. -/
noncomputable abbrev obj (F : DecreasingFiltration A) (n : ℤ) : Subobject A := F n

/-- The stages form a decreasing chain. -/
theorem antitone_obj (F : DecreasingFiltration A) : Antitone F.obj := by
  intro i j hij
  exact F.monotone hij

/-- Consecutive stages of a decreasing filtration satisfy `F^{p + 1} ≤ F^p`. -/
theorem succ_le (F : DecreasingFiltration A) (p : ℤ) : F.obj (p + 1) ≤ F.obj p :=
  F.antitone_obj (by omega)

/-- The canonical inclusion `F^{p + 1} A ⟶ F^p A` attached to a decreasing filtration. -/
noncomputable abbrev stageInclusion (F : DecreasingFiltration A) (p : ℤ) :
    (F.obj (p + 1) : C) ⟶ (F.obj p : C) :=
  Subobject.ofLE (F.obj (p + 1)) (F.obj p) (F.succ_le p)

/-- A decreasing filtration is exhaustive if the whole object is the smallest subobject containing
every stage. -/
def IsExhaustive {A : C} (F : DecreasingFiltration A) : Prop :=
  ∀ Y : Subobject A, (∀ i : ℤ, F i ≤ Y) → ⊤ ≤ Y

end DecreasingFiltration

section ZeroObject

variable [HasZeroObject C]

namespace DecreasingFiltration

/-- A decreasing filtration is finite if some stage is the whole object and some stage is zero. -/
def IsFinite {A : C} (F : DecreasingFiltration A) : Prop :=
  ∃ n m : ℤ, F n = ⊤ ∧ F m = ⊥

/-- A decreasing filtration is separated if the zero subobject is the largest subobject contained
in every stage. -/
def IsSeparated {A : C} (F : DecreasingFiltration A) : Prop :=
  ∀ Y : Subobject A, (∀ i : ℤ, Y ≤ F i) → Y ≤ ⊥

end DecreasingFiltration

end ZeroObject

/-- The source-facing owner object for Chap12 Definition 12 19 1 is an object equipped with a
decreasing `ℤ`-indexed filtration by subobjects. Later abelian-category constructions specialize
this owner to the textbook setting. -/
@[stacks 0121]
structure FilteredObject (C : Type u) [Category.{v} C] where
  /-- The underlying object. -/
  obj : C
  /-- The decreasing filtration on the underlying object. -/
  filtration : DecreasingFiltration obj

/- The Stacks Project writes the category of filtered objects in `C` as `Fil(C)`. This is
notation for the source-facing owner type `FilteredObject C`. -/
scoped notation "Fil(" C ")" => FilteredObject C

namespace FilteredObject

variable (A : Fil(C))

/-- The underlying object of the `p`-th filtration stage. -/
noncomputable abbrev stage (p : ℤ) : C :=
  A.filtration.obj p

/-- Textbook notation for the underlying object of the filtration stage `F^p A`. -/
notation:max "F^{" p "} " A:max => FilteredObject.stage A p

/-- Consecutive filtration stages satisfy `F^{p + 1} A ≤ F^p A`. -/
theorem succ_le (p : ℤ) : A.filtration.obj (p + 1) ≤ A.filtration.obj p :=
  DecreasingFiltration.succ_le A.filtration p

end FilteredObject

section FilteredObjectZeroObject

variable [HasZeroObject C]

namespace FilteredObject

/-- A filtered object has a finite filtration if some stage is the whole object and some stage is
zero. -/
def IsFinite (A : Fil(C)) : Prop :=
  DecreasingFiltration.IsFinite A.filtration

end FilteredObject

end FilteredObjectZeroObject

section Cokernels

variable [HasZeroMorphisms C] [HasCokernels C]

namespace DecreasingFiltration

variable {A : C}

/-- The `p`-th graded piece `gr^p(A) = F^p A / F^{p + 1} A` of a decreasing filtration. -/
noncomputable abbrev gradedPiece (F : DecreasingFiltration A) (p : ℤ) : C :=
  cokernel (F.stageInclusion p)

end DecreasingFiltration

end Cokernels

section CompleteLattice

variable [LocallySmall C] [WellPowered C] [HasWidePullbacks C] [HasImages C] [HasCoproducts C]
  [InitialMonoClass C]

namespace DecreasingFiltration

variable {A : C}

/-- A decreasing filtration is exhaustive exactly when the union of its stages is the whole
ambient object. -/
theorem isExhaustive_iff_iSup_eq_top (F : DecreasingFiltration A) :
    IsExhaustive F ↔ (⨆ p : ℤ, F p) = ⊤ := by
  constructor
  · intro h
    have h' : ∀ Y : Subobject A, (∀ i : ℤ, F i ≤ Y) → ⊤ ≤ Y := by
      simpa [IsExhaustive] using h
    apply le_antisymm
    · exact le_top
    · exact h' _ (fun p ↦ le_iSup (fun q : ℤ ↦ F q) p)
  · intro h
    refine (show IsExhaustive F from ?_)
    simpa [IsExhaustive] using
      (fun Y hY ↦ by
        simpa [h] using (iSup_le hY : (⨆ p : ℤ, F p) ≤ Y))

end DecreasingFiltration

end CompleteLattice

section CompleteLatticeZeroObject

variable [HasZeroObject C] [LocallySmall C] [WellPowered C] [HasWidePullbacks C] [HasImages C]
  [HasCoproducts C] [InitialMonoClass C]

namespace DecreasingFiltration

variable {A : C}

/-- A decreasing filtration is separated exactly when the intersection of its stages is the zero
subobject. -/
theorem isSeparated_iff_iInf_eq_bot (F : DecreasingFiltration A) :
    IsSeparated F ↔ (⨅ p : ℤ, F p) = ⊥ := by
  constructor
  · intro h
    have h' : ∀ Y : Subobject A, (∀ i : ℤ, Y ≤ F i) → Y ≤ ⊥ := by
      simpa [IsSeparated] using h
    apply le_antisymm
    · exact h' _ (fun p ↦ iInf_le (fun q : ℤ ↦ F q) p)
    · exact bot_le
  · intro h
    refine (show IsSeparated F from ?_)
    simpa [IsSeparated] using
      (fun Y hY ↦ by
        simpa [h] using (le_iInf hY : Y ≤ ⨅ p : ℤ, F p))

end DecreasingFiltration

end CompleteLatticeZeroObject

section Cokernels

variable [HasZeroMorphisms C] [HasCokernels C]

namespace FilteredObject

variable (A : FilteredObject C)

/-- The `p`-th graded piece `gr^p(A) = F^p A / F^{p + 1} A`. -/
noncomputable abbrev gradedPiece (p : ℤ) : C :=
  A.filtration.gradedPiece p

/-- Textbook notation for the graded piece `gr^p(A)`. -/
notation:max "gr^{" p "} " A:max => FilteredObject.gradedPiece A p

/-- The associated graded object of a filtered object. -/
noncomputable def associatedGraded : GradedObject ℤ C :=
  fun p ↦ gr^{p} A

end FilteredObject

end Cokernels

section Pullbacks

variable [HasPullbacks C]

namespace DecreasingFiltration

/-- The filtration induced on a subobject by intersecting with each ambient filtration stage. -/
noncomputable def induced {A : C} (F : DecreasingFiltration A) (X : Subobject A) :
    DecreasingFiltration (X : C) :=
  (Subobject.pullback X.arrow).toOrderHom.comp F

end DecreasingFiltration

end Pullbacks

namespace FilteredObject

/-- A morphism of filtered objects preserves each filtration stage. -/
@[ext] structure Hom (X Y : Fil(C)) where
  /-- The underlying morphism in the ambient category. -/
  hom : X.obj ⟶ Y.obj
  /-- Each stage of the source filtration is mapped into the corresponding stage of the target
  filtration. -/
  preserves (i : ℤ) : (Y.filtration i).Factors ((X.filtration i).arrow ≫ hom)

namespace Hom

/-- The identity morphism of a filtered object preserves the filtration. -/
private def id (X : Fil(C)) : FilteredObject.Hom X X where
  hom := 𝟙 X.obj
  preserves i := by
    simpa using (X.filtration i).factors_self

/-- The composite of two filtration-preserving morphisms again preserves the filtration. -/
private def comp {X Y Z : Fil(C)} (f : FilteredObject.Hom X Y)
    (g : FilteredObject.Hom Y Z) : FilteredObject.Hom X Z where
  hom := f.hom ≫ g.hom
  preserves i := by
    let u := (Y.filtration i).factorThru ((X.filtration i).arrow ≫ f.hom) (f.preserves i)
    let v := (Z.filtration i).factorThru ((Y.filtration i).arrow ≫ g.hom) (g.preserves i)
    simpa [u, v, Category.assoc] using
      (Subobject.factors_comp_arrow (u ≫ v : (X.filtration i : C) ⟶ Z.filtration i))

end Hom

-- Proof sketch: equality of filtered morphisms is equality of the underlying morphisms together
-- with proof irrelevance for the filtration-preservation field.
/-- Identity is a left unit for morphisms of filtered objects. -/
private theorem id_comp_eq {X Y : Fil(C)} (f : FilteredObject.Hom X Y) :
    Hom.comp (Hom.id X) f = f := by
  ext
  simp [Hom.comp, Hom.id]

-- Proof sketch: equality of filtered morphisms is equality of the underlying morphisms together
-- with proof irrelevance for the filtration-preservation field.
/-- Identity is a right unit for morphisms of filtered objects. -/
private theorem comp_id_eq {X Y : Fil(C)} (f : FilteredObject.Hom X Y) :
    Hom.comp f (Hom.id Y) = f := by
  ext
  simp [Hom.comp, Hom.id]

-- Proof sketch: reduce to associativity of composition in the ambient category and then use proof
-- irrelevance for the filtration-preservation field.
/-- Composition of morphisms of filtered objects is associative. -/
private theorem assoc_eq {W X Y Z : Fil(C)} (f : FilteredObject.Hom W X)
    (g : FilteredObject.Hom X Y) (h : FilteredObject.Hom Y Z) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := by
  ext
  simp [Hom.comp, Category.assoc]

/-- The category of filtered objects over any ambient category. -/
instance : Category (Fil(C)) where
  Hom X Y := FilteredObject.Hom X Y
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := id_comp_eq
  comp_id := comp_id_eq
  assoc := assoc_eq

@[simp] theorem id_hom (X : Fil(C)) : (𝟙 X : X ⟶ X).hom = 𝟙 X.obj := rfl

@[simp] theorem comp_hom {X Y Z : Fil(C)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

namespace Hom

variable {X Y : Fil(C)}

/-- The morphism induced by a filtered morphism on the `p`-th filtration stages. -/
noncomputable abbrev stageMap (f : X ⟶ Y) (p : ℤ) : F^{p} X ⟶ F^{p} Y :=
  (Y.filtration.obj p).factorThru ((X.filtration.obj p).arrow ≫ f.hom) (f.preserves p)

/-- The `p`-th stage map is the restriction of the underlying morphism to the filtration stages. -/
theorem stageMap_comm (f : X ⟶ Y) (p : ℤ) :
    stageMap f p ≫ (Y.filtration.obj p).arrow = (X.filtration.obj p).arrow ≫ f.hom :=
  Subobject.factorThru_arrow _ _ (f.preserves p)

/-- The stage maps commute with the consecutive inclusions `F^{p + 1} ↪ F^p`. -/
theorem stageInclusion_naturality (f : X ⟶ Y) (p : ℤ) :
    X.filtration.stageInclusion p ≫ stageMap f p =
      stageMap f (p + 1) ≫ Y.filtration.stageInclusion p := by
  apply (cancel_mono (Y.filtration.obj p).arrow).1
  calc
    (X.filtration.stageInclusion p ≫ stageMap f p) ≫ (Y.filtration.obj p).arrow
        = X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow ≫ f.hom := by
            rw [Category.assoc, stageMap_comm]
    _ = (X.filtration.obj (p + 1)).arrow ≫ f.hom := by
          simp [DecreasingFiltration.stageInclusion]
    _ = stageMap f (p + 1) ≫ (Y.filtration.obj (p + 1)).arrow := by
          rw [stageMap_comm]
    _ = (stageMap f (p + 1) ≫ Y.filtration.stageInclusion p) ≫ (Y.filtration.obj p).arrow := by
          simp [Category.assoc, DecreasingFiltration.stageInclusion]

end Hom

/-- The forgetful functor from filtered objects to the ambient category. -/
def forget : Fil(C) ⥤ C where
  obj X := X.obj
  map f := f.hom

instance : (forget : Fil(C) ⥤ C).Faithful where
  map_injective {X Y} f g h := by
    exact FilteredObject.Hom.ext h

variable {X Y : Fil(C)}

instance (f : X ⟶ Y) [Epi f.hom] : Epi f := by
  exact (forget : Fil(C) ⥤ C).epi_of_epi_map (by simpa)

end FilteredObject

section Pullbacks

variable [HasPullbacks C]

namespace FilteredObject.Hom

variable {X Y : Fil(C)}

/-- Pullback reformulation of stagewise filtration-preservation. This is the bridge from the
primitive factorization owner to the induced-filtration view. -/
theorem pullback_preserves (f : X ⟶ Y) (i : ℤ) :
    X.filtration i ≤ (Subobject.pullback f.hom).obj (Y.filtration i) := by
  refine Subobject.le_of_factors ?_
  rw [pullback_factors_iff]
  simpa [Category.assoc] using f.preserves i

end FilteredObject.Hom

end Pullbacks

section ZeroMorphisms

variable [HasZeroMorphisms C]

namespace FilteredObject

/-- The zero morphism of filtered objects preserves every filtration stage. -/
private theorem zero_preserves (X Y : Fil(C)) (i : ℤ) :
    (Y.filtration i).Factors ((X.filtration i).arrow ≫ (0 : X.obj ⟶ Y.obj)) := by
  simpa using
    (Subobject.factors_zero : (Y.filtration i).Factors (0 : (X.filtration i : C) ⟶ Y.obj))

instance {X Y : Fil(C)} : Zero (X ⟶ Y) where
  zero :=
    { hom := 0
      preserves := zero_preserves X Y }

@[simp] theorem zero_hom {X Y : Fil(C)} : (0 : X ⟶ Y).hom = 0 := rfl

instance : HasZeroMorphisms (Fil(C)) where
  zero X Y := inferInstance
  comp_zero {X Y} f Z := by
    exact FilteredObject.forget.map_injective <| by
      change f.hom ≫ 0 = 0
      simp
  zero_comp X {Y Z} f := by
    exact FilteredObject.forget.map_injective <| by
      change (0 : X.obj ⟶ Y.obj) ≫ f.hom = 0
      simp

end FilteredObject

end ZeroMorphisms

section ZeroObjectOnFilteredObjects

variable [HasZeroObject C]

namespace FilteredObject

open scoped ZeroObject

noncomputable local instance : HasZeroMorphisms C :=
  HasZeroObject.zeroMorphismsOfZeroObject (C := C)

private noncomputable abbrev zeroObject : Fil(C) where
  obj := (0 : C)
  filtration :=
    { toFun := fun _ ↦ ⊤
      monotone' := fun _ _ _ ↦ le_rfl }

private theorem isZero_zeroObject : IsZero (zeroObject : Fil(C)) := by
  let toZero (X : Fil(C)) : zeroObject ⟶ X :=
    { hom := 0
      preserves := fun i ↦ by
        simpa using
          (Subobject.factors_zero :
            (X.filtration i).Factors
              (0 : Subobject.underlying.obj (zeroObject.filtration.obj i) ⟶ X.obj)) }
  let fromZero (X : Fil(C)) : X ⟶ zeroObject :=
    { hom := 0
      preserves := fun i ↦ by
        simpa using
          (Subobject.factors_zero :
            (zeroObject.filtration i).Factors
              (0 : Subobject.underlying.obj (X.filtration.obj i) ⟶ zeroObject.obj)) }
  refine
    { unique_to := fun X ↦ ⟨⟨toZero X⟩, ?_⟩
      unique_from := fun X ↦ ⟨⟨fromZero X⟩, ?_⟩ }
  · intro f
    apply FilteredObject.Hom.ext
    exact (isZero_zero C).eq_of_src _ _
  · intro f
    apply FilteredObject.Hom.ext
    exact (isZero_zero C).eq_of_tgt _ _

noncomputable instance : HasZeroObject (Fil(C)) :=
  ⟨⟨zeroObject, isZero_zeroObject⟩⟩

end FilteredObject

end ZeroObjectOnFilteredObjects

section Images

variable [HasImages C]

namespace DecreasingFiltration

/-- The filtration on the target obtained by taking the images of the stages of the source
filtration. For an epimorphism, this is the quotient filtration. -/
noncomputable def quotient {A B : C} (F : DecreasingFiltration A) (π : A ⟶ B) :
    DecreasingFiltration B :=
  (Subobject.exists π).toOrderHom.comp F

end DecreasingFiltration

end Images

section BinaryBiproducts

variable [HasZeroMorphisms C] [HasBinaryBiproducts C]

namespace DecreasingFiltration

variable {X Y : C}

private noncomputable abbrev biprodStage (FX : DecreasingFiltration X)
    (FY : DecreasingFiltration Y) (p : ℤ) : Subobject (X ⊞ Y : C) :=
  Subobject.mk
    (biprod.map (FX p).arrow (FY p).arrow :
      ((FX p : C) ⊞ (FY p : C)) ⟶ (X ⊞ Y : C))

/-- The stagewise direct-sum filtration induced by filtrations on `X` and `Y`. -/
private theorem biprod_antitone (FX : DecreasingFiltration X) (FY : DecreasingFiltration Y) :
    Antitone (biprodStage FX FY) := by
  intro p q hpq
  -- Map the stage at `q` into the stage at `p` componentwise.
  have hX : FX q ≤ FX p := DecreasingFiltration.antitone_obj FX hpq
  have hY : FY q ≤ FY p := DecreasingFiltration.antitone_obj FY hpq
  refine
    Subobject.mk_le_mk_of_comm
      (biprod.map (Subobject.ofLE _ _ hX) (Subobject.ofLE _ _ hY)) ?_
  apply biprod.hom_ext <;> simp [Category.assoc, Subobject.ofLE_arrow]

/-- The decreasing filtration on `X ⊞ Y` obtained by taking the stagewise biproduct of two
filtrations. -/
noncomputable def biprod (FX : DecreasingFiltration X) (FY : DecreasingFiltration Y) :
    DecreasingFiltration (X ⊞ Y : C) where
  toFun := biprodStage FX FY
  monotone' := by
    intro p q hpq
    exact biprod_antitone FX FY hpq

end DecreasingFiltration

namespace FilteredObject

variable {X Y : Fil(C)}

private theorem biprodFst_preserves (X Y : Fil(C)) (p : ℤ) :
    (X.filtration p).Factors
      (((DecreasingFiltration.biprod X.filtration Y.filtration) p).arrow ≫ biprod.fst) := by
  let stageArrow :
      ((X.filtration p : C) ⊞ (Y.filtration p : C)) ⟶ (X.obj ⊞ Y.obj : C) :=
    biprod.map (X.filtration p).arrow (Y.filtration p).arrow
  -- Work with the explicit `Subobject.mk` representative of the biproduct stage.
  change (X.filtration p).Factors ((Subobject.mk stageArrow).arrow ≫ biprod.fst)
  -- The chosen carrier maps to the `X`-stage through the stagewise first projection.
  refine (Subobject.factors_iff _ _).2 ?_
  refine ⟨(Subobject.underlyingIso stageArrow).hom ≫ biprod.fst, ?_⟩
  calc
    ((Subobject.underlyingIso stageArrow).hom ≫ biprod.fst) ≫ (X.filtration p).arrow
        = (Subobject.underlyingIso stageArrow).hom ≫ (biprod.fst ≫ (X.filtration p).arrow) := by
            simp [Category.assoc]
    _ = (Subobject.underlyingIso stageArrow).hom ≫ (stageArrow ≫ biprod.fst) := by
          simp [stageArrow]
    _ = (Subobject.mk stageArrow).arrow ≫ biprod.fst := by
          simp

private theorem biprodSnd_preserves (X Y : Fil(C)) (p : ℤ) :
    (Y.filtration p).Factors
      (((DecreasingFiltration.biprod X.filtration Y.filtration) p).arrow ≫ biprod.snd) := by
  let stageArrow :
      ((X.filtration p : C) ⊞ (Y.filtration p : C)) ⟶ (X.obj ⊞ Y.obj : C) :=
    biprod.map (X.filtration p).arrow (Y.filtration p).arrow
  -- Work with the explicit `Subobject.mk` representative of the biproduct stage.
  change (Y.filtration p).Factors ((Subobject.mk stageArrow).arrow ≫ biprod.snd)
  -- The chosen carrier maps to the `Y`-stage through the stagewise second projection.
  refine (Subobject.factors_iff _ _).2 ?_
  refine ⟨(Subobject.underlyingIso stageArrow).hom ≫ biprod.snd, ?_⟩
  calc
    ((Subobject.underlyingIso stageArrow).hom ≫ biprod.snd) ≫ (Y.filtration p).arrow
        = (Subobject.underlyingIso stageArrow).hom ≫ (biprod.snd ≫ (Y.filtration p).arrow) := by
            simp [Category.assoc]
    _ = (Subobject.underlyingIso stageArrow).hom ≫ (stageArrow ≫ biprod.snd) := by
          simp [stageArrow]
    _ = (Subobject.mk stageArrow).arrow ≫ biprod.snd := by
          simp

private theorem biprodInl_preserves (X Y : Fil(C)) (p : ℤ) :
    ((DecreasingFiltration.biprod X.filtration Y.filtration) p).Factors
      ((X.filtration p).arrow ≫ biprod.inl) := by
  let stageArrow :
      ((X.filtration p : C) ⊞ (Y.filtration p : C)) ⟶ (X.obj ⊞ Y.obj : C) :=
    biprod.map (X.filtration p).arrow (Y.filtration p).arrow
  -- Use the explicit `Subobject.mk` presentation of the stagewise biproduct.
  change (Subobject.mk stageArrow).Factors ((X.filtration p).arrow ≫ biprod.inl)
  rw [Subobject.mk_factors_iff]
  refine ⟨biprod.inl, ?_⟩
  simp [stageArrow]

private theorem biprodInr_preserves (X Y : Fil(C)) (p : ℤ) :
    ((DecreasingFiltration.biprod X.filtration Y.filtration) p).Factors
      ((Y.filtration p).arrow ≫ biprod.inr) := by
  let stageArrow :
      ((X.filtration p : C) ⊞ (Y.filtration p : C)) ⟶ (X.obj ⊞ Y.obj : C) :=
    biprod.map (X.filtration p).arrow (Y.filtration p).arrow
  -- Use the explicit `Subobject.mk` presentation of the stagewise biproduct.
  change (Subobject.mk stageArrow).Factors ((Y.filtration p).arrow ≫ biprod.inr)
  rw [Subobject.mk_factors_iff]
  refine ⟨biprod.inr, ?_⟩
  simp [stageArrow]

variable {W Z : Fil(C)}

private theorem biprodLift_preserves (f : W ⟶ X) (g : W ⟶ Y) (p : ℤ) :
    ((DecreasingFiltration.biprod X.filtration Y.filtration) p).Factors
      ((W.filtration p).arrow ≫ biprod.lift f.hom g.hom) := by
  let stageArrow :
      ((X.filtration p : C) ⊞ (Y.filtration p : C)) ⟶ (X.obj ⊞ Y.obj : C) :=
    biprod.map (X.filtration p).arrow (Y.filtration p).arrow
  -- The universal biproduct arrow on stages gives the desired factorization.
  change (Subobject.mk stageArrow).Factors ((W.filtration p).arrow ≫ biprod.lift f.hom g.hom)
  rw [Subobject.mk_factors_iff]
  refine ⟨biprod.lift (FilteredObject.Hom.stageMap f p) (FilteredObject.Hom.stageMap g p), ?_⟩
  -- Compare both composites after postcomposing with the two biproduct projections.
  apply biprod.hom_ext <;>
    simp [stageArrow, Category.assoc]

private theorem biprodDesc_preserves (f : X ⟶ Z) (g : Y ⟶ Z) (p : ℤ) :
    (Z.filtration p).Factors
      (((DecreasingFiltration.biprod X.filtration Y.filtration) p).arrow ≫ biprod.desc f.hom g.hom) := by
  let stageArrow :
      ((X.filtration p : C) ⊞ (Y.filtration p : C)) ⟶ (X.obj ⊞ Y.obj : C) :=
    biprod.map (X.filtration p).arrow (Y.filtration p).arrow
  -- Transport from the chosen stage carrier to the explicit biproduct of stages.
  change (Z.filtration p).Factors ((Subobject.mk stageArrow).arrow ≫ biprod.desc f.hom g.hom)
  refine (Subobject.factors_iff _ _).2 ?_
  refine
    ⟨(Subobject.underlyingIso stageArrow).hom ≫
        biprod.desc (FilteredObject.Hom.stageMap f p) (FilteredObject.Hom.stageMap g p), ?_⟩
  calc
    ((Subobject.underlyingIso stageArrow).hom ≫
        biprod.desc (FilteredObject.Hom.stageMap f p) (FilteredObject.Hom.stageMap g p)) ≫
          (Z.filtration p).arrow
        =
          (Subobject.underlyingIso stageArrow).hom ≫
            (biprod.desc (FilteredObject.Hom.stageMap f p) (FilteredObject.Hom.stageMap g p) ≫
              (Z.filtration p).arrow) := by
            simp [Category.assoc]
    _ =
          (Subobject.underlyingIso stageArrow).hom ≫
            (stageArrow ≫ biprod.desc f.hom g.hom) := by
              congr 1
              apply biprod.hom_ext' <;>
                simp [stageArrow]
    _ = (Subobject.mk stageArrow).arrow ≫ biprod.desc f.hom g.hom := by
          simp
    _ =
          ((DecreasingFiltration.biprod X.filtration Y.filtration) p).arrow ≫
            biprod.desc f.hom g.hom := by
              simp [DecreasingFiltration.biprod, DecreasingFiltration.biprodStage, stageArrow]

private noncomputable def binaryBicone (X Y : Fil(C)) : BinaryBicone X Y where
  pt :=
    { obj := X.obj ⊞ Y.obj
      filtration := DecreasingFiltration.biprod X.filtration Y.filtration }
  fst :=
    { hom := biprod.fst
      preserves := biprodFst_preserves X Y }
  snd :=
    { hom := biprod.snd
      preserves := biprodSnd_preserves X Y }
  inl :=
    { hom := biprod.inl
      preserves := biprodInl_preserves X Y }
  inr :=
    { hom := biprod.inr
      preserves := biprodInr_preserves X Y }
  inl_fst := by
    apply FilteredObject.forget.map_injective
    change biprod.inl ≫ biprod.fst = 𝟙 X.obj
    exact
      (biprod.inl_fst :
        (biprod.inl : X.obj ⟶ X.obj ⊞ Y.obj) ≫ biprod.fst = 𝟙 X.obj)
  inl_snd := by
    apply FilteredObject.forget.map_injective
    change biprod.inl ≫ biprod.snd = 0
    exact
      (biprod.inl_snd :
        (biprod.inl : X.obj ⟶ X.obj ⊞ Y.obj) ≫ biprod.snd = 0)
  inr_fst := by
    apply FilteredObject.forget.map_injective
    change biprod.inr ≫ biprod.fst = 0
    exact
      (biprod.inr_fst :
        (biprod.inr : Y.obj ⟶ X.obj ⊞ Y.obj) ≫ biprod.fst = 0)
  inr_snd := by
    apply FilteredObject.forget.map_injective
    change biprod.inr ≫ biprod.snd = 𝟙 Y.obj
    exact
      (biprod.inr_snd :
        (biprod.inr : Y.obj ⟶ X.obj ⊞ Y.obj) ≫ biprod.snd = 𝟙 Y.obj)

/-- Chap12 Definition 12 19 1: the stagewise biproduct bicone on filtered objects is a bilimit in
the category of filtered objects. -/
private noncomputable def binaryBiconeIsBilimit (X Y : Fil(C)) :
    (binaryBicone X Y).IsBilimit where
  isLimit :=
    { lift := fun s ↦
        { hom := biprod.lift (BinaryFan.fst s).hom (BinaryFan.snd s).hom
          preserves := biprodLift_preserves (BinaryFan.fst s) (BinaryFan.snd s) }
      fac := by
        intro s j
        rcases j with ⟨⟨⟩⟩
        · apply FilteredObject.forget.map_injective
          change
            biprod.lift (BinaryFan.fst s).hom (BinaryFan.snd s).hom ≫ biprod.fst =
              (BinaryFan.fst s).hom
          exact
            (biprod.lift_fst (BinaryFan.fst s).hom (BinaryFan.snd s).hom :
              biprod.lift (BinaryFan.fst s).hom (BinaryFan.snd s).hom ≫ biprod.fst =
                (BinaryFan.fst s).hom)
        · apply FilteredObject.forget.map_injective
          change
            biprod.lift (BinaryFan.fst s).hom (BinaryFan.snd s).hom ≫ biprod.snd =
              (BinaryFan.snd s).hom
          exact
            (biprod.lift_snd (BinaryFan.fst s).hom (BinaryFan.snd s).hom :
              biprod.lift (BinaryFan.fst s).hom (BinaryFan.snd s).hom ≫ biprod.snd =
                (BinaryFan.snd s).hom)
      uniq := by
        intro s m h
        apply FilteredObject.forget.map_injective
        apply biprod.hom_ext
        · change
            m.hom ≫ biprod.fst =
              biprod.lift (BinaryFan.fst s).hom (BinaryFan.snd s).hom ≫ biprod.fst
          rw [biprod.lift_fst]
          simpa [binaryBicone] using congrArg FilteredObject.Hom.hom (h ⟨WalkingPair.left⟩)
        · change
            m.hom ≫ biprod.snd =
              biprod.lift (BinaryFan.fst s).hom (BinaryFan.snd s).hom ≫ biprod.snd
          rw [biprod.lift_snd]
          simpa [binaryBicone] using congrArg FilteredObject.Hom.hom (h ⟨WalkingPair.right⟩) }
  isColimit :=
    { desc := fun s ↦
        { hom := biprod.desc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom
          preserves := biprodDesc_preserves (BinaryCofan.inl s) (BinaryCofan.inr s) }
      fac := by
        intro s j
        rcases j with ⟨⟨⟩⟩
        · apply FilteredObject.forget.map_injective
          change
            biprod.inl ≫ biprod.desc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom =
              (BinaryCofan.inl s).hom
          exact
            (biprod.inl_desc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom :
              biprod.inl ≫ biprod.desc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom =
                (BinaryCofan.inl s).hom)
        · apply FilteredObject.forget.map_injective
          change
            biprod.inr ≫ biprod.desc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom =
              (BinaryCofan.inr s).hom
          exact
            (biprod.inr_desc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom :
              biprod.inr ≫ biprod.desc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom =
                (BinaryCofan.inr s).hom)
      uniq := by
        intro s m h
        apply FilteredObject.forget.map_injective
        apply biprod.hom_ext'
        · change
            biprod.inl ≫ m.hom =
              biprod.inl ≫ biprod.desc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom
          rw [biprod.inl_desc]
          simpa [binaryBicone] using congrArg FilteredObject.Hom.hom (h ⟨WalkingPair.left⟩)
        · change
            biprod.inr ≫ m.hom =
              biprod.inr ≫ biprod.desc (BinaryCofan.inl s).hom (BinaryCofan.inr s).hom
          rw [biprod.inr_desc]
          simpa [binaryBicone] using congrArg FilteredObject.Hom.hom (h ⟨WalkingPair.right⟩) }

/-- Filtered objects inherit binary biproducts from the ambient category by equipping the ambient
biproduct object with the stagewise biproduct filtration. -/
noncomputable instance (X Y : Fil(C)) : HasBinaryBiproduct X Y :=
  HasBinaryBiproduct.mk
    { bicone := binaryBicone X Y
      isBilimit := binaryBiconeIsBilimit X Y }

instance : HasBinaryBiproducts (Fil(C)) where
  has_binary_biproduct _ _ := inferInstance

end FilteredObject

end BinaryBiproducts

end CategoryTheory
