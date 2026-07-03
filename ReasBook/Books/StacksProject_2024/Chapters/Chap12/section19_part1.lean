import Mathlib
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_19_1 (from Chap12) -/
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

/-- Definition 12.19.1: the source-facing owner object is an object equipped with a decreasing
`ℤ`-indexed filtration by subobjects. Later abelian-category constructions specialize this owner
to the textbook setting. -/
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
    Antitone (biprodStage FX FY) := sorry

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
  sorry

private theorem biprodSnd_preserves (X Y : Fil(C)) (p : ℤ) :
    (Y.filtration p).Factors
      (((DecreasingFiltration.biprod X.filtration Y.filtration) p).arrow ≫ biprod.snd) := by
  sorry

private theorem biprodInl_preserves (X Y : Fil(C)) (p : ℤ) :
    ((DecreasingFiltration.biprod X.filtration Y.filtration) p).Factors
      ((X.filtration p).arrow ≫ biprod.inl) := by
  sorry

private theorem biprodInr_preserves (X Y : Fil(C)) (p : ℤ) :
    ((DecreasingFiltration.biprod X.filtration Y.filtration) p).Factors
      ((Y.filtration p).arrow ≫ biprod.inr) := by
  sorry

variable {W Z : Fil(C)}

private theorem biprodLift_preserves (f : W ⟶ X) (g : W ⟶ Y) (p : ℤ) :
    ((DecreasingFiltration.biprod X.filtration Y.filtration) p).Factors
      ((W.filtration p).arrow ≫ biprod.lift f.hom g.hom) := by
  sorry

private theorem biprodDesc_preserves (f : X ⟶ Z) (g : Y ⟶ Z) (p : ℤ) :
    (Z.filtration p).Factors
      (((DecreasingFiltration.biprod X.filtration Y.filtration) p).arrow ≫ biprod.desc f.hom g.hom) := by
  sorry

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

/-! ### Lemma_12_19_2 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace FilteredObject

/- Source/core/bridge triage for Lemma 12.19.2:
- source-facing: the textbook statement that filtered objects form a preadditive category.
- core/canonical owners: `FilteredObject.Hom`, `FilteredObject.forget`, and `CategoryTheory.Preadditive`.
- primitive data: a filtered morphism is an ambient morphism together with stagewise factorization
  through the target filtration.
- derived API: additive operations on filtered morphisms, the induced `Hom.hom` simp lemmas, the
  additive forgetful functor, and the `Preadditive (FilteredObject C)` instance.
- domain-style sampling:
  * `FilteredObject.Hom` and the faithful owner functor `FilteredObject.forget` in
    `Definition_12_19_1`;
  * `CategoryTheory.Preadditive` in mathlib;
  * `Function.Injective.addCommGroup` together with the owner-side `Hom.hom` projection pattern in
    mathlib categories such as `ModuleCat` and `HomologicalComplex`.

The canonical owner stays `FilteredObject.Hom`: the additive structure is not recalled from a
fully faithful transport theorem, but induced from the ambient preadditive hom-group along the
injective projection `Hom.hom`. -/

variable {X Y : FilteredObject C}

private theorem add_preserves (f g : X ⟶ Y) :
    ∀ i : ℤ, (Y.filtration i).Factors ((X.filtration i).arrow ≫ (f.hom + g.hom)) := sorry

private theorem neg_preserves (f : X ⟶ Y) :
    ∀ i : ℤ, (Y.filtration i).Factors ((X.filtration i).arrow ≫ (-f.hom)) := sorry

private theorem sub_preserves (f g : X ⟶ Y) :
    ∀ i : ℤ, (Y.filtration i).Factors ((X.filtration i).arrow ≫ (f.hom - g.hom)) := sorry

private theorem zsmul_preserves (n : ℤ) (f : X ⟶ Y) :
    ∀ i : ℤ, (Y.filtration i).Factors ((X.filtration i).arrow ≫ (n • f.hom)) := sorry

private theorem nsmul_preserves (n : ℕ) (f : X ⟶ Y) :
    ∀ i : ℤ, (Y.filtration i).Factors ((X.filtration i).arrow ≫ (n • f.hom)) := sorry

instance : Add (X ⟶ Y) where
  add f g :=
    { hom := f.hom + g.hom
      preserves := add_preserves f g }

instance : Neg (X ⟶ Y) where
  neg f :=
    { hom := -f.hom
      preserves := neg_preserves f }

instance : Sub (X ⟶ Y) where
  sub f g :=
    { hom := f.hom - g.hom
      preserves := sub_preserves f g }

instance : SMul ℕ (X ⟶ Y) where
  smul n f :=
    { hom := n • f.hom
      preserves := nsmul_preserves n f }

instance : SMul ℤ (X ⟶ Y) where
  smul n f :=
    { hom := n • f.hom
      preserves := zsmul_preserves n f }

@[simp] theorem add_hom (f g : X ⟶ Y) :
    (f + g).hom = f.hom + g.hom := rfl

@[simp] theorem neg_hom (f : X ⟶ Y) :
    (-f).hom = -f.hom := rfl

@[simp] theorem sub_hom (f g : X ⟶ Y) :
    (f - g).hom = f.hom - g.hom := rfl

@[simp] theorem nsmul_hom (n : ℕ) (f : X ⟶ Y) :
    (n • f).hom = n • f.hom := rfl

@[simp] theorem zsmul_hom (n : ℤ) (f : X ⟶ Y) :
    (n • f).hom = n • f.hom := rfl

omit [Preadditive C] in
theorem hom_injective : Function.Injective (Hom.hom : (X ⟶ Y) → (X.obj ⟶ Y.obj)) := by
  intro f g h
  exact FilteredObject.forget.map_injective h

instance : AddCommGroup (X ⟶ Y) :=
  Function.Injective.addCommGroup (Hom.hom : (X ⟶ Y) → (X.obj ⟶ Y.obj)) hom_injective
    rfl
    (fun _ _ ↦ rfl)
    (fun _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl)

variable {P Q R : FilteredObject C}

/-- Lemma 12.19.2: in the textbook abelian setting the category of filtered objects is
preadditive; the construction only uses the stagewise factorization owner and `[Preadditive C]`. -/
instance filteredObject_preadditive : Preadditive (FilteredObject C) where
  add_comp P Q R f f' g := by
    apply hom_injective
    change (f.hom + f'.hom) ≫ g.hom = f.hom ≫ g.hom + f'.hom ≫ g.hom
    exact Preadditive.add_comp P.obj Q.obj R.obj f.hom f'.hom g.hom
  comp_add P Q R f g g' := by
    apply hom_injective
    change f.hom ≫ (g.hom + g'.hom) = f.hom ≫ g.hom + f.hom ≫ g'.hom
    exact Preadditive.comp_add P.obj Q.obj R.obj f.hom g.hom g'.hom

instance : (FilteredObject.forget : FilteredObject C ⥤ C).Additive where
  map_add := by
    intro _ _ f g
    rfl

end FilteredObject

end CategoryTheory

/-! ### Definition_12_19_3 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C]

namespace Limits

/-- In a balanced category, an epimorphism has full image, so its image subobject is the top
subobject. This bridge is used by the strictness criterion for epimorphisms. -/
theorem imageSubobject_eq_top_of_epi [Balanced C] {X Y : C} (g : X ⟶ Y) [Epi g] :
    imageSubobject g = (⊤ : Subobject Y) := by
  let e : X ⟶ imageSubobject g := factorThruImageSubobject g
  letI : Epi (e ≫ (imageSubobject g).arrow) := by
    simpa [e] using (inferInstance : Epi g)
  letI : Epi (imageSubobject g).arrow := epi_of_epi e (imageSubobject g).arrow
  letI : IsIso (imageSubobject g).arrow := isIso_of_mono_of_epi (imageSubobject g).arrow
  exact Subobject.eq_top_of_isIso_arrow (imageSubobject g)

/-
The balanced hypothesis is essential here: the conclusion identifies the image mono of an epi
with an isomorphism, which is exactly the mono+epi-to-iso step provided by `Balanced`.
-/

/-- In a balanced category with equalizers, the image of a composite `f ≫ g` is exactly the image
of `g` restricted to the image subobject of `f`. -/
theorem imageSubobject_comp_eq_imageSubobject_restriction [HasEqualizers C] [Balanced C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
  let h := imageSubobject_comp_le (factorThruImageSubobject f) ((imageSubobject f).arrow ≫ g)
  let φ := Subobject.ofLE _ _ h
  haveI : Epi φ := by
    dsimp [φ, h]
    infer_instance
  haveI : IsIso φ := isIso_of_mono_of_epi φ
  have :
      imageSubobject (factorThruImageSubobject f ≫ (imageSubobject f).arrow ≫ g) =
        imageSubobject ((imageSubobject f).arrow ≫ g) :=
    Subobject.eq_of_comm (asIso φ) (by simp [φ])
  simpa [Category.assoc] using this

end Limits

namespace DecreasingFiltration

variable {X Y : C}

/-- The quotient filtration is computed stagewise by the image of the composite into the target.
-/
theorem quotient_eq_imageSubobject_comp (F : DecreasingFiltration X) (g : X ⟶ Y) (i : ℤ) :
    F.quotient g i = imageSubobject ((F i).arrow ≫ g) := by
  change (Subobject.«exists» g).obj (F i) = _
  apply Subobject.eq_of_comm
    (Subobject.existsIsoImage g (F i) ≪≫ (imageSubobjectIso _).symm)
  calc
    ((Subobject.existsIsoImage g (F i)).hom ≫
        (imageSubobjectIso ((F i).arrow ≫ g)).inv) ≫
        (imageSubobject ((F i).arrow ≫ g)).arrow
        = (Subobject.existsIsoImage g (F i)).hom ≫ image.ι ((F i).arrow ≫ g) := by
            simp [Category.assoc]
    _ = ((Subobject.«exists» g).obj (F i)).arrow := by
          simpa [Subobject.existsIsoImage] using
            (Over.w ((Subobject.existsCompRepresentativeIso g).app (F i)).hom.hom)

end DecreasingFiltration

namespace FilteredObject.Hom

variable [HasPullbacks C]
variable {A B : FilteredObject C}

/-
Source/core/bridge triage for Definition 12.19.3:
- sampled owner declarations in this domain:
  `Subobject.existsIsoImage`, `DecreasingFiltration.quotient`,
  `Limits.imageSubobject_mono`, `Subobject.eq_top_of_isIso_arrow`
- source-facing owner: strictness of a filtered morphism
- core/canonical owner: `FilteredObject.Hom.Strict`
- primitive data: the stagewise image subobject of `(A.filtration i).arrow ≫ f.hom`
- bridge/view: the quotient filtration `A.filtration.quotient f.hom`
- derived API: the quotient-filtration reformulation and the identity map is strict
-/

/-- Definition 12.19.3: a morphism of filtered objects is strict when, for every integer `i`, the
image of the `i`-th filtration step is exactly the intersection of the total image with the
`i`-th filtration step of the target. -/
def Strict (f : A ⟶ B) : Prop :=
  ∀ i : ℤ, imageSubobject ((A.filtration i).arrow ≫ f.hom) = imageSubobject f.hom ⊓ B.filtration i

/-- Bridge/view reformulation of strictness in terms of the quotient filtration. -/
theorem strict_iff_quotient_eq_inf (f : A ⟶ B) :
    Strict f ↔ ∀ i : ℤ, A.filtration.quotient f.hom i = imageSubobject f.hom ⊓ B.filtration i := by
  constructor <;> intro hf i <;>
    simpa [DecreasingFiltration.quotient_eq_imageSubobject_comp] using hf i

/-- The identity morphism of a filtered object is strict. -/
@[simp] theorem strict_id (A : FilteredObject C) : Strict (𝟙 A) := by
  intro i
  change imageSubobject ((A.filtration i).arrow ≫ 𝟙 A.obj) =
      imageSubobject (𝟙 A.obj) ⊓ A.filtration i
  rw [Limits.imageSubobject_mono]
  rw [Limits.imageSubobject_mono, ← Subobject.top_eq_id A.obj]
  simp

end FilteredObject.Hom

end CategoryTheory

/-! ### Lemma_12_19_4 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FilteredObject

variable (A : FilteredObject C)

-- Internal bridge: transport a filtered object structure across an isomorphism of underlying
-- objects so the public `image` owner can reuse `subobjectFilteredObject` rather than rebuilding
-- its filtration entrywise.
private abbrev ofIso {X : C} (e : A.obj ≅ X) : FilteredObject C where
  obj := X
  filtration := ((Subobject.mapIsoToOrderIso e : Subobject A.obj →o Subobject X)).comp A.filtration

section Pullbacks

variable [HasPullbacks C]
variable (X : Subobject A.obj)

/-- The induced filtered object on a subobject `X ⊆ A`. -/
def subobjectFilteredObject : FilteredObject C where
  obj := X
  filtration := A.filtration.induced X

/-- The inclusion of a filtered subobject into the ambient filtered object. -/
def subobjectInclusion : A.subobjectFilteredObject X ⟶ A where
  hom := X.arrow
  preserves := by
    intro p
    sorry

end Pullbacks

section Quotients

variable [HasZeroMorphisms C] [HasImages C] [HasCokernels C]
variable (X : Subobject A.obj)

/-- The quotient filtered object `A / X`. -/
def quotientFilteredObject : FilteredObject C where
  obj := cokernel X.arrow
  filtration := A.filtration.quotient (cokernel.π X.arrow)

/-- The quotient map from a filtered object to the quotient by a subobject. -/
def toQuotient : A ⟶ A.quotientFilteredObject X where
  hom := cokernel.π X.arrow
  preserves := by
    intro p
    sorry

end Quotients

section PullbacksQuotients

variable [HasPullbacks C] [HasZeroMorphisms C] [HasImages C] [HasCokernels C]
variable (X : Subobject A.obj)

/-- The inclusion of a filtered subobject followed by the quotient map is zero. -/
theorem subobjectInclusion_comp_toQuotient :
    A.subobjectInclusion X ≫ A.toQuotient X = 0 := sorry

end PullbacksQuotients

section Abelian

variable [Abelian C]

namespace Hom

variable {A B : FilteredObject C}

open FilteredObject

/-
Source/core/bridge triage for Lemma 12.19.4:
- source-facing: strictness of a filtered morphism
- core/canonical owners: `FilteredObject.subobjectFilteredObject`,
  `FilteredObject.quotientFilteredObject`, and `Abelian.coimageImageComparison f.hom`
- bridge/view: the filtered `coimage`, filtered `image`, and their lifted comparison morphism
- primitive data: filtration-preserving morphisms are built from stagewise factorization data
- derived API: the filtered comparison morphism and the strictness/isomorphism criterion
-/

/-- The filtered coimage of a morphism, equipped with the quotient filtration coming from the
source via the canonical projection `Abelian.coimage.π`. -/
abbrev coimage (f : A ⟶ B) : FilteredObject C :=
  { obj := Abelian.coimage f.hom
    filtration := A.filtration.quotient (Abelian.coimage.π f.hom) }

/-- The filtered image of a morphism, equipped with the induced filtration coming from the target.
-/
abbrev image (f : A ⟶ B) : FilteredObject C :=
  (B.subobjectFilteredObject (imageSubobject f.hom)).ofIso
    (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm)

-- Proof sketch: by construction, the filtration on `coim(f)` is the quotient filtration from the
-- source and the filtration on `im(f)` is the induced filtration from the target, so the canonical
-- comparison map yields the stagewise factorization needed for a filtered morphism.
private theorem coimageImageComparison_preserves (f : A ⟶ B) (i : ℤ) :
    ((image f).filtration i).Factors
      (((coimage f).filtration i).arrow ≫ Abelian.coimageImageComparison f.hom) :=
  sorry

/-- The canonical morphism from the filtered coimage of `f` to the filtered image of `f`. -/
def coimageImageComparison (f : A ⟶ B) : coimage f ⟶ image f where
  hom := Abelian.coimageImageComparison f.hom
  preserves := coimageImageComparison_preserves f

-- Proof sketch: the quotient filtration on `coim(f)` and the induced filtration on `im(f)` agree
-- exactly when the stagewise image/intersection equality defining strictness holds. Thus `f` is
-- strict precisely when the canonical comparison is an isomorphism in the filtered category.
/-- Lemma 12.19.4: for a morphism of filtered objects in an abelian category, strictness is
equivalent to the canonical comparison morphism `coim(f) ⟶ im(f)` being an isomorphism of
filtered objects. -/
theorem strict_iff_coimageImageComparison_isIso (f : A ⟶ B) :
    Strict f ↔ IsIso (coimageImageComparison f) := sorry

end Hom
end Abelian
end FilteredObject

end CategoryTheory

/-! ### Lemma_12_19_5 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasImages 𝒜] [HasPullbacks 𝒜]
  [HasBinaryBiproducts 𝒜]

namespace FilteredObject.Hom

open FilteredObject

variable {A B C : FilteredObject 𝒜}

/-
Source/core/bridge triage for Lemma 12.19.5:
- source-facing: strictness of the filtered biproduct lift attached to a strict monomorphism
- core/canonical owners: `strict_iff_induced_filtration_of_mono` and
  `biprod.mono_lift_of_mono_left`, `HasBinaryBiproducts (FilteredObject C)`
- bridge/view: the canonical map `biprod.lift f g : A ⟶ B ⊞ C`
-/

-- Proof sketch: first recover `Mono (biprod.lift f g).hom` from the ambient owner instance
-- `biprod.mono_lift_of_mono_left`. Then apply the canonical
-- mono-side strictness criterion `strict_iff_induced_filtration_of_mono` to `biprod.lift f g`.
-- The induced filtration along `biprod.lift f.hom g.hom` is computed from the left component
-- using strictness of `f`; `g` contributes only the already bundled filtration-preservation data.
/-- Lemma 12.19.5: if `f : A ⟶ B` is a strict monomorphism of filtered objects and
`g : A ⟶ C` is any filtered morphism, then the induced morphism
`A ⟶ B ⊞ C` is strict. Its monomorphism part is the ambient owner instance
`biprod.mono_lift_of_mono_left` on the underlying biproduct-lift map. -/
theorem strict_biprodLift (f : A ⟶ B) (g : A ⟶ C) [Mono f.hom] (hf : Strict f) :
    Strict (biprod.lift f g) := by
  letI : Mono (biprod.lift f g).hom := by
    change Mono (biprod.lift f.hom g.hom)
    infer_instance
  rw [strict_iff_induced_filtration_of_mono]
  refine OrderHom.ext _ _ (funext fun i ↦ le_antisymm ?_ ?_)
  · refine Subobject.le_of_factors ?_
    exact Limits.pullback_factors (biprod.lift f g).hom (((B ⊞ C : FilteredObject 𝒜)).filtration i)
      (A.filtration i).arrow ((biprod.lift f g).preserves i)
  · have hstage :
        ((B ⊞ C : FilteredObject 𝒜)).filtration i ≤
          (Subobject.pullback biprod.fst).obj (B.filtration i) := by
      refine Subobject.le_of_factors ?_
      exact Limits.pullback_factors biprod.fst (B.filtration i)
        (((B ⊞ C : FilteredObject 𝒜)).filtration i).arrow (biprod.fst.preserves i)
    calc
      (Subobject.pullback (biprod.lift f g).hom).obj (((B ⊞ C : FilteredObject 𝒜)).filtration i)
          ≤ (Subobject.pullback (biprod.lift f g).hom).obj
              ((Subobject.pullback biprod.fst).obj (B.filtration i)) :=
            (Subobject.pullback (biprod.lift f g).hom).monotone hstage
      _ = (Subobject.pullback f.hom).obj (B.filtration i) := by
            calc
              (Subobject.pullback (biprod.lift f g).hom).obj
                  ((Subobject.pullback biprod.fst).obj (B.filtration i))
                  = (Subobject.pullback ((biprod.lift f g).hom ≫ biprod.fst)).obj
                      (B.filtration i) := by
                          symm
                          exact Subobject.pullback_comp (biprod.lift f g).hom biprod.fst
                            (B.filtration i)
              _ = (Subobject.pullback f.hom).obj (B.filtration i) := by
                    change
                      (Subobject.pullback ((biprod.lift f g).hom ≫ biprod.fst)).obj
                          (B.filtration i)
                        = (Subobject.pullback f.hom).obj (B.filtration i)
                    simp
      _ = A.filtration i := by
            simpa using
              (congrArg (fun F ↦ F i)
                ((strict_iff_induced_filtration_of_mono f).1 hf)).symm

end FilteredObject.Hom

end CategoryTheory

/-! ### Lemma_12_19_6 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroMorphisms 𝒜] [HasImages 𝒜] [HasPullbacks 𝒜]
  [HasBinaryBiproducts 𝒜] [Balanced 𝒜]

namespace FilteredObject.Hom

open FilteredObject

variable {X Y Z : FilteredObject 𝒜}

/-
Source/core/bridge triage for Lemma 12.19.6:
- sampled owner declarations in this filtered-object domain:
  `FilteredObject.Hom.Strict`,
  `FilteredObject.Hom.strict_iff_quotient_eq_inf`,
  `FilteredObject.Hom.strict_iff_quotient_filtration_of_epi`,
  `CategoryTheory.Limits.biprod.epi_desc_of_epi_left`
- source-facing: strictness of the filtered biproduct descent map
- core/canonical owner: `FilteredObject.Hom.Strict`, accessed through the epi-side criterion
  `strict_iff_quotient_filtration_of_epi`
- bridge/view: the canonical map `biprod.desc f g : X ⊞ Y ⟶ Z`; the sampled ambient owner
  `biprod.epi_desc_of_epi_left` supplies the needed `Epi` instance on the underlying biproduct
  descent map
- primitive data: filtered morphisms `f`, `g`, together with the strict epimorphism data on `f`
- derived API: strictness of `biprod.desc f g`, obtained by identifying its quotient filtration
  with the filtration on `Z`
-/

-- Proof sketch: apply the canonical epi-side strictness criterion
-- `strict_iff_quotient_filtration_of_epi` to `biprod.desc f g`. The required epimorphism on the
-- underlying map is the canonical mathlib instance `biprod.epi_desc_of_epi_left`. The quotient
-- filtration of the stagewise biproduct along `biprod.desc f.hom g.hom` is then computed from the
-- left summand because `g` already preserves filtration stages, and strictness of `f` identifies
-- that quotient filtration with the given filtration on `Z`.
/-- Lemma 12.19.6: if `f : X ⟶ Z` is a strict epimorphism of filtered objects and `g : Y ⟶ Z` is
any filtered morphism, then the induced morphism `X ⊞ Y ⟶ Z` is again a
strict morphism. The key owner criterion is the epi-side strictness reformulation
`strict_iff_quotient_filtration_of_epi`, together with the canonical ambient instance
`biprod.epi_desc_of_epi_left` on the underlying biproduct descent map. -/
theorem strict_biprodDesc (f : X ⟶ Z) (g : Y ⟶ Z) [Epi f.hom] (hf : Strict f) :
    Strict (biprod.desc f g) := by
  have hinl : (biprod.inl : X ⟶ X ⊞ Y).hom ≫ (biprod.desc f g).hom = f.hom := by
    exact congrArg FilteredObject.Hom.hom (biprod.inl_desc f g)
  letI : Epi (biprod.desc f g).hom := by
    exact epi_of_epi_fac hinl
  refine (strict_iff_quotient_filtration_of_epi (biprod.desc f g)).2 ?_
  refine OrderHom.ext _ _ (funext fun i ↦ le_antisymm ?_ ?_)
  · rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    have hquot :
        Z.filtration i = imageSubobject ((X.filtration i).arrow ≫ f.hom) := by
      simpa [DecreasingFiltration.quotient_eq_imageSubobject_comp] using
        congrArg (fun F ↦ F i) ((strict_iff_quotient_filtration_of_epi f).1 hf)
    have hstage :
        ((X ⊞ Y).filtration i).Factors
          ((X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom) := by
      simpa using (biprod.inl : X ⟶ X ⊞ Y).preserves i
    let α :=
      ((X ⊞ Y).filtration i).factorThru
        ((X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom) hstage
    have hα :
        α ≫ ((X ⊞ Y).filtration i).arrow =
          (X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom := by
      simpa [α] using
        Subobject.factorThru_arrow ((X ⊞ Y).filtration i)
          ((X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom) hstage
    have hcomp :
        (X.filtration i).arrow ≫ f.hom =
          α ≫ ((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom := by
      calc
        (X.filtration i).arrow ≫ f.hom =
            (X.filtration i).arrow ≫ (biprod.inl : X ⟶ X ⊞ Y).hom ≫ (biprod.desc f g).hom := by
              simpa [Category.assoc] using
                (congrArg (fun t ↦ (X.filtration i).arrow ≫ t) hinl).symm
        _ = (α ≫ ((X ⊞ Y).filtration i).arrow) ≫ (biprod.desc f g).hom := by
              simpa [hα]
        _ = α ≫ ((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom := by
              simp [Category.assoc]
    calc
      Z.filtration i = imageSubobject (α ≫ ((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom) := by
        simpa [hcomp] using hquot
      _ ≤ imageSubobject (((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom) := by
        simpa [Category.assoc] using
          (imageSubobject_comp_le α
            (((X ⊞ Y).filtration i).arrow ≫ (biprod.desc f g).hom))
  · simpa [DecreasingFiltration.quotient_eq_imageSubobject_comp] using
      imageSubobject_le _ _ (Subobject.factorThru_arrow _ _ ((biprod.desc f g).preserves i))

end FilteredObject.Hom

end CategoryTheory

/-! ### Lemma_12_19_7 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory
namespace FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C]
variable {A B : FilteredObject C} (f : A ⟶ B)

-- Proof sketch: pull back the stagewise strictness identity along the monomorphism `f.hom`.
-- Because pullback along a mono inverts the forward-map functor on subobjects, the left side
-- becomes the source filtration stage; the right side becomes the pullback of the target stage.
/-- Lemma 12.19.7 (1): for an injective morphism of filtered objects, strictness is equivalent to
the source filtration agreeing stagewise with the induced filtration. We keep the right-hand side
on `A.obj`, so it is written in the pullback form underlying `DecreasingFiltration.induced`. -/
theorem strict_iff_induced_filtration_of_mono [Mono f.hom] :
    Strict f ↔
      A.filtration = (Subobject.pullback f.hom).toOrderHom.comp B.filtration := by
  constructor
  · intro hf
    refine OrderHom.ext _ _ ?_
    funext i
    have hi := congrArg ((Subobject.pullback f.hom).obj) ((strict_iff_quotient_eq_inf f).1 hf i)
    simpa [DecreasingFiltration.quotient, Subobject.exists_iso_map,
      Limits.imageSubobject_mono, Subobject.inf_pullback, Subobject.pullback_self] using hi
  · intro h
    refine (strict_iff_quotient_eq_inf f).2 ?_
    intro i
    have hi := congrArg (fun F ↦ F i) h
    calc
      A.filtration.quotient f.hom i
          = (Subobject.map f.hom).obj ((Subobject.pullback f.hom).obj (B.filtration i)) := by
              simpa [DecreasingFiltration.quotient, Subobject.exists_iso_map] using
                congrArg ((Subobject.«exists» f.hom).obj) hi
      _ = Limits.imageSubobject f.hom ⊓ B.filtration i := by
              simpa [Subobject.inf_def, Limits.imageSubobject_mono] using
                (Subobject.inf_eq_map_pullback' (MonoOver.mk f.hom) (B.filtration i)).symm

-- Proof sketch: when `f.hom` is epi, `imageSubobject f.hom = ⊤`, so the stagewise strictness
-- equality becomes the statement that each target filtration stage is the image of the
-- corresponding source filtration stage under `f.hom`.
/-- Lemma 12.19.7 (2): for a surjective morphism of filtered objects, strictness is equivalent to
the target filtration agreeing stagewise with the quotient filtration. -/
theorem strict_iff_quotient_filtration_of_epi [Balanced C] [Epi f.hom] :
    Strict f ↔ B.filtration = A.filtration.quotient f.hom :=
  by
    constructor
    · intro hf
      refine OrderHom.ext _ _ ?_
      funext i
      simpa [Limits.imageSubobject_eq_top_of_epi f.hom] using
        ((strict_iff_quotient_eq_inf f).1 hf i).symm
    · intro h
      refine (strict_iff_quotient_eq_inf f).2 ?_
      intro i
      have hi := congrArg (fun F ↦ F i) h
      simpa [Limits.imageSubobject_eq_top_of_epi f.hom] using hi.symm

end FilteredObject.Hom
end CategoryTheory

/-! ### Lemma_12_19_8 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe v u v₁ u₁

noncomputable section

namespace CategoryTheory
namespace FilteredObject.Hom

/-
Source/core/bridge triage for Lemma 12.19.8:
- source-facing: closure and non-closure properties of strict filtered morphisms under composition
- core/canonical owner: `FilteredObject.Hom.Strict`
- bridge/view: the mono/epi characterizations from Lemma `12.19.7`
-/

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C]
variable [HasEqualizers C]

private theorem imageSubobject_comp_eq_map_of_mono [Balanced C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    imageSubobject (f ≫ g) = (Subobject.map g).obj (imageSubobject f) := by
  calc
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
      rw [CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction f g]
    _ = Subobject.mk ((imageSubobject f).arrow ≫ g) := by
      simpa using (Limits.imageSubobject_mono ((imageSubobject f).arrow ≫ g))
    _ = (Subobject.map g).obj (Subobject.mk (imageSubobject f).arrow) := by
      rw [Subobject.map_mk]
    _ = (Subobject.map g).obj (imageSubobject f) := by
      rw [Subobject.mk_arrow]

private theorem imageSubobject_comp_eq_of_epi [Balanced C] {X Y Z : C}
    (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) :
    imageSubobject (f ≫ g) = imageSubobject g := by
  calc
    imageSubobject (f ≫ g) = imageSubobject ((imageSubobject f).arrow ≫ g) := by
      rw [CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction f g]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ g) := by
      simpa using congrArg (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ g))
        (Limits.imageSubobject_eq_top_of_epi f)
    _ = imageSubobject g := by
      simpa using
        (CategoryTheory.Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) g)

-- Proof sketch: use the explicit two-step filtration on a two-dimensional vector space, together
-- with the induced filtration on a line and the quotient filtration on the quotient by a basis
-- vector, to obtain strict maps whose nonzero composite fails the strictness equality.
/-- Lemma 12.19.8 (1): in general, the composite of strict morphisms of filtered objects need not
be strict. -/
theorem strict_comp_not_in_general :
    ¬ ∀ {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] {A B C : FilteredObject 𝒜}
        (f : A ⟶ B) (g : B ⟶ C), Strict f → Strict g → Strict (f ≫ g) := by
  sorry

variable {A B D : FilteredObject C}

private theorem map_inf_eq_of_strict_mono (g : B ⟶ D) [Mono g.hom] (hg : Strict g)
    (x : Subobject B.obj) (i : ℤ) :
    (Subobject.map g.hom).obj (x ⊓ B.filtration i) =
      (Subobject.map g.hom).obj x ⊓ D.filtration i := by
  have hgi : B.filtration i = (Subobject.pullback g.hom).obj (D.filtration i) := by
    exact congrArg (fun F ↦ F i) ((strict_iff_induced_filtration_of_mono g).1 hg)
  rw [hgi, Subobject.inf_map]
  rw [show (Subobject.map g.hom).obj ((Subobject.pullback g.hom).obj (D.filtration i)) =
      Subobject.mk g.hom ⊓ D.filtration i by
        simpa [Subobject.inf_def] using
          (Subobject.inf_eq_map_pullback' (MonoOver.mk g.hom) (D.filtration i)).symm]
  have hx : (Subobject.map g.hom).obj x ≤ Subobject.mk g.hom := by
    induction x using Subobject.ind
    rename_i X m hm
    simpa [Subobject.map_mk] using
      (Subobject.mk_le_mk_of_comm m (by simp) :
        Subobject.mk (m ≫ g.hom) ≤ Subobject.mk g.hom)
  calc
    (Subobject.map g.hom).obj x ⊓ (Subobject.mk g.hom ⊓ D.filtration i)
        = ((Subobject.map g.hom).obj x ⊓ Subobject.mk g.hom) ⊓ D.filtration i := by
            simp [inf_assoc]
    _ = (Subobject.map g.hom).obj x ⊓ D.filtration i := by
            simp [inf_eq_left.mpr hx]

private theorem quotient_comp_eq_quotient_of_quotient [Balanced C] (f : A ⟶ B) (g : B ⟶ D)
    (i : ℤ) : A.filtration.quotient (f.hom ≫ g.hom) i =
      (A.filtration.quotient f.hom).quotient g.hom i := by
  rw [DecreasingFiltration.quotient_eq_imageSubobject_comp,
    DecreasingFiltration.quotient_eq_imageSubobject_comp]
  rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
  simpa [Category.assoc] using
    (CategoryTheory.Limits.imageSubobject_comp_eq_imageSubobject_restriction
      ((A.filtration i).arrow ≫ f.hom) g.hom)

-- Proof sketch: strictness of `f` identifies `g (f(F^p A))` with
-- `g (f(A) ∩ F^p B)`; injectivity of `g.hom` turns this into the intersection of the image of the
-- composite with `g(F^p B)`, and strictness of `g` rewrites `g(F^p B)` as `F^p C ∩ image g`.
/-- Lemma 12.19.8 (2): if `g` is injective, then the composite `g ∘ f` of strict morphisms of
filtered objects is strict. -/
theorem strict_comp_of_mono [Balanced C] (f : A ⟶ B) (g : B ⟶ D) [Mono g.hom]
    (hf : Strict f) (hg : Strict g) :
    Strict (f ≫ g) := by
  refine (strict_iff_quotient_eq_inf (f ≫ g)).2 ?_
  intro i
  calc
    A.filtration.quotient (f.hom ≫ g.hom) i
        = imageSubobject ((A.filtration i).arrow ≫ f.hom ≫ g.hom) := by
            rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    _ = (Subobject.map g.hom).obj (imageSubobject ((A.filtration i).arrow ≫ f.hom)) := by
            simpa [Category.assoc] using
              (imageSubobject_comp_eq_map_of_mono ((A.filtration i).arrow ≫ f.hom) g.hom)
    _ = (Subobject.map g.hom).obj (A.filtration.quotient f.hom i) := by
            rw [DecreasingFiltration.quotient_eq_imageSubobject_comp]
    _ = (Subobject.map g.hom).obj (imageSubobject f.hom ⊓ B.filtration i) := by
            rw [(strict_iff_quotient_eq_inf f).1 hf i]
    _ = (Subobject.map g.hom).obj (imageSubobject f.hom) ⊓ D.filtration i := by
            simpa using map_inf_eq_of_strict_mono g hg (imageSubobject f.hom) i
    _ = imageSubobject (f.hom ≫ g.hom) ⊓ D.filtration i := by
            rw [← imageSubobject_comp_eq_map_of_mono f.hom g.hom]

-- Proof sketch: rewrite the preimage of `F^p C` under `g ∘ f` as the preimage under `f` of
-- `F^p B + ker g` using strictness of `g`; surjectivity of `f.hom` lets the pullback of this sum
-- split as the sum of the pullbacks, and strictness of `f` identifies the pullback of `F^p B`
-- with `F^p A + ker f`, which collapses to `F^p A + ker (g ≫ f)`.
/-- Lemma 12.19.8 (3): if `f` is surjective, then the composite `g ∘ f` of strict morphisms of
filtered objects is strict. -/
theorem strict_comp_of_epi [Balanced C] (f : A ⟶ B) (g : B ⟶ D) [Epi f.hom]
    (hf : Strict f) (hg : Strict g) :
    Strict (f ≫ g) := by
  refine (strict_iff_quotient_eq_inf (f ≫ g)).2 ?_
  intro i
  calc
    A.filtration.quotient (f.hom ≫ g.hom) i
        = (A.filtration.quotient f.hom).quotient g.hom i :=
            quotient_comp_eq_quotient_of_quotient f g i
    _ = B.filtration.quotient g.hom i := by
          have hfi : A.filtration.quotient f.hom = B.filtration := by
            simpa using ((strict_iff_quotient_filtration_of_epi f).1 hf).symm
          rw [hfi]
    _ = imageSubobject g.hom ⊓ D.filtration i := by
          exact (strict_iff_quotient_eq_inf g).1 hg i
    _ = imageSubobject (f.hom ≫ g.hom) ⊓ D.filtration i := by
          rw [imageSubobject_comp_eq_of_epi f.hom g.hom]

end FilteredObject.Hom
end CategoryTheory
