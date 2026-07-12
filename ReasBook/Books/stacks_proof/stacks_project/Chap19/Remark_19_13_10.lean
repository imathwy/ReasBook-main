import Mathlib
import StacksProject_2024.Chap12.Lemma_12_19_12
import StacksProject_2024.Chap12.Lemma_12_24_2
import StacksProject_2024.Chap12.Lemma_12_24_13
import StacksProject_2024.Chap12.Definition_12_24_5
import StacksProject_2024.Chap12.Definition_12_24_9
import StacksProject_2024.Chap19.Lemma_19_12_3
import StacksProject_2024.Chap19.Lemma_19_13_12
import StacksProject_2024.Chap19.Remark_19_13_8
import StacksProject_2024.Chap19.Theorem_19_12_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open FilteredComplex
open ComplexShape
open CochainComplex.HomComplex.CohomologyClass
open DerivedCategory HomotopyCategory

noncomputable section

universe w v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [LocallySmall 𝒜] [WellPowered 𝒜]
  [HasWidePullbacks 𝒜] [HasCoproducts 𝒜] [InitialMonoClass 𝒜] [IsGrothendieckAbelian.{w} 𝒜]
  [HasDerivedCategory 𝒜]

local notation "FilteredComplex" => CategoryTheory.FilteredComplex 𝒜
local notation "AbFilteredComplex" => CategoryTheory.FilteredComplex AddCommGrpCat

/-- Helper for Remark 19.13.10: precomposition with a cochain-complex morphism induces a chain map
between Hom complexes. -/
private noncomputable def homComplexPrecomp
    {L M I : CochainComplex 𝒜 ℤ} (f : L ⟶ M) :
    CochainComplex.HomComplex M I ⟶ CochainComplex.HomComplex L I where
  f n :=
    AddCommGrpCat.ofHom <|
      AddMonoidHom.mk'
        (fun z ↦ (CochainComplex.HomComplex.Cochain.ofHom f).comp z (zero_add n))
        (by
          intro z z'
          ext p q hpq
          -- Proof comment: precomposition is bilinear because composition in the ambient
          -- preadditive category is bilinear.
          simp [Preadditive.add_comp])
  comm' := by
    intro i j hij
    ext z
    -- Proof comment: the Hom-complex differential commutes with precomposition.
    simpa using
      (CochainComplex.HomComplex.δ_ofHom_comp (f := f) (z := z) (m := j))

/-- Helper for Remark 19.13.10: Hom-complex precomposition is functorial under composition of the
source map. -/
private theorem homComplexPrecomp_comp
    {L M N I : CochainComplex 𝒜 ℤ} (f : L ⟶ M) (g : M ⟶ N) :
    homComplexPrecomp (f := f ≫ g) (I := I) =
      homComplexPrecomp (f := g) (I := I) ≫ homComplexPrecomp (f := f) (I := I) := by
  ext n z
  -- Proof comment: both sides are iterated precomposition, so associativity of cochain
  -- composition reduces the equality to associativity in `𝒜`.
  rfl

/-- Helper for Remark 19.13.10: precomposition by the identity source map is the identity on the
Hom complex. -/
private theorem homComplexPrecomp_id
    {L I : CochainComplex 𝒜 ℤ} :
    homComplexPrecomp (f := 𝟙 L) (I := I) = 𝟙 (CochainComplex.HomComplex L I) := by
  ext n z
  -- Proof comment: precomposing by the identity leaves each cochain component unchanged.
  rfl

/-- Helper for Remark 19.13.10: transport of morphisms along source and target isomorphisms is
additive in any preadditive category. -/
private theorem isoHomCongr_map_add
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
    (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  -- Proof comment: `Iso.homCongr` is composition with the isomorphism legs, so additivity is
  -- bilinearity of composition in the ambient preadditive category.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Remark 19.13.10: isomorphisms on source and target induce an additive equivalence
on the corresponding Hom groups. -/
private noncomputable def isoHomCongrAddEquiv
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) where
  toEquiv := α.homCongr β
  map_add' := isoHomCongr_map_add α β

/-- Helper for Remark 19.13.10: the quotient complex `M^• / F^p M^•` obtained by applying the
filtered-object quotient functor degreewise. -/
noncomputable abbrev FilteredComplex.quotient (M : FilteredComplex) (p : ℤ) :
    CochainComplex 𝒜 ℤ :=
  ((FilteredObject.quotientFunctor p).mapHomologicalComplex (ComplexShape.up ℤ)).obj M

/-- Helper for Remark 19.13.10: the canonical quotient map from the underlying complex to the
stagewise quotient complex `M^• / F^p M^•`. -/
noncomputable def FilteredComplex.underlyingToQuotient (M : FilteredComplex) (p : ℤ) :
    M.underlying ⟶ M.quotient p where
  f n := cokernel.π ((M.X n).filtration.obj p).arrow
  comm' := by
    intro i j hij
    -- Proof comment: each differential is a filtered morphism, so the quotient projections are
    -- natural with respect to the induced map on quotients.
    exact FilteredObject.Hom.quotientMap_comm (M.d i j) p

/-- Helper for Remark 19.13.10: quotient maps are natural with respect to lowering the
filtration index. -/
private theorem quotientMapOfLE_naturality
    {A B : FilteredObject 𝒜} (f : A ⟶ B) {p q : ℤ} (hpq : p ≤ q) :
    FilteredObject.Hom.quotientMap f q ≫ subobjectQuotientMap (B.filtration.antitone_obj hpq) =
      subobjectQuotientMap (A.filtration.antitone_obj hpq) ≫
        FilteredObject.Hom.quotientMap f p := by
  -- Proof comment: compare both composites after precomposing with the quotient projection
  -- `B ⟶ B / F^q B`; both sides collapse to the quotient map for filtration stage `p`.
  refine (cancel_epi (cokernel.π (A.filtration.obj q).arrow)).1 ?_
  calc
    cokernel.π (A.filtration.obj q).arrow ≫ FilteredObject.Hom.quotientMap f q ≫
        subobjectQuotientMap (B.filtration.antitone_obj hpq)
        = f.hom ≫ cokernel.π (B.filtration.obj q).arrow ≫
            subobjectQuotientMap (B.filtration.antitone_obj hpq) := by
              simp [FilteredObject.Hom.quotientMap_comm, Category.assoc]
    _ = f.hom ≫ cokernel.π (B.filtration.obj p).arrow := by
          simp [subobjectQuotientMap, Category.assoc]
    _ = cokernel.π (A.filtration.obj p).arrow ≫ FilteredObject.Hom.quotientMap f p := by
          simpa [Category.assoc] using (FilteredObject.Hom.quotientMap_comm (f := f) p).symm
    _ = (cokernel.π (A.filtration.obj q).arrow ≫
          subobjectQuotientMap (A.filtration.antitone_obj hpq)) ≫
            FilteredObject.Hom.quotientMap f p := by
          simp [subobjectQuotientMap, Category.assoc]
    _ = cokernel.π (A.filtration.obj q).arrow ≫
          (subobjectQuotientMap (A.filtration.antitone_obj hpq) ≫
            FilteredObject.Hom.quotientMap f p) := by
          simp [Category.assoc]

/-- Helper for Remark 19.13.10: the canonical transition map
`M^• / F^q M^• ⟶ M^• / F^p M^•` for `p ≤ q`. -/
noncomputable def FilteredComplex.quotientMapOfLE (M : FilteredComplex) {p q : ℤ}
    (hpq : p ≤ q) : M.quotient q ⟶ M.quotient p where
  f n := subobjectQuotientMap ((M.X n).filtration.antitone_obj hpq)
  comm' := by
    intro i j hij
    -- Proof comment: the quotient transition is degreewise `subobjectQuotientMap`, and the
    -- differentials are filtered morphisms, so naturality reduces to the filtered-object lemma
    -- above.
    simpa [FilteredComplex.quotient] using
      (quotientMapOfLE_naturality (f := M.d i j) hpq).symm

/-- Helper for Remark 19.13.10: the quotient map from `M^•` to `M^• / F^p M^•` factors through
the canonical transition `M^• / F^q M^• ⟶ M^• / F^p M^•` when `p ≤ q`. -/
private theorem underlyingToQuotient_comp_quotientMapOfLE
    (M : FilteredComplex) {p q : ℤ} (hpq : p ≤ q) :
    M.underlyingToQuotient q ≫ M.quotientMapOfLE hpq = M.underlyingToQuotient p := by
  ext n
  -- Proof comment: both composites are the canonical quotient map from `M.X n` to the quotient
  -- by `F^p(M.X n)`, and this is detected by the universal property of cokernels.
  simp [FilteredComplex.underlyingToQuotient, FilteredComplex.quotientMapOfLE, subobjectQuotientMap]

/-- Helper for Remark 19.13.10: the quotient-transition map is the identity when the filtration
index does not change. -/
private theorem quotientMapOfLE_refl
    (M : FilteredComplex) (p : ℤ) :
    M.quotientMapOfLE (show p ≤ p by rfl) = 𝟙 (M.quotient p) := by
  ext n
  -- Proof comment: the reflexive filtration comparison gives the identity subobject quotient map
  -- in every degree.
  simp [FilteredComplex.quotientMapOfLE, subobjectQuotientMap]

/-- Helper for Remark 19.13.10: quotient-transition maps compose exactly along the filtration
order. -/
private theorem quotientMapOfLE_comp
    (M : FilteredComplex) {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    M.quotientMapOfLE hqr ≫ M.quotientMapOfLE hpq =
      M.quotientMapOfLE (le_trans hpq hqr) := by
  ext n
  -- Proof comment: degreewise, every composite is the canonical quotient map induced by the
  -- composite inclusion `F^r(M^n) ≤ F^q(M^n) ≤ F^p(M^n)`.
  simp [FilteredComplex.quotientMapOfLE, subobjectQuotientMap, Category.assoc]

/-- Helper for Remark 19.13.10: the quotient tower of the filtered source complex acts on Hom
complexes by precomposition. -/
private noncomputable def sourceQuotientHomTransition
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) {p q : ℤ} (hpq : p ≤ q) :
    CochainComplex.HomComplex (M.quotient p) I ⟶
      CochainComplex.HomComplex (M.quotient q) I :=
  homComplexPrecomp (f := M.quotientMapOfLE hpq) (I := I)

/-- Helper for Remark 19.13.10: the quotient-Hom transition is the identity when the quotient
index does not change. -/
private theorem sourceQuotientHomTransition_refl
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) (p : ℤ) :
    sourceQuotientHomTransition M I (show p ≤ p by rfl) =
      𝟙 (CochainComplex.HomComplex (M.quotient p) I) := by
  -- Proof comment: this is precomposition by the identity quotient map.
  simp [sourceQuotientHomTransition, quotientMapOfLE_refl, homComplexPrecomp_id]

/-- Helper for Remark 19.13.10: the quotient-Hom transitions compose along the quotient tower. -/
private theorem sourceQuotientHomTransition_comp
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) {p q r : ℤ}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    sourceQuotientHomTransition M I hpq ≫ sourceQuotientHomTransition M I hqr =
      sourceQuotientHomTransition M I (le_trans hpq hqr) := by
  -- Proof comment: both sides are precomposition by the same composite quotient map.
  rw [sourceQuotientHomTransition, sourceQuotientHomTransition, sourceQuotientHomTransition,
    ← homComplexPrecomp_comp, quotientMapOfLE_comp]

/-- Helper for Remark 19.13.10: the quotient-Hom stages form the inverse system that will be
realized as the filtered Hom complex in `D(AddCommGrpCat)`. -/
private noncomputable def sourceQuotientHomTower
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) :
    ℤᵒᵖ ⥤ DerivedCategory AddCommGrpCat where
  obj p :=
    DerivedCategory.Q.obj <| CochainComplex.HomComplex (M.quotient (-p.unop + 1)) I
  map {p q} f :=
    -- Proof comment: a morphism `op p ⟶ op q` means `q ≤ p`, so the quotient indices satisfy
    -- `-p + 1 ≤ -q + 1`, exactly the direction needed for contravariant precomposition.
    DerivedCategory.Q.map <|
      sourceQuotientHomTransition M I (by omega : -p.unop + 1 ≤ -q.unop + 1)
  map_id p := by
    -- Proof comment: the reflexive quotient transition is the identity, so the derived map is
    -- also the identity.
    simpa using
      congrArg DerivedCategory.Q.map
        (sourceQuotientHomTransition_refl M I (-p.unop + 1))
  map_comp {p q r} f g := by
    -- Proof comment: functoriality is exactly the composition law for the quotient-Hom
    -- transitions, transported through `DerivedCategory.Q`.
    rw [← DerivedCategory.Q.map_comp]
    simpa using
      congrArg DerivedCategory.Q.map <|
        sourceQuotientHomTransition_comp M I
          (by omega : -p.unop + 1 ≤ -q.unop + 1)
          (by omega : -q.unop + 1 ≤ -r.unop + 1)

/-- Helper for Remark 19.13.10: the underlying Hom complex is the cocone point of the explicit
quotient-Hom inverse system. -/
private noncomputable def sourceQuotientHomTowerCocone
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) :
    Cocone (sourceQuotientHomTower M I) where
  pt := DerivedCategory.Q.obj (CochainComplex.HomComplex M.underlying I)
  ι :=
    { app := fun p ↦
        DerivedCategory.Q.map (homComplexPrecomp (f := M.underlyingToQuotient (-p.unop + 1))
          (I := I))
      naturality := by
        intro p q f
        -- Proof comment: both composites are precomposition by the quotient map from
        -- `M.underlying` to `M.quotient (-q + 1)`, and the factorization is the quotient-tower
        -- identity `underlyingToQuotient_comp_quotientMapOfLE`.
        rw [← DerivedCategory.Q.map_comp]
        rw [sourceQuotientHomTransition, ← homComplexPrecomp_comp]
        simpa using
          congrArg (fun k ↦ DerivedCategory.Q.map (homComplexPrecomp (f := k) (I := I))) <|
            underlyingToQuotient_comp_quotientMapOfLE M
              (by omega : -p.unop + 1 ≤ -q.unop + 1) }

-- Proof sketch: composition in the derived category is additive in the second factor, so
-- precomposition with `f` defines an additive homomorphism on morphism groups.
/-- Precomposition with a morphism in the first variable is additive on derived `Ext` groups. -/
theorem derivedExtGroupPrecomp_add
    (K : DerivedCategory 𝒜) {X Y : DerivedCategory 𝒜} (f : X ⟶ Y) (n : ℤ)
    (α β : Y ⟶ K⟦n⟧) :
    f ≫ (α + β) = f ≫ α + f ≫ β := by
  -- Proof comment: `DerivedCategory 𝒜` is preadditive, so left composition distributes over
  -- addition on Hom-groups.
  simpa using comp_add f α β

/-- The map on derived `Ext` groups induced contravariantly by a morphism in the first variable.
-/
def derivedExtGroupPrecomp
    (K : DerivedCategory 𝒜) {X Y : DerivedCategory 𝒜} (f : X ⟶ Y) (n : ℤ) :
    derivedExtGroup Y K n ⟶ derivedExtGroup X K n :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk'
      (fun α ↦ f ≫ α)
      (derivedExtGroupPrecomp_add K f n)

/-- Helper for Remark 19.13.10: if `I` is K-injective, then the degree-`n` cohomology of the
Hom complex `Hom^•(L, I)` computes the derived `Ext` group from `L` to `Q.obj I`. -/
private noncomputable def homComplexHomologyAddEquivDerivedExt
    (L I : CochainComplex 𝒜 ℤ) [I.IsKInjective] (n : ℤ) :
    ((CochainComplex.HomComplex L I).homology n) ≃+
      ↑(derivedExtGroup (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I) n) :=
  let KQ := HomotopyCategory.quotient 𝒜 (up ℤ)
  let KL := KQ.obj L
  let e₀ :
      (CochainComplex.HomComplex L I).homology n ≃+
        (KL ⟶ KQ.obj (I⟦n⟧)) :=
    -- Proof comment: the canonical Hom-complex cohomology bridge lands in the homotopy category.
    (CochainComplex.HomComplex.homologyAddEquiv L I n).trans homAddEquiv
  let e₁ :
      (KL ⟶ KQ.obj (I⟦n⟧)) ≃+
        (DerivedCategory.Qh.obj KL ⟶ DerivedCategory.Qh.obj (KQ.obj (I⟦n⟧))) :=
    -- Proof comment: K-injectivity of `I⟦n⟧` identifies homotopy morphisms with derived
    -- morphisms after localization.
    AddEquiv.ofBijective
      (DerivedCategory.Qh.mapAddHom :
        (KL ⟶ KQ.obj (I⟦n⟧)) →+
          (DerivedCategory.Qh.obj KL ⟶ DerivedCategory.Qh.obj (KQ.obj (I⟦n⟧))))
      (CochainComplex.IsKInjective.Qh_map_bijective KL (I⟦n⟧))
  let e₂ :
      (DerivedCategory.Qh.obj KL ⟶ DerivedCategory.Qh.obj (KQ.obj (I⟦n⟧))) ≃+
        ((DerivedCategory.Q.obj L : DerivedCategory 𝒜) ⟶
          (DerivedCategory.Q.obj (I⟦n⟧) : DerivedCategory 𝒜)) :=
    -- Proof comment: `quotientCompQhIso` removes the intermediate homotopy-category quotient.
    isoHomCongrAddEquiv
      ((DerivedCategory.quotientCompQhIso 𝒜).app L)
      ((DerivedCategory.quotientCompQhIso 𝒜).app (I⟦n⟧))
  let e₃ :
      ((DerivedCategory.Q.obj L : DerivedCategory 𝒜) ⟶
          (DerivedCategory.Q.obj (I⟦n⟧) : DerivedCategory 𝒜)) ≃+
        ↑(derivedExtGroup (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I) n) :=
    -- Proof comment: commute the shift through `Q` to read the target as `Ext^n`.
    isoHomCongrAddEquiv (Iso.refl _) ((DerivedCategory.Q.commShiftIso n).app I)
  e₀.trans (e₁.trans (e₂.trans e₃))

/-- Helper for Remark 19.13.10: the K-injective Hom-complex comparison above packaged as an
isomorphism in `AddCommGrpCat`. -/
private noncomputable def homComplexHomologyIsoDerivedExt
    (L I : CochainComplex 𝒜 ℤ) [I.IsKInjective] (n : ℤ) :
    AddCommGrpCat.of ((CochainComplex.HomComplex L I).homology n) ≅
      derivedExtGroup (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj I) n :=
  (homComplexHomologyAddEquivDerivedExt L I n).toAddCommGrpIso

/-- Helper for Remark 19.13.10: an isomorphism on the target variable transports derived `Ext`
groups functorially. -/
private noncomputable def derivedExtGroupIsoOfTargetIso
    (L : DerivedCategory 𝒜) {X Y : DerivedCategory 𝒜} (e : X ≅ Y) (n : ℤ) :
    derivedExtGroup L X n ≅ derivedExtGroup L Y n :=
  -- Proof comment: `Ext^n(L,-)` is represented by morphisms into the shifted target, so an
  -- isomorphism `X ≅ Y` transports directly after applying the shift functor.
  (isoHomCongrAddEquiv (Iso.refl _) ((shiftFunctor (DerivedCategory 𝒜) n).mapIso e)).toAddCommGrpIso

/-- Helper for Remark 19.13.10: a realization witness identifies the derived object of the
underlying complex with the point of the realized inverse-system cocone. -/
private noncomputable def realizesInverseSystemPointIso
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    {system : ℤᵒᵖ ⥤ DerivedCategory B} (F : CategoryTheory.FilteredComplex B) (c : Cocone system)
    (hF : FilteredComplex.RealizesInverseSystem F c) : DerivedCategory.Q.obj F.underlying ≅ c.pt := by
  rcases hF with ⟨_, coconeHom, hIso⟩
  letI : IsIso coconeHom := hIso
  -- Proof comment: the point component of the realizing cocone comparison is already an
  -- isomorphism.
  exact asIso coconeHom.hom

/-- Helper for Remark 19.13.10: a realization witness identifies each stage of the realized
filtered complex with the prescribed inverse-system value. -/
private noncomputable def realizesInverseSystemStageIso
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    {system : ℤᵒᵖ ⥤ DerivedCategory B} (F : CategoryTheory.FilteredComplex B) (c : Cocone system)
    (hF : FilteredComplex.RealizesInverseSystem F c) (p : ℤ) :
    DerivedCategory.Q.obj (F.stage p) ≅ system.obj (Opposite.op p) := by
  rcases hF with ⟨stageIso, _, _⟩
  -- Proof comment: the stage comparison is the `op p` component of the realizing natural
  -- isomorphism.
  exact stageIso.app (Opposite.op p)

/-- Helper for Remark 19.13.10: the derived-category homology of a represented complex is the
ordinary homology of that representative. -/
private noncomputable def qObjHomologyIso
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (L : CochainComplex B ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctor B n).obj (DerivedCategory.Q.obj L) ≅ L.homology n :=
  ((DerivedCategory.homologyFunctorFactors B n).app L).symm

/-- Helper for Remark 19.13.10: the realized filtered Hom complex has the expected abutment
cohomology `Ext^n(M, K)`. -/
private noncomputable def underlyingHomologyIsoDerivedExt
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) [I.IsKInjective]
    (K : DerivedCategory 𝒜) (eK : DerivedCategory.Q.obj I ≅ K)
    (F : AbFilteredComplex) (hF : F.RealizesInverseSystem (sourceQuotientHomTowerCocone M I))
    (n : ℤ) :
    F.underlying.homology n ≅
      derivedExtGroup (DerivedCategory.Q.obj M.underlying) K n := by
  -- Proof comment: pass from ordinary homology of `F.underlying` to derived homology of
  -- `Q.obj F.underlying`, transport along the realization isomorphism, then compute derived
  -- homology on the concrete Hom complex.
  refine ((DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app F.underlying) ≪≫ ?_
  refine (DerivedCategory.homologyFunctor AddCommGrpCat n).mapIso
      (realizesInverseSystemPointIso F (sourceQuotientHomTowerCocone M I) hF) ≪≫ ?_
  simpa [sourceQuotientHomTowerCocone] using
    (qObjHomologyIso (L := CochainComplex.HomComplex M.underlying I) n ≪≫
      homComplexHomologyIsoDerivedExt M.underlying I n ≪≫
      derivedExtGroupIsoOfTargetIso (DerivedCategory.Q.obj M.underlying) eK n)

/-- Helper for Remark 19.13.10: each realized stage computes the corresponding quotient-Ext
group. -/
private noncomputable def stageHomologyIsoQuotientDerivedExt
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) [I.IsKInjective]
    (K : DerivedCategory 𝒜) (eK : DerivedCategory.Q.obj I ≅ K)
    (F : AbFilteredComplex) (hF : F.RealizesInverseSystem (sourceQuotientHomTowerCocone M I))
    (p n : ℤ) :
    (F.stage p).homology n ≅
      derivedExtGroup (DerivedCategory.Q.obj (M.quotient (-p + 1))) K n := by
  -- Proof comment: the `p`-th stage of the realization represents the quotient-Hom complex for
  -- `M / F^(-p + 1) M`, so the same derived-homology transport computes its `Ext` group.
  refine ((DerivedCategory.homologyFunctorFactors AddCommGrpCat n).app (F.stage p)) ≪≫ ?_
  refine (DerivedCategory.homologyFunctor AddCommGrpCat n).mapIso
      (realizesInverseSystemStageIso F (sourceQuotientHomTowerCocone M I) hF p) ≪≫ ?_
  simpa [sourceQuotientHomTower] using
    (qObjHomologyIso (L := CochainComplex.HomComplex (M.quotient (-p + 1)) I) n ≪≫
      homComplexHomologyIsoDerivedExt (M.quotient (-p + 1)) I n ≪≫
      derivedExtGroupIsoOfTargetIso
        (DerivedCategory.Q.obj (M.quotient (-p + 1))) eK n)

/-- Helper for Remark 19.13.10: every graded piece of a filtered complex is the cokernel of the
successor stage map. -/
private noncomputable def filteredComplexGradedPieceCokernelIso
    (F : FilteredComplex) (p : ℤ) :
    F.gradedPiece p ≅ cokernel (F.stageMapOfLE (lt_add_one p).le) := by
  -- Proof comment: for filtered cochain complexes, `gr^p` is definitionally the cokernel of the
  -- map `F^(p + 1) ⟶ F^p`.
  exact eqToIso rfl

/-- Helper for Remark 19.13.10: the stagewise quotient map
`M^n / F^q M^n ⟶ M^n / F^p M^n` is epic whenever `p ≤ q`. -/
private theorem quotientMapOfLE_epi
    (M : FilteredComplex) {p q n : ℤ} (hpq : p ≤ q) :
    Epi ((M.quotientMapOfLE hpq).f n) := by
  -- Proof comment: degreewise this is the canonical quotient map induced by an inclusion of
  -- subobjects, hence an epimorphism.
  simpa [FilteredComplex.quotientMapOfLE] using
    (inferInstance : Epi (subobjectQuotientMap ((M.X n).filtration.antitone_obj hpq)))

/-- Helper for Remark 19.13.10: a morphism into the target of an epimorphism lifts after
refining the source by an epimorphism. -/
private theorem existsRefinementLiftOfEpi
    {X Y A : 𝒜} (e : X ⟶ Y) [Epi e] (y : A ⟶ Y) :
    ∃ (A' : 𝒜) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ e := by
  -- Proof comment: realize the desired lift on the pullback of `e` along `y`.
  refine ⟨pullback e y, pullback.snd e y, inferInstance, pullback.fst e y, ?_⟩
  simpa using (pullback.condition (f := e) (g := y)).symm

/-- Helper for Remark 19.13.10: the object-level transition
`X / F^(p + 1) X ⟶ X / F^p X`. -/
private noncomputable def filteredObjectQuotientTransition
    (X : FilteredObject 𝒜) (p : ℤ) :
    cokernel (X.filtration.obj (p + 1)).arrow ⟶ cokernel (X.filtration.obj p).arrow :=
  cokernel.desc (X.filtration.obj (p + 1)).arrow
    (cokernel.π (X.filtration.obj p).arrow)
    (by
      -- Proof comment: the quotient by `F^p X` already kills the smaller stage `F^(p + 1) X`.
      have hstageArrow :
          X.filtration.stageInclusion p ≫ (X.filtration.obj p).arrow =
            (X.filtration.obj (p + 1)).arrow := by
        exact Subobject.ofLE_arrow (X.filtration.succ_le p)
      rw [← hstageArrow, Category.assoc, cokernel.condition]
      simp)

/-- Helper for Remark 19.13.10: the object-level quotient transition is induced by the ambient
quotient projection. -/
private theorem filteredObjectQuotientTransition_comm
    (X : FilteredObject 𝒜) (p : ℤ) :
    cokernel.π (X.filtration.obj (p + 1)).arrow ≫ filteredObjectQuotientTransition X p =
      cokernel.π (X.filtration.obj p).arrow := by
  -- Proof comment: this is the defining equation of `cokernel.desc`.
  simp [filteredObjectQuotientTransition]

/-- Helper for Remark 19.13.10: the object-level quotient transition is epic. -/
private theorem filteredObjectQuotientTransition_epi
    (X : FilteredObject 𝒜) (p : ℤ) :
    Epi (filteredObjectQuotientTransition X p) := by
  -- Proof comment: the ambient quotient projection to `X / F^p X` factors through this map.
  exact epi_of_epi_fac (filteredObjectQuotientTransition_comm X p)

/-- Helper for Remark 19.13.10: the object-level graded piece maps canonically to the next
quotient `X / F^(p + 1) X`. -/
private noncomputable def filteredObjectGradedToQuotientSucc
    (X : FilteredObject 𝒜) (p : ℤ) :
    gr^{p} X ⟶ cokernel (X.filtration.obj (p + 1)).arrow :=
  cokernel.desc (X.filtration.stageInclusion p)
    ((X.filtration.obj p).arrow ≫ cokernel.π (X.filtration.obj (p + 1)).arrow)
    (by
      -- Proof comment: the quotient by `F^(p + 1) X` kills the image of the stage inclusion.
      simp [DecreasingFiltration.stageInclusion, Category.assoc])

/-- Helper for Remark 19.13.10: the graded-to-quotient map is induced from the ambient stage
inclusion. -/
private theorem filteredObjectGradedToQuotientSucc_comm
    (X : FilteredObject 𝒜) (p : ℤ) :
    cokernel.π (X.filtration.stageInclusion p) ≫ filteredObjectGradedToQuotientSucc X p =
      (X.filtration.obj p).arrow ≫ cokernel.π (X.filtration.obj (p + 1)).arrow := by
  -- Proof comment: this is the defining computation rule for the descended map.
  simp [filteredObjectGradedToQuotientSucc]

/-- Helper for Remark 19.13.10: the object-level quotient transitions are natural in filtered
morphisms. -/
private theorem filteredObjectQuotientTransition_naturality
    {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    FilteredObject.Hom.quotientMap f (p + 1) ≫ filteredObjectQuotientTransition B p =
      filteredObjectQuotientTransition A p ≫ FilteredObject.Hom.quotientMap f p := by
  -- Proof comment: compare both composites after precomposing with the quotient projection from
  -- `A / F^(p + 1) A`.
  refine (cancel_epi (cokernel.π (A.filtration.obj (p + 1)).arrow)).1 ?_
  calc
    cokernel.π (A.filtration.obj (p + 1)).arrow ≫
        FilteredObject.Hom.quotientMap f (p + 1) ≫ filteredObjectQuotientTransition B p
        =
      (cokernel.π (A.filtration.obj (p + 1)).arrow ≫
          FilteredObject.Hom.quotientMap f (p + 1)) ≫
        filteredObjectQuotientTransition B p := by
          simp [Category.assoc]
    _ = (f.hom ≫ cokernel.π (B.filtration.obj (p + 1)).arrow) ≫
          filteredObjectQuotientTransition B p := by
          rw [FilteredObject.Hom.quotientMap_comm]
    _ = f.hom ≫ cokernel.π (B.filtration.obj (p + 1)).arrow ≫
          filteredObjectQuotientTransition B p := by
          simp [Category.assoc]
    _ = f.hom ≫ cokernel.π (B.filtration.obj p).arrow := by
          rw [filteredObjectQuotientTransition_comm]
    _ = cokernel.π (A.filtration.obj p).arrow ≫ FilteredObject.Hom.quotientMap f p := by
          rw [FilteredObject.Hom.quotientMap_comm]
    _ = cokernel.π (A.filtration.obj (p + 1)).arrow ≫
          (filteredObjectQuotientTransition A p ≫ FilteredObject.Hom.quotientMap f p) := by
          calc
            cokernel.π (A.filtration.obj p).arrow ≫ FilteredObject.Hom.quotientMap f p
                =
              (cokernel.π (A.filtration.obj (p + 1)).arrow ≫
                  filteredObjectQuotientTransition A p) ≫
                FilteredObject.Hom.quotientMap f p := by
                  rw [filteredObjectQuotientTransition_comm]
            _ = cokernel.π (A.filtration.obj (p + 1)).arrow ≫
                  (filteredObjectQuotientTransition A p ≫
                    FilteredObject.Hom.quotientMap f p) := by
                  simp [Category.assoc]

/-- Helper for Remark 19.13.10: the object-level graded-to-quotient maps are natural in filtered
morphisms. -/
private theorem filteredObjectGradedToQuotientSucc_naturality
    {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    FilteredObject.Hom.gradedPieceMap f p ≫ filteredObjectGradedToQuotientSucc B p =
      filteredObjectGradedToQuotientSucc A p ≫ FilteredObject.Hom.quotientMap f (p + 1) := by
  -- Proof comment: compare both composites after precomposing with the source graded-piece
  -- projection.
  refine (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 ?_
  calc
    cokernel.π (A.filtration.stageInclusion p) ≫
        FilteredObject.Hom.gradedPieceMap f p ≫ filteredObjectGradedToQuotientSucc B p
        =
      FilteredObject.Hom.stageMap f p ≫ cokernel.π (B.filtration.stageInclusion p) ≫
        filteredObjectGradedToQuotientSucc B p := by
          simp [FilteredObject.Hom.gradedPieceMap, Category.assoc]
    _ = FilteredObject.Hom.stageMap f p ≫ (B.filtration.obj p).arrow ≫
          cokernel.π (B.filtration.obj (p + 1)).arrow := by
          rw [filteredObjectGradedToQuotientSucc_comm]
    _ = (A.filtration.obj p).arrow ≫ f.hom ≫ cokernel.π (B.filtration.obj (p + 1)).arrow := by
          calc
            FilteredObject.Hom.stageMap f p ≫ (B.filtration.obj p).arrow ≫
                cokernel.π (B.filtration.obj (p + 1)).arrow
                =
              (FilteredObject.Hom.stageMap f p ≫ (B.filtration.obj p).arrow) ≫
                cokernel.π (B.filtration.obj (p + 1)).arrow := by
                  simp [Category.assoc]
            _ = ((A.filtration.obj p).arrow ≫ f.hom) ≫
                  cokernel.π (B.filtration.obj (p + 1)).arrow := by
                    rw [FilteredObject.Hom.stageMap_comm]
            _ = (A.filtration.obj p).arrow ≫ f.hom ≫
                  cokernel.π (B.filtration.obj (p + 1)).arrow := by
                    simp [Category.assoc]
    _ = (A.filtration.obj p).arrow ≫ cokernel.π (A.filtration.obj (p + 1)).arrow ≫
          FilteredObject.Hom.quotientMap f (p + 1) := by
          calc
            (A.filtration.obj p).arrow ≫ f.hom ≫ cokernel.π (B.filtration.obj (p + 1)).arrow
                =
              (A.filtration.obj p).arrow ≫
                (f.hom ≫ cokernel.π (B.filtration.obj (p + 1)).arrow) := by
                  simp [Category.assoc]
            _ = (A.filtration.obj p).arrow ≫
                  (cokernel.π (A.filtration.obj (p + 1)).arrow ≫
                    FilteredObject.Hom.quotientMap f (p + 1)) := by
                    rw [FilteredObject.Hom.quotientMap_comm]
            _ = (A.filtration.obj p).arrow ≫ cokernel.π (A.filtration.obj (p + 1)).arrow ≫
                  FilteredObject.Hom.quotientMap f (p + 1) := by
                    simp [Category.assoc]
    _ = cokernel.π (A.filtration.stageInclusion p) ≫
          filteredObjectGradedToQuotientSucc A p ≫
            FilteredObject.Hom.quotientMap f (p + 1) := by
          calc
            (A.filtration.obj p).arrow ≫ cokernel.π (A.filtration.obj (p + 1)).arrow ≫
                FilteredObject.Hom.quotientMap f (p + 1)
                =
              (cokernel.π (A.filtration.stageInclusion p) ≫
                  filteredObjectGradedToQuotientSucc A p) ≫
                FilteredObject.Hom.quotientMap f (p + 1) := by
                  rw [filteredObjectGradedToQuotientSucc_comm]
                  simp [Category.assoc]
            _ = cokernel.π (A.filtration.stageInclusion p) ≫
                  filteredObjectGradedToQuotientSucc A p ≫
                    FilteredObject.Hom.quotientMap f (p + 1) := by
                    simp [Category.assoc]

/-- Helper for Remark 19.13.10: the object-level quotient row
`gr^p X ⟶ X / F^(p + 1) X ⟶ X / F^p X` is short exact. -/
private theorem filteredObjectGradedQuotientSuccShortExact
    (X : FilteredObject 𝒜) (p : ℤ) :
    (ShortComplex.mk
      (filteredObjectGradedToQuotientSucc X p)
      (filteredObjectQuotientTransition X p)
      (by
        -- Proof comment: the composite factors through the quotient by `F^p X`, so it vanishes.
        refine (cancel_epi (cokernel.π (X.filtration.stageInclusion p))).1 ?_
        calc
          cokernel.π (X.filtration.stageInclusion p) ≫
              filteredObjectGradedToQuotientSucc X p ≫
                filteredObjectQuotientTransition X p
              =
            (X.filtration.obj p).arrow ≫
              cokernel.π (X.filtration.obj (p + 1)).arrow ≫
                filteredObjectQuotientTransition X p := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun t ↦ t ≫ filteredObjectQuotientTransition X p)
                      (filteredObjectGradedToQuotientSucc_comm X p)
          _ = (X.filtration.obj p).arrow ≫ cokernel.π (X.filtration.obj p).arrow := by
                simpa [Category.assoc] using
                  congrArg
                    (fun t ↦ (X.filtration.obj p).arrow ≫ t)
                    (filteredObjectQuotientTransition_comm X p)
          _ = 0 := by
                simpa using (cokernel.condition ((X.filtration.obj p).arrow))
          _ = cokernel.π (X.filtration.stageInclusion p) ≫ 0 := by
                symm
                simp)).ShortExact := by
  let T : ShortComplex 𝒜 :=
    ShortComplex.mk
      ((X.filtration.obj p).arrow)
      (cokernel.π (X.filtration.obj p).arrow)
      (cokernel.condition _)
  have hT : T.Exact := by
    -- Proof comment: the standard stage row `F^p X ⟶ X ⟶ X / F^p X` is exact.
    simpa [T] using ShortComplex.exact_cokernel ((X.filtration.obj p).arrow)
  have hExact :
      (ShortComplex.mk
        (filteredObjectGradedToQuotientSucc X p)
        (filteredObjectQuotientTransition X p)
        (by
          refine (cancel_epi (cokernel.π (X.filtration.stageInclusion p))).1 ?_
          calc
            cokernel.π (X.filtration.stageInclusion p) ≫
                filteredObjectGradedToQuotientSucc X p ≫
                  filteredObjectQuotientTransition X p
                =
              (X.filtration.obj p).arrow ≫
                cokernel.π (X.filtration.obj (p + 1)).arrow ≫
                  filteredObjectQuotientTransition X p := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun t ↦ t ≫ filteredObjectQuotientTransition X p)
                        (filteredObjectGradedToQuotientSucc_comm X p)
            _ = (X.filtration.obj p).arrow ≫ cokernel.π (X.filtration.obj p).arrow := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun t ↦ (X.filtration.obj p).arrow ≫ t)
                      (filteredObjectQuotientTransition_comm X p)
            _ = 0 := by
                  simpa using (cokernel.condition ((X.filtration.obj p).arrow))
            _ = cokernel.π (X.filtration.stageInclusion p) ≫ 0 := by
                  symm
                  simp)).Exact := by
    -- Proof comment: reuse the textbook quotient-row argument after first lifting through
    -- `X / F^(p + 1) X` and then through `X`.
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro A x₂ hx₂
    obtain ⟨A₁, π₁, hπ₁, y, hy⟩ :=
      existsRefinementLiftOfEpi (e := cokernel.π (X.filtration.obj (p + 1)).arrow) x₂
    have hy_zero : y ≫ cokernel.π (X.filtration.obj p).arrow = 0 := by
      calc
        y ≫ cokernel.π (X.filtration.obj p).arrow
            = y ≫ cokernel.π (X.filtration.obj (p + 1)).arrow ≫
                filteredObjectQuotientTransition X p := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun t ↦ y ≫ t)
                      (filteredObjectQuotientTransition_comm X p).symm
        _ = π₁ ≫ x₂ ≫ filteredObjectQuotientTransition X p := by
              simpa [Category.assoc] using
                congrArg
                  (fun t ↦ t ≫ filteredObjectQuotientTransition X p)
                  hy.symm
        _ = 0 := by
              simpa [Category.assoc] using congrArg (fun t ↦ π₁ ≫ t) hx₂
    obtain ⟨A₂, ρ, hρ, z, hz⟩ := hT.exact_up_to_refinements y hy_zero
    refine ⟨A₂, ρ ≫ π₁, inferInstance, z ≫ cokernel.π (X.filtration.stageInclusion p), ?_⟩
    calc
      (ρ ≫ π₁) ≫ x₂ = ρ ≫ (π₁ ≫ x₂) := by simp [Category.assoc]
      _ = ρ ≫ (y ≫ cokernel.π (X.filtration.obj (p + 1)).arrow) := by rw [hy]
      _ = (ρ ≫ y) ≫ cokernel.π (X.filtration.obj (p + 1)).arrow := by simp [Category.assoc]
      _ = (z ≫ (X.filtration.obj p).arrow) ≫ cokernel.π (X.filtration.obj (p + 1)).arrow := by
            rw [hz]
      _ = z ≫ ((X.filtration.obj p).arrow ≫ cokernel.π (X.filtration.obj (p + 1)).arrow) := by
            simp [Category.assoc]
      _ = z ≫ (cokernel.π (X.filtration.stageInclusion p) ≫
            filteredObjectGradedToQuotientSucc X p) := by
            rw [filteredObjectGradedToQuotientSucc_comm]
      _ = (z ≫ cokernel.π (X.filtration.stageInclusion p)) ≫
            filteredObjectGradedToQuotientSucc X p := by
            simp [Category.assoc]
  -- Proof comment: exactness plus endpoint mono/epi data upgrades the quotient row to short
  -- exactness.
  exact ShortComplex.ShortExact.mk' hExact inferInstance
    (filteredObjectQuotientTransition_epi X p)

/-- Helper for Remark 19.13.10: the canonical complex map
`gr^r(M^•) ⟶ M^• / F^(r + 1) M^•`. -/
private noncomputable def gradedPieceToQuotientSucc
    (M : FilteredComplex) (r : ℤ) :
    M.gradedPiece r ⟶ M.quotient (r + 1) where
  f n := filteredObjectGradedToQuotientSucc (M.X n) r
  comm' := by
    intro i j hij
    -- Proof comment: the degreewise graded-to-quotient maps are natural in the filtered
    -- differential `M.d i j`.
    simpa [FilteredComplex.gradedPiece, FilteredComplex.quotient] using
      (filteredObjectGradedToQuotientSucc_naturality (f := M.d i j) r).symm

/-- Helper for Remark 19.13.10: the quotient row of complexes
`gr^r(M^•) ⟶ M^• / F^(r + 1) M^• ⟶ M^• / F^r M^•` is short exact. -/
private theorem gradedPieceQuotientSuccShortExact
    (M : FilteredComplex) (r : ℤ) :
    (ShortComplex.mk
      (gradedPieceToQuotientSucc M r)
      (M.quotientMapOfLE (by omega : r ≤ r + 1))
      (by
        -- Proof comment: the complex-level composite vanishes because each degree lies in the
        -- object-level short exact quotient row.
        ext n
        simpa [gradedPieceToQuotientSucc, FilteredComplex.quotientMapOfLE,
          filteredObjectQuotientTransition] using
          (ShortComplex.zero
            (ShortComplex.mk
              (filteredObjectGradedToQuotientSucc (M.X n) r)
              (filteredObjectQuotientTransition (M.X n) r)
              (by
                refine (cancel_epi (cokernel.π ((M.X n).filtration.stageInclusion r))).1 ?_
                calc
                  cokernel.π ((M.X n).filtration.stageInclusion r) ≫
                      filteredObjectGradedToQuotientSucc (M.X n) r ≫
                        filteredObjectQuotientTransition (M.X n) r
                      =
                    ((M.X n).filtration.obj r).arrow ≫
                      cokernel.π ((M.X n).filtration.obj (r + 1)).arrow ≫
                        filteredObjectQuotientTransition (M.X n) r := by
                          simpa [Category.assoc] using
                            congrArg
                              (fun t ↦ t ≫ filteredObjectQuotientTransition (M.X n) r)
                              (filteredObjectGradedToQuotientSucc_comm (M.X n) r)
                  _ = ((M.X n).filtration.obj r).arrow ≫
                        cokernel.π ((M.X n).filtration.obj r).arrow := by
                        simpa [Category.assoc] using
                          congrArg
                            (fun t ↦ ((M.X n).filtration.obj r).arrow ≫ t)
                            (filteredObjectQuotientTransition_comm (M.X n) r)
                  _ = 0 := by
                        simpa using (cokernel.condition (((M.X n).filtration.obj r).arrow))
                  _ = cokernel.π ((M.X n).filtration.stageInclusion r) ≫ 0 := by
                        symm
                        simp))) )
    ).ShortExact := by
  let T : ShortComplex (CochainComplex 𝒜 ℤ) :=
    ShortComplex.mk
      (gradedPieceToQuotientSucc M r)
      (M.quotientMapOfLE (by omega : r ≤ r + 1))
      (by
        ext n
        simpa [gradedPieceToQuotientSucc, FilteredComplex.quotientMapOfLE,
          filteredObjectQuotientTransition] using
          (ShortComplex.zero
            (ShortComplex.mk
              (filteredObjectGradedToQuotientSucc (M.X n) r)
              (filteredObjectQuotientTransition (M.X n) r)
              (by
                refine (cancel_epi (cokernel.π ((M.X n).filtration.stageInclusion r))).1 ?_
                calc
                  cokernel.π ((M.X n).filtration.stageInclusion r) ≫
                      filteredObjectGradedToQuotientSucc (M.X n) r ≫
                        filteredObjectQuotientTransition (M.X n) r
                      =
                    ((M.X n).filtration.obj r).arrow ≫
                      cokernel.π ((M.X n).filtration.obj (r + 1)).arrow ≫
                        filteredObjectQuotientTransition (M.X n) r := by
                          simpa [Category.assoc] using
                            congrArg
                              (fun t ↦ t ≫ filteredObjectQuotientTransition (M.X n) r)
                              (filteredObjectGradedToQuotientSucc_comm (M.X n) r)
                  _ = ((M.X n).filtration.obj r).arrow ≫
                        cokernel.π ((M.X n).filtration.obj r).arrow := by
                        simpa [Category.assoc] using
                          congrArg
                            (fun t ↦ ((M.X n).filtration.obj r).arrow ≫ t)
                            (filteredObjectQuotientTransition_comm (M.X n) r)
                  _ = 0 := by
                        simpa using (cokernel.condition (((M.X n).filtration.obj r).arrow))
                  _ = cokernel.π ((M.X n).filtration.stageInclusion r) ≫ 0 := by
                        symm
                        simp))))
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Proof comment: exactness of complexes is checked degreewise against the object-level
    -- quotient-row short exactness.
    rw [HomologicalComplex.exact_iff_degreewise_exact]
    intro n
    simpa [T, gradedPieceToQuotientSucc, FilteredComplex.quotientMapOfLE,
      filteredObjectQuotientTransition] using
      (filteredObjectGradedQuotientSuccShortExact (M.X n) r).exact
  · -- Proof comment: monomorphy of the left complex map is detected on each component.
    exact HomologicalComplex.mono_of_mono_f _ (fun n ↦ by
      simpa [T, gradedPieceToQuotientSucc, FilteredComplex.quotientMapOfLE,
        filteredObjectQuotientTransition] using
        (filteredObjectGradedQuotientSuccShortExact (M.X n) r).mono_f)
  · -- Proof comment: epimorphy of the right complex map is detected on each component.
    exact HomologicalComplex.epi_of_epi_f _ (fun n ↦ by
      simpa [T, gradedPieceToQuotientSucc, FilteredComplex.quotientMapOfLE,
        filteredObjectQuotientTransition] using
        (filteredObjectGradedQuotientSuccShortExact (M.X n) r).epi_g)

/-- Helper for Remark 19.13.10: against a termwise injective target, the cokernel of the
quotient-Hom transition is the Hom complex of the graded piece. -/
private noncomputable def quotientHomCokernelIsoHomComplexGradedPiece
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ)
    (hTermInj : ∀ n : ℤ, Injective (I.X n)) (r : ℤ) :
    cokernel (sourceQuotientHomTransition M I (by omega : r ≤ r + 1)) ≅
      CochainComplex.HomComplex (M.gradedPiece r) I := by
  let S : ShortComplex (CochainComplex 𝒜 ℤ) :=
    ShortComplex.mk
      (gradedPieceToQuotientSucc M r)
      (M.quotientMapOfLE (by omega : r ≤ r + 1))
      (by
        simpa using (gradedPieceQuotientSuccShortExact M r).zero)
  let hS : S.ShortExact := by
    simpa [S] using gradedPieceQuotientSuccShortExact M r
  let hHom :
      ({ X₁ := CochainComplex.HomComplex S.X₃ I
         X₂ := CochainComplex.HomComplex S.X₂ I
         X₃ := CochainComplex.HomComplex S.X₁ I
         f := CategoryTheory.CochainComplex.homComplexPrecomp (f := S.g) (I := I)
         g := CategoryTheory.CochainComplex.homComplexPrecomp (f := S.f) (I := I)
         zero := by
           ext n z p q hpq
           simp [CategoryTheory.CochainComplex.homComplexPrecomp, S.zero] } :
        ShortComplex (CochainComplex AddCommGrpCat ℤ)).ShortExact :=
    CategoryTheory.CochainComplex.homComplexShortExactOfTermwiseInjective S hS I hTermInj
  let hcofork :
      IsColimit
        (CokernelCofork.ofπ
          (CategoryTheory.CochainComplex.homComplexPrecomp
            (f := gradedPieceToQuotientSucc M r) (I := I))
          (by
            ext n z p q hpq
            simp [CategoryTheory.CochainComplex.homComplexPrecomp, S.zero])) :=
    ShortComplex.ShortExact.gIsCokernel hHom
  -- Proof comment: the Hom-side short exact row identifies the right-hand map as a cokernel of
  -- the explicit quotient-Hom transition.
  exact
    (IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (sourceQuotientHomTransition M I (by omega : r ≤ r + 1)))
      hcofork).symm

/-- Helper for Remark 19.13.10: the realization witness identifies each filtered stage transition
with the explicit quotient-Hom transition in the source tower. -/
private theorem realizationStageMap_comp_sourceQuotientHomTransition
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ)
    (F : AbFilteredComplex) (hF : F.RealizesInverseSystem (sourceQuotientHomTowerCocone M I))
    (p : ℤ) :
    DerivedCategory.Q.map (F.stageMapOfLE (lt_add_one p).le) ≫
        (realizesInverseSystemStageIso F (sourceQuotientHomTowerCocone M I) hF p).hom =
      (realizesInverseSystemStageIso F (sourceQuotientHomTowerCocone M I) hF (p + 1)).hom ≫
        DerivedCategory.Q.map
          (sourceQuotientHomTransition M I (by omega : -p ≤ -p + 1)) := by
  classical
  rcases hF with ⟨stageIso, _, _⟩
  -- Proof comment: this is the naturality square of the realizing stage-tower isomorphism for the
  -- unique morphism `op (p + 1) ⟶ op p`.
  simpa [sourceQuotientHomTower] using
    stageIso.hom.naturality
      ((homOfLE (show p ≤ p + 1 by omega)).op : Opposite.op (p + 1) ⟶ Opposite.op p)

/-- Helper for Remark 19.13.10: the realization witness identifies the stage inclusion with the
explicit precomposition map from the quotient tower cocone. -/
private theorem realizationStageInclusion_comp_sourceQuotientHomPrecomp
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ)
    (F : AbFilteredComplex) (hF : F.RealizesInverseSystem (sourceQuotientHomTowerCocone M I))
    (p : ℤ) :
    DerivedCategory.Q.map (F.stageInclusion p) ≫
        (realizesInverseSystemPointIso F (sourceQuotientHomTowerCocone M I) hF).hom =
      (realizesInverseSystemStageIso F (sourceQuotientHomTowerCocone M I) hF p).hom ≫
        DerivedCategory.Q.map
          (homComplexPrecomp (f := M.underlyingToQuotient (-p + 1)) (I := I)) := by
  classical
  rcases hF with ⟨stageIso, coconeHom, _⟩
  -- Proof comment: the cocone comparison in the realization data already records the desired
  -- compatibility between the canonical stage inclusion and the explicit quotient-Hom cocone leg.
  simpa [FilteredComplex.stageTowerCocone, sourceQuotientHomTowerCocone] using
    coconeHom.w (Opposite.op p)

/-- Helper for Remark 19.13.10: the quotient projection `M^• ⟶ M^• / F^p M^•` is epic degreewise,
hence epic as a cochain-complex morphism. -/
private theorem underlyingToQuotient_epi
    (M : FilteredComplex) (p : ℤ) :
    Epi (M.underlyingToQuotient p) := by
  -- Proof comment: every component of the quotient projection is the cokernel projection onto the
  -- stagewise quotient, so `epi_of_epi_f` upgrades the degreewise epimorphy to a complex-level
  -- epimorphism.
  exact HomologicalComplex.epi_of_epi_f _ (fun n ↦ by
    simpa [FilteredComplex.underlyingToQuotient] using
      (inferInstance : Epi (cokernel.π ((M.X n).filtration.obj p).arrow)))

/-- Helper for Remark 19.13.10: precomposition by an epic source map is monic on Hom complexes. -/
private theorem homComplexPrecomp_mono_of_epi
    {L M I : CochainComplex 𝒜 ℤ} (f : L ⟶ M) [Epi f] :
    Mono (homComplexPrecomp (f := f) (I := I)) := by
  -- Proof comment: degreewise, precomposition with an epic map is injective, and the owner lemma
  -- `mono_of_mono_f` promotes those componentwise monomorphisms to a mono of complexes.
  refine HomologicalComplex.mono_of_mono_f _ ?_
  intro n
  refine ConcreteCategory.mono_of_injective _ ?_
  intro z z' hzz'
  ext p q hpq
  have hcomp := congrArg (fun t ↦ t p q hpq) hzz'
  change f.f p ≫ z p q hpq = f.f p ≫ z' p q hpq at hcomp
  exact (cancel_epi (f.f p)).1 hcomp

/-- Helper for Remark 19.13.10: each degreewise precomposition map from a quotient Hom complex
is monic. -/
private noncomputable instance filteredHomDegreeStageComponentMono
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) (n p : ℤ) :
    Mono ((homComplexPrecomp (f := M.underlyingToQuotient (-p + 1)) (I := I)).f n) := by
  letI : Epi (M.underlyingToQuotient (-p + 1)) := underlyingToQuotient_epi M (-p + 1)
  letI :
      Mono (homComplexPrecomp (f := M.underlyingToQuotient (-p + 1)) (I := I)) :=
    homComplexPrecomp_mono_of_epi (f := M.underlyingToQuotient (-p + 1)) (I := I)
  infer_instance

/-- Helper for Remark 19.13.10: the `p`-th degreewise stage of the explicit filtered Hom owner is
the image subobject cut out by precomposition from `M^• / F^(-p + 1) M^•`. -/
private noncomputable abbrev filteredHomDegreeStageSubobject
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) (n p : ℤ) :
    Subobject ((CochainComplex.HomComplex M.underlying I).X n) :=
  Subobject.mk ((homComplexPrecomp (f := M.underlyingToQuotient (-p + 1)) (I := I)).f n)

/-- Helper for Remark 19.13.10: the explicit quotient-Hom stages form a decreasing filtration in
each cochain degree. -/
private theorem filteredHomDegreeStageSubobject_le
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) (n : ℤ) {p q : ℤ} (hpq : p ≤ q) :
    filteredHomDegreeStageSubobject M I n q ≤ filteredHomDegreeStageSubobject M I n p := by
  refine Subobject.mk_le_mk_of_comm
      ((sourceQuotientHomTransition M I (by omega : -q + 1 ≤ -p + 1)).f n) ?_
  -- Proof comment: the stage-`q` arrow factors through the stage-`p` arrow because
  -- `M^• ⟶ M^• / F^(-q + 1) M^•` factors through the intermediate quotient
  -- `M^• / F^(-p + 1) M^•`.
  have hcomp :
      sourceQuotientHomTransition M I (by omega : -q + 1 ≤ -p + 1) ≫
          homComplexPrecomp (f := M.underlyingToQuotient (-p + 1)) (I := I) =
        homComplexPrecomp (f := M.underlyingToQuotient (-q + 1)) (I := I) := by
    rw [sourceQuotientHomTransition, ← homComplexPrecomp_comp]
    simpa using
      congrArg (fun k ↦ homComplexPrecomp (f := k) (I := I)) <|
        underlyingToQuotient_comp_quotientMapOfLE M
          (by omega : -q + 1 ≤ -p + 1)
  simpa [filteredHomDegreeStageSubobject] using congrArg (fun t ↦ t.f n) hcomp

/-- Helper for Remark 19.13.10: in each degree, the explicit quotient-Hom stages give a genuine
decreasing filtration on the ambient Hom group. -/
private noncomputable def filteredHomDegreeFiltration
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) (n : ℤ) :
    DecreasingFiltration ((CochainComplex.HomComplex M.underlying I).X n) where
  toFun p := filteredHomDegreeStageSubobject M I n p
  monotone' := by
    intro p q hpq
    -- Proof comment: monotonicity in `ℤᵒᵈ` is exactly antitonicity in the textbook filtration
    -- index.
    exact
      filteredHomDegreeStageSubobject_le M I n
        (p := q) (q := p) (show (q : ℤ) ≤ p from hpq)

/-- Helper for Remark 19.13.10: the `n`-th degree object of the explicit filtered Hom owner. -/
private noncomputable def filteredHomDegreeObject
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) (n : ℤ) :
    FilteredObject AddCommGrpCat where
  obj := (CochainComplex.HomComplex M.underlying I).X n
  filtration := filteredHomDegreeFiltration M I n

/-- Helper for Remark 19.13.10: the `p`-th explicit stage in degree `n` is canonically the
degree-`n` term of the quotient Hom complex. -/
private noncomputable def filteredHomDegreeStageIso
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) (n p : ℤ) :
    (filteredHomDegreeObject M I n).filtration.obj p ≅
      (CochainComplex.HomComplex (M.quotient (-p + 1)) I).X n :=
  (Subobject.underlyingIso
    ((homComplexPrecomp (f := M.underlyingToQuotient (-p + 1)) (I := I)).f n)).symm

/-- Helper for Remark 19.13.10: the explicit stage inclusion in degree `n` is literally the
component of the quotient-Hom precomposition map. -/
private theorem filteredHomDegreeStageIso_hom_comp_arrow
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) (n p : ℤ) :
    (filteredHomDegreeStageIso M I n p).hom ≫
        (filteredHomDegreeStageSubobject M I n p).arrow =
      (homComplexPrecomp (f := M.underlyingToQuotient (-p + 1)) (I := I)).f n := by
  -- Proof comment: `Subobject.underlyingIso` is the canonical identification between the stage
  -- object and the domain of the monomorphism defining that subobject.
  simpa [filteredHomDegreeStageIso, filteredHomDegreeStageSubobject]

/-- Helper for Remark 19.13.10: the ambient differential preserves the explicit quotient-Hom
stages degreewise. -/
private theorem filteredHomDegreeStageArrow_comp_d
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) (n p : ℤ) :
    (filteredHomDegreeStageSubobject M I n p).arrow ≫
        (CochainComplex.HomComplex M.underlying I).d n (n + 1) =
      (CochainComplex.HomComplex (M.quotient (-p + 1)) I).d n (n + 1) ≫
        (filteredHomDegreeStageSubobject M I (n + 1) p).arrow := by
  -- Proof comment: `homComplexPrecomp` is a chain map, so its degree components commute with the
  -- Hom-complex differential.
  simpa [filteredHomDegreeStageSubobject] using
    (homComplexPrecomp (f := M.underlyingToQuotient (-p + 1)) (I := I)).comm n (n + 1)
      (by simp [ComplexShape.up, ComplexShape.up'])

/-- For every total degree, the groups `Ext^n(M / F^p M, K)` vanish for all sufficiently small
filtration indices `p`. -/
def EventualQuotientDerivedExtVanishesBelow
    (M : FilteredComplex) (K : DerivedCategory 𝒜) : Prop :=
  ∀ n : ℤ, ∃ p₀ : ℤ, ∀ ⦃p : ℤ⦄, p ≤ p₀ →
    IsZero (derivedExtGroup (DerivedCategory.Q.obj (M.quotient p)) K n)

/-- For every total degree, the canonical maps `Ext^n(M / F^p M, K) → Ext^n(M, K)` are
isomorphisms for all sufficiently large filtration indices `p`. -/
def EventualQuotientDerivedExtStabilizesAbove
    (M : FilteredComplex) (K : DerivedCategory 𝒜) : Prop :=
  ∀ n : ℤ, ∃ p₁ : ℤ, ∀ ⦃p : ℤ⦄, p₁ ≤ p →
    IsIso (derivedExtGroupPrecomp K (DerivedCategory.Q.map (M.underlyingToQuotient p)) n)

/-- Helper for Remark 19.13.10: the realized page-one term of the filtered Hom complex should be
identified with the derived `Ext` group of the corresponding graded piece. -/
private noncomputable def pageOneIsoOfFilteredHomRealization
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) [I.IsKInjective]
    (hTermInj : ∀ n : ℤ, Injective (I.X n))
    (K : DerivedCategory 𝒜) (eK : DerivedCategory.Q.obj I ≅ K)
    (F : AbFilteredComplex) (E : CohomologicalSpectralSequence AddCommGrpCat 0)
    (hF : F.RealizesInverseSystem (sourceQuotientHomTowerCocone M I))
    [IsAssociatedToFilteredComplex F E] (p q : ℤ) :
    (E.page 1).X (p, q) ≅
      derivedExtGroup (DerivedCategory.Q.obj (M.gradedPiece (-p))) K (p + q) := by
  -- Route correction: the explicit quotient row and the Hom-side cokernel bridge are now proved.
  -- The remaining blocker is not the object-level exactness, but upgrading the realized graded
  -- piece of the abstract filtered complex `F` to the explicit quotient-Hom cokernel without
  -- assuming `Q` preserves cokernels.
  -- Proof comment: first rewrite the page-one term using the owner comparison
  -- `FilteredComplex.pageOneIso F E p q`, then identify `F.gradedPiece p` with the Hom complex of
  -- `M.gradedPiece (-p)` via the realized quotient tower and the concrete cokernel bridge proved
  -- above.
  -- TODO: use the short exact row
  -- `gr^{-p} M ⟶ M / F^{-p + 1} M ⟶ M / F^{-p} M`
  -- together with `quotientHomCokernelIsoHomComplexGradedPiece` to identify the explicit
  -- quotient-Hom cokernel with `CochainComplex.HomComplex (M.gradedPiece (-p)) I`; what remains
  -- is the realization-side bridge from `F.gradedPiece p` to that cokernel at the actual-complex
  -- level, rather than only in the derived category.
  sorry

/-- Helper for Remark 19.13.10: eventual vanishing of quotient `Ext` groups gives the Chapter 12
upper stage-cohomology vanishing hypothesis for the realized filtered Hom complex. -/
private theorem eventualStageCohomologyVanishesAbove_of_eventualQuotientDerivedExtVanishesBelow
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) [I.IsKInjective]
    (K : DerivedCategory 𝒜) (eK : DerivedCategory.Q.obj I ≅ K)
    (F : AbFilteredComplex) (hF : F.RealizesInverseSystem (sourceQuotientHomTowerCocone M I))
    (hvanish : EventualQuotientDerivedExtVanishesBelow M K) :
    FilteredComplex.EventualStageCohomologyVanishesAbove F := by
  intro n
  obtain ⟨p₀, hp₀⟩ := hvanish n
  refine ⟨1 - p₀, ?_⟩
  intro p hp
  -- Proof comment: the `p`-th stage of `F` realizes the quotient complex
  -- `M^• / F^{-p + 1} M^•`, so the eventual quotient-`Ext` vanishing applies after the index
  -- change `r = -p + 1`.
  have hzero :
      IsZero (derivedExtGroup (DerivedCategory.Q.obj (M.quotient (-p + 1))) K n) :=
    hp₀ (p := -p + 1) (by omega)
  exact (stageHomologyIsoQuotientDerivedExt M I K eK F hF p n).isZero_iff.mpr hzero

/-- Helper for Remark 19.13.10: eventual stabilization of quotient `Ext` groups should give the
Chapter 12 lower stage-cohomology stabilization hypothesis for the realized filtered Hom complex.
-/
private theorem eventualStageCohomologyStabilizesBelow_of_eventualQuotientDerivedExtStabilizesAbove
    (M : FilteredComplex) (I : CochainComplex 𝒜 ℤ) [I.IsKInjective]
    (K : DerivedCategory 𝒜) (eK : DerivedCategory.Q.obj I ≅ K)
    (F : AbFilteredComplex) (hF : F.RealizesInverseSystem (sourceQuotientHomTowerCocone M I))
    (hstable : EventualQuotientDerivedExtStabilizesAbove M K) :
    FilteredComplex.EventualStageCohomologyStabilizesBelow F := by
  intro n
  obtain ⟨p₁, hp₁⟩ := hstable n
  refine ⟨1 - p₁, ?_⟩
  intro p hp
  -- Proof comment: after rewriting the stage and underlying cohomology objects through
  -- `stageHomologyIsoQuotientDerivedExt` and `underlyingHomologyIsoDerivedExt`, the stage
  -- cohomology map should become the derived precomposition map induced by
  -- `M.underlyingToQuotient (-p + 1)`.
  let eStage := stageHomologyIsoQuotientDerivedExt M I K eK F hF p n
  let eUnder := underlyingHomologyIsoDerivedExt M I K eK F hF n
  let f :=
    derivedExtGroupPrecomp K (DerivedCategory.Q.map (M.underlyingToQuotient (-p + 1))) n
  have hf : IsIso f := hp₁ (p := -p + 1) (by omega)
  letI : IsIso f := hf
  -- Proof comment: the realization identifies `F.stageInclusion p` with the explicit cocone leg,
  -- so the induced cohomology map is the conjugate of the derived precomposition map.
  convert (show IsIso (eStage.hom ≫ f ≫ eUnder.inv) by infer_instance) using 1
  -- TODO: normalize `F.cohomologyMap p n` through `realizationStageInclusion_comp_sourceQuotientHomPrecomp`
  -- and the naturality of `homComplexHomologyIsoDerivedExt` under `homComplexPrecomp`.
  simp [eStage, eUnder, f, FilteredComplex.cohomologyMap, stageHomologyIsoQuotientDerivedExt,
    underlyingHomologyIsoDerivedExt, realizationStageInclusion_comp_sourceQuotientHomPrecomp,
    sourceQuotientHomTower, sourceQuotientHomTowerCocone, qObjHomologyIso,
    derivedExtGroupIsoOfTargetIso, homComplexHomologyIsoDerivedExt, Category.assoc]

/-- A filtered-complex model for the dual Ext spectral sequence
`E_1^{p,q} = Ext^{p + q}(gr^{-p} M, K)` attached to a filtered complex `M^•` and a derived object
`K`. -/
structure FilteredComplexSourceExtSpectralSequenceData
    (M : FilteredComplex) (K : DerivedCategory 𝒜) where
  /-- The filtered complex of abelian groups producing the spectral sequence. -/
  filteredHomComplex : AbFilteredComplex
  /-- The cohomological spectral sequence attached to the chosen filtered Hom complex. -/
  spectralSequence : CohomologicalSpectralSequence AddCommGrpCat 0
  /-- The spectral sequence is associated to the chosen filtered Hom complex. -/
  associated : IsAssociatedToFilteredComplex filteredHomComplex spectralSequence
  /-- The `E₁`-page identifies with the derived `Ext` groups of the shifted graded pieces
  `gr^{-p}(M^•)`. -/
  pageOneIso : ∀ p q : ℤ,
    (spectralSequence.page 1).X (p, q) ≅
      derivedExtGroup (DerivedCategory.Q.obj (M.gradedPiece (-p))) K (p + q)
  /-- The abutment cohomology of the filtered Hom complex identifies with `Ext^n(M, K)`. -/
  abutmentIso : ∀ n : ℤ,
    filteredHomComplex.underlying.homology n ≅
      derivedExtGroup (DerivedCategory.Q.obj (M.underlying)) K n
  /-- The eventual quotient-Ext vanishing and stabilization hypotheses force the spectral
  sequence to be bounded. -/
  bounded_of_eventualQuotientExt_control :
    EventualQuotientDerivedExtVanishesBelow M K →
      EventualQuotientDerivedExtStabilizesAbove M K →
      CohomologicalSpectralSequence.IsBounded spectralSequence
  /-- The same hypotheses force convergence of the associated filtered complex to its abutment
  cohomology. -/
  converges_of_eventualQuotientExt_control :
    EventualQuotientDerivedExtVanishesBelow M K →
      EventualQuotientDerivedExtStabilizesAbove M K →
      CategoryTheory.FilteredComplex.convergesToCohomology filteredHomComplex spectralSequence

-- Proof sketch: choose a K-injective complex `I^•` representing `K`, form the filtered complex
-- `Hom^•(M^•, I^•)` with filtration
-- `F^p Hom^•(M^•, I^•) = Hom^•(M^• / F^{-p + 1} M^•, I^•)`, and apply the filtered-complex
-- spectral sequence from Chapter 12. The `E₁`-page identifies with
-- `Ext^{p+q}(gr^{-p} M, K)`, while Lemma 12.24.13 turns the eventual vanishing and eventual
-- stabilization hypotheses on `Ext^n(M / F^p M, K)` into boundedness and convergence to
-- `Ext^{p+q}(M, K)`.
/-- Remark 19.13.10: for a Grothendieck abelian category `𝒜`, a filtered complex `M^•`, and an
object `K` of `D(𝒜)`, there is a spectral sequence in abelian groups with
`E₁^{p,q} = Ext^{p + q}(gr^{-p}(M^•), K)`; moreover, if `Ext^n(M / F^p M, K)` vanishes for
`p ≪ 0` and the canonical map `Ext^n(M / F^p M, K) → Ext^n(M, K)` is an isomorphism for
`p ≫ 0`, then this spectral sequence is bounded and converges to `Ext^{p + q}(M, K)`. In this
file, the chosen spectral sequence is packaged as
`FilteredComplexSourceExtSpectralSequenceData M K`. -/
@[stacks 0G1Z]
theorem filteredComplexSourceExtSpectralSequence_exists
    (M : FilteredComplex) (K : DerivedCategory 𝒜) :
    -- Route correction: the remaining work is the source-faithful filtered-Hom construction,
    -- not a synthetic page package, because `associated` must come from an actual filtered
    -- complex whose stage cohomology matches the quotient-Ext tower.
    -- Route correction: the quotient map `M / F^(-p + 1) M ⟶ M / F^(-p) M` is epic degreewise,
    -- so the next bridge must use its kernel `gr^(-p) M` and then pass to the cokernel only
    -- after applying `Hom(-, I)`.
    -- Proof comment: choose a K-injective representative `I` of `K`, realize the quotient-Hom
    -- inverse system by a filtered complex `F`, and then package the associated spectral
    -- sequence of `F`.
    Nonempty (FilteredComplexSourceExtSpectralSequenceData M K) := by
  classical
  obtain ⟨J, hInj, hKinj⟩ := CochainComplex.exists_functorial_kInjective_resolution 𝒜
  let L := DerivedCategory.Q.objPreimage K
  let I : CochainComplex 𝒜 ℤ := J.toFunctor.obj L
  letI : I.IsKInjective := hKinj L
  have hQI :
      DerivedCategory.Q.obj I ≅ K := by
    letI :
        IsIso (DerivedCategory.Q.map (J.ι.app L)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso 𝒜 (J.ι.app L)).2 (J.quasiIso_app L)
    -- Proof comment: invert the derived image of the chosen resolution map and compose with the
    -- canonical comparison between `Q.objPreimage K` and `K`.
    exact
      (asIso (DerivedCategory.Q.map (J.ι.app L))).symm ≪≫
        DerivedCategory.Q.objObjPreimageIso K
  obtain ⟨F, hF⟩ :=
    exists_filteredCochainComplexRealization_of_inverseSystem
      (sourceQuotientHomTower M I) (sourceQuotientHomTowerCocone M I)
  obtain ⟨E, hE⟩ := exists_filteredComplexAssociatedSpectralSequence F
  letI : IsAssociatedToFilteredComplex F E := hE
  refine ⟨{
    filteredHomComplex := F
    spectralSequence := E
    associated := hE
    pageOneIso := pageOneIsoOfFilteredHomRealization M I (hInj L) K hQI F E hF
    abutmentIso := ?_
    bounded_of_eventualQuotientExt_control := ?_
    converges_of_eventualQuotientExt_control := ?_
  }⟩
  · intro n
    -- Proof comment: the realization cocone already identifies the derived object of
    -- `F.underlying` with the concrete Hom complex `Hom(M.underlying, I)`, and the ordinary
    -- homology comparison is recovered through `DerivedCategory.homologyFunctorFactors`.
    exact underlyingHomologyIsoDerivedExt M I K hQI F hF n
  · intro hvanish hstable
    -- Proof comment: convert the quotient-Ext control into the Chapter 12 stage-cohomology
    -- control expected by the owner boundedness theorem for associated spectral sequences.
    exact
      FilteredComplex.associatedSpectralSequence_isBounded_of_eventual_stage_cohomology F E
        (eventualStageCohomologyVanishesAbove_of_eventualQuotientDerivedExtVanishesBelow
          M I K hQI F hF hvanish)
        (eventualStageCohomologyStabilizesBelow_of_eventualQuotientDerivedExtStabilizesAbove
          M I K hQI F hF hstable)
  · intro hvanish hstable
    -- Proof comment: the same transferred stage-cohomology control feeds directly into the owner
    -- convergence theorem for the associated spectral sequence of `F`.
    exact
      FilteredComplex.associatedSpectralSequence_convergesToCohomology_of_eventual_stage_cohomology
        F E
        (eventualStageCohomologyVanishesAbove_of_eventualQuotientDerivedExtVanishesBelow
          M I K hQI F hF hvanish)
        (eventualStageCohomologyStabilizesBelow_of_eventualQuotientDerivedExtStabilizesAbove
          M I K hQI F hF hstable)

end CategoryTheory
