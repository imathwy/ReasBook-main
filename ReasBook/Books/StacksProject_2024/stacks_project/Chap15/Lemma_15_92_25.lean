import Mathlib
import StacksProject_2024.stacks_project.Chap13.Lemma_13_4_9
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.stacks_project.Chap13.Lemma_13_31_7
import StacksProject_2024.stacks_project.Chap13.Lemma_13_30_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_56_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_56_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_60_3
import StacksProject_2024.stacks_project.Chap15.Lemma_15_90_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_92_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_92_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.ObjectProperty

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A)

local notation "IB" => I.map (algebraMap A B)
local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)
local notation "KModA" => HomotopyCategory (ModuleCat A) (up ℤ)
local notation "KModB" => HomotopyCategory (ModuleCat B) (up ℤ)
local notation "KQA" => HomotopyCategory.quotient (ModuleCat A) (up ℤ)
local notation "QhA" => (DerivedCategory.Qh : KModA ⥤ DModA)
local notation "QhB" => (DerivedCategory.Qh : KModB ⥤ DModB)
local notation "QisA" => HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)
local notation "QisB" => HomotopyCategory.quasiIso (ModuleCat B) (up ℤ)

/- Domain-style sampling:
- primary domain: derived-complete full subcategories in derived module categories under change of
  rings;
- sampled owner-side declarations:
  `DerivedCategory.derivedCompleteObjectProperty`,
  `ObjectProperty.lift`,
  `CategoryTheory.isDerivedCompleteWithRespectTo_iff_restrictScalars`,
  `CategoryTheory.derivedTensorWithAlgebraAdjunction`;
- best owner abstraction: the source-facing equivalence lives on the full subcategories cut out by
  `derivedCompleteObjectProperty`, and the comparison functor is the canonical
  `ObjectProperty.lift` of derived restriction of scalars;
- primitive data: the ideal `I`, the flat algebra map `A → B`, and the canonical derived
  restriction functor `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- derived API: the induced equivalence
  `D_comp(B, IB) ⥤ D_comp(A, I)`.

Layer triage:
- `source-facing`: the equivalence between the derived-complete full subcategories;
- `core/canonical`: `derivedCompleteObjectProperty` together with `ObjectProperty.lift`;
- `bridge/view`: `isDerivedCompleteWithRespectTo_iff_restrictScalars` and
  `derivedTensorWithAlgebraAdjunction`. -/

-- Proof sketch: Lemma `15.92.24` shows that restriction lands in the derived-complete full
-- subcategory. For essential surjectivity, use the Stacks construction
-- `K ↦ RHom_A(B, K)` from the source proof, realized through the derived change-of-rings
-- adjunction of Lemma `15.60.3`; the flatness and quotient-bijectivity hypotheses together with
-- Lemma `15.90.4` make the unit and counit become isomorphisms on the derived-complete
-- subcategories.
/-- Helper for Lemma 15.92.25: derived completeness is preserved under isomorphism of derived
objects. -/
private lemma isDerivedCompleteWithRespectTo_iff_of_iso
    {I : Ideal A} {K L : DModA} (e : K ≅ L) :
    K.IsDerivedCompleteWithRespectTo I ↔ L.IsDerivedCompleteWithRespectTo I := by
  constructor
  · intro hK
    -- Proof comment: postcompose maps into `L` with `e.inv` to transport the defining
    -- subsingleton condition back to `K`.
    intro f hf E
    have hSub :
        Subsingleton
          ((((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).obj
              E) ⟶ K) :=
      hK f hf E
    refine ⟨fun g₁ g₂ ↦ ?_⟩
    have hEq : g₁ ≫ e.inv = g₂ ≫ e.inv := @Subsingleton.elim _ hSub _ _
    simpa [Category.assoc] using congrArg (fun h ↦ h ≫ e.hom) hEq
  · intro hL
    -- Proof comment: the reverse implication is the same transport argument using `e.hom`.
    intro f hf E
    have hSub :
        Subsingleton
          ((((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).obj
              E) ⟶ L) :=
      hL f hf E
    refine ⟨fun g₁ g₂ ↦ ?_⟩
    have hEq : g₁ ≫ e.hom = g₂ ≫ e.hom := @Subsingleton.elim _ hSub _ _
    simpa [Category.assoc] using congrArg (fun h ↦ h ≫ e.inv) hEq

/-- Helper for Lemma 15.92.25: fix a functorial K-injective replacement on cochain complexes of
`A`-modules so the source proof can compute `RHom_A(B, -)` on explicit models. -/
private noncomputable abbrev derivedCoextendScalars_k_injective_resolution :
    CochainComplex.FunctorialComplexApproximation (ModuleCat A) :=
  Classical.choose (CochainComplex.exists_functorial_kInjective_resolution (ModuleCat A))

/-- Helper for Lemma 15.92.25: choose a K-injective cochain-complex representative of a derived
`A`-module. -/
private noncomputable abbrev derivedCoextendScalars_k_injective_preimage
    (K : DModA) : CpxA :=
  derivedCoextendScalars_k_injective_resolution (A := A).toFunctor.obj
    (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 15.92.25: the chosen representative is K-injective. -/
private theorem derivedCoextendScalars_k_injective_preimage_isKInjective
    (K : DModA) :
    (derivedCoextendScalars_k_injective_preimage (A := A) K).IsKInjective := by
  -- Proof comment: the fixed functorial approximation lands in K-injective complexes by
  -- construction, so the chosen representative inherits that property immediately.
  exact
    (Classical.choose_spec
      (CochainComplex.exists_functorial_kInjective_resolution (ModuleCat A))).2
      (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 15.92.25: the chosen K-injective representative is canonically
quasi-isomorphic to the original `Q.objPreimage` model. -/
private noncomputable abbrev derivedCoextendScalars_k_injective_preimage_map
    (K : DModA) :
    DerivedCategory.Q.objPreimage K ⟶ derivedCoextendScalars_k_injective_preimage (A := A) K :=
  derivedCoextendScalars_k_injective_resolution (A := A).ι.app
    (DerivedCategory.Q.objPreimage K)

/-- Helper for Lemma 15.92.25: the chosen K-injective replacement still represents the original
derived object. -/
private theorem derivedCoextendScalars_k_injective_preimage_q_map_isIso
    (K : DModA) :
    IsIso (DerivedCategory.Q.map (derivedCoextendScalars_k_injective_preimage_map (A := A) K)) := by
  -- Proof comment: the approximation morphism is a quasi-isomorphism, and `DerivedCategory.Q`
  -- inverts quasi-isomorphisms by definition.
  exact
    DerivedCategory.Q_isInverted _ (derivedCoextendScalars_k_injective_preimage_map (A := A) K)

/-- Helper for Lemma 15.92.25: the chosen K-injective replacement represents the same derived
object as the original model of `K`. -/
private noncomputable abbrev derivedCoextendScalars_k_injective_preimage_iso
    (K : DModA) :
    DerivedCategory.Q.obj (derivedCoextendScalars_k_injective_preimage (A := A) K) ≅ K :=
  letI :
      IsIso (DerivedCategory.Q.map (derivedCoextendScalars_k_injective_preimage_map (A := A) K)) :=
    derivedCoextendScalars_k_injective_preimage_q_map_isIso (A := A) K
  (asIso (DerivedCategory.Q.map (derivedCoextendScalars_k_injective_preimage_map (A := A) K))).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso K

/-- Helper for Lemma 15.92.25: fixed-algebra coextension on homotopy categories is the source
functor whose total right derived functor models `RHom_A(B, -)`. -/
private abbrev derivedCoextendScalars_homotopy_to_derived :
    KModA ⥤ DModB :=
  (((ModuleCat.coextendScalars (algebraMap A B)).mapHomotopyCategory (up ℤ)) ⋙ QhB)

/-- Helper for Lemma 15.92.25: K-injective resolutions globalize fixed-algebra coextension to a
canonical total right derived functor. -/
private instance derivedCoextendScalars_hasRightDerivedFunctor :
    (derivedCoextendScalars_homotopy_to_derived (A := A) (B := B)).HasRightDerivedFunctor QisA := by
  -- Proof comment: every cochain complex of `A`-modules admits a functorial K-injective
  -- resolution, so Lemma `13.31.7` supplies the global right derived functor.
  refine hasRightDerivedFunctor_of_kInjective_resolutions
    (F := derivedCoextendScalars_homotopy_to_derived (A := A) (B := B)) ?_
  intro K
  let R := derivedCoextendScalars_k_injective_resolution (A := A)
  refine ⟨R.toFunctor.obj K, ?_, R.ι.app K, R.quasiIso_app K⟩
  exact
    (Classical.choose_spec
      (CochainComplex.exists_functorial_kInjective_resolution (ModuleCat A))).2 K

/-- Helper for Lemma 15.92.25: the ambient right adjoint from the source proof, namely the total
right derived functor of coextension along `A → B`. -/
noncomputable abbrev derivedCoextendScalars : DModA ⥤ DModB :=
  Functor.totalRightDerived
    (derivedCoextendScalars_homotopy_to_derived (A := A) (B := B))
    QhA
    QisA

/-- Helper for Lemma 15.92.25: on a K-injective complex, the ambient right adjoint evaluates to
ordinary termwise coextension. -/
noncomputable def derivedCoextendScalars_value_iso
    (I : CpxA) [I.IsKInjective] :
    (derivedCoextendScalars (A := A) (B := B)).obj (QhA.obj (KQA.obj I)) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.coextendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj I) := by
  let F : KModA ⥤ DModB := derivedCoextendScalars_homotopy_to_derived (A := A) (B := B)
  let _ : F.ComputesRightDerivedAt QisA (KQA.obj I) :=
    kInjective_computesRightDerivedFunctorAt F I
  calc
    (derivedCoextendScalars (A := A) (B := B)).obj (QhA.obj (KQA.obj I)) ≅
        rightDerivedValue QisA F (KQA.obj I) := by
      -- Proof comment: `Functor.totalRightDerived` is defined pointwise by the right-derived
      -- value, so evaluating at `QhA.obj ((KQA).obj I)` produces that colimit object.
      simpa [Functor.totalRightDerived, derivedCoextendScalars,
        derivedCoextendScalars_homotopy_to_derived, F] using
        (QhA.leftKanExtensionObjIsoColimit F (QhA.obj (KQA.obj I)))
    _ ≅
        DerivedCategory.Q.obj
          (((ModuleCat.coextendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj I) := by
      -- Proof comment: because `I` is K-injective, the identity denominator already computes the
      -- right-derived value of coextension on the nose.
      let hId : QisA (𝟙 (KQA.obj I)) := MorphismProperty.id_mem _ _
      simpa [F] using
        (asIso (rightDerivedValueLeg QisA F (𝟙 (KQA.obj I)) hId)).symm

/-- Helper for Lemma 15.92.25: evaluating the ambient right adjoint on a derived object `K`
agrees with coextending the chosen K-injective representative of `K`. -/
noncomputable def derivedCoextendScalars_obj_iso
    (K : DModA) :
    (derivedCoextendScalars (A := A) (B := B)).obj K ≅
      DerivedCategory.Q.obj
        (((ModuleCat.coextendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj
          (derivedCoextendScalars_k_injective_preimage (A := A) K)) := by
  let I := derivedCoextendScalars_k_injective_preimage (A := A) K
  let eK : QhA.obj (KQA.obj I) ≅ K :=
    (DerivedCategory.quotientCompQhIso (ModuleCat A)).app I ≪≫
      derivedCoextendScalars_k_injective_preimage_iso (A := A) K
  letI : I.IsKInjective := derivedCoextendScalars_k_injective_preimage_isKInjective (A := A) K
  calc
    (derivedCoextendScalars (A := A) (B := B)).obj K ≅
        (derivedCoextendScalars (A := A) (B := B)).obj (QhA.obj (KQA.obj I)) :=
      (derivedCoextendScalars (A := A) (B := B)).mapIso eK.symm
    _ ≅
        DerivedCategory.Q.obj
          (((ModuleCat.coextendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj I) :=
      derivedCoextendScalars_value_iso (A := A) (B := B) I

/-- Helper for Lemma 15.92.25: exact restriction of scalars on cochain complexes computes its own
pointwise left derived functor at every `B`-complex. -/
private theorem restrictScalars_computesLeftDerivedAt_fixed_algebra
    (L : CochainComplex (ModuleCat B) ℤ) :
    let F :
        CochainComplex (ModuleCat B) ℤ ⥤ DModA :=
      (((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)) ⋙
        (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DModA))
    F.ComputesLeftDerivedAt
      (HomologicalComplex.quasiIso (ModuleCat B) (up ℤ))
      L := by
  let σ := algebraMap A B
  let F₀ : ModuleCat B ⥤ ModuleCat A := ModuleCat.restrictScalars σ
  let F :
      CochainComplex (ModuleCat B) ℤ ⥤ DModA :=
    (F₀.mapHomologicalComplex (up ℤ)) ⋙
      (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DModA)
  let Qis :
      MorphismProperty (CochainComplex (ModuleCat B) ℤ) :=
    HomologicalComplex.quasiIso (ModuleCat B) (up ℤ)
  letI :
      F₀.mapDerivedCategory.IsLeftDerivedFunctor
        F₀.mapDerivedCategoryFactors.hom
        Qis := by
    -- Proof comment: restriction of scalars is exact, so its derived lift is already computed by
    -- the canonical comparison from the underived functor.
    simpa [F₀, Qis] using
      (Functor.isLeftDerivedFunctor_of_inverts
        Qis
        F₀.mapDerivedCategory
        F₀.mapDerivedCategoryFactors)
  letI : F.HasLeftDerivedFunctor Qis :=
    Functor.HasLeftDerivedFunctor.mk'
      F₀.mapDerivedCategory
      F₀.mapDerivedCategoryFactors.hom
  have hComparison :
      IsIso (F₀.mapDerivedCategoryFactors.hom.app L) := by
    let hInverts : Qis.IsInvertedBy F := by
      intro X Y g hg
      change IsIso
        (DerivedCategory.Q.map (((ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ)).map g))
      exact
        DerivedCategory.Q_isInverted _
          (((ModuleCat.restrictScalars σ).mapHomologicalComplex (up ℤ)).map g)
    have :
        IsIso F₀.mapDerivedCategoryFactors.hom := by
      -- Proof comment: once the exact functor is recognized as its own left derived functor, the
      -- comparison natural transformation is objectwise invertible.
      exact
        Functor.isIso_of_isLeftDerivedFunctor_of_inverts
          F₀.mapDerivedCategory
          F₀.mapDerivedCategoryFactors.hom
          hInverts
    infer_instance
  -- Proof comment: the comparison above is exactly the fixed-algebra pointwise left-derived
  -- computation needed for the later `Adjunction.derived` packaging.
  simpa [F, F₀, Qis] using hComparison

/-- Helper for Lemma 15.92.25: after restricting the source-faithful coextended K-injective
model, one reaches the concrete `Q`-image of the restricted cochain complex. -/
noncomputable abbrev derivedCoextendScalars_restrict_obj_iso
    (K : DModA) :
    ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
      ((derivedCoextendScalars (A := A) (B := B)).obj K)) ≅
      DerivedCategory.Q.obj
        ((((ModuleCat.restrictScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj
          (((ModuleCat.coextendScalars (algebraMap A B)).mapHomologicalComplex (up ℤ)).obj
            (derivedCoextendScalars_k_injective_preimage (A := A) K)))) :=
  let σ := algebraMap A B
  let I₀ := derivedCoextendScalars_k_injective_preimage (A := A) K
  let C₀ :
      CochainComplex (ModuleCat B) ℤ :=
    (((ModuleCat.coextendScalars σ).mapHomologicalComplex (up ℤ)).obj I₀)
  -- Proof comment: first identify `derivedCoextendScalars.obj K` with the `Q`-image of the
  -- chosen coextended model, then use the exact-functor comparison for restriction of scalars.
  ((ModuleCat.restrictScalars σ).mapDerivedCategory).mapIso
      (derivedCoextendScalars_obj_iso (A := A) (B := B) K) ≪≫
    (ModuleCat.restrictScalars σ).mapDerivedCategoryFactors.app C₀

/-- Helper for Lemma 15.92.25: this is the source proof's ambient evaluation component
`restrict(RHom_A(B, K)) ⟶ K`, written directly on the chosen K-injective model of `K`. -/
noncomputable abbrev derivedCoextendScalars_evaluation_app
    (K : DModA) :
    ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
      ((derivedCoextendScalars (A := A) (B := B)).obj K)) ⟶ K :=
  let σ := algebraMap A B
  let I₀ := derivedCoextendScalars_k_injective_preimage (A := A) K
  -- Proof comment: normalize to the concrete restricted coextended complex, apply the underived
  -- counit on the chosen K-injective model, and transport back to the original derived object.
  (derivedCoextendScalars_restrict_obj_iso (A := A) (B := B) K).hom ≫
    DerivedCategory.Q.map
      ((((ModuleCat.restrictCoextendScalarsAdj σ).mapHomologicalComplex (up ℤ)).counit.app I₀)) ≫
    (derivedCoextendScalars_k_injective_preimage_iso (A := A) K).hom

/-- Helper for Lemma 15.92.25: every nonempty monomial in a finite generating family already lies
in the span ideal generated by that family. -/
private lemma monomial_mem_span_range
    {r : ℕ} (f : Fin r → A) {d : ℕ} (hd : 0 < d) (g : Fin d → Fin r) :
    (∏ i, f (g i)) ∈ Ideal.span (Set.range f) := by
  classical
  cases d with
  | zero =>
      cases Nat.not_lt_zero _ hd
  | succ d =>
      have hgen : f (g 0) ∈ Ideal.span (Set.range f) :=
        Ideal.subset_span (Set.mem_range_self (g 0))
      -- Proof comment: split off the first factor; the span ideal contains that generator and is
      -- closed under multiplication by arbitrary ring elements.
      simpa [Fin.prod_univ_succ] using
        Ideal.mul_mem_right (Ideal.span (Set.range f))
          (∏ i : Fin d, f (g i.succ)) hgen

/-- Helper for Lemma 15.92.25: exact restriction of scalars on homotopy categories is already
its own left derived functor. -/
private theorem restrictScalars_mapDerivedCategoryh_isLeftDerivedFunctor :
    ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).IsLeftDerivedFunctor
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactorsh.hom)
      QisB := by
  let F : ModuleCat B ⥤ ModuleCat A := ModuleCat.restrictScalars (algebraMap A B)
  letI : Limits.PreservesFiniteLimits F := by
    infer_instance
  -- Proof comment: exact restriction preserves quasi-isomorphisms already on homotopy
  -- categories, so the standard comparison `mapDerivedCategoryFactorsh.hom` is the left-derived
  -- counit on the nose.
  simpa [F] using
    (Functor.isLeftDerivedFunctor_of_inverts
      QisB
      F.mapDerivedCategory
      F.mapDerivedCategoryFactorsh)

/-- Helper for Lemma 15.92.25: the homotopy-level restriction-to-derived functor admits the
canonical total left derived functor computed by exact restriction of scalars. -/
private instance restrictScalars_mapHomotopyToDerived_hasLeftDerivedFunctor :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapHomotopyCategory (up ℤ)) ⋙ QhA)
      .HasLeftDerivedFunctor QisB := by
  -- Proof comment: package the previous exact left-derived comparison into the total
  -- left-derived owner on the homotopy-category source.
  simpa using
    (Functor.HasLeftDerivedFunctor.mk'
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory)
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactorsh.hom) :
      (((ModuleCat.restrictScalars (algebraMap A B)).mapHomotopyCategory (up ℤ)) ⋙ QhA)
        .HasLeftDerivedFunctor QisB)

/-- Helper for Lemma 15.92.25: the source adjunction `restrictScalars ⊣ coextendScalars` on
homotopy categories globalizes to an ambient adjunction
`D(B) ⇄ D(A)` whose right adjoint is the chosen `RHom_A(B,-)` model
`derivedCoextendScalars`. -/
noncomputable def restrictScalars_derivedCoextendScalars_adjunction :
    (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory ⊣
      derivedCoextendScalars (A := A) (B := B) :=
  -- Proof comment: apply the generic pointwise-derived Hom-equivalence on homotopy categories to
  -- the lifted adjunction `restrictScalars.mapHomotopyCategory ⊣ coextendScalars.mapHomotopyCategory`.
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M K ↦
        ((Adjunction.mapHomotopyCategory
            (ModuleCat.restrictCoextendScalarsAdj (algebraMap A B))).pointwiseDerivedHomEquiv
          QisA
          QisB
          K M).symm }

/-- Helper for Lemma 15.92.25: derived restriction of scalars reflects isomorphisms because it
reflects zero third objects in distinguished triangles. -/
private instance restrictScalars_mapDerivedCategory_reflectsIsomorphisms :
    ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).ReflectsIsomorphisms where
  reflects {X Y} f := by
    let F := (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory
    rw [isIso_iff_isZero_obj₃_of_distinguished_triangle (D := DModB) f]
    intro Z g h hT
    have hRestrictedZero :
        IsZero (F.obj Z) := by
      letI : IsIso (F.map f) := inferInstance
      have hMapped :
          Triangle.mk (F.map f) (F.map g)
              (F.map h ≫ (F.commShiftIso (1 : ℤ)).hom.app X) ∈ distTriang DModA := by
        -- Proof comment: exact derived restriction is triangulated, so it sends the chosen
        -- distinguished triangle on `f` to a distinguished triangle on `F.map f`.
        simpa [F] using F.map_distinguished (Triangle.mk f g h) hT
      -- Proof comment: the mapped triangle is a zero cone because `F.map f` is an isomorphism.
      exact
        ((isIso_iff_isZero_obj₃_of_distinguished_triangle (D := DModA) (F.map f)).1
          (inferInstance : IsIso (F.map f))) hMapped
    -- Proof comment: Lemma `15.92.24` reflects zero objects back through derived restriction.
    exact
      (isZero_restrictScalars_mapDerivedCategory_obj_iff (A := A) (B := B) Z).1 hRestrictedZero

/-- Helper for Lemma 15.92.25: the ambient counit of
`restrictScalars_derivedCoextendScalars_adjunction` is an isomorphism on `I`-derived-complete
objects. -/
private theorem derivedCoextendScalars_counit_isIso_of_isDerivedComplete
    [Module.Flat A B] (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          IB
          (algebraMap A B)
          Ideal.le_comap_map))
    (K : DModA) (hK : K.IsDerivedCompleteWithRespectTo I) :
    IsIso ((restrictScalars_derivedCoextendScalars_adjunction
      (A := A) (B := B)).counit.app K) := by
  -- Proof comment: the remaining source-faithful step is to identify the ambient derived counit
  -- with `derivedCoextendScalars_evaluation_app K` via the adjunction Hom-equivalence and then
  -- prove that explicit evaluation map is invertible by the Čech/K-injective model computation.
  -- TODO: prove the adapter `adj.homEquiv (...) (derivedCoextendScalars_evaluation_app K) = 𝟙 _`,
  -- establish the underived quasi-isomorphism on
  -- `(((ModuleCat.restrictCoextendScalarsAdj _).mapHomologicalComplex _).counit.app I₀)` using
  -- `extendedAlternatingCechComplex_baseChangeUnit_quasiIso_of_flat_of_quotientMap_bijective` and
  -- the localization-away vanishing criterion, and transport that quasi-isomorphism through `Q`.
  sorry

/-- Helper for Lemma 15.92.25: under the ambient derived restriction/coextension adjunction, the
ambient counit corresponds to the identity of `derivedCoextendScalars.obj K`. -/
private theorem restrictScalars_derivedCoextendScalars_homEquiv_counit_app
    (K : DModA) :
    let adj := restrictScalars_derivedCoextendScalars_adjunction (A := A) (B := B)
    adj.homEquiv ((derivedCoextendScalars (A := A) (B := B)).obj K) K
      (adj.counit.app K) = 𝟙 ((derivedCoextendScalars (A := A) (B := B)).obj K) := by
  let adj := restrictScalars_derivedCoextendScalars_adjunction (A := A) (B := B)
  -- Proof comment: this is the standard adjunction normalization of the counit under the
  -- Hom-equivalence, recorded explicitly because the final source-faithful argument compares the
  -- ambient counit against the explicit evaluation morphism by checking that both map to `𝟙`.
  simpa using (Adjunction.homEquiv_counit adj K)

/-- Helper for Lemma 15.92.25: the ambient unit of
`restrictScalars_derivedCoextendScalars_adjunction` is an isomorphism on `IB`-derived-complete
objects. -/
private theorem derivedCoextendScalars_unit_isIso_of_isDerivedComplete
    [Module.Flat A B] (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          IB
          (algebraMap A B)
          Ideal.le_comap_map))
    (L : (derivedCompleteObjectProperty IB).FullSubcategory) :
    IsIso ((restrictScalars_derivedCoextendScalars_adjunction
      (A := A) (B := B)).unit.app L.obj) := by
  let F := (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory
  let adj := restrictScalars_derivedCoextendScalars_adjunction (A := A) (B := B)
  have hRestrictedComplete :
      (F.obj L.obj).IsDerivedCompleteWithRespectTo I := by
    -- Proof comment: Lemma `15.92.24` identifies `IB`-derived completeness with derived
    -- completeness after restriction of scalars.
    exact (isDerivedCompleteWithRespectTo_iff_restrictScalars L.obj I).2 L.property
  letI : IsIso (adj.counit.app (F.obj L.obj)) := by
    -- Proof comment: apply the completed A-side counit theorem to the restricted complete object.
    exact
      derivedCoextendScalars_counit_isIso_of_isDerivedComplete
        (I := I) hI hquot (F.obj L.obj) hRestrictedComplete
  have hMapUnit : IsIso (F.map (adj.unit.app L.obj)) := by
    -- Route correction: once derived restriction is known to reflect isomorphisms, the source
    -- proof's split-right-inverse argument packages into the adjunction triangle identity.
    exact isIso_of_hom_comp_eq_id _ (adj.left_triangle_components L.obj)
  -- Proof comment: reflect the isomorphism of the restricted unit back to the ambient unit.
  exact isIso_of_reflects_iso (adj.unit.app L.obj) F

/-- Helper for Lemma 15.92.25: once the ambient counit for a right adjoint `G` to derived
restriction is invertible on `I`-derived-complete objects, that right adjoint automatically lands
in the `IB`-derived-complete subcategory. -/
theorem rightAdjoint_preserves_isDerivedComplete_of_counit_isIso
    (G : DModA ⥤ DModB)
    (adj : (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory ⊣ G)
    (hcounit :
      ∀ K : DModA,
        K.IsDerivedCompleteWithRespectTo I →
          IsIso (adj.counit.app K)) :
    ∀ K : DModA,
      K.IsDerivedCompleteWithRespectTo I →
        (G.obj K).IsDerivedCompleteWithRespectTo IB := by
  intro K hK
  letI : IsIso (adj.counit.app K) := hcounit K hK
  have hRestricted :
      (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj
        (G.obj K)).IsDerivedCompleteWithRespectTo I := by
    -- Proof comment: transport derived completeness backwards across the counit isomorphism
    -- `restrict(G(K)) ≅ K`.
    exact
      (isDerivedCompleteWithRespectTo_iff_of_iso
        (I := I) (asIso (adj.counit.app K))).2 hK
  -- Proof comment: Lemma `15.92.24` identifies `IB`-derived completeness with derived
  -- completeness after restriction of scalars.
  exact
    (isDerivedCompleteWithRespectTo_iff_restrictScalars (G.obj K) I).1 hRestricted

/-- Helper for Lemma 15.92.25: the canonical restriction functor from `IB`-derived-complete
objects of `D(B)` to `I`-derived-complete objects of `D(A)`. -/
abbrev derivedCompleteRestrictionFunctor :
    (derivedCompleteObjectProperty IB).FullSubcategory ⥤
      (derivedCompleteObjectProperty I).FullSubcategory :=
  (derivedCompleteObjectProperty I).lift
    ((derivedCompleteObjectProperty IB).ι ⋙
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory)
    (fun L ↦ (isDerivedCompleteWithRespectTo_iff_restrictScalars L.obj I).2 L.property)

/-- Helper for Lemma 15.92.25: if an ambient right adjoint to derived restriction preserves
derived completeness, then it restricts to the derived-complete full subcategories. -/
abbrev derivedCompleteRestrictionRightAdjoint
    (G : DModA ⥤ DModB)
    (hG_mem :
      ∀ K : DModA,
        K.IsDerivedCompleteWithRespectTo I →
          (G.obj K).IsDerivedCompleteWithRespectTo IB) :
    (derivedCompleteObjectProperty I).FullSubcategory ⥤
      (derivedCompleteObjectProperty IB).FullSubcategory :=
  (derivedCompleteObjectProperty IB).lift
    ((derivedCompleteObjectProperty I).ι ⋙ G)
    (fun K ↦ hG_mem K.obj K.property)

/-- Helper for Lemma 15.92.25: an ambient unit isomorphism restricts to the derived-complete
subcategories, objectwise. -/
noncomputable def derivedCompleteRestriction_unitComponentIso
    (G : DModA ⥤ DModB)
    (hG_mem :
      ∀ K : DModA,
        K.IsDerivedCompleteWithRespectTo I →
          (G.obj K).IsDerivedCompleteWithRespectTo IB)
    (adj :
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory ⊣ G)
    (hunit :
      ∀ K : (derivedCompleteObjectProperty IB).FullSubcategory,
        IsIso (adj.unit.app K.obj))
    (K : (derivedCompleteObjectProperty IB).FullSubcategory) :
    K ≅
      (derivedCompleteRestrictionFunctor (I := I) ⋙
        derivedCompleteRestrictionRightAdjoint (I := I) G hG_mem).obj K :=
  -- Proof comment: both source and target already lie in the `IB`-complete full subcategory,
  -- so the ambient unit morphism packages directly into an isomorphism upstairs.
  ObjectProperty.isoMk
    (P := derivedCompleteObjectProperty IB)
    (X := K)
    (Y := (derivedCompleteRestrictionFunctor (I := I) ⋙
      derivedCompleteRestrictionRightAdjoint (I := I) G hG_mem).obj K)
    (@asIso _ _ _ _ (adj.unit.app K.obj) (hunit K))

/-- Helper for Lemma 15.92.25: the restricted unit components inherit the ambient naturality
square. -/
theorem derivedCompleteRestriction_unitComponentIso_naturality
    (G : DModA ⥤ DModB)
    (hG_mem :
      ∀ K : DModA,
        K.IsDerivedCompleteWithRespectTo I →
          (G.obj K).IsDerivedCompleteWithRespectTo IB)
    (adj :
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory ⊣ G)
    (hunit :
      ∀ K : (derivedCompleteObjectProperty IB).FullSubcategory,
        IsIso (adj.unit.app K.obj))
    {K L : (derivedCompleteObjectProperty IB).FullSubcategory} (f : K ⟶ L) :
    f ≫ (derivedCompleteRestriction_unitComponentIso
        (I := I) G hG_mem adj hunit L).hom =
      (derivedCompleteRestriction_unitComponentIso
        (I := I) G hG_mem adj hunit K).hom ≫
        (derivedCompleteRestrictionFunctor (I := I) ⋙
          derivedCompleteRestrictionRightAdjoint (I := I) G hG_mem).map f := by
  -- Proof comment: forgetting the full-subcategory structure reduces the claim to unit naturality
  -- in the ambient derived categories.
  apply ObjectProperty.hom_ext
  simpa
      [derivedCompleteRestrictionFunctor, derivedCompleteRestrictionRightAdjoint,
        derivedCompleteRestriction_unitComponentIso]
    using adj.unit.naturality f.hom

/-- Helper for Lemma 15.92.25: the ambient unit isomorphisms assemble into a natural isomorphism
on the restricted restriction/right-adjoint pair. -/
noncomputable def derivedCompleteRestriction_unitIso
    (G : DModA ⥤ DModB)
    (hG_mem :
      ∀ K : DModA,
        K.IsDerivedCompleteWithRespectTo I →
          (G.obj K).IsDerivedCompleteWithRespectTo IB)
    (adj :
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory ⊣ G)
    (hunit :
      ∀ K : (derivedCompleteObjectProperty IB).FullSubcategory,
        IsIso (adj.unit.app K.obj)) :
    𝟭 ((derivedCompleteObjectProperty IB).FullSubcategory) ≅
      derivedCompleteRestrictionFunctor (I := I) ⋙
        derivedCompleteRestrictionRightAdjoint (I := I) G hG_mem :=
  NatIso.ofComponents
    (derivedCompleteRestriction_unitComponentIso
      (I := I) G hG_mem adj hunit)
    (fun f ↦ derivedCompleteRestriction_unitComponentIso_naturality
      (I := I) G hG_mem adj hunit f)

/-- Helper for Lemma 15.92.25: an ambient counit isomorphism restricts to the derived-complete
subcategories, objectwise. -/
noncomputable def derivedCompleteRestriction_counitComponentIso
    (G : DModA ⥤ DModB)
    (hG_mem :
      ∀ K : DModA,
        K.IsDerivedCompleteWithRespectTo I →
          (G.obj K).IsDerivedCompleteWithRespectTo IB)
    (adj :
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory ⊣ G)
    (hcounit :
      ∀ K : (derivedCompleteObjectProperty I).FullSubcategory,
        IsIso (adj.counit.app K.obj))
    (K : (derivedCompleteObjectProperty I).FullSubcategory) :
    (derivedCompleteRestrictionRightAdjoint (I := I) G hG_mem ⋙
      derivedCompleteRestrictionFunctor (I := I)).obj K ≅ K :=
  -- Proof comment: the ambient counit already targets an `I`-complete object, so it descends to
  -- the restricted full subcategory without additional transport work.
  ObjectProperty.isoMk
    (P := derivedCompleteObjectProperty I)
    (X := (derivedCompleteRestrictionRightAdjoint (I := I) G hG_mem ⋙
      derivedCompleteRestrictionFunctor (I := I)).obj K)
    (Y := K)
    (@asIso _ _ _ _ (adj.counit.app K.obj) (hcounit K))

/-- Helper for Lemma 15.92.25: the restricted counit components inherit the ambient naturality
square. -/
theorem derivedCompleteRestriction_counitComponentIso_naturality
    (G : DModA ⥤ DModB)
    (hG_mem :
      ∀ K : DModA,
        K.IsDerivedCompleteWithRespectTo I →
          (G.obj K).IsDerivedCompleteWithRespectTo IB)
    (adj :
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory ⊣ G)
    (hcounit :
      ∀ K : (derivedCompleteObjectProperty I).FullSubcategory,
        IsIso (adj.counit.app K.obj))
    {K L : (derivedCompleteObjectProperty I).FullSubcategory} (f : K ⟶ L) :
    (derivedCompleteRestrictionRightAdjoint (I := I) G hG_mem ⋙
      derivedCompleteRestrictionFunctor (I := I)).map f ≫
        (derivedCompleteRestriction_counitComponentIso
          (I := I) G hG_mem adj hcounit L).hom =
      (derivedCompleteRestriction_counitComponentIso
        (I := I) G hG_mem adj hcounit K).hom ≫
        f := by
  -- Proof comment: after forgetting to the ambient derived category, this is exactly the
  -- counit naturality square.
  apply ObjectProperty.hom_ext
  simpa
      [derivedCompleteRestrictionFunctor, derivedCompleteRestrictionRightAdjoint,
        derivedCompleteRestriction_counitComponentIso]
    using adj.counit.naturality f.hom

/-- Helper for Lemma 15.92.25: the ambient counit isomorphisms assemble into a natural
isomorphism on the restricted right-adjoint/restriction pair. -/
noncomputable def derivedCompleteRestriction_counitIso
    (G : DModA ⥤ DModB)
    (hG_mem :
      ∀ K : DModA,
        K.IsDerivedCompleteWithRespectTo I →
          (G.obj K).IsDerivedCompleteWithRespectTo IB)
    (adj :
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory ⊣ G)
    (hcounit :
      ∀ K : (derivedCompleteObjectProperty I).FullSubcategory,
        IsIso (adj.counit.app K.obj)) :
    derivedCompleteRestrictionRightAdjoint (I := I) G hG_mem ⋙
      derivedCompleteRestrictionFunctor (I := I) ≅
        𝟭 ((derivedCompleteObjectProperty I).FullSubcategory) :=
  NatIso.ofComponents
    (derivedCompleteRestriction_counitComponentIso
      (I := I) G hG_mem adj hcounit)
    (fun f ↦ derivedCompleteRestriction_counitComponentIso_naturality
      (I := I) G hG_mem adj hcounit f)

/-- Helper for Lemma 15.92.25: once the ambient derived restriction functor admits a right
adjoint on derived-complete objects and the ambient unit/counit are isomorphisms there, the
restricted derived restriction functor is an equivalence. -/
theorem derivedCompleteRestriction_isEquivalence_of_rightAdjoint
    (G : DModA ⥤ DModB)
    (hG_mem :
      ∀ K : DModA,
        K.IsDerivedCompleteWithRespectTo I →
          (G.obj K).IsDerivedCompleteWithRespectTo IB)
    (adj :
      (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory ⊣ G)
    (hunit :
      ∀ K : (derivedCompleteObjectProperty IB).FullSubcategory,
        IsIso (adj.unit.app K.obj))
    (hcounit :
      ∀ K : (derivedCompleteObjectProperty I).FullSubcategory,
        IsIso (adj.counit.app K.obj)) :
    Functor.IsEquivalence
      (derivedCompleteRestrictionFunctor (I := I) :
        (derivedCompleteObjectProperty IB).FullSubcategory ⥤
          (derivedCompleteObjectProperty I).FullSubcategory) := by
  -- Proof comment: the restricted right adjoint together with the restricted unit and counit
  -- give the standard equivalence datum.
  exact Functor.IsEquivalence.mk'
    (derivedCompleteRestrictionRightAdjoint (I := I) G hG_mem)
    (derivedCompleteRestriction_unitIso (I := I) G hG_mem adj hunit)
    (derivedCompleteRestriction_counitIso (I := I) G hG_mem adj hcounit)

/-- Lemma 15.92.25: if `A → B` is flat, `I ⊆ A` is finitely generated, and the canonical quotient
map `A / I → B / I B` is bijective, then the restriction functor `D(B) ⥤ D(A)` induces an
equivalence from the full subcategory `D_{comp}(B, I B)` of `IB`-derived-complete complexes to the
full subcategory `D_{comp}(A, I)` of `I`-derived-complete complexes. -/
theorem derivedCompleteRestriction_isEquivalence_of_flat_of_quotientMap_bijective
    [Module.Flat A B] (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          IB
          (algebraMap A B)
          Ideal.le_comap_map)) :
    Functor.IsEquivalence
      ((derivedCompleteObjectProperty I).lift
        ((derivedCompleteObjectProperty IB).ι ⋙
          (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory)
        (fun L ↦ (isDerivedCompleteWithRespectTo_iff_restrictScalars L.obj I).2 L.property)) := by
  let adj := restrictScalars_derivedCoextendScalars_adjunction (A := A) (B := B)
  have hG_mem :
      ∀ K : DModA,
        K.IsDerivedCompleteWithRespectTo I →
          ((derivedCoextendScalars (A := A) (B := B)).obj K).IsDerivedCompleteWithRespectTo IB := by
    intro K hK
    -- Proof comment: once the derived counit is invertible on complete `A`-objects, the generic
    -- transport lemma moves derived completeness across that counit.
    exact
      rightAdjoint_preserves_isDerivedComplete_of_counit_isIso
        (I := I)
        (G := derivedCoextendScalars (A := A) (B := B))
        adj
        (fun X hX ↦
          derivedCoextendScalars_counit_isIso_of_isDerivedComplete
            (I := I) hI hquot X hX)
        K hK
  have hunit :
      ∀ K : (derivedCompleteObjectProperty IB).FullSubcategory,
        IsIso (adj.unit.app K.obj) := by
    intro K
    -- Proof comment: the source proof's split coevaluation on `B`-side K-injective models is the
    -- remaining input needed to show the ambient unit is invertible on complete objects.
    exact
      derivedCoextendScalars_unit_isIso_of_isDerivedComplete
        (I := I) hI hquot K
  have hcounit :
      ∀ K : (derivedCompleteObjectProperty I).FullSubcategory,
        IsIso (adj.counit.app K.obj) := by
    intro K
    -- Proof comment: this is exactly the Čech-based evaluation isomorphism from the source
    -- proof, now phrased as the ambient counit on the complete subcategory.
    exact
      derivedCoextendScalars_counit_isIso_of_isDerivedComplete
        (I := I) hI hquot K.obj K.property
  have hEquiv :
      Functor.IsEquivalence (derivedCompleteRestrictionFunctor (I := I)) := by
    -- Proof comment: with the ambient adjunction and the restricted unit/counit isomorphisms in
    -- place, the generic categorical packaging produces the desired equivalence of full
    -- subcategories.
    exact
      derivedCompleteRestriction_isEquivalence_of_rightAdjoint
        (I := I)
        (G := derivedCoextendScalars (A := A) (B := B))
        hG_mem
        adj
        hunit
        hcounit
  simpa [derivedCompleteRestrictionFunctor] using hEquiv

end

end CategoryTheory
