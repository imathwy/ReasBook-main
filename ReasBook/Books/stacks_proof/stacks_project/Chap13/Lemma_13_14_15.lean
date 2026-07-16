import Mathlib
import stacks_proof.stacks_project.Chap04.Definition_4_22_1
import stacks_proof.stacks_project.Chap04.Lemma_4_22_11
import stacks_proof.stacks_project.Chap04.Lemma_4_22_13
import stacks_proof.stacks_project.Chap04.Definition_4_27_20
import stacks_proof.stacks_project.Chap04.Remark_4_27_7
import stacks_proof.stacks_project.Chap04.Remark_4_27_15
import stacks_proof.stacks_project.Chap13.Lemma_13_5_8
import stacks_proof.stacks_project.Chap13.Lemma_13_14_14

open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits

open scoped MorphismPropertyUnder MorphismPropertyOver

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

/- Domain-style sampling for Lemma 13.14.15:
- primary domain: pointwise derived-functor existence criteria from a source-facing subset of
  good objects for a localization class;
- inspected owner declarations:
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`,
  `Functor.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt`,
  `Functor.hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt`;
- best owner abstraction: the public API should live directly on the canonical derived-functor
  owner predicates above, with the subset hypotheses carried by `ObjectProperty D`.

Source/core/bridge triage:
- `source-facing`: the subset criteria from the Stacks proof;
- `core/canonical`: the derived-functor owner predicates
  `ComputesRightDerivedAt` / `ComputesLeftDerivedAt` and their pointwise-existence companions;
- `bridge/view`: the four theorems below, which translate the subset hypotheses into those owner
  predicates without introducing a second packaging layer.
-/

variable {D : Type u₁} {D' : Type u₂}
variable [Category.{v₁} D] [Category.{v₂} D']
variable (F : D ⥤ D') (S : MorphismProperty D)
variable [S.IsSaturatedMultiplicativeSystem]

/-- Helper for Lemma 13.14.15: a commutative denominator square yields the equality needed to
construct the corresponding morphism in the costructured-arrow indexing category. -/
private theorem denominatorCostructuredArrowHomEq {X X' X'' : D}
    (s : X ⟶ X') (s' : X ⟶ X'') (hs : S s) (hs' : S s') (f : X' ⟶ X'')
    (hf : s ≫ f = s') :
    S.Q.map f ≫ (Localization.isoOfHom S.Q S s' hs').inv =
      (Localization.isoOfHom S.Q S s hs).inv := by
  -- Proof comment: localize the denominator triangle and whisker by the inverse denominator
  -- isomorphisms to isolate the required comparison morphism.
  have hsq := congrArg
    (fun k ↦
      (Localization.isoOfHom S.Q S s hs).inv ≫ k ≫
        (Localization.isoOfHom S.Q S s' hs').inv)
    (congrArg (fun k ↦ S.Q.map k) hf)
  simpa [Functor.map_comp, Category.assoc, Localization.isoOfHom_hom] using hsq

/-- Helper for Lemma 13.14.15: a commutative denominator square yields the equality needed to
construct the corresponding morphism in the structured-arrow indexing category. -/
private theorem denominatorStructuredArrowHomEq {X X' X'' : D}
    (s : X' ⟶ X) (s' : X'' ⟶ X) (hs : S s) (hs' : S s') (f : X' ⟶ X'')
    (hf : f ≫ s' = s) :
    (Localization.isoOfHom S.Q S s hs).inv ≫ S.Q.map f =
      (Localization.isoOfHom S.Q S s' hs').inv := by
  -- Proof comment: this is the dual normalization: localize the triangle and cancel the two
  -- denominator isomorphisms.
  have hsq := congrArg
    (fun k ↦
      (Localization.isoOfHom S.Q S s hs).inv ≫ k ≫
        (Localization.isoOfHom S.Q S s' hs').inv)
    (congrArg (fun k ↦ S.Q.map k) hf)
  simpa [Functor.map_comp, Category.assoc, Localization.isoOfHom_hom] using hsq

/-- Helper for Lemma 13.14.15: any ambient right-indexing object receives a morphism from one
coming from an actual arrow into `X`. -/
private theorem costructuredArrowExistsHomFromPlainMap {X : D}
    [S.HasRightCalculusOfFractions] (g : CostructuredArrow S.Q (S.Q.obj X)) :
    ∃ (X' : D) (s : X' ⟶ g.left) (_ : S s) (f : X' ⟶ X),
      S.Q.map s ≫ g.hom = S.Q.map f := by
  -- Proof comment: represent `g.hom` by a right fraction in the localization; its numerator
  -- and denominator give the desired plain-map presentation.
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction S.Q S g.hom
  refine ⟨ψ.X', ψ.s, ψ.hs, ψ.f, ?_⟩
  simpa [hψ] using rfl

/-- Helper for Lemma 13.14.15: a right fraction can be completed to a common-target denominator
square. -/
private theorem rightFractionExistsTargetDenominatorSquare {A X : D}
    [S.HasLeftCalculusOfFractions] (ψ : S.RightFraction A X) :
    ∃ (X' : D) (s : X ⟶ X') (_ : S s) (f : A ⟶ X'),
      ψ.s ≫ f = ψ.f ≫ s := by
  -- Proof comment: pass to the opposite left fraction and then unop the common-target square.
  obtain ⟨φ, hφ⟩ := ψ.op.exists_rightFraction
  refine ⟨Opposite.unop φ.X', φ.s.unop, φ.hs, φ.f.unop, ?_⟩
  simpa using (congrArg Quiver.Hom.unop hφ).symm

/-- Helper for Lemma 13.14.15: every ambient right-indexing object maps to one indexed by an
actual denominator out of `X`. -/
private theorem costructuredArrowExistsHomToDenominator {X : D}
    [S.HasRightCalculusOfFractions] [S.HasLeftCalculusOfFractions]
    (g : CostructuredArrow S.Q (S.Q.obj X)) :
    ∃ (X' : D) (s : X ⟶ X') (hs : S s),
      Nonempty (g ⟶ CostructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv)) := by
  -- Proof comment: first rewrite `g` as a plain-map stage, then complete that presentation to a
  -- common-target denominator square.
  rcases costructuredArrowExistsHomFromPlainMap (S := S) g with ⟨A, t, ht, u, hu⟩
  rcases rightFractionExistsTargetDenominatorSquare (S := S)
      (MorphismProperty.RightFraction.mk t ht u) with ⟨X', s, hs, f, hsq⟩
  refine ⟨X', s, hs, ⟨CostructuredArrow.homMk f ?_⟩⟩
  have hcomp : g.hom ≫ S.Q.map s = S.Q.map f := by
    letI : IsIso (S.Q.map t) := Localization.inverts S.Q S t ht
    apply (cancel_epi (S.Q.map t)).1
    calc
      S.Q.map t ≫ (g.hom ≫ S.Q.map s) = (S.Q.map t ≫ g.hom) ≫ S.Q.map s := by
        simp [Category.assoc]
      _ = S.Q.map u ≫ S.Q.map s := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ S.Q.map s) hu
      _ = S.Q.map (u ≫ s) := by
        simp [Functor.map_comp]
      _ = S.Q.map (t ≫ f) := by
        rw [hsq]
      _ = S.Q.map t ≫ S.Q.map f := by
        simp [Functor.map_comp]
  letI : IsIso (S.Q.map s) := Localization.inverts S.Q S s hs
  apply (cancel_mono (S.Q.map s)).1
  calc
    (S.Q.map f ≫ (Localization.isoOfHom S.Q S s hs).inv) ≫ S.Q.map s = S.Q.map f := by
      simp [Category.assoc]
    _ = g.hom ≫ S.Q.map s := hcomp.symm

/-- Helper for Lemma 13.14.15: every ambient left-indexing object receives a morphism from one
indexed by an actual denominator into `Y`. -/
private theorem structuredArrowExistsHomFromDenominator {Y : D}
    [S.HasRightCalculusOfFractions] (g : StructuredArrow (S.Q.obj Y) S.Q) :
    ∃ (Y' : D) (s : Y' ⟶ Y) (hs : S s),
      Nonempty (StructuredArrow.mk ((Localization.isoOfHom S.Q S s hs).inv) ⟶ g) := by
  -- Proof comment: a right-fraction presentation of `g.hom` already has the denominator
  -- orientation needed for a morphism from a denominator stage.
  obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction S.Q S g.hom
  refine ⟨ψ.X', ψ.s, ψ.hs, ?_⟩
  refine ⟨StructuredArrow.homMk ψ.f ?_⟩
  calc
    (Localization.isoOfHom S.Q S ψ.s ψ.hs).inv ≫ S.Q.map ψ.f =
        ψ.map S.Q (Localization.inverts S.Q S) := by
          rfl
    _ = g.hom := hψ.symm

section Right

variable (I : ObjectProperty D)

/-- Helper for Lemma 13.14.15: the good denominator stages out of `X` are those whose targets lie
in `I`. -/
private abbrev goodTargetDenominatorProperty
    (X : D) : ObjectProperty (X / S) :=
  fun U ↦ I U.right

/-- Helper for Lemma 13.14.15: every denominator out of `X` refines to one whose target lies in
`I`, so the good full subcategory of `X / S` is final. -/
private theorem goodTargetDenominatorInclusionFinal
    (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s)
    (X : D) :
    Functor.Final (ObjectProperty.ι (goodTargetDenominatorProperty (I := I) (S := S) X)) := by
  let P := goodTargetDenominatorProperty (I := I) (S := S) X
  let inclusion := ObjectProperty.ι P
  let h :
      ∀ U : X / S, ∃ V : P.FullSubcategory, Nonempty (U ⟶ inclusion.obj V) := by
    intro U
    rcases hI_reaches U.right with ⟨Y, u, hY, hu⟩
    let V : P.FullSubcategory :=
      ⟨MorphismProperty.Under.mk (P := S) (Q := ⊤) (X := X)
        (U.hom ≫ u) (S.comp_mem _ _ U.prop hu), hY⟩
    refine ⟨V, ?_⟩
    -- Proof comment: the refinement `U.hom ≫ u` gives a morphism from the original denominator to
    -- a good one landing in `I`.
    exact ⟨MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := X) u rfl⟩
  -- Proof comment: the good denominator subcategory is final by the standard filtered
  -- full-subcategory criterion.
  exact Functor.final_of_exists_of_isFiltered_of_fullyFaithful inclusion h

/-- Helper for Lemma 13.14.15: on good denominator stages out of `X`, the restricted diagram is
explicitly coconed by `F.obj X` via the inverses of the denominator maps. -/
private theorem goodTargetRestrictedDiagram_map
    {X : D}
    {U V : (goodTargetDenominatorProperty (I := I) (S := S) X).FullSubcategory}
    (f : U ⟶ V) :
    ((ObjectProperty.ι (goodTargetDenominatorProperty (I := I) (S := S) X) ⋙
        MorphismProperty.Under.forget S ⊤ X ⋙ CategoryTheory.Under.forget X ⋙ F).map f) =
      F.map f.1.right := by
  -- Proof comment: the restricted functor is the evident forgetful composite, so on morphisms it
  -- is literally the map of the underlying right edge.
  rfl

/-- Helper for Lemma 13.14.15: on good denominator stages out of `X`, the restricted diagram is
explicitly coconed by `F.obj X` via the inverses of the denominator maps. -/
private noncomputable def goodTargetRestrictedCocone
    {X : D} (hX : I X)
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s)) :
    Cocone
      (ObjectProperty.ι (goodTargetDenominatorProperty (I := I) (S := S) X) ⋙
        MorphismProperty.Under.forget S ⊤ X ⋙ CategoryTheory.Under.forget X ⋙ F) where
  pt := F.obj X
  ι :=
    { app := fun U ↦ by
        -- Proof comment: each good denominator `U.1.hom : X ⟶ U.1.right` is inverted by `F`, so
        -- its inverse gives the cocone leg back to `F.obj X`.
        letI : IsIso (F.map U.1.hom) := hI_isIso U.1.hom hX U.2 U.1.prop
        exact (asIso (F.map U.1.hom)).inv
      naturality := fun U V f ↦ by
        -- Proof comment: the commutative triangle in `X / S` becomes
        -- `F.map U.1.hom ≫ F.map f.1.right = F.map V.1.hom`, so cancel the good denominator on
        -- the left.
        letI : IsIso (F.map U.1.hom) := hI_isIso U.1.hom hX U.2 U.1.prop
        letI : IsIso (F.map V.1.hom) := hI_isIso V.1.hom hX V.2 V.1.prop
        change
          ((ObjectProperty.ι (goodTargetDenominatorProperty (I := I) (S := S) X) ⋙
              MorphismProperty.Under.forget S ⊤ X ⋙ CategoryTheory.Under.forget X ⋙ F).map f) ≫
              (asIso (F.map V.1.hom)).inv =
            (asIso (F.map U.1.hom)).inv ≫
              ((Functor.const _).obj (F.obj X)).map f
        simp only [goodTargetRestrictedDiagram_map (F := F) (S := S) (I := I) (f := f),
          Functor.const_obj_obj]
        have hw : F.map U.1.hom ≫ F.map f.1.right = F.map V.1.hom := by
          simpa [Functor.map_comp] using congrArg (fun k ↦ F.map k) (MorphismProperty.Under.w f.1)
        -- Proof comment: whisker the mapped commutative triangle by the inverse denominator maps.
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ (asIso (F.map U.1.hom)).inv ≫ k ≫ (asIso (F.map V.1.hom)).inv)
            hw }

/-- Helper for Lemma 13.14.15: the explicit restricted cocone leg at a good denominator stage is
the inverse of the denominator map under `F`. -/
private theorem goodTargetRestrictedCocone_app
    {X : D} (hX : I X)
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s))
    (U : (goodTargetDenominatorProperty (I := I) (S := S) X).FullSubcategory) :
    letI : IsIso (F.map U.1.hom) := hI_isIso U.1.hom hX U.2 U.1.prop
    (goodTargetRestrictedCocone (F := F) (S := S) (I := I) hX hI_isIso).ι.app U =
      (asIso (F.map U.1.hom)).inv := by
  -- Proof comment: this is just the defining formula of `goodTargetRestrictedCocone`.
  letI : IsIso (F.map U.1.hom) := hI_isIso U.1.hom hX U.2 U.1.prop
  rfl

/-- Helper for Lemma 13.14.15: the explicit restricted cocone on the good denominator
subcategory is already essentially constant with vertex `F.obj X`. -/
private theorem goodTargetRestrictedCocone_essentiallyConstant
    {X : D} (hX : I X)
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s)) :
    IsEssentiallyConstantFilteredCocone
      (goodTargetRestrictedCocone (F := F) (S := S) (I := I) hX hI_isIso) := by
  rw [isEssentiallyConstantFilteredCocone_iff]
  let i₀ : (goodTargetDenominatorProperty (I := I) (S := S) X).FullSubcategory :=
    ⟨MorphismProperty.Under.mk (P := S) (Q := ⊤) (X := X) (𝟙 X) (S.id_mem X), hX⟩
  refine ⟨i₀, 𝟙 (F.obj X), ?_, ?_⟩
  · -- Proof comment: the distinguished identity denominator has cocone leg the inverse of
    -- `F.map (𝟙 X)`, which simplifies to the identity.
    letI : IsIso (F.map (𝟙 X)) := hI_isIso (𝟙 X) hX hX (S.id_mem X)
    rw [goodTargetRestrictedCocone_app (F := F) (S := S) (I := I) hX hI_isIso i₀]
    change 𝟙 (F.obj X) ≫ CategoryTheory.inv (F.map (𝟙 X)) = 𝟙 (F.obj X)
    simpa [Functor.map_id]
  · intro U
    let ik : i₀ ⟶ U :=
      ObjectProperty.homMk
        (MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := X) U.1.hom (by
          change (𝟙 X) ≫ U.1.hom = U.1.hom
          simp))
    refine ⟨U, ik, 𝟙 U, ?_⟩
    letI : IsIso (F.map U.1.hom) := hI_isIso U.1.hom hX U.2 U.1.prop
    -- Proof comment: the map from the identity denominator to `U` is exactly `U.1.hom`, so the
    -- cocone leg followed by the diagram map along that morphism is `inv ≫ hom = 𝟙`.
    rw [Functor.map_id,
      goodTargetRestrictedCocone_app (F := F) (S := S) (I := I) hX hI_isIso U,
      goodTargetRestrictedDiagram_map (F := F) (S := S) (I := I) (f := ik)]
    letI : IsIso (F.map U.1.hom) := hI_isIso U.1.hom hX U.2 U.1.prop
    have hik : ik.hom.right = U.1.hom := by
      rfl
    rw [hik]
    calc
      𝟙 (F.obj U.1.right) = CategoryTheory.inv (F.map U.1.hom) ≫ F.map U.1.hom := by
        simpa using (IsIso.inv_hom_id (F.map U.1.hom)).symm
      _ = CategoryTheory.inv (F.map U.1.hom) ≫ 𝟙 (F.obj X) ≫ F.map U.1.hom := by
        simp

/-- Helper for Lemma 13.14.15: on the good full subcategory of `X / S`, the denominator diagram is
essentially constant with value `F.obj X`. -/
private theorem goodTargetRestrictedDiagram_essentiallyConstant
    {X : D} (hX : I X)
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s)) :
    IsEssentiallyConstantFilteredDiagram
      (ObjectProperty.ι (goodTargetDenominatorProperty (I := I) (S := S) X) ⋙
        MorphismProperty.Under.forget S ⊤ X ⋙ CategoryTheory.Under.forget X ⋙ F) := by
  -- Proof comment: the strengthened cocone-level helper already packages the required witness.
  exact
    ⟨goodTargetRestrictedCocone (F := F) (S := S) (I := I) hX hI_isIso,
      goodTargetRestrictedCocone_essentiallyConstant
        (F := F) (S := S) (I := I) hX hI_isIso⟩

/-- Helper for Lemma 13.14.15: the ordinary denominator category `X / S` maps to the ambient
costructured-arrow indexing category for `RF(X)` by sending a denominator to its localized
inverse. -/
private noncomputable def targetDenominatorToCostructuredArrow (X : D) :
    (X / S) ⥤ CostructuredArrow S.Q (S.Q.obj X) where
  obj U := CostructuredArrow.mk ((Localization.isoOfHom S.Q S U.hom U.prop).inv)
  map := fun {U V} f ↦
    CostructuredArrow.homMk f.right
      (denominatorCostructuredArrowHomEq (S := S) U.hom V.hom U.prop V.prop f.right
        (MorphismProperty.Under.w f))

/-- Helper for Lemma 13.14.15: the denominator functor `X / S ⥤ CostructuredArrow S.Q (S.Q.obj X)`
is final. -/
private theorem targetDenominatorToCostructuredArrow_final
    (X : D) [S.HasRightCalculusOfFractions] [S.HasLeftCalculusOfFractions] :
    Functor.Final (targetDenominatorToCostructuredArrow (S := S) X) := by
  let T := targetDenominatorToCostructuredArrow (S := S) X
  -- Proof comment: every ambient stage refines to an actual denominator stage, and two such
  -- refinements into the same denominator equalize after refining that denominator once more.
  refine Functor.final_of_exists_of_isFiltered T ?_ ?_
  · intro g
    rcases costructuredArrowExistsHomToDenominator (S := S) (X := X) g with
      ⟨X', s, hs, ⟨α⟩⟩
    exact ⟨MorphismProperty.Under.mk (P := S) (Q := ⊤) (X := X) s hs, ⟨α⟩⟩
  · intro g U α β
    have hα :
        S.Q.map α.left = g.hom ≫ S.Q.map U.hom := by
      have h :=
        congrArg (fun k ↦ k ≫ S.Q.map U.hom) α.w
      simpa [T, targetDenominatorToCostructuredArrow, Category.assoc, Localization.isoOfHom_hom]
        using h
    have hβ :
        S.Q.map β.left = g.hom ≫ S.Q.map U.hom := by
      have h :=
        congrArg (fun k ↦ k ≫ S.Q.map U.hom) β.w
      simpa [T, targetDenominatorToCostructuredArrow, Category.assoc, Localization.isoOfHom_hom]
        using h
    obtain ⟨Y, t, ht, hfac⟩ :=
      (MorphismProperty.map_eq_iff_postcomp (L := S.Q) (W := S) α.left β.left).1
        (hα.trans hβ.symm)
    let V : X / S :=
      MorphismProperty.Under.mk (P := S) (Q := ⊤) (X := X) (U.hom ≫ t)
        (S.comp_mem _ _ U.prop ht)
    let γ : U ⟶ V :=
      MorphismProperty.Under.homMk (P := S) (Q := ⊤) (X := X) t rfl
    refine ⟨V, γ, ?_⟩
    apply CostructuredArrow.hom_ext
    simpa [T, targetDenominatorToCostructuredArrow, γ, V, Category.assoc] using hfac

/-- Helper for Lemma 13.14.15: the restriction of `F` to the full subcategory on `I` inverts the
restricted localization system `S.inverseImage I.ι`. -/
private theorem restrictedInvertsOnGoodSubset
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s)) :
    (fullSubcategoryLocalizationSystem I S).IsInvertedBy (I.ι ⋙ F) := by
  intro X Y f hf
  -- Proof comment: a restricted denominator is just an ambient denominator whose endpoints lie in
  -- `I`, so the given hypothesis applies directly to its underlying morphism.
  change IsIso (F.map f.hom)
  exact hI_isIso f.hom X.property Y.property
    (by simpa [fullSubcategoryLocalizationSystem] using hf)

/-- Helper for Lemma 13.14.15: the outgoing good-subset hypothesis supplies right resolutions for
the good full-subcategory inclusion localizer. -/
private theorem rightSubsetLocalizer_hasRightResolutions
    (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s) :
    (fullSubcategoryLocalizerMorphism I S).HasRightResolutions := by
  intro X
  rcases hI_reaches X with ⟨X', s, hX', hs⟩
  let Xgood : I.FullSubcategory := ⟨X', hX'⟩
  -- Proof comment: the chosen denominator `s : X ⟶ X'` with `X' ∈ I` is exactly a right
  -- resolution of `X` for the inclusion of the good full subcategory.
  exact ⟨{ X₁ := Xgood
           w := s
           hw := hs }⟩

/-- Helper for Lemma 13.14.15: after localizing the full subcategory on `I`, the restricted
inclusion `I.ι ⋙ S.Q` is itself a localization functor. -/
private theorem restrictedInclusionIsLocalization
    (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), I X' ∧ S s) :
    (I.ι ⋙ S.Q).IsLocalization (fullSubcategoryLocalizationSystem I S) := by
  let Φ := fullSubcategoryLocalizerMorphism I S
  have hCover :
      ∀ X : D, ∃ (X' : I.FullSubcategory) (s : I.ι.obj X' ⟶ X), S s := by
    intro X
    rcases hI_reaches X with ⟨X', s, hX', hs⟩
    exact ⟨⟨X', hX'⟩, s, hs⟩
  letI : Φ.IsLocalizedEquivalence :=
    fullSubcategoryLocalizerMorphism_isLocalizedEquivalence I S hCover
  -- Proof comment: once the good inclusion is known to induce an equivalence on localized
  -- categories, the composite `I.ι ⋙ S.Q` is the canonical localization functor of the
  -- restricted system.
  simpa [Φ, fullSubcategoryLocalizerMorphism] using
    (inferInstance :
      (Φ.functor ⋙ S.Q).IsLocalization (fullSubcategoryLocalizationSystem I S))

/-- Helper for Lemma 13.14.15: on the full subcategory of good objects, the restricted functor
already computes its right derived functor everywhere because it inverts the restricted
denominators. -/
private theorem restrictedComputesRightDerivedOnGoodSubset
    (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s)
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s))
    (X : I.FullSubcategory) :
    (I.ι ⋙ F).ComputesRightDerivedAt (fullSubcategoryLocalizationSystem I S) X := by
  let W := fullSubcategoryLocalizationSystem I S
  let G : I.FullSubcategory ⥤ D' := I.ι ⋙ F
  have hInv : W.IsInvertedBy G :=
    restrictedInvertsOnGoodSubset (F := F) (S := S) I hI_isIso
  letI : G.HasPointwiseRightDerivedFunctor W :=
    Functor.hasPointwiseRightDerivedFunctor_of_inverts G hInv
  have hUnitNatIso : IsIso (G.totalRightDerivedUnit W.Q W) := by
    -- Proof comment: once `G` inverts the restricted system, its canonical localized factor is a
    -- right derived functor and the comparison unit is an isomorphism.
    exact
      Functor.isIso_of_isRightDerivedFunctor_of_inverts
        (W := W) (L := W.Q)
        (RF := G.totalRightDerived W.Q W)
        (α := G.totalRightDerivedUnit W.Q W) hInv
  have hUnitIso : IsIso ((G.totalRightDerivedUnit W.Q W).app X) := by
    infer_instance
  -- Proof comment: transport the unit isomorphism back to the source-facing computation owner.
  exact
    (Functor.computesRightDerivedAt_iff (F := G) (S := W) (X := X)).2 hUnitIso

/-- Lemma 13.14.15 (2): under the subset criterion for right derived functors, any object of the
chosen good subset computes the right derived functor of `F` with respect to `S`. -/
@[stacks 06XN]
theorem computesRightDerivedAt_of_mem_subset
    (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s)
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s))
    {X : D} (hX : I X) :
    F.ComputesRightDerivedAt S X := by
  let J := goodTargetDenominatorProperty (I := I) (S := S) X
  let inclusion := ObjectProperty.ι J
  let U₀ : J.FullSubcategory :=
    ⟨MorphismProperty.Under.mk (P := S) (Q := ⊤) (X := X) (𝟙 X) (S.id_mem X), hX⟩
  letI : Functor.Final inclusion :=
    goodTargetDenominatorInclusionFinal (S := S) (I := I) hI_reaches X
  let cGood := goodTargetRestrictedCocone (F := F) (S := S) (I := I) hX hI_isIso
  have hcGood : IsColimit cGood :=
    (goodTargetRestrictedCocone_essentiallyConstant
      (F := F) (S := S) (I := I) hX hI_isIso).isColimit
  let cUnder :
      Cocone
        (MorphismProperty.Under.forget S ⊤ X ⋙ CategoryTheory.Under.forget X ⋙ F) :=
    (Functor.Final.extendCocone (F := inclusion)).obj cGood
  have hcUnder : IsColimit cUnder :=
    ((Functor.Final.isColimitExtendCoconeEquiv
      (F := inclusion) cGood).symm hcGood)
  let T := targetDenominatorToCostructuredArrow (S := S) X
  letI : Functor.Final T := targetDenominatorToCostructuredArrow_final (S := S) X
  let cUnder' :
      Cocone (T ⋙ CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) := cUnder
  let cAmbient : ColimitCocone (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) :=
    { cocone := (Functor.Final.extendCocone (F := T)).obj cUnder'
      isColimit :=
        ((Functor.Final.isColimitExtendCoconeEquiv
          (F := T) cUnder').symm hcUnder) }
  letI : HasColimit (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F) := HasColimit.mk cAmbient
  letI : F.HasPointwiseRightDerivedFunctorAt S X :=
    (Functor.hasPointwiseRightDerivedFunctorAt_iff (F := F) (L := S.Q) (W := S) X).2 inferInstance
  have hUnderId :
      cUnder.ι.app U₀.1 = cGood.ι.app U₀ := by
    -- Proof comment: extending along the final good-subcategory inclusion does not change the
    -- cocone leg at the chosen identity denominator object.
    simpa [cUnder, inclusion, J] using
      (Functor.Final.extendCocone_obj_ι_app' (F := inclusion) cGood
        (X := U₀.1) (Y := U₀) (f := 𝟙 U₀.1))
  have hAmbientId :
      cAmbient.cocone.ι.app
          (CostructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)) =
        cUnder.ι.app U₀.1 := by
    -- Proof comment: extending from the ordinary denominator category to the ambient
    -- costructured-arrow category again preserves the identity-stage leg.
    simpa [cAmbient, T, targetDenominatorToCostructuredArrow, U₀] using
      (Functor.Final.extendCocone_obj_ι_app' (F := T) cUnder'
        (X := T.obj U₀.1) (Y := U₀.1) (f := 𝟙 (T.obj U₀.1)))
  have hExplicit :
      cAmbient.cocone.ι.app
          (CostructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)) =
        (asIso (F.map (𝟙 X))).inv := by
    rw [hAmbientId, hUnderId]
    exact goodTargetRestrictedCocone_app (F := F) (S := S) (I := I) hX hI_isIso U₀
  have hLegComp :
      rightDerivedValueLeg S F (𝟙 X) (S.id_mem X) ≫
          (colimit.isoColimitCocone cAmbient).hom =
        (asIso (F.map (𝟙 X))).inv := by
    simpa [rightDerivedValueLeg, cAmbient] using
      (colimit.isoColimitCocone_ι_hom cAmbient
        (CostructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv))).trans
        hExplicit
  have hLegIso :
      IsIso (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X)) := by
    have hCompIso :
        IsIso
          (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X) ≫
            (colimit.isoColimitCocone cAmbient).hom) := by
      rw [hLegComp]
      infer_instance
    exact
      (isIso_comp_right_iff
        (rightDerivedValueLeg S F (𝟙 X) (S.id_mem X))
        ((colimit.isoColimitCocone cAmbient).hom)).1 hCompIso
  -- Proof comment: the explicit ambient colimit cocone defines `RF(X)` at `X`, and its identity
  -- denominator leg is the inverse of `F.map (𝟙 X)`.
  exact ⟨hLegIso⟩

/-- Lemma 13.14.15 (1): if every object reaches an object of `I` by a denominator in `S`, and if
`F` inverts denominators between objects of `I`, then `F` has pointwise right derived functors
with respect to `S`. -/
@[stacks 06XN]
theorem hasPointwiseRightDerivedFunctor_of_subset :
    (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s) →
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s)) →
    F.HasPointwiseRightDerivedFunctor S :=
  fun hI_reaches hI_isIso ↦
    F.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt S
      (fun X ↦ by
        rcases hI_reaches X with ⟨X', s, hX', hs⟩
        exact
          ⟨X', s, hs,
            computesRightDerivedAt_of_mem_subset F S I hI_reaches hI_isIso hX'⟩)

end Right

section Left

variable (P : ObjectProperty D)

/-- Helper for Lemma 13.14.15: the good denominator stages into `X` are those whose sources lie in
`P`. -/
private abbrev goodSourceDenominatorProperty
    (X : D) : ObjectProperty (S / X) :=
  fun U ↦ P U.left

/-- Helper for Lemma 13.14.15: every denominator into `X` can be refined from one whose source
lies in `P`, so the good full subcategory of `S / X` is initial. -/
private theorem goodSourceDenominatorInclusionInitial
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (X : D) :
    Functor.Initial (ObjectProperty.ι (goodSourceDenominatorProperty (P := P) (S := S) X)) := by
  let G := goodSourceDenominatorProperty (P := P) (S := S) X
  let inclusion := ObjectProperty.ι G
  let h :
      ∀ U : S / X, ∃ V : G.FullSubcategory, Nonempty (inclusion.obj V ⟶ U) := by
    intro U
    rcases hP_reaches U.left with ⟨Y, u, hY, hu⟩
    let V : G.FullSubcategory :=
      ⟨MorphismProperty.Over.mk (P := S) (Q := ⊤) (X := X)
        (u ≫ U.hom) (S.comp_mem _ _ hu U.prop), hY⟩
    refine ⟨V, ?_⟩
    -- Proof comment: precomposing the given denominator by a good source stage yields the desired
    -- morphism from the good full subcategory back to `U`.
    exact ⟨MorphismProperty.Over.homMk (P := S) (Q := ⊤) (X := X) u rfl⟩
  -- Proof comment: the good denominator subcategory is initial by the standard cofiltered
  -- full-subcategory criterion.
  exact Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful inclusion h

/-- Helper for Lemma 13.14.15: on good denominator stages into `X`, the restricted diagram is
explicitly coned by `F.obj X` via the inverses of the denominator maps. -/
private theorem goodSourceRestrictedDiagram_map
    {X : D}
    {U V : (goodSourceDenominatorProperty (P := P) (S := S) X).FullSubcategory}
    (f : U ⟶ V) :
    ((ObjectProperty.ι (goodSourceDenominatorProperty (P := P) (S := S) X) ⋙
        MorphismProperty.Over.forget S ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ F).map f) =
      F.map f.1.left := by
  -- Proof comment: this restricted functor is again just the forgetful composite, now reading
  -- the left edge of a morphism in `S / X`.
  rfl

/-- Helper for Lemma 13.14.15: on good denominator stages into `X`, the restricted diagram is
explicitly coned by `F.obj X` via the inverses of the denominator maps. -/
private noncomputable def goodSourceRestrictedCone
    {X : D} (hX : P X)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s)) :
    Cone
      (ObjectProperty.ι (goodSourceDenominatorProperty (P := P) (S := S) X) ⋙
        MorphismProperty.Over.forget S ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ F) where
  pt := F.obj X
  π :=
    { app := fun U ↦ by
        -- Proof comment: each good source denominator `U.1.hom : U.1.left ⟶ X` is inverted by
        -- `F`, so its inverse gives the cone projection out of `F.obj X`.
        letI : IsIso (F.map U.1.hom) := hP_isIso U.1.hom U.2 hX U.1.prop
        exact (asIso (F.map U.1.hom)).inv
      naturality := fun U V f ↦ by
        -- Proof comment: the commutative triangle in `S / X` becomes
        -- `F.map f.1.left ≫ F.map V.1.hom = F.map U.1.hom`, so cancel the good denominator on
        -- the right.
        letI : IsIso (F.map U.1.hom) := hP_isIso U.1.hom U.2 hX U.1.prop
        letI : IsIso (F.map V.1.hom) := hP_isIso V.1.hom V.2 hX V.1.prop
        change
          ((Functor.const _).obj (F.obj X)).map f ≫ (asIso (F.map V.1.hom)).inv =
            (asIso (F.map U.1.hom)).inv ≫
              ((ObjectProperty.ι (goodSourceDenominatorProperty (P := P) (S := S) X) ⋙
                  MorphismProperty.Over.forget S ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ F).map f)
        simp only [goodSourceRestrictedDiagram_map (F := F) (S := S) (P := P) (f := f),
          Functor.const_obj_obj]
        have hw : F.map f.1.left ≫ F.map V.1.hom = F.map U.1.hom := by
          simpa [Functor.map_comp] using congrArg (fun k ↦ F.map k) (MorphismProperty.Over.w f.1)
        -- Proof comment: whisker the mapped commutative triangle by the inverse denominator maps.
        symm
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ (asIso (F.map U.1.hom)).inv ≫ k ≫ (asIso (F.map V.1.hom)).inv)
            hw }

/-- Helper for Lemma 13.14.15: the explicit restricted cone projection at a good denominator
stage is the inverse of the denominator map under `F`. -/
private theorem goodSourceRestrictedCone_app
    {X : D} (hX : P X)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s))
    (U : (goodSourceDenominatorProperty (P := P) (S := S) X).FullSubcategory) :
    letI : IsIso (F.map U.1.hom) := hP_isIso U.1.hom U.2 hX U.1.prop
    (goodSourceRestrictedCone (F := F) (S := S) (P := P) hX hP_isIso).π.app U =
      (asIso (F.map U.1.hom)).inv := by
  -- Proof comment: this is the defining formula of `goodSourceRestrictedCone`.
  letI : IsIso (F.map U.1.hom) := hP_isIso U.1.hom U.2 hX U.1.prop
  rfl

/-- Helper for Lemma 13.14.15: the explicit restricted cone on the good denominator subcategory
is already essentially constant with vertex `F.obj X`. -/
private theorem goodSourceRestrictedCone_essentiallyConstant
    {X : D} (hX : P X)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s)) :
    IsEssentiallyConstantCofilteredCone
      (goodSourceRestrictedCone (F := F) (S := S) (P := P) hX hP_isIso) := by
  rw [isEssentiallyConstantCofilteredCone_iff]
  let i₀ : (goodSourceDenominatorProperty (P := P) (S := S) X).FullSubcategory :=
    ⟨MorphismProperty.Over.mk (P := S) (Q := ⊤) (X := X) (𝟙 X) (S.id_mem X), hX⟩
  refine ⟨i₀, ?_, ?_⟩
  · refine
      { retraction := 𝟙 (F.obj X)
        id := ?_ }
    -- Proof comment: the distinguished identity denominator has cone projection the inverse of
    -- `F.map (𝟙 X)`, hence the identity.
    letI : IsIso (F.map (𝟙 X)) := hP_isIso (𝟙 X) hX hX (S.id_mem X)
    rw [goodSourceRestrictedCone_app (F := F) (S := S) (P := P) hX hP_isIso i₀]
    change (asIso (F.map (𝟙 X))).inv ≫ 𝟙 (F.obj X) = 𝟙 (F.obj X)
    simpa [Functor.map_id]
  · intro U
    let ki : U ⟶ i₀ :=
      ObjectProperty.homMk
        (MorphismProperty.Over.homMk (P := S) (Q := ⊤) (X := X) U.1.hom (by
          change U.1.hom ≫ 𝟙 X = U.1.hom
          simp))
    refine ⟨U, ki, 𝟙 U, ?_⟩
    letI : IsIso (F.map U.1.hom) := hP_isIso U.1.hom U.2 hX U.1.prop
    -- Proof comment: the morphism `U ⟶ i₀` again records the denominator `U.1.hom`, so the
    -- diagram map along it followed by the cone projection is `hom ≫ inv = 𝟙`.
    rw [Functor.map_id,
      goodSourceRestrictedDiagram_map (F := F) (S := S) (P := P) (f := ki)]
    letI : IsIso (F.map U.1.hom) := hP_isIso U.1.hom U.2 hX U.1.prop
    have hki : ki.hom.left = U.1.hom := by
      rfl
    rw [hki]
    change 𝟙 (F.obj U.1.left) =
      F.map U.1.hom ≫ 𝟙 (F.obj X) ≫ (asIso (F.map U.1.hom)).inv
    simp

/-- Helper for Lemma 13.14.15: on the good full subcategory of `S / X`, the denominator diagram is
essentially constant with value `F.obj X`. -/
private theorem goodSourceRestrictedDiagram_essentiallyConstant
    {X : D} (hX : P X)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s)) :
    IsEssentiallyConstantCofilteredDiagram
      (ObjectProperty.ι (goodSourceDenominatorProperty (P := P) (S := S) X) ⋙
        MorphismProperty.Over.forget S ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ F) := by
  -- Proof comment: the strengthened cone-level helper already packages the required witness.
  exact
    ⟨goodSourceRestrictedCone (F := F) (S := S) (P := P) hX hP_isIso,
      goodSourceRestrictedCone_essentiallyConstant
        (F := F) (S := S) (P := P) hX hP_isIso⟩

/-- Helper for Lemma 13.14.15: the ordinary denominator category `S / X` maps to the ambient
structured-arrow indexing category for `LF(X)` by sending a denominator to its localized
inverse. -/
private noncomputable def sourceDenominatorToStructuredArrow (X : D) :
    (S / X) ⥤ StructuredArrow (S.Q.obj X) S.Q where
  obj U := StructuredArrow.mk ((Localization.isoOfHom S.Q S U.hom U.prop).inv)
  map := fun {U V} f ↦
    StructuredArrow.homMk f.left
      (denominatorStructuredArrowHomEq (S := S) U.hom V.hom U.prop V.prop f.left
        (MorphismProperty.Over.w f))

/-- Helper for Lemma 13.14.15: the denominator functor `S / X ⥤ StructuredArrow (S.Q.obj X) S.Q`
is initial. -/
private theorem sourceDenominatorToStructuredArrow_initial
    (X : D) [S.HasRightCalculusOfFractions] :
    Functor.Initial (sourceDenominatorToStructuredArrow (S := S) X) := by
  let T := sourceDenominatorToStructuredArrow (S := S) X
  -- Proof comment: every ambient structured-arrow stage receives a morphism from a denominator
  -- stage, and two maps out of the same denominator become equal after refining the source once.
  refine Functor.initial_of_exists_of_isCofiltered T ?_ ?_
  · intro g
    rcases structuredArrowExistsHomFromDenominator (S := S) (Y := X) g with
      ⟨Y', s, hs, ⟨α⟩⟩
    exact ⟨MorphismProperty.Over.mk (P := S) (Q := ⊤) (X := X) s hs, ⟨α⟩⟩
  · intro g U α β
    have hα :
        S.Q.map α.right = S.Q.map U.hom ≫ g.hom := by
      apply (cancel_epi (Localization.isoOfHom S.Q S U.hom U.prop).inv).1
      simpa [Category.assoc, Localization.isoOfHom_hom] using α.w.symm
    have hβ :
        S.Q.map β.right = S.Q.map U.hom ≫ g.hom := by
      apply (cancel_epi (Localization.isoOfHom S.Q S U.hom U.prop).inv).1
      simpa [Category.assoc, Localization.isoOfHom_hom] using β.w.symm
    obtain ⟨Y, t, ht, hfac⟩ :=
      (MorphismProperty.map_eq_iff_precomp (L := S.Q) (W := S) α.right β.right).1
        (hα.trans hβ.symm)
    let V : S / X :=
      MorphismProperty.Over.mk (P := S) (Q := ⊤) (X := X) (t ≫ U.hom)
        (S.comp_mem _ _ ht U.prop)
    let γ : V ⟶ U :=
      MorphismProperty.Over.homMk (P := S) (Q := ⊤) (X := X) t rfl
    refine ⟨V, γ, ?_⟩
    apply StructuredArrow.hom_ext
    simpa [T, sourceDenominatorToStructuredArrow, γ, V, Category.assoc] using hfac

/-- Helper for Lemma 13.14.15: the restriction of `F` to the full subcategory on `P` inverts the
restricted localization system `S.inverseImage P.ι`. -/
private theorem restrictedInvertsOnDualGoodSubset
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s)) :
    (fullSubcategoryLocalizationSystem P S).IsInvertedBy (P.ι ⋙ F) := by
  intro X Y f hf
  -- Proof comment: the restricted left-derived setup uses the same underlying ambient arrows, so
  -- the inversion hypothesis again applies on the nose.
  change IsIso (F.map f.hom)
  exact hP_isIso f.hom X.property Y.property
    (by simpa [fullSubcategoryLocalizationSystem] using hf)

/-- Helper for Lemma 13.14.15: the incoming good-subset hypothesis supplies left resolutions for
the good full-subcategory inclusion localizer. -/
private theorem dualGoodSubsetLocalizer_hasLeftResolutions
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s) :
    (fullSubcategoryLocalizerMorphism P S).HasLeftResolutions := by
  intro X
  rcases hP_reaches X with ⟨X', s, hX', hs⟩
  let Xgood : P.FullSubcategory := ⟨X', hX'⟩
  -- Proof comment: the chosen denominator `s : X' ⟶ X` with `X' ∈ P` is exactly a left
  -- resolution of `X` for the inclusion of the good full subcategory.
  exact ⟨{ X₁ := Xgood
           w := s
           hw := hs }⟩

/-- Helper for Lemma 13.14.15: after localizing the full subcategory on `P`, the restricted
inclusion `P.ι ⋙ S.Q` is itself a localization functor. -/
private theorem restrictedDualInclusionIsLocalization
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s) :
    (P.ι ⋙ S.Q).IsLocalization (fullSubcategoryLocalizationSystem P S) := by
  let Φ := fullSubcategoryLocalizerMorphism P S
  have hCover :
      ∀ X : D, ∃ (X' : P.FullSubcategory) (s : P.ι.obj X' ⟶ X), S s := by
    intro X
    rcases hP_reaches X with ⟨X', s, hX', hs⟩
    exact ⟨⟨X', hX'⟩, s, hs⟩
  letI : Φ.IsLocalizedEquivalence :=
    fullSubcategoryLocalizerMorphism_isLocalizedEquivalence P S hCover
  simpa [Φ, fullSubcategoryLocalizerMorphism] using
    (inferInstance :
      (Φ.functor ⋙ S.Q).IsLocalization (fullSubcategoryLocalizationSystem P S))

/-- Helper for Lemma 13.14.15: on the full subcategory of good objects, the restricted functor
already computes its left derived functor everywhere because it inverts the restricted
denominators. -/
private theorem restrictedComputesLeftDerivedOnDualGoodSubset
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s))
    (X : P.FullSubcategory) :
    (P.ι ⋙ F).ComputesLeftDerivedAt (fullSubcategoryLocalizationSystem P S) X := by
  let W := fullSubcategoryLocalizationSystem P S
  let G : P.FullSubcategory ⥤ D' := P.ι ⋙ F
  have hInv : W.IsInvertedBy G :=
    restrictedInvertsOnDualGoodSubset (F := F) (S := S) P hP_isIso
  letI : G.HasPointwiseLeftDerivedFunctor W :=
    Functor.hasPointwiseLeftDerivedFunctor_of_inverts G hInv
  have hCounitNatIso : IsIso (G.totalLeftDerivedCounit W.Q W) := by
    -- Proof comment: on the restricted localization, the left-derived counit is invertible
    -- because `G` already inverts every denominator.
    exact
      Functor.isIso_of_isLeftDerivedFunctor_of_inverts
        (W := W) (L := W.Q)
        (LF := G.totalLeftDerived W.Q W)
        (α := G.totalLeftDerivedCounit W.Q W) hInv
  have hCounitIso : IsIso ((G.totalLeftDerivedCounit W.Q W).app X) := by
    infer_instance
  -- Proof comment: convert the invertible counit into the source-facing left computation owner.
  exact
    (Functor.computesLeftDerivedAt_iff (F := G) (S := W) (X := X)).2 hCounitIso

/-- Lemma 13.14.15 (4): under the dual subset criterion, any object of the chosen good subset
computes the left derived functor of `F` with respect to `S`. -/
@[stacks 06XN]
theorem computesLeftDerivedAt_of_mem_subset
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s))
    {X : D} (hX : P X) :
    F.ComputesLeftDerivedAt S X := by
  let J := goodSourceDenominatorProperty (P := P) (S := S) X
  let inclusion := ObjectProperty.ι J
  let U₀ : J.FullSubcategory :=
    ⟨MorphismProperty.Over.mk (P := S) (Q := ⊤) (X := X) (𝟙 X) (S.id_mem X), hX⟩
  letI : Functor.Initial inclusion :=
    goodSourceDenominatorInclusionInitial (S := S) (P := P) hP_reaches X
  let cGood := goodSourceRestrictedCone (F := F) (S := S) (P := P) hX hP_isIso
  have hcGood : IsLimit cGood :=
    (goodSourceRestrictedCone_essentiallyConstant
      (F := F) (S := S) (P := P) hX hP_isIso).isLimit
  let cOver :
      Cone
        (MorphismProperty.Over.forget S ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ F) :=
    (Functor.Initial.extendCone (F := inclusion)).obj cGood
  have hcOver : IsLimit cOver :=
    ((Functor.Initial.isLimitExtendConeEquiv
      (F := inclusion) cGood).symm hcGood)
  let T := sourceDenominatorToStructuredArrow (S := S) X
  letI : Functor.Initial T := sourceDenominatorToStructuredArrow_initial (S := S) X
  let cOver' :
      Cone (T ⋙ StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) := cOver
  let cAmbient : LimitCone (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) :=
    { cone := (Functor.Initial.extendCone (F := T)).obj cOver'
      isLimit :=
        ((Functor.Initial.isLimitExtendConeEquiv
          (F := T) cOver').symm hcOver) }
  letI : HasLimit (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F) := HasLimit.mk cAmbient
  letI : F.HasPointwiseLeftDerivedFunctorAt S X :=
    (Functor.hasPointwiseLeftDerivedFunctorAt_iff (F := F) (L := S.Q) (W := S) X).2 inferInstance
  have hOverId :
      cOver.π.app U₀.1 = cGood.π.app U₀ := by
    -- Proof comment: extending along the initial good-subcategory inclusion preserves the
    -- identity denominator projection.
    simpa [cOver, inclusion, J] using
      (Functor.Initial.extendCone_obj_π_app' (F := inclusion) cGood
        (X := U₀) (Y := U₀.1) (f := 𝟙 U₀.1))
  have hAmbientId :
      cAmbient.cone.π.app
          (StructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)) =
        cOver.π.app U₀.1 := by
    -- Proof comment: the ambient structured-arrow limit cone has the same identity-stage
    -- projection as the ordinary denominator cone.
    simpa [cAmbient, T, sourceDenominatorToStructuredArrow, U₀] using
      (Functor.Initial.extendCone_obj_π_app' (F := T) cOver'
        (X := U₀.1) (Y := T.obj U₀.1) (f := 𝟙 (T.obj U₀.1)))
  have hExplicit :
      cAmbient.cone.π.app
          (StructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv)) =
        (asIso (F.map (𝟙 X))).inv := by
    rw [hAmbientId, hOverId]
    simpa [U₀] using
      goodSourceRestrictedCone_app (F := F) (S := S) (P := P) hX hP_isIso U₀
  have hLegComp :
      (limit.isoLimitCone cAmbient).inv ≫
          leftDerivedValueProjection S F (𝟙 X) (S.id_mem X) =
        (asIso (F.map (𝟙 X))).inv := by
    -- Proof comment: compare the canonical identity projection with the identity-stage leg of
    -- the explicit ambient limit cone.
    simpa [leftDerivedValueProjection, cAmbient] using
      (limit.isoLimitCone_inv_π cAmbient
        (StructuredArrow.mk ((Localization.isoOfHom S.Q S (𝟙 X) (S.id_mem X)).inv))).trans
        hExplicit
  have hProjectionIso :
      IsIso (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) := by
    have hCompIso :
        IsIso
          ((limit.isoLimitCone cAmbient).inv ≫
            leftDerivedValueProjection S F (𝟙 X) (S.id_mem X)) := by
      rw [hLegComp]
      infer_instance
    exact
      (isIso_comp_left_iff
        ((limit.isoLimitCone cAmbient).inv)
        (leftDerivedValueProjection S F (𝟙 X) (S.id_mem X))).1 hCompIso
  -- Proof comment: the explicit ambient limit cone defines `LF(X)` at `X`, and its identity
  -- denominator projection is the inverse of `F.map (𝟙 X)`.
  exact ⟨hProjectionIso⟩

/-- Lemma 13.14.15 (3): if every object receives a denominator in `S` from an object of `P`, and
if `F` inverts denominators between objects of `P`, then `F` has pointwise left derived functors
with respect to `S`. -/
@[stacks 06XN]
theorem hasPointwiseLeftDerivedFunctor_of_subset :
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s) →
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s)) →
    F.HasPointwiseLeftDerivedFunctor S :=
  fun hP_reaches hP_isIso ↦
    F.hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt S
      (fun X ↦ by
        rcases hP_reaches X with ⟨X', s, hX', hs⟩
        exact
          ⟨X', s, hs,
            computesLeftDerivedAt_of_mem_subset F S P hP_reaches hP_isIso hX'⟩)

end Left

end

end Functor

end CategoryTheory
