import Mathlib
import StacksProject_2024.Chap13.Definition_13_23_2
import StacksProject_2024.Chap13.Lemma_13_18_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Localization
open ComplexShape
open scoped CategoryTheory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

attribute [local instance] HasDerivedCategory.standard

/-
Domain-style sampling:
- primary domain: bounded-below injective resolutions viewed in the bounded-below homotopy
  category;
- sampled owner declarations:
  `CochainComplex.ResolutionFunctorOne`,
  `CategoryTheory.HomotopyResolutionFunctor`,
  `CategoryTheory.ObjectProperty.ι (CategoryTheory.boundedBelowInjectiveHomotopyProperty 𝒜)`,
  `CochainComplex.InjectivePlus.toHomotopy`,
  `HomotopyCategory.Plus.quotient`;
- best owner abstraction: `CategoryTheory.HomotopyResolutionFunctor` is the canonical owner for
  the homotopy-category realization, while `ResolutionFunctorOne` is only the source-facing
  objectwise choice of injective resolutions;
- primitive data: `R : ResolutionFunctorOne 𝒜`;
- derived API: the induced object of `K^+(\mathcal I)`, the comparison morphism in
  `K^+(\mathcal A)`, and the bridge predicate comparing `R` with a homotopy resolution
  functor through explicit objectwise isomorphisms in `K^+(\mathcal I)`.

Source/core/bridge triage:
- `source-facing`: `ResolutionFunctorOne 𝒜`;
- `core/canonical`: `CategoryTheory.HomotopyResolutionFunctor 𝒜`;
- `bridge/view`: `ResolutionFunctorOne.homotopyObj`, `ResolutionFunctorOne.homotopyι`, and
  `ResolutionFunctorOne.RealizedBy`.
-/
namespace ResolutionFunctorOne

local notation "Qplus" => HomotopyCategory.Plus.quotient 𝒜
local notation "KinjIncl" =>
  ObjectProperty.ι (CategoryTheory.boundedBelowInjectiveHomotopyProperty 𝒜)

/-- The chosen injective resolution `j(K)` viewed as an object of `K^+(\mathcal I)`. -/
abbrev homotopyObj (R : ResolutionFunctorOne 𝒜) (K : Plus 𝒜) :
    K⁺ᵢ(𝒜) :=
  ⟨(Qplus).obj (R K : Plus 𝒜), fun n ↦ by
    simpa using (R K).injective n⟩

/-- The comparison map `K ⟶ j(K)` viewed in `K^+(\mathcal A)`. -/
abbrev homotopyι (R : ResolutionFunctorOne 𝒜) (K : Plus 𝒜) :
    (Qplus).obj K ⟶ (KinjIncl).obj (R.homotopyObj K) :=
  (Qplus).map ⟨(R K).ι⟩

/-- A homotopy resolution functor realizes `R` when, on each bounded-below complex `K`, its
value is canonically isomorphic to the chosen object `j(K)`, and after transporting along that
isomorphism its comparison morphism agrees in `K^+(\mathcal A)` with the chosen
quasi-isomorphism `K ⟶ j(K)`. -/
def RealizedBy (R : ResolutionFunctorOne 𝒜)
    (j : HomotopyResolutionFunctor 𝒜) : Prop :=
  ∀ K : Plus 𝒜, ∃! eK : j.toFunctor.obj ((Qplus).obj K) ≅ R.homotopyObj K,
    j.ι.app ((Qplus).obj K) ≫ (KinjIncl).map eK.hom = homotopyι R K

end ResolutionFunctorOne

local notation "Qplus" => HomotopyCategory.Plus.quotient 𝒜

/-- Helper for Lemma 13.23.3: the inclusion `K^+(\mathcal I) ↪ K^+(\mathcal A)`. -/
private abbrev KinjIncl : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜) :=
  ObjectProperty.ι (CategoryTheory.boundedBelowInjectiveHomotopyProperty 𝒜)

/-- Helper for Lemma 13.23.3: the inclusion `K^+(\mathcal A) ↪ K(\mathcal A)`. -/
private abbrev KplusIncl : K⁺(𝒜) ⥤ K(𝒜) :=
  ObjectProperty.ι (HomotopyCategory.plus 𝒜)

/-- Helper for Lemma 13.23.3: the bounded-below homotopy category followed by localization to the
derived category. -/
private noncomputable abbrev Dplus : K⁺(𝒜) ⥤ DerivedCategory 𝒜 :=
  KplusIncl ⋙ DerivedCategory.Qh

/-- Helper for Lemma 13.23.3: recover the bounded-below cochain complex underlying an object of
`K^+(\mathcal A)`. -/
private abbrev sourcePlus (X : K⁺(𝒜)) : Plus 𝒜 :=
  ⟨X.obj.as, X.property⟩

/-- Helper for Lemma 13.23.3: the chosen injective target attached to `X : K^+(\mathcal A)`. -/
private abbrev chosenObj (R : ResolutionFunctorOne 𝒜) (X : K⁺(𝒜)) : K⁺ᵢ(𝒜) :=
  R.homotopyObj (sourcePlus X)

/-- Helper for Lemma 13.23.3: the chosen comparison map from `X` to its injective target. -/
private abbrev chosenι (R : ResolutionFunctorOne 𝒜) (X : K⁺(𝒜)) :
    X ⟶ KinjIncl.obj (chosenObj R X) :=
  R.homotopyι (sourcePlus X)

/-- Helper for Lemma 13.23.3: passing from a bounded-below complex to its image in `K^+` and back
recovers the original complex. -/
private theorem sourcePlus_qplusObj (K : Plus 𝒜) :
    sourcePlus ((Qplus).obj K) = K := by
  cases K
  rfl

/-- Helper for Lemma 13.23.3: the packaged object part agrees with the original chosen resolution
on complexes coming directly from `Plus 𝒜`. -/
private theorem chosenObj_qplusObj
    (R : ResolutionFunctorOne 𝒜) (K : Plus 𝒜) :
    chosenObj R ((Qplus).obj K) = R.homotopyObj K := by
  cases K
  rfl

/-- Helper for Lemma 13.23.3: the packaged comparison map agrees with the original chosen
quasi-isomorphism on complexes coming directly from `Plus 𝒜`. -/
private theorem chosenι_qplusObj
    (R : ResolutionFunctorOne 𝒜) (K : Plus 𝒜) :
    chosenι R ((Qplus).obj K) = R.homotopyι K := by
  cases K
  rfl

/-- Helper for Lemma 13.23.3: the chosen comparison map becomes a quasi-isomorphism in the
ambient homotopy category. -/
private theorem chosenι_quasiIso_ambient
    (R : ResolutionFunctorOne 𝒜) (X : K⁺(𝒜)) :
    (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage KplusIncl (chosenι R X) := by
  -- Proof comment: after forgetting bounded-below structure, this is exactly the quotient class
  -- of the cochain-level quasi-isomorphism stored in the injective resolution `R (sourcePlus X)`.
  change
    HomotopyCategory.quasiIso 𝒜 (up ℤ)
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).map ((R (sourcePlus X)).ι))
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact (R (sourcePlus X)).quasiIso

/-- Helper for Lemma 13.23.3: morphisms from a bounded-below homotopy object into a bounded-below
injective target are detected uniquely in the derived category. -/
private theorem boundedBelowHomotopyToDerived_map_bijective
    (X : K⁺(𝒜)) (Y : K⁺ᵢ(𝒜)) :
    Function.Bijective
      (Dplus.map :
        (X ⟶ KinjIncl.obj Y) →
          (Dplus.obj X ⟶ Dplus.obj (KinjIncl.obj Y))) := by
  let hKplusIncl :
      Function.Bijective
        (KplusIncl.map :
          (X ⟶ KinjIncl.obj Y) →
            (X.obj ⟶ (KinjIncl.obj Y).obj)) := by
    simpa using
      (Functor.FullyFaithful.ofFullyFaithful KplusIncl).map_bijective X (KinjIncl.obj Y)
  let hQh :
      Function.Bijective
        (DerivedCategory.Qh.map :
          (X.obj ⟶ (KinjIncl.obj Y).obj) →
            (DerivedCategory.Qh.obj X.obj ⟶ DerivedCategory.Qh.obj (KinjIncl.obj Y).obj)) := by
    simpa using
      homotopyCategory_to_derived_bijective_of_boundedBelow_injective X.obj.as Y.toInjectivePlus
  simpa [Dplus] using hQh.comp hKplusIncl

/-- Helper for Lemma 13.23.3: every map `f : X ⟶ Y` in `K^+(\mathcal A)` induces a unique
comparison map between the chosen injective targets that commutes with the chosen
quasi-isomorphisms. -/
private theorem existsUnique_mapToHomotopyObj
    (R : ResolutionFunctorOne 𝒜) {X Y : K⁺(𝒜)} (f : X ⟶ Y) :
    ∃! a : chosenObj R X ⟶ chosenObj R Y,
      chosenι R X ≫ KinjIncl.map a = f ≫ chosenι R Y := by
  classical
  have hι :
      IsIso (Dplus.map (chosenι R X)) := by
    -- Proof comment: the comparison map becomes invertible in the derived category because it is
    -- a quasi-isomorphism after forgetting to the ambient homotopy category.
    simpa [Dplus] using
      (Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso 𝒜 (up ℤ)) _ (chosenι_quasiIso_ambient R X))
  let t :
      Dplus.obj (KinjIncl.obj (chosenObj R X)) ⟶
        Dplus.obj (KinjIncl.obj (chosenObj R Y)) :=
    inv (Dplus.map (chosenι R X)) ≫ Dplus.map (f ≫ chosenι R Y)
  obtain ⟨g, hg⟩ :=
    (boundedBelowHomotopyToDerived_map_bijective
      (X := KinjIncl.obj (chosenObj R X)) (Y := chosenObj R Y)).surjective t
  let a : chosenObj R X ⟶ chosenObj R Y := KinjIncl.preimage g
  have ha_map : KinjIncl.map a = g := by
    simpa [a] using KinjIncl.map_preimage g
  refine ⟨a, ?_, ?_⟩
  · -- Proof comment: compare the two lifts after applying the faithful map to the derived
    -- category, where `chosenι R X` has an inverse.
    apply (boundedBelowHomotopyToDerived_map_bijective (X := X) (Y := chosenObj R Y)).injective
    rw [Functor.map_comp, ha_map, hg]
    simp [t]
  · intro b hb
    -- Proof comment: any other compatible lift has the same derived image, hence the same
    -- underlying homotopy morphism, and therefore agrees already in `K^+(\mathcal I)`.
    apply KinjIncl.map_injective
    apply (boundedBelowHomotopyToDerived_map_bijective
      (X := KinjIncl.obj (chosenObj R X)) (Y := chosenObj R Y)).injective
    have hbD : Dplus.map (KinjIncl.map b) = t := by
      have h := congrArg Dplus.map hb
      rw [Functor.map_comp] at h
      have h' := congrArg (fun k ↦ inv (Dplus.map (chosenι R X)) ≫ k) h
      simpa [t, Category.assoc] using h'
    rw [ha_map]
    exact hbD.trans hg.symm

/-- Helper for Lemma 13.23.3: the uniquely induced morphism on chosen injective targets. -/
private noncomputable abbrev chosenMap
    (R : ResolutionFunctorOne 𝒜) {X Y : K⁺(𝒜)} (f : X ⟶ Y) :
    chosenObj R X ⟶ chosenObj R Y :=
  Classical.choose (existsUnique_mapToHomotopyObj (R := R) f)

/-- Helper for Lemma 13.23.3: the chosen morphism is characterized by the comparison square with
the fixed quasi-isomorphisms. -/
private theorem chosenMap_spec
    (R : ResolutionFunctorOne 𝒜) {X Y : K⁺(𝒜)} (f : X ⟶ Y) :
    chosenι R X ≫ KinjIncl.map (chosenMap R f) = f ≫ chosenι R Y := by
  exact (Classical.choose_spec (existsUnique_mapToHomotopyObj (R := R) f)).1

/-- Helper for Lemma 13.23.3: the chosen lift over an identity morphism is the identity on the
chosen injective target. -/
private theorem chosenMap_id
    (R : ResolutionFunctorOne 𝒜) (X : K⁺(𝒜)) :
    chosenMap R (𝟙 X) = 𝟙 (chosenObj R X) := by
  -- Proof comment: the identity map on the injective target satisfies the same comparison square,
  -- so uniqueness forces the chosen lift to be the identity.
  exact
    ((Classical.choose_spec
      (existsUnique_mapToHomotopyObj (R := R) (f := 𝟙 X))).2 _ (by simp)).symm

/-- Helper for Lemma 13.23.3: the chosen lifts preserve composition because both composites solve
the same universal lifting problem over `f ≫ g`. -/
private theorem chosenMap_comp
    (R : ResolutionFunctorOne 𝒜) {X Y Z : K⁺(𝒜)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    chosenMap R (f ≫ g) = chosenMap R f ≫ chosenMap R g := by
  -- Proof comment: compose the two defining comparison squares and then use uniqueness for the
  -- lift over `f ≫ g`.
  have hcomp :
      chosenι R X ≫ KinjIncl.map (chosenMap R f ≫ chosenMap R g) =
        (f ≫ g) ≫ chosenι R Z := by
    calc
      chosenι R X ≫ KinjIncl.map (chosenMap R f ≫ chosenMap R g)
          = chosenι R X ≫ KinjIncl.map (chosenMap R f) ≫
              KinjIncl.map (chosenMap R g) := by
            simp
      _ = f ≫ chosenι R Y ≫ KinjIncl.map (chosenMap R g) := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ k ≫ KinjIncl.map (chosenMap R g))
                (chosenMap_spec (R := R) (f := f))
      _ = f ≫ (chosenι R Y ≫ KinjIncl.map (chosenMap R g)) := by
            simp
      _ = f ≫ (g ≫ chosenι R Z) := by
            rw [chosenMap_spec (R := R) (f := g)]
      _ = (f ≫ g) ≫ chosenι R Z := by
            simp [Category.assoc]
  exact
    ((Classical.choose_spec
      (existsUnique_mapToHomotopyObj (R := R) (f := f ≫ g))).2 _ hcomp).symm

/-- Helper for Lemma 13.23.3: the canonical comparison maps assemble to a natural
transformation `𝟭 ⟶ j ⋙ K^+(\mathcal I) ↪ K^+(\mathcal A)`. -/
private theorem chosenι_natural
    (R : ResolutionFunctorOne 𝒜) {X Y : K⁺(𝒜)} (f : X ⟶ Y) :
    f ≫ chosenι R Y = chosenι R X ≫ KinjIncl.map (chosenMap R f) := by
  -- Proof comment: this is exactly the defining commutative square for the chosen lift, read in
  -- the natural-transformation direction.
  simpa using (chosenMap_spec (R := R) (f := f)).symm

/-- Helper for Lemma 13.23.3: the functor on `K^+(\mathcal A)` determined by the universal lift
against the chosen quasi-isomorphisms. -/
private noncomputable def homotopyResolutionToFunctor
    (R : ResolutionFunctorOne 𝒜) :
    K⁺(𝒜) ⥤ K⁺ᵢ(𝒜) where
  obj := chosenObj R
  map := fun f ↦ chosenMap R f
  map_id := chosenMap_id R
  map_comp := chosenMap_comp R

/-- Helper for Lemma 13.23.3: the canonical comparison maps from a bounded-below complex to its
chosen injective target. -/
private noncomputable def homotopyResolutionNatTrans
    (R : ResolutionFunctorOne 𝒜) :
    𝟭 (K⁺(𝒜)) ⟶ homotopyResolutionToFunctor R ⋙ KinjIncl where
  app := chosenι R
  naturality _ _ f := chosenι_natural R f

/-- Helper for Lemma 13.23.3: package the chosen objectwise resolutions into a homotopy
resolution functor. -/
private noncomputable def homotopyResolutionFunctorOfResolutionFunctorOne
    (R : ResolutionFunctorOne 𝒜) :
    HomotopyResolutionFunctor 𝒜 where
  toFunctor := homotopyResolutionToFunctor R
  ι := homotopyResolutionNatTrans R
  quasiIso_app := chosenι_quasiIso_ambient R

-- Route correction: `HomotopyResolutionFunctor` and `K⁺ᵢ(𝒜)` now come from the earlier owner
-- file `Definition_13_23_2`, so this realization theorem no longer validates through the later
-- exactness file `Lemma_13_23_5`.
-- Proof sketch: for each morphism of bounded-below complexes, Lemmas 13.18.6 and 13.18.7 give a
-- unique induced morphism between the chosen injective resolutions in the homotopy category.
-- Those unique lifts force preservation of identities and composition, so the objectwise
-- resolution data extends uniquely to the canonical homotopy-category owner
-- `CategoryTheory.HomotopyResolutionFunctor`.
/-- Lemma 13.23.3: a resolution functor 1 on bounded-below cochain complexes admits a
homotopy-category realization. The source uniqueness is uniqueness of the functorial structure and
comparison 2-isomorphism extending the fixed objectwise resolution data; with the current local
predicate `RealizedBy`, objectwise comparison isomorphisms are still explicit witnesses, so the
statement records the existence part and avoids an overly strong uniqueness claim for the whole
structure. -/
@[stacks 05TJ]
theorem exists_homotopyResolutionFunctor_of_resolutionFunctorOne
    (R : ResolutionFunctorOne 𝒜) :
    ∃ j : HomotopyResolutionFunctor 𝒜, R.RealizedBy j := by
  classical
  refine ⟨homotopyResolutionFunctorOfResolutionFunctorOne R, ?_⟩
  intro K
  refine ⟨Iso.refl _, ?_, ?_⟩
  · -- Proof comment: for the packaged functor, the comparison map at `K` is literally the fixed
    -- quasi-isomorphism `R.homotopyι K`.
    change
      chosenι R ((Qplus).obj K) ≫ KinjIncl.map (𝟙 (chosenObj R ((Qplus).obj K))) =
        R.homotopyι K
    simpa using (chosenι_qplusObj (R := R) K)
  · intro eK heK
    have hchosen :
        chosenMap R (𝟙 ((Qplus).obj K)) = 𝟙 (R.homotopyObj K) := by
      simpa [chosenObj_qplusObj] using chosenMap_id (R := R) ((Qplus).obj K)
    have heHom :
        eK.hom = 𝟙 (R.homotopyObj K) := by
      -- Proof comment: any compatible automorphism of the chosen injective target solves the same
      -- universal lifting problem as the identity, so uniqueness forces its morphism part to be
      -- the identity.
      have huniq :=
        (Classical.choose_spec
          (existsUnique_mapToHomotopyObj (R := R)
            (X := (Qplus).obj K) (Y := (Qplus).obj K) (f := 𝟙 ((Qplus).obj K)))).2
      have heCompat :
          chosenι R ((Qplus).obj K) ≫ KinjIncl.map eK.hom =
            (𝟙 ((Qplus).obj K)) ≫ chosenι R ((Qplus).obj K) := by
        simpa [homotopyResolutionFunctorOfResolutionFunctorOne, homotopyResolutionNatTrans,
          homotopyResolutionToFunctor, chosenι_qplusObj] using heK
      exact (huniq _ heCompat).trans hchosen
    apply Iso.ext
    simpa using heHom

/-- Compatibility name for older generated files. This is only an existence statement; it does not
claim uniqueness of the entire bundled `HomotopyResolutionFunctor` structure. -/
theorem existsUnique_homotopyResolutionFunctor_of_resolutionFunctorOne
    (R : ResolutionFunctorOne 𝒜) :
    ∃ j : HomotopyResolutionFunctor 𝒜, R.RealizedBy j :=
  exists_homotopyResolutionFunctor_of_resolutionFunctorOne R

end CochainComplex
