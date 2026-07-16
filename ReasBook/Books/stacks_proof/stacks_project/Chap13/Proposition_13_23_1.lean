import Mathlib
import stacks_proof.stacks_project.Chap04.Lemma_4_2_18
import stacks_proof.stacks_project.Chap13.Lemma_13_18_8
import stacks_proof.stacks_project.Chap13.Lemma_13_11_6
import stacks_proof.stacks_project.Chap13.Lemma_13_23_4
import stacks_proof.stacks_project.Chap13.Lemma_13_23_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Localization
open CategoryTheory.ObjectProperty
open CochainComplex
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Proposition 13.23.1:
- primary domain: bounded-below homotopy and derived categories, with the injective full
  subcategory as a source-facing bridge into the canonical localization functor;
- sampled owner declarations:
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)`,
  `mapBoundedBelowHomotopyToDerivedBelow`,
  `HomotopyResolutionFunctor`,
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedBelow_injective`;
- best owner abstraction: the proposition is about the canonical composite
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
  mapBoundedBelowHomotopyToDerivedBelow`, not about a new
  owner functor alias;
- primitive vs. derived API:
  primitive data: the injective full subcategory `K⁺ᵢ(𝒜)`, the localization functor
    `mapBoundedBelowHomotopyToDerivedBelow`, and a homotopy resolution functor;
  derived API: the factorization of a homotopy resolution through `D⁺(𝒜)` and the resulting
    equivalence statement.

Source/core/bridge triage:
- `source-facing`: Proposition 13.23.1 itself, asserting that bounded-below injective complexes
  compute `D⁺(𝒜)`;
- `core/canonical`: `Functor.IsLocalization`, `Localization.lift`, and the hom-bijection into
  bounded-below injective complexes;
-/

local notation "Q" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))
local notation "KinjIncl" =>
  (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜))
local notation "IToD" => KinjIncl ⋙ Q

attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

/-- Helper for Proposition 13.23.1: the canonical functor from bounded-below injective homotopy
objects to `D^+(\mathcal A)` is full and faithful on morphisms. -/
private theorem iToD_map_bijective (X Y : K⁺ᵢ(𝒜)) :
    Function.Bijective
      (((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜)) ⋙
          mapBoundedBelowHomotopyToDerivedBelow).map : (X ⟶ Y) → _) := by
  let Q' : K⁺(𝒜) ⥤ D⁺(𝒜) := mapBoundedBelowHomotopyToDerivedBelow
  let KinjIncl' : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜) :=
    ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
  let IToD' : K⁺ᵢ(𝒜) ⥤ D⁺(𝒜) := KinjIncl' ⋙ Q'
  let KplusIncl := (ObjectProperty.ι (HomotopyCategory.plus 𝒜) : K⁺(𝒜) ⥤ _)
  let Qplus := KplusIncl ⋙ DerivedCategory.Qh
  let DplusIncl := (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))) : D⁺(𝒜) ⥤ _)
  -- Proof comment: first forget the injective structure, which is fully faithful by construction.
  let hIncl :
      Function.Bijective
        (KinjIncl'.map : (X ⟶ Y) → (X.obj ⟶ Y.obj)) := by
    simpa [KinjIncl'] using (Functor.FullyFaithful.ofFullyFaithful KinjIncl').map_bijective X Y
  -- Proof comment: then compare the bounded-below derived localization with the ambient derived
  -- category where Lemma 13.18.8 applies.
  let hQ :
      Function.Bijective
        (Q'.map : (X.obj ⟶ Y.obj) → (Q'.obj X.obj ⟶ Q'.obj Y.obj)) := by
    let hAmbient :
        Function.Bijective
          (Qplus.map :
            (X.obj ⟶ Y.obj) → (Qplus.obj X.obj ⟶ Qplus.obj Y.obj)) := by
      let hKplusIncl :
          Function.Bijective
            (KplusIncl.map :
              (X.obj ⟶ Y.obj) → (X.obj.obj ⟶ Y.obj.obj)) := by
        simpa using
          (Functor.FullyFaithful.ofFullyFaithful KplusIncl).map_bijective X.obj Y.obj
      let hQh :
          Function.Bijective
            (DerivedCategory.Qh.map :
              (X.obj.obj ⟶ Y.obj.obj) →
                (DerivedCategory.Qh.obj X.obj.obj ⟶ DerivedCategory.Qh.obj Y.obj.obj)) := by
        let X' : K⁺(𝒜) := X.obj
        simpa using
          homotopyCategory_to_derived_bijective_of_boundedBelow_injective X'.obj.as
            Y.toInjectivePlus
      simpa [Functor.comp_map] using hQh.comp hKplusIncl
    let hDplusIncl :
        Function.Bijective
          (DplusIncl.map :
            (Q'.obj X.obj ⟶ Q'.obj Y.obj) →
              (DplusIncl.obj (Q'.obj X.obj) ⟶ DplusIncl.obj (Q'.obj Y.obj))) := by
      simpa using
        (Functor.FullyFaithful.ofFullyFaithful DplusIncl).map_bijective
          (Q'.obj X.obj) (Q'.obj Y.obj)
    have hcomp :
        DplusIncl.map ∘
            (Q'.map : (X.obj ⟶ Y.obj) → (Q'.obj X.obj ⟶ Q'.obj Y.obj)) =
          (Qplus.map : (X.obj ⟶ Y.obj) → (Qplus.obj X.obj ⟶ Qplus.obj Y.obj)) := by
      funext f
      rfl
    exact (Function.Bijective.of_comp_iff' hDplusIncl _).mp (hcomp ▸ hAmbient)
  simpa [IToD', Q', KinjIncl', Functor.comp_map] using hQ.comp hIncl

/-- Helper for Proposition 13.23.1: the functor `K^+(\mathcal I) ⥤ D^+(\mathcal A)` reflects
isomorphisms because Lemma 13.18.8 makes it fully faithful. -/
private theorem iToD_reflects_isIso {X Y : K⁺ᵢ(𝒜)} (g : X ⟶ Y)
    [IsIso (IToD.map g)] : IsIso g := by
  let F : K⁺ᵢ(𝒜) ⥤ D⁺(𝒜) := IToD
  obtain ⟨hFF⟩ :
      Nonempty F.FullyFaithful := by
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro X Y
    simpa [F] using iToD_map_bijective X Y
  -- Proof comment: once `F` is known to be fully faithful, it reflects isomorphisms formally.
  letI : F.ReflectsIsomorphisms := Functor.FullyFaithful.reflectsIsomorphisms hFF
  exact Functor.ReflectsIsomorphisms.reflects F g

namespace HomotopyResolutionFunctor

/-- Helper for Proposition 13.23.1: a homotopy resolution functor sends bounded-below
quasi-isomorphisms to isomorphisms of `K^+(\mathcal I)`. -/
theorem isInvertedBy (j : HomotopyResolutionFunctor 𝒜) :
    MorphismProperty.IsInvertedBy (Qis⁺(𝒜)) j.toFunctor := by
  intro X Y f hf
  let F : K⁺ᵢ(𝒜) ⥤ D⁺(𝒜) := IToD
  have hnat :
      Q.map (j.ι.app X) ≫ F.map (j.toFunctor.map f) =
        Q.map f ≫ Q.map (j.ι.app Y) := by
    -- Proof comment: applying the localization to the naturality square for `j.ι` expresses the
    -- resolved morphism in terms of quasi-isomorphisms that are already inverted by `Q`.
    simpa [F, Functor.comp_map, Category.assoc] using congrArg Q.map (j.ι.naturality f)
  let _ : IsIso (Q.map (j.ι.app X)) := by
    -- Proof comment: each comparison map of the resolution functor is a quasi-isomorphism.
    exact Localization.inverts Q (Qis⁺(𝒜)) _ (j.quasiIso_app X)
  let _ : IsIso (Q.map (j.ι.app Y)) := by
    exact Localization.inverts Q (Qis⁺(𝒜)) _ (j.quasiIso_app Y)
  let _ : IsIso (Q.map f) := by
    -- Proof comment: the localization functor inverts the given bounded-below quasi-isomorphism.
    exact Localization.inverts Q (Qis⁺(𝒜)) _ hf
  have hFmap :
      IsIso (F.map (j.toFunctor.map f)) := by
    have hrewrite :
        F.map (j.toFunctor.map f) =
          inv (Q.map (j.ι.app X)) ≫ Q.map f ≫ Q.map (j.ι.app Y) := by
      -- Proof comment: solve for the middle arrow in the localized naturality identity.
      calc
        F.map (j.toFunctor.map f)
            = inv (Q.map (j.ι.app X)) ≫
                (Q.map (j.ι.app X) ≫ F.map (j.toFunctor.map f)) := by
              simp
        _ = inv (Q.map (j.ι.app X)) ≫ (Q.map f ≫ Q.map (j.ι.app Y)) := by
              rw [hnat]
        _ = inv (Q.map (j.ι.app X)) ≫ Q.map f ≫ Q.map (j.ι.app Y) := by
              simp [Category.assoc]
    rw [hrewrite]
    infer_instance
  let _ : IsIso (F.map (j.toFunctor.map f)) := hFmap
  -- Proof comment: reflect the isomorphism back along the fully faithful injective-to-derived
  -- functor.
  simpa [F] using iToD_reflects_isIso (𝒜 := 𝒜) (j.toFunctor.map f)

noncomputable abbrev lift (j : HomotopyResolutionFunctor 𝒜) :
    D⁺(𝒜) ⥤ K⁺ᵢ(𝒜) :=
  Localization.lift j.toFunctor (isInvertedBy j) Q

noncomputable abbrev liftCompIso (j : HomotopyResolutionFunctor 𝒜) :
    Q ⋙ j.lift ≅ j.toFunctor :=
  Localization.fac j.toFunctor (isInvertedBy j) Q

private noncomputable def toDerivedIso (j : HomotopyResolutionFunctor 𝒜) :
    Q ≅ j.toFunctor ⋙ IToD := by
  let τ : Q ⟶ j.toFunctor ⋙ IToD :=
    (Functor.leftUnitor Q).inv ≫ Functor.whiskerRight j.ι Q ≫
      (Functor.associator j.toFunctor KinjIncl Q).hom
  have hτ : ∀ X, IsIso (τ.app X) := by
    intro X
    haveI : IsIso ((Functor.whiskerRight j.ι Q).app X) := by
      simpa using (Localization.inverts Q (Qis⁺(𝒜)) _ (j.quasiIso_app X))
    change IsIso ((Functor.leftUnitor Q).inv.app X ≫
      (Functor.whiskerRight j.ι Q).app X ≫
      (Functor.associator j.toFunctor KinjIncl Q).hom.app X)
    infer_instance
  exact NatIso.ofComponents (fun X ↦ asIso (τ.app X)) (fun f ↦ τ.naturality f)

noncomputable def lift_unitIso (j : HomotopyResolutionFunctor 𝒜) :
    𝟭 (D⁺(𝒜)) ≅ j.lift ⋙ IToD := by
  let e : Q ≅ Q ⋙ (j.lift ⋙ IToD) :=
    j.toDerivedIso ≪≫
      Functor.isoWhiskerRight (j.liftCompIso).symm IToD ≪≫
      Functor.associator Q j.lift IToD
  exact
    Localization.liftNatIso Q (Qis⁺(𝒜)) Q (Q ⋙ (j.lift ⋙ IToD)) (𝟭 (D⁺(𝒜)))
      (j.lift ⋙ IToD) e

end HomotopyResolutionFunctor

namespace HomotopyResolutionFunctor

/-- Proposition 13.23.1, canonical owner form: for any homotopy resolution functor
`j : K^+(\mathcal A) ⥤ K^+(\mathcal I)`, the canonical functor
`K^+(\mathcal I) ⥤ D^+(\mathcal A)` is an equivalence of categories. -/
@[stacks 013V]
theorem toDerived_isEquivalence (j : HomotopyResolutionFunctor 𝒜) :
    Functor.IsEquivalence
      (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
        mapBoundedBelowHomotopyToDerivedBelow) := by
  let F : K⁺ᵢ(𝒜) ⥤ D⁺(𝒜) := IToD
  obtain ⟨hFF⟩ :
      Nonempty F.FullyFaithful := by
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro X Y
    simpa [F] using iToD_map_bijective X Y
  let _ : F.Full := hFF.full
  let _ : F.Faithful := hFF.faithful
  simpa [F] using F.fully_faithful_isEquivalence_of_objwise_iso
    (fun X ↦ j.lift.obj X) (fun X ↦ (j.lift_unitIso).app X)

end HomotopyResolutionFunctor

-- Proof sketch: essential surjectivity is obtained by choosing bounded-below injective
-- resolutions in the presence of enough injectives, while full faithfulness follows from the
-- bijection between homotopy and derived morphisms into bounded-below injective complexes.
/-- Proposition 13.23.1: if an abelian category `𝒜` has enough injectives, then the canonical
functor `K^+(\mathcal I) ⥤ D^+(\mathcal A)` from bounded-below complexes of injective objects to
the bounded-below derived category is an equivalence of categories. -/
@[stacks 013V]
theorem boundedBelowInjectiveHomotopyToDerived_isEquivalence [EnoughInjectives 𝒜] :
    Functor.IsEquivalence
      (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
        mapBoundedBelowHomotopyToDerivedBelow) := by
  obtain ⟨j⟩ : Nonempty (HomotopyResolutionFunctor 𝒜) := exists_homotopyResolutionFunctor
  simpa using j.toDerived_isEquivalence

end

end CategoryTheory
