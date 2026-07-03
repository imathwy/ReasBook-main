import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import StacksProject_2024.Chap13.Definition_13_14_10
import StacksProject_2024.Chap13.Lemma_13_5_8
import StacksProject_2024.Chap13.Lemma_13_11_6
import StacksProject_2024.Chap15.Lemma_15_96_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped nonZeroDivisors

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

/- Domain-style sampling:
- primary domain: left-derived endofunctors on derived categories, built from the Berthelot-Ogus
  operator on bounded-below cochain complexes of `A`-modules;
- sampled owner declarations in the project:
  `fullSubcategoryLocalizationSystem`,
  `HomotopyCategory.Plus.quotient`,
  `mapBoundedBelowHomotopyToDerivedBelow`,
  `Functor.totalLeftDerived`,
  `Functor.ComputesLeftDerivedAt`;
- best owner abstraction:
  `source-facing`: Lemma `15.96.4`, asserting existence of a derived endofunctor whose
    representative-level action on termwise `f`-torsion-free nonnegative complexes is `η_f`;
  `core/canonical`: the restricted quasi-isomorphism system on the torsion-free full subcategory,
    the bounded-below localization chain
    `Comp⁺(A) ⥤ K⁺(A) ⥤ D⁺(A) ⥤ D(A)`, and the Chapter `13` owners
    `Functor.HasLeftDerivedFunctor` / `Functor.ComputesLeftDerivedAt`;
  `bridge/view`: the full subcategory of termwise `f`-torsion-free complexes and the comparison
    natural isomorphism on representatives.
- primitive data vs derived API: the primitive data are the source-facing `η_f` endofunctor on
  `NatModuleCochainComplex A`, the torsion-free full subcategory, the restricted quasi-isomorphism
  system, and the canonical functor from nonnegative complexes to the derived category through the
  bounded-below owner layer. The theorem-level existence statement is derived API and should be
  expressed through the Chapter `13` derived/localization owners, with the raw existential
  factorization kept only as a consequence.
-/

/-- The object property of being termwise `f`-torsion free for an `ℕ`-indexed cochain complex of
`A`-modules. -/
abbrev fTorsionFreeNatComplexProperty (f : A) : ObjectProperty (NatModuleCochainComplex A) :=
  IsTermwiseFTorsionFree f

/-- The full subcategory of `ℕ`-indexed cochain complexes of `A`-modules whose terms are
`f`-torsion free. -/
abbrev FTorsionFreeNatComplex (A : Type u) [CommRing A] (f : A) :=
  (fTorsionFreeNatComplexProperty f).FullSubcategory

/-- The quasi-isomorphism system on the full subcategory of termwise `f`-torsion-free
`ℕ`-indexed cochain complexes of `A`-modules. -/
abbrev fTorsionFreeNatComplexQuasiIso (f : A) :
    MorphismProperty (FTorsionFreeNatComplex A f) :=
  fullSubcategoryLocalizationSystem
    (fTorsionFreeNatComplexProperty f)
    (HomologicalComplex.quasiIso (ModuleCat A) (up ℕ))

-- Proof sketch: each term of `etaFComplex f M` is a submodule of the corresponding term of `M`,
-- so injectivity of multiplication by `f` on `M.X n` restricts to injectivity on the degree-`n`
-- term of `η_f M`.
/-- The Berthelot-Ogus complex of a termwise `f`-torsion-free complex is again termwise
`f`-torsion free. -/
theorem etaFComplex_preserves_termwiseFTorsionFree
    (f : A) (M : NatModuleCochainComplex A) (hM : IsTermwiseFTorsionFree f M) :
    IsTermwiseFTorsionFree f (η[f] M) := sorry

-- Proof sketch: `etaFMap f (𝟙 M)` is obtained by conjugating the owner-level identity morphism
-- `BerthelotOgusInt.map f (extendMap (𝟙 M) _)` by the canonical restriction isomorphisms from
-- `Lemma_15_96_2`, so it is itself the identity.
/-- The Berthelot-Ogus construction sends identity morphisms of complexes to identity morphisms. -/
theorem etaFMap_id (f : A) (M : NatModuleCochainComplex A) :
    etaFMap f (𝟙 M) = 𝟙 (η[f] M) := sorry

-- Proof sketch: `etaFMap` is the bounded-below bridge of the owner-level functorial map
-- `BerthelotOgusInt.map`. Functoriality of `extendMap`, `BerthelotOgusInt.map`, and
-- `restrictionMap` gives the composite formula after conjugating by the canonical restriction
-- isomorphisms.
/-- The Berthelot-Ogus construction sends composites of morphisms of complexes to composites. -/
theorem etaFMap_comp (f : A) {M N K : NatModuleCochainComplex A}
    (φ : M ⟶ N) (ψ : N ⟶ K) :
    etaFMap f (φ ≫ ψ) = etaFMap f φ ≫ etaFMap f ψ := sorry

/-- The Berthelot-Ogus operator as an endofunctor on `ℕ`-indexed cochain complexes. -/
def etaFEndofunctor (f : A) : NatModuleCochainComplex A ⥤ NatModuleCochainComplex A where
  obj M := η[f] M
  map φ := etaFMap f φ
  map_id M := etaFMap_id f M
  map_comp φ ψ := etaFMap_comp f φ ψ

/-- The Berthelot-Ogus operator on the full subcategory of termwise `f`-torsion-free
`ℕ`-indexed cochain complexes. -/
def etaFTorsionFreeEndofunctor (f : A) :
    FTorsionFreeNatComplex A f ⥤ FTorsionFreeNatComplex A f :=
  (fTorsionFreeNatComplexProperty f).lift
    ((fTorsionFreeNatComplexProperty f).ι ⋙ etaFEndofunctor f)
    (fun M ↦ etaFComplex_preserves_termwiseFTorsionFree f M.obj M.property)

/-- The extension of an `ℕ`-indexed cochain complex of `A`-modules to a bounded below
`ℤ`-indexed cochain complex. -/
noncomputable def natComplexToPlus :
    NatModuleCochainComplex A ⥤ CochainComplex.Plus (ModuleCat A) :=
  (CochainComplex.plus (ModuleCat A)).lift
    (embeddingUpNat.extendFunctor (ModuleCat A))
    (fun M ↦ ⟨0, by
      change CochainComplex.IsStrictlyGE (M.extend embeddingUpNat) 0
      infer_instance⟩)

/-- The functor from `ℕ`-indexed cochain complexes of `A`-modules to the derived category,
obtained by passing through the canonical bounded-below homotopy and derived owners from
Chapter `13`. -/
noncomputable def natComplexToDerived :
    NatModuleCochainComplex A ⥤ DerivedCategory (ModuleCat A) :=
  natComplexToPlus ⋙
    HomotopyCategory.Plus.quotient (ModuleCat A) ⋙
    mapBoundedBelowHomotopyToDerivedBelow ⋙
    (t.plus : ObjectProperty (DerivedCategory (ModuleCat A))).ι

-- Proof sketch: let `𝒯` be the full subcategory of termwise `f`-torsion-free complexes.
-- Flat resolutions give quasi-isomorphic representatives in `𝒯`, so the localization of `𝒯`
-- by quasi-isomorphisms identifies with `D(A)`. Lemma `15.96.3` shows that `η_f` preserves
-- quasi-isomorphisms on `𝒯`, hence it descends through this localization to the required
-- additive endofunctor, and every torsion-free representative computes this left derived functor.
/-- Lemma 15.96.4, canonical Chapter `13` form: for a ring `A` and a nonzerodivisor `f : A`,
the functor on termwise `f`-torsion-free representatives obtained by applying `η_f` and then
passing to the derived category admits a left derived functor along the canonical representative
functor from the torsion-free full subcategory to `D(A)`, and every torsion-free representative
computes that left derived functor. -/
theorem exists_left_derived_etaF_functor
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    let L : FTorsionFreeNatComplex A f ⥤ DerivedCategory (ModuleCat A) :=
      (fTorsionFreeNatComplexProperty f).ι ⋙ natComplexToDerived
    let ηL : FTorsionFreeNatComplex A f ⥤ DerivedCategory (ModuleCat A) :=
      etaFTorsionFreeEndofunctor f ⋙ L
    ∃ hL : Functor.IsLocalization L (fTorsionFreeNatComplexQuasiIso f),
      let _ : Functor.IsLocalization L (fTorsionFreeNatComplexQuasiIso f) := hL
      ηL.HasLeftDerivedFunctor (fTorsionFreeNatComplexQuasiIso f) ∧
        ∀ X : FTorsionFreeNatComplex A f,
          ηL.ComputesLeftDerivedAt (fTorsionFreeNatComplexQuasiIso f) X := sorry

-- Proof sketch: once the localization instance and left-derived existence statement above are in
-- place, take the canonical total left derived functor and use that each torsion-free
-- representative computes it. Definition `13.14.10` upgrades objectwise computation to
-- invertibility of the total counit components, yielding a natural isomorphism on representatives.
/-- Lemma 15.96.4, existential corollary: the canonical Chapter `13` derived-functor statement
implies the traditional formulation that there exists an additive endofunctor on `D(A)` whose
value on a termwise `f`-torsion-free representative is `η_f` of that representative. -/
theorem exists_left_derived_etaF_functor_iso
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    let L : FTorsionFreeNatComplex A f ⥤ DerivedCategory (ModuleCat A) :=
      (fTorsionFreeNatComplexProperty f).ι ⋙ natComplexToDerived
    let ηL : FTorsionFreeNatComplex A f ⥤ DerivedCategory (ModuleCat A) :=
      etaFTorsionFreeEndofunctor f ⋙ L
    ∃ (F : DerivedCategory (ModuleCat A) ⥤ DerivedCategory (ModuleCat A)) (_ : F.Additive),
      Nonempty (L ⋙ F ≅ ηL) := sorry

end
