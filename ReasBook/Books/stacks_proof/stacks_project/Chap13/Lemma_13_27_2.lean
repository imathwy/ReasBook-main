import Mathlib
import stacks_proof.stacks_project.Chap13.Definition_13_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory
open scoped DerivedExt

noncomputable section

universe v u

namespace CochainComplex

section

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

/-- Helper for Lemma 13.27.2: an injective resolution of a cochain complex is a quasi-isomorphism
to a bounded-below cochain complex with injective terms. -/
structure InjectiveResolution (K : CochainComplex 𝒜 ℤ) where
  /-- The resolving bounded-below cochain complex. -/
  complex : CochainComplex 𝒜 ℤ
  /-- The resolving complex vanishes in sufficiently negative degrees. -/
  boundedBelow : ∃ a : ℤ, complex.IsStrictlyGE a
  /-- Each term of the resolving complex is injective. -/
  injective : ∀ n : ℤ, Injective (complex.X n)
  /-- The comparison morphism from the target complex to the resolving complex. -/
  ι : K ⟶ complex
  /-- The comparison morphism is a quasi-isomorphism. -/
  quasiIso : QuasiIso ι

attribute [instance] InjectiveResolution.quasiIso

namespace InjectiveResolution

/-- Helper for Lemma 13.27.2: an injective resolution is used through its underlying cochain
complex. -/
instance {K : CochainComplex 𝒜 ℤ} : CoeOut (InjectiveResolution K) (CochainComplex 𝒜 ℤ) where
  coe I := I.complex

/-- Helper for Lemma 13.27.2: the resolving complex of an injective resolution is K-injective. -/
instance instIsKInjective {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    IsKInjective (I : CochainComplex 𝒜 ℤ) := by
  obtain ⟨a, ha⟩ := I.boundedBelow
  let _ : (I : CochainComplex 𝒜 ℤ).IsStrictlyGE a := ha
  let _ : ∀ n : ℤ, Injective ((I : CochainComplex 𝒜 ℤ).X n) := I.injective
  exact isKInjective_of_injective (I : CochainComplex 𝒜 ℤ) a

end InjectiveResolution

/-- Helper for Lemma 13.27.2: a projective resolution of a cochain complex is a quasi-isomorphism
from a bounded-above cochain complex with projective terms. -/
structure ProjectiveResolution (K : CochainComplex 𝒜 ℤ) where
  /-- The resolving bounded-above cochain complex. -/
  complex : CochainComplex 𝒜 ℤ
  /-- The resolving complex vanishes in sufficiently high degrees. -/
  boundedAbove : ∃ d : ℤ, complex.IsStrictlyLE d
  /-- Each term of the resolving complex is projective. -/
  projective : ∀ n : ℤ, Projective (complex.X n)
  /-- The comparison morphism from the resolving complex to the target complex. -/
  π : complex ⟶ K
  /-- The comparison morphism is a quasi-isomorphism. -/
  quasiIso : QuasiIso π

attribute [instance] ProjectiveResolution.quasiIso

namespace ProjectiveResolution

/-- Helper for Lemma 13.27.2: a projective resolution is used through its underlying cochain
complex. -/
instance {K : CochainComplex 𝒜 ℤ} : CoeOut (ProjectiveResolution K) (CochainComplex 𝒜 ℤ) where
  coe P := P.complex

/-- Helper for Lemma 13.27.2: the resolving complex of a projective resolution is K-projective. -/
instance instIsKProjective {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    IsKProjective (P : CochainComplex 𝒜 ℤ) := by
  obtain ⟨d, hd⟩ := P.boundedAbove
  let _ : (P : CochainComplex 𝒜 ℤ).IsStrictlyLE d := hd
  let _ : ∀ n : ℤ, Projective ((P : CochainComplex 𝒜 ℤ).X n) := P.projective
  exact isKProjective_of_projective (P : CochainComplex 𝒜 ℤ) d

end ProjectiveResolution

/- Domain-style sampling for Lemma 13.27.2:
- primary domain: morphisms in the derived category of cochain complexes, computed from
  K-injective and K-projective resolutions;
- sampled owner API:
  `CategoryTheory.Abelian.Ext.homAddEquiv`,
  `DerivedCategory.Q.commShiftIso`,
  `DerivedCategory.Qh.mapAddHom`,
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedBelow_injective`,
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective`,
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.ProjectiveResolution`;
- best owner abstraction: the canonical quotient functors
  `HomotopyCategory.quotient 𝒜 (up ℤ)` and `DerivedCategory.Qh`, together with their shift
  compatibilities and the chapter owner bijectivity theorems for bounded-below injective and
  bounded-above projective complexes;
- primitive data: a chosen injective or projective resolution;
- derived API: the owner-level shifted-Hom comparison equivalences
  `InjectiveResolution.extAddEquiv` and `ProjectiveResolution.extAddEquiv`.

Source/core/bridge triage:
- `source-facing`: the Ext-computation statements with a chosen injective or projective
  resolution;
- `core/canonical`: `Q.commShiftIso`, `quotientCompQhIso`, and the owner bijectivity theorems
  for `Qh.mapAddHom`;
- `bridge/view`: the owner-level equivalences below transporting raw Hom-types to `ShiftedHom`.

The local raw-Hom helper abbreviations were duplicate shells around this owner API, so the file
should expose only the source-facing additive bridge equivalences on the chosen resolution owners.
-/

/-- Helper for Lemma 13.27.2: transporting a morphism along source and target isomorphisms
preserves addition. -/
private theorem isoHomCongrAddEquiv_map_add
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
    (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  -- Proof comment: `Iso.homCongr` is composition with the isomorphism legs, so additivity is
  -- exactly bilinearity of composition in a preadditive category.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Lemma 13.27.2: isomorphisms on source and target induce an additive equivalence on
Hom groups. -/
private noncomputable def isoHomCongrAddEquiv
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) :=
  { toEquiv := α.homCongr β
    map_add' := isoHomCongrAddEquiv_map_add α β }

namespace InjectiveResolution

variable {Y : CochainComplex 𝒜 ℤ}

/-- Lemma 13.27.2 (1): if `Y^• ⟶ I^•` is an injective resolution, then
`Ext^i_{\mathcal A}(X^•, Y^•)` is computed by the shifted homotopy-category morphisms
`Hom_{K(\mathcal A)}(X^•, I^•[i])` as an additive equivalence. -/
@[stacks 06XR]
noncomputable def extAddEquiv (I : InjectiveResolution Y) (X : CochainComplex 𝒜 ℤ) (i : ℤ) :
    Ext^i(Q.obj X, Q.obj Y) ≃+ Ext^i((KQ).obj X, (KQ).obj I) :=
  let e₁ :
      Ext^i(Q.obj X, Q.obj Y) ≃+ (Q.obj X ⟶ Q.obj (Y⟦i⟧)) :=
    -- Proof comment: rewrite derived `Ext` as ordinary morphisms into the shifted target.
    isoHomCongrAddEquiv (Iso.refl _) ((Q.commShiftIso i).app Y).symm
  let e₂ :
      (Q.obj X ⟶ Q.obj (Y⟦i⟧)) ≃+ (Q.obj X ⟶ Q.obj (I⟦i⟧)) :=
    -- Proof comment: the shifted quasi-isomorphism `Y⟦i⟧ ⟶ I⟦i⟧` lets us replace the target by
    -- the shifted injective resolution object in the derived category.
    isoHomCongrAddEquiv (Iso.refl _) (asIso (Q.map (I.ι⟦i⟧')))
  let hQhBijective :
      Function.Bijective
        (Qh.map : ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) → _) :=
    IsKInjective.Qh_map_bijective ((KQ).obj X) (I⟦i⟧)
  let e₃ :
      (Q.obj X ⟶ Q.obj (I⟦i⟧)) ≃+ ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) :=
    -- Proof comment: K-injectivity of the shifted resolution identifies derived morphisms with
    -- homotopy-category morphisms.
    (AddEquiv.ofBijective
        (Qh.mapAddHom : ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) →+ _)
        hQhBijective).symm
  let e₄ :
      ((KQ).obj X ⟶ (KQ).obj (I⟦i⟧)) ≃+ Ext^i((KQ).obj X, (KQ).obj I) :=
    -- Proof comment: commute the shift back through the quotient functor to read the result as
    -- a shifted Hom group in the homotopy category.
    isoHomCongrAddEquiv (Iso.refl _) (((quotient 𝒜 (up ℤ)).commShiftIso i).app I)
  (e₁.trans (e₂.trans e₃)).trans e₄

end InjectiveResolution

namespace ProjectiveResolution

variable {X : CochainComplex 𝒜 ℤ}

/-- Lemma 13.27.2 (2): if `P^• ⟶ X^•` is a projective resolution, then
`Ext^i_{\mathcal A}(X^•, Y^•)` is computed by the shifted homotopy-category morphisms out of
`P^•`, equivalently by `Hom_{K(\mathcal A)}(P^•[-i], Y^•)`, as an additive equivalence. -/
@[stacks 06XR]
noncomputable def extAddEquiv (P : ProjectiveResolution X) (Y : CochainComplex 𝒜 ℤ) (i : ℤ) :
    Ext^i(Q.obj X, Q.obj Y) ≃+ Ext^i((KQ).obj P, (KQ).obj Y) :=
  let e₁ :
      Ext^i(Q.obj X, Q.obj Y) ≃+ (Q.obj X ⟶ Q.obj (Y⟦i⟧)) :=
    -- Proof comment: expand the derived `Ext` group into morphisms to the shifted target.
    isoHomCongrAddEquiv (Iso.refl _) ((Q.commShiftIso i).app Y).symm
  let e₂ :
      (Q.obj X ⟶ Q.obj (Y⟦i⟧)) ≃+ (Q.obj P ⟶ Q.obj (Y⟦i⟧)) :=
    -- Proof comment: the projective resolution map becomes an isomorphism in the derived
    -- category, so we may replace the source `X` by its projective model `P`.
    isoHomCongrAddEquiv (asIso (Q.map P.π)).symm (Iso.refl _)
  let hQhBijective :
      Function.Bijective
        (Qh.map : ((KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) → _) :=
    IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) ((KQ).obj (Y⟦i⟧))
  let e₃ :
      (Q.obj P ⟶ Q.obj (Y⟦i⟧)) ≃+ ((KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) :=
    -- Proof comment: bounded-above projectivity of `P` identifies derived morphisms out of `P`
    -- with homotopy-category morphisms.
    (AddEquiv.ofBijective
        (Qh.mapAddHom : ((KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) →+ _)
        hQhBijective).symm
  let e₄ :
      ((KQ).obj P ⟶ (KQ).obj (Y⟦i⟧)) ≃+ Ext^i((KQ).obj P, (KQ).obj Y) :=
    -- Proof comment: commute the shift through the quotient functor to recover the shifted Hom
    -- presentation in the homotopy category.
    isoHomCongrAddEquiv (Iso.refl _) (((quotient 𝒜 (up ℤ)).commShiftIso i).app Y)
  (e₁.trans (e₂.trans e₃)).trans e₄

end ProjectiveResolution

end

end CochainComplex
