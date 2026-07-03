import Mathlib
import Mathlib.CategoryTheory.Sites.LocallySurjective

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_13_1 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Sheaf
open Opposite CategoryOfElements

noncomputable section

universe u v

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J (Type (max u v))]
variable (𝒪 : Sheaf J RingCat.{max u v})

/-- The pullback of the structure sheaf `\mathcal O` to the localized site `\mathcal C/K`. -/
abbrev localizationRingSheaf
    (K : Sheaf J (Type (max u v))) :
    Sheaf (localizationTopology K) RingCat.{max u v} :=
  (CategoryTheory.Functor.sheafPushforwardContinuous (localizationProjection K)
    RingCat.{max u v} (localizationTopology K) J).obj 𝒪

/-- The inverse-image functor on abelian sheaves for localization at a sheaf of sets `K`. -/
abbrev localizationInverseImage
    (K : Sheaf J (Type (max u v))) :
    Sheaf J AddCommGrpCat.{max u v} ⥤
      Sheaf (localizationTopology K) AddCommGrpCat.{max u v} :=
  (CategoryTheory.Functor.sheafPushforwardContinuous (localizationProjection K)
    AddCommGrpCat.{max u v} (localizationTopology K) J)

/-- The cohomology of an abelian sheaf over a sheaf of sets `K`, computed on the localized site
`\mathcal C/K`. -/
abbrev cohomologyOverSheaf
    (K : Sheaf J (Type (max u v)))
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasExt (Sheaf (localizationTopology K) AddCommGrpCat.{max u v})]
    (F : Sheaf J AddCommGrpCat.{max u v}) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of (((localizationInverseImage K).obj F).H p)

/-- Restriction of `\mathcal O`-modules from the base ringed site to the localized ringed site
over a sheaf of sets `K`. -/
abbrev localizationModuleRestriction
    (K : Sheaf J (Type (max u v))) :
    SheafOfModules 𝒪 ⥤ SheafOfModules (localizationRingSheaf 𝒪 K) :=
  SheafOfModules.pushforward (𝟙 (localizationRingSheaf 𝒪 K))

/-- Module cohomology over a sheaf of sets `K`, computed on the localized ringed site
`(\mathcal C/K, \mathcal O|_K)`. -/
abbrev moduleCohomologyOverSheaf
    (K : Sheaf J (Type (max u v)))
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasExt (Sheaf (localizationTopology K) AddCommGrpCat.{max u v})]
    [HasExt (SheafOfModules (localizationRingSheaf 𝒪 K))]
    (ℱ : SheafOfModules 𝒪) (p : ℕ) : AddCommGrpCat.{max u v} :=
  (Abelian.extFunctorObj (SheafOfModules.unit (localizationRingSheaf 𝒪 K)) p).obj
    ((localizationModuleRestriction 𝒪 K).obj ℱ)

-- Proof sketch: apply Lemma `21.12.4 (1)` on the localized ringed site
-- `(\mathcal C/K, \mathcal O|_K)` to the restricted module `j_K^* \mathcal F`. The resulting
-- comparison identifies module cohomology on the localized ringed site with the cohomology of the
-- underlying abelian sheaf pulled back to `\mathcal C/K`, which is exactly
-- `cohomologyOverSheaf K \mathcal F_{ab}` by Definition `21.13.3`.
/-- The module cohomology of an `\mathcal O`-module over a sheaf of sets `K` agrees with the
cohomology of its underlying abelian sheaf over `K`. -/
theorem moduleCohomologyOverSheaf_eq_underlyingAbelianSheafCohomology
    (K : Sheaf J (Type (max u v)))
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{max u v}]
    [HasExt (Sheaf (localizationTopology K) AddCommGrpCat.{max u v})]
    [HasExt (SheafOfModules (localizationRingSheaf 𝒪 K))]
    (ℱ : SheafOfModules 𝒪) (p : ℕ) :
    moduleCohomologyOverSheaf 𝒪 K ℱ p =
      cohomologyOverSheaf K ((SheafOfModules.toSheaf 𝒪).obj ℱ) p := sorry

-- Proof sketch: replace the presheaf of sets `K` by its sheafification `aK`. By definition,
-- `H^p(K, \mathcal F)` is computed on the localized ringed site over `aK`, and the preceding
-- localized-site comparison identifies this with the cohomology of the underlying abelian sheaf
-- over `aK`.
/-- Lemma 21.13.1: for a ringed site `(\mathcal C, \mathcal O)`, a presheaf of sets `K`, and an
`\mathcal O`-module `\mathcal F`, the cohomology `H^p(K, \mathcal F)` computed after sheafifying
`K` agrees with the cohomology `H^p(K, \mathcal F_{ab})` of the underlying sheaf of abelian
groups. -/
theorem moduleCohomologyOverPresheaf_eq_underlyingAbelianSheafCohomology
    (K : Cᵒᵖ ⥤ Type (max u v))
    [HasWeakSheafify (localizationTopology ((presheafToSheaf J (Type (max u v))).obj K))
      AddCommGrpCat.{max u v}]
    [HasSheafify (localizationTopology ((presheafToSheaf J (Type (max u v))).obj K))
      AddCommGrpCat.{max u v}]
    [HasGlobalSectionsFunctor
      (localizationTopology ((presheafToSheaf J (Type (max u v))).obj K))
      AddCommGrpCat.{max u v}]
    [HasExt
      (Sheaf (localizationTopology ((presheafToSheaf J (Type (max u v))).obj K))
        AddCommGrpCat.{max u v})]
    [HasExt
      (SheafOfModules
        (localizationRingSheaf 𝒪 ((presheafToSheaf J (Type (max u v))).obj K)))]
    (ℱ : SheafOfModules 𝒪) (p : ℕ) :
    moduleCohomologyOverSheaf 𝒪 ((presheafToSheaf J (Type (max u v))).obj K) ℱ p =
      cohomologyOverSheaf ((presheafToSheaf J (Type (max u v))).obj K)
        ((SheafOfModules.toSheaf 𝒪).obj ℱ) p := sorry

end Sheaf
end CategoryTheory

/-! ### Lemma_21_13_2 (from Chap21) -/
open CategoryTheory Opposite
open CategoryTheory.Abelian

noncomputable section

universe v u

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J (Type (max u v))]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]

/-- The sheafified arrow associated to a map of presheaves of sets on a site. -/
abbrev sheafifiedArrow {K K' : Cᵒᵖ ⥤ Type (max u v)} (φ : K' ⟶ K) :
    Arrow (Sheaf J (Type (max u v))) :=
  Arrow.mk ((presheafToSheaf J (Type (max u v))).map φ)

/-- The `p`-th object of the Čech nerve of the sheafified map associated to `φ`. This is the
sheafified version of the iterated fiber product
`K' ×_K ⋯ ×_K K'` with `p + 1` factors. -/
abbrev sheafifiedCechLevel {K K' : Cᵒᵖ ⥤ Type (max u v)} (φ : K' ⟶ K) (p : ℕ) :
    Sheaf J (Type (max u v)) :=
  (sheafifiedArrow φ).cechNerve.obj (op (SimplexCategory.mk p))

/-- A first-quadrant spectral sequence attached to a locally surjective map of presheaves of sets.
Its `E₁`-page is the cohomology of an abelian sheaf over the sheafified Čech nerve levels of the
map, written as Ext from the free abelian sheaf generated by each level. -/
structure LocallySurjectiveCechSpectralSequence
    {K K' : Cᵒᵖ ⥤ Type (max u v)} (φ : K' ⟶ K)
    (F : Sheaf J AddCommGrpCat.{max u v}) where
  /-- The chosen first-quadrant cohomological spectral sequence. -/
  spectralSequence : CohomologicalSpectralSequenceNat AddCommGrpCat 1
  /-- The `E₁`-page is the cohomology of `F` over the sheafified Čech simplices of `φ`. -/
  pageOneIso :
    ∀ p q : ℕ,
      (spectralSequence.page 1).X (p, q) ≅
        AddCommGrpCat.of
          (Ext
            ((sheafToPresheaf J (Type (max u v)) ⋙
                (Functor.whiskeringRight Cᵒᵖ (Type (max u v)) AddCommGrpCat).obj
                  AddCommGrpCat.free ⋙
                presheafToSheaf J AddCommGrpCat).obj
              (sheafifiedCechLevel φ p))
            F
            q)
  /-- The chosen abutment objects of the spectral sequence. -/
  abutment : ℕ → AddCommGrpCat.{max u v}
  /-- The abutment identifies with the cohomology of `F` over the sheafification of `K`. -/
  targetIso :
    ∀ n : ℕ,
      abutment n ≅
        AddCommGrpCat.of
          (Ext
            ((sheafToPresheaf J (Type (max u v)) ⋙
                (Functor.whiskeringRight Cᵒᵖ (Type (max u v)) AddCommGrpCat).obj
                  AddCommGrpCat.free ⋙
                presheafToSheaf J AddCommGrpCat).obj
              ((presheafToSheaf J (Type (max u v))).obj K))
            F
            n)

-- Proof sketch: replace the map of presheaves by its sheafification, using left exactness of
-- sheafification to identify the sheafified Čech nerve levels with the sheafifications of the
-- iterated fiber products `K'_p`. After enlarging the site as in Lemma `7.29.5`, represent the
-- sheafified map by a covering of an object and apply the Čech-to-cohomology spectral sequence of
-- Lemma `21.10.6` on the localized site.
/-- Lemma 21.13.2: let `φ : K' ⟶ K` be a map of presheaves of sets on a site whose sheafification
is surjective, formalized here by `Presheaf.IsLocallySurjective J φ`. Then for every abelian sheaf `F`
there is a first-quadrant spectral sequence whose `E_1^{p,q}` term is the cohomology of `F` over
the sheafified Čech `p`-simplex of `φ`, i.e. the sheafified form of
`K'_p = K' ×_K ⋯ ×_K K'`, and whose abutment is the cohomology of `F` over the sheafification of
`K`. -/
theorem exists_cechSpectralSequence_of_isLocallySurjective
    {K K' : Cᵒᵖ ⥤ Type (max u v)} (φ : K' ⟶ K)
    (hφ : Presheaf.IsLocallySurjective J φ)
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    Nonempty (LocallySurjectiveCechSpectralSequence φ F) := sorry

end Sheaf
end CategoryTheory

/-! ### Lemma_21_13_3 (from Chap21) -/
open CategoryTheory Opposite CategoryOfElements
open CategoryTheory.Sheaf

noncomputable section

universe u v

namespace CategoryTheory
namespace Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The inverse-image functor on abelian sheaves for the localization morphism at `K`. -/
abbrev localizationInverseImage (K : Sheaf J (Type v)) :
    Sheaf J AddCommGrpCat.{v} ⥤ Sheaf (localizationTopology K) AddCommGrpCat.{v} :=
  Functor.sheafPushforwardContinuous (localizationProjection K)
    AddCommGrpCat.{v} (localizationTopology K) J

/-- The cohomology of an abelian sheaf over a sheaf of sets, computed on the localized site. -/
abbrev cohomologyOverSheaf (K : Sheaf J (Type v))
    [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasSheafify (localizationTopology K) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{v}]
    [HasExt (Sheaf (localizationTopology K) AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) : AddCommGrpCat.{v} :=
  AddCommGrpCat.of (((localizationInverseImage K).obj F).H p)

-- Proof sketch: the localization morphism at `K` is presented by the projection from the
-- category of elements of `K`; apply the standard exact-left-adjoint criterion for a geometric
-- inverse-image functor.
/-- Lemma 21.13.3 (1): the inverse-image functor of the localization morphism
`j : \operatorname{Sh}(\mathcal C/K) \to \operatorname{Sh}(\mathcal C)` preserves injective
abelian sheaves. -/
theorem localizationInverseImage_preserves_injective
    (K : Sheaf J (Type v)) (F : Sheaf J AddCommGrpCat.{v}) (hF : Injective F) :
    Injective ((localizationInverseImage K).obj F) := sorry

variable (K : Sheaf J (Type v))
variable [HasWeakSheafify (localizationTopology K) AddCommGrpCat.{v}]
variable [HasSheafify (localizationTopology K) AddCommGrpCat.{v}]
variable [HasGlobalSectionsFunctor (localizationTopology K) AddCommGrpCat.{v}]
variable [HasExt (Sheaf (localizationTopology K) AddCommGrpCat.{v})]

-- Proof sketch: unfold `cohomologyOverSheaf`; by definition it is the global cohomology of the
-- inverse-image abelian sheaf on the localized site presenting `Sh(C/K)`.
/-- Lemma 21.13.3 (2): the cohomology `H^p(K, \mathcal F)` is computed by the global cohomology of
the inverse-image abelian sheaf on the localized site `\mathcal C/K`. -/
theorem cohomologyOverSheaf_eq_localizedSite_cohomology
    (F : Sheaf J AddCommGrpCat.{v}) (p : ℕ) :
    cohomologyOverSheaf K F p =
      AddCommGrpCat.of (((localizationInverseImage K).obj F).H p) := sorry

end

end Sheaf
end CategoryTheory

/-! ### Definition_21_13_4 (from Chap21) -/
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe u v w w'

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- Definition 21.13.4: an abelian sheaf `F` on a site is totally acyclic `1` if for every sheaf
of sets `K`, all positive cohomology groups `H^p(K, F)` vanish. Here `H^p(K, F)` is formalized as
the `p`-th `Ext` group from the free abelian sheaf generated by `K` to `F`. -/
class IsTotallyAcyclicOne (F : Sheaf J AddCommGrpCat.{w}) : Prop where
  /-- Every positive cohomology group of `F` over every sheaf of sets vanishes, formalized by the
  corresponding `Ext` group from the free abelian sheaf generated by that sheaf. -/
  isZero_higherCohomologyOverSheaf :
    ∀ (K : Sheaf J (Type w)) (n : ℕ),
      IsZero
        (AddCommGrpCat.of
          (Ext
            ((Sheaf.composeAndSheafify J AddCommGrpCat.free).obj K)
            F
            (n + 1)))

/-- The constant trivial abelian sheaf is totally acyclic `1`. -/
instance isTotallyAcyclicOne_constantTrivial :
    IsTotallyAcyclicOne
      ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of PUnit.{w + 1})) := sorry

end Sheaf
end CategoryTheory

/-! ### Lemma_21_13_5 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}
variable [HasSheafify J (Type (max u v))]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]

/-- The underlying presheaf morphism attached to a morphism of sheaves of sets. -/
abbrev underlyingPresheafHom {K K' : Sheaf J (Type (max u v))} (α : K' ⟶ K) :
    (sheafToPresheaf J (Type (max u v))).obj K' ⟶
      (sheafToPresheaf J (Type (max u v))).obj K :=
  (sheafToPresheaf J (Type (max u v))).map α

/-- Every positive cohomology group of `F` over an object of the site vanishes. -/
def ObjectwiseHigherCohomologyVanishes
    (F : Sheaf J AddCommGrpCat.{max u v}) : Prop :=
  ∀ (U : C) (n : ℕ), IsZero (F.H' (n + 1) U)

/-- The extended Čech complex on degree-zero cohomology is exact for locally surjective morphisms
of sheaves of sets, formalized by vanishing of the positive-degree `E₂^{p,0}` terms of any
associated Čech spectral sequence. -/
def HasExactExtendedCechComplexOnSheafSurjections
    (F : Sheaf J AddCommGrpCat.{max u v}) : Prop :=
  ∀ ⦃K K' : Sheaf J (Type (max u v))⦄ (α : K' ⟶ K)
    (hα : Presheaf.IsLocallySurjective J (underlyingPresheafHom α))
    (S : LocallySurjectiveCechSpectralSequence (underlyingPresheafHom α) F)
    (p : ℕ), 0 < p →
      IsZero ((S.spectralSequence.page 2 (by decide)).X (p, 0))

-- Proof sketch: for the forward implication, apply total acyclicity to the representable sheaves
-- `h_U^#` and to the Čech nerve levels of a locally surjective map of sheaves, then use the
-- spectral sequence from Lemma `21.13.2` to identify the `E₂^{p,0}` terms with the cohomology of
-- the extended Čech complex on `H^0(-, F)`. For the converse, start from a locally surjective
-- resolution of an arbitrary sheaf of sets by coproducts of representables and repeat the source
-- induction on the cohomological degree, using the vanishing on objects and the Čech exactness
-- hypothesis to force all relevant `E₂`-terms to vanish.
/-- Lemma 21.13.5: an abelian sheaf `F` on a site is totally acyclic if and only if all higher
cohomology groups `H^p(U, F)` vanish for every object `U` of the site and, for every surjective
morphism of sheaves of sets, the extended Čech complex on `H^0(-, F)` is exact. The Čech
exactness clause is formalized here by vanishing of the positive-degree `E₂^{p,0}` terms of the
associated Čech spectral sequence. -/
theorem isTotallyAcyclicOne_iff_objectwiseHigherCohomologyVanishes_and_exactExtendedCechComplex
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    IsTotallyAcyclicOne F ↔
      ObjectwiseHigherCohomologyVanishes F ∧
        HasExactExtendedCechComplexOnSheafSurjections F := sorry

end Sheaf
end CategoryTheory
