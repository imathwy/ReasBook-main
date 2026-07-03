import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_18_1 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ObjectProperty

/- Definition 13.18.1 is the cochain-complex definition of an injective resolution: for a cochain
complex `K`, it is a quasi-isomorphism from `K` to a bounded-below cochain complex of injective
objects. The main owner of this file is therefore the source-facing cochain-complex notion
`CochainComplex.InjectiveResolution`. -/

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: bounded-below injective models for cochain complexes;
- sampled owner declarations:
  `CochainComplex.PlusWithTermsIn`,
  `CochainComplex.InjectivePlus`,
  `CochainComplex.plus_iff`,
  `CochainComplex.isKInjective_of_injective`,
  `CochainComplex.ProjectiveResolution`;
- best owner abstraction: the source-facing owner is `CochainComplex.InjectiveResolution`; its
  bounded-below injective datum should be owned by the chapter owner
  `CochainComplex.InjectivePlus 𝒜`, which is the thin source-facing vocabulary layer over the
  generic owner `CochainComplex.PlusWithTermsIn (isInjective 𝒜)`;
- primitive data here: a chosen bounded-below injective complex in the owner
  `CochainComplex.InjectivePlus 𝒜` and a comparison morphism from the original complex;
- derived API here: coercions to the bounded-below / underlying complex, the bounded-below witness,
  termwise injectivity, quasi-isomorphism, and the resulting `IsKInjective` instance.
- `source-facing`: `CochainComplex.InjectiveResolution`;
- `core/canonical`: `CochainComplex.InjectivePlus 𝒜`, viewed through the generic owner
  `CochainComplex.PlusWithTermsIn (isInjective 𝒜)`;
- `bridge/view`: the coercions from `InjectiveResolution K` to the underlying bounded-below and
  raw cochain complexes.

This file is therefore `source-facing`: it bundles a chosen injective resolution of a cochain
complex, but its bounded-below injective data should be owned by the generic bounded-below owner
`CochainComplex.PlusWithTermsIn` rather than by a duplicate local full-subcategory definition.
-/

/-- The bounded-below cochain complexes whose terms are injective objects. -/
abbrev InjectivePlus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  CochainComplex.PlusWithTermsIn (isInjective 𝒜)

namespace PlusWithTermsIn

/-- A bounded-below cochain complex of injective objects is K-injective. -/
instance instIsKInjective (I : PlusWithTermsIn (isInjective 𝒜)) :
    CochainComplex.IsKInjective (I : CochainComplex 𝒜 ℤ) := by
  obtain ⟨a, ha⟩ := I.exists_isStrictlyGE
  let _ : (I : CochainComplex 𝒜 ℤ).IsStrictlyGE a := ha
  let _ : ∀ n : ℤ, Injective ((I : CochainComplex 𝒜 ℤ).X n) := I.term_mem
  exact isKInjective_of_injective (I : CochainComplex 𝒜 ℤ) a

end PlusWithTermsIn

/-- A bounded-below injective resolution of a cochain complex is a quasi-isomorphism from the
given complex to a bounded-below cochain complex of injective objects. -/
structure InjectiveResolution (K : CochainComplex 𝒜 ℤ) where
  /-- The bounded-below injective cochain complex appearing in the resolution. -/
  complex : InjectivePlus 𝒜
  /-- The comparison map from the original complex to the resolving complex. -/
  ι : K ⟶ complex
  /-- The comparison map is a quasi-isomorphism. -/
  quasiIso : QuasiIso ι := by infer_instance

attribute [instance] InjectiveResolution.quasiIso

namespace InjectiveResolution

/-- An injective resolution can be used as its bounded-below injective complex. -/
instance {K : CochainComplex 𝒜 ℤ} :
    CoeOut (InjectiveResolution K) (InjectivePlus 𝒜) where
  coe I := I.complex

/-- An injective resolution can be used as its bounded-below resolving complex. -/
instance {K : CochainComplex 𝒜 ℤ} : CoeOut (InjectiveResolution K) (Plus 𝒜) where
  coe I := I.complex

/-- An injective resolution can be used as its resolving cochain complex. -/
instance {K : CochainComplex 𝒜 ℤ} : CoeOut (InjectiveResolution K) (CochainComplex 𝒜 ℤ) where
  coe I := I.complex

/-- The resolving complex in an injective resolution is bounded below. -/
theorem plus {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    CochainComplex.plus 𝒜 (I : CochainComplex 𝒜 ℤ) := by
  simpa using I.complex.plus

/-- The resolving complex in an injective resolution is zero in all sufficiently negative
degrees. -/
theorem exists_isStrictlyGE {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    ∃ a : ℤ, (I : CochainComplex 𝒜 ℤ).IsStrictlyGE a := by
  simpa using I.complex.exists_isStrictlyGE

/-- Each term of the resolving complex in an injective resolution is injective. -/
theorem injective {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) (n : ℤ) :
    Injective ((I : CochainComplex 𝒜 ℤ).X n) := by
  simpa using I.complex.term_mem n

attribute [instance] InjectiveResolution.injective

-- Proof sketch: unpack the canonical bounded-below owner `CochainComplex.plus 𝒜 I` to obtain a
-- degree bound, then apply `CochainComplex.isKInjective_of_injective`.
/-- The resolving complex of a bounded-below injective resolution is K-injective. -/
instance instIsKInjective {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    IsKInjective (I : CochainComplex 𝒜 ℤ) :=
  PlusWithTermsIn.instIsKInjective I.complex

end InjectiveResolution

end CochainComplex

/-! ### Lemma_13_18_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace CochainComplex.InjectiveResolution

variable {K : CochainComplex C ℤ}

/- Domain-style sampling:
- primary domain: bounded-below injective resolutions of cochain complexes and the induced
  eventual vanishing of low-degree homology;
- sampled owner declarations:
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.InjectiveResolution.exists_isStrictlyGE`,
  `CochainComplex.isZero_of_isGE`,
  `isoOfQuasiIsoAt`,
  `exists_quasiIso_to_truncGE_of_eventually_isZero_homology`;
- best owner abstraction: `CochainComplex.InjectiveResolution` already owns the primitive bounded-
  below resolving complex, while eventual vanishing and truncation replacement are derived API;
- primitive data here: the chosen injective resolution `I` together with its bounded-below witness
  from `I.exists_isStrictlyGE`;
- derived API here: vanishing of `K.homology n` for `n ≪ 0`, and the lower-truncation
  replacement recalled below.

Source/core/bridge triage:
- `source-facing`: the source statement that a bounded-below injective resolution forces eventual
  vanishing of low-degree homology;
- `core/canonical`: `InjectiveResolution.exists_isStrictlyGE`, `ExactAt`, and quasi-isomorphism
  invariance of homology;
- `bridge/view`: the truncation existence theorem already provided by Lemma 13.11.5.
-/
-- Proof sketch: let `a` be a lower bound for the bounded-below resolving complex `I.complex.obj`.
-- Since `I.complex.obj` is strictly concentrated in degrees `≥ a`, its homology vanishes in every
-- degree `< a`. The quasi-isomorphism `I.ι` identifies the homology of `K` with that of
-- `I.complex.obj`, so `H^n(K) = 0` for all `n < a`.
/-- Lemma 13.18.2 (1): if `I` is a bounded-below injective resolution of `K`, then the homology
objects `H^n(K)` vanish for all sufficiently negative degrees. -/
theorem eventually_isZero_homology (I : InjectiveResolution K) :
    ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n) := by
  obtain ⟨a, hI⟩ := I.exists_isStrictlyGE
  letI := hI
  exact ⟨a, fun n hn ↦ by
    simpa using IsZero.of_iso
      ((I : CochainComplex C ℤ).isZero_of_isGE a n hn)
      (isoOfQuasiIsoAt I.ι n)⟩

end CochainComplex.InjectiveResolution

/- Lemma 13.18.2 (2): this is exactly the bounded-below truncation replacement already proved as
Lemma 13.11.5 (1). -/
recall exists_quasiIso_to_truncGE_of_eventually_isZero_homology

/-! ### Lemma_13_18_3 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CochainComplex
open scoped ZeroObject

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
variable {K : CochainComplex 𝒜 ℤ}

local instance isInjective_containsZero : (isInjective 𝒜).ContainsZero where
  exists_zero := ⟨0, isZero_zero 𝒜, inferInstance⟩

local instance isInjective_hasMonoEmbedding : HasMonoEmbedding (isInjective 𝒜) where
  exists_mono X := ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩

/- Domain-style sampling:
- primary domain: bounded-below injective resolutions of cochain complexes in an abelian category
  with enough injectives;
- sampled owner declarations:
  `CategoryTheory.InjectiveResolution.of`,
  `CategoryTheory.HasInjectiveResolutions`,
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.PlusWithTermsIn`,
  `IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn`;
- best owner abstraction: `CochainComplex.InjectiveResolution` is the source-facing owner for a
  chosen injective resolution of a cochain complex, while the bounded-below termwise-monomorphic
  enhancement belongs to the Chapter `13.15` owner
  `IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn`, whose target packages canonically through
  `CochainComplex.PlusWithTermsIn`;
- primitive data: a resolving cochain complex, the comparison morphism from `K`, and the
  bounded-below/injective/quasi-isomorphism data already owned by
  `CochainComplex.InjectiveResolution`;
- derived API: eventual homology vanishing, existence under enough injectives, and the extra
  termwise-monomorphic strengthening in part `(3)`.

Source/core/bridge triage:
- `source-facing`: the three existence statements below for injective resolutions of cochain
  complexes;
- `core/canonical`: the mathlib instance `HasInjectiveResolutions` under enough injectives, the
  project owner `CochainComplex.InjectiveResolution`, the bounded-below owner
  `CochainComplex.PlusWithTermsIn`, and the chapter owner
  `IsTermwiseMonoStrictlyGEQuasiIsoWithTermsIn`;
- `bridge/view`: the packaging of a Chapter `13.15` replacement into a
  `CochainComplex.InjectiveResolution`.
-/

/- Lemma 13.18.3 (1): in an abelian category with enough injectives, the canonical owner
`HasInjectiveResolutions 𝒜` is already provided by mathlib. -/
recall HasInjectiveResolutions

-- Proof sketch: choose a bound below which the homology of `K` vanishes, apply the bounded-below
-- replacement from Lemma 13.18.2, then use Lemma 13.15.5 with the object property of injective
-- objects and repackage the result as a bounded-below injective resolution.
/-- Lemma 13.18.3 (2): if a cochain complex has vanishing homology in all sufficiently negative
degrees, then it admits a bounded-below injective resolution. -/
theorem nonempty_injectiveResolution_of_eventually_isZero_homology
    (hK : ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.homology n)) :
    Nonempty (CochainComplex.InjectiveResolution K) := by
  obtain ⟨a, hK⟩ := hK
  obtain ⟨I, α, h⟩ :=
    exists_quasiIso_with_terms_in_of_isZero_homology_below (isInjective 𝒜) a K hK
  exact ⟨{
    complex := h.toPlusWithTermsIn,
    ι := α,
    quasiIso := h.quasiIso
  }⟩

-- Proof sketch: apply Lemma 13.15.5 to the bounded-below complex `K` with the object property of
-- injective objects. The resulting quasi-isomorphism is termwise monomorphic, its target remains
-- strictly concentrated in degrees `≥ a`, and its terms are injective.
/-- Lemma 13.18.3 (3): if `K` is zero in degrees below `a`, then `K` admits an injective
resolution whose target is also zero below `a` and whose comparison morphism is termwise
monomorphic. -/
theorem exists_injectiveResolution_strictlyGE_with_termwise_mono
    (a : ℤ) (hK : K.IsStrictlyGE a) :
    ∃ I : CochainComplex.InjectiveResolution K,
      ((I : CochainComplex 𝒜 ℤ).IsStrictlyGE a) ∧ ∀ n : ℤ, Mono (I.ι.f n) := by
  obtain ⟨I, α, h⟩ :=
    exists_termwiseMono_quasiIso_with_terms_in_of_isStrictlyGE (isInjective 𝒜) a K hK
  exact ⟨{ complex := h.toPlusWithTermsIn, ι := α, quasiIso := h.quasiIso },
    h.strictlyGE, h.term_mono⟩

end

/-! ### Lemma_13_18_4 (from Chap13) -/
open CategoryTheory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 13.18.4:
- primary domain: bounded-below injective cochain complexes and null-homotopies from acyclic
  complexes;
- sampled owner declarations:
  `CochainComplex.IsKInjective.nonempty_homotopy_zero`,
  `CochainComplex.IsKInjective`,
  `CochainComplex.InjectivePlus`,
  `PlusWithTermsIn.instIsKInjective`;
- best owner abstraction: `InjectivePlus 𝒜`, the chapter owner for bounded-below cochain
  complexes with injective terms; the null-homotopy conclusion is derived by upgrading this
  source-facing owner to the canonical core owner `CochainComplex.IsKInjective`;
- primitive vs. derived API:
  the primitive data is the acyclic source complex `K`, the bounded-below injective target
  `I : InjectivePlus 𝒜`, and the morphism `α : K ⟶ I`;
  the `IsKInjective` structure on the target and the null-homotopy conclusion are derived API and
  should be read from the canonical owner theorem rather than from repeated bounded-below and
  termwise-injective hypotheses.

Source/core/bridge triage:
- `source-facing`: the statement that any map from an acyclic complex to a bounded-below
  injective complex is homotopic to zero;
- `core/canonical`: `IsKInjective` and `IsKInjective.nonempty_homotopy_zero`;
- `bridge/view`: `PlusWithTermsIn.instIsKInjective` in `Definition 13.18.1` upgrades the
  bounded-below injective owner to the canonical `IsKInjective` owner used by the homotopy
  theorem.
-/

variable {K : CochainComplex 𝒜 ℤ}

-- Proof sketch: the bounded-below injective owner `InjectivePlus 𝒜` carries a canonical
-- `IsKInjective` instance, so the statement is exactly the owner theorem
-- `CochainComplex.IsKInjective.nonempty_homotopy_zero`.
/-- Lemma 13.18.4: if `K^•` is acyclic and `I^•` is a bounded-below cochain complex whose terms
are injective objects, then every morphism `K^• ⟶ I^•` is homotopic to zero. -/
lemma homotopic_to_zero_of_acyclic_to_boundedBelow_injective
    (I : InjectivePlus 𝒜) (α : K ⟶ I) (hK : K.Acyclic) :
    Nonempty (Homotopy α 0) :=
  IsKInjective.nonempty_homotopy_zero α hK

end CochainComplex

/-! ### Remark_13_18_5 (from Chap13) -/
open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe v u

namespace CochainComplex

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: morphisms in the homotopy category into bounded-below injective cochain
  complexes and their comparison with the derived category;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `CochainComplex.PlusWithTermsIn.instIsKInjective`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `CochainComplex.isKInjective_of_injective`;
- best owner abstraction: the bounded-below injective target is canonically owned by
  `CochainComplex.InjectivePlus 𝒜`; K-injectivity and the comparison map to the derived category
  are derived API from that owner, so the remark should take the owner directly rather than
  repeating separate bounded-below and termwise-injective hypotheses;
- primitive data: a quasi-isomorphism `α : K ⟶ L` and a bounded-below injective target
  `I : InjectivePlus 𝒜`;
- derived API: bijectivity of precomposition by `α` on morphisms into `I` in the homotopy
  category.

Source/core/bridge triage:
- `source-facing`: the textbook bijectivity statement below;
- `core/canonical`: `CochainComplex.IsKInjective.Qh_map_bijective`;
- `bridge/view`: the canonical `IsKInjective` instance on `InjectivePlus 𝒜`.
-/

-- Proof sketch: bounded-below complexes of injectives are K-injective by
-- `CochainComplex.PlusWithTermsIn.instIsKInjective`. The owner theorem
-- `CochainComplex.IsKInjective.Qh_map_bijective` identifies morphisms into `I^•` in the homotopy
-- category with morphisms into `I^•` in the derived category. Since the quasi-isomorphism `α`
-- becomes an isomorphism in the derived category, `Iso.homCongr` gives the resulting
-- precomposition equivalence there, and transport across the two `Qh.map` bijections yields the
-- claimed bijection in `K(\mathcal A)`.
/-- Remark 13.18.5: if `α : K^• ⟶ L^•` is a quasi-isomorphism and `I^•` is a bounded-below
cochain complex of injective objects, then precomposition with `α` induces a bijection
`Hom_{K(\mathcal A)}(L^•, I^•) ≃ Hom_{K(\mathcal A)}(K^•, I^•)`. -/
theorem homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (I : InjectivePlus 𝒜) :
    Function.Bijective
      (fun g : (quotient 𝒜 (up ℤ)).obj L ⟶ (quotient 𝒜 (up ℤ)).obj I ↦
        (quotient 𝒜 (up ℤ)).map α ≫ g) := by
  let Q := quotient 𝒜 (up ℤ)
  letI : (I : CochainComplex 𝒜 ℤ).IsKInjective := inferInstance
  have hα : IsIso (Qh.map (Q.map α)) := by
    change IsIso ((Q ⋙ Qh).map α)
    exact ((NatIso.isIso_map_iff (quotientCompQhIso 𝒜) α)).2
      ((isIso_Q_map_iff_quasiIso 𝒜 α).2 inferInstance)
  let eα : Qh.obj (Q.obj K) ≅ Qh.obj (Q.obj L) := asIso (Qh.map (Q.map α))
  have hpreD :
      Function.Bijective
        (fun g : Qh.obj (Q.obj L) ⟶ Qh.obj (Q.obj I) ↦ Qh.map (Q.map α) ≫ g) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      exact (eα.symm.homCongr (Iso.refl _)).injective (by simpa [eα] using h)
    · intro g
      obtain ⟨g', hg'⟩ := (eα.symm.homCongr (Iso.refl _)).surjective g
      refine ⟨g', ?_⟩
      simpa [eα] using hg'
  let hL := IsKInjective.Qh_map_bijective (Q.obj L) I
  let hK := IsKInjective.Qh_map_bijective (Q.obj K) I
  have hcomp :
      ((Qh.map : (Q.obj K ⟶ Q.obj I) → (Qh.obj (Q.obj K) ⟶ Qh.obj (Q.obj I))) ∘
        fun g : Q.obj L ⟶ Q.obj I ↦ Q.map α ≫ g) =
      (fun g : Qh.obj (Q.obj L) ⟶ Qh.obj (Q.obj I) ↦ Qh.map (Q.map α) ≫ g) ∘
        (Qh.map : (Q.obj L ⟶ Q.obj I) → (Qh.obj (Q.obj L) ⟶ Qh.obj (Q.obj I))) := by
    funext g
    simp
  have hbijcomp :
      Function.Bijective
        ((Qh.map : (Q.obj K ⟶ Q.obj I) → (Qh.obj (Q.obj K) ⟶ Qh.obj (Q.obj I))) ∘
          fun g : Q.obj L ⟶ Q.obj I ↦ Q.map α ≫ g) := by
    rw [hcomp]
    exact hpreD.comp hL
  exact (Function.Bijective.of_comp_iff' hK _).mp hbijcomp

end CochainComplex

/-! ### Lemma_13_18_6 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex
open HomComplex
open scoped ZeroObject

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: lifting morphisms of cochain complexes into bounded-below injective complexes,
  viewed through the homotopy and derived categories, and strictified via the canonical cochain
  lifting obstruction theory;
- sampled owner declarations:
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`,
  `CochainComplex.Lifting.hasLift`,
  `cokernel_acyclic_of_termwiseMono_quasiIso`;
- best owner abstraction: the chapter bridge theorem
  `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`, whose core owner is
  the K-injective comparison theorem `CochainComplex.IsKInjective.Qh_map_bijective`; for the
  strict lifting statement, the owner abstraction is the canonical obstruction-theoretic lifting
  engine `CochainComplex.Lifting.hasLift`;
- primitive data: a quasi-isomorphism `α : K ⟶ L`, a map `γ : K ⟶ I`, and the bounded-below
  injective structure on `I`;
- derived API: existence of a lift up to homotopy, and the stricter source-facing exact lift when
  `α` is termwise monomorphic.

Source/core/bridge triage:
- `source-facing`: the two lifting statements in this file;
- `core/canonical`: `CochainComplex.IsKInjective.Qh_map_bijective` for part (1), and
  `CochainComplex.Lifting.hasLift` for part (2);
- `bridge/view`: the chapter theorem
  `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`, from which the
  homotopy-level existence result is derived directly, together with the acyclic obstruction
  calculation on `cokernel α` for the strict lift.
-/

-- Proof sketch: pass to the homotopy category and apply the owner theorem
-- `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective` to the class of
-- `γ`. Surjectivity gives a class of maps `L^• ⟶ I^•` whose precomposition with `α` equals the
-- class of `γ`, and equality in the homotopy category is exactly homotopy.
/-- Lemma 13.18.6 (1): if `α : K^• ⟶ L^•` is a quasi-isomorphism and `I^•` is a bounded-below
cochain complex of injective objects, then every map `γ : K^• ⟶ I^•` extends along `α` to a map
`β : L^• ⟶ I^•` for which `β ∘ α` and `γ` are homotopic. -/
theorem exists_homotopy_lift_to_boundedBelow_injective
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α]
    (I : InjectivePlus 𝒜) (γ : K ⟶ I) :
    ∃ β : L ⟶ I, Nonempty (Homotopy (α ≫ β) γ) := by
  let Q := HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)
  let hα := homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective α I
  obtain ⟨β, hβ⟩ := hα.surjective (Q.map γ)
  obtain ⟨β, rfl⟩ := Q.map_surjective β
  refine ⟨β, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  simpa [Functor.map_comp] using hβ

-- Proof sketch: apply the canonical cochain lifting engine to the square with right edge
-- `I^• ⟶ 0`. Degreewise liftings exist because each `α.f n` is monic and `I.X n` is injective.
-- The obstruction cocycle lies in `Cocycle (cokernel α) I 1`; the cokernel complex is acyclic by
-- 13.18.6.1, while `I⟦1⟧` is K-injective, so the corresponding map `cokernel α ⟶ I⟦1⟧` is
-- null-homotopic. Converting that null-homotopy back to a degree-zero cochain shows that the
-- obstruction is a coboundary, and `CochainComplex.Lifting.hasLift` then produces the desired
-- strict lift.
/-- Lemma 13.18.6 (2): if, in addition, each component `α^n` is a monomorphism, then the lift
`β : L^• ⟶ I^•` can be chosen so that `β ∘ α = γ` exactly. -/
theorem exists_strict_lift_to_boundedBelow_injective_of_termwiseMono
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α]
    (I : InjectivePlus 𝒜) (γ : K ⟶ I)
    (hmono : ∀ n : ℤ, Mono (α.f n)) :
    ∃ β : L ⟶ I, α ≫ β = γ := by
  let J : CochainComplex 𝒜 ℤ := I
  let sq : CommSq γ α (0 : J ⟶ 0) (0 : L ⟶ 0) := CommSq.mk (by simp)
  let hsq : ∀ n : ℤ, (sq.map (eval 𝒜 (ComplexShape.up ℤ) n)).LiftStruct := by
    intro n
    let _ : Injective (J.X n) := I.term_mem n
    refine
      { l := (Injective.factorThru (γ.f n) (α.f n) : L.X n ⟶ J.X n)
        fac_left := ?_
        fac_right := ?_ }
    · exact Injective.comp_factorThru (γ.f n) (α.f n)
    · exact comp_zero
  have hQ : IsColimit (CokernelCofork.ofπ (cokernel.π α) (cokernel.condition α)) :=
    CokernelCofork.IsColimit.ofπ' (cokernel.π α) (cokernel.condition α)
      (fun k hk ↦ ⟨cokernel.desc α k hk, by exact cokernel.π_desc α k hk⟩)
  have hK :
      IsLimit
        ((KernelFork.ofι (𝟙 J) (by simp)) : KernelFork (0 : J ⟶ 0)) :=
    KernelFork.IsLimit.ofId (0 : J ⟶ 0) rfl
  let obstruction : Cocycle (cokernel α) J 1 :=
    CochainComplex.Lifting.cocycle₁ sq hsq hQ hK
  have hac : (cokernel α).Acyclic :=
    cokernel_acyclic_of_termwiseMono_quasiIso α hmono
  let hnull :
      Homotopy
        (Cocycle.equivHomShift.symm obstruction)
        0 :=
    IsKInjective.homotopyZero (Cocycle.equivHomShift.symm obstruction) hac
  obtain ⟨cochainShift, hcochainShift⟩ :=
    Cochain.equivHomotopy (Cocycle.equivHomShift.symm obstruction) 0 hnull
  have hcochainShift :
      Cochain.ofHom (Cocycle.equivHomShift.symm obstruction) =
        δ (-1) 0 cochainShift := by
    simpa using hcochainShift
  have hobstruction :
      (Cochain.ofHom (Cocycle.equivHomShift.symm obstruction)).rightUnshift 1 (by simp) =
        obstruction.1 := by
    change
      (Cocycle.equivHomShift (Cocycle.equivHomShift.symm obstruction)).1 = obstruction.1
    exact
      congrArg
        (fun z : Cocycle (cokernel α) J 1 ↦ z.1)
        (Cocycle.equivHomShift.apply_symm_apply obstruction)
  let cochain :
      Cochain (cokernel α) J 0 :=
    (-cochainShift).rightUnshift 0 (by simp)
  have hδ : δ 0 1 cochain = obstruction.1 := by
    dsimp [cochain]
    rw [Cochain.δ_rightUnshift (-cochainShift) 0 (by simp) 1 0 (by simp)]
    simp only [Int.negOnePow_one, Int.reduceNeg, δ_neg, Cochain.rightUnshift_neg, smul_neg,
      Units.neg_smul, one_smul, neg_neg]
    rw [← hcochainShift]
    exact hobstruction
  letI : sq.HasLift := CochainComplex.Lifting.hasLift sq hsq hQ hK cochain hδ
  exact ⟨sq.lift, sq.fac_left⟩

end CochainComplex

/-! ### Lemma_13_18_7 (from Chap13) -/
open CategoryTheory ComplexShape HomotopyCategory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K L : CochainComplex 𝒜 ℤ}

/- Domain-style sampling:
- primary domain: homotopy-category uniqueness of lifts along quasi-isomorphisms into
  bounded-below injective cochain complexes;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `CochainComplex.PlusWithTermsIn.plus`,
  `CochainComplex.PlusWithTermsIn.term_mem`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`,
  `HomotopyCategory.eq_of_homotopy`,
  `HomotopyCategory.homotopyOfEq`;
- best owner abstraction: `CochainComplex.InjectivePlus`, the chapter owner for bounded-below
  cochain complexes with injective terms; the bridge theorem
  `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective` is derived API whose
  canonical core owner is `CochainComplex.IsKInjective.Qh_map_bijective`;
- primitive data: a quasi-isomorphism `α : K ⟶ L`, a bounded-below injective target
  `I : InjectivePlus 𝒜`, and maps `γ : K ⟶ I`, `β₁, β₂ : L ⟶ I`;
- derived API: uniqueness of the lift up to homotopy.

Source/core/bridge triage:
- `source-facing`: the uniqueness-up-to-homotopy statement below;
- `core/canonical`: `CochainComplex.InjectivePlus` and
  `CochainComplex.IsKInjective.Qh_map_bijective`;
- `bridge/view`: the chapter bijectivity theorem on homotopy-category precomposition, instantiated
  from the `InjectivePlus` owner.
-/

-- Proof sketch: pass to the homotopy category. The hypotheses `α ≫ β₁ ∼ γ` and `α ≫ β₂ ∼ γ`
-- say that precomposition by `α` sends the classes of `β₁` and `β₂` to the same morphism
-- `K^• ⟶ I^•`. By Remark 13.18.5, instantiated with the bounded-below injective owner `I`,
-- precomposition with the quasi-isomorphism `α` is bijective on maps into `I^•`, so those
-- classes are equal; then
-- `HomotopyCategory.homotopyOfEq` yields a homotopy `β₁ ∼ β₂`.
/-- Lemma 13.18.7: if `α : K^• ⟶ L^•` is a quasi-isomorphism, `I^•` is bounded below with
injective terms, and two morphisms `β₁, β₂ : L^• ⟶ I^•` both make the triangle with
`γ : K^• ⟶ I^•` commute up to homotopy, then `β₁` and `β₂` are homotopic. -/
theorem homotopic_lifts_of_quasiIso_to_boundedBelow_injective
    (α : K ⟶ L) [QuasiIso α] (I : InjectivePlus 𝒜) (γ : K ⟶ I) (β₁ β₂ : L ⟶ I)
    (hβ₁ : Nonempty (Homotopy (α ≫ β₁) γ))
    (hβ₂ : Nonempty (Homotopy (α ≫ β₂) γ)) :
    Nonempty (Homotopy β₁ β₂) := by
  let Q := HomotopyCategory.quotient 𝒜 (up ℤ)
  obtain ⟨hβ₁⟩ := hβ₁
  obtain ⟨hβ₂⟩ := hβ₂
  refine ⟨homotopyOfEq _ _ ?_⟩
  apply (homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective α I).injective
  simpa [Q, Functor.map_comp] using
    (eq_of_homotopy _ _ hβ₁).trans (eq_of_homotopy _ _ hβ₂).symm

end CochainComplex

/-! ### Lemma_13_18_8 (from Chap13) -/
open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

/- Domain-style sampling:
- primary domain: morphisms into bounded-below injective cochain complexes in the homotopy and
  derived categories;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `PlusWithTermsIn.instIsKInjective`,
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `CochainComplex.isKInjective_of_injective`;
- best owner abstraction: `CochainComplex.InjectivePlus`, the chapter owner for bounded-below
  cochain complexes with injective terms; K-injectivity and the `Qh.map` bijection are derived API
  from that owner;
- primitive data: the source complex `L` and the bounded-below injective target `I :
  InjectivePlus 𝒜`;
- derived API: the canonical `IsKInjective` instance on `I` and the induced bijection on morphisms
  from `L` in the homotopy category to the derived category.

Source/core/bridge triage:
- `source-facing`: the textbook statement for bounded-below injective targets;
- `core/canonical`: `CochainComplex.IsKInjective.Qh_map_bijective`;
- `bridge/view`: `PlusWithTermsIn.instIsKInjective`, which upgrades the bounded-below injective owner
  to the canonical K-injective owner.
-/

-- Proof sketch: the chapter owner `InjectivePlus 𝒜` carries the canonical `IsKInjective`
-- instance from Definition `13.18.1`, so the statement is exactly
-- `CochainComplex.IsKInjective.Qh_map_bijective` specialized to the homotopy-category image of
-- `L` and the owner object `I`.
/-- Lemma 13.18.8: if `I^•` is a bounded-below cochain complex of injective objects in an abelian
category `𝒜`, then for every cochain complex `L^•` the canonical map from morphisms
`L^• ⟶ I^•` in the homotopy category `K(𝒜)` to morphisms `L^• ⟶ I^•` in the derived category
`D(𝒜)` is bijective. -/
theorem homotopyCategory_to_derived_bijective_of_boundedBelow_injective
    (L : CochainComplex 𝒜 ℤ) (I : InjectivePlus 𝒜) :
    Function.Bijective
      (DerivedCategory.Qh.map :
        ((KQ).obj L ⟶ (KQ).obj I) → _) := by
  simpa using IsKInjective.Qh_map_bijective ((KQ).obj L) I

end CochainComplex

/-! ### Lemma_13_18_9 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: short exact sequences of bounded-below cochain complexes and compatible
  bounded-below injective resolutions;
- sampled owner declarations:
  `CategoryTheory.ShortComplex.Hom`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `CochainComplex.PlusWithTermsIn.ι`,
  `CochainComplex.plus`,
  `CochainComplex.InjectivePlus`,
  `CochainComplex.InjectiveResolution`;
- best owner abstraction: the resolving row should be owned by
  `ShortComplex (InjectivePlus 𝒜)`, its comparison with the given short exact sequence by a
  single `ShortComplex.Hom`, and short exactness by `ShortComplex.ShortExact`;
- primitive data here: the short exact resolving row in `InjectivePlus 𝒜`, the morphism from `S`
  to its underlying short complex, and the quasi-isomorphism witnesses on the three vertical
  components;
- derived API here: the source-facing existence theorems below, with any columnwise
  `InjectiveResolution` view recovered directly from the canonical row and comparison morphism.

Source/core/bridge triage:
- `source-facing`: the injective-resolution diagram data above a bounded-below short exact
  sequence, together with its existence theorems;
- `core/canonical`: `ShortComplex (InjectivePlus 𝒜)`, `ShortComplex.Hom`,
  `ShortComplex.ShortExact`, `CochainComplex.InjectiveResolution`, and the generic
  extension-closure interface `ObjectProperty.prop_X₂_of_shortExact`;
- `bridge/view`: the `strictlyGE_zero` existence specializations below.
-/

local notation "injPlusι" => PlusWithTermsIn.ι (isInjective 𝒜)

section

variable [EnoughInjectives 𝒜]

-- Proof sketch: choose an injective resolution of the left complex, push out the short exact
-- sequence along it to reduce to the termwise split case, resolve the right complex, lift the
-- connecting morphism to the chosen injective resolutions by Lemma 13.18.6, and use the resulting
-- upper-triangular differential on the direct-sum complex to build the middle injective
-- resolution and the lower short exact row.
/-- Lemma 13.18.9: if `0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` is a short exact sequence of cochain complexes
whose outer terms are bounded below, then it extends to a commutative diagram whose vertical maps
are injective resolutions and whose lower row is again a short exact sequence of complexes. The
middle term is bounded below because bounded-below cochain complexes are closed under extensions.
-/
theorem exists_injectiveResolutionDiagram_of_shortExact
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.plus 𝒜 S.X₁) (hC : CochainComplex.plus 𝒜 S.X₃) :
    ∃ row : ShortComplex (InjectivePlus 𝒜), ∃ hom : S ⟶ row.map injPlusι,
      (row.map injPlusι).ShortExact ∧
        QuasiIso hom.τ₁ ∧ QuasiIso hom.τ₂ ∧ QuasiIso hom.τ₃ := sorry

-- Proof sketch: run the construction of `exists_injectiveResolutionDiagram_of_shortExact` starting
-- from the prescribed injective resolution of the left complex, then perform the pushout
-- reduction and the lifted-connecting-morphism construction relative to that fixed choice.
/-- Given a chosen injective resolution of the left complex, the diagram can be built with that
resolution as its left column, provided the outer terms of the short exact row are bounded below.
The middle term is then bounded below by short exactness. -/
theorem exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.plus 𝒜 S.X₁) (hC : CochainComplex.plus 𝒜 S.X₃)
    (I : InjectiveResolution S.X₁) :
    ∃ (J K : InjectivePlus 𝒜) (f : I.complex ⟶ J) (g : J ⟶ K) (hfg : f ≫ g = 0)
      (φ : S ⟶ (ShortComplex.mk f g hfg).map injPlusι),
        φ.τ₁ = I.ι ∧
          ((ShortComplex.mk f g hfg).map injPlusι).ShortExact ∧
          QuasiIso φ.τ₂ ∧ QuasiIso φ.τ₃ := sorry

-- Proof sketch: choose the left and right injective resolutions using Lemma 13.18.3 with lower
-- bound `0`, so their targets are zero in negative degrees, and then carry out the same
-- upper-triangular construction of the middle resolution; the direct-sum model is also zero in
-- negative degrees.
/-- If the outer terms of the original short exact sequence are zero in negative degrees, then the
middle term is also zero in negative degrees, and the injective-resolution diagram can be chosen
so that all three lower resolving complexes are zero in negative degrees as well. -/
theorem exists_injectiveResolutionDiagram_of_shortExact_strictlyGE_zero
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : S.X₁.IsStrictlyGE 0) (hC : S.X₃.IsStrictlyGE 0) :
    ∃ row : ShortComplex (InjectivePlus 𝒜), ∃ hom : S ⟶ row.map injPlusι,
      (row.map injPlusι).ShortExact ∧
        QuasiIso hom.τ₁ ∧
        QuasiIso hom.τ₂ ∧
        QuasiIso hom.τ₃ ∧
        (row.X₁ : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 ∧
        (row.X₂ : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 ∧
        (row.X₃ : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 := sorry

-- Proof sketch: combine the prescribed-left-resolution construction with the bounded-below choice
-- from the previous theorem, using the given lower bound on the chosen left resolution to keep
-- the whole lower row zero in negative degrees.
/-- If the outer terms of the original sequence are zero in negative degrees and the chosen left
injective resolution is also zero in negative degrees, then the middle term is automatically zero
in negative degrees, and the diagram can be built with that prescribed left comparison map and
with the remaining resolving complexes zero in negative degrees. -/
theorem exists_injectiveResolutionDiagram_of_shortExact_with_leftResolution_strictlyGE_zero
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) (hI : (I : CochainComplex 𝒜 ℤ).IsStrictlyGE 0)
    (hA : S.X₁.IsStrictlyGE 0) (hC : S.X₃.IsStrictlyGE 0) :
    ∃ (J K : InjectivePlus 𝒜) (f : I.complex ⟶ J) (g : J ⟶ K) (hfg : f ≫ g = 0)
      (φ : S ⟶ (ShortComplex.mk f g hfg).map injPlusι),
        φ.τ₁ = I.ι ∧
          ((ShortComplex.mk f g hfg).map injPlusι).ShortExact ∧
          QuasiIso φ.τ₂ ∧
          QuasiIso φ.τ₃ ∧
          (J : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 ∧
          (K : CochainComplex 𝒜 ℤ).IsStrictlyGE 0 := sorry

end

end CochainComplex
