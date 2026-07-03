import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_19_1 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ObjectProperty

/- Definition 13.19.1: for an object `A` of an abelian category, the canonical mathlib structure
`CategoryTheory.ProjectiveResolution A` encodes a projective resolution of `A`; its associated
cochain complex is `R.cochainComplex`, and the map to `A[0]` is `R.π'`. -/
recall CategoryTheory.ProjectiveResolution

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: bounded-above projective models for cochain complexes;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.MinusWithTermsIn`,
  `CochainComplex.MinusWithTermsIn.term_mem`,
  `CochainComplex.MinusWithTermsIn.exists_isStrictlyLE`,
  `CochainComplex.isKProjective_of_projective`,
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.InjectivePlus`;
- best owner abstraction: the source-facing thin vocabulary layer
  `CochainComplex.ProjectiveMinus 𝒜` over the generic owner
  `CochainComplex.MinusWithTermsIn (isProjective 𝒜)` for bounded-above complexes whose terms are
  projective;
- primitive data here: a chosen bounded-above projective complex in that owner and a comparison
  morphism to the target complex;
- derived API here: coercions from a chosen projective resolution to the canonical owner / bounded-
  above / underlying complex, the bounded-above witness, termwise projectivity, quasi-isomorphism,
  and the resulting `IsKProjective` instance.

This file is therefore `source-facing`: it bundles a chosen projective resolution of a cochain
complex, but its bounded-above termwise-projective data should be owned by the chapter owner
`CochainComplex.ProjectiveMinus 𝒜`, viewed through the generic owner
`CochainComplex.MinusWithTermsIn (isProjective 𝒜)`, rather than by a duplicate local full
subcategory definition.
-/

/-- The bounded-above cochain complexes whose terms are projective objects. -/
abbrev ProjectiveMinus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  CochainComplex.MinusWithTermsIn (isProjective 𝒜)

namespace MinusWithTermsIn

-- Proof sketch: unpack the bounded-above owner `MinusWithTermsIn (isProjective 𝒜)` into the
-- bounded-above witness and termwise projectivity, then apply
-- `CochainComplex.isKProjective_of_projective`.
/-- A bounded-above projective complex is K-projective. -/
instance instIsKProjective (P : ProjectiveMinus 𝒜) :
    IsKProjective (P : CochainComplex 𝒜 ℤ) := by
  obtain ⟨d, hd⟩ := P.exists_isStrictlyLE
  let _ : (P : CochainComplex 𝒜 ℤ).IsStrictlyLE d := hd
  let _ : ∀ n : ℤ, Projective ((P : CochainComplex 𝒜 ℤ).X n) := P.term_mem
  exact isKProjective_of_projective (P : CochainComplex 𝒜 ℤ) d

end MinusWithTermsIn

/-- A bounded-above projective resolution of a cochain complex is a quasi-isomorphism from a
bounded-above cochain complex of projective objects to the given complex. -/
structure ProjectiveResolution (K : CochainComplex 𝒜 ℤ) where
  /-- The bounded-above projective cochain complex appearing in the resolution. -/
  complex : ProjectiveMinus 𝒜
  /-- The comparison map from the resolving complex to the target complex. -/
  π : (complex : CochainComplex 𝒜 ℤ) ⟶ K
  /-- The comparison map is a quasi-isomorphism. -/
  quasiIso : QuasiIso π := by infer_instance

attribute [instance] ProjectiveResolution.quasiIso

namespace IsStrictlyLEQuasiIsoWithTermsIn

variable {a : ℤ} {K Q : CochainComplex 𝒜 ℤ} {π : Q ⟶ K}

/-- A bounded-above quasi-isomorphism from a cochain complex of projective objects canonically
packages as a cochain-complex projective resolution. -/
abbrev toProjectiveResolution
    (hπ : IsStrictlyLEQuasiIsoWithTermsIn (isProjective 𝒜) a K Q π) :
    ProjectiveResolution K where
  complex := hπ.toMinusWithTermsIn
  π := π
  quasiIso := hπ.quasiIso

end IsStrictlyLEQuasiIsoWithTermsIn

namespace ProjectiveResolution

/-- A projective resolution can be used as its bounded-above projective complex. -/
instance {K : CochainComplex 𝒜 ℤ} :
    CoeOut (ProjectiveResolution K) (ProjectiveMinus 𝒜) where
  coe P := P.complex

/-- A projective resolution can be used as its bounded-above resolving complex. -/
instance {K : CochainComplex 𝒜 ℤ} : CoeOut (ProjectiveResolution K) (Minus 𝒜) where
  coe P := P.complex

/-- A projective resolution can be used as its resolving cochain complex. -/
instance {K : CochainComplex 𝒜 ℤ} : CoeOut (ProjectiveResolution K) (CochainComplex 𝒜 ℤ) where
  coe P := P.complex

/-- The resolving complex in a projective resolution is bounded above. -/
theorem minus {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    CochainComplex.minus 𝒜 (P : CochainComplex 𝒜 ℤ) :=
  by
    simpa using P.complex.minus

/-- The resolving complex in a projective resolution is zero in all sufficiently high degrees. -/
theorem exists_isStrictlyLE {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    ∃ d : ℤ, (P : CochainComplex 𝒜 ℤ).IsStrictlyLE d :=
  by
    simpa using P.complex.exists_isStrictlyLE

/-- Each term of the resolving complex in a projective resolution is projective. -/
theorem projective {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) (n : ℤ) :
    Projective ((P : CochainComplex 𝒜 ℤ).X n) :=
  by
    simpa using P.complex.term_mem n

attribute [instance] ProjectiveResolution.projective

-- Proof sketch: the canonical owner `MinusWithTermsIn (isProjective 𝒜)` already packages the
-- bounded-above/projective hypotheses and carries the `IsKProjective` instance.
/-- The resolving complex in a projective resolution is K-projective. -/
instance instIsKProjective {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    IsKProjective (P : CochainComplex 𝒜 ℤ) :=
  MinusWithTermsIn.instIsKProjective P.complex

end ProjectiveResolution

end CochainComplex

/-! ### Lemma_13_19_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open CochainComplex

universe v u

namespace CochainComplex.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ}

/- Domain-style sampling for Lemma 13.19.2:
- primary domain: bounded-above cochain complexes, projective resolutions, and eventual vanishing
  of homology;
- sampled owner declarations:
  `CochainComplex.ProjectiveResolution`,
  `CochainComplex.ProjectiveResolution.exists_isStrictlyLE`,
  `CochainComplex.isZero_of_isLE`,
  `isoOfQuasiIsoAt`,
  `exists_quasiIso_from_truncLE_of_eventually_isZero_homology`;
- best owner abstraction:
  `CochainComplex.ProjectiveResolution K` is the source-faithful owner for the projective side,
  while the bounded-above replacement in part `(2)` is already canonically owned by
  `exists_quasiIso_from_truncLE_of_eventually_isZero_homology`;
- primitive-vs-derived split:
  for part `(1)`, the primitive data are just `P : ProjectiveResolution K`; the bounded-above
  witness and degreewise projectivity are derived from the owner;
  for part `(2)`, the primitive owner data are the canonical truncation object `K.truncLE b` and
  map `K.ιTruncLE b`, while the existential bounded-above replacement is derived;
- source/core/bridge triage:
  `source-facing`: eventual vanishing of `K.homology` for a complex admitting a bounded-above
    projective resolution;
  `core/canonical`: `ProjectiveResolution K`, `K.IsLE b`, and the canonical truncation theorem
    from `Lemma 13.11.5`;
  `bridge/view`: transport of eventual homology vanishing from the bounded-above resolving complex
    via `CochainComplex.isZero_of_isLE` and `isoOfQuasiIsoAt`.
-/

-- Proof sketch: choose a bound `b` with `P.IsStrictlyLE b`, view this as an `IsLE b` instance on
-- the resolving complex, deduce its homology vanishes in degrees `> b` via
-- `CochainComplex.isZero_of_isLE`, and transport that vanishing across the quasi-isomorphism
-- `P.π`.
/-- Lemma 13.19.2 (1): if a cochain complex `K` admits a bounded-above projective resolution,
then the homology objects `H^n(K)` vanish for all sufficiently large `n`. -/
theorem eventually_isZero_homology
    (P : ProjectiveResolution K) :
    ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (K.homology n) := by
  obtain ⟨b, hP⟩ := P.exists_isStrictlyLE
  let _ : (P : CochainComplex C ℤ).IsStrictlyLE b := hP
  exact ⟨b, fun n hn ↦ by
    simpa using IsZero.of_iso
      ((P : CochainComplex C ℤ).isZero_of_isLE b n hn)
      (isoOfQuasiIsoAt P.π n).symm⟩

end CochainComplex.ProjectiveResolution

/- Lemma 13.19.2 (2): if the homology of `K` vanishes in all sufficiently positive degrees, then
the canonical upper truncation map `K.truncLE b ⟶ K` is a quasi-isomorphism for some `b`, so `K`
admits a bounded-above quasi-isomorphic model. This is already the canonical theorem
`exists_quasiIso_from_truncLE_of_eventually_isZero_homology` from `Lemma 13.11.5`. -/
recall exists_quasiIso_from_truncLE_of_eventually_isZero_homology

/-! ### Lemma_13_19_3 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CochainComplex
open scoped ZeroObject

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughProjectives 𝒜]
variable {K : CochainComplex 𝒜 ℤ}

local instance isProjective_containsZero : (isProjective 𝒜).ContainsZero where
  exists_zero := ⟨(0 : 𝒜), Limits.isZero_zero 𝒜, inferInstance⟩

local instance isProjective_hasEpiCover : HasEpiCover (isProjective 𝒜) where
  exists_epi X := ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩

/- Domain-style sampling:
- primary domain: bounded-above projective resolutions of cochain complexes in an abelian category
  with enough projectives;
- sampled owner declarations:
  `CategoryTheory.HasProjectiveResolutions`,
  `CategoryTheory.ProjectiveResolution.of`,
  `CochainComplex.ProjectiveResolution`,
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`;
- best owner abstraction: `CochainComplex.ProjectiveResolution` is the source-facing owner for a
  chosen projective resolution of a cochain complex, while the bounded-above termwise-epimorphic
  enhancement belongs to the Chapter `13.15` owner
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`;
- primitive data: a resolving cochain complex, the comparison morphism to the target complex, and
  the bounded-above/projective/quasi-isomorphism data already owned by
  `CochainComplex.ProjectiveResolution`;
- derived API: eventual homology vanishing, existence under enough projectives, and the extra
  termwise-epimorphic strengthening in part `(3)`.

Source/core/bridge triage:
- `source-facing`: the two existence statements below for projective resolutions of cochain
  complexes;
- `core/canonical`: the mathlib instance `HasProjectiveResolutions` under enough projectives, the
  chapter owner `CochainComplex.ProjectiveResolution`, and the chapter owner
  `IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn`;
- `bridge/view`: the packaging of a Chapter `13.15` replacement into a
  `CochainComplex.ProjectiveResolution`.
-/

/- Lemma 13.19.3 (1): in an abelian category with enough projectives, the canonical owner
`HasProjectiveResolutions 𝒜` is already provided by mathlib. -/
recall HasProjectiveResolutions

-- Proof sketch: apply the canonical bounded-above truncation replacement from Lemma 13.11.5 and
-- then resolve the resulting bounded-above complex degreewise by projectives as in
-- Lemma 13.15.4, packaging the outcome in the chapter owner
-- `CochainComplex.ProjectiveResolution K`.
/-- Lemma 13.19.3 (2): if a cochain complex has vanishing homology in all sufficiently positive
degrees, then it admits a projective resolution. -/
theorem nonempty_projectiveResolution_of_eventually_isZero_homology
    (hK : ∃ a : ℤ, ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    Nonempty (CochainComplex.ProjectiveResolution K) := by
  obtain ⟨a, hK⟩ := hK
  obtain ⟨Q, π, hπ⟩ :=
    exists_quasiIso_with_terms_in_of_isZero_homology_above (isProjective 𝒜) a K hK
  exact ⟨{ complex := hπ.toMinusWithTermsIn, π := π, quasiIso := hπ.quasiIso }⟩

-- Proof sketch: start from the bounded-above complex `K`, construct projective presentations
-- degreewise beginning at the top degree, and splice them inductively so that the resulting
-- comparison morphism is termwise epimorphic; then package the resolving complex and its
-- quasi-isomorphism to `K` as a `ProjectiveResolution K`.
/-- Lemma 13.19.3 (3): if `K` is zero in degrees above `a`, then there exists a projective
resolution whose resolving complex is also zero above `a` and whose comparison morphism is
termwise epimorphic. -/
theorem exists_projectiveResolution_strictlyLE_with_termwise_epi
    (a : ℤ) (hK : K.IsStrictlyLE a) :
    ∃ P : CochainComplex.ProjectiveResolution K,
      (P : CochainComplex 𝒜 ℤ).IsStrictlyLE a ∧ ∀ n : ℤ, Epi (P.π.f n) := by
  obtain ⟨Q, π, hπ⟩ :=
    exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE (isProjective 𝒜) a K hK
  exact ⟨{ complex := hπ.toMinusWithTermsIn, π := π, quasiIso := hπ.quasiIso },
    hπ.strictlyLE, hπ.term_epi⟩

end

/-! ### Lemma_13_19_4 (from Chap13) -/
open CategoryTheory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K : CochainComplex 𝒜 ℤ}

/- Domain-style sampling for Lemma 13.19.4:
- primary domain: null-homotopies from bounded-above projective cochain complexes to acyclic
  cochain complexes;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.MinusWithTermsIn.instIsKProjective`,
  `CochainComplex.IsKProjective`,
  `CochainComplex.IsKProjective.nonempty_homotopy_zero`;
- best owner abstraction: the chapter owner `ProjectiveMinus 𝒜` for the bounded-above projective
  source complex, together with the canonical core owner theorem
  `CochainComplex.IsKProjective.nonempty_homotopy_zero`;
- primitive data: a bounded-above projective source
  `P : ProjectiveMinus 𝒜`, a morphism
  `α : (P : CochainComplex 𝒜 ℤ) ⟶ K`, and an acyclicity proof `hK : K.Acyclic`;
- derived API: the resulting null-homotopy.

Source/core/bridge triage:
- `source-facing`: the textbook bounded-above/projective-to-acyclic null-homotopy statement;
- `core/canonical`: `CochainComplex.IsKProjective.nonempty_homotopy_zero`;
- `bridge/view`: `CochainComplex.MinusWithTermsIn.instIsKProjective`, which upgrades the
  source-facing owner to the canonical K-projective owner.
-/

-- Proof sketch: `P` already carries the canonical `IsKProjective` instance from
-- `Definition 13.19.1`, so the claim is exactly the owner theorem
-- `CochainComplex.IsKProjective.nonempty_homotopy_zero`.
/-- Lemma 13.19.4: if `P^•` is a bounded-above cochain complex of projective objects and `K^•`
is acyclic, then every morphism `P^• ⟶ K^•` is homotopic to zero. -/
theorem homotopic_to_zero_of_boundedAbove_projective_to_acyclic
    (P : ProjectiveMinus 𝒜) (α : (P : CochainComplex 𝒜 ℤ) ⟶ K)
    (hK : K.Acyclic) :
    Nonempty (Homotopy α 0) :=
  IsKProjective.nonempty_homotopy_zero α hK

end CochainComplex

/-! ### Remark_13_19_5 (from Chap13) -/
open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe v u

namespace CochainComplex

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-
Domain-style sampling:
- primary domain: morphisms from bounded-above projective cochain complexes in the homotopy and
  derived categories of an abelian category;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.MinusWithTermsIn.instIsKProjective`,
  `CochainComplex.IsKProjective`,
  `homotopyCategory_to_derived_bijective_of_boundedAbove_projective`,
  `DerivedCategory.isIso_Q_map_iff_quasiIso`,
  `NatIso.isIso_map_iff`;
- best owner abstraction: `ProjectiveMinus 𝒜` is the chapter owner for the bounded-above
  projective source, and its `IsKProjective` instance is derived API feeding the chapter owner
  theorem `homotopyCategory_to_derived_bijective_of_boundedAbove_projective`;
- primitive data: a quasi-isomorphism `α : K ⟶ L` and a source complex `P : ProjectiveMinus 𝒜`;
- derived API: bijectivity of postcomposition by `α` in the homotopy category.

This remark is therefore a `bridge/view`: it should take the source-facing owner
`ProjectiveMinus 𝒜` directly and transport postcomposition bijectivity from the derived category
through the chapter comparison theorem for that owner, rather than rebuilding boundedness and
termwise-projective data locally.
-/

-- Proof sketch: `13.19.8` already identifies morphisms out of `P` in the homotopy category with
-- morphisms out of `P` in the derived category. The quasi-isomorphism `α` becomes an isomorphism
-- in the derived category, where postcomposition is therefore bijective. Transporting that
-- bijection back across the two comparison maps gives the homotopy-category bijection.
/-- Remark 13.19.5: if `α : K^• ⟶ L^•` is a quasi-isomorphism and `P^•` is a bounded-above
cochain complex of projective objects, then postcomposition with `α` induces a bijection
`Hom_{K(\mathcal A)}(P^•, K^•) ≃ Hom_{K(\mathcal A)}(P^•, L^•)`. -/
theorem homotopyCategory_postcomp_bijective_of_quasiIso_from_boundedAbove_projective
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (P : ProjectiveMinus 𝒜) :
    Function.Bijective
      (fun g : (quotient 𝒜 (up ℤ)).obj P ⟶ (quotient 𝒜 (up ℤ)).obj K ↦
        g ≫ (quotient 𝒜 (up ℤ)).map α) := by
  let Q := quotient 𝒜 (up ℤ)
  have hα : IsIso (Qh.map (Q.map α)) := by
    change IsIso ((Q ⋙ Qh).map α)
    exact ((NatIso.isIso_map_iff (quotientCompQhIso 𝒜) α)).2
      ((isIso_Q_map_iff_quasiIso 𝒜 α).2 inferInstance)
  have hpostD :
      Function.Bijective
        (fun g : Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K) ↦ g ≫ Qh.map (Q.map α)) := by
    refine ⟨?_, ?_⟩
    · intro g₁ g₂ h
      exact (cancel_mono (Qh.map (Q.map α))).1 h
    · intro g
      refine ⟨g ≫ inv (Qh.map (Q.map α)), ?_⟩
      simp [Category.assoc]
  have hK := homotopyCategory_to_derived_bijective_of_boundedAbove_projective P K
  have hL := homotopyCategory_to_derived_bijective_of_boundedAbove_projective P L
  have hcomp :
      ((Qh.map : (Q.obj P ⟶ Q.obj L) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L))) ∘
        fun g : Q.obj P ⟶ Q.obj K ↦ g ≫ Q.map α) =
      (fun g : Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K) ↦ g ≫ Qh.map (Q.map α)) ∘
        (Qh.map : (Q.obj P ⟶ Q.obj K) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj K))) := by
    funext g
    simp [Functor.map_comp]
  have hbijcomp :
      Function.Bijective
        (((Qh.map : (Q.obj P ⟶ Q.obj L) → (Qh.obj (Q.obj P) ⟶ Qh.obj (Q.obj L))) ∘
          fun g : Q.obj P ⟶ Q.obj K ↦ g ≫ Q.map α)) := by
    rw [hcomp]
    exact hpostD.comp hK
  exact (Function.Bijective.of_comp_iff' hL _).mp hbijcomp

end CochainComplex

/-! ### Lemma_13_19_6 (from Chap13) -/
open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory HomologicalComplex
open scoped ZeroObject

universe v u

namespace CochainComplex

open HomComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K L : CochainComplex 𝒜 ℤ}

/- Domain-style sampling:
- primary domain: homotopy lifting along quasi-isomorphisms from bounded-above projective
  cochain complexes;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `homotopyCategory_postcomp_bijective_of_quasiIso_from_boundedAbove_projective`,
  `CochainComplex.MinusWithTermsIn.instIsKProjective`,
  `CochainComplex.Lifting.hasLift`;
- best owner abstraction: `ProjectiveMinus 𝒜` is the chapter owner for the bounded-above
  projective source complex; the present lifting statements are bridge/view results derived from
  that owner, the homotopy-category bijectivity theorem, and for the strict statement the
  canonical cochain lifting engine;
- primitive data: a projective-minus source complex `P`, a quasi-isomorphism `α : L ⟶ K`, and a
  map `γ : P ⟶ K`;
- derived API: existence of a lift `β : P ⟶ L` up to homotopy, and the stricter exact lift under
  termwise epimorphy.

Source/core/bridge triage:
- `source-facing`: the two lifting statements below;
- `core/canonical`: `ProjectiveMinus 𝒜` and its induced `IsKProjective` instance;
- `bridge/view`: the factorization results obtained from the owner-level K-projective comparison
  API.
-/

-- Proof sketch: the owner `MinusWithTermsIn (isProjective 𝒜)` already packages the
-- bounded-above/projective hypothesis and carries the canonical `IsKProjective` instance. Remark
-- `13.19.5` then identifies postcomposition with the quasi-isomorphism `α` as a bijection on
-- morphisms out of `P` in the homotopy category. Apply surjectivity to the class of `γ`, and
-- unpack equality in the homotopy category as a homotopy between `β ≫ α` and `γ`.
/-- Lemma 13.19.6: if `α : L^• ⟶ K^•` is a quasi-isomorphism and `P^•` is a bounded-above
cochain complex of projective objects, then every morphism `γ : P^• ⟶ K^•` factors through `α`
up to homotopy. -/
theorem exists_homotopy_factor_through_quasiIso_from_boundedAbove_projective
    (P : ProjectiveMinus 𝒜) (α : L ⟶ K) [QuasiIso α]
    (γ : (P : CochainComplex 𝒜 ℤ) ⟶ K) :
    ∃ β : (P : CochainComplex 𝒜 ℤ) ⟶ L, Nonempty (Homotopy (β ≫ α) γ) := by
  let Q := quotient 𝒜 (up ℤ)
  obtain ⟨β, hβ⟩ :=
    (homotopyCategory_postcomp_bijective_of_quasiIso_from_boundedAbove_projective α P).surjective
      (Q.map γ)
  obtain ⟨β, rfl⟩ := Q.map_surjective β
  exact ⟨β, ⟨homotopyOfEq _ _ (by simpa [Q, Functor.map_comp] using hβ)⟩⟩

theorem kernel_acyclic_of_termwiseEpi_quasiIso
    (α : L ⟶ K) [QuasiIso α] (hα : ∀ n : ℤ, Epi (α.f n)) :
    (kernel α).Acyclic := by
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let S := ShortComplex.kernelSequence α
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance
      (HomologicalComplex.epi_of_epi_f α hα)
    exact ShortComplex.kernelSequence_exact α
  refine ((hS.homology_exact₁ (n - 1) n (by simp)).isZero_X₂ ?_ ?_)
  · rw [← (hS.homology_exact₃ (n - 1) n (by simp)).epi_f_iff]
    have : Epi (homologyMap α (n - 1)) := by infer_instance
    simpa [S] using this
  · rw [← (hS.homology_exact₂ n).mono_g_iff]
    have : Mono (homologyMap α n) := by infer_instance
    simpa [S] using this

-- Proof sketch: start with degreewise projective lifts of the components `γ.f n` across the
-- epimorphisms `α.f n`, producing a commutative square against the zero map. The failure of these
-- degreewise lifts to define a chain map is measured by the canonical obstruction cocycle for
-- `CochainComplex.Lifting`; since the kernel complex of a termwise-epimorphic quasi-isomorphism is
-- acyclic, the bounded-above projective owner `P` kills that obstruction, and
-- `CochainComplex.Lifting.hasLift` strictifies the homotopy lift to an exact factorization.
/-- If the quasi-isomorphism `α` is termwise epimorphic, the factorization of a map from a
bounded-above projective complex can be chosen to commute strictly. -/
theorem exists_strict_factor_through_termwiseEpi_quasiIso_from_boundedAbove_projective
    (P : ProjectiveMinus 𝒜) (α : L ⟶ K) [QuasiIso α]
    (γ : (P : CochainComplex 𝒜 ℤ) ⟶ K)
    (hα : ∀ n : ℤ, Epi (α.f n)) :
    ∃ β : (P : CochainComplex 𝒜 ℤ) ⟶ L, β ≫ α = γ := by
  let P' : CochainComplex 𝒜 ℤ := P
  let Z := (0 : CochainComplex 𝒜 ℤ)
  let sq : CommSq (0 : Z ⟶ L) (0 : Z ⟶ P') α γ := CommSq.mk (by simp)
  let hsq : ∀ n : ℤ, (sq.map (eval 𝒜 (up ℤ) n)).LiftStruct := by
    intro n
    let _ : Projective (P'.X n) := by
      simpa [P'] using P.term_mem n
    refine
      { l := show P'.X n ⟶ L.X n from Projective.factorThru (γ.f n) (α.f n)
        fac_left := by simp
        fac_right := by exact Projective.factorThru_comp (γ.f n) (α.f n) }
  have hQ : IsColimit (CokernelCofork.ofπ (𝟙 P') (show (0 : Z ⟶ P') ≫ 𝟙 P' = 0 by simp)) :=
    CokernelCofork.IsColimit.ofId (0 : Z ⟶ P') rfl
  have hK :
      IsLimit
        (KernelFork.ofι (kernel.ι α) (kernel.condition α)) :=
    KernelFork.IsLimit.ofι' (kernel.ι α) (kernel.condition α) (fun k hk ↦ kernel.lift' α k hk)
  let obstruction : Cocycle P' (kernel α) 1 :=
    CochainComplex.Lifting.cocycle₁ sq hsq hQ hK
  have hac : (kernel α).Acyclic :=
    kernel_acyclic_of_termwiseEpi_quasiIso α hα
  have hacShift : ((kernel α)⟦(1 : ℤ)⟧).Acyclic := by
    rw [HomologicalComplex.acyclic_iff]
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have hk : IsZero ((kernel α).homology (1 + n)) := by
      rw [← HomologicalComplex.exactAt_iff_isZero_homology]
      exact hac (1 + n)
    exact IsZero.of_iso hk
      (((HomologicalComplex.homologyFunctor 𝒜 (up ℤ) (0 : ℤ)).shiftIso 1 n _ rfl).app
        (kernel α))
  let hnull :
      Homotopy
        (Cocycle.equivHomShift.symm obstruction)
        0 :=
    IsKProjective.homotopyZero (Cocycle.equivHomShift.symm obstruction) hacShift
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
        (fun z : Cocycle P' (kernel α) 1 ↦ z.1)
        (Cocycle.equivHomShift.apply_symm_apply obstruction)
  let cochain : Cochain P' (kernel α) 0 :=
    (-cochainShift).rightUnshift 0 (by simp)
  have hδ : δ 0 1 cochain = obstruction.1 := by
    dsimp [cochain]
    rw [Cochain.δ_rightUnshift (-cochainShift) 0 (by simp) 1 0 (by simp)]
    simp only [Int.negOnePow_one, Int.reduceNeg, δ_neg, Cochain.rightUnshift_neg, smul_neg,
      Units.neg_smul, one_smul, neg_neg]
    rw [← hcochainShift]
    exact hobstruction
  letI : sq.HasLift := CochainComplex.Lifting.hasLift sq hsq hQ hK cochain hδ
  exact ⟨sq.lift, sq.fac_right⟩

end CochainComplex

/-! ### Lemma_13_19_7 (from Chap13) -/
open CategoryTheory ComplexShape HomotopyCategory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K L : CochainComplex 𝒜 ℤ}

/- Domain-style sampling:
- primary domain: uniqueness of homotopy lifts from bounded-above projective cochain complexes
  along quasi-isomorphisms;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.MinusWithTermsIn.minus`,
  `CochainComplex.MinusWithTermsIn.term_mem`,
  `homotopyCategory_postcomp_bijective_of_quasiIso_from_boundedAbove_projective`,
  `HomotopyCategory.eq_of_homotopy`,
  `HomotopyCategory.homotopyOfEq`;
- best owner abstraction: `ProjectiveMinus 𝒜` is the chapter owner for a bounded-above complex of
  projective objects, so this lemma should take that owner directly
  instead of separate boundedness and termwise-projective hypotheses;
- primitive data: a projective-minus source complex `P`, a quasi-isomorphism `α : L ⟶ K`, and
  maps `γ : P ⟶ K`, `β₁, β₂ : P ⟶ L`;
- derived API: uniqueness of lifts up to homotopy, obtained from the owner-level bijectivity of
  postcomposition in the homotopy category.

Source/core/bridge triage:
- `source-facing`: the uniqueness-up-to-homotopy statement below;
- `core/canonical`: `ProjectiveMinus 𝒜` and the homotopy-category postcomposition bijection for
  K-projective sources;
- `bridge/view`: the passage from commuting-up-to-homotopy triangles to equality in the homotopy
  category, then back to a homotopy via `homotopyOfEq`.
-/

-- Proof sketch: pass to the homotopy category. The hypotheses `β₁ ≫ α ∼ γ` and `β₂ ≫ α ∼ γ`
-- say that postcomposition by `α` sends the classes of `β₁` and `β₂` to the same morphism
-- `P^• ⟶ K^•`. By Remark 13.19.5, instantiated with the owner
-- `ProjectiveMinus 𝒜`,
-- postcomposition with the quasi-isomorphism `α` is bijective on maps out of `P^•`, so those
-- classes are equal; then
-- `HomotopyCategory.homotopyOfEq` yields a homotopy `β₁ ∼ β₂`.
/-- Lemma 13.19.7: if `α : L^• ⟶ K^•` is a quasi-isomorphism, `P^•` is bounded above with
projective terms, and two morphisms `β₁, β₂ : P^• ⟶ L^•` both make the triangle with
`γ : P^• ⟶ K^•` commute up to homotopy, then `β₁` and `β₂` are homotopic. -/
theorem homotopic_lifts_along_quasiIso_from_boundedAbove_projective
    (P : ProjectiveMinus 𝒜) (α : L ⟶ K) [QuasiIso α]
    (γ : (P : CochainComplex 𝒜 ℤ) ⟶ K)
    (β₁ β₂ : (P : CochainComplex 𝒜 ℤ) ⟶ L)
    (hβ₁ : Nonempty (Homotopy (β₁ ≫ α) γ))
    (hβ₂ : Nonempty (Homotopy (β₂ ≫ α) γ)) :
    Nonempty (Homotopy β₁ β₂) := by
  let Q := HomotopyCategory.quotient 𝒜 (up ℤ)
  obtain ⟨hβ₁⟩ := hβ₁
  obtain ⟨hβ₂⟩ := hβ₂
  refine ⟨homotopyOfEq _ _ ?_⟩
  apply (homotopyCategory_postcomp_bijective_of_quasiIso_from_boundedAbove_projective α P).injective
  simpa [Q, Functor.map_comp] using
    (eq_of_homotopy _ _ hβ₁).trans (eq_of_homotopy _ _ hβ₂).symm

end CochainComplex

/-! ### Lemma_13_19_8 (from Chap13) -/
open CategoryTheory ComplexShape DerivedCategory HomotopyCategory

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

/- Domain-style sampling:
- primary domain: morphisms from bounded-above projective cochain complexes in the homotopy and
  derived categories;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.MinusWithTermsIn.instIsKProjective`,
  `CochainComplex.IsKProjective.Qh_map_bijective`,
  `CochainComplex.isKProjective_of_projective`;
- best owner abstraction: `ProjectiveMinus 𝒜`, the chapter owner for bounded-above cochain
  complexes with projective terms; the bijection on morphisms is derived API coming from its
  canonical `IsKProjective` instance;
- primitive data: the bounded-above projective source
  `P : ProjectiveMinus 𝒜` and the target
  complex `L`;
- derived API: the canonical bijection induced by `DerivedCategory.Qh.map`.

Source/core/bridge triage:
- `source-facing`: the textbook bounded-above/projective comparison statement;
- `core/canonical`: `CochainComplex.IsKProjective.Qh_map_bijective`;
- `bridge/view`: `MinusWithTermsIn.instIsKProjective`, which upgrades the canonical owner to the
  canonical K-projective owner.
-/

-- Proof sketch: the canonical owner `MinusWithTermsIn (isProjective 𝒜)` already packages the
-- bounded-above and termwise-projective hypotheses and carries the canonical `IsKProjective`
-- instance from Definition `13.19.1`, so the statement is exactly
-- `CochainComplex.IsKProjective.Qh_map_bijective` specialized to the homotopy-category image of
-- `L`.
/-- Lemma 13.19.8: if `P^•` is a bounded-above cochain complex of projective objects in an abelian
category `𝒜`, then for every cochain complex `L^•` the canonical map from morphisms
`P^• ⟶ L^•` in the homotopy category `K(𝒜)` to morphisms `P^• ⟶ L^•` in the derived category
`D(𝒜)` is bijective. -/
theorem homotopyCategory_to_derived_bijective_of_boundedAbove_projective
    (P : ProjectiveMinus 𝒜) (L : CochainComplex 𝒜 ℤ) :
    Function.Bijective
      (DerivedCategory.Qh.map : ((KQ).obj P ⟶ (KQ).obj L) → _) := by
  simpa using IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) ((KQ).obj L)

end CochainComplex

/-! ### Lemma_13_19_9 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ObjectProperty

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: short exact sequences of bounded-above cochain complexes and compatible
  projective resolutions;
- sampled owner declarations:
  `CategoryTheory.ShortComplex.Hom`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `CategoryTheory.ObjectProperty.ι`,
  `CochainComplex.minus`,
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.ProjectiveResolution`,
  `CochainComplex.InjectiveResolution`;
- best owner abstraction: the resolving row should be owned by
  `ShortComplex (ProjectiveMinus 𝒜)`, its comparison with the given short exact sequence by a
  single `ShortComplex.Hom`, and short exactness by `ShortComplex.ShortExact`; this is the
  projective dual of the direct short-complex formulation used for injective resolutions in
  Lemma `13.18.9`;
- primitive data here: a short exact sequence `S` of cochain complexes, the short exact resolving
  row in `ProjectiveMinus 𝒜`, the morphism from that underlying short complex to `S`, and the
  quasi-isomorphism witnesses on the three vertical components;
- derived API here: the source-facing existence theorems below, with any columnwise
  `ProjectiveResolution` view recovered directly from the canonical row and comparison morphism.

Source/core/bridge triage:
- `source-facing`: the projective-resolution diagram above a short exact sequence of cochain
  complexes, together with its existence theorems;
- `core/canonical`: `ShortComplex (ProjectiveMinus 𝒜)`, `ShortComplex.Hom`,
  `ShortComplex.ShortExact`, and `CochainComplex.ProjectiveResolution`;
- `bridge/view`: the prescribed-right-resolution specialization below.
-/

local notation "projMinusι" => MinusWithTermsIn.ι (isProjective 𝒜)

section

variable [EnoughProjectives 𝒜]

-- Proof sketch: fix the prescribed projective resolution of `C^•`, resolve `A^•` by projectives,
-- lift the map to `C^•` along the chosen resolution using the projective lifting machinery, and
-- then form the middle resolving complex so that the upper row is short exact and both squares
-- commute. The outer terms of the given short exact sequence are assumed bounded above so that
-- the outer columns are source-faithful projective resolutions, and the middle resolving complex
-- is then bounded above by extension-closure.
/-- Lemma 13.19.9: if `0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` is a short exact sequence of cochain complexes
in an abelian category with enough projectives whose outer terms are bounded above, then it
extends to a commutative diagram whose vertical maps are projective resolutions and whose upper
row is again a short exact sequence of complexes. The middle term is bounded above because
bounded-above cochain complexes are closed under extensions. -/
theorem exists_projectiveResolutionDiagram_of_shortExact
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.minus 𝒜 S.X₁) (hC : CochainComplex.minus 𝒜 S.X₃) :
    ∃ row : ShortComplex (ProjectiveMinus 𝒜), ∃ hom : row.map projMinusι ⟶ S,
      (row.map projMinusι).ShortExact ∧
        QuasiIso hom.τ₁ ∧
        QuasiIso hom.τ₂ ∧
        QuasiIso hom.τ₃ := sorry

-- Proof sketch: run the previous construction starting from the prescribed projective resolution
-- of `C^•`, using `ProjectiveResolution.minus` for the bounded-above right column, lifting the map
-- from the left resolution into that fixed right resolution, and then building the middle
-- resolving complex so that the upper row is short exact.
/-- Given a chosen projective resolution of the right complex, the diagram can be built with that
resolution as its right column, provided the left term of the short exact row is bounded above;
the right bounded-above hypothesis is already supplied by the chosen projective resolution. The
middle term is then bounded above by short exactness. -/
theorem exists_projectiveResolutionDiagram_of_shortExact_with_rightResolution
    (S : ShortComplex (CochainComplex 𝒜 ℤ)) (hS : S.ShortExact)
    (hA : CochainComplex.minus 𝒜 S.X₁) (P : ProjectiveResolution S.X₃) :
    ∃ (Q R : ProjectiveMinus 𝒜) (f : Q ⟶ R) (g : R ⟶ P.complex) (hfg : f ≫ g = 0)
      (φ : (ShortComplex.mk f g hfg).map projMinusι ⟶ S),
        φ.τ₃ = P.π ∧
          ((ShortComplex.mk f g hfg).map projMinusι).ShortExact ∧
          QuasiIso φ.τ₁ ∧
          QuasiIso φ.τ₂ := sorry

end

end CochainComplex

/-! ### Lemma_13_19_10 (from Chap13) -/
open CategoryTheory CategoryTheory.Limits ComplexShape DerivedCategory DerivedCategory.TStructure
  HomotopyCategory
  HomologicalComplex

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {K L : CochainComplex 𝒜 ℤ}

/- Domain-style sampling:
- primary domain: hom-vanishing from bounded-above projective cochain complexes, detected by
  strict source support, target homology truncation, and the K-projective comparison from the
  homotopy category to the derived category;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.IsKProjective.Qh_map_bijective`,
  `CochainComplex.isZero_of_isStrictlyGE`,
  `CochainComplex.isZero_of_isStrictlyLE`,
  `CochainComplex.quasiIso_ιTruncLE_iff`,
  `DerivedCategory.isIso_Q_map_iff_quasiIso`;
- best owner abstraction: `ProjectiveMinus 𝒜` is the source-facing owner for the bounded-above
  projective source complex, and `IsKProjective.Qh_map_bijective` is the canonical comparison
  owner; the target homology-vanishing hypothesis should first be turned into the canonical
  truncation quasi-isomorphism `K.truncLE (n - 1) ⟶ K`, and only then transported across the
  comparison map;
- source/core/bridge triage:
  `source-facing`: the homotopy-category vanishing statement of Lemma `13.19.10`;
  `core/canonical`: `ProjectiveMinus 𝒜`, `IsKProjective.Qh_map_bijective`, and the truncation map
    `K.ιTruncLE (n - 1)`;
  `bridge/view`: the target homology-vanishing condition `∀ i ≥ n, IsZero (K.homology i)` as the
    proof that `K.ιTruncLE (n - 1)` is a quasi-isomorphism, and the resulting derived-category
    vanishing statement for maps out of `Q.obj P`.

Primitive data are the bounded-above projective source `P : ProjectiveMinus 𝒜`, the strict lower
support bound on `P`, the target complex `K`, and the homology-vanishing range on `K`. The
derived-category equality-to-zero statement is only a `bridge/view` corollary of the homotopy
statement through `IsKProjective.Qh_map_bijective`; it is not the owner theorem. -/

local notation "KQ" => quotient 𝒜 (up ℤ)

/-- A cochain complex whose homology vanishes in degrees `≥ n` lies in `D^{≤ n - 1}` after
passing to the derived category. -/
theorem isLE_of_homology_vanishing_ge
    (n : ℤ) (hK : ∀ i : ℤ, n ≤ i → IsZero (K.homology i)) :
    K.IsLE (n - 1) := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  exact hK i (by omega)

/-- Under the hypotheses of the main lemma, every morphism `P^• ⟶ K^•` in the homotopy category
`K(\mathcal A)` is zero. -/
theorem homotopyCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge
    {P : ProjectiveMinus 𝒜} (n : ℤ)
    (hP_ge : (P : CochainComplex 𝒜 ℤ).IsStrictlyGE n)
    (hK : ∀ i : ℤ, n ≤ i → IsZero (K.homology i))
    (f : (KQ).obj P ⟶ (KQ).obj K) :
    f = 0 := by
  letI : (P : CochainComplex 𝒜 ℤ).IsStrictlyGE n := hP_ge
  letI : K.IsLE (n - 1) := isLE_of_homology_vanishing_ge n hK
  let K' := K.truncLE (n - 1)
  let e := Iso.homCongr ((quotientCompQhIso 𝒜).app P) ((quotientCompQhIso 𝒜).app K)
  let e' := Iso.homCongr ((quotientCompQhIso 𝒜).app P) ((quotientCompQhIso 𝒜).app K')
  have hι : IsIso (Q.map (K.ιTruncLE (n - 1))) := by
    rw [isIso_Q_map_iff_quasiIso]
    infer_instance
  let f' : Q.obj P ⟶ Q.obj K' := e (Qh.map f) ≫ inv (Q.map (K.ιTruncLE (n - 1)))
  obtain ⟨g, hg⟩ :=
      (IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) ((KQ).obj K')).surjective
      (e'.symm f')
  have hg_zero : g = 0 := by
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient 𝒜 (up ℤ)).map_surjective g
    have hφ_zero : φ = 0 := by
      ext i
      by_cases hi : i < n
      · exact ((P : CochainComplex 𝒜 ℤ).isZero_of_isStrictlyGE n i hi).eq_of_src _ _
      · exact (K'.isZero_of_isStrictlyLE (n - 1) i (by omega)).eq_of_tgt _ _
    simp [hφ_zero]
  have hf'_zero : f' = 0 := by
    have hgf' : e' (Qh.map g) = f' := by
      rw [hg]
      exact e'.apply_symm_apply f'
    have he'_zero : e' 0 = 0 := by
      change (quotientCompQhIso 𝒜).inv.app P ≫ 0 ≫ (quotientCompQhIso 𝒜).hom.app K' = 0
      simp only [zero_comp, comp_zero]
    rw [← hgf']
    rw [hg_zero]
    simpa using he'_zero
  have hQh_zero : Qh.map f = 0 := by
    have he_zero : e 0 = 0 := by
      change (quotientCompQhIso 𝒜).inv.app P ≫ 0 ≫ (quotientCompQhIso 𝒜).hom.app K = 0
      simp only [zero_comp, comp_zero]
    apply e.injective
    calc
      e (Qh.map f) = f' ≫ Q.map (K.ιTruncLE (n - 1)) := by simp [f']
      _ = 0 := by simp [hf'_zero]
      _ = e 0 := he_zero.symm
  have hQh_zero' : Qh.map f = Qh.map 0 := by
    simpa using hQh_zero
  exact (IsKProjective.Qh_map_bijective P ((KQ).obj K)).injective hQh_zero'

/-- Bridge form of Lemma `13.19.10`: if `P^•` is bounded above with projective terms, if
`P^i = 0` for `i < n`, and if `H^i(K^•) = 0` for all `i ≥ n`, then every morphism
`P^• ⟶ K^•` in `D(\mathcal A)` is zero. -/
theorem derivedCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge
    {P : ProjectiveMinus 𝒜} (n : ℤ)
    (hP_ge : (P : CochainComplex 𝒜 ℤ).IsStrictlyGE n)
    (hK : ∀ i : ℤ, n ≤ i → IsZero (K.homology i))
    (f : Q.obj P ⟶ Q.obj K) :
    f = 0 := by
  let e := Iso.homCongr ((quotientCompQhIso 𝒜).app P) ((quotientCompQhIso 𝒜).app K)
  obtain ⟨g, hg⟩ :=
    (IsKProjective.Qh_map_bijective (P : CochainComplex 𝒜 ℤ) ((KQ).obj K)).surjective
      (e.symm f)
  have hg_zero :
      g = 0 :=
    homotopyCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge
      n hP_ge hK g
  have hgf : e (Qh.map g) = f := by
    rw [hg]
    exact e.apply_symm_apply f
  have he_zero : e 0 = 0 := by
    change (quotientCompQhIso 𝒜).inv.app P ≫ 0 ≫ (quotientCompQhIso 𝒜).hom.app K = 0
    simp only [zero_comp, comp_zero]
  rw [← hgf]
  rw [hg_zero]
  simpa using he_zero

end CochainComplex

/-! ### Lemma_13_19_11 (from Chap13) -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ComplexShape
  DerivedCategory HomotopyCategory HomologicalComplex

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {E L : CochainComplex 𝒜 ℤ}

/- Domain-style sampling:
- primary domain: homotopy lifting for bounded-above projective cochain complexes, detected via
  mapping cones, distinguished triangles, and homology-vanishing criteria;
- sampled owner declarations:
  `CochainComplex.ProjectiveMinus`,
  `homotopyCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge`,
  `DerivedCategory.mappingCone_triangle_distinguished`,
  `Triangle.coyoneda_exact₂`;
- best owner abstraction: `ProjectiveMinus 𝒜` is the chapter owner for the bounded-above
  projective source complex, while the lift itself is most canonically extracted from the
  distinguished mapping-cone triangle via `Triangle.coyoneda_exact₂`;
- primitive data: the projective-minus source complex `P`, the maps `β : P ⟶ L` and `α : E ⟶ L`,
  the lower-support bound `P.IsStrictlyGE n`, and the homology conditions on `α`;
- derived API: vanishing of maps from `P` to `mappingCone α` in the homotopy category, and the
  resulting lift `γ : P ⟶ E` whose composite with `α` is homotopic to `β`.

Source/core/bridge triage:
- `source-facing`: the lifting statement in this file;
- `core/canonical`: the owner `ProjectiveMinus 𝒜` and the exactness of represented Hom on a
  distinguished triangle via `Triangle.coyoneda_exact₂`;
- `bridge/view`: the mapping-cone reduction from the homology hypotheses on `α` to vanishing of
  `H^i(mappingCone α)` for `i ≥ n`, then to vanishing of maps out of `P` by Lemma `13.19.10`.
-/

/-- If `H^j(α)` is an isomorphism for all `j > n` and an epimorphism for `j = n`, then the
mapping cone of `α` has zero homology in every degree `i ≥ n`. This is the canonical bridge from
the source-facing homology hypotheses on `α` to the mapping-cone vanishing used in
Lemma `13.19.11`. -/
theorem isZero_mappingCone_homology_of_homologyMap_iso_above_and_epi_at
    (α : E ⟶ L) (n i : ℤ)
    (hα_iso : ∀ j : ℤ, n < j → IsIso (homologyMap α j))
    (hα_epi : Epi (homologyMap α n))
    (hi : n ≤ i) :
    IsZero ((mappingCone α).homology i) := by
  let T : Triangle (CochainComplex 𝒜 ℤ) := mappingCone.triangle α
  have hT : Q.mapTriangle.obj T ∈ distTriang (DerivedCategory 𝒜) := by
    simpa [T] using DerivedCategory.mappingCone_triangle_distinguished α
  have hmor₁_epi : Epi (homologyMap T.mor₁ i) := by
    by_cases hni : i = n
    · subst hni
      simpa [T] using hα_epi
    · have hni' : n < i := lt_of_le_of_ne hi (fun h ↦ hni h.symm)
      haveI : IsIso (homologyMap α i) := hα_iso i hni'
      simpa [T] using (show Epi (homologyMap α i) by infer_instance)
  have hmor₁_mono : Mono (homologyMap T.mor₁ (i + 1)) := by
    haveI : IsIso (homologyMap α (i + 1)) := hα_iso (i + 1) (by omega)
    simpa [T] using (show Mono (homologyMap α (i + 1)) by infer_instance)
  have hmor₂_zero : homologyMap T.mor₂ i = 0 := by
    exact ((homologyMap_exact₂_of_distTriang T hT i).epi_f_iff).1 hmor₁_epi
  have hδ_zero : homologyδOfTriangle T i (i + 1) rfl = 0 := by
    exact ((homologyMap_exact₁_of_distTriang T hT i (i + 1) rfl).mono_g_iff).1 hmor₁_mono
  simpa [T] using
    (homologyMap_exact₃_of_distTriang T hT i (i + 1) rfl).isZero_X₂ hmor₂_zero hδ_zero
/-- Lemma 13.19.11: let `β : P^• ⟶ L^•` and `α : E^• ⟶ L^•` be morphisms of cochain complexes in
an abelian category, with `P^•` a bounded-above complex of projective objects satisfying
`P^i = 0` for `i < n`. If the induced map on homology `H^i(α)` is an isomorphism for `i > n` and
an epimorphism for `i = n`, then there exists a morphism `γ : P^• ⟶ E^•` such that `α ∘ γ` is
homotopic to `β`. -/
theorem exists_homotopy_lift_of_bounded_projective_strictlyGE_of_homologyMap_iso_above_and_epi_at
    (P : ProjectiveMinus 𝒜) (α : E ⟶ L)
    (β : (P : CochainComplex 𝒜 ℤ) ⟶ L) (n : ℤ)
    (hP_ge : ((P : CochainComplex 𝒜 ℤ)).IsStrictlyGE n)
    (hα_iso : ∀ i : ℤ, n < i → IsIso (homologyMap α i))
    (hα_epi : Epi (homologyMap α n)) :
    ∃ γ : (P : CochainComplex 𝒜 ℤ) ⟶ E, Nonempty (Homotopy (γ ≫ α) β) := by
  let Ho := HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)
  let T : Triangle (HomotopyCategory 𝒜 (ComplexShape.up ℤ)) := mappingCone.triangleh α
  have hT : T ∈ distTriang (HomotopyCategory 𝒜 (ComplexShape.up ℤ)) := by
    simpa [T] using HomotopyCategory.mappingCone_triangleh_distinguished α
  have hβ_zero : Ho.map β ≫ T.mor₂ = 0 := by
    change Ho.map (β ≫ mappingCone.inr α) = 0
    simpa [Ho] using
      homotopyCategory_hom_eq_zero_of_bounded_projective_strictlyGE_and_homology_vanishing_ge
        n hP_ge
        (fun i hi ↦
          isZero_mappingCone_homology_of_homologyMap_iso_above_and_epi_at α n i hα_iso hα_epi hi)
        (Ho.map (β ≫ mappingCone.inr α))
  obtain ⟨γ, hγ⟩ := T.coyoneda_exact₂ hT (Ho.map β) hβ_zero
  obtain ⟨γ, rfl⟩ := Ho.map_surjective γ
  refine ⟨γ, ⟨homotopyOfEq _ _ ?_⟩⟩
  simpa [Ho, T, Functor.map_comp] using hγ.symm

end CochainComplex
