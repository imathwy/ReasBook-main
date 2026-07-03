import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_92_1 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling:
- primary domain: the Stacks-project object `T(K, f)` and its vanishing criterion in `D(A)`;
- sampled owner-side declarations:
  `(ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory`,
  `DerivedCategory.singleFunctor`,
  `Functor.ofOpSequence`,
  `CategoryTheory.IsDerivedLimit`;
- best owner abstraction: keep the source-facing owner `T(K, f)` visible, realized through the
  canonical internal-Hom owner on `D(A)` under an ambient monoidal-closed structure, while the
  localization-away predicate remains the canonical owner-independent vanishing criterion;
- primitive data: `f : A`, `K : D(A)`, and the restriction-of-scalars functor `D(A_f) ⥤ D(A)`;
- derived API: the Milnor tower model of `T(K, f)`, the equivalence theorem to the vanishing
  predicate, and the module-level specialization `ModuleCat.moduleLocalizationAwayTVanishing`.

Layer triage:
- `source-facing`: `localizationAwayT H f K`, the textbook `T(K, f)`;
- `core/canonical`: the owner-independent predicate
  `localizationAwayDerivedHomVanishingCondition f K`;
- `bridge/view`: `localizationAwayTower`, `localizationAwayT_isDerivedLimit`, the vanishing
  equivalence, and the degree-zero module specialization. -/

/-- Lemma 15.92.1 source-facing owner: after restriction of scalars along `A → A_f`, every
morphism from an object of `D(A_f)` to `K` is zero. -/
def localizationAwayDerivedHomVanishingCondition (f : A) (K : DMod) : Prop :=
  ∀ E : DerivedCategory (ModuleCat (Localization.Away f)),
    Subsingleton
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶ K)

/-- The constant tower `\cdots \xrightarrow{f} K \xrightarrow{f} K \xrightarrow{f} K` in `D(A)`,
with transition maps given by multiplication by `f`. -/
abbrev localizationAwayTower (f : A) (K : DMod) : ℕᵒᵖ ⥤ DMod :=
  let X : ℕ → DMod := fun _ ↦ K
  let step : (n : ℕ) → X (n + 1) ⟶ X n := fun _ ↦ f • 𝟙 K
  Functor.ofOpSequence step

section Monoidal

variable [MonoidalCategory (DerivedCategory (ModuleCat A))]
  (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- The textbook object `T(K, f)`, realized canonically as the derived internal Hom
`R\mathrm{Hom}_A(A_f, K)` in `D(A)`. -/
abbrev localizationAwayT (f : A) (K : DMod) : DMod := by
  letI := H
  exact (ihom ((single₀).obj (ModuleCat.of A (Localization.Away f)))).obj K

-- Proof sketch: use the standard two-term resolution of `A_f` and identify the resulting derived
-- internal Hom with the Milnor triangle for the constant tower with transition `f • 𝟙`.
/-- Lemma 15.92.1: the textbook object `T(K, f)` is a derived limit of the constant tower
`\cdots \xrightarrow{f} K \xrightarrow{f} K \xrightarrow{f} K`. -/
theorem localizationAwayT_isDerivedLimit (f : A) (K : DMod) :
    IsDerivedLimit (localizationAwayTower f K) (localizationAwayT H f K) := sorry

-- Proof sketch: by derived adjunction, morphisms from an object of `D(A_f)` to `K` after
-- restriction of scalars are the same source-facing data as morphisms into `T(K, f)`, so the
-- universal vanishing condition is equivalent to `T(K, f)` being zero.
/-- The textbook vanishing statement `T(K, f) = 0` is equivalent to the owner-independent
localization-away derived-Hom vanishing condition. -/
theorem localizationAwayT_isZero_iff
    (f : A) (K : DMod) :
    IsZero (localizationAwayT H f K) ↔
      localizationAwayDerivedHomVanishingCondition f K := sorry

/-- Rewriting the owner-independent vanishing condition in terms of the source-facing object
`T(K, f)`. -/
theorem localizationAwayDerivedHomVanishingCondition_iff
    (f : A) (K : DMod) :
    localizationAwayDerivedHomVanishingCondition f K ↔
      IsZero (localizationAwayT H f K) := by
  simpa using (localizationAwayT_isZero_iff H f K).symm

end Monoidal

end

end CategoryTheory.DerivedCategory

namespace ModuleCat

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/-- The module-level vanishing condition `T(M, f) = 0`, expressed by specializing the derived
owner from Lemma `15.92.1` to the degree-zero object `M[0]`. -/
def moduleLocalizationAwayTVanishing (M : ModuleCat A) (f : A) : Prop :=
  CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition f ((single₀).obj M)

section Monoidal

variable [MonoidalCategory (DerivedCategory (ModuleCat A))]
  (H : MonoidalClosed (DerivedCategory (ModuleCat A)))

/-- The module-level vanishing condition is exactly the vanishing of the degree-zero specialization
of `T(K, f)`. -/
theorem moduleLocalizationAwayTVanishing_iff (M : ModuleCat A) (f : A) :
    moduleLocalizationAwayTVanishing M f ↔
      IsZero (CategoryTheory.DerivedCategory.localizationAwayT H f ((single₀).obj M)) := by
  simpa [moduleLocalizationAwayTVanishing] using
    CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition_iff
      H f ((single₀).obj M)

end Monoidal

end

end ModuleCat

/-! ### Lemma_15_92_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

namespace CategoryTheory.DerivedCategory

/- Domain-style sampling:
- primary domain: localization-away vanishing loci in the derived category of `A`-modules;
- sampled owner-side declarations:
  `localizationAwayDerivedHomVanishingCondition`,
  `Ideal`,
  `Ideal.IsRadical`,
  the downstream containment owner `IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing ideal
  `K.localizationAwayDerivedHomVanishingIdeal`, built from the primitive predicate
  `localizationAwayDerivedHomVanishingCondition f K`;
- primitive data: `K : DMod` and the vanishing predicate in the scalar `f : A`;
- derived API: membership rewriting and the downstream containment formulation of derived
  completeness.

Layer triage:
- `source-facing`: `K.localizationAwayDerivedHomVanishingIdeal`;
- `core/canonical`: the primitive predicate `localizationAwayDerivedHomVanishingCondition`;
- `bridge/view`: the membership iff and the derived-completeness containment API. -/

-- Proof sketch: for `f = 0`, the localization `A_0` is the zero ring, so `D(A_0)` is the zero
-- derived category and every morphism out of an object of `D(A_0)` is zero.
/-- The vanishing condition holds for the zero element. -/
theorem localizationAwayDerivedHomVanishingCondition_zero (K : DMod) :
    localizationAwayDerivedHomVanishingCondition 0 K := sorry

-- Proof sketch: use the standard Mayer-Vietoris short exact sequence
-- `0 → A_{f + g} → A_{f(f + g)} ⊕ A_{g(f + g)} → A_{fg(f + g)} → 0`, then apply the long exact
-- sequence of derived `Hom` groups and the multiplicative stability of the vanishing condition.
/-- The vanishing condition is stable under addition of elements. -/
theorem localizationAwayDerivedHomVanishingCondition_add
    {f g : A} {K : DMod}
    (hf : localizationAwayDerivedHomVanishingCondition f K)
    (hg : localizationAwayDerivedHomVanishingCondition g K) :
    localizationAwayDerivedHomVanishingCondition (f + g) K := sorry

-- Proof sketch: `A_{r • f}` is an `A_f`-module via the localization map, so restriction of
-- scalars from `D(A_{r • f})` factors through `D(A_f)`. The vanishing for `f` therefore implies
-- vanishing for `r • f`.
/-- The vanishing condition is stable under multiplication by arbitrary elements of `A`. -/
theorem localizationAwayDerivedHomVanishingCondition_smul
    (r : A) {f : A} {K : DMod}
    (hf : localizationAwayDerivedHomVanishingCondition f K) :
    localizationAwayDerivedHomVanishingCondition (r • f) K := sorry

/-- The ideal of elements `f ∈ A` such that the textbook object `T(K, f)` vanishes, expressed via
the equivalent derived-Hom vanishing condition from Lemma `15.92.1`. -/
def localizationAwayDerivedHomVanishingIdeal (K : DMod) : Ideal A where
  carrier := {f : A | localizationAwayDerivedHomVanishingCondition f K}
  zero_mem' := localizationAwayDerivedHomVanishingCondition_zero K
  add_mem' := fun hf hg ↦ localizationAwayDerivedHomVanishingCondition_add hf hg
  smul_mem' := fun r _ hf ↦ localizationAwayDerivedHomVanishingCondition_smul r hf

-- Proof sketch: this is immediate from the definition of
-- `localizationAwayDerivedHomVanishingIdeal`.
/-- Membership in `K.localizationAwayDerivedHomVanishingIdeal` is exactly the localization-away
derived-Hom vanishing condition. -/
theorem mem_localizationAwayDerivedHomVanishingIdeal_iff (K : DMod) (f : A) :
    f ∈ K.localizationAwayDerivedHomVanishingIdeal ↔
      localizationAwayDerivedHomVanishingCondition f K := Iff.rfl

-- Proof sketch: the multiplicative closure above shows ideal membership. For radicality, if
-- `f^n` lies in the ideal with `n > 0`, then `A_f ≅ A_{f^n}`, so the vanishing condition for
-- `f^n` is equivalent to the vanishing condition for `f`. This proves that the radical is
-- contained in the ideal.
/-- Lemma 15.92.2: for a commutative ring `A` and `K ∈ D(A)`, the set of elements `f ∈ A` such
that `T(K, f) = 0` is a radical ideal of `A`, formalized through the equivalent localization-away
derived-Hom vanishing condition of Lemma `15.92.1`. -/
theorem localizationAwayDerivedHomVanishingIdeal_isRadical (K : DMod) :
    K.localizationAwayDerivedHomVanishingIdeal.IsRadical := sorry

end CategoryTheory.DerivedCategory

end

/-! ### Lemma_15_92_3 (from Chap15) -/
universe u

section

variable {A : Type u} [CommRing A]

namespace ModuleCat

variable {I : Ideal A} (M : ModuleCat A)

/- Domain-style sampling:
- primary domain: adic completeness and derived completeness for modules over a commutative ring;
- sampled owner-side declarations:
  `IsAdicComplete`,
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `isAdicComplete_of_le_of_fg`,
  `surjective_adicCompletion_of_span_eq_of_generatorwise_surjective`;
- best owner abstraction: the chapter owner predicate `M.IsDerivedCompleteWithRespectTo I`,
  whose pointwise expansion in terms of `T(M, f)` is already derived API from
  `Definition_15_92_4`;
- primitive data: the ideal `I`, the module `M`, and the completion map `AdicCompletion.of I M`;
- derived API: the pointwise `T(M, f)` vanishing criterion for each `f ∈ I` and the
  finitely-generated reduction to principal completion maps.

Layer triage:
- `source-facing`: surjectivity of the completion map `M → lim M / I^n M`;
- `core/canonical`: `IsAdicComplete`, `AdicCompletion.of I M`, and
  `M.IsDerivedCompleteWithRespectTo I`;
- `bridge/view`: the generatorwise `T(M, f)` vanishing criterion coming from
  `Definition_15_92_4`. -/

-- Proof sketch: for each `f ∈ I`, the principal ideal `(f)` is finitely generated and contained
-- in `I`, so `M` is also `(f)`-adically complete by `isAdicComplete_of_le_of_fg`. The pointwise
-- vanishing criterion from Definition `15.92.4` then shows that `M` is derived complete with
-- respect to `I`.
/-- Lemma 15.92.3 (1): an `I`-adically complete `A`-module is derived complete with respect to
`I`. Equivalently, for every `f ∈ I` the textbook object `T(M, f)` vanishes. -/
theorem isDerivedCompleteWithRespectTo_of_isAdicComplete
    (hcomplete : IsAdicComplete I M) :
    M.IsDerivedCompleteWithRespectTo I := sorry

-- Proof sketch: choose finitely many generators of `I`. The hypothesis gives the vanishing
-- condition `T(M, f_i) = 0` for each chosen generator because
-- `M.IsDerivedCompleteWithRespectTo I` is exactly the generatorwise localization-away vanishing
-- criterion. Lemma `10.96.7` then reduces surjectivity of `M → lim M / I^n M` to the principal
-- generator cases.
/-- Lemma 15.92.3 (2): if `I` is finitely generated and `M` is derived complete with respect to
`I`, then the canonical map `M → lim M / I^n M` is surjective. Equivalently, it is enough that
`T(M, f) = 0` for every `f ∈ I`. -/
theorem surjective_adicCompletion_of_isDerivedCompleteWithRespectTo
    (hfg : I.FG) (hM : M.IsDerivedCompleteWithRespectTo I) :
    Function.Surjective (AdicCompletion.of I M) := sorry

end ModuleCat

end

/-! ### Definition_15_92_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

namespace CategoryTheory.DerivedCategory

/- Domain-style sampling:
- primary domain: derived completeness in `D(A)` via localization-away derived-Hom vanishing;
- sampled owner-side declarations:
  `localizationAwayDerivedHomVanishingCondition`,
  `localizationAwayDerivedHomVanishingIdeal`,
  `mem_localizationAwayDerivedHomVanishingIdeal_iff`,
  the downstream object-property owner `derivedCompleteObjectProperty`;
- best owner abstraction: the source-facing predicate `K.IsDerivedCompleteWithRespectTo I`,
  whose primitive data is only the ideal containment
  `I ≤ K.localizationAwayDerivedHomVanishingIdeal`;
- primitive data: `K : DMod` and `I : Ideal A`;
- derived API: the pointwise criterion `isDerivedCompleteWithRespectTo_iff` and the module bridge
  `ModuleCat.IsDerivedCompleteWithRespectTo`.

Layer triage:
- `source-facing`: `CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo`;
- `core/canonical`: `K.localizationAwayDerivedHomVanishingIdeal`;
- `bridge/view`: the pointwise criterion and `ModuleCat.IsDerivedCompleteWithRespectTo`. -/

/-- Definition 15.92.4: an object `K` of `D(A)` is derived complete with respect to an ideal
`I ⊆ A` if, for every `f ∈ I`, every morphism from an object of `D(A_f)` to `K` is zero after
restriction of scalars along `A → A_f`. By Lemma `15.92.1`, this is equivalent to the textbook
condition `T(K, f) = 0` for all `f ∈ I`. -/
def IsDerivedCompleteWithRespectTo (K : DMod) (I : Ideal A) : Prop :=
  I ≤ K.localizationAwayDerivedHomVanishingIdeal

/-- An object of `D(A)` is derived complete with respect to `I` exactly when the
localization-away derived-Hom vanishing condition holds for every `f ∈ I`. -/
theorem isDerivedCompleteWithRespectTo_iff
    (K : DMod) (I : Ideal A) :
    K.IsDerivedCompleteWithRespectTo I ↔
      ∀ f ∈ I, localizationAwayDerivedHomVanishingCondition f K :=
  Iff.rfl

/-- The object property on `D(A)` selecting the complexes that are derived complete with respect
to the ideal `I`. -/
abbrev derivedCompleteObjectProperty (I : Ideal A) : ObjectProperty DMod :=
  fun K ↦ K.IsDerivedCompleteWithRespectTo I

end CategoryTheory.DerivedCategory

namespace ModuleCat

/-- The module-theoretic notion of derived completeness with respect to `I`, obtained by applying
the derived-category predicate to the degree-zero object `M[0]`. -/
abbrev IsDerivedCompleteWithRespectTo (M : ModuleCat A) (I : Ideal A) : Prop :=
  ((ModuleCat.single0Functor : ModuleCat A ⥤ DMod).obj M).IsDerivedCompleteWithRespectTo I

/-- The object property on `Mod_A` selecting the modules that are derived complete with respect
to `I`. -/
abbrev derivedCompleteObjectProperty (I : Ideal A) : ObjectProperty (ModuleCat A) :=
  fun M ↦ M.IsDerivedCompleteWithRespectTo I

end ModuleCat

end

/-! ### Proposition_15_92_5 (from Chap15) -/
universe u

section

variable {A : Type u} [CommRing A]

namespace ModuleCat

/- Domain-style sampling:
- primary domain: adic completeness, derived completeness, and `I`-adic separatedness for modules;
- sampled owner-side declarations:
  `IsAdicComplete`,
  `IsHausdorff`,
  `ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete`,
  `ModuleCat.surjective_adicCompletion_of_isDerivedCompleteWithRespectTo`;
- best owner abstraction: the canonical separatedness owner `IsHausdorff I M` together with the
  completeness owner `IsAdicComplete I M`;
- primitive data: the module `M`, the ideal `I`, and the completion map `AdicCompletion.of I M`;
- derived API: the source-facing intersection formula
  `(⨅ n, I ^ n • (⊤ : Submodule A M)) = ⊥` via `isHausdorff_iff`. -/

-- Proof sketch: Lemma `15.92.3` gives derived completeness from `I`-adic completeness and, for
-- finitely generated `I`, surjectivity of the completion map from derived completeness. Combine
-- that surjectivity with the canonical `IsHausdorff` owner for injectivity of the completion map.
/-- Proposition 15.92.5, owner-facing form: for a finitely generated ideal `I`, an `A`-module `M`
is `I`-adically complete if and only if it is derived complete with respect to `I` and
`I`-adically Hausdorff. -/
theorem isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff
    {I : Ideal A} {M : ModuleCat A} (hI : I.FG) :
    IsAdicComplete I M ↔
      M.IsDerivedCompleteWithRespectTo I ∧ IsHausdorff I M := by
  constructor
  · intro hcomplete
    exact ⟨isDerivedCompleteWithRespectTo_of_isAdicComplete M hcomplete, hcomplete.toIsHausdorff⟩
  · rintro ⟨hderived, hhaus⟩
    have hsurj : Function.Surjective (AdicCompletion.of I M) :=
      surjective_adicCompletion_of_isDerivedCompleteWithRespectTo M hI hderived
    exact (AdicCompletion.of_bijective_iff).mp
      ⟨(AdicCompletion.of_injective_iff).mpr hhaus, hsurj⟩

-- Proof sketch: this is the source-facing restatement of the preceding owner-level theorem, using
-- the standard criterion `isHausdorff_iff` for `I`-adic separatedness.
/-- Proposition 15.92.5: for a finitely generated ideal `I`, an `A`-module `M` is `I`-adically
complete if and only if it is derived complete with respect to `I` and is `I`-adically
separated, i.e. `⋂ n, I ^ n M = 0`. -/
theorem isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_iInf_pow_smul_eq_bot
    {I : Ideal A} {M : ModuleCat A} (hI : I.FG) :
    IsAdicComplete I M ↔
      M.IsDerivedCompleteWithRespectTo I ∧
        (⨅ n : ℕ, (I ^ n) • (⊤ : Submodule A M) : Submodule A M) = ⊥ := by
  constructor
  · intro hcomplete
    obtain ⟨hderived, hhaus⟩ :=
      (isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff hI).mp hcomplete
    exact ⟨hderived, IsHausdorff.iInf_pow_smul hhaus⟩
  · rintro ⟨hderived, hsep⟩
    have hhaus : IsHausdorff I M := by
      refine ⟨fun x hx ↦ ?_⟩
      have hx' : x ∈ (⨅ n : ℕ, (I ^ n) • (⊤ : Submodule A M) : Submodule A M) := by
        simpa [SModEq.zero] using hx
      simpa [hsep] using hx'
    exact (isAdicComplete_iff_isDerivedCompleteWithRespectTo_and_isHausdorff hI).mpr
      ⟨hderived, hhaus⟩

end ModuleCat

end

/-! ### Lemma_15_92_6 (from Chap15) -/
open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

/- Domain-style sampling:
- primary domain: object properties on `ModuleCat A` and the generic derived-category owner
  `derivedCategoryCohomologyInProperty`;
- sampled owner-side declarations:
  `ObjectProperty.IsWeakSerreClass`,
  `ObjectProperty.weakSerreSubcategory_inclusion_exact`,
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategory.derivedCompleteObjectProperty`,
  `ModuleCat.derivedCompleteObjectProperty`;
- best owner abstraction: the object-property owners
  `ModuleCat.derivedCompleteObjectProperty I` and
  `DerivedCategory.derivedCompleteObjectProperty I`;
- primitive data: the module and derived derived-complete predicates from
  `Definition_15_92_4`;
- derived API: the weak-LinearRepresentations_Serre_1977 structure on the module owner and the identification of the
  derived owner with the generic cohomology-in-property owner.

Layer triage:
- `source-facing`: derived-complete modules and derived-complete objects with respect to `I`;
- `core/canonical`: `ModuleCat.derivedCompleteObjectProperty I`,
  `DerivedCategory.derivedCompleteObjectProperty I`, and
  `derivedCategoryCohomologyInProperty`;
- `bridge/view`: the pointwise iff restatement below, derived from the owner-level equality. -/

-- Proof sketch: Lemma 15.92.1 identifies derived completeness with vanishing of
-- `Ext^n_A(A_f, -)` for every `f ∈ I`; the associated long exact sequences show closure under
-- kernels, cokernels, and extensions, and Lemma 12.10.3 packages these closures into the weak
-- LinearRepresentations_Serre_1977 structure.
/-- Lemma 15.92.6: the derived complete `A`-modules with respect to `I` form a weak LinearRepresentations_Serre_1977
subcategory of `Mod_A`. -/
theorem derivedCompleteObjectProperty_isWeakSerreClass :
    IsWeakSerreClass (ModuleCat.derivedCompleteObjectProperty I) := sorry

namespace DerivedCategory

local notation "DMod" => DerivedCategory (ModuleCat A)

-- Proof sketch: use Lemma 15.92.1 to pass between derived completeness of a complex and the
-- vanishing criterion after localizing at each `f ∈ I`. The long exact cohomology sequences show
-- that this criterion holds degreewise on the cohomology modules of `K`.
/-- The derived-complete owner on `D(A)` is exactly the generic cohomology-in-property owner
attached to derived-complete modules. -/
theorem derivedCompleteObjectProperty_eq_derivedCategoryCohomologyInProperty :
    DerivedCategory.derivedCompleteObjectProperty I =
      derivedCategoryCohomologyInProperty (ModuleCat.derivedCompleteObjectProperty I) := by
  ext K
  sorry

/-- Companion pointwise restatement of
`derivedCompleteObjectProperty_eq_derivedCategoryCohomologyInProperty`. -/
theorem isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty
    (K : DMod) :
    K.IsDerivedCompleteWithRespectTo I ↔
      derivedCategoryCohomologyInProperty (ModuleCat.derivedCompleteObjectProperty I) K := by
  change DerivedCategory.derivedCompleteObjectProperty I K ↔
    derivedCategoryCohomologyInProperty (ModuleCat.derivedCompleteObjectProperty I) K
  exact
    (congrArg (fun P : ObjectProperty DMod ↦ P K)
      (derivedCompleteObjectProperty_eq_derivedCategoryCohomologyInProperty I)).to_iff


end DerivedCategory

end

/-! ### Lemma_15_92_7 (from Chap15) -/
universe u

section

variable {A : Type u} [CommRing A]

namespace ModuleCat

/- Domain-style sampling:
- primary domain: derived-complete modules over a commutative ring, with quotient-vanishing and
  submodule-saturation criteria for zero modules;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `derivedCompleteObjectProperty_isWeakSerreClass`,
  `surjective_adicCompletion_of_isDerivedCompleteWithRespectTo`,
  `subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson`;
- best owner abstraction: the project owner predicate `ModuleCat.IsDerivedCompleteWithRespectTo`,
  with the primitive zero-criterion expressed by the owner-level equality
  `I • (⊤ : Submodule A M) = ⊤`;
- primitive data: the ideal `I`, the module `M`, derived completeness of `M`, and the submodule
  equality `I • ⊤ = ⊤`;
- derived API: the source-facing quotient formulation
  `Subsingleton (M ⧸ I • (⊤ : Submodule A M))`.

Layer triage:
- `source-facing`: the quotient-vanishing statement `M / IM = 0`;
- `core/canonical`: `M.IsDerivedCompleteWithRespectTo I` together with `I • ⊤ = ⊤`;
- `bridge/view`: the quotient-subsingleton companion theorem below. -/

variable {I : Ideal A} {M : ModuleCat A}

local notation "IM" => I • (⊤ : Submodule A M)

-- Proof sketch: write `I = (f₁, …, f_r)` and choose the largest `i` such that
-- `M / (f₁, …, fᵢ) M` is nonzero. Lemma `15.92.6` shows this quotient is still derived complete.
-- Then `fᵢ₊₁` acts surjectively on it because `(M ⧸ I • ⊤)` is zero, producing a nonzero derived
-- limit of the constant tower with transition map `fᵢ₊₁`, contradicting derived completeness.
/-- Lemma 15.92.7, owner-level form: if `I` is finitely generated and a derived-complete module
`M` satisfies `IM = M`, then `M` is zero. -/
lemma subsingleton_of_isDerivedCompleteWithRespectTo_of_smul_top_eq_top
    (hI : I.FG) (hM : M.IsDerivedCompleteWithRespectTo I) (hIM : IM = ⊤) :
    Subsingleton M := sorry

/-- Lemma 15.92.7: if `I` is finitely generated and an `A`-module `M` is derived complete with
respect to `I`, then the vanishing condition `M / I M = 0`, formalized by the quotient
`M ⧸ I • (⊤ : Submodule A M)` being subsingleton, forces `M` itself to be zero. -/
lemma subsingleton_of_isDerivedCompleteWithRespectTo_of_subsingleton_quotient_smul_top
    (hI : I.FG) (hM : M.IsDerivedCompleteWithRespectTo I) (hquot : Subsingleton (M ⧸ IM)) :
    Subsingleton M := by
  apply subsingleton_of_isDerivedCompleteWithRespectTo_of_smul_top_eq_top hI hM
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  have hx : Submodule.mkQ IM x = 0 := Subsingleton.elim _ _
  simpa [Submodule.Quotient.mk_eq_zero] using hx

end ModuleCat

end

/-! ### Lemma_15_92_8 (from Chap15) -/
open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling:
- primary domain: pseudo-coherent objects in `D(A)` and the chapter owner predicate
  `K.IsDerivedCompleteWithRespectTo I`;
- sampled owner-side declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete`,
  `derivedCompleteObjectProperty_isWeakSerreClass`,
  `isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty`;
- best owner abstraction: the source-facing statements below should stay on the canonical owner
  `K.IsDerivedCompleteWithRespectTo I`, with module-level adic completeness entering only through
  the bridge theorem from Lemma `15.92.3`;
- primitive data: the ideal `I`, the derived object `K`, and the ring object
  `ModuleCat.of A A`;
- derived API: the weak-LinearRepresentations_Serre_1977 owner on derived-complete modules and the cohomology-in-property
  reformulation from Lemma `15.92.6`.

Layer triage:
- `source-facing`: Lemma `15.92.8` itself;
- `core/canonical`: `K.IsDerivedCompleteWithRespectTo I`;
- `bridge/view`: `ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete` and
  `isDerivedCompleteWithRespectTo_iff_mem_derivedCategoryCohomologyInProperty`. -/

-- Proof sketch: a pseudo-coherent object of `D(A)` is represented by a bounded-above finite-free
-- complex, so every cohomology module is a subquotient of finite free `A`-modules and hence is
-- pseudo-coherent as an `A`-module. Since `A`, viewed as an `A`-module, is derived complete,
-- pseudo-coherent modules are derived complete by the weak LinearRepresentations_Serre_1977 property from Lemma `15.92.6`;
-- apply the cohomological criterion there to conclude that `K` itself is derived complete.
/-- Lemma 15.92.8: if the ring `A`, viewed as an `A`-module, is derived complete with respect to
an ideal `I`, then every pseudo-coherent object of `D(A)` is derived complete with respect to
`I`. -/
theorem isDerivedCompleteWithRespectTo_of_isPseudoCoherent
    {K : DMod} (hA : (ModuleCat.of A A).IsDerivedCompleteWithRespectTo I)
    (hK : K.IsPseudoCoherent) :
    K.IsDerivedCompleteWithRespectTo I := sorry

-- Proof sketch: by Lemma `15.92.3`, `I`-adic completeness of the `A`-module `A` implies derived
-- completeness with respect to `I`; then apply `isDerivedCompleteWithRespectTo_of_isPseudoCoherent`.
/-- If the ring `A`, viewed as an `A`-module, is `I`-adically complete, then every
pseudo-coherent object of `D(A)` is derived complete with respect to `I`. -/
theorem isDerivedCompleteWithRespectTo_of_isPseudoCoherent_of_isAdicComplete
    {K : DMod} (hA : IsAdicComplete I (ModuleCat.of A A))
    (hK : K.IsPseudoCoherent) :
    K.IsDerivedCompleteWithRespectTo I := by
  exact isDerivedCompleteWithRespectTo_of_isPseudoCoherent I
    (ModuleCat.isDerivedCompleteWithRespectTo_of_isAdicComplete (ModuleCat.of A A) hA)
    hK

end

/-! ### Lemma_15_92_9 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "Cpx" => CochainComplex (ModuleCat A) ℤ
local notation "single₀" => (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ) : ModuleCat A ⥤ DMod)

private abbrev singleZeroCpx (M : ModuleCat A) : Cpx :=
  (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M

private noncomputable instance : (DerivedCategory.Q : Cpx ⥤ DMod).Monoidal := by
  change (((HomotopyCategory.quotient (ModuleCat A) (up ℤ)) ⋙
      (DerivedCategory.Qh : HomotopyCategory (ModuleCat A) (up ℤ) ⥤ DMod))).Monoidal
  infer_instance

section Monoidal

local instance : MonoidalCategory DMod := inferInstance

private noncomputable abbrev localizationAwayTensorLinearEquiv
    (f g : A) :
    Localization.Away f ⊗[A] Localization.Away g ≃ₗ[A] Localization.Away (f * g) :=
  ((LocalizedModule.equivTensorProduct (Submonoid.powers f) (Localization.Away g)).symm.restrictScalars A) ≪≫ₗ
    awayMulLinearEquiv g f A ≪≫ₗ
      awayEqLinearEquiv A (mul_comm g f)

private noncomputable abbrev localizationAwayTensorModuleIso
    (f g : A) :
    ModuleCat.of A (Localization.Away f ⊗[A] Localization.Away g) ≅
      ModuleCat.of A (Localization.Away (f * g)) :=
  (localizationAwayTensorLinearEquiv f g).toModuleIso

private theorem singleZeroTensorComplex_eq_tensorObj
    (M N : ModuleCat A) :
    singleZeroCpx (ModuleCat.of A ((↑M) ⊗[A] ↑N)) =
      HomologicalComplex.tensorObj (singleZeroCpx M) (singleZeroCpx N) := by
  sorry

private noncomputable def singleZeroDerivedTensorModuleIso
    (M N : ModuleCat A) :
    ((single₀).obj M ⊗[A]^L (single₀).obj N) ≅
      (single₀).obj (ModuleCat.of A ((↑M) ⊗[A] ↑N)) :=
  ((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (ModuleCat.of A ((↑M) ⊗[A] ↑N))).symm) ≪≫
    (DerivedCategory.Q.mapIso (eqToIso (singleZeroTensorComplex_eq_tensorObj M N))) ≪≫
      (Functor.Monoidal.μIso (DerivedCategory.Q : Cpx ⥤ DMod) (singleZeroCpx M) (singleZeroCpx N)).symm ≪≫
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M) ⊗ᵢ
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app N)) ≪≫
          derivedCategory_tensorObj_iso_derivedTensorProduct ((single₀).obj M) ((single₀).obj N)).symm

private noncomputable def localizationAwayTensorIso
    (f g : A) :
    ((single₀).obj (ModuleCat.of A (Localization.Away f)) ⊗[A]^L
      (single₀).obj (ModuleCat.of A (Localization.Away g))) ≅
      (single₀).obj (ModuleCat.of A (Localization.Away (f * g))) :=
  singleZeroDerivedTensorModuleIso
      (ModuleCat.of A (Localization.Away f))
      (ModuleCat.of A (Localization.Away g)) ≪≫
    (single₀).mapIso (localizationAwayTensorModuleIso f g)

/- Domain-style sampling for Lemma 15.92.9:
- primary domain: localization-away objects `T(K, f)` in the closed monoidal derived category
  `D(A)`;
- sampled owner declarations:
  `CategoryTheory.DerivedCategory.localizationAwayT`,
  `CategoryTheory.derivedInternalHomTensorIso`,
  `awayMulLinearEquiv`,
  `CategoryTheory.DerivedCategory.localizationAwayT_isDerivedLimit`,
  `CategoryTheory.derivedInternalHom_comp`;
- best owner abstraction: the chapter owner `localizationAwayT H f K` for the textbook object
  `T(K, f)`;
- primitive data: `H : RHomPkg`, `f g : A`, and `K : DMod`;
- derived API: the product-localization comparison below.

Layer triage:
- `source-facing`: `localizationAwayT_mul`;
- `core/canonical`: `localizationAwayT H f K` and the currying comparison
  `derivedInternalHomTensorIso`;
- `bridge/view`: the identification of iterated away localizations with localization away from
  `f * g`, concretely routed through the module-side owner `awayMulLinearEquiv` on
  `Localization.Away g` and then transported to degree-zero objects in `D(A)`, expressed as an
  object-level `Iso`. -/

-- Proof sketch: combine the tensor-Hom currying comparison from Lemma `15.74.1` with the
-- module-side owner `awayMulLinearEquiv` identifying iterated away localization with
-- localization away from `f * g`, transported to the degree-zero objects `A_f`, `A_g`, and
-- `A_{fg}` in `D(A)`.
/-- The canonical comparison morphism
`T(T(K, g), f) ⟶ T(K, fg)` obtained by currying together the two localization-away internal-Hom
owners and then identifying the degree-zero localized tensor factor with `A_{fg}[0]`. -/
private noncomputable def localizationAwayT_mul_hom
    (H : RHomPkg) (f g : A) (K : DMod) :
    localizationAwayT H f (localizationAwayT H g K) ⟶ localizationAwayT H (f * g) K :=
  (derivedInternalHomTensorIso H
      ((single₀).obj (ModuleCat.of A (Localization.Away f)))
      ((single₀).obj (ModuleCat.of A (Localization.Away g)))
      K).hom ≫
    derivedInternalHomMap H (localizationAwayTensorIso f g).inv (𝟙 K)

private theorem localizationAwayT_mul_hom_isIso
    (H : RHomPkg) (f g : A) (K : DMod) :
    IsIso (localizationAwayT_mul_hom H f g K) := by
  sorry

/-- Lemma 15.92.9: the textbook localization-away object satisfies
`T(T(K, g), f) ≃ T(K, fg)`. This is the owner-level form of the iterated derived internal-Hom
comparison for the degree-zero localization objects `A_f`, `A_g`, and `A_{fg}`. -/
noncomputable abbrev localizationAwayT_mul
    (H : RHomPkg) (f g : A) (K : DMod) :
    localizationAwayT H f (localizationAwayT H g K) ≅ localizationAwayT H (f * g) K := by
  letI := localizationAwayT_mul_hom_isIso H f g K
  exact asIso (localizationAwayT_mul_hom H f g K)

end Monoidal

end

end CategoryTheory.DerivedCategory

/-! ### Lemma_15_92_10 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open Opposite
open scoped DerivedInternalHom

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "RHomPkg" => MonoidalClosed DMod
local notation "Q" => (DerivedCategory.Q : CochainComplex (ModuleCat A) ℤ ⥤ DMod)

/-- The extended alternating Čech complex on a finite generating family `f`, viewed as an object
of `D(A)` by extending the natural `ℕ`-indexed cochain complex to a `ℤ`-indexed one and passing to
the derived category. -/
abbrev extendedAlternatingCechDerivedObject {r : ℕ} (f : Fin r → A) : DMod :=
  Q.obj ((extendedAlternatingCechComplex f A).extend embeddingUpNat)

-- Proof sketch: identify `I` with the ideal generated by `f`, use Lemma `15.92.9` to compute
-- `RHom_A(A_g, RHom_A(\check C(f), K))` by adjoining `g` to the Čech family, and then apply
-- Lemmas `15.29.4`, `15.29.5`, and `15.92.1` exactly as in the textbook argument to show the
-- resulting derived internal-Hom object vanishes for every `g ∈ I`.
/-- For a chosen finite generating family of `I`, the explicit completion object
`RHom_A(\check C(f), K)` is derived complete with respect to `I`. -/
theorem derivedCompletionObj_isDerivedComplete_of_span_range
    (I : Ideal A) (H : RHomPkg)
    {r : ℕ} (f : Fin r → A) (hI : I = Ideal.span (Set.range f)) (K : DMod) :
    (RHom[H](extendedAlternatingCechDerivedObject f, K)).IsDerivedCompleteWithRespectTo I := sorry

-- Proof sketch: the map from the extended alternating Čech complex to `A[0]` induces a morphism
-- `η : K ⟶ RHom_A(\check C(f), K)`. The previous theorem gives that the target is derived
-- complete, and the textbook argument shows that precomposition with `η` gives a bijection on
-- morphism sets into every derived-complete object.
/-- For a chosen finite generating family of `I`, the explicit completion object carries a
universal morphism from `K` whose induced map on morphism sets into any derived-complete object is
bijective. -/
theorem exists_derivedCompletionMap_of_span_range
    (I : Ideal A) (H : RHomPkg)
    {r : ℕ} (f : Fin r → A) (hI : I = Ideal.span (Set.range f))
    (K : DMod) :
    ∃ η : K ⟶ RHom[H](extendedAlternatingCechDerivedObject f, K),
      ∀ E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory,
        Function.Bijective
          (fun φ : RHom[H](extendedAlternatingCechDerivedObject f, K) ⟶ E.obj ↦ η ≫ φ) := sorry

-- Proof sketch: choose a finite generating family `f` for `I`. The companion completion functor
-- `K ↦ RHom_A(\check C(f), K)` lands in the full subcategory of derived-complete objects by
-- `derivedCompletionObj_isDerivedComplete_of_span_range`, and
-- `exists_derivedCompletionMap_of_span_range` supplies the universal property showing that it is
-- left adjoint to the inclusion.
/-- Lemma 15.92.10: if `I` is a finitely generated ideal of `A`, then the inclusion of the full
subcategory of derived-complete objects of `D(A)` into `D(A)` has a left adjoint; for a chosen
finite generating family of `I`, this reflector is realized by the derived internal Hom from the
extended alternating Čech complex on those generators. -/
theorem derivedCompleteInclusion_isRightAdjoint_of_fg
    (I : Ideal A) (hI : I.FG) :
    Functor.IsRightAdjoint ((DerivedCategory.derivedCompleteObjectProperty I).ι) := sorry

end

end DerivedCategory

/-! ### Remark_15_92_11 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
private abbrev derivedCompleteInclusion (I : Ideal A) :=
  (DerivedCategory.derivedCompleteObjectProperty I).ι
private abbrev derivedCompleteLeftAdjoint (I : Ideal A) (hI : I.FG) :
    DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory :=
  @Functor.leftAdjoint _ _ _ _ (derivedCompleteInclusion I)
    (derivedCompleteInclusion_isRightAdjoint_of_fg I hI)

private abbrev derivedCompleteAdjunction (I : Ideal A) (hI : I.FG) :
    derivedCompleteLeftAdjoint I hI ⊣ derivedCompleteInclusion I :=
  @Adjunction.ofIsRightAdjoint _ _ _ _ (derivedCompleteInclusion I)
    (derivedCompleteInclusion_isRightAdjoint_of_fg I hI)

/-- Remark 15.92.11: the derived completion endofunctor on `D(A)` is the composite of the chosen
left adjoint to the inclusion `D_comp(A, I) ⥤ D(A)` with that inclusion, for a finitely generated
ideal `I ⊆ A`. Its value on `K` is the textbook object denoted `K^∧`. -/
abbrev derivedCompletion (I : Ideal A) (hI : I.FG) : DMod ⥤ DMod :=
  derivedCompleteLeftAdjoint I hI ⋙ derivedCompleteInclusion I

/-- The derived completion `K^∧` of an object `K` of `D(A)`. -/
abbrev derivedCompletionOf (I : Ideal A) (hI : I.FG) (K : DMod) : DMod :=
  (derivedCompletion I hI).obj K

notation:max K:max "^∧[" I:max ", " hI:max "]" => derivedCompletionOf I hI K

/-- The canonical map from `K` to its derived completion `K^∧`. -/
abbrev toDerivedCompletion (I : Ideal A) (hI : I.FG) (K : DMod) :
    K ⟶ K^∧[I, hI] :=
  (derivedCompleteAdjunction I hI).unit.app K

/-- The derived completion of `K` is derived complete with respect to `I`. -/
theorem derivedCompletionOf_isDerivedComplete
    (I : Ideal A) (hI : I.FG) (K : DMod) :
    (K^∧[I, hI]).IsDerivedCompleteWithRespectTo I :=
  ((derivedCompleteLeftAdjoint I hI).obj K).property

end

end DerivedCategory

/-! ### Lemma_15_92_12 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.92.12:
- primary domain: essential-image statements for the derived restriction-of-scalars functor
  `D(A_f) ⥤ D(A)` and derived completion in `D(A)`;
- sampled owner declarations:
  `Functor.essImage`,
  `Functor.obj_mem_essImage`,
  `Functor.EssSurj.mem_essImage`,
  `derivedCompletionOf`;
- best owner abstraction: the canonical object property
  `((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).essImage`
  on `D(A)`, rather than an explicit witness `∃ E, Nonempty (F.obj E ≅ K)`;
- primitive data: the ideal `I`, the finitely generated hypothesis `hI`, the element `f ∈ I`, the
  object `K : D(A)`, and membership of `K` in the essential image of the localization-away
  restriction functor;
- derived API: the existential witness model of an essential-image proof, which should stay
  internal to the canonical owner `Functor.essImage`.

Source/core/bridge triage:
- `source-facing`: the vanishing of the derived completion of an object coming from `D(A_f)`;
- `core/canonical`: `Functor.essImage` for the restriction functor and `derivedCompletionOf`;
- `bridge/view`: the existential witness formulation of essential-image membership, which is
  subsumed by the owner predicate. -/

-- Proof sketch: by Lemma `15.92.1`, any object of `D(A_f)` has zero morphisms into every
-- `I`-derived-complete object when `f ∈ I`. Therefore the object `K`, which comes from `D(A_f)`,
-- has zero morphisms into every object of the reflective subcategory. Applying the universal
-- property of the left adjoint from Lemma `15.92.10` to the zero object shows that the reflector
-- of `K` is itself zero.
/-- Lemma 15.92.12: let `A` be a commutative ring and let `I ⊆ A` be a finitely generated ideal.
If `K` comes from `D(A_f)` for some `f ∈ I`, formalized canonically as membership in the
essential image of the restriction functor
`D(A_f) ⥤ D(A)`, then the derived completion of `K` with respect to `I` is zero. -/
theorem derivedCompletion_isZero_of_mem_essImage_localizationAway
    (I : Ideal A) (hI : I.FG) {f : A} (hf : f ∈ I) {K : DMod}
    (hK :
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).essImage
        K)) :
    IsZero (derivedCompletionOf I hI K) := sorry

end

end DerivedCategory

/-! ### Lemma_15_92_13 (from Chap15) -/
noncomputable section

open CategoryTheory
open DerivedCategory
open scoped DerivedInternalHom

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.92.13:
- primary domain: derived completion and derived internal Hom in `D(A)`;
- sampled owner declarations:
  `DerivedCategory.derivedCompletionOf`,
  `DerivedCategory.toDerivedCompletion`,
  `DerivedCategory.extendedAlternatingCechDerivedObject`,
  `CategoryTheory.derivedInternalHomTensorIso`;
- best owner abstraction:
  `source-facing`: compatibility of derived completion with `RHom_A(K, -)` and the induced map
    from `K ⟶ K^∧`;
  `core/canonical`: the derived-completion reflector `derivedCompletionOf I hI` and its unit
    `toDerivedCompletion I hI`;
  `bridge/view`: the explicit Čech-model object from Lemma `15.92.10`, which realizes the same
    completion functor for a chosen generating family but should not remain the public owner here.
- primitive data: the ideal `I`, the finite-generation witness `hI : I.FG`, the chosen derived
  internal-Hom owner `H : MonoidalClosed DMod`, and the objects `K`, `L`;
- derived API: any explicit chosen generators and the Čech-model presentation of completion. -/

-- Proof sketch: choose the canonical derived-completion reflector from Remark `15.92.11`, whose
-- explicit Čech-model realization is supplied by Lemma `15.92.10`. Then apply the
-- tensor-Hom currying comparison from Lemma `15.74.1` together with the symmetry of derived tensor
-- product to identify
-- `RHom_A(\check C(f), RHom_A(K, L))` with `RHom_A(K, RHom_A(\check C(f), L))`.
/-- Lemma 15.92.13 (1): for a ring `A`, a finitely generated ideal `I`, and derived
`A`-complexes `K` and `L`, the derived completion of `R\mathrm{Hom}_A(K, L)` is canonically
isomorphic to `R\mathrm{Hom}_A(K, L^\wedge)`. -/
theorem derivedCompletionOf_derivedInternalHom_isIsomorphic
    (I : Ideal A) (hI : I.FG) (H : MonoidalClosed DMod)
    (K L : DMod) :
    IsIsomorphic
      ((RHom[H](K, L))^∧[I, hI])
      (RHom[H](K, L^∧[I, hI])) := sorry

-- Proof sketch: the canonical morphism `K ⟶ K^\wedge` supplied by the adjunction from
-- Remark `15.92.11` induces a morphism
-- `RHom_A(K^\wedge, L^\wedge) ⟶ RHom_A(K, L^\wedge)`. Since `L^\wedge` is already derived
-- complete, the universal property of derived completion makes this morphism an isomorphism.
/-- Lemma 15.92.13 (2): for a ring `A`, a finitely generated ideal `I`, and derived
`A`-complexes `K` and `L`, the canonical map `K ⟶ K^\wedge` induces an isomorphism
`R\mathrm{Hom}_A(K^\wedge, L^\wedge) \to R\mathrm{Hom}_A(K, L^\wedge)`. -/
theorem derivedInternalHom_toDerivedCompletion_isIso
    (I : Ideal A) (hI : I.FG) (H : MonoidalClosed DMod)
    (K L : DMod) :
    IsIso
      (derivedInternalHomMap H (toDerivedCompletion I hI K)
        (𝟙 (L^∧[I, hI]))) := sorry

end

end CategoryTheory

/-! ### Lemma_15_92_14 (from Chap15) -/
noncomputable section

open CategoryTheory
open Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/-
Domain-style sampling:
- primary domain: derived completeness in `D(A)` and its behavior under sequential derived limits;
- sampled owner-side declarations:
  `DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `DerivedCategory.isDerivedCompleteWithRespectTo_iff`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.DerivedCategory.localizationAwayT_isDerivedLimit`;
- best owner abstraction: the canonical predicate `K.IsDerivedCompleteWithRespectTo I` together
  with the ambient derived-limit owner `IsDerivedLimit Ksys K'`;
- primitive data: the ideal `I`, the inverse system `Ksys`, a stagewise derived-completeness
  witness, and a chosen derived-limit witness;
- derived API: the stronger source-facing bridge where stagewise derived completeness is produced
  from the textbook power-zero hypothesis.

Layer triage:
- `source-facing`: the power-zero formulation from the Stacks-project statement;
- `core/canonical`: derived completeness of each stage and the owner predicate `IsDerivedLimit`;
- `bridge/view`: the passage from stagewise power-zero actions to stagewise derived completeness. -/

-- Proof sketch: derived completeness with respect to `I` is defined by vanishing of the
-- localization-away objects `T(-, f)` for `f ∈ I`. For a fixed `f`, Lemma `15.92.1` realizes
-- `T(-, f)` as a derived limit of the tower with transition map `f • 𝟙`, so applying it to a
-- Milnor triangle for `Ksys` reduces the claim to the fact that zero objects are preserved under
-- sequential derived limits when every stage already satisfies the vanishing condition.
/-- Any derived limit of a sequential inverse system of `I`-derived-complete objects is again
derived complete with respect to `I`. -/
theorem isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (K' : DMod)
    (hstage :
      ∀ n : ℕ, (Ksys.obj (op n)).IsDerivedCompleteWithRespectTo I)
    (hlim : IsDerivedLimit Ksys K') :
    K'.IsDerivedCompleteWithRespectTo I := sorry

-- Proof sketch: for each stage `K_n` and each `f ∈ I`, if some power `f^e` acts by zero on
-- `K_n`, then after inverting `f` the identity of `K_n` vanishes, so `K_n` is derived complete
-- with respect to `I`. Apply the canonical stagewise derived-completeness theorem above to the
-- resulting tower.
/-- Lemma 15.92.14: if `(K_n)` is a sequential inverse system in `D(A)` such that for every
`f ∈ I` and every `n` some power `f^e` acts by zero on `K_n`, then any derived limit of `(K_n)`
is derived complete with respect to `I`. The textbook object
`R \!\varprojlim_n (K \otimes_A^{\mathbf L} K_n)` is the intended application, since its stages
inherit the same annihilation property. -/
theorem isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise_power_zero
    (I : Ideal A) (Ksys : ℕᵒᵖ ⥤ DMod) (K' : DMod)
    (hpow :
      ∀ f ∈ I, ∀ n : ℕ, ∃ e : ℕ, (f ^ e : A) • 𝟙 (Ksys.obj (op n)) = 0)
    (hlim : IsDerivedLimit Ksys K') :
    K'.IsDerivedCompleteWithRespectTo I := by
  apply isDerivedCompleteWithRespectTo_of_isDerivedLimit_of_stagewise I Ksys K'
  · intro n
    sorry
  · exact hlim

end

end CategoryTheory

/-! ### Lemma_15_92_16 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open Opposite
open scoped KoszulComplex

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.92.16:
- primary domain: derived-category realizations of the powered Koszul tower and sequential derived
  limits of its tensor image;
- sampled owner declarations:
  `koszulPowerInverseSystem`,
  `ComplexShape.embeddingDownNat.extendFunctor`,
  `DerivedCategory.Q`,
  `DerivedCategory.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing derived tower should be obtained from the chapter owner
  `koszulPowerInverseSystem` by the canonical extension-and-localization functor, rather than by a
  parallel stage alias in this file;
- primitive data: the powered Koszul inverse system from Situation `15.92.15`;
- derived API: the tensor tower and the derived-completeness statement for a chosen derived limit.

Source/core/bridge triage:
- `source-facing`: the powered Koszul tensor tower in `D(A)` and the derived-completeness theorem
  for its derived limit;
- `core/canonical`: `koszulPowerInverseSystem`, `ComplexShape.embeddingDownNat.extendFunctor`,
  `DerivedCategory.Q`, and `K.IsDerivedCompleteWithRespectTo I`;
- `bridge/view`: the canonical stage object
  `(derivedCompletionKoszulPowersDerivedInverseSystem f).obj (Opposite.op n)`. -/

/-- The inverse system in `D(A)` whose `n`th stage is the derived tensor product of the `n`th
powered Koszul complex with the fixed object `K`. This is the library-facing model of the tower
`(K \otimes_A^{\mathbf L} K_n^\bullet)_n`. -/
abbrev derivedCompletionKoszulPowerTensorDerivedInverseSystem
    (K : DMod) (f : Fin r → A) : ℕᵒᵖ ⥤ DMod :=
  derivedCompletionKoszulPowersDerivedInverseSystem f ⋙ derivedTensorProduct K

-- Proof sketch: Lemma `15.28.6` makes each generator `f i` act null-homotopically on every
-- powered Koszul stage, so each tensor stage satisfies the stagewise annihilation hypothesis from
-- Lemma `15.92.14`. Applying that lemma to the chosen derived limit gives derived completeness.
/-- Lemma 15.92.16: in Situation `15.92.15`, if `K'` is a chosen derived limit of the inverse
system obtained by applying the derived tensor functor `- \otimes_A^{\mathbf L} K` to the powered
Koszul tower `(K_n^\bullet)_n`, then `K'` is derived complete with respect to the ideal
`I = (f_1, \ldots, f_r)`. This is the library-facing form of the textbook object
`R \!\varprojlim (K \otimes_A^{\mathbf L} K_n^\bullet)`. -/
theorem derivedLimitOfKoszulPowerTensor_isDerivedCompleteWithRespectTo_spanRange
    (f : Fin r → A) (K K' : DMod)
    (hlim : IsDerivedLimit (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) K') :
    K'.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) := sorry

end

end CategoryTheory

/-! ### Lemma_15_92_17 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open Opposite
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.92.17:
- primary domain: the canonical comparison from `K` to a chosen derived limit of the powered
  Koszul tensor tower in `D(A)`;
- sampled owner declarations:
  `derivedCompletionKoszulPowerTensorDerivedInverseSystem`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.HasMilnorTriangle.WithMap`,
  `K.IsDerivedCompleteWithRespectTo I`;
- best owner abstraction: the Chapter `13` owner
  `HasMilnorTriangle.WithMap
    (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ι`, together with the
  source-facing stagewise equations asserting that a map `c : K ⟶ L` induces the canonical stage
  maps coming from the augmentation `A[0] ⟶ K_n^\bullet`;
- primitive data: the tower
  `derivedCompletionKoszulPowerTensorDerivedInverseSystem K f`, a chosen product map
  `ι : L ⟶ ∏ K_n`, a Milnor-triangle witness
  `HasMilnorTriangle.WithMap (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ι`,
  a comparison morphism `c : K ⟶ L`, and the canonical stage maps from `K` into the tensor
  stages;
- derived API: the induced `IsDerivedLimit` witness and the isomorphism criterion for `c`.

Source/core/bridge triage:
- `source-facing`: the comparison predicate below for maps from `K` to a chosen derived limit of
  the powered Koszul tensor tower;
- `core/canonical`: `derivedCompletionKoszulPowerTensorDerivedInverseSystem K f`,
  `IsDerivedLimit`, `HasMilnorTriangle.WithMap`, and
  `K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f))`;
- `bridge/view`: the explicit stagewise formula against the canonical map
  `K ⟶ K_n^\bullet \otimes_A^{\mathbf L} K`. -/

/-- The canonical map from `K` to the `n`th stage
`K_n^\bullet \otimes_A^{\mathbf L} K` of the powered Koszul tensor tower. -/
abbrev derivedCompletionKoszulPowerTensorToStage
    (K : DMod) (f : Fin r → A) (n : ℕ) :
    K ⟶ (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f).obj (op n) :=
  (singleZeroDerivedTensorIso K).inv ≫
    (derivedTensorProduct K).map
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (ModuleCat.of A A)).hom ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.extendSingleIso embeddingDownNat (ModuleCat.of A A)
              (0 : ℕ) (0 : ℤ) rfl).inv ≫
            HomologicalComplex.extendMap (koszulPowerAugmentation f n) embeddingDownNat))

/-- A morphism `c : K ⟶ L` is the canonical comparison from `K` to a chosen derived limit of the
powered Koszul tensor tower if `L` sits in the Milnor triangle of that tower and the stage
projections recover the canonical maps
`K ⟶ K_n^\bullet \otimes_A^{\mathbf L} K`. -/
def IsDerivedCompletionKoszulPowerTensorComparison
    (f : Fin r → A) (K L : DMod) (c : K ⟶ L) : Prop :=
  ∃ _ : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)),
    ∃ ι :
        L ⟶
          ∏ᶜ inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f),
      HasMilnorTriangle.WithMap
          (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) ι ∧
        ∀ n : ℕ,
          c ≫ ι ≫
              Pi.π
                (inverseSystemFamily
                  (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f))
                n =
            derivedCompletionKoszulPowerTensorToStage K f n

/-- A derived-completion comparison presents its target as a derived limit of the powered Koszul
tensor tower. -/
theorem IsDerivedCompletionKoszulPowerTensorComparison.isDerivedLimit
    {f : Fin r → A} {K L : DMod} {c : K ⟶ L}
    (hc : IsDerivedCompletionKoszulPowerTensorComparison f K L c) :
    IsDerivedLimit (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f) L := by
  rcases hc with ⟨hP, _, hι, _⟩
  let _ : HasProduct
      (inverseSystemFamily (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)) := hP
  exact ⟨hP, hι.hasMilnorTriangle (derivedCompletionKoszulPowerTensorDerivedInverseSystem K f)⟩

-- Proof sketch: if `c` is a compatible comparison to a chosen derived limit of the powered Koszul
-- tensor tower, then the target is derived complete by Lemma `15.92.16`, so an isomorphism `c`
-- forces derived completeness of `K`. Conversely, assume `K` is derived complete with respect to
-- `I = (f_1, ..., f_r)`. Filter each powered Koszul complex by stupid truncations, apply the
-- exactness of `E ↦ R lim (K ⊗_A^L E)` from Lemma `15.88.11`, and use the vanishing of the
-- negative graded pieces supplied by derived completeness to deduce that the comparison map is an
-- isomorphism.
/-- Lemma 15.92.17: in Situation `15.92.15`, for any comparison morphism
`c : K ⟶ L` formalizing the canonical map
`K \to R\!\varprojlim (K \otimes_A^{\mathbf L} K_n^\bullet)`, the object `K` is derived complete
with respect to `I = (f_1, \ldots, f_r)` if and only if `c` is an isomorphism. -/
theorem isDerivedCompleteWithRespectTo_spanRange_iff_isIso_derivedCompletionComparison
    (f : Fin r → A) {K L : DMod} (c : K ⟶ L)
    (hc : IsDerivedCompletionKoszulPowerTensorComparison f K L c) :
    K.IsDerivedCompleteWithRespectTo (Ideal.span (Set.range f)) ↔ IsIso c := sorry

end

end CategoryTheory

/-! ### Lemma_15_92_18 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

open DerivedCategory

local notation "DMod" => DerivedCategory (ModuleCat A)
variable (f : Fin r → A)

local notation "I" => Ideal.span (Set.range f)

/- Domain-style sampling for Lemma 15.92.18:
- primary domain: reflective full subcategories in the derived category, expressed through the
  canonical comparison map to the derived limit of the powered Koszul tensor tower and the
  resulting adjunction with the inclusion of derived-complete objects;
- sampled owner declarations:
  `IsDerivedCompletionKoszulPowerTensorComparison`,
  `IsDerivedCompletionKoszulPowerTensorComparison.isDerivedLimit`,
  `isDerivedCompleteWithRespectTo_spanRange_iff_isIso_derivedCompletionComparison`,
  `derivedCompleteObjectProperty`,
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.ι`,
  `Adjunction.mkOfHomEquiv`;
- best owner abstraction: the source-facing owner here is the actual adjunction `L ⊣ ι`, not the
  weaker proposition `L.IsLeftAdjoint`; the comparison predicate
  `IsDerivedCompletionKoszulPowerTensorComparison` and the isomorphism criterion from
  Lemma `15.92.17` are the bridge data used to build the canonical Hom-equivalence for that
  adjunction;
- primitive data: the functor `L`, the natural transformation `η`, and the fact that each
  `η.app K` is the canonical comparison map to the powered Koszul derived limit;
- derived API: the induced adjunction `L ⊣ ι` and its consequence `L.IsLeftAdjoint`.

Source/core/bridge triage:
- `source-facing`: the adjunction `L ⊣ ι` for the powered Koszul derived-completion functor;
- `core/canonical`: `derivedCompleteObjectProperty` and
  `IsDerivedCompletionKoszulPowerTensorComparison`, together with the canonical owner
  `Adjunction`;
- `bridge/view`: the comparison morphism `η.app K`, viewed through the owner predicate above and
  the induced Hom-equivalence into derived-complete targets. -/

-- Proof sketch: the primitive input is that `η.app K` is the canonical comparison morphism to the
-- powered Koszul derived limit, encoded by
-- `IsDerivedCompletionKoszulPowerTensorComparison`. Lemma `15.92.17` then supplies both the
-- derived-limit witness and the isomorphism criterion on already derived-complete sources. The
-- usual reflective-subcategory argument therefore shows that precomposition with `η.app K`
-- induces a Hom-equivalence on morphisms into every derived-complete object, giving the required
-- adjunction with the inclusion from Lemma `15.92.10`. The proposition `L.IsLeftAdjoint` is then
-- only the derived typeclass consequence.
private theorem eta_app_isIso_of_derivedComplete
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    IsIso (η.app E.obj) := by
  exact
    (isDerivedCompleteWithRespectTo_spanRange_iff_isIso_derivedCompletionComparison
      f (η.app E.obj) (hη E.obj)).1 E.property

private noncomputable def derivedLimitOfKoszulPowerTensorFunctorCounitApp
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    L.obj E.obj ⟶ E := by
  letI := eta_app_isIso_of_derivedComplete f L η hη E
  exact (DerivedCategory.derivedCompleteObjectProperty I).ι.preimage
    (asIso (η.app E.obj)).inv

private noncomputable def derivedLimitOfKoszulPowerTensorFunctorHomEquiv
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    (K : DMod)
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    (L.obj K ⟶ E) ≃
      (K ⟶ ((DerivedCategory.derivedCompleteObjectProperty I).ι).obj E) where
  toFun φ := η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ
  invFun ψ := L.map ψ ≫ derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη E
  left_inv φ := by
    sorry
  right_inv ψ := by
    sorry

/-- Lemma 15.92.18: in Situation `15.92.15`, let `L : D(A) ⥤ D_{comp}(A, I)` be a functor to the
full subcategory of objects derived complete with respect to `I = (f_1, \ldots, f_r)`. Assume
that, for every `K : D(A)`, the component `η.app K` of a natural transformation
`η : 𝟭 ⟶ L ⋙ ι` is the canonical comparison map
`K \to R\!\varprojlim (K \otimes_A^{\mathbf L} K_n^\bullet)` in the source-facing sense of
`IsDerivedCompletionKoszulPowerTensorComparison`. Then `L` is left adjoint to the inclusion
`D_{comp}(A, I) ⥤ D(A)` constructed in Lemma `15.92.10`, with unit given by the supplied
comparison map `η`. This is the library-facing form of the statement that the functor
`K ↦ R\!\varprojlim (K \otimes_A^{\mathbf L} K_n^\bullet)` is the reflector onto
derived-complete objects. -/
noncomputable def derivedLimitOfKoszulPowerTensorFunctorAdjunction
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K)) :
    L ⊣ (DerivedCategory.derivedCompleteObjectProperty I).ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv := derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη
      homEquiv_naturality_left_symm := by
        sorry
      homEquiv_naturality_right := by
        sorry }

/-- Derived consequence of Lemma `15.92.18`: the functor realizing the powered Koszul derived
limit is a left adjoint. The source-facing content is the adjunction
`derivedLimitOfKoszulPowerTensorFunctorAdjunction`. -/
theorem derivedLimitOfKoszulPowerTensorFunctor_isLeftAdjoint
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K)) :
    L.IsLeftAdjoint :=
  (derivedLimitOfKoszulPowerTensorFunctorAdjunction f L η hη).isLeftAdjoint

end

end CategoryTheory
