import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_118_1 (from Chap10) -/
universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

open GenericFlatness

/- Domain-style sampling:
* primary domain: generic freeness for finite type algebras and finite modules over a domain;
* sampled owner declarations:
  `Module.FinitePresentation.exists_free_localizedModule_powers`,
  `Module.freeLocus`,
  `LocalizationCondition`,
  `exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType`;
* core/canonical owner in this chapter: `LocalizationCondition R S M f`;
* primitive vs derived API: the localization parameter `f` is primitive, while freeness of
  `LocalizedModule.Away (algebraMap R S f) M` is derived owner API via
  `LocalizationCondition.free_module`;
* layer triage: this file is `bridge/view`, keeping the source-facing freeness consequence while
  reusing the stronger localization owner from `Lemma_10_118_3`.
-/
-- Proof sketch: apply the stronger finite-type generic-flatness theorem `Lemma_10_118_3`, which
-- already produces a nonzero `f` with `LocalizationCondition R S M f`; the present statement is
-- just the `free_module` projection from that owner.
/-- Lemma 10.118.1: if `R` is a domain, `S` is a finite type `R`-algebra, and `M` is a finite
`S`-module, then some nonzero localization `M_f` is a free `R_f`-module. -/
theorem exists_nonzero_localization_away_module_free
    [IsDomain R] [Algebra.FiniteType R S] [Module.Finite S M] :
    ∃ f : R, f ≠ 0 ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away (algebraMap R S f) M) := by
  obtain ⟨f, hf, hcond⟩ : ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f :=
    exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType
  exact ⟨f, hf, hcond.free_module⟩

end

/-! ### Lemma_10_118_2 (from Chap10) -/
/- Lemma 10.118.2 lives in the generic-freeness domain for finite type algebras and finite modules
over a domain. Sampled chapter/project owners in this domain are
`GenericFlatness.LocalizationCondition`,
`exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType`, and the chapter-level
freeness consequence `exists_nonzero_localization_away_module_free`. The best owner abstraction for
this item is the latter theorem: finite presentation of `S` and `M` only supplies the derived
instances `[Algebra.FiniteType R S]` and `[Module.Finite S M]`, so the stronger-hypothesis version
in the source is a `bridge/view` recall of the existing canonical chapter theorem rather than a new
owner. Primitive data are the rings/algebra/module; the freeness conclusion is derived API. -/
recall exists_nonzero_localization_away_module_free

/-! ### Lemma_10_118_3 (from Chap10) -/
universe u v w

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]

open GenericFlatness

/- Domain-style sampling:
* primary domain: generic freeness / generic flatness for finite type algebras and finite modules
  over a domain;
* sampled owner declarations:
  `GenericFlatness.LocalizationCondition`,
  `GenericFlatness.goodLocus`,
  `Module.FinitePresentation.exists_free_localizedModule_powers`,
  `Module.freeLocus`;
* best owner abstraction in this chapter: `LocalizationCondition R S M f`;
* primitive data: the rings/algebra/module and the localization parameter `f`;
* derived API: finite presentation and freeness of `S_f` and `M_f`;
* layer triage: this file is `source-facing`, asserting existence of a localization satisfying the
  chapter owner condition.
-/
-- Proof sketch: choose a finite presentation of `S` as a quotient of a polynomial ring over `R`
-- and first treat that polynomial case by replacing `M` with a finitely presented approximation
-- having the same generic fiber. Apply Lemma `10.118.2` to obtain a nonzero `f` making that
-- approximation free over `R_f`; then identify it with `M_f`. Finite presentation of `S_f` and
-- `M_f` follows from finite type after localizing away the same `f`.
/-- Lemma 10.118.3: if `R` is a domain, `R → S` is of finite type, and `M` is a finite `S`-module,
then there exists a nonzero `f ∈ R` such that `S_f` and `M_f` are free as `R_f`-modules, `S_f` is
a finitely presented `R_f`-algebra, and `M_f` is a finitely presented `S_f`-module. -/
lemma exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType :
    ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f := sorry

end

/-! ### Lemma_10_118_4 (from Chap10) -/
universe u v

open PrimeSpectrum GenericFlatness

/-
Domain-style sampling:
* primary domain: generic flatness on `Spec R`, with the short exact sequence treated through the
  chapter's canonical owner `ShortComplex (ModuleCat S)`.
* inspected owner declarations:
  `GenericFlatness.goodLocus`,
  `CategoryTheory.ShortComplex.ShortExact.flat_X₂`,
  `Module.FinitePresentation.of_exact`,
  `ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`.
* best owner abstraction: a short exact complex `T : ShortComplex (ModuleCat S)`.
* layer triage: the short exact complex is `core/canonical`; the textbook inclusion of good loci
  remains `source-facing`.
* primitive data: `T` and `hT : T.ShortExact`.
* derived API: the inclusion
  `goodLocus R S T.X₁ ∩ goodLocus R S T.X₃ ⊆ goodLocus R S T.X₂`.
-/

namespace CategoryTheory
namespace ShortComplex
namespace ShortExact

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {T : ShortComplex (ModuleCat.{max u v} S)}

/-- Helper for Lemma 10.118.4: in an exact sequence of modules over a commutative ring, if the
outer terms are free, then the middle term is free. -/
lemma free_middle_of_exact_of_free_ends
    {A : Type*} [CommRing A]
    {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] [AddCommGroup M₃] [Module A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    [Module.Free A M₁] [Module.Free A M₃] :
    Module.Free A M₂ := by
  -- Split the surjection using projectivity of the free quotient.
  obtain ⟨s, hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg)
  -- Then identify the middle term with the product of the two free endpoint modules.
  obtain ⟨e, _, _⟩ := ((hfg.split_tfae hf hg).out 0 2 rfl rfl).mp ⟨s, hs⟩
  exact Module.Free.of_equiv' inferInstance e.symm

/-- Helper for Lemma 10.118.4: `R_(fg)` carries the canonical `R_f`-algebra structure. -/
noncomputable instance product_away_algebra_over_left (f g : R) :
    Algebra (Localization.Away f) (Localization.Away (f * g)) :=
  (IsLocalization.Away.awayToAwayRight (S := Localization.Away f) f g).toAlgebra

/-- Helper for Lemma 10.118.4: `S_(fg)` carries the canonical `S_f`-algebra structure. -/
noncomputable instance target_product_away_algebra_over_left (f g : R) :
    Algebra (Localization.Away (algebraMap R S f))
      (Localization.Away (algebraMap R S (f * g))) :=
  by
    -- The target localization is still away from the product image `(fg)`, hence away from
    -- `(algebraMap R S f) * (algebraMap R S g)` after rewriting `map_mul`.
    have : IsLocalization.Away ((algebraMap R S f) * (algebraMap R S g))
        (Localization.Away (algebraMap R S (f * g))) := by
      simpa [map_mul] using
        (inferInstance :
          IsLocalization.Away (algebraMap R S (f * g))
            (Localization.Away (algebraMap R S (f * g))))
    exact (IsLocalization.Away.awayToAwayRight (S := Localization.Away (algebraMap R S f))
      (algebraMap R S f) (algebraMap R S g)).toAlgebra

/-- Helper for Lemma 10.118.4: after localizing away from `f`, multiplying the second parameter by
`f` only changes it by an associate. -/
lemma away_mul_associated_right (f g : R) :
    Associated (algebraMap R (Localization.Away f) (f * g))
      (algebraMap R (Localization.Away f) g) := by
  -- Rewrite `(fg) / 1` as `(f / 1) * (g / 1)` and cancel the unit `f / 1`.
  rw [map_mul]
  simpa [mul_comm] using
    (associated_mul_unit_left
      (algebraMap R (Localization.Away f) g)
      (algebraMap R (Localization.Away f) f)
      (IsLocalization.Away.algebraMap_isUnit (R := R) (S := Localization.Away f) (x := f)))

/-- Helper for Lemma 10.118.4: localizing the already-free algebra `S_f` once more at `g / 1`
keeps it free over `(R_f)_g`. -/
lemma iterated_away_free_algebra_over_base
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R) (hf : LocalizationCondition R S M f) :
    Module.Free (Localization.Away (algebraMap R (Localization.Away f) g))
      (Localization.Away
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g))) := by
  -- TODO: identify the iterated target ring as an `R_f`-localized module via the explicit
  -- `awayMapₐ` scalar tower `R_f → (R_f)_g → (S_f)_g`, then apply
  -- `Module.free_of_isLocalizedModule` to `hf.free_algebra`.
  sorry

/-- Helper for Lemma 10.118.4: localizing the already-free module `M_f` once more at `g / 1`
keeps it free over `(R_f)_g`. -/
lemma iterated_away_free_module_over_base
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R) (hf : LocalizationCondition R S M f) :
    Module.Free (Localization.Away (algebraMap R (Localization.Away f) g))
      (LocalizedModule.Away
        (algebraMap (Localization.Away f) (Localization.Away (algebraMap R S f))
          (algebraMap R (Localization.Away f) g))
        (LocalizedModule.Away (algebraMap R S f) M)) := by
  -- TODO: construct the restricted-scalars localization map
  -- `M_f → ((M_f) localized at g / 1)` and prove it is `IsLocalizedModule (.powers (g / 1))`
  -- before applying `Module.free_of_isLocalizedModule` to `hf.free_module`.
  sorry

/-- Helper for Lemma 10.118.4: once `(10.118.3.1)` holds at `f`, its finite-presentation data
survives one more localization in the already-localized `f`-world. The remaining freeness fields
still need the module-side transport from `R_f` to `(R_f)_g`. -/
lemma localizationCondition_map_away_self
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R) (hf : LocalizationCondition R S M f) :
    LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g) := by
  -- TODO: after the two explicit freeness transports are available, package the four fields
  -- separately. The remaining nontrivial part is the algebra/module finite-presentation transport
  -- from `R_f` to `(R_f)_g`, not the exactness or short-exact argument later in the file.
  sorry

/-- Helper for Lemma 10.118.4: package the direct-versus-iterated comparison for the product case.
The ring-side associate rewrite is already isolated in `away_mul_associated_right`; what remains is
to transport the module-side freeness and finite-presentation data through the canonical
localization equivalences. -/
lemma localizationCondition_of_map_away_product
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R)
    (hfg :
      LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g)) :
    LocalizationCondition R S M (f * g) := by
  -- Route correction: compare the direct `(fg)`-objects with the iterated `g / 1`-localizations
  -- only at the whole-condition level, instead of rebuilding separate bridge lemmas first.
  -- TODO: use `away_mul_associated_right` together with the canonical algebra and module
  -- equivalences between direct and iterated away-localizations, then transport the four fields of
  -- `hfg` across those equivalences.
  sorry

lemma localizationCondition_mul_right
    {M : Type*} [AddCommGroup M] [Module S M]
    (f g : R) (hf : LocalizationCondition R S M f) :
    LocalizationCondition R S M (f * g) := by
  -- First localize the already-good `f`-world once more at `g / 1`, then identify that iterated
  -- witness with the direct `(fg)`-localization.
  exact localizationCondition_of_map_away_product (R := R) (S := S) (M := M) f g <|
    localizationCondition_map_away_self (R := R) (S := S) (M := M) f g hf

/-- Helper for Lemma 10.118.4: at a fixed localization parameter, exactness plus the endpoint
generic-flatness conditions imply the middle generic-flatness condition. -/
lemma localizationCondition_middle_of_shortExact
    (f : R) (hT : T.ShortExact)
    (h₁ : LocalizationCondition R S T.X₁ f) (h₃ : LocalizationCondition R S T.X₃ f) :
    LocalizationCondition R S T.X₂ f := by
  let S₀ : Submonoid S := Submonoid.powers (algebraMap R S f)
  let f₁ : T.X₁ →ₗ[S] LocalizedModule S₀ T.X₁ := LocalizedModule.mkLinearMap S₀ T.X₁
  let f₂ : T.X₂ →ₗ[S] LocalizedModule S₀ T.X₂ := LocalizedModule.mkLinearMap S₀ T.X₂
  let f₃ : T.X₃ →ₗ[S] LocalizedModule S₀ T.X₃ := LocalizedModule.mkLinearMap S₀ T.X₃
  letI : Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) T.X₁) := h₁.finitePresentation_module
  letI : Module.FinitePresentation (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) T.X₃) := h₃.finitePresentation_module
  letI : Module.Free (Localization.Away f)
      (LocalizedModule.Away (algebraMap R S f) T.X₁) := h₁.free_module
  letI : Module.Free (Localization.Away f)
      (LocalizedModule.Away (algebraMap R S f) T.X₃) := h₃.free_module
  -- Localizing a short exact sequence preserves exactness and the endpoint injective/surjective
  -- maps.
  have hExact : Function.Exact T.f.hom T.g.hom := by
    simpa using (moduleCat_exact_iff_function_exact T).mp hT.exact
  have hLocExact :
      Function.Exact (IsLocalizedModule.map S₀ f₁ f₂ T.f.hom)
        (IsLocalizedModule.map S₀ f₂ f₃ T.g.hom) := by
    simpa [f₁, f₂, f₃] using IsLocalizedModule.map_exact S₀ f₁ f₂ f₃ T.f.hom T.g.hom hExact
  have hLocInj : Function.Injective (IsLocalizedModule.map S₀ f₁ f₂ T.f.hom) := by
    simpa [f₁, f₂, f₃] using LocalizedModule.map_injective S₀ T.f.hom hT.moduleCat_injective_f
  have hLocSurj : Function.Surjective (IsLocalizedModule.map S₀ f₂ f₃ T.g.hom) := by
    simpa [f₁, f₂, f₃] using LocalizedModule.map_surjective S₀ T.g.hom hT.moduleCat_surjective_g
  let mapf :
      LocalizedModule.Away (algebraMap R S f) T.X₁ →ₗ[Localization.Away (algebraMap R S f)]
        LocalizedModule.Away (algebraMap R S f) T.X₂ := by
    simpa [S₀] using
      (LocalizedModule.map S₀ T.f.hom :
        LocalizedModule S₀ T.X₁ →ₗ[Localization S₀] LocalizedModule S₀ T.X₂)
  let mapg :
      LocalizedModule.Away (algebraMap R S f) T.X₂ →ₗ[Localization.Away (algebraMap R S f)]
        LocalizedModule.Away (algebraMap R S f) T.X₃ := by
    simpa [S₀] using
      (LocalizedModule.map S₀ T.g.hom :
        LocalizedModule S₀ T.X₂ →ₗ[Localization S₀] LocalizedModule S₀ T.X₃)
  have hLocExactAway : Function.Exact mapf mapg := by
    simpa [mapf, mapg, S₀] using hLocExact
  have hLocInjAway : Function.Injective mapf := by
    simpa [mapf, S₀] using hLocInj
  have hLocSurjAway : Function.Surjective mapg := by
    simpa [mapg, S₀] using hLocSurj
  -- Finite presentation of the localized middle term comes from Lemma 10.5.3.
  have hfp₂ :
      Module.FinitePresentation (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) T.X₂) := by
    exact Module.finitePresentation_of_exact mapf mapg hLocInjAway hLocSurjAway hLocExactAway
  let locf :
      LocalizedModule.Away (algebraMap R S f) T.X₁ →ₗ[Localization.Away f]
        LocalizedModule.Away (algebraMap R S f) T.X₂ :=
    { toFun := mapf
      map_add' := mapf.map_add
      map_smul' := fun r x ↦ by
        change mapf ((algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R S f)) r) • x) =
          (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R S f)) r) • mapf x
        simpa using mapf.map_smulₛₗ ((algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R S f)) r)) x }
  let locg :
      LocalizedModule.Away (algebraMap R S f) T.X₂ →ₗ[Localization.Away f]
        LocalizedModule.Away (algebraMap R S f) T.X₃ :=
    { toFun := mapg
      map_add' := mapg.map_add
      map_smul' := fun r x ↦ by
        change mapg ((algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R S f)) r) • x) =
          (algebraMap (Localization.Away f)
            (Localization.Away (algebraMap R S f)) r) • mapg x
        simpa using mapg.map_smulₛₗ ((algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R S f)) r)) x }
  have hLocExact' : Function.Exact locf locg := by
    simpa [locf, locg] using hLocExactAway
  have hLocInj' : Function.Injective locf := by
    simpa [locf] using hLocInjAway
  have hLocSurj' : Function.Surjective locg := by
    simpa [locg] using hLocSurjAway
  -- The localized middle term is free because the localized short exact sequence splits.
  have hfree₂ :
      Module.Free (Localization.Away f)
        (LocalizedModule.Away (algebraMap R S f) T.X₂) :=
    free_middle_of_exact_of_free_ends locf locg hLocInj' hLocSurj' hLocExact'
  exact
    { finitePresentation_algebra := h₁.finitePresentation_algebra
      finitePresentation_module := hfp₂
      free_algebra := h₁.free_algebra
      free_module := hfree₂ }

-- Proof sketch: let `u` lie in both good loci. Choose basic opens around `u` coming from elements
-- `f1, f3 : R` witnessing the generic-flatness condition for `T.X₁` and `T.X₃`, and replace them by
-- the common refinement `f1 * f3`. Localizing the short exact sequence at that element preserves
-- exactness; then the endpoint assumptions imply the middle localized module is finitely presented
-- by Lemma `10.5.3`, and freeness is preserved under extensions. Hence the same basic open is
-- contained in the good locus of `T.X₂`.
/-- Lemma 10.118.4: for a short exact sequence `0 → M1 → M2 → M3 → 0` of `S`-modules, the
intersection of the generic-flatness good loci of the outer terms is contained in the good locus
of the middle term. -/
theorem goodLocus_inter_subset_of_shortExact
    (hT : T.ShortExact) :
    goodLocus R S T.X₁ ∩ goodLocus R S T.X₃ ⊆ goodLocus R S T.X₂ := by
  intro u hu
  rw [goodLocus_eq_iUnion] at hu ⊢
  rcases hu with ⟨hu₁, hu₃⟩
  rcases Set.mem_iUnion.mp hu₁ with ⟨f₁, hf₁⟩
  rcases Set.mem_iUnion.mp hu₃ with ⟨f₃, hf₃⟩
  -- Refine the two basic-open witnesses to their common product witness.
  refine Set.mem_iUnion.mpr ?_
  refine ⟨⟨f₁.1 * f₃.1, ?_⟩, ?_⟩
  · have h₁' : LocalizationCondition R S T.X₁ (f₁.1 * f₃.1) :=
      localizationCondition_mul_right (R := R) (S := S) (M := T.X₁) f₁.1 f₃.1 f₁.2
    have h₃' : LocalizationCondition R S T.X₃ (f₁.1 * f₃.1) := by
      simpa [mul_comm] using
        (localizationCondition_mul_right (R := R) (S := S) (M := T.X₃) f₃.1 f₁.1 f₃.2)
    exact localizationCondition_middle_of_shortExact (R := R) (S := S) (T := T)
      (f₁.1 * f₃.1) hT h₁' h₃'
  · -- The point remains in the refined basic open because `D(f₁f₃) = D(f₁) ∩ D(f₃)`.
    rw [basicOpen_mul]
    exact ⟨hf₁, hf₃⟩

end

end ShortExact
end ShortComplex
end CategoryTheory

/-! ### Lemma_10_118_5 (from Chap10) -/
open PrimeSpectrum
open scoped PrimeSpectrum

noncomputable section

universe u v w

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/- Domain triage:
* primary domain: generic-flatness loci on prime spectra under localization away from one element;
* source-facing owner: `goodLocus R S M` from `10_118_3_2`;
* core/canonical bridge: `primeSpectrum_localizationAway_homeomorph_D f` and its pointwise
  description via `PrimeSpectrum.comap`;
* bridge/view target of this file: transport `goodLocus` across the canonical identification
  `Spec(R_f) ≃ D(f)`, with the restriction to `D(f)` expressed canonically as a subtype preimage
  rather than a separate wrapper set. -/

/-- Helper for Lemma 10.118.5: membership in `goodLocus` is equivalent to the existence of a
single witness element avoiding the given prime. -/
lemma mem_goodLocus_iff (p : PrimeSpectrum R) :
    p ∈ goodLocus R S M ↔ ∃ g : R, LocalizationCondition R S M g ∧ g ∉ p.asIdeal := by
  -- Unfold the defining union and rewrite basic-open membership into non-membership in the prime.
  rw [goodLocus_eq_iUnion]
  constructor
  · intro hp
    rcases Set.mem_iUnion.mp hp with ⟨g, hg⟩
    exact ⟨g.1, g.2, (PrimeSpectrum.mem_basicOpen g.1 p).mp hg⟩
  · rintro ⟨g, hgcond, hg⟩
    refine Set.mem_iUnion.mpr ?_
    exact ⟨⟨g, hgcond⟩, (PrimeSpectrum.mem_basicOpen g p).mpr hg⟩

/-- Helper for Lemma 10.118.5: the canonical map `R_f → R_(fg)` is compatible with the original
`R`-algebra structures, so `R_(fg)` sits in a scalar tower over `R_f`. -/
lemma away_mul_isScalarTower (f g : R) :
    letI : Algebra (Localization.Away f) (Localization.Away (f * g)) :=
      (IsLocalization.Away.awayToAwayRight
        (S := Localization.Away f) (P := Localization.Away (f * g)) f g).toAlgebra
    IsScalarTower R (Localization.Away f) (Localization.Away (f * g)) := by
  letI : Algebra (Localization.Away f) (Localization.Away (f * g)) :=
    (IsLocalization.Away.awayToAwayRight
      (S := Localization.Away f) (P := Localization.Away (f * g)) f g).toAlgebra
  -- The comparison map `R_f → R_(fg)` still agrees with the original structure map from `R`.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  symm
  simpa using
    (IsLocalization.Away.awayToAwayRight_eq
      (S := Localization.Away f) (P := Localization.Away (f * g)) (x := f) (y := g) x)

/-- Helper for Lemma 10.118.5: inside `R_f`, the elements `(fg) / 1` and `g / 1` are associated
because `f / 1` is a unit. -/
lemma away_mul_associated_right (f g : R) :
    Associated (algebraMap R (Localization.Away f) (f * g))
      (algebraMap R (Localization.Away f) g) := by
  -- After rewriting `(fg) / 1` as `(f / 1) * (g / 1)`, cancel the unit `f / 1`.
  rw [map_mul]
  simpa [mul_comm] using
    (associated_mul_unit_left
      (algebraMap R (Localization.Away f) g)
      (algebraMap R (Localization.Away f) f)
      (IsLocalization.Away.algebraMap_isUnit (R := R) (S := Localization.Away f) (x := f)))

/-- Helper for Lemma 10.118.5: the iterated localization `(R_f)_(g / 1)` carries the composed
`R`-algebra structure, and this agrees with the evident scalar tower through `R_f`. -/
lemma away_map_isScalarTower (f g : R) :
    letI : Algebra R (Localization.Away (algebraMap R (Localization.Away f) g)) :=
      ((algebraMap (Localization.Away f)
          (Localization.Away (algebraMap R (Localization.Away f) g))).comp
        (algebraMap R (Localization.Away f))).toAlgebra
    IsScalarTower R (Localization.Away f)
      (Localization.Away (algebraMap R (Localization.Away f) g)) := by
  -- TODO: pin down the composed `R`-algebra structure on `(R_f)_(g / 1)` so that the resulting
  -- `SMul` fields agree definitionally with the scalar tower expected by `IsLocalization`.
  sorry

/-- Helper for Lemma 10.118.5: both `R_(fg)` and `(R_f)_(g / 1)` localize `R` away from `fg`, so
they are canonically isomorphic as `R`-algebras. -/
noncomputable def away_mul_base_algEquiv (f g : R) :
    Localization.Away (f * g) ≃ₐ[R]
      Localization.Away (algebraMap R (Localization.Away f) g) := by
  -- TODO: after `away_map_isScalarTower` is available with the canonical `SMul` data, register
  -- `(R_f)_(g / 1)` as an away-localization of `R` at `fg` via `Away.mul_of_associated`, and then
  -- use `IsLocalization.algEquiv` to compare it with `R_(fg)`.
  sorry

/-- Helper for Lemma 10.118.5: a witness for `U(R → S, M)` remains a witness after localizing the
whole setup away from `f`. -/
lemma localizationCondition_map_away (f g : R) (hg : LocalizationCondition R S M g) :
    LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) (algebraMap R (Localization.Away f) g) := by
  -- Route correction: the remaining gap is no longer the base-ring tower.
  -- TODO: first build the explicit comparison
  -- `Localization.Away (f * g) ≃ₐ[Localization.Away f] Localization.Away (algebraMap R (Localization.Away f) g)`
  -- using `away_mul_isScalarTower` and `away_mul_associated_right`; then transport the codomain
  -- algebra and localized module across the corresponding `AlgEquiv` and `LinearEquiv`.
  sorry

/-- Helper for Lemma 10.118.5: a witness in the localized pair can be cleared to a witness in the
original pair by multiplying by the numerator returned by `IsLocalization.Away.sec`. -/
lemma localizationCondition_of_localized_witness (f : R) (u : Localization.Away f)
    (hu :
      LocalizationCondition (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) u) :
    LocalizationCondition R S M (f * (IsLocalization.Away.sec f u).1) := by
  -- Route correction: the denominator-clearing step should reuse the same comparison package as
  -- `localizationCondition_map_away`, with `g` replaced by `(IsLocalization.Away.sec f u).1` and
  -- the localized basic open replaced by `u`.
  -- TODO: use `away_of_sec_fst` to identify `Localization.Away u` with
  -- `Localization.Away (f * (IsLocalization.Away.sec f u).1)`, then transport the codomain ring
  -- and localized module through the induced `AlgEquiv` and `LinearEquiv`.
  sorry

/-- Lemma 10.118.5: pulling back `U(R → S, M)` along `Spec(R_f) → Spec(R)` gives the good locus of
the localized pair `(R_f → S_f, M_f)`. Equivalently, under the identification
`Spec(R_f) ≃ D(f)`, this is the equality `U(R_f → S_f, M_f) = D(f) ∩ U(R → S, M)`. -/
-- Proof sketch: membership in the localized good locus means there is `g ∈ R_f` such that
-- `(10.118.3.1)` holds after localizing once more at `g`. Write `g = a / f^n`, replace it by an
-- element of `R` giving the same doubly localized rings and modules, and use that the image of
-- `Spec(R_f) → Spec(R)` is `D(f)`.
theorem goodLocus_localizationAway_eq_preimage (f : R) :
    goodLocus (Localization.Away f) (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) =
    PrimeSpectrum.comap (algebraMap R (Localization.Away f)) ⁻¹'
      goodLocus R S M := by
  ext p
  -- Rewrite both sides as existence of a single witness avoiding the relevant prime.
  rw [mem_goodLocus_iff, Set.mem_preimage, mem_goodLocus_iff]
  constructor
  · rintro ⟨u, hucond, hu⟩
    let a : R := (IsLocalization.Away.sec f u).1
    refine ⟨f * a, localizationCondition_of_localized_witness (R := R) (S := S) (M := M) f u hucond, ?_⟩
    -- Clearing the denominator multiplies by `f`, and `f` is already invertible in `R_f`.
    intro hfa_mem
    have hf_not_mem : algebraMap R (Localization.Away f) f ∉ p.asIdeal := by
      intro hf_mem
      exact p.2.ne_top <| Ideal.eq_top_of_isUnit_mem _ hf_mem
        (IsLocalization.Away.algebraMap_isUnit (R := R) (S := Localization.Away f) (x := f))
    have ha_mem : algebraMap R (Localization.Away f) a ∈ p.asIdeal := by
      have hprod_mem : algebraMap R (Localization.Away f) (f * a) ∈ p.asIdeal := by
        simpa using hfa_mem
      have hmul_mem :
          algebraMap R (Localization.Away f) f * algebraMap R (Localization.Away f) a ∈ p.asIdeal := by
        simpa [map_mul] using hprod_mem
      exact (p.2.mem_or_mem hmul_mem).resolve_left hf_not_mem
    have hu_mem : u ∈ p.asIdeal := by
      exact (Ideal.mem_iff_of_associated
        (IsLocalization.Away.associated_sec_fst (R := R) (S := Localization.Away f) (x := f) u)).mp ha_mem
    exact hu hu_mem
  · rintro ⟨g, hgcond, hg⟩
    refine ⟨algebraMap R (Localization.Away f) g,
      localizationCondition_map_away (R := R) (S := S) (M := M) f g hgcond, ?_⟩
    simpa using hg

/-- Under the canonical homeomorphism `Spec(R_f) ≃ D(f)`, the localized good locus is the
restriction of `U(R → S, M)` to the basic open `D(f)`. -/
-- Proof sketch: rewrite `goodLocus_localizationAway_eq_preimage` through
-- `primeSpectrum_localizationAway_homeomorph_D f`, using the explicit description of that
-- homeomorphism on points. Express the restriction to `D(f)` as the preimage of `goodLocus R S M`
-- under the subtype coercion `D(f) → Spec(R)`.
theorem goodLocus_localizationAway_eq_D_restrict (f : R) :
    Set.image (primeSpectrum_localizationAway_homeomorph_D f)
      (goodLocus (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M)) =
    ((↑) : D(f) → PrimeSpectrum R) ⁻¹' goodLocus R S M := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    -- Transport membership across theorem 1, then read the homeomorphism pointwise.
    have hp' : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) p ∈ goodLocus R S M := by
      simpa [goodLocus_localizationAway_eq_preimage (R := R) (S := S) (M := M) (f := f)] using hp
    simpa [primeSpectrum_localizationAway_homeomorph_D_apply] using hp'
  · intro hx
    let p : PrimeSpectrum (Localization.Away f) := (primeSpectrum_localizationAway_homeomorph_D f).symm x
    -- Pull the point back along the homeomorphism and apply theorem 1 in the reverse direction.
    have hp_eq : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) p = x.1 := by
      change (primeSpectrum_localizationAway_homeomorph_D f p).1 = x.1
      simpa [p] using congrArg Subtype.val
        ((primeSpectrum_localizationAway_homeomorph_D f).apply_symm_apply x)
    have hp' : PrimeSpectrum.comap (algebraMap R (Localization.Away f)) p ∈ goodLocus R S M := by
      simpa [hp_eq] using hx
    have hp : p ∈ goodLocus (Localization.Away f) (Localization.Away (algebraMap R S f))
        (LocalizedModule.Away (algebraMap R S f) M) := by
      simpa [goodLocus_localizationAway_eq_preimage (R := R) (S := S) (M := M) (f := f)] using hp'
    refine ⟨p, hp, ?_⟩
    simpa [p] using (primeSpectrum_localizationAway_homeomorph_D f).apply_symm_apply x

end GenericFlatness

end

/-! ### Lemma_10_118_6 (from Chap10) -/
open PrimeSpectrum

universe u v w x

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M]

namespace GenericFlatness

/-- Helper for Lemma 10.118.6: the good locus is open because it is a union of basic opens. -/
lemma isOpen_goodLocus_aux :
    IsOpen (goodLocus R S M) := by
  -- Expand the defining union and use that every basic open in `Spec(R)` is open.
  rw [goodLocus_eq_iUnion]
  exact isOpen_iUnion fun g => PrimeSpectrum.isOpen_basicOpen

-- Proof sketch: by Lemma `10.118.5`, for each `i` the localized good locus on `Spec(R_{f i})`
-- identifies with the restriction of `goodLocus R S M` to `D(f i)`. Thus the hypothesis is that
-- the complement of `goodLocus R S M` is nowhere dense on every member of a dense standard-open
-- cover. Apply Topology, Lemma `5.21.4` to that complement and use density of the union of the
-- cover members.
/-- Lemma 10.118.6: if a dense union of basic opens `⋃ i, D(fᵢ)` has the property that the
restriction of `U(R → S, M)` to each `D(fᵢ)` is dense, then `U(R → S, M)` is dense in
`Spec(R)`. -/
theorem dense_goodLocus_of_dense_standardOpen_cover
    {ι : Type x} (f : ι → R)
    (hcover : Dense (⋃ i, (basicOpen (f i) : Set (PrimeSpectrum R))))
    (hdense :
      ∀ i, Dense (((↑) : PrimeSpectrum.basicOpen (f i) → PrimeSpectrum R) ⁻¹' goodLocus R S M)) :
    Dense (goodLocus R S M) := by
  let V : Set (PrimeSpectrum R) := ⋃ i, (basicOpen (f i) : Set (PrimeSpectrum R))
  have hDenseOnV : Dense (((↑) : V → PrimeSpectrum R) ⁻¹' goodLocus R S M) := by
    rw [dense_iff_inter_open]
    intro W hWopen hWnonempty
    rcases hWnonempty with ⟨x, hxW⟩
    rcases Set.mem_iUnion.mp x.2 with ⟨i, hxi⟩
    let includeToV : PrimeSpectrum.basicOpen (f i) → Subtype V :=
      fun y ↦ ⟨y.1, Set.mem_iUnion.mpr ⟨i, y.2⟩⟩
    have hIncludeToV : Continuous includeToV := by
      -- The chosen basic open sits inside the ambient union `V`, so its inclusion is continuous.
      exact Continuous.subtype_mk
        (p := V)
        (f := fun y : PrimeSpectrum.basicOpen (f i) ↦ (y : PrimeSpectrum R))
        continuous_subtype_val
        (fun y ↦ Set.mem_iUnion.mpr ⟨i, y.2⟩)
    let Wi : Set (PrimeSpectrum.basicOpen (f i)) := includeToV ⁻¹' W
    have hWi_open : IsOpen Wi := hWopen.preimage hIncludeToV
    have hxWi : (⟨x.1, hxi⟩ : PrimeSpectrum.basicOpen (f i)) ∈ Wi := by
      simpa [Wi, includeToV] using hxW
    have hWi_nonempty : Wi.Nonempty := ⟨⟨x.1, hxi⟩, hxWi⟩
    rcases (hdense i).inter_open_nonempty Wi hWi_open hWi_nonempty with ⟨y, hyW, hyGood⟩
    refine ⟨includeToV y, ?_⟩
    constructor
    · simpa [Wi, includeToV] using hyW
    · simpa [includeToV] using hyGood
  have hV_subset_closure :
      V ⊆ closure (goodLocus R S M) := by
    rw [Subtype.dense_iff] at hDenseOnV
    intro x hxV
    have hxImage :
        x ∈ closure
          (((↑) : V → PrimeSpectrum R) '' (((↑) : V → PrimeSpectrum R) ⁻¹' goodLocus R S M)) :=
      hDenseOnV hxV
    -- The image of the restricted good locus in the subtype is contained in the ambient good locus.
    exact closure_mono
      (fun y hy ↦ by
        rcases hy with ⟨z, hz, rfl⟩
        exact hz)
      hxImage
  -- Density on the dense open union `V` forces density in the whole spectrum.
  intro x
  simpa [closure_closure] using closure_mono hV_subset_closure (hcover x)

end GenericFlatness

end
