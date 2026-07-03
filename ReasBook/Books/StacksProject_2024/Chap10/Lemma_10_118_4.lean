import stacks_project.Chap10.«10_118_3_2»
import stacks_project.Chap10.Lemma_10_5_3
import Mathlib.Algebra.Category.ModuleCat.Localization
import Mathlib.RingTheory.LocalProperties.Projective

-- Declarations for this item will be appended below by the statement pipeline.

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
