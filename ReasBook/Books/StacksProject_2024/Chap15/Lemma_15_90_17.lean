import Mathlib
import Mathlib.CategoryTheory.CommSq
import StacksProject_2024.Chap15.Lemma_15_90_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ModuleCat

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: flat base change and formal glueing for module morphisms in `ModuleCat`;
- inspected same-domain owners:
  `CategoryTheory.CommSq`,
  `ModuleCat.extendScalars`,
  `idealPowerTorsionRestrictedBaseChange_isEquivalence`,
  `formalGlueingCan`,
  `formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective`;
- best owner abstraction: the ambient owner is the canonical base-change functor
  `ModuleCat.extendScalars (algebraMap R S)`, while the comparison compatibilities themselves are
  canonically owned by `CategoryTheory.CommSq`; the source-facing content here is only the
  existence of a descended map together with its comparison isomorphism;
- primitive data: a descended `R`-module, the descended morphism, and the comparison
  isomorphism after extension of scalars;
- derived API: the kernel and cokernel comparison isomorphisms, which come from the flat formal
  glueing equivalence and should stay theorem-level output rather than primitive packaged fields.

Source/core/bridge triage:
- `source-facing`: the two existence statements below;
- `core/canonical`: `ModuleCat.extendScalars (algebraMap R S)` and the formal glueing equivalence;
- `bridge/view`: the comparison isomorphism identifying the given `S`-linear map with the base
  change of the descended `R`-linear map.
-/

-- Proof sketch: choose generators `f₁, ..., fₜ` of `I`, regard the localizations of `φ` as an
-- object of the formal glueing category from Remark `15.90.10`, and apply Proposition `15.90.16`
-- to descend `M'` and the localized comparison data to an `R`-module `M`. The induced morphism in
-- the glueing category then comes from a unique `R`-linear map `M ⟶ N`, and Lemma `15.90.3`
-- gives the kernel and cokernel comparison isomorphisms as derived consequences of the chosen
-- descent datum.
/-- Lemma 15.90.17 (1): let `φ : R → S` be a flat ring map, let `I ⊆ R` be a finitely generated
ideal such that `R ⧸ I → S ⧸ IS` is bijective, and let `M' ⟶ S ⊗[R] N` be an `S`-linear map
whose kernel and cokernel are `IS`-power torsion. Then this map descends to an `R`-linear map
`M ⟶ N` together with an isomorphism `S ⊗[R] M ≅ M'`; the kernel and cokernel comparisons after
base change are derived in the companion theorems below. -/
theorem exists_mapToBaseChangeDescent_of_kernel_cokernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S)) :
    ∃ (M : ModuleCat R) (f : M ⟶ N)
      (e : (extendScalars (algebraMap R S)).obj M ≅ M'),
      CommSq e.hom ((extendScalars (algebraMap R S)).map f) φ (𝟙 _) := sorry

/-- Companion to Lemma 15.90.17 (1): once a descent datum `M, f, e` is chosen, the kernel
comparison after base change is canonical. -/
theorem mapToBaseChangeDescent_kernelIso_of_kernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    {M : ModuleCat R} (f : M ⟶ N)
    (e : (extendScalars (algebraMap R S)).obj M ≅ M')
    (he : CommSq e.hom ((extendScalars (algebraMap R S)).map f) φ (𝟙 _)) :
    ∃ eker : (extendScalars (algebraMap R S)).obj (kernel f) ≅ kernel φ,
      CommSq
        ((extendScalars (algebraMap R S)).map (kernel.ι f))
        eker.hom
        e.hom
        (kernel.ι φ) := sorry

/-- Companion to Lemma 15.90.17 (1): once a descent datum `M, f, e` is chosen, the cokernel
comparison after base change is canonical. -/
theorem mapToBaseChangeDescent_cokernelIso_of_cokernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (N : ModuleCat R) (M' : ModuleCat S)
    (φ : M' ⟶ (extendScalars (algebraMap R S)).obj N)
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    {M : ModuleCat R} (f : M ⟶ N)
    (e : (extendScalars (algebraMap R S)).obj M ≅ M')
    (he : CommSq e.hom ((extendScalars (algebraMap R S)).map f) φ (𝟙 _)) :
    ∃ ecoker : (extendScalars (algebraMap R S)).obj (cokernel f) ≅ cokernel φ,
      CommSq
        ((extendScalars (algebraMap R S)).map (cokernel.π f))
        (𝟙 _)
        ecoker.hom
        (cokernel.π φ) := sorry

-- Proof sketch: localize the map `S ⊗[R] M ⟶ N'` at generators of `I`; each localization is an
-- isomorphism because the kernel and cokernel are `IS`-power torsion. Using the same formal
-- glueing equivalence as in part `(1)`, descend the target `N'` and the localized comparison maps
-- to an `R`-module `N`, and obtain the descended map `M ⟶ N`. Lemma `15.90.3` then identifies the
-- base-changed kernels and cokernels from the chosen descent datum.
/-- Lemma 15.90.17 (2): under the same hypotheses on `R → S` and `I`, let `S ⊗[R] M ⟶ N'` be an
`S`-linear map whose kernel and cokernel are `IS`-power torsion. Then this map descends to an
`R`-linear map `M ⟶ N` together with an isomorphism `S ⊗[R] N ≅ N'`; the kernel and cokernel
comparisons after base change are derived in the companion theorems below. -/
theorem exists_mapFromBaseChangeDescent_of_kernel_cokernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S)) :
    ∃ (N : ModuleCat R) (f : M ⟶ N)
      (e : (extendScalars (algebraMap R S)).obj N ≅ N'),
      CommSq ((extendScalars (algebraMap R S)).map f) φ e.hom (𝟙 _) := sorry

/-- Companion to Lemma 15.90.17 (2): once a descent datum `N, f, e` is chosen, the kernel
comparison after base change is canonical. -/
theorem mapFromBaseChangeDescent_kernelIso_of_kernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hker : Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (kernel φ : ModuleCat S))
    {N : ModuleCat R} (f : M ⟶ N)
    (e : (extendScalars (algebraMap R S)).obj N ≅ N')
    (he : CommSq ((extendScalars (algebraMap R S)).map f) φ e.hom (𝟙 _)) :
    ∃ eker : (extendScalars (algebraMap R S)).obj (kernel f) ≅ kernel φ,
      CommSq
        ((extendScalars (algebraMap R S)).map (kernel.ι f))
        eker.hom
        (𝟙 _)
        (kernel.ι φ) := sorry

/-- Companion to Lemma 15.90.17 (2): once a descent datum `N, f, e` is chosen, the cokernel
comparison after base change is canonical. -/
theorem mapFromBaseChangeDescent_cokernelIso_of_cokernel_idealPowerTorsion
    (I : Ideal R) (hflat : (algebraMap R S).Flat) (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))
    (M : ModuleCat R) (N' : ModuleCat S)
    (φ : (extendScalars (algebraMap R S)).obj M ⟶ N')
    (hcoker :
      Module.IsIdealPowerTorsion (Ideal.map (algebraMap R S) I) (cokernel φ : ModuleCat S))
    {N : ModuleCat R} (f : M ⟶ N)
    (e : (extendScalars (algebraMap R S)).obj N ≅ N')
    (he : CommSq ((extendScalars (algebraMap R S)).map f) φ e.hom (𝟙 _)) :
    ∃ ecoker : (extendScalars (algebraMap R S)).obj (cokernel f) ≅ cokernel φ,
      CommSq
        ((extendScalars (algebraMap R S)).map (cokernel.π f))
        e.hom
        ecoker.hom
        (cokernel.π φ) := sorry

end
