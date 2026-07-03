import StacksProject_2024.Chap10.Definition_10_54_1
import StacksProject_2024.Chap10.Lemma_10_128_8_Crit_re_de_platitude_par_fibres

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing
open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
variable [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
variable [AddCommGroup M] [Module S' M] [Module.FinitePresentation S' M]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S
local notation "ClosedFiberModule" => ClosedFiber ⊗[S] RestrictScalars S S' M

/- Domain-style sampling for Lemma 10.128.9:
* primary domain: local commutative algebra of essential finite presentation and fiberwise
  flatness along a local tower `R → S → S'`;
* sampled owner declarations:
  `Algebra.EssFiniteType`,
  `Algebra.EssFinitePresentation`,
  `Ideal.Fiber`,
  `algebraMap_flat_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base`,
  `flat_over_middleRing_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base`;
* best owner abstraction: the new source-facing content is the upgrade
  `Algebra.EssFiniteType R S ⟶ Algebra.EssFinitePresentation R S` under fiberwise flatness
  hypotheses, while the closed fiber itself should live on the canonical owners
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S` and
  `ClosedFiberModule = ClosedFiber ⊗[S] RestrictScalars S S' M`.

Primitive data vs. derived API:
* primitive data: the local tower `R → S → S'`, the essential finite type hypothesis on `R → S`,
  the essential finite presentation hypothesis on `R → S'`, the finitely presented `S'`-module
  `M`, flatness of `ClosedFiberModule` over `ClosedFiber`, and flatness of `M` over `R` after
  restriction of scalars along `R → S'`;
* derived API: essential finite presentation of `R → S`, then the flatness conclusions from
  Lemma `10.128.8`.

Source/core/bridge triage:
* `source-facing`: the first theorem below, which is the extra Stacks content of Lemma `10.128.9`;
* `core/canonical`: `Algebra.EssFiniteType`, `Algebra.EssFinitePresentation`, `Ideal.Fiber`,
  `Module.Flat`, and `RingHom.Flat`;
* `bridge/view`: the quotient presentation
  `M ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S M))` of the canonical
  closed-fiber module after restricting scalars from `S'` to `S`.
-/

-- Proof sketch: write the essentially finite type local algebra `S` as a localization of a finite
-- type `R`-algebra. Choose a finitely generated subideal cutting out the same closed fiber modulo
-- `maximalIdeal R`, apply Lemma `10.128.8` to each finite-presentation approximation `R → B / J' →
-- S'`, and use Lemma `10.128.4` to show two such approximations coincide once they agree modulo the
-- maximal ideal. Hence the defining ideal is finitely generated, so `R → S` is essentially of
-- finite presentation.
/-- Lemma 10.128.9 (1): if `R → S → S'` are local ring homomorphisms, `R → S'` is essentially of
finite presentation, `R → S` is essentially of finite type, `M` is a nonzero finitely presented
`S'`-module, the canonical closed-fiber module
`ClosedFiberModule = ((maximalIdeal R).Fiber S) ⊗[S] M`, equivalently `M / 𝔪_R M`, is flat over
the canonical closed-fiber ring `ClosedFiber = (maximalIdeal R).Fiber S`, equivalently
`S / 𝔪_R S`, and `M` is flat over `R`, then `R → S` is essentially of finite presentation. -/
theorem middleRing_essFinitePresentation_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
    (hM : Nontrivial M) (hRS : Algebra.EssFiniteType R S)
    (hRS' : Algebra.EssFinitePresentation R S')
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    Algebra.EssFinitePresentation R S := sorry

-- Proof sketch: first obtain that `R → S` is essentially of finite presentation from the previous
-- theorem. Then apply Lemma `10.128.8 (1)` to the local maps `R → S → S'` and the module `M`.
/-- Under the hypotheses of Lemma 10.128.9, the local homomorphism `R → S` is flat. -/
theorem algebraMap_flat_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
    (hM : Nontrivial M) (hRS : Algebra.EssFiniteType R S)
    (hRS' : Algebra.EssFinitePresentation R S')
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    (algebraMap R S).Flat := by
  letI : Nontrivial M := hM
  letI : Module S M := Module.compHom M (algebraMap S S')
  letI : Module R M := Module.compHom M (algebraMap R S')
  letI : IsScalarTower S S' M := IsScalarTower.of_algebraMap_smul fun s m ↦ by
    rfl
  letI : IsScalarTower R S' M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
    rfl
  letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
    simpa [Module.compHom, RingHom.comp_apply] using
      (congrArg (fun f : R →+* S' ↦ f r • m) (IsScalarTower.algebraMap_eq R S S')).symm
  have hmid : Algebra.EssFinitePresentation R S :=
    middleRing_essFinitePresentation_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
      hM hRS hRS' hflat_closedFiber hflat_R
  have hflat_closedFiber' : Module.Flat ClosedFiber (ClosedFiber ⊗[S] M) := by
    simpa using hflat_closedFiber
  have hflat_R' : Module.Flat R M := by
    simpa using hflat_R
  exact
    algebraMap_flat_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base
      (RingHom.essFinitePresentation_algebraMap.mpr hmid)
      (RingHom.essFinitePresentation_algebraMap.mpr hRS')
      hflat_closedFiber'
      hflat_R'

-- Proof sketch: if `M` is nontrivial, combine the essential finite presentation statement proved
-- above with Lemma `10.128.8 (2)`. If `M` is subsingleton, then `M` is flat over every ring, so
-- the conclusion is immediate.
/-- Under the hypotheses of Lemma 10.128.9, the `S'`-module `M` is flat over `S`. -/
theorem flat_over_middleRing_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
    (hRS : Algebra.EssFiniteType R S) (hRS' : Algebra.EssFinitePresentation R S')
    (hflat_closedFiber : Module.Flat ClosedFiber ClosedFiberModule)
    (hflat_R : Module.Flat R (RestrictScalars R S' M)) :
    Module.Flat S (RestrictScalars S S' M) := by
  obtain hM | hM := subsingleton_or_nontrivial M
  · letI : Subsingleton (RestrictScalars S S' M) := by
      change Subsingleton M
      exact hM
    infer_instance
  · letI : Nontrivial M := hM
    letI : Module S M := Module.compHom M (algebraMap S S')
    letI : Module R M := Module.compHom M (algebraMap R S')
    letI : IsScalarTower S S' M := IsScalarTower.of_algebraMap_smul fun s m ↦ by
      rfl
    letI : IsScalarTower R S' M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
      rfl
    letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
      simpa [Module.compHom, RingHom.comp_apply] using
        (congrArg (fun f : R →+* S' ↦ f r • m) (IsScalarTower.algebraMap_eq R S S')).symm
    have hmid : Algebra.EssFinitePresentation R S :=
      middleRing_essFinitePresentation_of_essFiniteType_of_flat_closedFiber_and_flat_over_base
        hM hRS hRS' hflat_closedFiber hflat_R
    have hflat_closedFiber' : Module.Flat ClosedFiber (ClosedFiber ⊗[S] M) := by
      simpa using hflat_closedFiber
    have hflat_R' : Module.Flat R M := by
      simpa using hflat_R
    have hflat_S : Module.Flat S M :=
      flat_over_middleRing_of_essFinitePresentation_of_flat_closedFiber_and_flat_over_base
        (RingHom.essFinitePresentation_algebraMap.mpr hmid)
        (RingHom.essFinitePresentation_algebraMap.mpr hRS')
        hflat_closedFiber'
        hflat_R'
    simpa using hflat_S

end
