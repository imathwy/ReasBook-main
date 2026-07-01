import Mathlib
import stacks_project.Chap15.«15_60_1_1»
import stacks_project.Chap15.Lemma_15_82_10

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [Algebra.FiniteType R A]
variable {ι : Type*} [Finite ι]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.16:
- primary domain: relative pseudo-coherence in `D(A)` and its locality on a finite principal-open
  cover of `Spec A`;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `isMPseudoCoherent_iff_localizationAway_unitIdeal`,
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`;
- best owner abstraction: this item is `source-facing`, while the core/canonical owners are the
  relative pseudo-coherence predicates `K.IsMPseudoCoherentRelativeTo R m` and
  `K.IsPseudoCoherentRelativeTo R` on derived `A`-complexes;
- primitive vs. derived:
  primitive data are the finite family `f : ι → A`, the unit-ideal hypothesis, and the localized
  derived objects `K ⊗[A]^L[Localization.Away (f i)]`;
  derived API is the relative pseudo-coherence conclusion on `K`, so the file should not keep a
  parallel coordinate-level `Fin r` interface or explicit functor application as the public
  surface;
- source/core/bridge triage:
  `source-facing`: the local-global equivalences below;
  `core/canonical`: the owner predicates `IsMPseudoCoherentRelativeTo` and
    `IsPseudoCoherentRelativeTo`;
  `bridge/view`: the localized derived scalar-extension objects
    `K ⊗[A]^L[Localization.Away (f i)]`.
-/

-- Proof sketch: for `←`, restrict the complex along any surjective polynomial presentation
-- `P → A`; the hypotheses identify each localization over `A_{f i}` with the corresponding
-- localization of the restricted `P`-complex, and Lemma `15.65.14` descends `m`-pseudo-coherence
-- from the principal-open cover because the images of the `f i` still generate the unit ideal.
-- For `→`, localize a relative `m`-pseudo-coherent approximation; this is the relative
-- localization statement proved earlier in the chapter.
/-- Lemma 15.82.16 (1): for a finite type ring map `R → A`, a derived `A`-complex `K^•`, an
integer `m`, and finitely many elements `f i : A` generating the unit ideal, `K^•` is
`m`-pseudo-coherent relative to `R` if and only if each principal localization
`K^• \otimes_A^{\mathbf L} A_{f i}` is `m`-pseudo-coherent relative to `R`. -/
theorem isMPseudoCoherentRelativeTo_iff_localizationAway_unitIdeal
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤) (K : DModA) (m : ℤ) :
    (∀ i, (K ⊗[A]^L[Localization.Away (f i)]).IsMPseudoCoherentRelativeTo R m) ↔
      K.IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: combine part `(1)` for every integer `m` with the definitions of relative
-- pseudo-coherence and ordinary pseudo-coherence as `m`-pseudo-coherence in all degrees.
/-- Lemma 15.82.16 (2): under the same hypotheses, `K^•` is pseudo-coherent relative to `R` if
and only if each principal localization `K^• \otimes_A^{\mathbf L} A_{f i}` is pseudo-coherent
relative to `R`. -/
theorem isPseudoCoherentRelativeTo_iff_localizationAway_unitIdeal
    (f : ι → A) (hunit : Ideal.span (Set.range f) = ⊤) (K : DModA) :
    (∀ i, (K ⊗[A]^L[Localization.Away (f i)]).IsPseudoCoherentRelativeTo R) ↔
      K.IsPseudoCoherentRelativeTo R := by
  constructor
  · intro hK m
    exact (isMPseudoCoherentRelativeTo_iff_localizationAway_unitIdeal f hunit K m).mp
      (fun i ↦ hK i m)
  · intro hK i m
    exact ((isMPseudoCoherentRelativeTo_iff_localizationAway_unitIdeal f hunit K m).mpr
      (hK m)) i

end

end CategoryTheory
