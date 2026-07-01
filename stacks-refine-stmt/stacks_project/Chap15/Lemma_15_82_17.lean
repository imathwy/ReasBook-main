import Mathlib
import stacks_project.Chap15.Lemma_15_65_17
import stacks_project.Chap15.Lemma_15_82_10
import stacks_project.Chap15.Lemma_15_82_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [IsNoetherianRing R]
variable [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "BoundedAbove" => (t.minus : ObjectProperty DModA)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.17:
- primary domain: relative pseudo-coherence for derived `A`-complexes and `A`-modules over a
  finite type algebra `A` above a Noetherian base `R`;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `isMPseudoCoherent_iff_boundedAbove_and_homology_finite_ge`;
- best owner abstraction: the chapter owner predicates
  `DerivedCategory.IsMPseudoCoherentRelativeTo` and `DerivedCategory.IsPseudoCoherentRelativeTo`;
- primitive vs. derived:
  primitive data are the relative pseudo-coherence owners from `15.82.10` and the absolute
  Noetherian criterion from `15.65.17`;
  derived API is the finite-homology characterization in this file, obtained presentationwise over
  surjective polynomial presentations;
- source/core/bridge triage:
  `source-facing`: the three equivalences of Lemma `15.82.17`;
  `core/canonical`: `DerivedCategory.IsMPseudoCoherentRelativeTo`,
    `DerivedCategory.IsPseudoCoherentRelativeTo`, and `ModuleCat.IsPseudoCoherentRelativeTo`;
  `bridge/view`: restriction of scalars along a surjective polynomial presentation.

This file is source-facing. The later ring-map class `RingHom.IsPseudoCoherentRingMap` is a
downstream bridge from `15.83`, so it must not be used as the main route here. -/

-- Proof sketch: fix a surjective polynomial presentation `α : R[x₁, ..., xₙ] → A`. The ring
-- `MvPolynomial (Fin n) R` is Noetherian, so Lemma `15.65.17 (1)` applies to the restricted
-- complex. Its bounded-above condition and finite-homology condition are exactly the intrinsic
-- conditions on `K`, because restriction of scalars along `α` preserves the underlying cohomology
-- objects and finite generation ascends and descends across the surjection.
/-- Lemma 15.82.17 (1): for a finite type `R`-algebra `A` over a Noetherian ring `R`, a derived
`A`-complex is `m`-pseudo-coherent relative to `R` exactly when it lies in `D^-(A)` and its
cohomology modules `H^i` are finite `A`-modules for all `i ≥ m`. -/
theorem isMPseudoCoherentRelativeTo_iff_boundedAbove_and_homology_finite_ge
    (K : DModA) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔
      BoundedAbove K ∧
        ∀ i : ℤ, m ≤ i → Module.Finite A ((H i).obj K) := by
  sorry

-- Proof sketch: combine part `(1)` for all integers `m` with the definition of relative
-- pseudo-coherence as relative `m`-pseudo-coherence in every degree.
/-- Lemma 15.82.17 (2): for a finite type `R`-algebra `A` over a Noetherian ring `R`, a derived
`A`-complex is pseudo-coherent relative to `R` exactly when it lies in `D^-(A)` and all of its
cohomology modules are finite `A`-modules. -/
theorem isPseudoCoherentRelativeTo_iff_boundedAbove_and_homology_finite
    (K : DModA) :
    K.IsPseudoCoherentRelativeTo R ↔
      BoundedAbove K ∧
        ∀ i : ℤ, Module.Finite A ((H i).obj K) := by
  sorry

end

section

variable {R A : Type u} [CommRing R] [IsNoetherianRing R]
variable [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
variable {M : Type u} [AddCommGroup M] [Module A M]

-- Proof sketch: choose one surjective polynomial presentation `P → A`. If `M` is relatively
-- pseudo-coherent, then in particular it is `0`-pseudo-coherent relative to `R`, hence finite by
-- Lemma `15.82.7 (1)`. Conversely, if `M` is finite over `A`, then for every surjective
-- polynomial presentation `P → A` the
-- restricted `P`-module is finite because `A` is finite over `P`; applying Lemma `15.65.17 (3)`
-- over `P` yields pseudo-coherence presentationwise.
/-- Lemma 15.82.17 (3): for a finite type `R`-algebra `A` over a Noetherian ring `R`, an
`A`-module is pseudo-coherent relative to `R` exactly when it is finite over `A`. -/
theorem _root_.Module.isPseudoCoherentRelativeTo_iff_finite
    : Module.IsPseudoCoherentRelativeTo R A M ↔ Module.Finite A M := by
  constructor
  · intro hM
    have h0 : Module.IsMPseudoCoherentRelativeTo R A M 0 := hM 0
    have hzero :
        Module.IsMPseudoCoherentRelativeTo R A M 0 ↔ Module.Finite A M :=
      Module.isZeroPseudoCoherentRelativeTo_iff_finite
    exact hzero.mp h0
  · intro hM
    refine Module.isPseudoCoherentRelativeTo_iff_hasInfiniteFiniteFreeResolutionRelativeTo.2 ?_
    intro n
    dsimp
    intro α hα
    let P := MvPolynomial (Fin n) R
    letI : Module P M := Module.compHom M α.toRingHom
    letI : Algebra P A := α.toAlgebra
    letI : IsScalarTower P A M := IsScalarTower.of_compHom P A M
    letI : Module.Finite P A := by
      simpa [AlgHom.Finite, RingHom.Finite] using AlgHom.Finite.of_surjective α hα
    letI : Module.Finite P M := Module.Finite.trans A M
    have hMP : (ModuleCat.of P M).IsPseudoCoherent :=
      (Module.isPseudoCoherent_iff_finite).2 inferInstance
    exact
      (moduleCat_isPseudoCoherent_iff_exists_infiniteFiniteFreeResolution
        (ModuleCat.of P M)).1 hMP

end

end CategoryTheory
