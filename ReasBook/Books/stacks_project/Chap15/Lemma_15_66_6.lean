import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Module.FinitePresentation
import stacks_project.Chap15.Definition_15_65_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/- Domain-style sampling for Lemma 15.66.6:
- primary domain: pseudo-coherent objects in a derived category and the degree-`i` homology map
  induced by a morphism into an object concentrated in degree `i`;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.homologyFunctor`,
  `DerivedCategory.singleFunctor`,
  `singleFunctorCompHomologyFunctorIso`;
- best owner abstraction: the source-facing content is the existence theorem below; the canonical
  owners are pseudo-coherence, homology, and single-degree objects in `DerivedCategory`. The map
  `H^i(K) ⟶ M` induced by `α : K ⟶ M[-i]` is bridge/view data obtained directly from the owner
  comparison `singleFunctorCompHomologyFunctorIso`; the reusable bridge is exposed below as
  `DerivedCategory.homologyToSingle`, and the source-facing theorem should use that bridge rather
  than repeat the raw composite;
- primitive vs. derived:
  primitive data are `K`, `M`, and the morphism
  `α : K ⟶ (DerivedCategory.singleFunctor (ModuleCat R) i).obj M`;
  derived API is the induced homology comparison `homologyToSingle i α`.
- source/core/bridge triage:
  `source-facing`: the existence theorem `exists_finitelyPresented_module_map_inducing_mono_of_isPseudoCoherent`;
  `core/canonical`: `K.IsPseudoCoherent`, `homologyFunctor`, `singleFunctor`, and
    `singleFunctorCompHomologyFunctorIso`;
  `bridge/view`: `DerivedCategory.homologyToSingle`.
-/

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single" => DerivedCategory.singleFunctor (ModuleCat R)

namespace DerivedCategory

/-- The canonical map `H^i(K) ⟶ M` induced by a morphism `K ⟶ M[-i]`, expressed via the owner
comparison `singleFunctorCompHomologyFunctorIso`. -/
abbrev homologyToSingle {K : DMod} {M : ModuleCat R} (i : ℤ)
    (α : K ⟶ (single i).obj M) : (H i).obj K ⟶ M :=
  (H i).map α ≫ ((singleFunctorCompHomologyFunctorIso (ModuleCat R) i).app M).hom

end DerivedCategory

-- Proof sketch: choose a bounded-above termwise finite-free representative of `K` from
-- pseudo-coherence. Let `M` be the cokernel of the differential `P^(i - 1) ⟶ P^i`; finite
-- presentation follows because both terms are finite free. The canonical morphism from `K` to the
-- degree-`i` single object on `M` induces the natural map `H^i(K) ⟶ M`, and on the chosen
-- representative this map is the inclusion of cocycles modulo boundaries into the cokernel, hence
-- is monic.
/-- Lemma 15.66.6: if `K` is pseudo-coherent in `D(R)`, then for every `i : ℤ` there exists a
finitely presented `R`-module `M` and a morphism from `K` to the degree-`i` single object on `M`
(equivalently, to `M[-i]`) whose induced map `H^i(K) ⟶ M`, formalized as
`DerivedCategory.homologyToSingle i α`, is injective. -/
lemma exists_finitelyPresented_module_map_inducing_mono_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) (i : ℤ) :
    ∃ (M : ModuleCat R) (_ : Module.FinitePresentation R M) (α : K ⟶ (single i).obj M),
      Mono (homologyToSingle i α) :=
  sorry

end

end CategoryTheory
