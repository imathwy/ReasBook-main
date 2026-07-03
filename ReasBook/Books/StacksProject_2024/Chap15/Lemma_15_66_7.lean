import Mathlib
import StacksProject_2024.Chap15.Lemma_15_66_6

noncomputable section

open CategoryTheory
open DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/-
Domain-style sampling for Lemma 15.66.7:
- primary domain: pseudo-coherent objects in the derived category of `A`-modules, together with
  the degree-`i` homology comparison induced by a map into a single-degree object and the
  commutative-algebra control of finite quotient modules by powers of an ideal;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.homologyToSingle`,
  `Ideal.exists_artin_rees_constant_of_exact`,
  `Submodule.annihilator_quotient`;
- best owner abstraction: the source-facing content is still the existence theorem below; the
  canonical owners are `K.IsPseudoCoherent`, the bridge morphism `DerivedCategory.homologyToSingle`
  from `15.66.6`, and the standard quotient/annihilator API used to produce an `I`-power-torsion
  finite module;
- primitive vs. derived:
  primitive data are the object `K`, the degree `i`, the ideal `I`, and the hypothesis that
  `H^i(K) / I H^i(K)` is nontrivial;
  derived API is the chosen finite `A`-module `E`, the annihilator containment `I ^ n ≤
  Module.annihilator A E`, and the morphism `α : K ⟶ E[-i]` with nonzero induced map on
  homology;
- source/core/bridge triage:
  `source-facing`: the existence theorem
    `exists_finite_ideal_pow_torsion_map_of_homology_mod_ideal_nontrivial`;
  `core/canonical`: `K.IsPseudoCoherent`, `homologyFunctor`, `singleFunctor`, and the Chapter 10
    Artin-Rees / quotient-annihilator owner API;
  `bridge/view`: `DerivedCategory.homologyToSingle`.
-/

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)
local notation "single" => DerivedCategory.singleFunctor (ModuleCat A)

-- Proof sketch: apply Lemma `15.66.6` to obtain a map from `K` to a finitely presented module in
-- degree `i` whose induced map on `H^i(K)` is injective. Use Artin-Rees for the inclusion
-- `H^i(K) ⊆ M` with respect to `I` to choose `n` with `H^i(K) ∩ I ^ n M ⊆ I H^i(K)`, pass to
-- the quotient `E = M / I ^ n M`, and compose with the quotient map; the induced map on
-- `H^i(K)` remains nonzero because `H^i(K) / I H^i(K)` is nontrivial.
/-- Lemma 15.66.7: let `A` be a Noetherian ring, let `K ∈ D(A)` be pseudo-coherent, and let `I`
be an ideal of `A`. If `H^i(K) / I H^i(K)` is nontrivial, then there exists a finite `A`-module
`E` annihilated by a power of `I` and a map `K ⟶ E[-i]` whose induced map on `H^i(K)`
is nonzero, formalized as `DerivedCategory.homologyToSingle i α ≠ 0`. -/
theorem exists_finite_ideal_pow_torsion_map_of_homology_mod_ideal_nontrivial
    (K : DMod) (hK : K.IsPseudoCoherent) (i : ℤ)
    (hHi : Nontrivial (((H i).obj K) ⧸ (I • (⊤ : Submodule A ((H i).obj K))))) :
    ∃ (E : ModuleCat A) (_ : Module.Finite A E) (n : ℕ)
      (_ : I ^ n ≤ Module.annihilator A E) (α : K ⟶ (single i).obj E),
        homologyToSingle i α ≠ 0 :=
  sorry

end

end CategoryTheory
