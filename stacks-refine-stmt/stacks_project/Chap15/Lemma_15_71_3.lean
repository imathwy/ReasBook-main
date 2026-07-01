import Mathlib
import stacks_project.Chap15.Definition_15_71_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian

universe u v

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M]

/- The free-factorization clause is an owner-level bridge: it depends only on the commutative-ring
owner `Module.IsIdealProjective` and the canonical equivalence between projective and free
factorizations. -/
/-- The chapter owner `Module.IsIdealProjective I M` is equivalent to requiring that, for every
`a ∈ I`, the scalar-action endomorphism `m ↦ (a : R) • m` factors through a free `R`-module. -/
theorem isIdealProjective_iff_smul_endomorphism_factorsThroughFree (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    Module.IsIdealProjective I M ↔
      ∀ a : I, (LinearMap.lsmul R M (a : R)).FactorsThroughFree := by
  refine ⟨?_, ?_⟩
  · intro hI a
    exact
      (LinearMap.factorsThroughProjective_iff_factorsThroughFree
        (LinearMap.lsmul R M (a : R))).mp (hI.factorsThroughProjective a)
  · intro hFree
    refine ⟨fun a ↦ ?_⟩
    exact
      (LinearMap.factorsThroughProjective_iff_factorsThroughFree
        (LinearMap.lsmul R M (a : R))).mpr (hFree a)

end

section

variable {R : Type u} [CommRing R]
variable {I : Ideal R}

/-
Domain-style sampling:
* primary domain: ideal-projective modules, expressed by pointwise factorization of the scalar-action
  endomorphisms `LinearMap.lsmul R M (a : R)`, together with the induced annihilation
  criterion on `Ext¹` in `ModuleCat R`;
* sampled owner declarations:
  `Module.IsIdealProjective`,
  `LinearMap.FactorsThroughProjective`,
  `LinearMap.FactorsThroughFree`,
  `LinearMap.factorsThroughProjective_iff_factorsThroughFree`,
  `Module.annihilator`,
  `Ext`;
* best owner abstraction: the source-facing projective clause is already owned by
  `Module.IsIdealProjective I M`, whose primitive data are the pointwise factorizations of the maps
  `LinearMap.lsmul R M (a : R)` through `LinearMap.FactorsThroughProjective`; the
  free-factorization clause is
  the companion bridge through `LinearMap.FactorsThroughFree`, while the Ext-annihilation clause is
  owned canonically by the annihilator containment
  `I ≤ Module.annihilator R (Ext M N 1)`;
* layer triage:
  this TFAE is `source-facing`,
  `Module.IsIdealProjective I M` is the chapter source-facing owner for clause `(1)`,
  the `LinearMap` factorization API is the canonical bridge for the scalar-action endomorphisms,
  and the `Ext¹`-annihilation clause is derived API;
* primitive data: the ideal `I`, the module object `M`, and for each `a : I` a factorization of
  the action endomorphism `LinearMap.lsmul R M (a : R)` through a projective module;
* derived API: by factoring identities on projective modules through free modules via
  `LinearMap.factorsThroughProjective_iff_factorsThroughFree`, one gets the free-factorization
  clause expressed by `LinearMap.FactorsThroughFree`, and the unpacked pointwise statement
  `∀ (N) (a : I) (e : Ext M N 1), (a : R) • e = 0`, which is equivalent to the annihilator owner
  clause.
-/

-- Proof sketch: for `(1) ↔ (2)`, if the action map `m ↦ (a : R) • m` factors through a
-- projective module `P`, factor `𝟙 P` through a free module using
-- `LinearMap.factorsThroughProjective_iff_factorsThroughFree` and compose with the given
-- pointwise factorization. For the equivalence with the `Ext¹` annihilation statement, compare
-- extension classes with short exact sequences `0 ⟶ N ⟶ P ⟶ M ⟶ 0`: the action map by `a`
-- factors through a projective module exactly when the pushforward/pullback of every such
-- extension by that map is split, i.e. when `(a : R)` acts trivially on every class in `Ext M N
-- 1`.
/-- Lemma 15.71.3: for an ideal `I` of a commutative ring `R` and an `R`-module `M`, the
following are equivalent: for every `a ∈ I`, the multiplication map `m ↦ (a : R) • m` factors
through a projective module, for every `a ∈ I` it factors through a free module, and for every
`R`-module `N` the ideal `I` is contained in the annihilator of `Ext^1_R(M, N)`. -/
theorem smul_endomorphism_tfae_factorsThroughProjective_factorsThroughFree_ext
    (I : Ideal R) (M : ModuleCat.{max u v} R) :
    List.TFAE
      [ Module.IsIdealProjective I M
      , ∀ a : I, (LinearMap.lsmul R M (a : R)).FactorsThroughFree
      , ∀ N : ModuleCat.{max u v} R, I ≤ Module.annihilator R (Ext M N 1)
      ] := sorry

/-- Companion projection of Lemma `15.71.3`: an `R`-module is `I`-projective exactly when `I`
annihilates `Ext^1_R(M, N)` for every `R`-module `N`. -/
theorem isIdealProjective_iff_ext_annihilator
    (I : Ideal R) (M : ModuleCat.{max u v} R) :
    Module.IsIdealProjective I M ↔
      ∀ N : ModuleCat.{max u v} R, I ≤ Module.annihilator R (Ext M N 1) :=
  (smul_endomorphism_tfae_factorsThroughProjective_factorsThroughFree_ext I M).out 0 2

end
