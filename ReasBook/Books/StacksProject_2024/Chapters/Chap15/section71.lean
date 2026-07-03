import Mathlib
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Maps

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_71_1 (from Chap15) -/
universe u v w

/-
Domain-style sampling:
* primary domain: factorization of linear maps through projective/free modules;
* sampled owner declarations:
  `Module.Projective`,
  `Module.projective_lifting_property`,
  `Module.Projective.iff_split`,
  `Module.Free`,
  `Module.Projective.of_free`,
  `Module.Free.of_subsingleton`;
* best owner abstraction: `Module.Projective R P` and `Module.Free R P` are the canonical owner
  properties on the intermediate module, while the source-facing public owner in this file is the
  induced predicate on a linear map;
* layer triage:
  `Module.Projective` and `Module.Free` are `core/canonical`,
  `FactorsThroughProjective` is `source-facing`,
  `FactorsThroughFree` is a `bridge/view` companion used in Lemma `15.71.1`;
* primitive data: an intermediate module `P` together with maps `M →ₗ[R] P →ₗ[R] N`;
* derived API: the tautological factorization for maps out of a projective domain, the zero-map
  factorization, and the free factorization criterion supplied by
  `factorsThroughProjective_iff_factorsThroughFree`.
-/

namespace LinearMap

section

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

open Module.Projective
open ULift

/-- A linear map factors through a projective `R`-module. -/
def FactorsThroughProjective (φ : M →ₗ[R] N) : Prop :=
  ∃ (P : Type (max u v w)) (_ : AddCommMonoid P) (_ : Module R P) (_ : Module.Projective R P)
    (f : M →ₗ[R] P) (g : P →ₗ[R] N), φ = g.comp f

/-- A linear map factors through a free `R`-module. -/
def FactorsThroughFree (φ : M →ₗ[R] N) : Prop :=
  ∃ (P : Type (max u v w)) (_ : AddCommMonoid P) (_ : Module R P) (_ : Module.Free R P)
    (f : M →ₗ[R] P) (g : P →ₗ[R] N), φ = g.comp f

/-- Any linear map with projective domain factors through a projective module. -/
theorem factorsThroughProjective_of_projective (φ : M →ₗ[R] N) [Module.Projective R M] :
    φ.FactorsThroughProjective := by
  let e : ULift.{max u w} M ≃ₗ[R] M := moduleEquiv
  let _ : Module.Projective R (ULift.{max u w} M) :=
    of_equiv' e.symm
  exact ⟨ULift.{max u w} M, inferInstance, inferInstance, inferInstance,
    e.symm.toLinearMap, φ.comp e.toLinearMap, by
      ext m
      rfl
  ⟩

/-- A free factorization is in particular a projective factorization. -/
theorem FactorsThroughFree.factorsThroughProjective {φ : M →ₗ[R] N}
    (hφ : φ.FactorsThroughFree) : φ.FactorsThroughProjective := by
  rcases hφ with ⟨F, _, _, _, f, g, rfl⟩
  exact ⟨F, inferInstance, inferInstance, inferInstance, f, g, rfl⟩

/-- The zero map factors through a projective module. -/
lemma factorsThroughProjective_zero :
    (0 : M →ₗ[R] N).FactorsThroughProjective := by
  exact ⟨PUnit, inferInstance, inferInstance, inferInstance, 0, 0, by
    ext m
    simp
  ⟩

/-- Any projective factorization may be refined to a free factorization. -/
theorem FactorsThroughProjective.factorsThroughFree {φ : M →ₗ[R] N}
    (hφ : φ.FactorsThroughProjective) : φ.FactorsThroughFree := by
  rcases hφ with ⟨P, _, _, hP, f, g, rfl⟩
  rcases iff_split.mp hP with ⟨F, _, _, _, i, s, hs⟩
  refine ⟨F, inferInstance, inferInstance, inferInstance, i.comp f, g.comp s, ?_⟩
  ext m
  exact congrArg g (LinearMap.congr_fun hs (f m)).symm

/-- Lemma 15.71.1: an `R`-linear map factors through a projective module if and only if it
factors through a free module. -/
theorem factorsThroughProjective_iff_factorsThroughFree (φ : M →ₗ[R] N) :
    φ.FactorsThroughProjective ↔ φ.FactorsThroughFree :=
  ⟨FactorsThroughProjective.factorsThroughFree, FactorsThroughFree.factorsThroughProjective⟩

end

end LinearMap

/-! ### Lemma_15_71_2 (from Chap15) -/
universe u v w

/-
Domain-style sampling:
* primary domain: factorization of linear maps through finite projective modules;
* sampled owner declarations:
  `LinearMap.FactorsThroughProjective`,
  `Module.Finite`,
  `Module.Projective`,
  `Module.FiniteProjective`;
* best owner abstraction: the canonical owner predicates on the intermediate module are
  `Module.Finite R P` and `Module.Projective R P`; the source-facing public owner in this file is
  the induced predicate on a linear map recording factorization through such an intermediate
  module, since the project-level abbreviation `Module.FiniteProjective` is restricted to the
  commutative-ring/additive-group setting and would strengthen the present semiring semantics;
* layer triage:
  `Module.Finite` and `Module.Projective` are `core/canonical`,
  `FactorsThroughFiniteProjective` is `source-facing`,
  `FactorsThroughFiniteProjective.factorsThroughProjective` is the `bridge/view` that forgets
  finiteness;
* primitive data: an intermediate module `P` together with maps `M →ₗ[R] P →ₗ[R] N`;
* derived API: forgetting finiteness yields a projective factorization, and when `M` is finite a
  projective factorization upgrades to a finite-projective one by shrinking a free factorization
  to a finite free submodule.
-/

namespace LinearMap

section

variable {R : Type u} [Semiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- A linear map factors through a finite projective `R`-module. -/
def FactorsThroughFiniteProjective (φ : M →ₗ[R] N) : Prop :=
  ∃ (P : Type (max u v w)) (_ : AddCommMonoid P) (_ : Module R P)
    (_ : Module.Finite R P) (_ : Module.Projective R P)
    (f : M →ₗ[R] P) (g : P →ₗ[R] N), φ = g.comp f

-- Proof sketch: forget the finiteness assumption on the intermediate module in the defining
-- factorization.
/-- A finite-projective factorization is in particular a projective factorization. -/
theorem FactorsThroughFiniteProjective.factorsThroughProjective {φ : M →ₗ[R] N}
    (hφ : φ.FactorsThroughFiniteProjective) : φ.FactorsThroughProjective := sorry

-- Proof sketch: by Lemma `15.71.1`, first factor `φ` through a free module. Because `M` is finite,
-- finitely many generators of `M` have images supported on only finitely many basis vectors, so
-- the factorization lands in a finite free submodule. A finite free module is finite projective.
/-- Lemma 15.71.2: if an `R`-linear map `φ : M →ₗ[R] N` factors through a projective module and
`M` is a finite `R`-module, then `φ` factors through a finite projective `R`-module. -/
theorem FactorsThroughProjective.factorsThroughFiniteProjective [Module.Finite R M]
    {φ : M →ₗ[R] N} (hφ : φ.FactorsThroughProjective) :
    φ.FactorsThroughFiniteProjective := sorry

end

end LinearMap

/-! ### Lemma_15_71_3 (from Chap15) -/
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

/-! ### Definition_15_71_4 (from Chap15) -/
universe u v

section

/- 
Domain-style sampling:
* primary domain: module-theoretic factorization of scalar-action endomorphisms through
  projective modules;
* sampled owner declarations:
  `LinearMap.FactorsThroughProjective`,
  `LinearMap.lsmul`,
  `Module.Projective`,
  `LinearMap.factorsThroughProjective_of_projective`;
* best owner abstraction: `LinearMap.FactorsThroughProjective` is the canonical owner for the
  pointwise factorization datum, while `Module.IsIdealProjective I M` is the source-facing
  module-level owner bundling that datum for every `a : I`;
* layer triage:
  `LinearMap.FactorsThroughProjective` is `core/canonical`,
  `Module.IsIdealProjective I M` is `source-facing`,
  and the projective-module instance below is derived API;
* primitive data: the ideal `I`, the module `M`, and for each `a : I` a projective factorization
  of the scalar-action endomorphism `LinearMap.lsmul R M (a : R)`;
* derived API: the instance saying projective modules are `I`-projective, obtained by factoring
  each scalar-action endomorphism through `M` itself.
-/

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

namespace Module

/-- Definition 15.71.4: an `R`-module `M` is `I`-projective if, for every `a : I`, the
scalar-action endomorphism `m ↦ (a : R) • m` factors through a projective `R`-module. -/
class IsIdealProjective (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] : Prop where
  /-- Multiplication by each element of `I` on `M` factors through a projective `R`-module. -/
  factorsThroughProjective (a : I) :
    (LinearMap.lsmul R M a).FactorsThroughProjective

/-- Projective `R`-modules are `I`-projective for every ideal `I`. -/
instance (I : Ideal R) [Projective R M] : IsIdealProjective I M where
  factorsThroughProjective a :=
    (LinearMap.lsmul R M a).factorsThroughProjective_of_projective

end Module

end

/-! ### Lemma_15_71_5 (from Chap15) -/
universe u v

/-
Domain-style sampling:
* primary domain: `I`-projective modules, expressed by projective factorizations of scalar
  multiplication maps;
* sampled owner declarations:
  `LinearMap.FactorsThroughProjective`,
  `LinearMap.lsmul`,
  `Module.Projective`,
  `Module.IsIdealProjective`;
* best owner abstraction: the module-level owner is `Module.IsIdealProjective I M`, whose
  primitive data are exactly the projective factorizations of the scalar-action endomorphisms
  `LinearMap.lsmul R M (a : R)` for `a ∈ I`;
* primitive data here: only the annihilator containment `I ≤ Module.annihilator R M`;
* derived API here: each multiplication map from `I` is zero, hence factors through the zero
  projective module.
-/

section

variable {R : Type u} [CommRing R]

section

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 15.71.5: if the ideal `I` annihilates the `R`-module `M`, then `M` is
`I`-projective. -/
theorem isIdealProjective_of_le_annihilator {I : Ideal R}
    (hM : I ≤ Module.annihilator R M) : Module.IsIdealProjective I M where
  factorsThroughProjective a := by
    have hzero : LinearMap.lsmul R M (a : R) = 0 := by
      ext m
      exact Module.mem_annihilator.mp (hM a.2) m
    simpa [hzero] using
      (LinearMap.factorsThroughProjective_zero :
        LinearMap.FactorsThroughProjective (0 : M →ₗ[R] M))

end

end

/-! ### Lemma_15_71_6 (from Chap15) -/
open CategoryTheory

universe u

/-
Domain-style sampling:
* primary domain: `I`-projective modules and their behavior in short exact sequences;
* sampled owner declarations:
  `Module.IsIdealProjective`,
  `smul_endomorphism_tfae_factorsThroughProjective_factorsThroughFree_ext`,
  `ShortComplex.ShortExact.extClass`,
  `precomp_extClass_surjective_of_projective_X₂`;
* best owner abstraction: the chapter owner is `Module.IsIdealProjective I M`, whose primitive
  data are projective factorizations of the multiplication maps `m ↦ (a : R) • m`; the canonical bridge
  for this short-exact statement is the `Ext`-annihilation formulation from Lemma `15.71.3`,
  combined with the short-exact `Ext` owner `ShortComplex.ShortExact.extClass` and its
  dimension-shifting API when the middle term is projective;
* primitive data: a short exact complex `S` together with explicit hypotheses
  `Module.IsIdealProjective I S.X₃` and `Projective S.X₂`;
* derived API: the `Ext¹`-annihilation characterization of `Module.IsIdealProjective`, obtained from
  `smul_endomorphism_tfae_factorsThroughProjective_factorsThroughFree_ext`, and the
  short-exact `Ext` comparison maps attached to `hS`;
* layer triage: this file is `source-facing`, reusing the chapter owner and the canonical
  short-exact `Ext` bridge rather than introducing a parallel `ModuleCat` wrapper.
-/

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {S : ShortComplex (ModuleCat.{u} R)}

/-- Lemma 15.71.6: in a short exact sequence `0 ⟶ K ⟶ P ⟶ M ⟶ 0` of `R`-modules, if `M` is
`I`-projective and `P` is projective, then `K` is `I`-projective. -/
theorem isIdealProjective_X₁ (hS : S.ShortExact) (hX₃ : Module.IsIdealProjective I S.X₃)
    (hX₂ : Projective S.X₂) :
    Module.IsIdealProjective I S.X₁ := sorry

end CategoryTheory.ShortComplex.ShortExact

/-! ### Lemma_15_71_7 (from Chap15) -/
universe u v

/-
Domain-style sampling:
* primary domain: duality for `I`-projective modules, expressed through factorization of scalar
  multiplication maps;
* sampled owner declarations:
  `Module.IsIdealProjective`,
  `LinearMap.FactorsThroughFiniteProjective`,
  `LinearMap.FactorsThroughProjective.factorsThroughFiniteProjective`,
  `Module.dual_projective`;
* best owner abstraction: `Module.IsIdealProjective I M` is the source-facing owner, while finite
  projective factorizations and dual projectivity are derived `core/canonical` tools;
* primitive data: for each `a : I`, the scalar-action endomorphism
  `LinearMap.lsmul R M (a : R)` factors through a projective module;
* derived API used here: because `M` is finite, each such factorization upgrades to a finite
  projective one, and dualizing that factorization gives the required projective factorization on
  `Module.Dual R M`.
-/

section

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Lemma 15.71.7: if `M` is a finite `I`-projective `R`-module, then the dual module
`Hom_R(M, R)` is `I`-projective. -/
theorem isIdealProjective_dual (hM : Module.IsIdealProjective I M) :
    Module.IsIdealProjective I (Module.Dual R M) where
  factorsThroughProjective a := by
    rcases (hM.factorsThroughProjective a).factorsThroughFiniteProjective with
      ⟨P, _instAddCommGroup, _instModule, _instFinite, _instProjective, f, g, hfg⟩
    refine ⟨Module.Dual R P, inferInstance, inferInstance, inferInstance, g.dualMap, f.dualMap, ?_⟩
    have hsmul :
        LinearMap.dualMap (LinearMap.lsmul R M (a : R)) =
          LinearMap.lsmul R (Module.Dual R M) (a : R) := by
      ext φ m
      change φ ((a : R) • m) = (a : R) • φ m
      simpa using map_smul φ (a : R) m
    have hdual := congrArg LinearMap.dualMap hfg
    simpa [hsmul, LinearMap.dualMap_comp_dualMap] using hdual

end
