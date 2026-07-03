import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Jacobson.Ring
import stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import stacks_project.Chap10.Lemma_10_82_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {P' : Type w} [AddCommGroup P'] [Module R P']
variable [Module.Finite R P]
variable [Module.Finite R P'] [Module.Projective R P']
variable (I : Ideal R)

local notation "IP" => I • (⊤ : Submodule R P)
local notation "IP'" => I • (⊤ : Submodule R P')

/- Domain-style sampling:
- primary domain: finite projective modules over a commutative ring and comparison modulo an
  ideal in the Jacobson radical;
- sampled owner declarations of the same kind:
  `LinearMap.quotientMapByIdeal`,
  `surjective_of_quotientMap_surjective_of_le_ring_jacobson`,
  `Module.projective_lifting_property`,
  `OrzechProperty.bijective_of_surjective_endomorphism`,
  `LinearEquiv.ofBijective`;
- best owner abstraction: the reduced comparison map `φ.quotientMapByIdeal I`, together with the
  chapter-level Nakayama owner
  `surjective_of_quotientMap_surjective_of_le_ring_jacobson`; `LinearEquiv` is the canonical owner
  for a lifted bijection;
- primitive data: for the first theorem, the ideal `I`, the Jacobson-radical containment `hI`,
  the map `φ`, finiteness of `P`, and finiteness plus projectivity of `P'`; for the second
  theorem, add projectivity of `P` and the quotient `(R ⧸ I)`-linear equivalence `e`;
- derived API: bijectivity of `φ` and the lifted `LinearEquiv`.

Layer classification:
- `source-facing`: the Jacobson-radical lifting statements below;
- `core/canonical`: `LinearMap.quotientMapByIdeal`,
  `surjective_of_quotientMap_surjective_of_le_ring_jacobson`,
  `Module.projective_lifting_property`, `OrzechProperty.bijective_of_surjective_endomorphism`, and
  `LinearEquiv.ofBijective`;
- `bridge/view`: the quotient comparison equation for the lifted equivalence.
-/

-- Proof sketch: use projectivity of `P'` to lift an inverse to the induced quotient map, obtaining
-- `ψ : P' →ₗ[R] P`. The composites `ψ ∘ₗ φ` and `φ ∘ₗ ψ` are the identity modulo `I`, so the
-- chapter owner `surjective_of_quotientMap_surjective_of_le_ring_jacobson` makes them surjective;
-- the canonical finite-module endomorphism criterion
-- `OrzechProperty.bijective_of_surjective_endomorphism` then upgrades these surjective
-- endomorphisms to automorphisms, which forces `φ` to be bijective.
/-- Lemma 15.3.5: if `I` is contained in the Jacobson radical of `R`, `P` is finite, `P'` is
finite projective, and the induced map `P / IP → P' / IP'` is bijective, then `φ` is bijective. -/
theorem bijective_of_bijective_mod_jacobson_of_finite_projective
    (hI : I ≤ Ring.jacobson R) (φ : P →ₗ[R] P')
    (hφ : Function.Bijective (φ.quotientMapByIdeal I)) :
    Function.Bijective φ := sorry

variable [Module.Projective R P]

-- Proof sketch: choose a linear lift `φ : P →ₗ[R] P'` of the underlying `R`-linear quotient
-- equivalence `e.restrictScalars R` using the projectivity owner
-- `Module.projective_lifting_property`, apply
-- `bijective_of_bijective_mod_jacobson_of_finite_projective` to obtain a bijective lift, and then
-- package that lift by the canonical owner `LinearEquiv.ofBijective`.
/-- An `(R ⧸ I)`-linear quotient equivalence between finite projective `R`-modules over a
Jacobson-radical ideal lifts to an `R`-linear equivalence. -/
theorem exists_lift_of_quotient_equiv_of_finite_projective
    (hI : I ≤ Ring.jacobson R) (e : (P ⧸ IP) ≃ₗ[R ⧸ I] (P' ⧸ IP')) :
    ∃ φ : P ≃ₗ[R] P',
      (φ : P →ₗ[R] P').quotientMapByIdeal I = e.restrictScalars R := sorry

end
