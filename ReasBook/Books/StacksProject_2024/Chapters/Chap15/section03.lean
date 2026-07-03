import Mathlib
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Jacobson.Ring

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_3_1 (from Chap15) -/
universe u v w

namespace Module

section

variable (R : Type u) [Ring R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable (N : Type w) [AddCommGroup N] [Module R N]

/- Domain-style sampling:
- primary domain: module isomorphisms after adjoining finite free summands;
- sampled owner declarations: `Module.Free`, `Module.Finite`, `LinearEquiv.prodCongr`, and
  `Module.Free.pi`;
- best owner abstraction: the source-facing owners here are `StablyIsomorphic` and `StablyFree`,
  while finite generation is already canonically owned by `Module.Finite`;
- primitive vs. derived: stable isomorphism and stable freeness are primitive content of this
  item, but "finite stably free" is only the conjunction of two existing owners and should stay a
  downstream combination rather than a separate wrapper class.
-/

/-- Definition 15.3.1: two `R`-modules are stably isomorphic if there exist `m, n ≥ 0` such that
`M ⊕ R^{\oplus m}` and `N ⊕ R^{\oplus n}` are isomorphic as `R`-modules, modeled in Lean by the
product modules `M × (Fin m → R)` and `N × (Fin n → R)`. -/
def StablyIsomorphic : Prop :=
  ∃ m n : ℕ, Nonempty ((M × (Fin m → R)) ≃ₗ[R] (N × (Fin n → R)))

/-- An `R`-module is stably free if it is stably isomorphic to a free module. -/
class StablyFree : Prop where
  exists_free :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F) (_ : Module.Free R F),
      StablyIsomorphic R M F

/-- Stable isomorphism is reflexive. -/
-- Proof sketch: take `m = n = 0`; then the added finite free summands are trivial, and the
-- resulting linear equivalence is induced by the identity equivalence on `M`.
theorem stablyIsomorphic_refl : StablyIsomorphic R M M :=
  ⟨0, 0, ⟨LinearEquiv.refl R (M × (Fin 0 → R))⟩⟩

/-- Every free module is stably free. -/
instance stablyFree_of_free [Module.Free R M] : StablyFree R M where
  exists_free := by
    refine ⟨ULift.{max u v} M, inferInstance, inferInstance, inferInstance, ?_⟩
    refine ⟨0, 0, ⟨?_⟩⟩
    exact LinearEquiv.prodCongr ULift.moduleEquiv.symm (LinearEquiv.refl R (Fin 0 → R))

end

end Module

open CategoryTheory

section

variable (R : Type u) [Ring R]

/-- The object property of finite stably free `R`-modules in `ModuleCat R`. -/
abbrev finiteStablyFreeModuleProperty : ObjectProperty (ModuleCat R) :=
  fun M ↦ Module.Finite R M ∧ Module.StablyFree R M

end

/-! ### Lemma_15_3_2 (from Chap15) -/
open CategoryTheory

universe u

section

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat R)}

/- Domain-style sampling:
* primary domain: short exact sequences of `R`-modules, projective splittings, and stable
  freeness;
* sampled owner declarations:
  `ShortComplex.ShortExact.splittingOfProjective`,
  `ModuleCat.free_shortExact`,
  `Module.Projective.of_free`,
  `Module.StablyFree`;
* best owner abstraction: the ambient owner is the short exact complex `S : ShortComplex
  (ModuleCat R)` with `hS : S.ShortExact`;
* primitive vs. derived:
  the primitive end-term data are the canonical owners `Module.Finite` and `Module.StablyFree`,
  while "finite stably free" is only their conjunction and should remain derived API rather than a
  separate wrapper; projectivity of a stably free end term is supporting bridge data rather than
  primitive public input for the closure lemmas that only use stable freeness.

Source/core/bridge triage:
* `source-facing`: the three closure statements from Stacks Lemma 15.3.2;
* `core/canonical`: `hS.splittingOfProjective` and the owner properties `Module.Finite` /
  `Module.StablyFree`;
* `bridge/view`: the identification of the middle term with a split product coming from the
  canonical splitting. -/

-- Proof sketch: use the canonical splitting `hS.splittingOfProjective`, so `S.X₂` identifies with
-- `S.X₁ × S.X₃`. Stabilize the two end terms by finite free summands, use that products preserve
-- finite/free modules, and apply `ModuleCat.free_shortExact` to obtain a finite free stabilization
-- of `S.X₂`.
/-- Lemma 15.3.2 (1): in a short exact sequence `0 ⟶ P' ⟶ P ⟶ P'' ⟶ 0` of finite projective
`R`-modules, if `P'` and `P''` are finite stably free, then `P` is finite stably free. -/
theorem finiteStablyFree_X₂_of_shortExact (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.StablyFree R S.X₁]
    [Module.Finite R S.X₃] [Module.StablyFree R S.X₃] :
    Module.Finite R S.X₂ ∧ Module.StablyFree R S.X₂ := sorry

-- Proof sketch: via `hS.splittingOfProjective`, the canonical decomposition
-- `S.X₂ ≃ₗ[R] S.X₁ × S.X₃` exhibits `S.X₃` as a direct summand of `S.X₂`; transport finite stable
-- freeness across that split-product description.
/-- Lemma 15.3.2 (2): in a short exact sequence `0 ⟶ P' ⟶ P ⟶ P'' ⟶ 0` of finite projective
`R`-modules, if `P'` and `P` are finite stably free, then `P''` is finite stably free. -/
theorem finiteStablyFree_X₃_of_shortExact (hS : S.ShortExact)
    [Module.Projective R S.X₃]
    [Module.Finite R S.X₁] [Module.StablyFree R S.X₁]
    [Module.Finite R S.X₂] [Module.StablyFree R S.X₂] :
    Module.Finite R S.X₃ ∧ Module.StablyFree R S.X₃ := sorry

-- Proof sketch: use the same canonical splitting of `hS`; under
-- `S.X₂ ≃ₗ[R] S.X₁ × S.X₃`, the module `S.X₁` is the complementary direct summand to `S.X₃`, so
-- finite stable freeness descends from the split-product description.
/-- Lemma 15.3.2 (3): in a short exact sequence `0 ⟶ P' ⟶ P ⟶ P'' ⟶ 0` of finite projective
`R`-modules, if `P` and `P''` are finite stably free, then `P'` is finite stably free. -/
theorem finiteStablyFree_X₁_of_shortExact (hS : S.ShortExact)
    [Module.Finite R S.X₂] [Module.StablyFree R S.X₂]
    [Module.Finite R S.X₃] [Module.StablyFree R S.X₃] :
    Module.Finite R S.X₁ ∧ Module.StablyFree R S.X₁ := sorry

end CategoryTheory.ShortComplex

end

/-! ### Lemma_15_3_3 (from Chap15) -/
universe u v

section

variable {R : Type u} [Ring R]
variable {I : Ideal R} [I.IsTwoSided]
variable {E : Type v} [AddCommGroup E] [Module (R ⧸ I) E]

/- Domain-style sampling:
- primary domain: Jacobson-radical lifting of finite stably free modules across a quotient ring;
- sampled owner declarations of the same kind:
  `Module.StablyFree`,
  `Module.Finite`,
  `Ring.jacobson`,
  `ModuleCat.finiteStablyFree_X₂_of_shortExact`;
- best owner abstraction: this item is source-facing existence data built from the canonical owners
  `Module.StablyFree` and `Module.Finite`, together with the standard quotient module
  `M ⧸ (I • (⊤ : Submodule R M))`;
- primitive vs. derived: the primitive witness is the lifted `R`-module together with the quotient
  equivalence to `E`, while finiteness and stable freeness are derived owner properties of that
  witness and should not be existentially packaged as separate primitive fields.

Layer classification:
- `source-facing`: the lifting statement below;
- `core/canonical`: `Module.StablyFree`, `Module.Finite`, and the Jacobson-radical containment
  `I ≤ Ring.jacobson R`;
- `bridge/view`: the quotient module `M ⧸ (I • (⊤ : Submodule R M))` over `R ⧸ I`.
-/

-- Proof sketch: choose a stable trivialization
-- `E × (Fin n → R ⧸ I) ≃ₗ[R ⧸ I] (Fin m → R ⧸ I)`. Lift the associated projection and section to
-- `R`-linear maps between `Fin m → R` and `Fin n → R`, use the Jacobson-radical hypothesis to make
-- the lifted endomorphism of `Fin n → R` invertible, and identify the kernel of the lifted
-- projection as a finite stably free `R`-module whose quotient modulo `I` recovers `E`.
/-- Lemma 15.3.3: if `I` is contained in the Jacobson radical of `R`, then every finite stably
free `R ⧸ I`-module lifts to a finite stably free `R`-module. -/
theorem exists_finiteStablyFree_lift_of_le_ring_jacobson
    [Module.Finite (R ⧸ I) E] [Module.StablyFree (R ⧸ I) E] (hI : I ≤ Ring.jacobson R) :
    ∃ (M : Type v) (_ : AddCommGroup M) (_ : Module R M)
      (e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] E),
      Module.Finite R M ∧ Module.StablyFree R M := sorry

end

/-! ### Lemma_15_3_4 (from Chap15) -/
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {I : Ideal R}
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]

omit [IsNoetherianRing R] [Module.Finite R M] [Module.Flat R M] in
private theorem descendProjectiveOfProjectiveCompletionTensor
    [Module.FaithfullyFlat R (AdicCompletion I R)]
    (h : Module.Projective (AdicCompletion I R) ((AdicCompletion I R) ⊗[R] M)) :
    Module.Projective R M :=
  @Module.Projective.of_projective_tensorProduct_of_faithfullyFlat
    R _ M _ _ (AdicCompletion I R) _ _ inferInstance h

/- Domain triage:
- primary domain: projective descent for finite flat modules across Jacobson-radical thickenings,
  organized through adic completion and faithfully flat descent;
- sampled owner declarations of the same kind:
  `Module.Projective`,
  `Module.Projective.of_projective_tensorProduct_of_faithfullyFlat`,
  `adicCompletion_algebraMap_faithfullyFlat_of_le_jacobson`,
  `completionMap_has_section_of_flat_of_projective_quotient`;
- best owner abstraction: the canonical predicate `Module.Projective R M`, with the completion map
  and quotient-projective lifting results treated as bridge API rather than parallel public owners;
- primitive data: the Noetherian commutative ring `R`, the ideal `I`, the finite flat `R`-module
  `M`, and projectivity of the reduction `M ⧸ (I • ⊤)` over `R ⧸ I`;
- derived API: projectivity of the completed base change of `M`, then projectivity of `M` itself
  by faithfully flat descent along the `I`-adic completion.

Layer classification:
- `source-facing`: the Jacobson-radical lifting criterion from the text;
- `core/canonical`: `Module.Projective R M`;
- `bridge/view`: the quotient module `M ⧸ (I • ⊤)` over `R ⧸ I` and the completed surjection
  supplied by `completionMap_has_section_of_flat_of_projective_quotient`.
-/

-- Proof sketch: choose a surjection `P → M` from a finite free module. Lemma `10.97.9` upgrades
-- the projectivity of `M / IM` to a section of the induced surjection on `I`-adic completions, so
-- `AdicCompletion I M` is projective over `AdicCompletion I R`. The canonical tensor/completion
-- equivalence `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` identifies this with the
-- completed base change `(AdicCompletion I R) ⊗[R] M`, and faithfully flat descent along the
-- completion map finishes the proof via
-- `Module.Projective.of_projective_tensorProduct_of_faithfullyFlat`.
/-- Lemma 15.3.4: if `R` is Noetherian, `I` is contained in the Jacobson radical of `R`, `M` is
a finite flat `R`-module, and the quotient `M / IM` is projective over `R ⧸ I`, then `M` is
projective over `R`; since finiteness is already an ambient hypothesis, this is exactly the
finite-projective conclusion of the textbook statement. -/
theorem projective_of_projective_quotient_of_le_ring_jacobson
    (hI : I ≤ Ring.jacobson R)
    (hquot : Module.Projective (R ⧸ I) (M ⧸ (I • ⊤ : Submodule R M))) :
    Module.Projective R M := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  letI : Module.FaithfullyFlat R (AdicCompletion I R) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp
      (adicCompletion_algebraMap_faithfullyFlat_of_le_jacobson I hI)
  letI : Module.Free (AdicCompletion I R) (AdicCompletion I R) :=
    Module.Free.self (AdicCompletion I R)
  letI : Module.Projective (AdicCompletion I R) (AdicCompletion I R) := Module.Projective.of_free
  letI : Module.Projective R (Fin n → R) := Module.Projective.of_free
  letI : Module.Projective (AdicCompletion I R) ((AdicCompletion I R) ⊗[R] (Fin n → R)) :=
    Module.Projective.tensorProduct
  letI : Module.Projective (AdicCompletion I R) (AdicCompletion I (Fin n → R)) :=
    Module.Projective.of_equiv'
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I (Fin n → R))
  obtain ⟨s, hs⟩ :=
    completionMap_has_section_of_flat_of_projective_quotient I π hπ hquot
  letI : Module.Projective (AdicCompletion I R) (AdicCompletion I M) :=
    Module.Projective.of_split s (AdicCompletion.map I π) hs
  have htensor : Module.Projective (AdicCompletion I R) ((AdicCompletion I R) ⊗[R] M) :=
    Module.Projective.of_equiv'
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).symm
  exact descendProjectiveOfProjectiveCompletionTensor htensor

end

/-! ### Lemma_15_3_5 (from Chap15) -/
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
