import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_15_40_1 (from Chap15) -/
open Algebra
open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [IsLocalRing A] [IsNoetherianRing A]

/- Domain-style sampling for Theorem 15.40.1:
- primary domain: local commutative algebra of Noetherian local `k`-algebras, relating adic
  formal smoothness, geometric regularity, and the cotangent-theoretic residue-field criteria;
- sampled owner declarations:
  `RingHom.formally_smooth_for_adic`,
  `IsGeometricallyRegular`,
  `H1Cotangent.map`,
  `KaehlerDifferential.residueFieldComparison`;
- best owner abstraction: this theorem remains `source-facing`, but its clauses should reuse the
  chapter owners above rather than introducing a parallel local regularity owner;
- primitive data: the field `k`, the Noetherian local `k`-algebra `A`, and the characteristic
  branch;
- derived API: the finite purely inseparable tensor-base-change clause is stated directly as the
  canonical bridge view of `IsGeometricallyRegular k A`, not through a second owner notion.

Source/core/bridge triage:
- `source-facing`: the characteristic-split theorem asserting the textbook equivalences;
- `core/canonical`: `RingHom.formally_smooth_for_adic`, `IsGeometricallyRegular`,
  `H1Cotangent.map`, and `KaehlerDifferential.residueFieldComparison`;
- `bridge/view`: the finite purely inseparable base-change criterion supplied by
  `isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing`.
-/

-- Proof sketch: in characteristic zero, combine Lemma `15.38.2` with Lemma `15.38.5`; the latter
-- applies because Proposition `10.158.9` makes every residue-field extension of a characteristic-zero
-- field separable in the Stacks Project sense. In characteristic `p > 0`, use Proposition
-- `15.35.1` for the equivalence among geometric regularity, the finite purely inseparable
-- base-change criterion, and the two cotangent-theoretic injectivity criteria; then combine
-- Lemmas `15.38.2`, `15.38.5`, and `15.37.8` to identify formal smoothness in the
-- `maximalIdeal A`-adic topology with the same list.
/-- Theorem 15.40.1: for a Noetherian local `k`-algebra `A`, if `k` has characteristic zero then
`A` is a regular local ring exactly when `k → A` is formally smooth for the `maximalIdeal A`-adic
topology. If `k` has characteristic `p > 0`, then the following project-facing clauses are
equivalent: `A` is geometrically regular over `k`; `k → A` is formally smooth for the
`maximalIdeal A`-adic topology; every finite purely inseparable field extension `k' / k` yields a
regular ring `k' ⊗[k] A`; `A` is regular local with injective canonical map
`H_1(L_{κ(A)/k}) → 𝔪_A / 𝔪_A^2`; and `A` is regular local with injective canonical map
`KaehlerDifferential.residueFieldComparison (ZMod p) k A`. -/
theorem regularLocalRing_formallySmooth_for_maximalIdeal_adic_tfae_by_characteristic :
    (∀ [CharZero k],
      IsRegularLocalRing A ↔
        (algebraMap k A).formally_smooth_for_adic (maximalIdeal A)) ∧
      ∀ (p : ℕ) [Fact p.Prime] [CharP k p],
        by
          letI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
          letI : Algebra (ZMod p) k := ZMod.algebra k p
          letI : Algebra (ZMod p) A := ZMod.algebra A p
          letI : IsScalarTower (ZMod p) k A := by infer_instance
          exact
            List.TFAE [
              IsGeometricallyRegular k A,
              (algebraMap k A).formally_smooth_for_adic (maximalIdeal A),
              ∀ (K : Type (max u v)) [Field K] [Algebra k K] [FiniteDimensional k K]
                [IsPurelyInseparable k K],
                  IsRegularRing (K ⊗[k] A),
              IsRegularLocalRing A ∧
                Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A)),
              IsRegularLocalRing A ∧
                Function.Injective
                  (KaehlerDifferential.residueFieldComparison (ZMod p) k A)
            ] := sorry

end

/-! ### Example_15_40_2 (from Chap15) -/
open PowerSeries
open IsLocalRing
open scoped RatFunc

universe u

section

variable {p : ℕ} [Fact p.Prime]
variable {K : Type u} [Field K] [ExpChar K p] [PerfectRing K p]
variable [Algebra (RatFunc (ZMod p)) K]
variable [IsPerfectClosure (algebraMap (RatFunc (ZMod p)) K) p]

/- Domain-style sampling for Example 15.40.2:
- primary domain: adic formal smoothness of coefficient maps into one-variable power series rings
  over perfect closures in characteristic `p`;
- sampled owner declarations:
  * `RingHom.formally_smooth_for_adic`,
  * `RingHom.formally_smooth_for_adic_baseChange`,
  * `regularLocalRing_formallySmooth_for_maximalIdeal_adic_tfae_by_characteristic`,
  * `zmod_to_mvPowerSeries_formally_smooth_for_madic`;
- best owner abstraction: the source-facing datum is still the specific ring homomorphism
  `f : RatFunc (ZMod p) →+* PowerSeries K` together with the condition on `f RatFunc.X`, but the
  topology owner on `PowerSeries K` should be the canonical local-ring ideal
  `maximalIdeal (PowerSeries K)` rather than the ad hoc presentation `Ideal.span {X}`;
- primitive data: the perfect-closure field `K`, the ring map `f`, and the equation
  `f RatFunc.X = C(t) + X`;
- derived API: adic formal smoothness of `f` for the one-variable power series target.

Source/core/bridge triage:
- `source-facing`: the Stacks example for the map sending `s` to `t + x`;
- `core/canonical`: `RingHom.formally_smooth_for_adic` and `maximalIdeal (PowerSeries K)`;
- `bridge/view`: the characteristic-`p` formal-smoothness criterion from Theorem `15.40.1`,
  specialized to this explicit map.
-/

-- Proof sketch: apply condition (5) of Theorem `15.40.1` through the differential criterion
-- described in the example. The source field `RatFunc (ZMod p)` has `Ω` free on `dX`, the chosen
-- map sends `X` to `t + x`, and hence `dX` maps to `dx`. Since `Ω[K[[x]]/𝔽_p]` is free on `dx`,
-- the induced map on differentials is injective, giving formal smoothness for the `(x)`-adic
-- topology.
/-- Example 15.40.2: let `k = RatFunc (ZMod p) = 𝔽_p(s)` and let `K` be a perfect closure of `k`,
modeling `𝔽_p(t)^{perf}`. If `f : k →+* K[[x]]`, formalized as
`f : RatFunc (ZMod p) →+* PowerSeries K`, sends the transcendental generator `s = RatFunc.X` to
`t + x`, where `t` is the image of `s` in `K`, then `f` is formally smooth for the `(x)`-adic
topology on `K[[x]]`; since `K` is a field, this is equivalently the
`maximalIdeal (PowerSeries K)`-adic topology. -/
theorem ratFunc_to_powerSeries_shift_formally_smooth_for_xadic
    (f : RatFunc (ZMod p) →+* PowerSeries K)
    (hfX :
      f RatFunc.X = C (algebraMap (RatFunc (ZMod p)) K RatFunc.X) + X) :
    f.formally_smooth_for_adic (maximalIdeal (PowerSeries K)) := sorry

end

/-! ### Lemma_15_40_3 (from Chap15) -/
open IsLocalRing

universe u v

namespace RingHom

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]

/- Domain-style sampling for Lemma 15.40.3:
- primary domain: adic formal smoothness of local homomorphisms of Noetherian local rings and the
  resulting flatness criterion.
- sampled owner declarations:
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.formally_smooth_for_adic_tfae_completion_invariance`
  * `adicCompletion_algebraMap_flat`
  * `exists_powerSeries_presentation_of_localHom_completeLocal`
- best owner abstraction: the primitive datum is the local ring map `f : A →+* B` itself, so the
  public statement should live on the owner `RingHom` and conclude with the canonical flatness
  predicate `f.Flat`, not with an auxiliary wrapper around the source and target rings.
- primitive data: the ring map `f`, the local/Noetherian hypotheses on `A` and `B`, and the
  maximal-ideal-adic formal smoothness hypothesis on `f`.
- derived API: flatness of `f`.

Source/core/bridge triage:
- `source-facing`: the Stacks-project implication from maximal-ideal-adic formal smoothness to
  flatness for a local homomorphism of Noetherian local rings;
- `core/canonical`: `RingHom.formally_smooth_for_adic` and `RingHom.Flat`;
- `bridge/view`: completion invariance, flatness of Noetherian adic completions, and the complete
  local power-series presentation from Lemma `15.39.3`.
-/

-- Proof sketch: pass to the completions of `A` and `B` using the completion-invariance of adic
-- formal smoothness and the flatness criterion for Noetherian completions. After reducing to the
-- complete local case, choose a flat power-series presentation as in Lemma `15.39.3`. Formal
-- smoothness provides a section of the quotient map from the base change `S / I S → B`, so `B` is
-- a retract of a flat `A`-module and hence flat.
/-- Lemma 15.40.3: a local homomorphism of Noetherian local rings which is formally smooth for the
`maximalIdeal B`-adic topology is flat. -/
theorem flat_of_formallySmooth_for_maximalIdeal_adic
    (f : A →+* B) [IsLocalHom f]
    (hfs : f.formally_smooth_for_adic (maximalIdeal B)) :
    f.Flat := sorry

end

end RingHom

/-! ### Lemma_15_40_4 (from Chap15) -/
open CategoryTheory
open Algebra
open IsLocalRing
open KaehlerDifferential
open scoped TensorProduct

universe u v

namespace Algebra

noncomputable section

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing B]

/- Domain-style sampling for Lemma 15.40.4:
- primary domain: the residue-field Jacobi-Zariski exact sequence for the local tower
  `A → B → κ(B)`, with the middle cotangent term written source-faithfully as
  `maximalIdeal B / (maximalIdeal B)^2`.
- sampled owner declarations:
  `KaehlerDifferential.kerCotangentToTensor`,
  `KaehlerDifferential.mapBaseChange`,
  `kaehlerDifferential_exact_cotangent_tensor_of_surjective`,
  `surjective_algebra_h1Cotangent_equiv_cotangent`,
  `ModuleCat.shortComplexOfCompEqZero`.
- best owner abstraction: the source-facing sequence should keep the cotangent-space term
  `(maximalIdeal B).Cotangent`; the public owner is the source-facing short complex
  `residueFieldCotangentSequence`, whose left map is the canonical conormal map
  `residueFieldCotangentToTensor`, built from `kerCotangentToTensor`, and whose right map is the
  canonical owner `KaehlerDifferential.mapBaseChange A B (ResidueField B)`. Since all three terms
  already carry their canonical `ResidueField B`-module structures, the sequence should live in
  `ShortComplex (ModuleCat (ResidueField B))`.
- primitive data: the algebra map `A → B` and the residue-field quotient `B → κ(B)`.
- derived API: the source-facing residue-field conormal map and the resulting
  exactness bridge theorem. The stronger local-hom/Noetherian and adic formal-smoothness
  hypotheses belong only to the injectivity theorem and the short-exact upgrade below.
- derived proof input: the bridge equivalence
  `H1Cotangent B κ(B) ≃ (maximalIdeal B).Cotangent` used in the injectivity theorem.

Source/core/bridge triage:
- `source-facing`: Lemma `15.40.4`, namely the exact sequence
  `0 → m_B / m_B² → κ(B) ⊗[B] Ω[B⁄A] → Ω[κ(B)⁄A] → 0`.
- `core/canonical`: `kerCotangentToTensor`, `KaehlerDifferential.mapBaseChange`, and
  `ModuleCat.shortComplexOfCompEqZero`.
- `bridge/view`: the kernel-identified exactness theorem
  `kaehlerDifferential_exact_cotangent_tensor_of_surjective` and the transport of the conormal
  owner from `ker (B → κ(B))` to `maximalIdeal B`, together with the quotient-linear upgrade of
  the left map from `B`-linearity to `ResidueField B`-linearity.
-/

/- The source-facing residue-field conormal exactness statement is already the kernel-identified
bridge `kaehlerDifferential_exact_cotangent_tensor_of_surjective`. -/
recall kaehlerDifferential_exact_cotangent_tensor_of_surjective

private theorem ker_algebraMap_residueField :
    RingHom.ker (algebraMap B (ResidueField B)) = maximalIdeal B := by
  simpa [ResidueField.algebraMap_eq] using
    (ker_residue : RingHom.ker (IsLocalRing.residue B) = maximalIdeal B)

private theorem algebraMap_residueField_surjective :
    Function.Surjective (algebraMap B (ResidueField B)) := by
  simpa [ResidueField.algebraMap_eq] using
    (residue_surjective : Function.Surjective (IsLocalRing.residue B))

private noncomputable def residueFieldKerCotangentEquiv :
    (maximalIdeal B).Cotangent ≃ₗ[B]
      (RingHom.ker (algebraMap B (ResidueField B))).Cotangent :=
  Ideal.Cotangent.equivOfEq
    (maximalIdeal B)
    (RingHom.ker (algebraMap B (ResidueField B)))
    ker_algebraMap_residueField.symm

variable (A B)

private noncomputable def residueFieldCotangentToTensorOverB :
    (maximalIdeal B).Cotangent →ₗ[B] ResidueField B ⊗[B] Ω[B⁄A] :=
  (kerCotangentToTensor A B (ResidueField B)).comp
    residueFieldKerCotangentEquiv.toLinearMap

noncomputable def residueFieldCotangentToTensor :
    (maximalIdeal B).Cotangent →ₗ[ResidueField B] ResidueField B ⊗[B] Ω[B⁄A] where
  toFun := residueFieldCotangentToTensorOverB A B
  map_add' := (residueFieldCotangentToTensorOverB A B).map_add
  map_smul' c x := by
    refine Quotient.inductionOn c ?_
    intro b
    change residueFieldCotangentToTensorOverB A B (b • x) = b • residueFieldCotangentToTensorOverB A B x
    exact (residueFieldCotangentToTensorOverB A B).map_smul b x

theorem residueFieldCotangentToTensor_exact :
    Function.Exact
      (residueFieldCotangentToTensor A B)
      (mapBaseChange A B (ResidueField B)) := by
  exact
    (kaehlerDifferential_exact_cotangent_tensor_of_surjective
      (maximalIdeal B)
      ker_algebraMap_residueField
      algebraMap_residueField_surjective).1

theorem residueFieldCotangentSequence_comp_eq_zero :
    (mapBaseChange A B (ResidueField B)).comp (residueFieldCotangentToTensor A B) =
      0 := by
  ext x
  simpa [Function.comp] using congrFun (residueFieldCotangentToTensor_exact A B).comp_eq_zero x

/-- The residue-field cotangent sequence
`(maximalIdeal B).Cotangent ⟶ ResidueField B ⊗[B] Ω[B⁄A] ⟶ Ω[ResidueField B⁄A]`
viewed in the canonical owner `ShortComplex (ModuleCat (ResidueField B))`. -/
noncomputable abbrev residueFieldCotangentSequence :
    ShortComplex (ModuleCat (ResidueField B)) :=
  ModuleCat.shortComplexOfCompEqZero
    (residueFieldCotangentToTensor A B)
    (mapBaseChange A B (ResidueField B))
    (residueFieldCotangentSequence_comp_eq_zero A B)

variable {A B}

section

variable [IsLocalRing A] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing A] [IsNoetherianRing B]

-- Proof sketch: identify the residue-field Jacobi-Zariski connecting term
-- `H₁(L_{κ(B)/B})` with `maximalIdeal B / (maximalIdeal B)^2` via the canonical surjective bridge
-- `surjective_algebra_h1Cotangent_equiv_cotangent`. The formal-smoothness hypothesis kills the
-- preceding homology term, so the source-facing conormal map becomes injective.
/-- Lemma 15.40.4: let `A → B` be a local homomorphism of Noetherian local rings. If
`A → B` is formally smooth for the `maximalIdeal B`-adic topology, then the leftmost map
`maximalIdeal B / (maximalIdeal B)^2 → κ(B) ⊗[B] Ω[B⁄A]`
in the residue-field cotangent sequence is injective. Combined with the kernel-identified
exactness bridge from Lemma `10.131.9`, this gives the source-facing exact sequence
`0 → maximalIdeal B / (maximalIdeal B)^2 → κ(B) ⊗[B] Ω[B⁄A] → Ω[κ(B)⁄A] → 0`. -/
theorem residueFieldCotangentToTensor_injective_of_formallySmooth_for_maximalIdeal_adic
    (hfs : RingHom.formally_smooth_for_adic (algebraMap A B) (maximalIdeal B)) :
    Function.Injective (residueFieldCotangentToTensor A B) := sorry

/-- Lemma 15.40.4: under maximal-ideal-adic formal smoothness, the residue-field cotangent
sequence
`0 → maximalIdeal B / (maximalIdeal B)^2 →
  κ(B) ⊗[B] Ω[B⁄A] → Ω[κ(B)⁄A] → 0`
is short exact. -/
theorem residueFieldCotangent_shortExact_of_formallySmooth_for_maximalIdeal_adic
    (hfs : RingHom.formally_smooth_for_adic (algebraMap A B) (maximalIdeal B)) :
    (residueFieldCotangentSequence A B).ShortExact := by
  refine ModuleCat.shortComplex_shortExact (residueFieldCotangentSequence A B) ?_ ?_ ?_
  · change Function.Exact (residueFieldCotangentToTensor A B) (mapBaseChange A B (ResidueField B))
    exact residueFieldCotangentToTensor_exact A B
  · change Function.Injective (residueFieldCotangentToTensor A B)
    exact residueFieldCotangentToTensor_injective_of_formallySmooth_for_maximalIdeal_adic hfs
  · change Function.Surjective (mapBaseChange A B (ResidueField B))
    exact mapBaseChange_surjective A B (ResidueField B) algebraMap_residueField_surjective

end

end

end

end Algebra

/-! ### Proposition_15_40_5 (from Chap15) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsLocalHom (algebraMap A B)]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) B
local notation "𝔪ClosedFiber" => Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)

/- Domain-style sampling for Proposition 15.40.5:
- primary domain: local commutative algebra of Noetherian local ring maps and their closed fibers;
- sampled owner declarations:
  `Ideal.Fiber`,
  `Algebra.IsGeometricallyRegular`,
  `RingHom.formally_smooth_for_adic`,
  `RingHom.Flat`;
- best owner abstraction: the special fiber is canonically owned by
  `ClosedFiber = Ideal.Fiber (maximalIdeal A) B`, while the tensor product presentation
  `ResidueField A ⊗[A] B` is only a bridge view;
- primitive data: the local map `A → B`, its flatness, the closed fiber `ClosedFiber`, and the
  adic ideal `𝔪ClosedFiber = Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)`;
- derived API: geometric regularity and adic formal smoothness of `ClosedFiber`.

Source/core/bridge triage:
- `source-facing`: the three-way equivalence in Proposition 15.40.5;
- `core/canonical`: `Ideal.Fiber`, `Algebra.IsGeometricallyRegular`,
  `RingHom.formally_smooth_for_adic`, and `RingHom.Flat`;
- `bridge/view`: the tensor-product presentation `ResidueField A ⊗[A] B` of `ClosedFiber`.
-/
-- Proof sketch: `(1) ↔ (2)` is Theorem `15.40.1` applied to the special fiber `κ(A) ⊗[A] B`.
-- The implication `(3) → (2)` combines flatness from Lemma `15.40.3` with base change of adic
-- formal smoothness along `A → κ(A)` from Lemma `15.37.8`. For `(2) → (3)`, pass to completions,
-- choose Cohen presentations as in Lemma `15.39.3`, identify the completed base change with `B`,
-- and then run the same derivation-splitting argument as in the proof of Theorem `15.40.1`.
/-- Proposition 15.40.5: for a local homomorphism `A → B` of Noetherian local rings with special
fiber `ClosedFiber = Ideal.Fiber (maximalIdeal A) B`, canonically presented by `κ(A) ⊗[A] B`,
the following are equivalent: `A → B` is flat and `ClosedFiber` is geometrically regular over
`κ(A)`; `A → B` is flat and `κ(A) → ClosedFiber` is formally smooth for the adic topology defined
by `𝔪ClosedFiber = Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)`; and `A → B` is
formally smooth for the `maximalIdeal B`-adic topology. -/
theorem flat_geometricallyRegularSpecialFiber_formallySmooth_tfae :
    List.TFAE [
      (algebraMap A B).Flat ∧ Algebra.IsGeometricallyRegular (ResidueField A) ClosedFiber,
      (algebraMap A B).Flat ∧
        RingHom.formally_smooth_for_adic (algebraMap (ResidueField A) ClosedFiber) 𝔪ClosedFiber,
      (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)
    ] := sorry

end

/-! ### Lemma_15_40_6 (from Chap15) -/
open IsLocalRing

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsNoetherianRing A] [IsCompleteLocalRing A]
variable [IsNoetherianRing B] [IsCompleteLocalRing B]
variable [Algebra (ResidueField A) B]

local notation "κA" => ResidueField A

/- Domain-style sampling for Lemma 15.40.6:
- primary domain: complete local commutative algebra, adic formal smoothness, and closed fibers of
  local maps;
- sampled owner declarations:
  * `Ideal.Fiber`,
  * `RingHom.formally_smooth_for_adic`,
  * `RingHom.formally_smooth_for_adic_baseChange`,
  * `flat_geometricallyRegularSpecialFiber_formallySmooth_tfae`;
- best owner abstraction: the closed fiber of the sought lift is canonically
  `Ideal.Fiber (maximalIdeal A) C`; the tensor-product model `ResidueField A ⊗[A] C` is only a
  bridge/view of that owner;
- primitive data: the complete local `ResidueField A`-algebra `B` and the adic formal smoothness
  hypothesis on `ResidueField A → B`;
- derived API: existence of a complete local `A`-algebra `C` whose structure map is adically
  formally smooth together with an explicit closed-fiber equivalence
  `Ideal.Fiber (maximalIdeal A) C ≃ₐ[ResidueField A] B`.

Source/core/bridge triage:
- `source-facing`: the existence of a formally smooth complete-local lift with prescribed closed
  fiber;
- `core/canonical`: `Ideal.Fiber` and `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the tensor-product presentation of the closed fiber.
-/
-- Proof sketch: choose the power-series presentation from Lemma `15.39.3` for the local map from a
-- Cohen ring or residue-field power series ring into `B`, then use regularity of the special
-- fiber to kill generators of the kernel so that the reduced presentation has special fiber
-- exactly `B`. Proposition `15.40.5` makes the resulting source formally smooth over the base
-- presentation ring, and Lemma `15.37.8` transports formal smoothness after base change along
-- the map to `A`.
/-- Lemma 15.40.6: if `A` is a Noetherian complete local ring and `B` is a Noetherian complete
local `ResidueField A`-algebra such that `ResidueField A → B` is formally smooth for the
`maximalIdeal B`-adic topology, then there exists a Noetherian complete local `A`-algebra `C`
whose structure map `A → C` is local and formally smooth for the `maximalIdeal C`-adic topology,
and whose closed fiber `Ideal.Fiber (maximalIdeal A) C`, canonically presented by
`ResidueField A ⊗[A] C`, is isomorphic to `B` over `ResidueField A`. -/
theorem exists_completeLocal_formallySmooth_lift_with_closedFiber
    (hfs : (algebraMap κA B).formally_smooth_for_adic (maximalIdeal B)) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : IsNoetherianRing C)
      (_ : IsCompleteLocalRing C) (_ : IsLocalHom (algebraMap A C))
      (_ : Ideal.Fiber (maximalIdeal A) C ≃ₐ[κA] B),
      (algebraMap A C).formally_smooth_for_adic (maximalIdeal C) := sorry

end

/-! ### Remark_15_40_7 (from Chap15) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open AdicCompletion
open IsLocalRing
open scoped TensorProduct

universe u v w

section

variable {A : Type u} {A' : Type v} {B : Type w}
variable [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
variable [IsNoetherianRing A] [IsCompleteLocalRing A]
variable [IsNoetherianRing A'] [IsCompleteLocalRing A']
variable [IsNoetherianRing B] [IsCompleteLocalRing B]
variable [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap A' B)]

local notation "κA" => ResidueField A
local notation "κA'" => ResidueField A'
local notation "ClosedFiberB" => Ideal.Fiber (maximalIdeal A') B
local notation "𝔪ClosedFiberB" => Ideal.map (algebraMap B ClosedFiberB) (maximalIdeal B)

variable (A) (A') in
private abbrev completedBaseChangeIdeal [CommRing A] [CommRing A'] [Algebra A A'] [IsLocalRing A]
    (C : Type*) [CommRing C] [Algebra A C] :
    Ideal (C ⊗[A] A') :=
  Ideal.map (algebraMap A (C ⊗[A] A')) (maximalIdeal A)

/-- The completed base change of an `A`-algebra `C` along the local map `A → A'`, completed with
respect to the ideal induced by `maximalIdeal A`. -/
abbrev completedBaseChange (A : Type u) (A' : Type v) [CommRing A] [CommRing A']
    [Algebra A A'] [IsLocalRing A] (C : Type*) [CommRing C] [Algebra A C] :=
  AdicCompletion (completedBaseChangeIdeal A A' C) (C ⊗[A] A')

/- Domain-style sampling for Remark 15.40.7:
- primary domain: complete local lifts with prescribed formally smooth closed fiber under a local
  base change with residue-field identification;
- sampled owner declarations:
  `Ideal.Fiber`,
  `Ideal.ResidueField.mapₐ`,
  `Algebra.TensorProduct.productMap`,
  `algebraMap A (C ⊗[A] A')`,
  `RingHom.adicCompletionMap`,
  `AdicCompletion.ofAlgEquiv`,
  `RingHom.formally_smooth_for_adic`,
  `exists_completeLocal_formallySmooth_lift_with_closedFiber`;
- best owner abstraction: the closed fiber should stay on the canonical owner
  `ClosedFiberB = Ideal.Fiber (maximalIdeal A') B`, and the comparison with
  the completed base change of `C` along `A → A'` should be the canonical `maximalIdeal A`-adic
  completion of `C ⊗[A] A'`, with comparison map induced by `algebraMap C B` and
  `algebraMap A' B`, not a separate wrapper predicate;
- primitive data: the local maps `A → A' → B`, the induced residue-field comparison
  on the maximal-ideal residue fields, and the adic formal smoothness of
  `κ(A') → ClosedFiberB`;
- derived API: the lifted complete local `A`-algebra `C`, the canonical completed base-change map
  `completedBaseChange C → B`, its surjectivity, and the surjective/finite/flat consequences.

Source/core/bridge triage:
- `source-facing`: the base-change variant of the complete-local lifting statement;
- `core/canonical`: `Ideal.Fiber`, `RingHom.formally_smooth_for_adic`, and
  `exists_completeLocal_formallySmooth_lift_with_closedFiber`, together with the completion owner
  `RingHom.adicCompletionMap`;
- `bridge/view`: the residue-field comparison on the closed fiber and the tensor-product
  presentation of the `maximalIdeal A`-adic completed base change before completion.
-/

variable (A) (A') (B) in
private abbrev tensorProductToTarget
    (C : Type*) [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B] :
    C ⊗[A] A' →+* B :=
  (Algebra.TensorProduct.productMap
    ((Algebra.ofId C B).restrictScalars A)
    ((Algebra.ofId A' B).restrictScalars A)).toRingHom

omit [IsNoetherianRing A] [IsCompleteLocalRing A] [IsNoetherianRing A'] [IsCompleteLocalRing A']
  [IsNoetherianRing B] [IsCompleteLocalRing B] [IsLocalHom (algebraMap A A')]
  [IsLocalHom (algebraMap A' B)] in
private theorem tensorProductToTarget_comp_algebraMap
    {C : Type*} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B] :
    (tensorProductToTarget A A' B C).comp
        (algebraMap A (C ⊗[A] A')) =
      algebraMap A B := by
  ext x
  simp [tensorProductToTarget]

omit [IsNoetherianRing A] [IsCompleteLocalRing A] [IsNoetherianRing A']
  [IsCompleteLocalRing A'] [IsNoetherianRing B] [IsCompleteLocalRing B] in
private theorem baseChangeIdeal_le_comap_maximalIdeal
    {C : Type*} [CommRing C] [IsLocalRing A] [IsLocalRing B]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B] [hAA' : IsLocalHom (algebraMap A A')]
    [hA'B : IsLocalHom (algebraMap A' B)] :
    completedBaseChangeIdeal A A' C ≤
      Ideal.comap (tensorProductToTarget A A' B C)
        (maximalIdeal B) := by
  let _ : IsLocalHom (algebraMap A A') := hAA'
  let _ : IsLocalHom (algebraMap A' B) := hA'B
  letI : IsLocalHom (algebraMap A B) := by
    simpa [IsScalarTower.algebraMap_eq A A' B] using
      (RingHom.isLocalHom_comp (algebraMap A' B) (algebraMap A A') :
        IsLocalHom ((algebraMap A' B).comp (algebraMap A A')))
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, tensorProductToTarget_comp_algebraMap]
  exact Ideal.map_le_iff_le_comap.mp (IsLocalRing.map_maximalIdeal_le (algebraMap A B))

omit [IsNoetherianRing A] [IsCompleteLocalRing A] [IsNoetherianRing A']
  [IsCompleteLocalRing A'] [IsNoetherianRing B] [IsCompleteLocalRing B]
  [IsLocalHom (algebraMap A A')] in
private theorem tensorProductToTarget_continuous
    {C : Type*} [CommRing C] [IsLocalRing A] [IsLocalRing B]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B] [hAA' : IsLocalHom (algebraMap A A')]
    [hA'B : IsLocalHom (algebraMap A' B)] :
    letI : TopologicalSpace (C ⊗[A] A') :=
      Ideal.adicTopology (completedBaseChangeIdeal A A' C)
    letI : TopologicalSpace B := Ideal.adicTopology (maximalIdeal B)
    Continuous (tensorProductToTarget A A' B C) := by
  let _ : IsLocalHom (algebraMap A A') := hAA'
  let _ : IsLocalHom (algebraMap A' B) := hA'B
  rw [RingHom.continuous_adic_iff_exists_pow_map_le]
  refine ⟨1, ?_⟩
  have hle :
      completedBaseChangeIdeal A A' C ≤
        Ideal.comap (tensorProductToTarget A A' B C) (maximalIdeal B) :=
    baseChangeIdeal_le_comap_maximalIdeal
  simpa [pow_one] using Ideal.map_le_iff_le_comap.mpr hle

/-- The canonical completed base-change map
`completedBaseChange C → B` induced by `C → B` and `A' → B`. -/
noncomputable def completedBaseChangeMap (A : Type u) (A' : Type v) (B : Type w)
    [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A' B] [Algebra A B]
    [IsScalarTower A A' B] [IsLocalRing A] [IsCompleteLocalRing B]
    [IsLocalHom (algebraMap A A')] [IsLocalHom (algebraMap A' B)]
    (C : Type*) [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B] :
    completedBaseChange A A' C →+* B :=
  (AdicCompletion.ofAlgEquiv (maximalIdeal B)).symm.toRingHom.comp
    (RingHom.adicCompletionMap
      (tensorProductToTarget A A' B C)
      (completedBaseChangeIdeal A A' C) (maximalIdeal B)
      tensorProductToTarget_continuous)

-- Proof sketch: apply Lemma `15.40.6` to the formally smooth special fiber over the common residue
-- field, obtaining a Noetherian complete local `A`-algebra `C` with the required closed fiber.
-- Then use Lemma `15.37.5` to lift the special-fiber map into `B`, producing the arrow `C → B`,
-- hence the canonical `maximalIdeal A`-adic completed base-change map `completedBaseChange C → B`.
/-- Remark 15.40.7: for local homomorphisms `A → A' → B` of Noetherian complete local rings, if
`A → A'` induces an isomorphism on residue fields and the special fiber
`ClosedFiberB = Ideal.Fiber (maximalIdeal A') B`, canonically presented by `κ(A') ⊗[A'] B`, is
formally smooth over `κ(A')` for the adic topology defined by
`𝔪ClosedFiberB = Ideal.map (algebraMap B ClosedFiberB) (maximalIdeal B)`, then there exists a
Noetherian complete local `A`-algebra `C` together with a local map `C → B` such that `A → C` is
formally smooth for the `maximalIdeal C`-adic topology and the canonical
`maximalIdeal A`-adic completed base-change map `completedBaseChange C → B` is surjective. -/
theorem exists_completeLocal_formallySmooth_lift_over_local_baseChange
    (hκ : Function.Bijective (ResidueField.map (algebraMap A A')))
    (hfs :
      (algebraMap κA' ClosedFiberB).formally_smooth_for_adic 𝔪ClosedFiberB) :
    ∃ (C : Type*) (_ : CommRing C) (_ : Algebra A C) (_ : IsNoetherianRing C)
      (_ : IsCompleteLocalRing C) (_ : IsLocalHom (algebraMap A C)) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (_ : IsLocalHom (algebraMap C B)),
      (algebraMap A C).formally_smooth_for_adic (maximalIdeal C) ∧
        Function.Surjective (completedBaseChangeMap A A' B C) := sorry

-- Proof sketch: Nakayama's lemma applied to the identified closed fibers shows that the map on
-- successive quotients modulo powers of `maximalIdeal A` are surjective. When `A → A'` itself is
-- surjective, the zeroth stage already forces `C → B` to be surjective.
/-- If the base change `A → A'` is surjective, then surjectivity of the canonical completed
base-change map `completedBaseChange C → B` forces `C → B` to be surjective. -/
theorem surjective_of_surjective_base_of_completedBaseChangeMap
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hbaseChange :
      Function.Surjective (completedBaseChangeMap A A' B C))
    (hAA' : Function.Surjective (algebraMap A A')) :
    Function.Surjective (algebraMap C B) := sorry

-- Proof sketch: first obtain surjectivity on all Artinian quotients from the closed-fiber
-- surjectivity of the completed base-change map by Nakayama. If `A'` is finite over `A`, the
-- completed-quotient argument identifies `B` as a finite `C`-module.
/-- If the intermediate extension `A → A'` is finite, then surjectivity of the canonical
completed base-change map makes `B` finite over `C`. -/
theorem finite_of_finite_base_of_completedBaseChangeMap
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hbaseChange :
      Function.Surjective (completedBaseChangeMap A A' B C))
    [Module.Finite A A'] :
    Module.Finite C B := sorry

-- Proof sketch: once the completed base-change map is surjective, flatness of `A' → B` kills its
-- kernel on all Artinian quotients, so the map is bijective.
/-- If `A' → B` is flat, then a surjective canonical completed base-change map is bijective. -/
theorem completedBaseChangeMap_bijective_of_flat
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hflat : (algebraMap A' B).Flat)
    (hbaseChange :
      Function.Surjective (completedBaseChangeMap A A' B C)) :
    Function.Bijective (completedBaseChangeMap A A' B C) := sorry

/-- In the flat case, the canonical completed base-change map is an isomorphism. -/
noncomputable def completedBaseChangeRingEquivOfFlat
    {C : Type*} [CommRing C] [Algebra A C] [IsNoetherianRing C] [IsCompleteLocalRing C]
    [IsLocalHom (algebraMap A C)] [Algebra C B] [IsScalarTower A C B]
    (hflat : (algebraMap A' B).Flat)
    (hbaseChange :
      Function.Surjective (completedBaseChangeMap A A' B C)) :
    completedBaseChange A A' C ≃+* B :=
  RingEquiv.ofBijective (completedBaseChangeMap A A' B C)
    (completedBaseChangeMap_bijective_of_flat hflat hbaseChange)

end
