import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_49_1 (from Chap15) -/
universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B]

namespace RingHom

/- Domain-style sampling:
- primary domain: formal smoothness of adic ring maps and extension of absolute derivations across
  square-zero thickenings.
- sampled owner declarations:
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.exists_continuous_lift_of_formally_smooth_for_adic`
  * `Derivation`
  * `Derivation.liftOfDerivationToSquareZero`
- best owner abstraction: an arbitrary ring map `f : A →+* B` together with the ideal
  `I : Ideal B` controlling the adic topology; the local/maximal-ideal case is a specialization.
- source/core/bridge triage:
  * `source-facing`: extension of an absolute derivation across a formally smooth adic map;
  * `core/canonical`: the owner lifting theorem
    `RingHom.exists_continuous_lift_of_formally_smooth_for_adic` together with the standard
    derivation/square-zero-extension API;
  * `bridge/view`: the complete-local maximal-ideal specialization below.
- primitive data: the ring map `f : A →+* B`, the ideal `I : Ideal B`, `I`-adic completeness of
  `B`, and the derivation `D : Derivation ℤ A A`.
- derived API: existence of an absolute derivation on `B` restricting to `D` along `f`.
-/

-- Proof sketch: form the square-zero thickening `B[ε]` and the map `A → B[ε]` sending
-- `a` to `f a + ε • f (D a)`. Because `B` is `I`-adically complete and `f` is formally smooth
-- for the `I`-adic topology, Lemma `15.37.5` provides a lift `B → B[ε]`. Taking the
-- `ε`-coefficient of that lift yields the required derivation on `B`, and the commutative square
-- forces it to agree with `D` on the image of `A`.
/-- A formally smooth adic ring map into an adically complete target extends absolute derivations
from the source to the target. -/
theorem exists_derivation_extension_of_formally_smooth_for_adic
    (f : A →+* B) (I : Ideal B) [IsAdicComplete I B]
    (hfs : f.formally_smooth_for_adic I)
    (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B, ∀ a : A, D' (f a) = f (D a) := sorry

end RingHom

section

open IsLocalRing

variable [Algebra A B] [IsCompleteLocalRing B]

/-- Lemma 15.49.1: if `B` is a complete local ring and `algebraMap A B` is formally smooth for
the `maximalIdeal B`-adic topology, then every absolute derivation `D : A → A` extends to an
absolute derivation `D' : B → B`. -/
theorem exists_derivation_extension_of_formally_smooth_for_completeLocal
    (hfs : RingHom.formally_smooth_for_adic (algebraMap A B) (maximalIdeal B))
    (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B, ∀ a : A, D' (algebraMap A B a) = algebraMap A B (D a) := by
  simpa using
    (algebraMap A B).exists_derivation_extension_of_formally_smooth_for_adic
      (maximalIdeal B) hfs D

end

end

/-! ### Proposition_15_49_2 (from Chap15) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open AdicCompletion
open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsCompleteLocalRing A]
variable [IsLocalRing B] [IsNoetherianRing B]
variable [IsLocalHom (algebraMap A B)]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A
local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) B
local notation "𝔪ClosedFiber" => Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)

/- Domain-style sampling for Proposition 15.49.2:
- primary domain: regular local morphisms from a Noetherian complete local source to a Noetherian
  local target, their special fibers, and adic formal smoothness;
- sampled owner declarations:
  `RingHom.IsRegularRingMap`,
  `flat_geometricallyRegularSpecialFiber_formallySmooth_tfae`,
  `RingHom.IsRegularRingMap.of_comp_of_faithfullyFlat`,
  `regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion`;
- best owner abstraction: the four-way equivalence is already canonically owned by
  `regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion`; in the complete-local
  case, this proposition is the specialization where the completion map
  `A → ACompletion` is regular;
- primitive data: the local map `A → B`, the complete-local owner on `A`, the local Noetherian
  target `B`, the special fiber `ClosedFiber`, and the adic ideal `𝔪ClosedFiber`;
- derived API: the regularity of `A → ACompletion`, obtained from the completion equivalence and
  faithfully-flat descent, and then the specialized `List.TFAE` conclusion.

Source/core/bridge triage:
- `source-facing`: Proposition 15.49.2 itself, the complete-local form of the four-way
  equivalence;
- `core/canonical`: `regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion`;
- `bridge/view`: the regularity of `A → ACompletion`, deduced from the equivalence
  `ofAlgEquiv (maximalIdeal A) : A ≃ₐ[A] ACompletion`.
-/
-- Proof sketch: apply the canonical theorem
-- `regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion`. Since `A` is already
-- complete for the `maximalIdeal A`-adic topology, the completion map `A → ACompletion` admits an
-- inverse ring map `ACompletion → A` from `ofAlgEquiv (maximalIdeal A)`. The composition is the
-- identity on `A`, hence regular; the inverse is bijective, therefore faithfully flat, so Lemma
-- `15.41.7` descends regularity to `A → ACompletion`.
/-- Proposition 15.49.2: for a local homomorphism `A → B` of Noetherian local rings with `A`
complete local, the following are equivalent: `A → B` is regular; `A → B` is flat and the special
fiber
`ClosedFiber = Ideal.Fiber (maximalIdeal A) B`, equivalently `ResidueField A ⊗[A] B`, is
geometrically regular over `ResidueField A`; `A → B` is flat and
`ResidueField A → ClosedFiber` is formally smooth for the `𝔪ClosedFiber`-adic topology; and
`A → B` is formally smooth for the `maximalIdeal B`-adic topology. -/
theorem regularMap_specialFiber_characterizations_tfae :
    List.TFAE [
      (algebraMap A B).IsRegularRingMap,
      (algebraMap A B).Flat ∧ Algebra.IsGeometricallyRegular (ResidueField A) ClosedFiber,
      (algebraMap A B).Flat ∧
        RingHom.formally_smooth_for_adic (algebraMap (ResidueField A) ClosedFiber) 𝔪ClosedFiber,
      (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)
    ] := by
  let g : ACompletion →+* A := (ofAlgEquiv (maximalIdeal A)).symm.toRingHom
  have hcomp : (g.comp (algebraMap A ACompletion)).IsRegularRingMap := by
    have hg : g.comp (algebraMap A ACompletion) = RingHom.id A := by
      ext x
      change (ofAlgEquiv (maximalIdeal A)).symm (of (maximalIdeal A) A x) = x
      simpa using ofAlgEquiv_symm_of (maximalIdeal A) x
    rw [hg]
    infer_instance
  have hACompletion : (algebraMap A ACompletion).IsRegularRingMap :=
    RingHom.IsRegularRingMap.of_comp_of_faithfullyFlat hcomp
      (RingHom.FaithfullyFlat.of_bijective (ofAlgEquiv (maximalIdeal A)).symm.bijective)
  exact regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion hACompletion

end

/-! ### Theorem_15_49_3_Andr (from Chap15) -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsLocalHom (algebraMap A B)]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) B
local notation "𝔪ClosedFiber" => Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)

/- Domain-style sampling for Theorem 15.49.3 (André):
- primary domain: regular local morphisms of Noetherian local rings, their special fibers, and
  adic formal smoothness;
- sampled owner declarations:
  `RingHom.IsRegularRingMap`,
  `flat_geometricallyRegularSpecialFiber_formallySmooth_tfae`,
  `RingHom.formally_smooth_for_adic_tfae_completion_invariance`,
  `RingHom.IsRegularRingMap.of_comp_of_faithfullyFlat`;
- best owner abstraction: this theorem is `source-facing`; its main clause is the canonical owner
  `(algebraMap A B).IsRegularRingMap`, while the remaining three clauses should reuse the
  already-established
  special-fiber owner package from Proposition `15.40.5` rather than introducing any parallel
  local wrapper;
- primitive data: the local map `algebraMap A B`, the closed fiber `ClosedFiber`, the adic ideal
  `𝔪ClosedFiber`, and the regularity hypothesis on the completion map `A → A^∧`;
- derived API: the equivalence among the last three clauses from Proposition `15.40.5`, and the
  completion/descent bridge used to compare clause `(1)` with that owner package.

Source/core/bridge triage:
- `source-facing`: the four-way `List.TFAE` theorem below;
- `core/canonical`: `(algebraMap A B).IsRegularRingMap`, `Ideal.Fiber`, and
  `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the tensor-product presentation `ResidueField A ⊗[A] B` of `ClosedFiber` and the
  completion maps entering the André hypothesis.
-/

-- Proof sketch: Proposition `15.40.5` gives the equivalence of the last three clauses. The
-- implication from regularity to flatness plus geometric regularity of the special fiber is the
-- closed-fiber part of the definition of `(algebraMap A B).IsRegularRingMap`. For the
-- converse, apply
-- Lemma `15.37.4` to pass formal smoothness to completions, use Proposition `15.49.2` to deduce
-- that `A^∧ → B^∧` is regular, compose with the assumed regular map `A → A^∧`, and then descend
-- regularity across the faithfully flat completion map `B → B^∧` by Lemma `15.41.7`.
/-- Theorem 15.49.3 (André): let `A → B` be a local homomorphism of Noetherian local rings, let
`ClosedFiber = Ideal.Fiber (maximalIdeal A) B`, canonically presented by
`ResidueField A ⊗[A] B`, be the special fiber. If the completion map
`A → AdicCompletion (maximalIdeal A) A` is regular, then the regularity of `A → B`, the standard
flatness-plus-closed-fiber conditions, and adic formal smoothness of `A → B` are equivalent. -/
theorem regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion
    (hA_completion :
      (algebraMap A (AdicCompletion (maximalIdeal A) A)).IsRegularRingMap) :
    List.TFAE [
      (algebraMap A B).IsRegularRingMap,
      (algebraMap A B).Flat ∧ Algebra.IsGeometricallyRegular (ResidueField A) ClosedFiber,
      (algebraMap A B).Flat ∧
        (algebraMap (ResidueField A) ClosedFiber).formally_smooth_for_adic 𝔪ClosedFiber,
      (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)
    ] := sorry

end
