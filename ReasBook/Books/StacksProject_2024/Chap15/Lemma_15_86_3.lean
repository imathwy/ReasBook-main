import Mathlib
import StacksProject_2024.Chap10.Definition_10_134_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Lemma_15_33_7
import StacksProject_2024.Chap15.Lemma_15_60_3
import StacksProject_2024.Chap15.Lemma_15_86_1

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open CategoryTheory
open ComplexShape
open ULift
open scoped DerivedTensorWithAlgebra NaiveCotangent TensorProduct

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

section

variable {A A' B : Type u}
variable [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A B]

local notation "B'" => A' ⊗[A] B
local notation "CpxB" => CochainComplex (ModuleCat B) ℤ
local notation "CpxB'" => CochainComplex (ModuleCat B') ℤ
local notation "DModB'" => DerivedCategory (ModuleCat B')

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

private abbrev extCpx : CpxB ⥤ CpxB' :=
  (ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex (up ℤ)

private local instance extendScalars_additive_local :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap B B')).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap B B')).left_adjoint_additive

/- Domain-style sampling for Lemma 15.86.3:
- primary domain: pushout/base-change comparison morphisms for naive cotangent complexes in
  `D(B')`;
- sampled owner declarations of the same kind:
  `NL_{B⁄A}`,
  `CategoryTheory.derivedTensorWithAlgebra`,
  `CategoryTheory.selfNaiveCotangentBaseChangeComparison` from `15.86.1`,
  `CategoryTheory.HasTorAmplitudeIn`,
  `Extension.CotangentSpace.map_comp_cotangentComplex`,
  `Generators.defaultHom`,
  `LinearMap.baseChange`;
- best owner abstraction: the source-facing owner is the canonical comparison morphism
  `NL_{B/A} ⊗[B] B' ⟶ NL_{B'/A'}`, together with its derived companion
  `NL_{B/A} ⊗[B]^L[B'] ⟶ NL_{B'/A'}`; the presentation-level tensorized conormal/cotangent-space
  maps are bridge data used only to build those owner morphisms;
- primitive data: only the pushout square `B' = A' ⊗[A] B` and the canonical self-presentations
  `Generators.self A B`, `Generators.self B B'`, `Generators.self A B'`, `Generators.self A' B'`;
- derived API: the underived comparison is a quasi-isomorphism when `A → B` is flat, and the
  derived comparison is an isomorphism under the intrinsic tor-amplitude hypothesis
  `HasTorAmplitudeIn NL_{B/A} (-1) 0`.

Source/core/bridge triage:
- `source-facing`: the two canonical comparison morphisms in `D(B')`;
- `core/canonical`: `NL_{B/A}`, `⊗[B]^L[B']`, and `HasTorAmplitudeIn`;
- `bridge/view`: the tensorized self-presentation complex of `NL_{B/A}` and the presentationwise
  chain maps built from `Extension.CotangentSpace.map_comp_cotangentComplex` and
  `Generators.defaultHom`.
 -/

local notation "PAB" => (Generators.self A B : Generators A B B)
local notation "Ppush" => (Generators.self B B' : Generators B B' B')
local notation "PtargetA" => (Generators.self A B' : Generators A B' B')
local notation "PtargetA'" => (Generators.self A' B' : Generators A' B' B')

private abbrev Pcomp : Generators A B' (B' ⊕ B) :=
  (Generators.self B B' : Generators B B' B').comp PAB

private noncomputable def tensorizedSelfNaiveCotangentChainComplex :
    ChainComplex (ModuleCat B') ℕ :=
  ChainComplex.mk'
    (ModuleCat.of B' (B' ⊗[B] (PAB).toExtension.CotangentSpace))
    (ModuleCat.of B' (B' ⊗[B] ULift ((PAB).toExtension.Cotangent)))
    (ModuleCat.ofHom
      (LinearMap.baseChange B'
        ((PAB).toExtension.cotangentComplex.comp ULift.moduleEquiv.toLinearMap)))
    (fun {_ _} _ ↦ ⟨ModuleCat.of B' PUnit, 0, CategoryTheory.Limits.zero_comp⟩)

private theorem extendScalarsComplex_selfNaiveCotangent_eq_tensorized :
    extCpx.obj (((PAB).toExtension.naiveCotangentChainComplex).extend embeddingDownNat) =
      ((tensorizedSelfNaiveCotangentChainComplex : ChainComplex (ModuleCat B') ℕ)).extend
        embeddingDownNat := by
  sorry

private noncomputable def tensorizedCompCotangentSpaceMap :
    B' ⊗[B] (PAB).toExtension.CotangentSpace →ₗ[B']
      ((((Generators.self B B' : Generators B B' B').comp
        (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).CotangentSpace :=
  let f := ((Ppush).toComp PAB).toExtensionHom
  show B' ⊗[B] (PAB).toExtension.CotangentSpace →ₗ[B']
      ((((Generators.self B B' : Generators B B' B').comp
        (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).CotangentSpace from
    (Extension.CotangentSpace.map f).liftBaseChange B'

private noncomputable def tensorizedCompCotangentMap :
    B' ⊗[B] (PAB).toExtension.Cotangent →ₗ[B']
      ((((Generators.self B B' : Generators B B' B').comp
        (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).Cotangent :=
  let f := ((Ppush).toComp PAB).toExtensionHom
  show B' ⊗[B] (PAB).toExtension.Cotangent →ₗ[B']
      ((((Generators.self B B' : Generators B B' B').comp
        (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).Cotangent from
    LinearMap.liftBaseChange B' (Extension.Cotangent.map f)

private noncomputable def tensorizedCompLiftCotangentMap :
    B' ⊗[B] ULift ((PAB).toExtension.Cotangent) →ₗ[B']
      ULift ((((Generators.self B B' : Generators B B' B').comp
        (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).Cotangent :=
  show B' ⊗[B] ULift ((PAB).toExtension.Cotangent) →ₗ[B']
      ULift ((((Generators.self B B' : Generators B B' B').comp
        (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).Cotangent from
    ((ULift.moduleEquiv :
        ULift ((((Generators.self B B' : Generators B B' B').comp
          (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).Cotangent ≃ₗ[B']
          ((((Generators.self B B' : Generators B B' B').comp
            (Generators.self A B : Generators A B B)) : Generators A B' (B' ⊕ B)).toExtension).Cotangent).symm.toLinearMap) ∘ₗ
      (tensorizedCompCotangentMap ∘ₗ
        LinearMap.baseChange B'
          ((ULift.moduleEquiv :
              ULift ((PAB).toExtension.Cotangent) ≃ₗ[B] (PAB).toExtension.Cotangent).toLinearMap))

private theorem tensorizedCompChainMap_comm :
    ModuleCat.ofHom tensorizedCompLiftCotangentMap ≫
      ((((Pcomp).toExtension : Algebra.Extension A B').naiveCotangentChainComplex).d 1 0) =
    tensorizedSelfNaiveCotangentChainComplex.d 1 0 ≫
      ModuleCat.ofHom tensorizedCompCotangentSpaceMap := by
  sorry

private theorem tensorizedSelfNaiveCotangentChainComplex_d_succ_succ (n : ℕ) :
    (tensorizedSelfNaiveCotangentChainComplex : ChainComplex (ModuleCat B') ℕ).d
      (n + 2) (n + 1) = 0 := by
  rw [tensorizedSelfNaiveCotangentChainComplex, ChainComplex.mk'_d]
  simp

private noncomputable def tensorizedCompChainMap :
    (tensorizedSelfNaiveCotangentChainComplex : ChainComplex (ModuleCat B') ℕ) ⟶
      (Pcomp).toExtension.naiveCotangentChainComplex :=
  ChainComplex.mkHom
    tensorizedSelfNaiveCotangentChainComplex
    (Pcomp).toExtension.naiveCotangentChainComplex
    (ModuleCat.ofHom tensorizedCompCotangentSpaceMap)
    (ModuleCat.ofHom tensorizedCompLiftCotangentMap)
    tensorizedCompChainMap_comm
    (fun i _ ↦ ⟨0, by
      rw [tensorizedSelfNaiveCotangentChainComplex_d_succ_succ]
      simp⟩)

private noncomputable def naiveCotangentUnderivedPushoutChainMap :
    (tensorizedSelfNaiveCotangentChainComplex : ChainComplex (ModuleCat B') ℕ) ⟶
      (PtargetA').toExtension.naiveCotangentChainComplex :=
  let f :
      (((Pcomp).toExtension : Algebra.Extension A B').Hom
        (((PtargetA').toExtension : Algebra.Extension A' B'))) :=
    (((PtargetA).defaultHom PtargetA').comp ((Pcomp).defaultHom PtargetA)).toExtensionHom
  tensorizedCompChainMap ≫ Extension.naiveCotangentChainMap f

end

section

variable (A A' B : Type u)
variable [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A B]

local notation "B'" => A' ⊗[A] B
local notation "CpxB" => CochainComplex (ModuleCat B) ℤ
local notation "PAB" => (Generators.self A B : Generators A B B)
local notation "DModB'" => DerivedCategory (ModuleCat B')

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

-- Proof sketch: the source is the ordinary tensorized two-term self-presentation model of
-- `NL_{B/A}` over `B'`, and the target is the canonical self-presentation model of `NL_{B'/A'}`.
-- The map is built from the presentation-level tensorized comparison to the composite
-- presentation of `B'` over `A`, followed by the canonical owner chain map induced by the
-- composite `defaultHom` comparison to the self-model over `A'`.
/-- The ordinary base-changed object `NL_{B/A} ⊗[B] B'` in `D(B')`, represented by extending
scalars on the canonical cochain model `NL_{B⁄A}.extend embeddingDownNat`. This is the
bridge/view source of the pushout comparison, not a second owner parallel to `NL_{B⁄A}`. -/
noncomputable abbrev naiveCotangentBaseChangeObject : DModB' :=
  DerivedCategory.Q.obj
    (((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex (up ℤ)).obj
      (((NL_{B⁄A}).extend embeddingDownNat : CpxB)))

/-- The canonical underived pushout comparison
`NL_{B/A} ⊗[B] B' ⟶ NL_{B'/A'}`
in `D(B')`, written on the source by the tensorized two-term self-presentation model of
`NL_{B/A}`. -/
noncomputable def naiveCotangentPushoutComparison :
    naiveCotangentBaseChangeObject A A' B ⟶
      naiveCotangentObject A' B' :=
  by
    change
      DerivedCategory.Q.obj
          (((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex (up ℤ)).obj
            (((PAB).toExtension.naiveCotangentChainComplex).extend embeddingDownNat)) ⟶
        naiveCotangentObject A' B'
    rw [extendScalarsComplex_selfNaiveCotangent_eq_tensorized]
    simpa using
      (DerivedCategory.Q.map
        (HomologicalComplex.extendMap
          naiveCotangentUnderivedPushoutChainMap
          embeddingDownNat))

-- Proof sketch: compose the canonical derived-to-underived comparison from Lemma `15.86.1`
-- for the self-presentation model of `NL_{B/A}` with the canonical underived pushout comparison
-- just defined above.
/-- The canonical derived pushout comparison
`NL_{B/A} ⊗[B]^{\mathbf L} B' ⟶ NL_{B'/A'}`
in `D(B')`. -/
noncomputable def naiveCotangentDerivedPushoutComparison :
    (naiveCotangentObject A B ⊗[B]^L[B']) ⟶
      naiveCotangentObject A' B' :=
  selfNaiveCotangentBaseChangeComparison ≫
    naiveCotangentPushoutComparison A A' B

-- Proof sketch: when `B` is flat over `A`, the tensorized self-presentation computes the
-- underived pushout `NL_{B/A} ⊗[B] B'`, and the source Stacks argument identifies the degree
-- `-1` and `0` maps with the canonical flat-base-change maps on `H1Cotangent` and Kähler
-- differentials. Since both complexes are two-term, those two homology isomorphisms imply the
-- comparison is a quasi-isomorphism.
/-- Lemma 15.86.3 (1): if `B` is flat over `A`, then the canonical underived pushout comparison
`NL_{B/A} ⊗[B] B' ⟶ NL_{B'/A'}`
is a quasi-isomorphism, i.e. an isomorphism in `D(B')`. -/
theorem naiveCotangentPushoutComparison_isIso_of_flat
    [Module.Flat A B] :
    IsIso (naiveCotangentPushoutComparison A A' B) := sorry

-- Proof sketch: the intrinsic hypothesis `HasTorAmplitudeIn NL_{B/A} (-1) 0` upgrades the
-- canonical derived-to-underived comparison for `NL_{B/A}` to a quasi-isomorphism after tensoring
-- with `B'`, and part `(1)` gives the underived pushout comparison as a quasi-isomorphism. Their
-- composite is therefore an isomorphism in `D(B')`.
/-- Lemma 15.86.3 (2): if `B` is flat over `A` and the canonical owner `NL_{B/A}` has
tor-amplitude in `[-1, 0]`, then the canonical derived pushout comparison
`NL_{B/A} ⊗[B]^{\mathbf L} B' ⟶ NL_{B'/A'}`
is a quasi-isomorphism, hence an isomorphism in `D(B')`. -/
theorem naiveCotangentDerivedPushoutComparison_isIso_of_flat_of_hasTorAmplitudeIn
    [Module.Flat A B]
    (hNL : HasTorAmplitudeIn (naiveCotangentObject A B) (-1) 0) :
    IsIso (naiveCotangentDerivedPushoutComparison A A' B) := sorry

end CategoryTheory

end
