import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_134_1
import stacks_proof.stacks_project.Chap15.Definition_15_67_1
import stacks_proof.stacks_project.Chap15.Lemma_15_33_7
import stacks_proof.stacks_project.Chap15.Lemma_15_60_3
import stacks_proof.stacks_project.Chap15.Lemma_15_86_1

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory.TStructure
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
  -- Proof comment: after unfolding the self-presentation two-term chain model, extending scalars
  -- along `B → B'` produces exactly the displayed tensorized two-term complex.
  rfl

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
  -- Proof comment: after removing the `ULift` bookkeeping, the degree `1 → 0` square is exactly
  -- the tensorized cotangent-complex compatibility for the composite presentation `Ppush.comp PAB`.
  -- TODO: rewrite the ambient `ModuleCat.ofHom` equality to the raw linear-map square on
  -- `y = baseChange ULift.moduleEquiv x`, then close it with
  -- `tensor_presentation_conormal_map_comp_cotangentComplex` plus the tensorized
  -- `LinearMap.baseChange` composition identity.
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
local notation "CpxB'" => CochainComplex (ModuleCat B') ℤ
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

/-- Helper for Lemma 15.86.3: in a cochain complex over `B'` supported in degrees `≥ -1`, the
degree `-1` cycles are the kernel of the outgoing differential. -/
private noncomputable def two_term_cycles_negOne_iso_kernel
    (P : CpxB') :
    P.cycles (-1) ≅ ModuleCat.of B' (LinearMap.ker ((P.d (-1) 0).hom)) := by
  let hprev : (ComplexShape.up ℤ).prev (-1) = -2 := by
    simpa using (CochainComplex.prev ℤ (-1))
  let hnext : (ComplexShape.up ℤ).next (-1) = 0 := by
    simpa using (CochainComplex.next ℤ (-1))
  let T : ShortComplex (ModuleCat B') := P.sc' (-2) (-1) 0
  let eShortKernel :
      T.cycles ≅ ModuleCat.of B' (LinearMap.ker ((P.d (-1) 0).hom)) := by
    -- Proof comment: on the owner short complex, cycles are literally the kernel of `d^{-1}`.
    simpa [T, hnext] using
      (T.cyclesIsoKernel ≪≫ ModuleCat.kernelIsoKer T.g)
  -- Proof comment: compare the ambient cycles object with the owner short complex first.
  exact (P.cyclesIsoSc' (-2) (-1) 0 hprev hnext) ≪≫ eShortKernel

/-- Helper for Lemma 15.86.3: in a cochain complex over `B'` supported in degrees `≥ -1`, the
degree `-1` homology is the kernel of the outgoing differential. -/
private noncomputable def two_term_homology_negOne_iso_kernel
    (P : CpxB') [CochainComplex.IsStrictlyGE P (-1)] :
    P.homology (-1) ≅ ModuleCat.of B' (LinearMap.ker ((P.d (-1) 0).hom)) := by
  have hzero_prev : P.d (-2) (-1) = 0 := by
    -- Proof comment: the source in degree `-2` vanishes under the lower support bound.
    exact (P.isZero_of_isStrictlyGE (-1) (-2) (by omega)).eq_of_src _ _
  let eHomology :
      P.homology (-1) ≅ P.cycles (-1) :=
    (P.isoHomologyπ (-2) (-1) (by simp) hzero_prev).symm
  -- Proof comment: after removing the zero incoming differential, only the kernel remains.
  exact eHomology ≪≫ two_term_cycles_negOne_iso_kernel (P := P)

/-- Helper for Lemma 15.86.3: in degree `0`, opcycles are the cokernel of `d^{-1}`. -/
private noncomputable def two_term_opcycles_zero_iso_cokernel
    (P : CpxB') :
    P.opcycles 0 ≅ cokernel (P.d (-1) 0) := by
  let hOpcycles :
      IsColimit (CokernelCofork.ofπ (P.pOpcycles 0) (P.d_pOpcycles (-1) 0)) := by
    simpa using P.opcyclesIsCokernel (i := -1) (j := 0) (by simp)
  -- Proof comment: compare the owner opcycle cokernel with the categorical cokernel of `d^{-1}`.
  exact
    (IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (P.d (-1) 0))
      hOpcycles).symm

/-- Helper for Lemma 15.86.3: the degree-`0` opcycles-to-cokernel identification is
characterized by the ambient quotient map `pOpcycles`. -/
private theorem pOpcycles_comp_two_term_opcycles_zero_iso_cokernel_hom
    (P : CpxB') :
    P.pOpcycles 0 ≫ (two_term_opcycles_zero_iso_cokernel (P := P)).hom =
      cokernel.π (P.d (-1) 0) := by
  let hOpcycles :
      IsColimit (CokernelCofork.ofπ (P.pOpcycles 0) (P.d_pOpcycles (-1) 0)) := by
    simpa using P.opcyclesIsCokernel (i := -1) (j := 0) (by simp)
  -- Proof comment: both cokernel presentations encode the same cofork, so the comparison
  -- isomorphism carries the owner projection `pOpcycles` to the categorical cokernel map.
  simpa [two_term_opcycles_zero_iso_cokernel, hOpcycles] using
    IsColimit.comp_coconePointUniqueUpToIso_hom
      hOpcycles
      (cokernelIsCokernel (P.d (-1) 0))
      WalkingParallelPair.one

/-- Helper for Lemma 15.86.3: in a two-term cochain complex over `B'`, degree `0` homology is
the cokernel of the degree `-1 → 0` differential. -/
private noncomputable def two_term_homology_zero_iso_cokernel
    (P : CpxB') [CochainComplex.IsStrictlyGE P (-1)] (hLE : P.IsStrictlyLE 0) :
    P.homology 0 ≅ cokernel (P.d (-1) 0) := by
  letI : P.IsStrictlyLE 0 := hLE
  have hzero_next : P.d 0 1 = 0 := by
    -- Proof comment: the target in degree `1` vanishes under the upper support bound.
    exact (P.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _
  let eHomology :
      P.homology 0 ≅ P.opcycles 0 :=
    P.isoHomologyι 0 1 (by simp) hzero_next
  -- Proof comment: once the outgoing differential vanishes, the remaining quotient is the cokernel.
  exact eHomology ≪≫ two_term_opcycles_zero_iso_cokernel (P := P)

/-- Helper for Lemma 15.86.3: the tor-amplitude hypothesis already places the derived source in
degrees `≥ -1` after tensoring with the regular `B`-module `B'`. -/
private theorem derived_pushout_source_isGE_of_hasTorAmplitude
    (hNL : HasTorAmplitudeIn (naiveCotangentObject A B) (-1) 0) :
    ((naiveCotangentObject A B) ⊗[B]^L[B']).IsGE (-1) := by
  -- Proof comment: evaluate the one-sided tor-amplitude bound on the test module `B'`.
  -- TODO: insert the canonical identification between scalar extension
  -- `K ⊗[B]^L[B']` and the derived tensor product against the degree-zero object `B'[0]`, then
  -- apply `HasTorAmplitudeIn.hasTorAmplitudeGE`.
  sorry

/-- Helper for Lemma 15.86.3: the canonical self-presentation cochain model for `NL_{B/A}` is
supported in degrees `≥ -1`. -/
private theorem self_naiveCotangent_isStrictlyGE :
    CochainComplex.IsStrictlyGE
      (show CpxB from (Algebra.naiveCotangent A B).extend embeddingDownNat)
      (-1) := by
  -- Proof comment: extending a chain complex on `ℕ` along `embeddingDownNat` only creates terms
  -- in nonpositive degrees, and `NL_{B/A}` itself is concentrated in chain degrees `0` and `1`.
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (Algebra.naiveCotangent A B).isZero_extend_X embeddingDownNat i fun j hij ↦ by
    have hnonpos : (embeddingDownNat.f j : ℤ) ≤ 0 := by
      simp [ComplexShape.embeddingDownNat]
    omega

private local instance self_naiveCotangent_isStrictlyGE_inst :
    CochainComplex.IsStrictlyGE
      (show CpxB from (Algebra.naiveCotangent A B).extend embeddingDownNat)
      (-1) :=
  self_naiveCotangent_isStrictlyGE (A := A) (B := B)

/-- Helper for Lemma 15.86.3: the canonical derived base-change comparison first factors through
the truncation `τ_{\ge -1}` of the derived tensor source, exactly as in the source proof. -/
private theorem selfNaiveCotangentBaseChangeComparison_factor_through_truncGE :
    (selfNaiveCotangentBaseChangeComparison
      (R := A) (S := B) (S' := B')) =
      ((t.truncGEπ (-1)).app
        ((naiveCotangentObject A B) ⊗[B]^L[B'])) ≫
        (selfNaiveCotangentBaseChangeTruncGEComparison
          (R := A) (S := B) (S' := B')) := by
  -- Proof comment: the truncation comparison is defined by `t.descTruncGE`, so the factorization
  -- is exactly the universal identity `t.π_descTruncGE` specialized to the self-presentation
  -- base-change morphism.
  simpa [Category.assoc, selfNaiveCotangentBaseChangeTruncGEComparison] using
    (t.π_descTruncGE
      (f := selfNaiveCotangentBaseChangeComparison
        (R := A) (S := B) (S' := B'))
      (-1))

-- Proof sketch: when `B` is flat over `A`, the tensorized self-presentation computes the
-- underived pushout `NL_{B/A} ⊗[B] B'`, and the source Stacks argument identifies the degree
-- `-1` and `0` maps with the canonical flat-base-change maps on `H1Cotangent` and Kähler
-- differentials. Since both complexes are two-term, those two homology isomorphisms imply the
-- comparison is a quasi-isomorphism.
/-- Lemma 15.86.3 (1): if `B` is flat over `A`, then the canonical underived pushout comparison
`NL_{B/A} ⊗[B] B' ⟶ NL_{B'/A'}`
is a quasi-isomorphism, i.e. an isomorphism in `D(B')`. -/
@[stacks 0FJU]
theorem naiveCotangentPushoutComparison_isIso_of_flat
    [Module.Flat A B] :
    IsIso (naiveCotangentPushoutComparison A A' B) := by
  -- Route correction: the degree-`0` branch now normalizes concretely through
  -- `pOpcycles_comp_two_term_opcycles_zero_iso_cokernel_hom`; the remaining source-faithful work
  -- is to conjugate the degree `-1` and `0` homology maps of
  -- `naiveCotangentPushoutComparison` to the public `H1Cotangent` and Kähler base-change owner
  -- maps, and then finish the two-term window argument.
  sorry

-- Proof sketch: the intrinsic hypothesis `HasTorAmplitudeIn NL_{B/A} (-1) 0` upgrades the
-- canonical derived-to-underived comparison for `NL_{B/A}` to a quasi-isomorphism after tensoring
-- with `B'`, and part `(1)` gives the underived pushout comparison as a quasi-isomorphism. Their
-- composite is therefore an isomorphism in `D(B')`.
/-- Lemma 15.86.3 (2): if `B` is flat over `A` and the canonical owner `NL_{B/A}` has
tor-amplitude in `[-1, 0]`, then the canonical derived pushout comparison
`NL_{B/A} ⊗[B]^{\mathbf L} B' ⟶ NL_{B'/A'}`
is a quasi-isomorphism, hence an isomorphism in `D(B')`. -/
@[stacks 0FJU]
theorem naiveCotangentDerivedPushoutComparison_isIso_of_flat_of_hasTorAmplitudeIn
    [Module.Flat A B]
    (hNL : HasTorAmplitudeIn (naiveCotangentObject A B) (-1) 0) :
    IsIso (naiveCotangentDerivedPushoutComparison A A' B) := by
  -- Route correction: instead of searching for a direct derived proof, factor the canonical map
  -- through `τ_{\ge -1}` exactly as in the source argument, then compose the two known
  -- isomorphisms.
  -- Proof comment: first upgrade the derived source to `D^{≥ -1}` using the tor-amplitude
  -- hypothesis, exactly as in the textbook passage from derived to ordinary tensor product.
  have hGE :
      ((naiveCotangentObject A B) ⊗[B]^L[B']).IsGE (-1) :=
    derived_pushout_source_isGE_of_hasTorAmplitude
      (A := A) (A' := A') (B := B) hNL
  have hπ :
      IsIso
        ((t.truncGEπ (-1)).app
          ((naiveCotangentObject A B) ⊗[B]^L[B'])) :=
    (t.isGE_iff_isIso_truncGEπ_app (-1)
      ((naiveCotangentObject A B) ⊗[B]^L[B'])).1 hGE
  have htrunc :
      IsIso
        (selfNaiveCotangentBaseChangeTruncGEComparison
          (R := A) (S := B) (S' := B')) := by
    -- Proof comment: Lemma `15.86.1` gives the self-presentation truncation comparison.
    simpa [naiveCotangentBaseChangeObject] using
      (selfNaiveCotangentBaseChangeComparison_truncGE_isIso
        (R := A) (S := B) (S' := B'))
  have hunderived :
      IsIso (naiveCotangentPushoutComparison A A' B) :=
    naiveCotangentPushoutComparison_isIso_of_flat
      (A := A) (A' := A') (B := B)
  have htail :
      IsIso
        ((selfNaiveCotangentBaseChangeTruncGEComparison
          (R := A) (S := B) (S' := B')) ≫
          naiveCotangentPushoutComparison A A' B) := by
    infer_instance
  have htotal :
      IsIso
        (((t.truncGEπ (-1)).app
          ((naiveCotangentObject A B) ⊗[B]^L[B'])) ≫
          ((selfNaiveCotangentBaseChangeTruncGEComparison
            (R := A) (S := B) (S' := B')) ≫
            naiveCotangentPushoutComparison A A' B)) := by
    infer_instance
  -- Proof comment: rewrite the first factor through `τ_{\ge -1}` and compose the three
  -- isomorphisms `truncGEπ`, `15.86.1`, and part `(1)`.
  simpa [naiveCotangentDerivedPushoutComparison,
    selfNaiveCotangentBaseChangeComparison_factor_through_truncGE
      (A := A) (A' := A') (B := B),
    Category.assoc] using htotal

end CategoryTheory

end
