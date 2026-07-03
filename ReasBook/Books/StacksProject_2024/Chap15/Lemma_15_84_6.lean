import Mathlib
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_84_1
import StacksProject_2024.Chap15.Lemma_15_72_1
import StacksProject_2024.Chap15.Lemma_15_74_4

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open Opposite
open scoped DerivedTensorWithAlgebra
open scoped DerivedInternalHom
open scoped ModuleComplexInternalHom
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A] [Algebra.FinitePresentation R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "MinusCpxA" => CochainComplex.minus (ModuleCat A)
local notation "BoundedCpxA" => CochainComplex.bounded (ModuleCat A)
local notation "PlusCpxA" => CochainComplex.plus (ModuleCat A)

/-
Domain-style sampling for Lemma 15.84.6:
- primary domain: derived internal-Hom in `D(A)` for a pseudo-coherent source and an
  `R`-perfect target, computed by the chapter owner `module_complex_internal_hom` through concrete
  cochain representatives over `A`;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.IsPerfectOver`,
  `isPerfectOver_iff_exists_bounded_flat_finitePresentation_representative`,
  `CochainComplex.minus`,
  `CochainComplex.bounded`,
  `CochainComplex.plus`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `module_complex_internal_hom`,
  `RHom[H](K, L)`,
  `module_complex_internal_hom_represents_derivedInternalHom_of_boundedAbove_projective`,
  `CochainComplex.IsTermwiseFlat`;
- best owner abstraction: the primitive owner data live upstream on `K.IsPseudoCoherent` and
  `DerivedCategory.IsPerfectOver R L`, together with the representative criterion
  `isPerfectOver_iff_exists_bounded_flat_finitePresentation_representative`; the concrete
  complexes `P`, `F`, and `⟪P, F⟫` here are therefore bridge/view data over those owners,
  expressed with the canonical boundedness owners
  `CochainComplex.minus`, `CochainComplex.bounded`, and `CochainComplex.plus`;
- primitive vs. derived:
  primitive data are the chosen bounded-above finite-free representative of `K` and bounded
  termwise `R`-flat finitely presented representative of `L`, with the latter obtained from
  `hL` through Lemma `15.84.4` under the ambient flat finite-presentation hypotheses on `R → A`;
  derived API is the resulting bounded-below flat finitely presented Hom-complex representative,
  together with the base-change and finite-presentation companion lemmas for fixed
  representatives;
- source/core/bridge triage:
  `source-facing`: the existential representative theorem immediately below;
  `core/canonical`: `DerivedCategory.IsPseudoCoherent`, `DerivedCategory.IsPerfectOver`,
    `CochainComplex.IsTermwiseFiniteFree`, `⟪P, F⟫`, and the canonical scalar-restriction and
    scalar-extension functors on cochain complexes;
  `bridge/view`: the fixed-representative Hom-complex theorems that follow.
-/

-- Proof sketch: unpack `hK : K.IsPseudoCoherent` to choose a bounded-above termwise finite-free
-- representative `P^•` of `K`, and use Lemma `15.84.4` under `[Module.Flat R A]` and
-- `[Algebra.FinitePresentation R A]` to choose a bounded termwise `R`-flat representative `F^•`
-- of `L` with finitely presented terms. The fixed-representative companion theorems below then
-- show that `Hom^•(P^•, F^•)` is bounded below, termwise `R`-flat after restriction of scalars,
-- has finitely presented terms, and computes the chosen derived internal-Hom object
-- `RHom[H](K, L)`.
/-- Lemma 15.84.6: let `R → A` be a flat ring map of finite presentation. If `K` is
pseudo-coherent and `L` is perfect over `R`, then one can choose a bounded-above termwise
finite-free representative `P^•` of `K` and a bounded termwise `R`-flat representative `F^•` of
`L` with finitely presented terms such that
`Hom^•(P^•, F^•)` is bounded below, termwise `R`-flat after restriction of scalars, has finitely
presented terms, and represents the chosen derived internal-Hom object
`R\mathrm{Hom}_A(K, L)`. -/
theorem exists_homComplex_termwiseFlat_finitePresentation_representative_of_isPseudoCoherent_of_isPerfectOver
    (H : MonoidalClosed DModA) {K L : DModA}
    (hK : K.IsPseudoCoherent)
    (hL : DerivedCategory.IsPerfectOver R L) :
    ∃ P F : CpxA,
      MinusCpxA P ∧
        P.IsTermwiseFiniteFree ∧
        IsIsomorphic (DerivedCategory.Q.obj P) K ∧
        BoundedCpxA F ∧
        CochainComplex.IsTermwiseFlat
          (((Functor.mapHomologicalComplex
            (ModuleCat.restrictScalars (algebraMap R A))
            (up ℤ)).obj F : CpxR)) ∧
        (∀ i : ℤ, Module.FinitePresentation A (F.X i)) ∧
        IsIsomorphic (DerivedCategory.Q.obj F) L ∧
        PlusCpxA ⟪P, F⟫ ∧
        CochainComplex.IsTermwiseFlat
          (((Functor.mapHomologicalComplex
            (ModuleCat.restrictScalars (algebraMap R A))
            (up ℤ)).obj ⟪P, F⟫ : CpxR)) ∧
        (∀ n : ℤ, Module.FinitePresentation A ((⟪P, F⟫).X n)) ∧
        IsIsomorphic (DerivedCategory.Q.obj ⟪P, F⟫) (RHom[H](K, L)) := sorry

-- Proof sketch: `P` is bounded above and termwise finite free, while `F` is bounded and termwise
-- `R`-flat, so `Hom^•(P^•, F^•)` is bounded below and its degree-`n` terms are finite direct sums
-- of `R`-flat modules. The standard K-projective Hom-complex computation identifies
-- `Hom^•(P^•, F^•)` with the canonical chosen derived internal-Hom object `RHom[H](K, L)` in
-- `D(A)`.
/-- Companion bridge for Lemma 15.84.6: once `P^•` and `F^•` are already chosen as above, the
Hom complex `\mathrm{Hom}^\bullet(P^•, F^•)` is a bounded-below termwise `R`-flat representative
of `R\mathrm{Hom}_A(K, L)`. -/
theorem homComplex_isBoundedBelowTermwiseFlatRepresentativeOverBase
    (H : MonoidalClosed DModA) {K L : DModA}
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hPiso : IsIsomorphic (DerivedCategory.Q.obj P) K)
    (hFbounded : BoundedCpxA F)
    (hFflat :
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj F : CpxR)))
    (hFiso : IsIsomorphic (DerivedCategory.Q.obj F) L) :
    PlusCpxA ⟪P, F⟫ ∧
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj ⟪P, F⟫ : CpxR)) ∧
      IsIsomorphic (DerivedCategory.Q.obj ⟪P, F⟫) (RHom[H](K, L)) := sorry

end

section

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']

local notation "Aprime" => A ⊗[R] R'
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModAprime" => DerivedCategory (ModuleCat Aprime)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "CpxR'" => CochainComplex (ModuleCat R') ℤ
local notation "CpxAprime" => CochainComplex (ModuleCat Aprime) ℤ
local notation "MinusCpxA" => CochainComplex.minus (ModuleCat A)
local notation "BoundedCpxA" => CochainComplex.bounded (ModuleCat A)
local notation "PlusCpxA" => CochainComplex.plus (ModuleCat A)
local notation "PlusCpxAprime" => CochainComplex.plus (ModuleCat Aprime)
local instance commRingAprime : CommRing Aprime := by infer_instance
local instance algebraRprimeAprime : Algebra R' Aprime := by infer_instance
local instance algebraAAprime : Algebra A Aprime := by infer_instance

-- Proof sketch: extend scalars degreewise from `A` to `A' = A ⊗[R] R'`. Because `P` is termwise
-- finite free, internal Homs commute with this scalar extension termwise, and the resulting
-- complex stays bounded below and computes the canonical derived internal-Hom object over `A'` of
-- the base-changed representatives.
/-- After any base change `R → R'`, the scalar extension of `Hom^•(P^•, F^•)` to
`A' = A ⊗[R] R'` is bounded below. -/
theorem baseChange_homComplex_isBoundedBelow
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hFboundedBelow : PlusCpxA F) :
    PlusCpxAprime
      (((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A Aprime))
          (up ℤ)).obj ⟪P, F⟫ : CpxAprime)) := sorry

/-- After any base change `R → R'`, the scalar extension of `Hom^•(P^•, F^•)` to
`A' = A ⊗[R] R'` is termwise `R'`-flat after restriction of scalars. -/
theorem baseChange_homComplex_isTermwiseFlatOverBase
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hFbounded : BoundedCpxA F)
    (hFflat :
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj F : CpxR))) :
    CochainComplex.IsTermwiseFlat
      (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R' Aprime))
          (up ℤ)).obj
          (((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (algebraMap A Aprime))
              (up ℤ)).obj ⟪P, F⟫ : CpxAprime)) : CpxR')) :=
      sorry

/-- After any base change `R → R'`, the scalar extension of `Hom^•(P^•, F^•)` to
`A' = A ⊗[R] R'` represents the derived internal-Hom of the actual derived base changes of the
objects represented by `P^•` and `F^•`. -/
theorem baseChange_homComplex_represents_derivedInternalHom
    (H' : MonoidalClosed DModAprime)
    {K L : DModA} (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hPiso : IsIsomorphic (DerivedCategory.Q.obj P) K)
    (hFbounded : BoundedCpxA F)
    (hFflat :
      CochainComplex.IsTermwiseFlat
        (((Functor.mapHomologicalComplex
          (ModuleCat.restrictScalars (algebraMap R A))
          (up ℤ)).obj F : CpxR)))
    (hFiso : IsIsomorphic (DerivedCategory.Q.obj F) L) :
    IsIsomorphic
      (DerivedCategory.Q.obj
        (((Functor.mapHomologicalComplex
            (ModuleCat.extendScalars (algebraMap A Aprime))
            (up ℤ)).obj ⟪P, F⟫ : CpxAprime)))
      (RHom[H'](K ⊗[A]^L[Aprime], L ⊗[A]^L[Aprime])) := sorry

end

section

variable {A : Type u} [CommRing A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "MinusCpxA" => CochainComplex.minus (ModuleCat A)
local notation "BoundedCpxA" => CochainComplex.bounded (ModuleCat A)

-- Proof sketch: because `P` is bounded above and termwise finite free while `F` is bounded, each
-- degree of `Hom^•(P^•, F^•)` is a finite direct sum of copies of finitely presented terms of
-- `F`; finite presentation is stable under finite direct sums.
/-- If `P^•` is bounded above and termwise finite free, and `F^•` is bounded with finitely
presented terms, then every degree of `Hom^•(P^•, F^•)` is a finitely presented `A`-module. -/
theorem homComplex_term_finitePresentation_of_boundedAbove_of_bounded_of_termwiseFiniteFree
    (P F : CpxA)
    (hPbounded : MinusCpxA P)
    (hPfiniteFree : P.IsTermwiseFiniteFree)
    (hFbounded : BoundedCpxA F)
    (hFfinitePresentation : ∀ i : ℤ, Module.FinitePresentation A (F.X i)) :
    ∀ n : ℤ, Module.FinitePresentation A ((⟪P, F⟫).X n) := sorry

end

end CategoryTheory
