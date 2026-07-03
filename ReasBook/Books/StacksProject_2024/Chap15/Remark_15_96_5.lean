import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.AdicCompletion.Functoriality
import StacksProject_2024.Chap15.Lemma_15_96_2
import StacksProject_2024.Chap15.PrincipalIdeal

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open HomologicalComplex
open CochainComplex
open scoped BerthelotOgusInt

universe u v w

noncomputable section

variable {A : Type u} [CommRing A]

/- Domain-style sampling for the reduction owner:
- primary domain: reduction modulo an ideal of cochain complexes of `A`-modules, and the
  source-facing Berthelot-Ogus reduction `η_f(K^\bullet) / f η_f(K^\bullet)`;
- sampled owner declarations:
  `CochainComplex (ModuleCat A) ι`,
  `LinearMap.reduceModIdeal`,
  `ModuleCat.restrictScalars`,
  `BerthelotOgusInt.complex`;
- best owner abstraction:
  `core/canonical`: reduction modulo an ideal of a cochain complex, owned once by
    `CochainComplex.reduceModIdeal` together with its induced map
    `CochainComplex.reduceModIdealMap` and scalar-restricted view
    `CochainComplex.reduceModIdealA`;
  `source-facing`: the Berthelot-Ogus reduction owners
    `BerthelotOgusEtaReduction.complex` together with the quotient-ring comparison map
    `BerthelotOgusEtaReduction.toHomology`;
  `bridge/view`: the scalar-restricted `A`-linear view, the nonnegative-degree restriction and
  homology identifications for `CochainComplex.reduceModIdealA`, and the bounded-below
    comparison map `BerthelotOgusEtaReduction.Nat.toHomology`;
  `primitive data vs derived API`: the primitive data are the quotient terms and induced
  differentials. The Berthelot-Ogus reduction and the quotient-to-homology maps are derived from
  that owner construction, so the file should not keep parallel local bounded-below copies of the
  quotient-ring reduction complex or cocycle map. -/

namespace CochainComplex

/-- The degree-`i` differential on the reduction of a cochain complex modulo `I`. -/
private abbrev reduceModIdealDifferential
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) (i : ι) :
    ModuleCat.of (A ⧸ I) (K.X i ⧸ I • (⊤ : Submodule A (K.X i))) ⟶
      ModuleCat.of (A ⧸ I) (K.X (i + 1) ⧸ I • (⊤ : Submodule A (K.X (i + 1)))) :=
  ModuleCat.ofHom <| (K.d i (i + 1)).hom.reduceModIdeal I

-- Proof sketch: the reduced differential is induced from the differential of `K`, so two
-- successive reduced differentials factor through the quotient of `d ≫ d = 0`.
/-- Two successive reduced differentials compose to zero. -/
private theorem reduceModIdealDifferential_sq
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) (i : ι) :
    reduceModIdealDifferential I K i ≫ reduceModIdealDifferential I K (i + 1) = 0 := sorry

/-- The cochain complex obtained by reducing every term of `K` modulo `I`, viewed over the
quotient ring `A ⧸ I`. -/
abbrev reduceModIdeal
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) :
    CochainComplex (ModuleCat.{v} (A ⧸ I)) ι :=
  let _ : DecidableEq ι := Classical.decEq ι
  CochainComplex.of
    (fun i ↦ ModuleCat.of (A ⧸ I) (K.X i ⧸ I • (⊤ : Submodule A (K.X i))))
    (fun i ↦ reduceModIdealDifferential I K i)
    (fun i ↦ reduceModIdealDifferential_sq I K i)

/-- The scalar-restricted `A`-linear view of `K / IK`. -/
abbrev reduceModIdealA
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{v} A) ι) :
    CochainComplex (ModuleCat.{v} A) ι :=
  ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ι)).obj
    (reduceModIdeal I K)

/-- The morphism induced on reduced complexes by a morphism of cochain complexes. -/
abbrev reduceModIdealMap
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    {K L : CochainComplex (ModuleCat.{v} A) ι} (I : Ideal A) (φ : K ⟶ L) :
    reduceModIdeal I K ⟶ reduceModIdeal I L where
  f i := ModuleCat.ofHom <| (φ.f i).hom.reduceModIdeal I
  comm' i j hij := by
    rcases hij with rfl
    sorry

/-- The scalar-restricted `A`-linear view of the morphism induced on reduced complexes. -/
abbrev reduceModIdealAMap
    {ι : Type w} [AddRightCancelSemigroup ι] [One ι]
    {K L : CochainComplex (ModuleCat.{v} A) ι} (I : Ideal A) (φ : K ⟶ L) :
    reduceModIdealA I K ⟶ reduceModIdealA I L :=
  ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
      (ComplexShape.up ι)).map
    (reduceModIdealMap I φ)

/-- The quotient submodule `IM` is preserved by the standard degree identification
`(M.extend embeddingUpNat).X i ≅ M.X i`. -/
private theorem smul_top_extendXIso_map
    (I : Ideal A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (I • (⊤ : Submodule A ((M.extend ComplexShape.embeddingUpNat).X (i : ℤ)))).map
        (M.extendXIso ComplexShape.embeddingUpNat (by simp)).toLinearEquiv.toLinearMap =
      I • (⊤ : Submodule A (M.X i)) := by
  sorry

/-- Restricting the reduction of `M.extend ComplexShape.embeddingUpNat` to nonnegative degrees
recovers the reduction of `M`. -/
private noncomputable def reduceModIdealARestrictionIso
    (I : Ideal A) (M : NatModuleCochainComplex A) :
    (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).restriction
        (ComplexShape.embeddingUpIntGE 0) ≅
      reduceModIdealA I M :=
  Hom.isoOfComponents
    (fun i ↦
      ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).restrictionXIso
          (ComplexShape.embeddingUpIntGE 0) (by simp)) ≪≫
        LinearEquiv.toModuleIso
          (Submodule.Quotient.equiv
            (I • (⊤ : Submodule A ((M.extend ComplexShape.embeddingUpNat).X (i : ℤ))))
            (I • (⊤ : Submodule A (M.X i)))
            (M.extendXIso ComplexShape.embeddingUpNat (by simp)).toLinearEquiv
            (smul_top_extendXIso_map I M i)))
    (by
      sorry)

/-- The degree `-1` term of the reduction of an extended nonnegative cochain complex is zero. -/
private theorem reduceModIdealA_isZero_negOne
    (I : Ideal A) (M : NatModuleCochainComplex A) :
    CategoryTheory.Limits.IsZero
      ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X (-1)) := by
  let hzero : CategoryTheory.Limits.IsZero ((M.extend ComplexShape.embeddingUpNat).X (-1 : ℤ)) :=
    M.isZero_extend_X ComplexShape.embeddingUpNat (-1) (by
      intro i hi
      change (i : ℤ) = -1 at hi
      have h : (0 : ℤ) ≤ (i : ℤ) := by
        exact_mod_cast Nat.zero_le i
      rw [hi] at h
      norm_num at h)
  letI : Subsingleton ((M.extend ComplexShape.embeddingUpNat).X (-1 : ℤ)) :=
    ModuleCat.subsingleton_of_isZero hzero
  letI : Subsingleton ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).X (-1)) := by
    change Subsingleton
      (((M.extend ComplexShape.embeddingUpNat).X (-1 : ℤ)) ⧸
        I • (⊤ : Submodule A ((M.extend ComplexShape.embeddingUpNat).X (-1 : ℤ))))
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

/-- The canonical homology identification between the reduction of
`M.extend ComplexShape.embeddingUpNat` and the reduction of `M`. -/
noncomputable abbrev reduceModIdealAHomologyIso
    (I : Ideal A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).homology (i : ℤ) ≅
      (reduceModIdealA I M).homology i :=
  match i with
  | 0 =>
      have h0 : (ComplexShape.embeddingUpIntGE 0).f 0 = (0 : ℤ) := by
        simp [ComplexShape.embeddingUpIntGE]
      have h1 : (ComplexShape.embeddingUpIntGE 0).f 1 = (1 : ℤ) := by
        simp [ComplexShape.embeddingUpIntGE]
      have hnext : (ComplexShape.up ℤ).next (0 : ℤ) = (1 : ℤ) := by
        simpa using (CochainComplex.next ℤ (0 : ℤ))
      let e₀ :
          (reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).homology (0 : ℤ) ≅
            ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).restriction
              (ComplexShape.embeddingUpIntGE 0)).homology 0 :=
        (((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).isoHomologyπ
              (-1) 0 (by simpa using (CochainComplex.prev ℤ (0 : ℤ)))
              (by
                simpa using
                  (reduceModIdealA_isZero_negOne I M).eq_of_src
                    ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).d (-1) 0) 0)).symm ≪≫
            ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).restrictionCyclesIso
              (ComplexShape.embeddingUpIntGE 0) 0 1 (by simp) h0 h1 hnext).symm) ≪≫
          CochainComplex.isoHomologyπ₀
            ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).restriction
              (ComplexShape.embeddingUpIntGE 0))
      e₀ ≪≫ homologyMapIso (reduceModIdealARestrictionIso I M) 0
  | n + 1 =>
      have hi : (ComplexShape.embeddingUpIntGE 0).f n = (n : ℤ) := by
        simp [ComplexShape.embeddingUpIntGE]
      have hj : (ComplexShape.embeddingUpIntGE 0).f (n + 1) = ((n + 1 : ℕ) : ℤ) := by
        simp [ComplexShape.embeddingUpIntGE]
      have hk : (ComplexShape.embeddingUpIntGE 0).f (n + 2) = ((n + 2 : ℕ) : ℤ) := by
        simp [ComplexShape.embeddingUpIntGE]
      have hprev : (ComplexShape.up ℤ).prev (((n + 1 : ℕ) : ℤ)) = (n : ℤ) := by
        simp
      have hnext : (ComplexShape.up ℤ).next (((n + 1 : ℕ) : ℤ)) = ((n + 2 : ℕ) : ℤ) := by
        calc
          (ComplexShape.up ℤ).next (((n + 1 : ℕ) : ℤ)) = (((n + 1 : ℕ) : ℤ) + 1) :=
            CochainComplex.next ℤ (((n + 1 : ℕ) : ℤ))
          _ = ((n + 2 : ℕ) : ℤ) := by
            exact_mod_cast (show n + 1 + 1 = n + 2 by omega)
      ((reduceModIdealA I (M.extend ComplexShape.embeddingUpNat)).restrictionHomologyIso
          (ComplexShape.embeddingUpIntGE 0) n (n + 1) (n + 2) (by simp) (by simp)
          hi hj hk hprev hnext
        ).symm ≪≫
        homologyMapIso (reduceModIdealARestrictionIso I M) (n + 1)

end CochainComplex

namespace BerthelotOgusEtaReduction

open BerthelotOgusInt

/-- The canonical inclusion `η_f(K^\bullet) ⟶ K^\bullet`. -/
private def etaInclusion (f : A) (K : ModuleComplex A) :
    η[f] K ⟶ K where
  f i := ModuleCat.ofHom (degreeSubmodule f K i).subtype
  comm' i j hij := by
    rcases hij with rfl
    sorry

/-- The bounded-below `ℤ`-indexed bridge reduction
`η_f(K^\bullet) / f η_f(K^\bullet)` over `A ⧸ (f)`. -/
abbrev complex (f : A) (K : ModuleComplex A) :
    ModuleComplex (A ⧸ principalIdeal f) :=
  reduceModIdeal (principalIdeal f) (BerthelotOgusInt.complex f K)

private abbrev toRawReductionLinear
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    (complex f K).X i →ₗ[A ⧸ principalIdeal f]
      (reduceModIdeal (principalIdeal f) K).X i :=
  ((reduceModIdealMap (principalIdeal f) (etaInclusion f K)).f i).hom

-- Proof sketch: an element of `η_f(K)^i` reduces to a cocycle in `K^i / fK^i` because its
-- differential is already divisible by `f` in degree `i + 1`.
/-- The canonical quotient map from the reduced Berthelot-Ogus term to the reduced complex lands in
cycles. -/
private theorem toRawReductionLinear_comp_d_eq_zero
    (f : A) (K : ModuleComplex A) (i : ℤ) :
    ModuleCat.ofHom (toRawReductionLinear f K i) ≫
        (reduceModIdeal (principalIdeal f) K).d i (i + 1) =
      0 := sorry

/-- The canonical map
`(η_f(K^\bullet)^i / f η_f(K^\bullet)^i) ⟶ Z^i(K^\bullet / f K^\bullet)`. -/
abbrev toCycles (f : A) (K : ModuleComplex A) (i : ℤ) :
    (complex f K).X i ⟶ (reduceModIdeal (principalIdeal f) K).cycles i :=
  (reduceModIdeal (principalIdeal f) K).liftCycles'
    (ModuleCat.ofHom (toRawReductionLinear f K i))
    (i + 1) (by simp) (toRawReductionLinear_comp_d_eq_zero f K i)

/-- The canonical map
`(η_f(K^\bullet)^i / f η_f(K^\bullet)^i) ⟶ H^i(K^\bullet / f K^\bullet)`. -/
abbrev toHomology (f : A) (K : ModuleComplex A) (i : ℤ) :
    (complex f K).X i ⟶ (reduceModIdeal (principalIdeal f) K).homology i :=
  toCycles f K i ≫ (reduceModIdeal (principalIdeal f) K).homologyπ i

namespace Nat

/-- The canonical inclusion `η_f(M^\bullet) ⟶ M^\bullet`. -/
private def etaInclusion (f : A) (M : NatModuleCochainComplex A) :
    η[f] M ⟶ M where
  f i := ModuleCat.ofHom (etaFDegreeSubmodule f M i).subtype
  comm' i j hij := by
    rcases hij with rfl
    sorry

private abbrev toRawReduction
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA (principalIdeal f) (η[f] M)).X i ⟶
      (reduceModIdealA (principalIdeal f) M).X i :=
  (reduceModIdealAMap (principalIdeal f) (etaInclusion f M)).f i

/-- The scalar-restricted `A`-linear quotient map induced by the canonical inclusion
`η_f(M^\bullet) ⟶ M^\bullet`. -/
private abbrev toRawReductionLinear
    (f : A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA (principalIdeal f) (η[f] M)).X i →ₗ[A]
      (reduceModIdealA (principalIdeal f) M).X i :=
  (toRawReduction f M i).hom

/-- The canonical bounded-below map
`(η_f(M^\bullet)^i / f η_f(M^\bullet)^i) ⟶ H^i(M^\bullet / f M^\bullet)`. -/
abbrev toHomology (f : A) (M : NatModuleCochainComplex A) (i : ℕ) :
    (reduceModIdealA (principalIdeal f) (η[f] M)).X i ⟶
      (reduceModIdealA (principalIdeal f) M).homology i :=
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) (η[f] M)).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  let _ : Module A ↑((reduceModIdeal (principalIdeal f) M).X i) :=
    Module.compHom _ (Ideal.Quotient.mk (principalIdeal f))
  (reduceModIdealA (principalIdeal f) M).liftCycles'
      (toRawReduction f M i)
      (i + 1) (by simp)
      (by
        -- This is the scalar-restricted bounded-below form of the owner cocycle calculation.
        sorry) ≫
    (reduceModIdealA (principalIdeal f) M).homologyπ i

end Nat

end BerthelotOgusEtaReduction
