import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_6
import LinearRepresentations_Serre_1977.Chap14.Exercise_14_14_4_6.EndomorphismReductionTransport
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.FiniteLevelAveraging
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.Index
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.TransitionLiftBridge
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_2_1
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.ResidueFieldLift
import LinearRepresentations_Serre_1977.Chap15.Proposition_15_15_5_1

open scoped MonoidAlgebra TensorProduct
open Polynomial

universe u v w x y

section

variable {A : Type u} [CommRing A] [IsLocalRing A]

namespace Representation

section

variable {p : ℕ}
variable [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type v} [Group G] [Finite G]
variable {E : Type w} [AddCommGroup E] [Module A E] [Module.Free A E] [Module.Finite A E]

local notation "𝔪" => IsLocalRing.maximalIdeal A
local notation "A⧸𝔪^(" n ")" => A ⧸ (𝔪 ^ n)
local notation "E⧸𝔪^(" n ")E" => E ⧸ ((𝔪 ^ n) • (⊤ : Submodule A E))

/-- Helper for Exercise 15-15.5-3: each single operator of the level-`n` representation admits an
upstairs linear lift along the transition `E / 𝔪^(n+1) E → E / 𝔪^n E`. -/
private theorem exists_groupElementLift_over_factorPowSucc
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (g : G) :
    letI : Module (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ))E) :=
      Module.compHom (E⧸𝔪^((n : ℕ))E) (Ideal.Quotient.factorPowSucc 𝔪 (n : ℕ))
    ∃ F : Module.End (A⧸𝔪^((n : ℕ) + 1)) (E⧸𝔪^((n : ℕ) + 1)E),
      maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n ∘ₗ F =
        downstairs_endomorphism_over_factorPowSucc (A := A) (E := E) n (ρn g) ∘ₗ
          maximalIdealPowTransition_linear_over_factorPowSucc (A := A) (E := E) n := by
  -- Reuse the public bridge theorem so the finite-level correction route no longer depends on a
  -- theorem-local private wrapper.
  simpa using
    (existsGroupElementLiftOverFactorPowSucc (A := A) (E := E) n ρn g)

-- Proof sketch: the obstruction to extending `ρn` from level `n` to level `n + 1` lies in a
-- second cohomology group of `G` with coefficients in `End(E / 𝔪E)`, and that cohomology group
-- vanishes when `|G|` is prime to `p`.
/-- Exercise 15-15.5-3 (1): if `|G|` is prime to `p`, every representation of `G` on the
`n`-th reduction of a finite free `A`-module `E` with `n ≥ 1` lifts to a representation on the
next reduction `E / 𝔪^(n+1) E`. -/
theorem exists_lift_of_maximalIdealPowLevel
    (hG : ¬ p ∣ Nat.card G)
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E)) :
    ∃ ρn1 : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E),
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)) := by
  -- Route correction: the defect now packages cleanly into the public correction algebra, so the
  -- target theorem is reduced to the single averaged `H²` closing step in the support file.
  simpa using
    Representation.averagedCorrectionProducesLift
      (A := A) (p := p) (G := G) (E := E) hG n ρn

-- Proof sketch: the vanishing of the first cohomology group identifies any two lifts as differing
-- by a coboundary, which is exactly conjugation by an automorphism reducing to the identity modulo
-- `𝔪^n`.
/-- Exercise 15-15.5-3 (2): if `|G|` is prime to `p`, two lifts of the same representation on the
`n`-th reduction of a finite free `A`-module are conjugate on `E / 𝔪^(n+1) E` by an automorphism
congruent to the identity modulo `𝔪^n`. -/
theorem lift_of_maximalIdealPowLevel_unique_up_to_conjugation
    (hG : ¬ p ∣ Nat.card G)
    (n : ℕ+)
    (ρn : Representation (A⧸𝔪^((n : ℕ))) G (E⧸𝔪^((n : ℕ))E))
    (ρn1 ρn1' : Representation (A⧸𝔪^((n : ℕ) + 1)) G (E⧸𝔪^((n : ℕ) + 1)E))
    (hρn1 :
      (Representation.restrictScalars A ρn1).IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ)))
    (hρn1' :
      (Representation.restrictScalars A ρn1').IsIntertwiningMap
        (Representation.restrictScalars A ρn)
        (Submodule.factorPowSucc 𝔪 E (n : ℕ))) :
    let π := Submodule.factorPowSucc 𝔪 E (n : ℕ)
    ∃ u : ρn1.Equiv ρn1',
      π ∘ₗ (u.toLinearMap.restrictScalars A) = π := by
  -- Route correction: the comparison terms now package cleanly into the public correction
  -- algebra, so the target theorem is reduced to the single averaged `H¹` closing step in the
  -- support file.
  simpa using
    Representation.comparisonCoboundaryProducesConjugator
      (A := A) (p := p) (G := G) (E := E) hG n ρn ρn1 ρn1' hρn1 hρn1'

end

noncomputable section

variable [HenselianLocalRing A]

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ}
variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type x} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
  [FiniteDimensional (IsLocalRing.ResidueField A) V]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Exercise 15-15.5-3: in a Henselian pair, idempotents lift from a quotient ring to
the original commutative ring. -/
private theorem quotient_idempotent_lift_of_henselianPair
    {S : Type*} [CommRing S] (I : Ideal S) [HenselianRing S I]
    (eBar : S ⧸ I) (heBar : IsIdempotentElem eBar) :
    ∃ e : S, IsIdempotentElem e ∧ Ideal.Quotient.mk I e = eBar := by
  obtain ⟨e0, he0⟩ := Ideal.Quotient.mk_surjective eBar
  let fS : Polynomial S := Polynomial.X ^ 2 - Polynomial.X
  have hEval : fS.eval e0 ∈ I := by
    have hzero : Ideal.Quotient.mk I (e0 ^ 2 - e0) = 0 := by
      rw [map_sub, map_pow, he0]
      exact sub_eq_zero.mpr (by simpa [pow_two] using IsIdempotentElem.eq heBar)
    have hmem : e0 ^ 2 - e0 ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    simpa [fS, pow_two] using hmem
  have hDeriv : IsUnit (Ideal.Quotient.mk I (fS.derivative.eval e0)) := by
    have hunit :
        IsUnit (((Polynomial.X ^ 2 - Polynomial.X : Polynomial (S ⧸ I)).derivative).eval eBar) :=
      derivative_eval_X_sq_sub_X_isUnit_of_isIdempotentElem heBar
    convert hunit using 1
    simp [fS, he0]
  have hMonic : fS.Monic := by
    have hfactor : fS = Polynomial.X * (Polynomial.X - 1) := by
      simp [fS]
      ring
    rw [hfactor]
    exact (Polynomial.monic_X (R := S)).mul (Polynomial.monic_X_sub_C (1 : S))
  obtain ⟨e, heRoot, heMem⟩ :=
    HenselianRing.is_henselian (R := S) (I := I) fS hMonic e0 hEval hDeriv
  refine ⟨e, ?_, ?_⟩
  · rw [IsIdempotentElem]
    exact sub_eq_zero.mp <| by
      simpa [fS, Polynomial.IsRoot, pow_two] using heRoot
  · have hquot : Ideal.Quotient.mk I (e - e0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr heMem
    have heq : Ideal.Quotient.mk I e = Ideal.Quotient.mk I e0 := by
      exact sub_eq_zero.mp <| by
        simpa [map_sub] using hquot
    exact heq.trans he0

/-- Helper for Exercise 15-15.5-3: a Henselian-pair structure on the restricted singleton
reduction kernel lifts the canonical reduced idempotent generator. -/
private theorem singletonAdjoin_lifts_idempotent_generator_of_henselianPair
    {B : Type*} [Ring B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
    {Bbar : Type*} [Ring Bbar] [Algebra A Bbar] [Algebra k Bbar]
    [IsScalarTower A k Bbar]
    (red : B →ₐ[A] Bbar)
    {u0 : B} {uBar : Bbar} (hu0 : red u0 = uBar)
    (huBar : IsIdempotentElem uBar) :
    let S := Algebra.adjoin A ({u0} : Set B)
    let redS := adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
    HenselianRing S (RingHom.ker redS) →
      ∃ u : S,
        IsIdempotentElem u ∧
          redS u =
            (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
              Algebra.adjoin A ({uBar} : Set Bbar)) := by
  dsimp
  intro hPair
  let S := Algebra.adjoin A ({u0} : Set B)
  let Sbar := Algebra.adjoin A ({uBar} : Set Bbar)
  let redS : S →ₐ[A] Sbar :=
    adjoin_singleton_codRestrict (A := A) (B := B) (Bbar := Bbar) red hu0
  let I : Ideal S := RingHom.ker redS
  let a0 : S := ⟨u0, Algebra.self_mem_adjoin_singleton A u0⟩
  letI : HenselianRing S I := hPair
  have hEval : a0 * a0 - a0 ∈ I := by
    change a0 * a0 - a0 ∈ RingHom.ker redS
    rw [RingHom.mem_ker]
    apply Subtype.ext
    simpa [S, Sbar, redS, a0, adjoin_singleton_codRestrict_apply, hu0, IsIdempotentElem,
      sub_eq_zero] using huBar.eq
  have hIdemQuot : IsIdempotentElem (Ideal.Quotient.mk I a0) := by
    rw [IsIdempotentElem]
    have hzero : Ideal.Quotient.mk I (a0 * a0 - a0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hEval
    have hquotSub :
        Ideal.Quotient.mk I a0 * Ideal.Quotient.mk I a0 -
          Ideal.Quotient.mk I a0 = 0 := by
      simpa [map_sub, map_mul] using hzero
    exact sub_eq_zero.mp hquotSub
  obtain ⟨u, hu, huQuot⟩ :=
    quotient_idempotent_lift_of_henselianPair
      (S := S) I (Ideal.Quotient.mk I a0) hIdemQuot
  use u
  constructor
  · exact hu
  · have hquot : Ideal.Quotient.mk I (u - a0) = 0 := by
      simpa [map_sub] using sub_eq_zero.mpr huQuot
    have hmem : u - a0 ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hquot
    have hred : redS u = redS a0 := by
      have hsub : redS u - redS a0 = 0 := by
        simpa [map_sub, I] using RingHom.mem_ker.mp hmem
      exact sub_eq_zero.mp hsub
    have ha0Red :
        redS a0 =
          (⟨uBar, Algebra.self_mem_adjoin_singleton A uBar⟩ :
            Algebra.adjoin A ({uBar} : Set Bbar)) := by
      apply Subtype.ext
      simpa [S, Sbar, redS, a0, adjoin_singleton_codRestrict_apply] using hu0
    exact hred.trans ha0Red

/-- Helper for Exercise 15-15.5-3: a singleton-generated subalgebra of a module-finite algebra is
module-finite over the base. -/
private theorem singletonAdjoinModuleFinite
    {B : Type*} [Ring B] [Algebra A B] [Module.Finite A B] (u0 : B) :
    Module.Finite A (Algebra.adjoin A ({u0} : Set B)) := by
  exact Module.Finite.iff_fg.mpr
    (IsIntegral.fg_adjoin_singleton (IsIntegral.of_finite A u0))

/-- Helper for Exercise 15-15.5-3: `HenselianLocalRing.TFAE` lifts points of standard etale
`A`-algebras from the residue field back to `A`. -/
private theorem standardEtale_lift_of_henselianLocal
    {T : Type u} [CommRing T] [Algebra A T] [Algebra.IsStandardEtale A T]
    (φbar : T →ₐ[A] k) :
    ∃ φ : T →ₐ[A] A, (Algebra.ofId A k).comp φ = φbar := by
  classical
  let P : StandardEtalePresentation A T :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let xbar : k := φbar P.x
  have hxbar : P.P.HasMap xbar := P.hasMap.map φbar
  have hroot : Polynomial.aeval xbar P.f = 0 := hxbar.1
  have hderiv_ne : Polynomial.aeval xbar P.f.derivative ≠ 0 :=
    hxbar.isUnit_derivative_f.ne_zero
  have hLift :
      ∃ a : A, P.f.IsRoot a ∧ IsLocalRing.residue A a = xbar := by
    have hTFAE := HenselianLocalRing.TFAE A
    have hresidueLift :
        ∀ f : A[X], f.Monic → ∀ a₀ : k,
          Polynomial.aeval a₀ f = 0 →
            Polynomial.aeval a₀ (Polynomial.derivative f) ≠ 0 →
              ∃ a : A, f.IsRoot a ∧ IsLocalRing.residue A a = a₀ := by
      exact (List.TFAE.out hTFAE 0 1).mp (show HenselianLocalRing A from inferInstance)
    exact hresidueLift P.f P.monic_f xbar hroot hderiv_ne
  obtain ⟨a, haRoot, haResidue⟩ := hLift
  have hgUnit : IsUnit (Polynomial.aeval a P.g) := by
    apply (IsLocalRing.notMem_maximalIdeal (R := A)).mp
    intro hgmem
    have hzero :
        IsLocalRing.residue A (Polynomial.aeval a P.g) = 0 :=
      (IsLocalRing.residue_eq_zero_iff (R := A) _).2 hgmem
    have hmap :
        IsLocalRing.residue A (Polynomial.aeval a P.g) =
          Polynomial.aeval xbar P.g := by
      rw [← haResidue]
      simpa [IsLocalRing.ResidueField.algebraMap_eq] using
        (Polynomial.aeval_algHom_apply (Algebra.ofId A k) a P.g).symm
    exact hxbar.2.ne_zero (hmap ▸ hzero)
  have haMap : P.P.HasMap a := by
    constructor
    · simpa [Polynomial.IsRoot] using haRoot
    · exact hgUnit
  let φP : P.P.Ring →ₐ[A] A := P.P.lift a haMap
  let φ : T →ₐ[A] A := φP.comp P.equivRing.toAlgHom
  refine ⟨φ, ?_⟩
  apply P.hom_ext
  change ((Algebra.ofId A k).comp φ) P.x = φbar P.x
  dsimp [φ, φP, xbar]
  simpa [P] using haResidue

/-- Helper for Exercise 15-15.5-3: points of etale finite-presentation algebras over the residue
field lift over a Henselian local base. -/
private theorem etale_lift_of_henselianLocal
    {T : Type u} [CommRing T] [Algebra A T] [Algebra.FinitePresentation A T]
    [Algebra.Etale A T]
    (φbar : T →ₐ[A] k) :
    ∃ φ : T →ₐ[A] A, (Algebra.ofId A k).comp φ = φbar := by
  classical
  let Q : Ideal T := RingHom.ker φbar.toRingHom
  haveI : Q.IsPrime := RingHom.ker_isPrime φbar.toRingHom
  have hEtaleAt : Algebra.IsEtaleAt A Q := by
    have hUniv : Algebra.etaleLocus A T = Set.univ :=
      (Algebra.etaleLocus_eq_univ_iff_etale (R := A) (A := T)).2
        (show Algebra.Etale A T from inferInstance)
    have hmem : (⟨Q, inferInstance⟩ : PrimeSpectrum T) ∈ Algebra.etaleLocus A T := by
      rw [hUniv]
      exact Set.mem_univ _
    exact (Algebra.mem_etaleLocus_iff (R := A) (A := T)).1 hmem
  obtain ⟨f, hfQ, hstd⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := A) (S := T) Q
  letI : Algebra.IsStandardEtale A (Localization.Away f) := hstd
  have hfunit : IsUnit (φbar f) := by
    have hf_ne_zero : φbar f ≠ 0 := by
      intro hfzero
      exact hfQ (by
        change φbar.toRingHom f = 0
        exact hfzero)
    exact (isUnit_iff_ne_zero).2 hf_ne_zero
  let φbarLoc : Localization.Away f →ₐ[A] k :=
    IsLocalization.liftAlgHom
      (M := Submonoid.powers f) (S := Localization.Away f) (f := φbar)
      (by
        intro y
        rcases y with ⟨y, n, rfl⟩
        simpa using hfunit.pow n)
  obtain ⟨ψ, hψ⟩ :=
    standardEtale_lift_of_henselianLocal (A := A) (T := Localization.Away f) φbarLoc
  let loc : T →ₐ[A] Localization.Away f :=
    IsScalarTower.toAlgHom A T (Localization.Away f)
  let φ : T →ₐ[A] A := ψ.comp loc
  refine ⟨φ, ?_⟩
  ext t
  have hψt :=
    congrArg (fun η : Localization.Away f →ₐ[A] k =>
      η (algebraMap T (Localization.Away f) t)) hψ
  change Algebra.ofId A k (φ t) = φbar t
  simpa [φ, loc, φbarLoc, IsLocalization.liftAlgHom_apply] using hψt

/-- Helper for Exercise 15-15.5-3: a coprime factorization of a monic polynomial over the residue
field lifts to a coprime factorization over a Henselian local base. -/
private theorem coprime_factorization_lift_of_henselianLocal
    (p : Polynomial A) (hp : p.Monic)
    (f g : Polynomial k) (hf : f.Monic) (hg : g.Monic)
    (H : p.map (algebraMap A k) = f * g) (Hcop : IsCoprime f g) :
    ∃ f' g' : Polynomial A,
      f'.Monic ∧ g'.Monic ∧ p = f' * g' ∧ IsCoprime f' g' ∧
        f'.map (algebraMap A k) = f ∧ g'.map (algebraMap A k) = g := by
  classical
  let m := f.natDegree
  let n := g.natDegree
  have hdeg : p.natDegree = m + n := by
    have h := congrArg Polynomial.natDegree H
    simpa [m, n, hf.natDegree_mul hg, hp.natDegree_map] using h
  let pM : MonicDegreeEq A p.natDegree := MonicDegreeEq.mk p hp rfl
  let fM : MonicDegreeEq k m := MonicDegreeEq.mk f hf rfl
  let gM : MonicDegreeEq k n := MonicDegreeEq.mk g hg rfl
  let U := Polynomial.UniversalCoprimeFactorizationRing m n hdeg pM
  let qbar :
      { q : MonicDegreeEq k m × MonicDegreeEq k n //
        (q.1 : Polynomial k) * (q.2 : Polynomial k) =
            (pM : Polynomial A).map (algebraMap A k) ∧
          IsCoprime (q.1 : Polynomial k) (q.2 : Polynomial k) } :=
    ⟨(fM, gM), by
      constructor
      · simpa [pM, fM, gM] using H.symm
      · simpa [fM, gM] using Hcop⟩
  let φbar : U →ₐ[A] k :=
    (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
      (R := A) (S := k) m n hdeg pM).symm
      qbar
  obtain ⟨φ, hφ⟩ :=
    etale_lift_of_henselianLocal (A := A) (T := U) φbar
  let q :=
    Polynomial.UniversalCoprimeFactorizationRing.homEquiv
      (R := A) (S := A) m n hdeg pM φ
  refine ⟨q.1.1.1, q.1.2.1, q.1.1.monic, q.1.2.monic, ?_, q.2.2, ?_, ?_⟩
  · simpa [pM] using q.2.1.symm
  · have hfmap :
        (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
          (R := A) (S := k) m n hdeg pM ((Algebra.ofId A k).comp φ)).1.1 =
          q.1.1.map (algebraMap A k) := by
        simpa [q] using
          (Polynomial.UniversalCoprimeFactorizationRing.homEquiv_comp_fst
            (R := A) (S := A) (T := k) m n hdeg pM φ (Algebra.ofId A k))
    have hfbar :
        (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
          (R := A) (S := k) m n hdeg pM φbar).1.1 = fM := by
      have hbar :
          Polynomial.UniversalCoprimeFactorizationRing.homEquiv
            (R := A) (S := k) m n hdeg pM φbar =
            qbar := by
        simpa [φbar] using
          (_root_.Equiv.apply_symm_apply
            (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
              (R := A) (S := k) m n hdeg pM) qbar)
      exact congrArg (fun q => q.1.1) hbar
    have hleft :
        (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
          (R := A) (S := k) m n hdeg pM ((Algebra.ofId A k).comp φ)).1.1 = fM := by
      simpa [hφ] using hfbar
    have hpoly :
        q.1.1.1.map (algebraMap A k) = f :=
      congrArg (fun q : MonicDegreeEq k m => (q : Polynomial k)) (hfmap.symm.trans hleft)
    simpa [fM, Polynomial.MonicDegreeEq.map] using hpoly
  · have hgmap :
        (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
          (R := A) (S := k) m n hdeg pM ((Algebra.ofId A k).comp φ)).1.2 =
          q.1.2.map (algebraMap A k) := by
        simpa [q] using
          (Polynomial.UniversalCoprimeFactorizationRing.homEquiv_comp_snd
            (R := A) (S := A) (T := k) m n hdeg pM φ (Algebra.ofId A k))
    have hgbar :
        (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
          (R := A) (S := k) m n hdeg pM φbar).1.2 = gM := by
      have hbar :
          Polynomial.UniversalCoprimeFactorizationRing.homEquiv
            (R := A) (S := k) m n hdeg pM φbar =
            qbar := by
        simpa [φbar] using
          (_root_.Equiv.apply_symm_apply
            (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
              (R := A) (S := k) m n hdeg pM) qbar)
      exact congrArg (fun q => q.1.2) hbar
    have hleft :
        (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
          (R := A) (S := k) m n hdeg pM ((Algebra.ofId A k).comp φ)).1.2 = gM := by
      simpa [hφ] using hgbar
    have hpoly :
        q.1.2.1.map (algebraMap A k) = g :=
      congrArg (fun q : MonicDegreeEq k n => (q : Polynomial k)) (hgmap.symm.trans hleft)
    simpa [gM, Polynomial.MonicDegreeEq.map] using hpoly

/-- Helper for Exercise 15-15.5-3: a Bezout decomposition of two annihilating factors produces
the corresponding idempotent projector by polynomial evaluation. -/
private theorem eval_bezout_factor_idempotent
    {R : Type*} [CommRing R]
    {S : Type*} [Ring S] [Algebra R S]
    (x : S) {F G a b : Polynomial R}
    (hbez : a * F + b * G = 1)
    (hann : Polynomial.aeval x (F * G) = 0) :
    IsIdempotentElem (Polynomial.aeval x (b * G)) := by
  let e : S := Polynomial.aeval x (b * G)
  let c : S := Polynomial.aeval x (a * F)
  have hsum : c + e = 1 := by
    have h := congrArg (fun q : Polynomial R => Polynomial.aeval x q) hbez
    simpa [c, e] using h
  have horth : e * c = 0 := by
    calc
      e * c = Polynomial.aeval x ((b * G) * (a * F)) := by
        simp [e, c]
      _ = Polynomial.aeval x ((a * b) * (F * G)) := by
        congr 1
        ring
      _ = 0 := by
        simp [hann]
  change e * e = e
  have hmul := congrArg (fun z : S => e * z) hsum
  have : e * c + e * e = e := by
    simpa [mul_add] using hmul
  simpa [horth] using this

/-- Helper for Exercise 15-15.5-3: on a nontrivial idempotent, the Bezout projector for
`(X - 1)^r` and `X^s` evaluates to the idempotent when both exponents are positive. -/
private theorem idempotent_projector_eval_eq_of_bezout
    {K : Type*} [Field K]
    {S : Type*} [Ring S] [Algebra K S]
    {u : S} (hu : IsIdempotentElem u)
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    {a b : Polynomial K}
    (hbez : a * ((Polynomial.X - 1) ^ r) + b * (Polynomial.X ^ s) = 1) :
    Polynomial.aeval u (b * Polynomial.X ^ s) = u := by
  let F : Polynomial K := (Polynomial.X - 1) ^ r
  let G : Polynomial K := Polynomial.X ^ s
  let e : S := Polynomial.aeval u (b * G)
  have hsum : Polynomial.aeval u (a * F) + e = 1 := by
    have h := congrArg (fun q : Polynomial K => Polynomial.aeval u q) hbez
    simpa [F, G, e] using h
  have hG : Polynomial.aeval u G = u := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hs)
    simp [G, IsIdempotentElem.pow_succ_eq n hu]
  have he_mul : e * u = e := by
    calc
      e * u = (Polynomial.aeval u b * Polynomial.aeval u G) * u := by
        simp [e]
      _ = (Polynomial.aeval u b * u) * u := by
        rw [hG]
      _ = Polynomial.aeval u b * (u * u) := by
        rw [mul_assoc]
      _ = Polynomial.aeval u b * u := by
        rw [hu.eq]
      _ = e := by
        simp [e, hG]
  have hF_mul : Polynomial.aeval u (a * F) * u = 0 := by
    have hFu : Polynomial.aeval u F * u = 0 := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hr)
      calc
        Polynomial.aeval u ((Polynomial.X - 1) ^ (n + 1) : Polynomial K) * u =
            ((u - 1) ^ (n + 1)) * u := by
          simp
        _ = ((u - 1) ^ n * (u - 1)) * u := by
          rw [pow_succ]
        _ = (u - 1) ^ n * ((u - 1) * u) := by
          rw [mul_assoc]
        _ = 0 := by
          simp [sub_mul, hu.eq]
    calc
      Polynomial.aeval u (a * F) * u =
          (Polynomial.aeval u a * Polynomial.aeval u F) * u := by
        simp
      _ = Polynomial.aeval u a * (Polynomial.aeval u F * u) := by
        rw [mul_assoc]
      _ = 0 := by
        rw [hFu, mul_zero]
  change e = u
  have hmul := congrArg (fun z : S => z * u) hsum
  have : Polynomial.aeval u (a * F) * u + e * u = u := by
    simpa [add_mul] using hmul
  calc
    e = 0 + e := by simp
    _ = Polynomial.aeval u (a * F) * u + e * u := by rw [hF_mul, he_mul]
    _ = u := this

/-- Helper for Exercise 15-15.5-3: the characteristic polynomial of left multiplication by an
idempotent is the product of the characteristic polynomials on its range and kernel. -/
private theorem charpoly_lmul_idempotent
    {K : Type*} [Field K]
    {B : Type*} [Ring B] [Algebra K B]
    [Module.Free K B] [Module.Finite K B]
    {e : B} (he : IsIdempotentElem e) :
    let L : Module.End K B := Algebra.lmul K B e
    L.charpoly =
      (Polynomial.X - 1) ^ Module.finrank K (LinearMap.range L) *
        Polynomial.X ^ Module.finrank K (LinearMap.ker L) := by
  classical
  let L : Module.End K B := Algebra.lmul K B e
  have hLidem : IsIdempotentElem L := by
    rw [IsIdempotentElem]
    ext x
    change e * (e * x) = e * x
    rw [← mul_assoc, he.eq]
  have hproj : LinearMap.IsProj (LinearMap.range L) L :=
    (LinearMap.isProj_range_iff_isIdempotentElem L).2 hLidem
  have hchar :
      L.charpoly =
        ((LinearMap.id : LinearMap.range L →ₗ[K] LinearMap.range L).prodMap
          (0 : LinearMap.ker L →ₗ[K] LinearMap.ker L)).charpoly := by
    conv_lhs =>
      rw [hproj.eq_conj_prodMap]
    exact LinearEquiv.charpoly_conj
      ((LinearMap.range L).prodEquivOfIsCompl (LinearMap.ker L) hproj.isCompl)
      ((LinearMap.id : LinearMap.range L →ₗ[K] LinearMap.range L).prodMap
        (0 : LinearMap.ker L →ₗ[K] LinearMap.ker L))
  have hidchar :
      (LinearMap.id : LinearMap.range L →ₗ[K] LinearMap.range L).charpoly =
        (Polynomial.X - 1) ^ Module.finrank K (LinearMap.range L) := by
    simpa [Module.End.one_eq_id] using
      (LinearMap.charpoly_one (R := K) (M := LinearMap.range L))
  have hzerochar :
      (0 : LinearMap.ker L →ₗ[K] LinearMap.ker L).charpoly =
        Polynomial.X ^ Module.finrank K (LinearMap.ker L) := by
    simpa using (LinearMap.charpoly_zero (R := K) (M := LinearMap.ker L))
  calc
    L.charpoly =
        ((LinearMap.id : LinearMap.range L →ₗ[K] LinearMap.range L).prodMap
          (0 : LinearMap.ker L →ₗ[K] LinearMap.ker L)).charpoly := hchar
    _ =
        (Polynomial.X - 1) ^ Module.finrank K (LinearMap.range L) *
          Polynomial.X ^ Module.finrank K (LinearMap.ker L) := by
      rw [LinearMap.charpoly_prodMap, hidchar, hzerochar]

/-- Helper for Exercise 15-15.5-3: idempotents lift along residue-field base change for finite
algebras over a Henselian local base. -/
private theorem finiteAlgebra_idempotent_lift_of_henselian
    {B : Type*} [Ring B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
    {Bbar : Type*} [Ring Bbar] [Algebra A Bbar] [Algebra k Bbar]
    [IsScalarTower A k Bbar]
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange k red.toLinearMap)
    (uBar : Bbar) (huBar : IsIdempotentElem uBar) :
    ∃ u : B, IsIdempotentElem u ∧ red u = uBar := by
  classical
  by_cases hzero : uBar = 0
  · refine ⟨0, ?_, ?_⟩
    · simp [IsIdempotentElem]
    · simp [hzero]
  by_cases hone : uBar = 1
  · refine ⟨1, ?_, ?_⟩
    · simp [IsIdempotentElem]
    · simp [hone]
  have hsurj : Function.Surjective red :=
    isBaseChange_surjective (A := A) (B := B) (Bbar := Bbar) red hred
  obtain ⟨u0, hu0⟩ := hsurj uBar
  letI : Module.Finite k (TensorProduct A k B) := inferInstance
  letI : Module.Finite k Bbar := Module.Finite.equiv hred.equiv
  letI : Module.Free k Bbar := hred.free
  let L0 : Module.End A B := Algebra.lmul A B u0
  let Lbar : Module.End k Bbar := Algebra.lmul k Bbar uBar
  let p : Polynomial A := L0.charpoly
  have hpMonic : p.Monic := by
    simpa [p] using LinearMap.charpoly_monic L0
  have hpEval : Polynomial.aeval u0 p = 0 := by
    simpa [p, L0] using (Algebra.aeval_self_charpoly_lmul (R := A) (M := B) u0)
  have hLbar_eq : hred.endHom L0 = Lbar := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    calc
      hred.endHom L0 (red y) = red (L0 y) := by
        simpa using hred.endHom_comp_apply L0 y
      _ = Lbar (red y) := by
        simp [L0, Lbar, hu0]
  have hchar_endHom : (hred.endHom L0).charpoly = p.map (algebraMap A k) := by
    let b := Module.Free.chooseBasis A B
    calc
      (hred.endHom L0).charpoly =
          ((LinearMap.toMatrix (hred.basis b) (hred.basis b)) (hred.endHom L0)).charpoly := by
        exact (LinearMap.charpoly_toMatrix (hred.endHom L0) (hred.basis b)).symm
      _ = (((LinearMap.toMatrix b b) L0).map (algebraMap A k)).charpoly := by
        rw [IsBaseChange.endHom_toMatrix (S := k) (M := B) hred b L0]
      _ = (((LinearMap.toMatrix b b) L0).charpoly).map (algebraMap A k) := by
        rw [Matrix.charpoly_map]
      _ = p.map (algebraMap A k) := by
        rw [LinearMap.charpoly_toMatrix L0 b]
  have hchar_red : p.map (algebraMap A k) = Lbar.charpoly :=
    hchar_endHom.symm.trans (congrArg LinearMap.charpoly hLbar_eq)
  let r : ℕ := Module.finrank k (LinearMap.range Lbar)
  let s : ℕ := Module.finrank k (LinearMap.ker Lbar)
  have hr : 0 < r := by
    have hmem : uBar ∈ LinearMap.range Lbar := by
      exact ⟨1, by simp [Lbar]⟩
    have hne : (⟨uBar, hmem⟩ : LinearMap.range Lbar) ≠ 0 := by
      intro h
      exact hzero (by simpa using congrArg Subtype.val h)
    letI : Nontrivial (LinearMap.range Lbar) := ⟨⟨⟨uBar, hmem⟩, 0, hne⟩⟩
    simpa [r] using (Module.finrank_pos (R := k) (M := LinearMap.range Lbar))
  have hs : 0 < s := by
    have hker : (1 - uBar) ∈ LinearMap.ker Lbar := by
      change Lbar (1 - uBar) = 0
      simp [Lbar, mul_sub, huBar.eq]
    have hne : (⟨1 - uBar, hker⟩ : LinearMap.ker Lbar) ≠ 0 := by
      intro h
      have hval : 1 - uBar = 0 := by
        simpa using congrArg Subtype.val h
      exact hone (sub_eq_zero.mp hval).symm
    letI : Nontrivial (LinearMap.ker Lbar) := ⟨⟨⟨1 - uBar, hker⟩, 0, hne⟩⟩
    simpa [s] using (Module.finrank_pos (R := k) (M := LinearMap.ker Lbar))
  let F : Polynomial k := (Polynomial.X - 1) ^ r
  let G : Polynomial k := Polynomial.X ^ s
  have hchar_lbar : Lbar.charpoly = F * G := by
    simpa [Lbar, F, G, r, s] using
      (charpoly_lmul_idempotent (K := k) (B := Bbar) huBar)
  have hFMonic : F.Monic := by
    simpa [F] using (Polynomial.monic_X_sub_C (1 : k)).pow r
  have hGMonic : G.Monic := by
    simpa [G] using (Polynomial.monic_X (R := k)).pow s
  have hcopBase : IsCoprime (Polynomial.X - (1 : Polynomial k)) (Polynomial.X : Polynomial k) := by
    have h :
        IsCoprime (Polynomial.X - Polynomial.C (1 : k))
          (Polynomial.X - Polynomial.C (0 : k)) :=
      Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by simp)
    simpa using h
  have hcop : IsCoprime F G := by
    simpa [F, G] using (hcopBase.pow (m := r) (n := s))
  have Hfac : p.map (algebraMap A k) = F * G :=
    hchar_red.trans hchar_lbar
  obtain ⟨F', G', hF', hG', hpFac, hcop', hFmap, hGmap⟩ :=
    coprime_factorization_lift_of_henselianLocal
      (A := A) p hpMonic F G hFMonic hGMonic Hfac hcop
  obtain ⟨a, b, hbez⟩ := hcop'
  let u : B := Polynomial.aeval u0 (b * G')
  have hann : Polynomial.aeval u0 (F' * G') = 0 := by
    simpa [← hpFac, p] using hpEval
  have hu : IsIdempotentElem u := by
    simpa [u] using
      (eval_bezout_factor_idempotent
        (R := A) (S := B) u0 (F := F') (G := G') (a := a) (b := b) hbez hann)
  have hFmap_res : Polynomial.map (IsLocalRing.residue A) F' = F := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using hFmap
  have hGmap_res : Polynomial.map (IsLocalRing.residue A) G' = G := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using hGmap
  have hbezbar :
      a.map (algebraMap A k) * F + b.map (algebraMap A k) * G = 1 := by
    have h := congrArg (Polynomial.map (algebraMap A k)) hbez
    simpa [Polynomial.map_add, Polynomial.map_mul, hFmap_res, hGmap_res,
      IsLocalRing.ResidueField.algebraMap_eq] using h
  have hprojbar :
      Polynomial.aeval uBar (b.map (algebraMap A k) * G) = uBar :=
    idempotent_projector_eval_eq_of_bezout
      (K := k) (S := Bbar) huBar hr hs hbezbar
  have hmap_bG :
      (b * G').map (algebraMap A k) = b.map (algebraMap A k) * G := by
    simpa [Polynomial.map_mul, hGmap_res, IsLocalRing.ResidueField.algebraMap_eq]
  have hred_evalA : red u = Polynomial.aeval uBar (b * G') := by
    calc
      red u = Polynomial.aeval (red u0) (b * G') := by
        simpa [u] using (Polynomial.aeval_algHom_apply red u0 (b * G')).symm
      _ = Polynomial.aeval uBar (b * G') := by
        rw [hu0]
  have hred_evalK :
      Polynomial.aeval uBar (b * G') =
        Polynomial.aeval uBar ((b * G').map (algebraMap A k)) := by
    exact (Polynomial.aeval_map_algebraMap k uBar (b * G')).symm
  refine ⟨u, hu, ?_⟩
  calc
    red u = Polynomial.aeval uBar (b * G') := hred_evalA
    _ = Polynomial.aeval uBar ((b * G').map (algebraMap A k)) := hred_evalK
    _ = Polynomial.aeval uBar (b.map (algebraMap A k) * G) := by
      rw [hmap_bG]
    _ = uBar := hprojbar

/-- Helper for Exercise 15-15.5-3: over a Henselian local base, idempotents lift along a
residue-field base change of a finite free algebra. -/
private theorem idempotent_lifts_along_residueFieldBaseChange_of_henselian
    {B : Type*} [Ring B] [Algebra A B] [Module.Free A B] [Module.Finite A B]
    {Bbar : Type*} [Ring Bbar] [Algebra A Bbar] [Algebra k Bbar]
    [IsScalarTower A k Bbar]
    (red : B →ₐ[A] Bbar)
    (hred : IsBaseChange k red.toLinearMap)
    (uBar : Bbar) (huBar : IsIdempotentElem uBar) :
    ∃ u : B, IsIdempotentElem u ∧ red u = uBar := by
  exact finiteAlgebra_idempotent_lift_of_henselian (A := A) red hred uBar huBar

/-- Helper for Exercise 15-15.5-3: `HenselianLocalRing.TFAE` gives a direct residue-field root
lifting principle for monic polynomials over `A`. -/
private theorem residueFieldRootLift_of_henselianLocal
    (f : Polynomial A) (hf : f.Monic) (a0 : k)
    (hroot : Polynomial.aeval a0 f = 0)
    (hderiv : Polynomial.aeval a0 (Polynomial.derivative f) ≠ 0) :
    ∃ a : A, f.IsRoot a ∧ IsLocalRing.residue A a = a0 := by
  have hTFAE := HenselianLocalRing.TFAE A
  have hresidueLift :
      ∀ g : Polynomial A, g.Monic → ∀ b0 : k,
        Polynomial.aeval b0 g = 0 →
          Polynomial.aeval b0 (Polynomial.derivative g) ≠ 0 →
            ∃ b : A, g.IsRoot b ∧ IsLocalRing.residue A b = b0 := by
    -- Read the residue-field formulation of Hensel's lemma directly from mathlib's TFAE package.
    exact (List.TFAE.out hTFAE 0 1).mp (show HenselianLocalRing A from inferInstance)
  -- Apply the packaged residue-field Hensel principle to the requested polynomial and point.
  exact hresidueLift f hf a0 hroot hderiv

/-- Helper for Exercise 15-15.5-3: the residue field carries its canonical `A`-module structure. -/
noncomputable local instance exercise_15_15_5_3_residueFieldModule : Module A k :=
  Module.compHom k (algebraMap A k)

/-- Helper for Exercise 15-15.5-3: the residue-field action is compatible with restriction of
scalars from `A`. -/
local instance exercise_15_15_5_3_residueFieldScalarTower : IsScalarTower A k k :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- Helper for Exercise 15-15.5-3: a residue-field vector space carries the canonical
restricted `A`-module structure. -/
noncomputable local instance exercise_15_15_5_3_targetModule : Module A V :=
  Module.compHom V (algebraMap A k)

/-- Helper for Exercise 15-15.5-3: the restricted `A`-action on `V` is compatible with the
given `k`-action. -/
local instance exercise_15_15_5_3_targetScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- Helper for Exercise 15-15.5-3: every residue-field lift is surjective on the underlying
module. -/
private theorem residue_field_lift_surjective
    (ρk : Representation k G V)
    {P : Type y} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    {ρA : Representation A G P}
    {red : P →ₗ[A] V}
    (hred : IsResidueFieldLift ρk ρA red) :
    Function.Surjective red := by
  intro x
  -- Write `x` through the canonical base-change equivalence and then lift that pure tensor.
  obtain ⟨t, rfl⟩ := hred.1.equiv.surjective x
  have hres : Function.Surjective (algebraMap A k) := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using IsLocalRing.residue_surjective
  obtain ⟨y, hy⟩ := TensorProduct.mk_surjective (R := A) (S := k) (M := P) hres t
  have heq : hred.1.equiv (1 ⊗ₜ[A] y) = (1 : k) • red y := by
    simpa using hred.1.equiv_tmul (1 : k) y
  have hyt : (1 ⊗ₜ[A] y : TensorProduct A k P) = t := by
    simpa using hy
  have hyred : red y = hred.1.equiv (1 ⊗ₜ[A] y) := by
    calc
      red y = (1 : k) • red y := by simp
      _ = hred.1.equiv (1 ⊗ₜ[A] y) := by simpa using heq.symm
  refine ⟨y, ?_⟩
  exact hyred.trans (congrArg hred.1.equiv hyt)

/-- Helper for Exercise 15-15.5-3: two free lifts of the same residue representation are
connected by an `A[G]`-linear equivalence whose reduction equation is exactly the identity. -/
private theorem exact_groupAlgebra_linearEquiv_of_common_reduction
    {P : Type y} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    [Module.Projective A[G] P] [Module.Free A P] [Module.Finite A P]
    {Pbar : Type x} [AddCommGroup Pbar] [Module k Pbar] [Module A Pbar]
    [IsScalarTower A k Pbar] [Module k[G] Pbar] [IsScalarTower k k[G] Pbar]
    {f : P →ₗ[A] Pbar}
    (hf : f.IsResidueFieldReduction G)
    {P' : Type y} [AddCommGroup P'] [Module A P'] [Module A[G] P'] [IsScalarTower A A[G] P']
    [Module.Projective A[G] P'] [Module.Free A P'] [Module.Finite A P']
    {f' : P' →ₗ[A] Pbar}
    (hf' : f'.IsResidueFieldReduction G) :
    ∃ e : P ≃ₗ[A[G]] P',
      f'.comp (e.toLinearMap.restrictScalars A) = f := by
  letI : Module A[G] Pbar :=
    Module.compHom Pbar (MonoidAlgebra.mapRingHom G (algebraMap A k))
  letI : IsScalarTower A A[G] Pbar :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A k))
            (MonoidAlgebra.single (1 : G) a) • x =
          a • x
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
            algebraMap k k[G] (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
            = (IsLocalRing.residue A a) • x := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k a x)
  let fGA : P →ₗ[A[G]] Pbar :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := hf.map_smul_restricted_groupAlgebra }
  let f'GA : P' →ₗ[A[G]] Pbar :=
    { toFun := f'
      map_add' := f'.map_add
      map_smul' := hf'.map_smul_restricted_groupAlgebra }
  -- Lift the chosen reduced comparison and its inverse across the two reduction maps.
  obtain ⟨w, hw⟩ :=
    Module.projective_lifting_property
      f'GA fGA hf'.surjective
  obtain ⟨w', hw'⟩ :=
    Module.projective_lifting_property
      fGA f'GA hf.surjective
  let u : Module.End A P :=
    (w'.restrictScalars A).comp (w.restrictScalars A)
  have hu_red : hf.1.endHom u = LinearMap.id := by
    -- Reduce the lifted composite and collapse it with the common reduction map.
    apply hf.1.algHom_ext'
    ext x
    have hwx : f' (w x) = f x := by
      have hwx' := LinearMap.congr_fun hw x
      simpa [fGA, f'GA] using hwx'
    calc
      (hf.1.endHom u) (f x) = f (w' (w x)) := by
        simpa [u] using hf.1.endHom_comp_apply u x
      _ = f' (w x) := by
        have hw'x := LinearMap.congr_fun hw' (w x)
        simpa [fGA, f'GA] using hw'x
      _ = f x := by rw [hwx]
      _ = f x := by simp
      _ = (LinearMap.id : Pbar →ₗ[k] Pbar) (f x) := rfl
  let u' : Module.End A P' :=
    (w.restrictScalars A).comp (w'.restrictScalars A)
  have hu'_red : hf'.1.endHom u' = LinearMap.id := by
    -- The same calculation on the other side shows that the symmetric composite also reduces to
    -- the identity.
    apply hf'.1.algHom_ext'
    ext x
    have hw'x : f (w' x) = f' x := by
      have hw'x' := LinearMap.congr_fun hw' x
      simpa [fGA, f'GA] using hw'x'
    calc
      (hf'.1.endHom u') (f' x) = f' (w (w' x)) := by
        simpa [u'] using hf'.1.endHom_comp_apply u' x
      _ = f (w' x) := by
        have hwx := LinearMap.congr_fun hw (w' x)
        simpa [fGA, f'GA] using hwx
      _ = f' x := by rw [hw'x]
      _ = f' x := by simp
      _ = (LinearMap.id : Pbar →ₗ[k] Pbar) (f' x) := rfl
  have hu_unit : IsUnit u :=
    hf.endomorphism_isUnit_of_endHom_eq_id u hu_red
  have hu'_unit : IsUnit u' :=
    hf'.endomorphism_isUnit_of_endHom_eq_id u' hu'_red
  have hu_bij : Function.Bijective u :=
    (Module.End.isUnit_iff u).mp hu_unit
  have hu'_bij : Function.Bijective u' :=
    (Module.End.isUnit_iff u').mp hu'_unit
  have hw_injective : Function.Injective w := by
    intro x y hxy
    apply hu_bij.1
    simpa [u, hxy]
  have hw_surjective : Function.Surjective w := by
    intro y
    rcases hu'_bij.2 y with ⟨z, hz⟩
    refine ⟨w' z, ?_⟩
    simpa [u'] using hz
  refine ⟨LinearEquiv.ofBijective w ⟨hw_injective, hw_surjective⟩, ?_⟩
  -- The chosen lift already satisfies the exact reduction equation by construction.
  apply LinearMap.ext
  intro x
  have hwx := LinearMap.congr_fun hw x
  simpa [fGA, f'GA]
    using hwx

/-- Helper for Exercise 15-15.5-3: postcomposing a residue-field reduction map with a reduced
`k[G]`-linear equivalence preserves the same reduction structure. -/
private theorem isResidueFieldReductionOfEquivTarget
    {P : Type*} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    {W : Type*} [AddCommGroup W] [Module k W] [Module k[G] W] [IsScalarTower k k[G] W]
    {V' : Type*} [AddCommGroup V'] [Module k V'] [Module k[G] V']
    [IsScalarTower k k[G] V']
    {f : P →ₗ[A] V'} (hf : f.IsResidueFieldReduction G)
    (e : V' ≃ₗ[k[G]] W) :
    (((e.restrictScalars k).toLinearMap.restrictScalars A).comp f).IsResidueFieldReduction G := by
  letI : Module A[G] V' := Module.compHom V' (MonoidAlgebra.mapRingHom G (algebraMap A k))
  letI : IsScalarTower A A[G] V' :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A k))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
            algebraMap k k[G] (IsLocalRing.residue A c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • y
            = (IsLocalRing.residue A c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A c) y)
        _ = c • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k c y)
  letI : Module A[G] W := Module.compHom W (MonoidAlgebra.mapRingHom G (algebraMap A k))
  letI : IsScalarTower A A[G] W :=
    IsScalarTower.of_algebraMap_smul fun c y ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A k))
            (MonoidAlgebra.single (1 : G) c) • y =
          c • y
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) =
            algebraMap k k[G] (IsLocalRing.residue A c) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A c) • y
            = (IsLocalRing.residue A c) • y := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A c) y)
        _ = c • y := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k c y)
  constructor
  · -- Only the target realization changes, so the base-change witness transports across `e`.
    refine IsBaseChange.of_equiv (hf.1.equiv ≪≫ₗ e.restrictScalars k) ?_
    intro x
    simpa [LinearMap.comp_apply] using congrArg e (hf.1.equiv_tmul x)
  · -- Check equivariance on the group generators and then rewrite through the `k[G]`-linearity of
    -- the chosen target equivalence.
    refine Representation.IsIntertwiningMap.mk ?_
    intro g x
    calc
      (((e.restrictScalars k).toLinearMap.restrictScalars A).comp f)
          (MonoidAlgebra.of A G g • x)
        = e (MonoidAlgebra.of k G g • f x) := by
            change e (f (MonoidAlgebra.of A G g • x)) = _
            rw [LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hf g x]
      _ = MonoidAlgebra.of k G g • e (f x) := by
            simpa using e.map_smul (MonoidAlgebra.of k G g) (f x)
      _ = (MonoidAlgebra.mapRingHom G (algebraMap A k) (MonoidAlgebra.of A G g)) •
            e (f x) := by
            simp [MonoidAlgebra.of_apply]
      _ = MonoidAlgebra.of A G g •
            (((e.restrictScalars k).toLinearMap.restrictScalars A).comp f x) := by
            rfl

/-- Helper for Exercise 15-15.5-3: over the residue field, Maschke's theorem makes every
`k[G]`-module projective when `|G|` is prime to `p`. -/
private theorem residueGroupAlgebraModuleProjectiveOfOrderPrimeToP
    (hG : ¬ p ∣ Nat.card G)
    {M : Type*} [AddCommGroup M] [Module k[G] M] :
    Module.Projective k[G] M := by
  let _ : Fintype G := Fintype.ofFinite G
  -- Maschke turns the prime-to-`p` hypothesis into semisimplicity of `k[G]`.
  let _ : NeZero (Nat.card G : k) := NeZero.of_not_dvd k hG
  let _ : IsSemisimpleRing k[G] := by
    infer_instance
  exact Module.projective_of_isSemisimpleRing k[G] M

/-- Helper for Exercise 15-15.5-3: the tautological owner module `ρl.asModule` is `k[G]`-linearly
equivalent to the original representation space `V`. -/
private theorem nonemptyAsModuleLinearEquivTarget
    (ρl : Representation k G V) :
    letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
    letI : IsScalarTower k k[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
        simp [Algebra.smul_def]
    Nonempty (ρl.asModule ≃ₗ[k[G]] V) := by
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  refine ⟨
    { toFun := fun x ↦ ρl.asModuleEquiv x
      invFun := fun x ↦ ρl.asModuleEquiv.symm x
      left_inv := fun x ↦ ρl.asModuleEquiv.symm_apply_apply x
      right_inv := fun x ↦ ρl.asModuleEquiv.apply_symm_apply x
      map_add' := fun x y ↦ ρl.asModuleEquiv.map_add x y
      map_smul' := ?_ }⟩
  intro a x
  -- Transport the `k[G]`-action through `asModuleEquiv`, then read it as the original action.
  calc
    ρl.asModuleEquiv (a • x) = ρl.asAlgebraHom a (ρl.asModuleEquiv x) := by
      simpa using Representation.asModuleEquiv_map_smul (ρ := ρl) a x
    _ = a • ρl.asModuleEquiv x := rfl

/-- Helper for Exercise 15-15.5-3: exposing the residue action of `ρl` turns `V` into a finite
projective `k[G]`-module when `|G|` is prime to `p`. -/
private theorem targetModuleFiniteProjectiveOfOrderPrimeToP
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V) :
    letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
    letI : IsScalarTower k k[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
        simp [Algebra.smul_def]
    Module.Projective k[G] V ∧ Module.Finite k[G] V := by
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  constructor
  · -- Maschke gives projectivity on the residue-field group algebra.
    exact residueGroupAlgebraModuleProjectiveOfOrderPrimeToP (A := A) (p := p) (G := G) hG
  · -- Finite-dimensionality over `k` already implies finite generation over `k[G]`.
    exact Module.Finite.of_restrictScalars_finite k k[G] V

/-- Helper for Exercise 15-15.5-3: a representation equivalence induces the corresponding
`k[G]`-linear equivalence on the owner modules. -/
private noncomputable def representationEquivAsModuleLinearEquiv
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {W' : Type*} [AddCommGroup W'] [Module k W']
    {ρ : Representation k G V'} {σ : Representation k G W'}
    (e : ρ.Equiv σ) :
    ρ.asModule ≃ₗ[k[G]] σ.asModule := by
  refine
    { toFun := (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ) e.toIntertwiningMap
      invFun := (Representation.IntertwiningMap.equivLinearMapAsModule σ ρ) e.symm.toIntertwiningMap
      left_inv := by
        -- The inverse owner map is induced by the inverse representation equivalence.
        intro x
        change e.symm (e x) = x
        simp
      right_inv := by
        -- The same computation works in the opposite direction.
        intro x
        change e (e.symm x) = x
        simp
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro a x
        simp }

/-- Helper for Exercise 15-15.5-3: an isomorphism of finite projective owners can be consumed as a
concrete `k[G]`-linear equivalence of the underlying reduced modules. -/
private theorem residueFieldReductionNonemptyLinearEquivOfNonemptyIso
    (F : FiniteProjectiveGroupAlgebraModule k G)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQ : Nonempty (Q.residueFieldReduction ≅ F)) :
    Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] F.V) := by
  -- Re-express the owner isomorphism as a plain linear equivalence once.
  exact
    (finiteProjectiveGroupAlgebraModule_nonempty_iso_iff_nonempty_linearEquiv
      (A := k) (G := G) Q.residueFieldReduction F).1 hQ

/-- Helper for Exercise 15-15.5-3: the same-universe coordinate model, its projective owner, and
the lifted owner over `A` compile to a reduced `k[G]`-linear equivalence back to `V`. -/
private theorem sameUniverseOwnerCompiledReducedEquiv
    {W : Type u} [AddCommGroup W] [Module k W]
    {ρl : Representation k G V}
    (ρW : Representation k G W)
    [FiniteDimensional k W]
    (eW : ρW.Equiv ρl)
    (F : FiniteProjectiveGroupAlgebraModule k G)
    (hF :
      letI : Module k[G] W := Module.compHom W ρW.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] W :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρW.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (F.V ≃ₗ[k[G]] W))
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQ : Nonempty (Q.residueFieldReduction ≅ F)) :
    letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
    letI : IsScalarTower k k[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
        simp [Algebra.smul_def]
    Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] V) := by
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  letI : Module k[G] W := Module.compHom W ρW.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] W :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρW.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  rcases residueFieldReductionNonemptyLinearEquivOfNonemptyIso
      (A := A) (G := G) (F := F) (Q := Q) hQ with ⟨eQF⟩
  rcases hF with ⟨eFW⟩
  have hW :
      letI : Module k[G] W := Module.compHom W ρW.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] W :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρW.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (ρW.asModule ≃ₗ[k[G]] W) :=
    nonemptyAsModuleLinearEquivTarget (A := A) (G := G) (V := W) ρW
  rcases hW with ⟨eWmod⟩
  have hV :
      letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] V :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (ρl.asModule ≃ₗ[k[G]] V) :=
    nonemptyAsModuleLinearEquivTarget (A := A) (G := G) (V := V) ρl
  rcases hV with ⟨eV⟩
  -- Compose the reduced owner equivalence with the coordinate-model bridge and the original
  -- representation equivalence.
  exact
    ⟨eQF.trans
      (eFW.trans
        (eWmod.symm.trans
          ((representationEquivAsModuleLinearEquiv (ρ := ρW) (σ := ρl) eW).trans eV)))⟩

/-- Helper for Exercise 15-15.5-3: the finite representation attached to a residue-side projective
owner can be moved once to the standard same-universe coordinate model. -/
private theorem residueOwnerSameUniverseCoordinateModel
    (F : FiniteProjectiveGroupAlgebraModule k G) :
    ∃ d : ℕ, ∃ _ : AddCommGroup (Fin d → k), ∃ _ : Module k (Fin d → k),
      ∃ ρW : Representation k G (Fin d → k),
        Nonempty (ρW.Equiv F.toFiniteRep.ρ) := by
  let d := Module.finrank k F.toFiniteRep.V
  letI : Module k k := Semiring.toModule
  letI : AddCommGroup (Fin d → k) := Pi.addCommGroup
  letI : Module k (Fin d → k) := Pi.Function.module (Fin d) k k
  -- Apply the same-universe model theorem directly to the finite representation carried by `F`.
  refine ⟨d, inferInstance, inferInstance, ?_⟩
  simpa [d] using exists_same_universe_finite_rep_model (ρ := F.toFiniteRep.ρ)

/-- Helper for Exercise 15-15.5-3: the intrinsic residue-field reduction owner is canonically
`k[G]`-linearly equivalent to the carrier of its tautological finite representation. -/
private theorem residueFieldReductionAsModuleNonemptyLinearEquiv
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    letI : Module k Q.residueFieldReduction.V :=
      Module.compHom Q.residueFieldReduction.V (algebraMap k k[G])
    letI : IsScalarTower k k[G] Q.residueFieldReduction.V :=
      IsScalarTower.of_compHom k k[G] Q.residueFieldReduction.V
    Nonempty
      (asModule Q.residueFieldReduction.toFiniteRep.ρ ≃ₗ[k[G]] Q.residueFieldReduction.V) := by
  letI : Module k Q.residueFieldReduction.V :=
    Module.compHom Q.residueFieldReduction.V (algebraMap k k[G])
  letI : IsScalarTower k k[G] Q.residueFieldReduction.V :=
    IsScalarTower.of_compHom k k[G] Q.residueFieldReduction.V
  change Nonempty
    ((Representation.ofModule (ModuleCat.of k[G] Q.residueFieldReduction.V)).asModule ≃ₗ[k[G]]
      Q.residueFieldReduction.V)
  let Mmod : ModuleCat k[G] := ModuleCat.of k[G] Q.residueFieldReduction.V
  let toFun : (Representation.ofModule Mmod).asModule → Q.residueFieldReduction.V := fun x ↦
    (RestrictScalars.addEquiv k k[G] Q.residueFieldReduction.V)
      ((Representation.ofModule Mmod).asModuleEquiv x)
  let invFun : Q.residueFieldReduction.V → (Representation.ofModule Mmod).asModule := fun x ↦
    (Representation.ofModule Mmod).asModuleEquiv.symm
      ((RestrictScalars.addEquiv k k[G] Q.residueFieldReduction.V).symm x)
  refine ⟨
    { toFun := toFun
      invFun := invFun
      left_inv := by
        -- Both directions are just the identity after unpacking the owner and restriction maps.
        intro x
        simp [toFun, invFun, Mmod]
      right_inv := by
        -- The same computation closes the inverse direction on the concrete owner carrier.
        intro x
        simp [toFun, invFun, Mmod]
      map_add' := by
        -- Addition is preserved because both comparison maps are additive.
        intro x y
        dsimp [toFun]
        rw [(Representation.ofModule Mmod).asModuleEquiv.map_add]
        exact (RestrictScalars.addEquiv k k[G] Q.residueFieldReduction.V).map_add _ _
      map_smul' := by
        -- The owner `asModule` action is definitionally the original `k[G]`-action.
        intro r x
        exact Representation.smul_ofModule_asModule (M := Mmod) r x }⟩

/-- Helper for Exercise 15-15.5-3: the canonical pure tensor `1 ⊗ x` is `A`-linear for the
restricted `A`-action on the literal tensor-product reduction. -/
private theorem residueFieldReductionTensor_tmul_smul
    (Q : FiniteProjectiveGroupAlgebraModule A G) (a : A) (x : Q.V) :
    letI : Module k Q.residueFieldReduction.V :=
      Module.compHom Q.residueFieldReduction.V (algebraMap k k[G])
    letI : Module A Q.residueFieldReduction.V :=
      Module.compHom Q.residueFieldReduction.V (algebraMap A k)
    letI : IsScalarTower A k Q.residueFieldReduction.V :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : IsScalarTower k k[G] Q.residueFieldReduction.V :=
      IsScalarTower.of_compHom k k[G] Q.residueFieldReduction.V
    ((1 : k) ⊗ₜ[A] (a • x) : TensorProduct A k Q.V) =
      a • ((1 : k) ⊗ₜ[A] x : TensorProduct A k Q.V) := by
  exact TensorProduct.tmul_smul (R := A) (R' := A) a (1 : k) x

/-- Helper for Exercise 15-15.5-3: the canonical pure tensor `1 ⊗ x` is additive on the
literal tensor-product reduction carrier. -/
private theorem residueFieldReductionTensor_tmul_add
    (Q : FiniteProjectiveGroupAlgebraModule A G) (x y : Q.V) :
    letI : Module k Q.residueFieldReduction.V :=
      Module.compHom Q.residueFieldReduction.V (algebraMap k k[G])
    letI : IsScalarTower k k[G] Q.residueFieldReduction.V :=
      IsScalarTower.of_compHom k k[G] Q.residueFieldReduction.V
    ((1 : k) ⊗ₜ[A] (x + y) : TensorProduct A k Q.V) =
      ((1 : k) ⊗ₜ[A] x : TensorProduct A k Q.V) +
        ((1 : k) ⊗ₜ[A] y : TensorProduct A k Q.V) := by
  simpa using (TensorProduct.tmul_add (R := A) (1 : k) x y)

/-- Helper for Exercise 15-15.5-3: the intrinsic residue-field reduction owner of `Q` has
underlying carrier definitionally equal to the tensor-product reduction `k ⊗[A] Q.V`. This keeps
the remaining closing transport on a stable carrier spelling. -/
private theorem residueFieldReductionTensorCarrierEq
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    (Q.residueFieldReduction.V : Type u) = k ⊗[A] Q.V := by
  -- Unfold the residue-field reduction owner once; its carrier is literally the tensor product.
  rfl

/-- Helper for Exercise 15-15.5-3: the left `k`-module structure on the tensor-product reduction
`k ⊗[A] Q.V` is compatible with restriction of scalars from `A`. This isolates the scalar-tower
instance that the intrinsic carrier transport will need later. -/
private theorem residueFieldReductionTensorLeftScalarTower
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    letI : Module A k := Algebra.toModule
    letI : Module k k := Semiring.toModule
    letI : Module k (k ⊗[A] Q.V) := TensorProduct.leftModule
    IsScalarTower A k (k ⊗[A] Q.V) := by
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (k ⊗[A] Q.V) := TensorProduct.leftModule
  exact
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · simp
      · intro z y
        simp [IsLocalRing.ResidueField.algebraMap_eq, Algebra.smul_def, TensorProduct.smul_tmul']
      · intro x₁ x₂ hx₁ hx₂
        rw [smul_add, smul_add, hx₁, hx₂]

/-- Helper for Exercise 15-15.5-3: the intrinsic residue-field reduction owner of `Q` should
carry the canonical tensor-product reduction map as an `A`-linear residue-field reduction. -/
private theorem intrinsicResidueFieldReductionMap
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    letI : Module k Q.residueFieldReduction.V :=
      Module.compHom Q.residueFieldReduction.V (algebraMap k k[G])
    letI : Module A Q.residueFieldReduction.V :=
      Module.compHom Q.residueFieldReduction.V (algebraMap A k)
    letI : IsScalarTower A k Q.residueFieldReduction.V :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : IsScalarTower k k[G] Q.residueFieldReduction.V :=
      IsScalarTower.of_compHom k k[G] Q.residueFieldReduction.V
    ∃ red0 : Q.V →ₗ[A] Q.residueFieldReduction.V,
      red0.IsResidueFieldReduction G := by
  letI : Module A k := Algebra.toModule
  letI : Module k k := Semiring.toModule
  letI : Module k (k ⊗[A] Q.V) := TensorProduct.leftModule
  letI : IsScalarTower A k (k ⊗[A] Q.V) :=
    residueFieldReductionTensorLeftScalarTower (A := A) (G := G) Q
  have hTarget :
      Nonempty ((k ⊗[A] Q.V) ≃ₗ[k[G]] Q.residueFieldReduction.V) := by
    simpa [FiniteProjectiveGroupAlgebraModule.residueFieldReduction,
      FiniteProjectiveGroupAlgebraModule.V] using
      (show Nonempty ((k ⊗[A] Q.V) ≃ₗ[k[G]] (k ⊗[A] Q.V)) from
        ⟨LinearEquiv.refl k[G] (k ⊗[A] Q.V)⟩)
  rcases hTarget with ⟨eTarget⟩
  let red0 : Q.V →ₗ[A] Q.residueFieldReduction.V :=
    (((eTarget.restrictScalars k).toLinearMap.restrictScalars A).comp
      (TensorProduct.mk A k Q.V 1))
  refine ⟨red0, ?_⟩
  -- The intrinsic reduction owner has the same carrier as the tensor reduction, so one target
  -- equivalence turns the canonical tensor map into the required owner-level reduction.
  simpa [red0] using
    (isResidueFieldReductionOfEquivTarget
      (A := A) (G := G)
      (f := TensorProduct.mk A k Q.V 1)
      (e := eTarget)
      (MonoidAlgebra.tensorProduct_mk_isResidueFieldReduction
        (Λ := A) (G := G) (P := Q.V)))

/-- Helper for Exercise 15-15.5-3: after exposing the `k[G]`-action of `ρl`, the residue
representation space is finite over the group algebra. This isolates the easy finite-generation
side condition from the later projective-owner lift blocker. -/
private theorem targetModuleFinite
    (ρl : Representation k G V) :
    letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
    letI : IsScalarTower k k[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
        simp [Algebra.smul_def]
    Module.Finite k[G] V := by
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  -- Finite-dimensionality over `k` already implies finite generation over `k[G]`.
  exact Module.Finite.of_restrictScalars_finite k k[G] V

/-- Helper for Exercise 15-15.5-3: the prime-to-`p` hypothesis packages the residue
representation admits the tautological self-equivalence used when later transport steps are
specialized to the identity case. -/
private theorem representationEquivReflNonempty
    (ρ : Representation k G V) :
    Nonempty (ρ.Equiv ρ) := by
  exact ⟨Representation.Equiv.refl ρ⟩

/-- Helper for Exercise 15-15.5-3: for a module viewed through `Representation.ofModule'`, the
associated group-algebra operator is exactly the original scalar action. -/
private theorem ofModule'_asAlgebraHom_apply
    {M : Type*} [AddCommGroup M] [Module A M] [Module A[G] M] [IsScalarTower A A[G] M]
    (r : A[G]) (m : M) :
    ((Representation.ofModule' M).asAlgebraHom r) m = r • m := by
  letI : Module A A[G] := Algebra.toModule
  have halg (a : A) (x : M) :
      ((Representation.ofModule' M).asAlgebraHom (algebraMap A A[G] a)) x = a • x := by
    simpa [Algebra.smul_def] using
      LinearMap.congr_fun ((Representation.ofModule' M).asAlgebraHom.commutes a) x
  -- Expand the group-algebra element linearly and check the claim on monomials `of g`.
  refine MonoidAlgebra.induction_on (p := fun s : A[G] =>
    ((Representation.ofModule' M).asAlgebraHom s) m = s • m) r ?_ ?_ ?_
  · intro g
    simp [Representation.ofModule', MonoidAlgebra.of]
  · intro a b ha hb
    calc
      ((Representation.ofModule' M).asAlgebraHom (a + b)) m
          = ((Representation.ofModule' M).asAlgebraHom a) m +
              ((Representation.ofModule' M).asAlgebraHom b) m := by
                simp
      _ = a • m + b • m := by rw [ha, hb]
      _ = (a + b) • m := by rw [add_smul]
  · intro a s hs
    calc
      ((Representation.ofModule' M).asAlgebraHom (a • s)) m
          = ((Representation.ofModule' M).asAlgebraHom (algebraMap A A[G] a * s)) m := by
              rw [Algebra.smul_def]
      _ = ((Representation.ofModule' M).asAlgebraHom (algebraMap A A[G] a))
            (((Representation.ofModule' M).asAlgebraHom s) m) := by
              rw [map_mul]
              rfl
      _ = a • (((Representation.ofModule' M).asAlgebraHom s) m) := by
              rw [halg]
      _ = a • (s • m) := by rw [hs]
      _ = (a • s) • m := by
              exact (smul_assoc a s m).symm

/-- Helper for Exercise 15-15.5-3: once the same-universe model of a residue representation is
viewed through its induced `k[G]`-action, the projective-owner API packages it as a finite
projective owner without changing the carrier. -/
private theorem sameUniverseModelAsModuleOwner
    {W : Type u} [AddCommGroup W] [Module k W]
    (ρW : Representation k G W)
    [FiniteDimensional k W]
    (hproj :
      letI : Module k[G] W := Module.compHom W ρW.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] W :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρW.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Module.Projective k[G] W ∧ Module.Finite k[G] W) :
    ∃ F : FiniteProjectiveGroupAlgebraModule k G,
      letI : Module k[G] W := Module.compHom W ρW.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] W :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρW.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (F.V ≃ₗ[k[G]] W) := by
  letI : Module k[G] W := Module.compHom W ρW.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] W :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρW.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  rcases hproj with ⟨hprojW, hfiniteW⟩
  letI : Module.Projective k[G] W := hprojW
  letI : Module.Finite k[G] W := hfiniteW
  -- The owner is just the same finite projective `k[G]`-module viewed through the chapter API.
  exact same_universe_model_finiteProjective_owner

/-- Helper for Exercise 15-15.5-3: any owner-level lift theorem for finite projective residue
owners already suffices to produce the reduced owner needed for the final lift packaging. -/
private theorem sameUniverseLiftedProjectorOwner_ofOwnerLift
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V)
    (hLift :
      ∀ F : FiniteProjectiveGroupAlgebraModule k G,
        ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
          Nonempty (Q.residueFieldReduction ≅ F)) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] V :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] V) := by
  -- Move the target representation to the same-universe coordinate model.
  obtain ⟨ρW, hρW⟩ :=
    exists_same_universe_finite_rep_model ρl
  rcases hρW with ⟨eW⟩
  letI : Module k k := Semiring.toModule
  letI : AddCommGroup (Fin (Module.finrank k V) → k) := Pi.addCommGroup
  letI : Module k (Fin (Module.finrank k V) → k) :=
    Pi.Function.module (Fin (Module.finrank k V)) k k
  -- Over the residue field, Maschke makes the coordinate model finite projective over `k[G]`.
  have hprojW :=
    targetModuleFiniteProjectiveOfOrderPrimeToP
      (A := A) (p := p) (G := G) (V := Fin (Module.finrank k V) → k) hG ρW
  -- Package that coordinate model once as a finite-projective owner over `k[G]`.
  obtain ⟨F, hF⟩ :=
    sameUniverseModelAsModuleOwner
      (A := A) (G := G) (W := Fin (Module.finrank k V) → k) ρW hprojW
  -- Lift the packaged residue owner through the abstract owner-lift hypothesis.
  obtain ⟨Q, hQ⟩ := hLift F
  refine ⟨Q, ?_⟩
  -- Compile the owner-level reduction back to the original representation space.
  exact
    sameUniverseOwnerCompiledReducedEquiv
      (A := A) (G := G) (V := V) (ρl := ρl) ρW eW F hF Q hQ

section NoetherianAdicOwnerLift

/-- Helper for Exercise 15-15.5-3: in the complete-Noetherian owner-lift wrappers, `A` is viewed
as a module over itself through the canonical semiring action. -/
local instance noetherianAdicOwnerLiftSelfModule : Module A A :=
  Semiring.toModule

/-- Helper for Exercise 15-15.5-3: on the stronger Chapter 14 surface, every finite projective
residue-side owner already has an upstairs lift. -/
private theorem noetherianAdicOwnerLift
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (F : FiniteProjectiveGroupAlgebraModule k G) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty (Q.residueFieldReduction ≅ F) := by
  -- The owner theorem already exists on this stronger surface, so no local projector work remains.
  simpa using
    exists_projective_lift_of_residueField_projective (A := A) (G := G) F

/-- Helper for Exercise 15-15.5-3: on the stronger Chapter 14 surface, the same-universe
coordinate-model packaging already proves the owner-lift step with no further local projector
arguments. -/
private theorem sameUniverseLiftedProjectorOwner_noetherianAdic
    [IsNoetherianRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] V :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] V) := by
  -- The already-proved abstract packaging theorem consumes the stronger owner lift directly.
  simpa using
    sameUniverseLiftedProjectorOwner_ofOwnerLift
      (A := A) (p := p) (G := G) (V := V) hG ρl
      (fun F ↦ noetherianAdicOwnerLift (A := A) (G := G) F)

end NoetherianAdicOwnerLift

/-- Helper for Exercise 15-15.5-3: a base-change witness already forces the reduction map to be
surjective on the underlying `A`-module. -/
private theorem surjective_of_isBaseChange
    {P : Type y} [AddCommGroup P] [Module A P]
    {W : Type*} [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower A k W]
    {red : P →ₗ[A] W}
    (hred : IsBaseChange k red) :
    Function.Surjective red := by
  intro x
  -- Write the target vector through the base-change equivalence and then lift that pure tensor.
  obtain ⟨t, rfl⟩ := hred.equiv.surjective x
  have hres : Function.Surjective (algebraMap A k) := by
    simpa [IsLocalRing.ResidueField.algebraMap_eq] using IsLocalRing.residue_surjective
  obtain ⟨y, hy⟩ := TensorProduct.mk_surjective (R := A) (S := k) (M := P) hres t
  refine ⟨y, ?_⟩
  have htmul : hred.equiv (1 ⊗ₜ[A] y) = red y := by
    simpa using hred.equiv_tmul (1 : k) y
  exact htmul.symm.trans (congrArg hred.equiv hy)

/-- Helper for Exercise 15-15.5-3: two residue-field reduction maps from the same `A[G]`-module
identify their targets by a canonical `k[G]`-linear equivalence. -/
private theorem targetLinearEquivOfCommonReduction
    {P : Type y} [AddCommGroup P] [Module A P] [Module A[G] P] [IsScalarTower A A[G] P]
    {W₁ : Type*} [AddCommGroup W₁] [Module k W₁] [Module A W₁] [IsScalarTower A k W₁]
      [Module k[G] W₁] [IsScalarTower k k[G] W₁]
    {W₂ : Type*} [AddCommGroup W₂] [Module k W₂] [Module A W₂] [IsScalarTower A k W₂]
      [Module k[G] W₂] [IsScalarTower k k[G] W₂]
    {red₁ : P →ₗ[A] W₁} {red₂ : P →ₗ[A] W₂}
    (hred₁ : red₁.IsResidueFieldReduction G)
    (hred₂ : red₂.IsResidueFieldReduction G) :
    Nonempty (W₁ ≃ₗ[k[G]] W₂) := by
  let e : W₁ ≃ₗ[k] W₂ := hred₁.1.equiv.symm.trans hred₂.1.equiv
  have happly (x : P) : e (red₁ x) = red₂ x := by
    have h₁ : hred₁.1.equiv (1 ⊗ₜ[A] x) = red₁ x := by
      simpa using hred₁.1.equiv_tmul (1 : k) x
    have h₂ : hred₂.1.equiv (1 ⊗ₜ[A] x) = red₂ x := by
      simpa using hred₂.1.equiv_tmul (1 : k) x
    calc
      e (red₁ x) = e (hred₁.1.equiv (1 ⊗ₜ[A] x)) := by rw [h₁.symm]
      _ = hred₂.1.equiv (1 ⊗ₜ[A] x) := by
            simp [e]
      _ = red₂ x := h₂
  have hsurj : Function.Surjective red₁ :=
    surjective_of_isBaseChange (A := A) (P := P) (W := W₁) hred₁.1
  refine
    ⟨{ toFun := e
       invFun := e.symm
       left_inv := e.left_inv
       right_inv := e.right_inv
       map_add' := e.map_add
       map_smul' := ?_ }⟩
  intro a y
  obtain ⟨x, rfl⟩ := hsurj y
  -- Check `k[G]`-linearity on a lifted source vector, then extend from the monoid basis.
  refine MonoidAlgebra.induction_on (p := fun b : k[G] ↦ e (b • red₁ x) = b • e (red₁ x)) a ?_ ?_ ?_
  · intro g
    calc
      e (MonoidAlgebra.of k G g • red₁ x)
          = e (red₁ (MonoidAlgebra.of A G g • x)) := by
              rw [LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hred₁ g x]
      _ = red₂ (MonoidAlgebra.of A G g • x) := by
            rw [happly]
      _ = MonoidAlgebra.of k G g • red₂ x := by
            rw [LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hred₂ g x]
      _ = MonoidAlgebra.of k G g • e (red₁ x) := by
            rw [happly]
  · intro b c hb hc
    calc
      e ((b + c) • red₁ x) = e (b • red₁ x + c • red₁ x) := by rw [add_smul]
      _ = e (b • red₁ x) + e (c • red₁ x) := by rw [e.map_add]
      _ = b • e (red₁ x) + c • e (red₁ x) := by rw [hb, hc]
      _ = (b + c) • e (red₁ x) := by rw [add_smul]
  · intro a' b hb
    calc
      e ((a' • b) • red₁ x) = e (a' • (b • red₁ x)) := by rw [smul_assoc]
      _ = a' • e (b • red₁ x) := by rw [e.map_smul]
      _ = a' • (b • e (red₁ x)) := by rw [hb]
      _ = (a' • b) • e (red₁ x) := by rw [smul_assoc]

section StandardFreeProjectorLift

/-- Helper for Exercise 15-15.5-3: in the standard free projector-lift block, the base ring acts
on itself through the canonical semiring module structure. -/
local instance standardFreeProjectorLiftSelfModule : Module A A :=
  Semiring.toModule

/-- Helper for Exercise 15-15.5-3: in the standard free projector-lift block, the residue field
acts on itself through the canonical semiring module structure. -/
local instance standardFreeProjectorLiftResidueSelfModule : Module k k :=
  Semiring.toModule

/-- Helper for Exercise 15-15.5-3: the standard free source group algebra uses its canonical
`A`-module structure. -/
local instance standardFreeProjectorLiftGroupAlgebraModule : Module A A[G] :=
  Algebra.toModule

/-- Helper for Exercise 15-15.5-3: the standard free target group algebra uses its canonical
`k`-module structure. -/
local instance standardFreeProjectorLiftResidueGroupAlgebraModule : Module k k[G] :=
  Algebra.toModule

/-- Helper for Exercise 15-15.5-3: the reduced group algebra is also an `A`-module through
the residue-field map. -/
local instance standardFreeProjectorLiftRestrictedResidueGroupAlgebraModule : Module A k[G] :=
  Module.compHom k[G] (algebraMap A k)

/-- Helper for Exercise 15-15.5-3: the finite standard free source module has its pointwise
canonical `A`-module structure. -/
local instance standardFreeProjectorLiftSourceModule (n : Nat) : Module A (Fin n → A[G]) :=
  Pi.Function.module (Fin n) A A[G]

/-- Helper for Exercise 15-15.5-3: the finite standard free target module has its pointwise
canonical `k`-module structure. -/
local instance standardFreeProjectorLiftTargetModule (n : Nat) : Module k (Fin n → k[G]) :=
  Pi.Function.module (Fin n) k k[G]

/-- Helper for Exercise 15-15.5-3: the finite standard free target module is viewed as an
`A`-module by restricting scalars through the residue field. -/
local instance standardFreeProjectorLiftRestrictedTargetModule (n : Nat) :
    Module A (Fin n → k[G]) :=
  Pi.Function.module (Fin n) A k[G]

/-- Helper for Exercise 15-15.5-3: on the standard free owner, the reduction map on
`A[G]`-linear endomorphisms is itself a residue-field base change. -/
private theorem standardFreeEndomorphismReduction_isBaseChange
    (n : Nat) :
    let f : (Fin n → A[G]) →ₗ[A] (Fin n → k[G]) :=
      LinearMap.compLeft
        (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
          A[G] →ₗ[A] k[G])) (Fin n)
    let hf : f.IsResidueFieldReduction G :=
      LinearMap.IsResidueFieldReduction.finite_free_groupAlgebra_residueFieldReduction
        (A := A) (G := G) n
    IsBaseChange k
      (LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraLinearMap
        (A := A) (G := G) hf) := by
  let f : (Fin n → A[G]) →ₗ[A] (Fin n → k[G]) :=
    LinearMap.compLeft
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
        A[G] →ₗ[A] k[G])) (Fin n)
  let hf : f.IsResidueFieldReduction G :=
    LinearMap.IsResidueFieldReduction.finite_free_groupAlgebra_residueFieldReduction
      (A := A) (G := G) n
  -- The imported Chapter 14 transport layer already proves the base-change claim for the free
  -- ambient owner; we name the specialization here so the remaining blocker is purely idempotent
  -- lifting rather than transport setup.
  simpa [f, hf] using
    (LinearMap.IsResidueFieldReduction.restricted_groupAlgebraEnd_isBaseChange
      (A := A) (G := G) hf)

/-- Helper for Exercise 15-15.5-3: an integral `A`-algebra pulls the maximal ideal of the local
base ring inside the Jacobson radical. -/
private theorem mapMaximalIdeal_le_jacobson_of_integral
    {S : Type*} [CommRing S] [Algebra A S] [Algebra.IsIntegral A S] :
    ((IsLocalRing.maximalIdeal A).map (algebraMap A S)) ≤ Ideal.jacobson (⊥ : Ideal S) := by
  -- Contract each maximal ideal of the integral extension back to the unique maximal ideal of `A`.
  rw [Ideal.jacobson, le_sInf_iff]
  intro J hJ
  let _ : J.IsMaximal := hJ.2
  refine Ideal.map_le_iff_le_comap.2 ?_
  exact le_of_eq
    (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (S := S) J)).symm

/-- Helper for Exercise 15-15.5-3: if an ideal lies in the Jacobson radical, then a unit modulo
that ideal already comes from a unit upstairs. -/
private theorem isUnit_of_isUnit_quotient_of_le_jacobson
    {S : Type*} [CommRing S] (I : Ideal S)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal S)) {x : S}
    (hx : IsUnit (Ideal.Quotient.mk I x)) :
    IsUnit x := by
  -- The quotient map is local under the Jacobson containment, so units lift through it.
  let _ : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I hI
  exact IsUnit.of_map (Ideal.Quotient.mk I) x hx

/-- Helper for Exercise 15-15.5-3: over a henselian pair, the polynomial `X^2 - X` lifts any
simple root across the defining ideal. -/
private theorem xSqSubX_rootLift_of_henselianPair
    {S : Type*} [CommRing S] [Algebra A S] (I : Ideal S) [HenselianRing S I]
    {a0 : S} :
    let fS : Polynomial S := (Polynomial.X ^ 2 - Polynomial.X : Polynomial A).map (algebraMap A S)
    ∀ (hEval : fS.eval a0 ∈ I),
      IsUnit (Ideal.Quotient.mk I (fS.derivative.eval a0)) →
      ∃ e : S, fS.IsRoot e ∧ e - a0 ∈ I := by
  dsimp
  intro hEval hDeriv
  -- Hensel's lemma applies directly once `X^2 - X` is viewed over the coefficient extension `S`.
  exact
    HenselianRing.is_henselian
      (R := S) (I := I)
      ((Polynomial.X ^ 2 - Polynomial.X : Polynomial A).map (algebraMap A S))
      (by
        have hfactor :
            (Polynomial.X ^ 2 - Polynomial.X : Polynomial A) =
              Polynomial.X * (Polynomial.X - 1) := by
          ring
        rw [hfactor]
        simpa using
          ((Polynomial.monic_X (R := A)).mul (Polynomial.monic_X_sub_C (1 : A))).map
            (algebraMap A S))
      a0
      hEval
      hDeriv

/-- Helper for Exercise 15-15.5-3: after choosing a raw preimage `u0` of the reduced projector in
the standard free endomorphism algebra, the remaining Henselian step is to lift the canonical
idempotent point inside the singleton-generated commutative algebra `A[u0]`. -/
private theorem standardFreeEndomorphismChosenPreimageLiftsIdempotentOfHenselian
    {n : Nat}
    {f : (Fin n → A[G]) →ₗ[A] (Fin n → k[G])}
    (hf : f.IsResidueFieldReduction G)
    (uBar : Module.End k[G] (Fin n → k[G]))
    (huBar : IsIdempotentElem uBar)
    {u0 : Module.End A[G] (Fin n → A[G])}
    (hu0 :
      LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraLinearMap
        (A := A) (G := G) hf u0 = uBar) :
    ∃ u : Module.End A[G] (Fin n → A[G]),
      IsIdempotentElem u ∧
        LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraLinearMap
          (A := A) (G := G) hf u = uBar := by
  letI : Module A (Module.End k[G] (Fin n → k[G])) :=
    Module.compHom (Module.End k[G] (Fin n → k[G])) (algebraMap A k)
  letI : Algebra A (Module.End k[G] (Fin n → k[G])) :=
    Algebra.compHom (Module.End k[G] (Fin n → k[G])) (algebraMap A k)
  letI : IsScalarTower A k (Module.End k[G] (Fin n → k[G])) :=
    IsScalarTower.of_algebraMap_smul fun a u ↦ by
      ext x
      rfl
  let red :
      Module.End A[G] (Fin n → A[G]) →ₐ[A]
        Module.End k[G] (Fin n → k[G]) :=
    LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraAlgHom
      (A := A) (G := G) hf
  have hred_toLinearMap :
      red.toLinearMap =
        LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraLinearMap
          (A := A) (G := G) hf := by
    exact
      LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraAlgHom_toLinearMap
        (A := A) (G := G) hf
  have hu0_alg : red u0 = uBar := by
    have hred_u0 :
      red u0 =
          LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraLinearMap
            (A := A) (G := G) hf u0 := by
      simpa [red] using congrArg (fun φ => φ u0) hred_toLinearMap
    exact hred_u0.trans hu0
  letI : Module.Finite A (Fin n → A[G]) :=
    LinearMap.IsResidueFieldReduction.finite_free_groupAlgebra_moduleFinite
      (A := A) (G := G) n
  letI : Module.Free A (Module.End A[G] (Fin n → A[G])) :=
    groupAlgebra_endomorphismModule_free (A := A) (G := G) (P := Fin n → A[G])
  letI :
      Module.Finite A
        (Representation.IntertwiningMap
          (Representation.ofModule' (Fin n → A[G]))
          (Representation.ofModule' (Fin n → A[G]))) :=
    equivariantEndomorphismAlgebra_finite (A := A) (G := G) (P := Fin n → A[G])
  let endEquiv :
      Representation.IntertwiningMap
          (Representation.ofModule' (Fin n → A[G]))
          (Representation.ofModule' (Fin n → A[G])) ≃ₗ[A]
        Module.End A[G] (Fin n → A[G]) :=
    (ofModule'_equivAlgEnd (G := G) A (Fin n → A[G])).toLinearEquiv
  letI : Module.Finite A (Module.End A[G] (Fin n → A[G])) :=
    Module.Finite.equiv endEquiv
  have hbase :
      IsBaseChange k red.toLinearMap := by
    simpa [hred_toLinearMap] using
      (LinearMap.IsResidueFieldReduction.restricted_groupAlgebraEnd_isBaseChange
        (A := A) (G := G) hf)
  obtain ⟨u, hu, huRed⟩ :=
    idempotent_lifts_along_residueFieldBaseChange_of_henselian
      (A := A)
      (B := Module.End A[G] (Fin n → A[G]))
      (Bbar := Module.End k[G] (Fin n → k[G]))
      red hbase uBar huBar
  refine ⟨u, hu, ?_⟩
  have hred_u :
      red u =
        LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraLinearMap
          (A := A) (G := G) hf u := by
    simpa [red] using congrArg (fun φ => φ u) hred_toLinearMap
  exact hred_u.symm.trans huRed

/-- Helper for Exercise 15-15.5-3: on the standard free owner, a reduced idempotent projector
should lift to an upstairs idempotent projector under the Henselian local hypothesis. -/
private theorem endHomRestrictGroupAlgebraLinearMapLiftsIdempotentOfHenselian
    {n : Nat}
    {f : (Fin n → A[G]) →ₗ[A] (Fin n → k[G])}
    (hf : f.IsResidueFieldReduction G)
    (uBar : Module.End k[G] (Fin n → k[G]))
    (huBar : IsIdempotentElem uBar) :
    ∃ u : Module.End A[G] (Fin n → A[G]),
      IsIdempotentElem u ∧
        LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraLinearMap
          (A := A) (G := G) hf u = uBar := by
  have hbase :
      IsBaseChange k
        (LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraLinearMap
          (A := A) (G := G) hf) := by
    -- The transport layer already identifies the endomorphism reduction map with residue-field
    -- base change; only the Henselian idempotent-lift step is still missing.
    simpa using
      (LinearMap.IsResidueFieldReduction.restricted_groupAlgebraEnd_isBaseChange
        (A := A) (G := G) hf)
  letI : Module.Free A (Module.End A[G] (Fin n → A[G])) :=
    groupAlgebra_endomorphismModule_free (A := A) (G := G) (P := Fin n → A[G])
  letI :
      Module.Finite A
        (Representation.IntertwiningMap
          (Representation.ofModule' (Fin n → A[G]))
          (Representation.ofModule' (Fin n → A[G]))) :=
    equivariantEndomorphismAlgebra_finite (A := A) (G := G) (P := Fin n → A[G])
  let endEquiv :
      Representation.IntertwiningMap
          (Representation.ofModule' (Fin n → A[G]))
          (Representation.ofModule' (Fin n → A[G])) ≃ₗ[A]
        Module.End A[G] (Fin n → A[G]) :=
    (ofModule'_equivAlgEnd (G := G) A (Fin n → A[G])).toLinearEquiv
  letI : Module.Finite A (Module.End A[G] (Fin n → A[G])) :=
    Module.Finite.equiv endEquiv
  letI : Module A (Module.End k[G] (Fin n → k[G])) :=
    Module.compHom (Module.End k[G] (Fin n → k[G])) (algebraMap A k)
  letI : Algebra A (Module.End k[G] (Fin n → k[G])) :=
    Algebra.compHom (Module.End k[G] (Fin n → k[G])) (algebraMap A k)
  letI : IsScalarTower A k (Module.End k[G] (Fin n → k[G])) :=
    IsScalarTower.of_algebraMap_smul fun a u ↦ by
      ext x
      rfl
  let red :
      Module.End A[G] (Fin n → A[G]) →ₐ[A]
        Module.End k[G] (Fin n → k[G]) :=
    LinearMap.IsResidueFieldReduction.endHom_restrict_groupAlgebraAlgHom
      (A := A) (G := G) hf
  -- Choose any preimage of the reduced projector, then move to the monogenic commutative algebra
  -- it generates and perform the Hensel correction there.
  obtain ⟨u0, hu0⟩ := surjective_of_isBaseChange
    (A := A)
    (P := Module.End A[G] (Fin n → A[G]))
    (W := Module.End k[G] (Fin n → k[G]))
    hbase uBar
  obtain ⟨u, hu, huRed⟩ :=
    standardFreeEndomorphismChosenPreimageLiftsIdempotentOfHenselian
      (A := A) (G := G) hf uBar huBar hu0
  exact ⟨u, hu, huRed⟩

/-- Helper for Exercise 15-15.5-3: every finite projective residue-side owner should lift to an
upstairs finite projective `A[G]`-owner on the current Henselian surface. -/
private theorem existsProjectiveOwnerLiftOfResidueOwner
    (F : FiniteProjectiveGroupAlgebraModule k G) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      Nonempty (Q.residueFieldReduction ≅ F) := by
  -- Route correction: abandon the coordinate-tower algebraization detour and reuse the Chapter 14
  -- projector-presentation skeleton directly on the current Henselian surface.
  obtain ⟨n, eBar, heBar, hF⟩ :=
    FiniteProjectiveGroupAlgebraModule.exists_free_projector_presentation_iso
      (A := A) (G := G) F
  letI : Module.Finite A (Fin n → A[G]) :=
    LinearMap.IsResidueFieldReduction.finite_free_groupAlgebra_moduleFinite
      (A := A) (G := G) n
  let f : (Fin n → A[G]) →ₗ[A] (Fin n → k[G]) :=
    LinearMap.compLeft
      (((MonoidAlgebra.mapAlgHom G (Algebra.ofId A k)).toLinearMap :
        A[G] →ₗ[A] k[G])) (Fin n)
  let hf : f.IsResidueFieldReduction G :=
    LinearMap.IsResidueFieldReduction.finite_free_groupAlgebra_residueFieldReduction
      (A := A) (G := G) n
  obtain ⟨e, he, heRed⟩ :=
    endHomRestrictGroupAlgebraLinearMapLiftsIdempotentOfHenselian
      (A := A) (G := G) (f := f) hf eBar heBar
  let Q :=
    FiniteProjectiveGroupAlgebraModule.finiteProjectiveGroupAlgebraModule_of_idempotent_range
      (A := A) (G := G) e he
  refine ⟨Q, ?_⟩
  -- Once the projector lifts, the Chapter 14 range-comparison theorem packages the lifted owner.
  simpa [Q, f, hf] using
    FiniteProjectiveGroupAlgebraModule.lifted_projector_range_nonempty_iso
      (A := A) (G := G) hf he heRed F hF

end StandardFreeProjectorLift

/-- Helper for Exercise 15-15.5-3: a free lifted representation packages as a finite-projective
`A[G]`-owner without changing the underlying `A[G]`-module. -/
private theorem finiteProjectiveOwnerOfDirectLift
    {P : Type u} [AddCommGroup P] [Module A P] [Module.Free A P] [Module.Finite A P]
    (hG : ¬ p ∣ Nat.card G)
    (ρA : Representation A G P) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      letI : Module A[G] P := Module.compHom P ρA.asAlgebraHom.toRingHom
      letI : IsScalarTower A A[G] P :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρA.asAlgebraHom (algebraMap A A[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (Q.V ≃ₗ[A[G]] P) := by
  letI : Module A[G] P := Module.compHom P ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A A[G] P :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A A[G] a) x = a • x
      simp [Algebra.smul_def]
  have hprojP : Module.Projective A[G] P :=
    free_groupAlgebra_module_projective_of_order_prime_to_p
      (A := A) (p := p) (G := G) (P := P) hG
  letI : Module.Finite A[G] P := Module.Finite.of_restrictScalars_finite A A[G] P
  let Pfg : FGModuleCat A[G] := FGModuleCat.of A[G] P
  let Q : FiniteProjectiveGroupAlgebraModule A G := ⟨Pfg, hprojP⟩
  refine ⟨Q, ?_⟩
  -- The packaged owner is definitionally the same `A[G]`-module.
  exact ⟨by simpa [Q, Pfg, FiniteProjectiveGroupAlgebraModule.V] using
    (LinearEquiv.refl A[G] P)⟩

/-- Helper for Exercise 15-15.5-3: lifting the residue-side finite projective owner of the
same-universe model already produces the owner needed for the closing compiled reduction API. -/
private theorem sameUniverseLiftedProjectorOwner_ofDirectLift
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] V :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] V) := by
  -- Route correction: the direct free lift is no longer the driver. First lift the residue-side
  -- finite projective owner, then compile that owner back to the target representation.
  exact
    sameUniverseLiftedProjectorOwner_ofOwnerLift
      (A := A) (p := p) (G := G) (V := V) hG ρl
      (fun F ↦ existsProjectiveOwnerLiftOfResidueOwner (A := A) (G := G) F)

/-- Helper for Exercise 15-15.5-3: the same-universe coordinate model of `ρl` admits a finite
projective `A[G]`-owner whose reduction compiles back to the original target representation. -/
private theorem sameUniverseLiftedProjectorOwner
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V) :
    ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
      letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] V :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] V) := by
  -- Route correction: the proof now pivots through the residue-owner lift, and the direct free
  -- lift is only a downstream wrapper reconstructed from that owner.
  exact sameUniverseLiftedProjectorOwner_ofDirectLift (A := A) (p := p) (G := G) (V := V) hG ρl

/-- Helper for Exercise 15-15.5-3: once an upstairs owner reduces to the original residue
representation, the actual residue-field lift is the canonical tensor-product reduction map
postcomposed with the compiled reduced equivalence. -/
private theorem residueFieldLiftOfCompiledOwner_baseChange
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    [Module k[G] V] [IsScalarTower k k[G] V]
    {red0 : Q.V →ₗ[A] Q.residueFieldReduction.V}
    (hred0 : red0.IsResidueFieldReduction G)
    (eQ : Q.residueFieldReduction.V ≃ₗ[k[G]] V) :
    IsBaseChange k ((((eQ.restrictScalars k).toLinearMap.restrictScalars A).comp red0)) := by
  -- Postcomposing the intrinsic owner reduction with the compiled target equivalence preserves
  -- the same base-change witness.
  refine IsBaseChange.of_equiv (hred0.1.equiv ≪≫ₗ eQ.restrictScalars k) ?_
  intro x
  simpa [LinearMap.comp_apply] using congrArg eQ (hred0.1.equiv_tmul (1 : k) x)

/-- Helper for Exercise 15-15.5-3: postcomposing an owner-level residue-field reduction with the
compiled reduced equivalence preserves the expected `MonoidAlgebra.of` action on each group
element. This isolates the clean target-side equivariance fragment from the remaining source-action
normalization. -/
private theorem compiledOwnerReduction_map_monoidAlgebra_of
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    [Module k[G] V] [IsScalarTower k k[G] V]
    {red0 : Q.V →ₗ[A] Q.residueFieldReduction.V}
    (hred0 : red0.IsResidueFieldReduction G)
    (eQ : Q.residueFieldReduction.V ≃ₗ[k[G]] V)
    (g : G) (x : Q.V) :
    (((eQ.restrictScalars k).toLinearMap.restrictScalars A).comp red0)
        ((MonoidAlgebra.of A G g) • x) =
      (MonoidAlgebra.of k G g) •
        ((((eQ.restrictScalars k).toLinearMap.restrictScalars A).comp red0) x) := by
  -- First use the owner-level reduction map on the monoid generator, then move the result through
  -- the compiled `k[G]`-linear equivalence.
  calc
    (((eQ.restrictScalars k).toLinearMap.restrictScalars A).comp red0)
        ((MonoidAlgebra.of A G g) • x)
      = eQ (red0 ((MonoidAlgebra.of A G g) • x)) := by
          rfl
    _ = eQ ((MonoidAlgebra.of k G g) • red0 x) := by
          rw [LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of hred0 g x]
    _ = (MonoidAlgebra.of k G g) • eQ (red0 x) := by
          simpa using eQ.map_smul (MonoidAlgebra.of k G g) (red0 x)
    _ = (MonoidAlgebra.of k G g) •
          ((((eQ.restrictScalars k).toLinearMap.restrictScalars A).comp red0) x) := by
          rfl

/-- Helper for Exercise 15-15.5-3: once an upstairs owner reduces to the original residue
representation, the actual residue-field lift is the canonical tensor-product reduction map
postcomposed with the compiled reduced equivalence. -/
private theorem targetOfModule_apply_eq_monoidAlgebra_of
    (ρl : Representation k G V) (g : G) (v : V) :
    letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
    letI : IsScalarTower k k[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
        simp [Algebra.smul_def]
    letI : Module A[G] V := Module.compHom V (MonoidAlgebra.mapRingHom G (algebraMap A k))
    letI : IsScalarTower A A[G] V :=
      IsScalarTower.of_algebraMap_smul fun a x ↦ by
        change
          (MonoidAlgebra.mapRingHom G (algebraMap A k))
              (MonoidAlgebra.single (1 : G) a) • x =
            a • x
        rw [MonoidAlgebra.mapRingHom_single]
        have hsingle :
            MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
              algebraMap k k[G] (IsLocalRing.residue A a) := by
          rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
          simp
        calc
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
              = (IsLocalRing.residue A a) • x := by
                  simpa only [hsingle] using
                    (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A a) x)
          _ = a • x := by
                simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                  (IsScalarTower.algebraMap_smul k a x)
    ((Representation.ofModule' V : Representation A G V) g) v =
      (MonoidAlgebra.mapRingHom G (algebraMap A k) (MonoidAlgebra.of A G g)) • v := by
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  letI : Module A[G] V := Module.compHom V (MonoidAlgebra.mapRingHom G (algebraMap A k))
  letI : IsScalarTower A A[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A k))
            (MonoidAlgebra.single (1 : G) a) • x =
          a • x
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
            algebraMap k k[G] (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
            = (IsLocalRing.residue A a) • x := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k a x)
  -- The transported `A[G]`-action on `V` evaluates a group generator by the corresponding
  -- reduced monomial obtained from `MonoidAlgebra.mapRingHom`.
  change ((Representation.ofModule' V : Representation A G V) g) v =
    (MonoidAlgebra.of A G g) • v
  simpa [Representation.asAlgebraHom_of, MonoidAlgebra.of_apply] using
    (ofModule'_asAlgebraHom_apply
      (A := A) (G := G) (M := V) (r := MonoidAlgebra.of A G g) (m := v))

/-- Helper for Exercise 15-15.5-3: once an upstairs owner reduces to the original residue
representation, the actual residue-field lift is the canonical tensor-product reduction map
postcomposed with the compiled reduced equivalence. -/
private theorem residueFieldLiftOfCompiledOwner
    (ρl : Representation k G V)
    (Q : FiniteProjectiveGroupAlgebraModule A G)
    (hQ :
      letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
      letI : IsScalarTower k k[G] V :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
          simp [Algebra.smul_def]
      Nonempty (Q.residueFieldReduction.V ≃ₗ[k[G]] V)) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρl ρA red := by
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simp [Algebra.smul_def]
  letI : Module A[G] V := Module.compHom V (MonoidAlgebra.mapRingHom G (algebraMap A k))
  letI : IsScalarTower A A[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (MonoidAlgebra.mapRingHom G (algebraMap A k))
            (MonoidAlgebra.single (1 : G) a) • x =
          a • x
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) =
            algebraMap k k[G] (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G) (IsLocalRing.residue A a) • x
            = (IsLocalRing.residue A a) • x := by
                simpa only [hsingle] using
                  (IsScalarTower.algebraMap_smul k[G] (IsLocalRing.residue A a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k a x)
  letI : Module.Free A Q.V := FiniteProjectiveGroupAlgebraModule.free Q
  letI : Module.Finite A Q.V := Q.finite
  let ρA : Representation A G Q.V := Representation.ofModule' Q.V
  rcases hQ with ⟨eQ⟩
  rcases intrinsicResidueFieldReductionMap (A := A) (G := G) Q with ⟨red0, hred0⟩
  let red : Q.V →ₗ[A] V :=
    (((eQ.restrictScalars k).toLinearMap.restrictScalars A).comp red0)
  have hred :
      letI : Module A[G] Q.V := Module.compHom Q.V ρA.asAlgebraHom.toRingHom
      letI : IsScalarTower A A[G] Q.V :=
        IsScalarTower.of_algebraMap_smul fun a x ↦ by
          change ρA.asAlgebraHom (algebraMap A A[G] a) x = a • x
          simpa using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
      red.IsResidueFieldReduction G := by
    refine ⟨?_, ?_⟩
    · -- The owner-level base-change witness survives postcomposition by the target equivalence.
      exact residueFieldLiftOfCompiledOwner_baseChange (A := A) (G := G) (V := V) Q hred0 eQ
    ·
      refine Representation.IsIntertwiningMap.mk ?_
      intro g x
      -- Put the temporary source action into the explicit `ρA.asAlgebraHom` normal form shared by
      -- both the transported `Module.compHom` spelling and the original owner action.
      change red (ρA.asAlgebraHom (MonoidAlgebra.of A G g) x) =
        ((Representation.ofModule' V : Representation A G V) g) (red x)
      -- Rewrite the source `Representation.ofModule'` action back to the owner's monoid action so
      -- the compiled owner-level equivariance theorem applies without instance-matching noise.
      have hsource :
          ρA.asAlgebraHom (MonoidAlgebra.of A G g) x =
            (MonoidAlgebra.of A G g) • x := by
        change
          ((Representation.ofModule' Q.V).asAlgebraHom (MonoidAlgebra.of A G g)) x =
            (MonoidAlgebra.of A G g) • x
        exact
          (ofModule'_asAlgebraHom_apply
            (A := A) (G := G) (M := Q.V) (r := MonoidAlgebra.of A G g) (m := x))
      have htarget :
          (MonoidAlgebra.of k G g) • red x =
            ((Representation.ofModule' V : Representation A G V) g) (red x) := by
        -- The target-side transported `A[G]`-action is exactly the reduced monoid action.
        simpa [MonoidAlgebra.of_apply] using
          (targetOfModule_apply_eq_monoidAlgebra_of
            (A := A) (G := G) (V := V) (ρl := ρl) g (red x)).symm
      calc
        red (ρA.asAlgebraHom (MonoidAlgebra.of A G g) x)
            = red ((MonoidAlgebra.of A G g) • x) := by rw [hsource]
        _ = (MonoidAlgebra.of k G g) • red x := by
              simpa [red] using
                compiledOwnerReduction_map_monoidAlgebra_of
                  (A := A) (G := G) (V := V) Q hred0 eQ g x
        _ = ((Representation.ofModule' V : Representation A G V) g) (red x) := by
              rw [htarget]
  refine ⟨Q.V, inferInstance, inferInstance, inferInstance, inferInstance, ρA, red, ?_⟩
  simpa [IsResidueFieldLift, red] using hred

/-- Helper for Exercise 15-15.5-3: once every finite projective residue-side owner lifts, the full
source-facing residue-field lift follows by same-universe packaging and the compiled owner
reduction map. -/
private theorem residueFieldLift_ofOwnerLift
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V)
    (hLift :
      ∀ F : FiniteProjectiveGroupAlgebraModule k G,
        ∃ Q : FiniteProjectiveGroupAlgebraModule A G,
          Nonempty (Q.residueFieldReduction ≅ F)) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρl ρA red := by
  -- Route correction: after the owner-first pivot, the whole exercise is formal once the
  -- residue-side finite projective owner can be lifted.
  obtain ⟨Q, hQ⟩ :=
    sameUniverseLiftedProjectorOwner_ofOwnerLift
      (A := A) (p := p) (G := G) (V := V) hG ρl hLift
  -- Compile the lifted owner back to a genuine free `A`-representation.
  exact residueFieldLiftOfCompiledOwner (A := A) (G := G) (V := V) ρl Q hQ

/-- Helper for Exercise 15-15.5-3: once the lifted owner is available, the direct free lift is
just the compiled owner reduction map read back as source-facing representation data. -/
private theorem existsDirectFreeLiftOnCoordinateModule
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρl ρA red := by
  -- Route correction: the direct free lift is only a wrapper around the owner-lift theorem.
  exact
    residueFieldLift_ofOwnerLift
      (A := A) (p := p) (G := G) (V := V) hG ρl
      (fun F ↦ existsProjectiveOwnerLiftOfResidueOwner (A := A) (G := G) F)

-- Proof sketch: apply the previous lifting theorem successively to the reductions modulo
-- `𝔪^n`, use the henselian-local hypothesis to pass from the compatible finite-level system to an
-- actual lift over `A`, and use uniqueness at each finite level to identify the result.
/-- Exercise 15-15.5-3 (3): if `A` is henselian local and `|G|` is prime to `p`, every
finite-dimensional linear representation of `G` over the residue field `k` lifts to a free
finitely generated representation of `G` over `A`. -/
theorem exists_residueFieldLift
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρl ρA red := by
  obtain ⟨Q, hQ⟩ :=
    sameUniverseLiftedProjectorOwner (A := A) (p := p) (G := G) (V := V) hG ρl
  -- The remaining endgame is formal: use the intrinsic reduction map of the lifted owner and
  -- compile its reduced target back to `V`.
  exact residueFieldLiftOfCompiledOwner (A := A) (G := G) (V := V) ρl Q hQ

-- Proof sketch: compare the two lifts modulo `𝔪^n` for every `n`, use the finite-level
-- conjugacy statement to choose compatible identifications, and use the henselian-local
-- hypothesis when passing from the finite-level system to the limit over `A`.
/-- Exercise 15-15.5-3 (4): if `A` is henselian local and `|G|` is prime to `p`, two free
finitely generated lifts of the same finite-dimensional residue-field representation are
equivariantly isomorphic through an `A`-linear isomorphism whose induced reduction map is the
identity on the residue representation. -/
theorem residueFieldLift_unique_up_to_equivariant_iso
    (hG : ¬ p ∣ Nat.card G)
    (ρl : Representation k G V)
    {P₁ : Type y} [AddCommGroup P₁] [Module A P₁] [Module.Free A P₁] [Module.Finite A P₁]
    (ρA₁ : Representation A G P₁)
    (red₁ : P₁ →ₗ[A] V)
    (hρA₁ : IsResidueFieldLift ρl ρA₁ red₁)
    {P₂ : Type y} [AddCommGroup P₂] [Module A P₂] [Module.Free A P₂] [Module.Finite A P₂]
    (ρA₂ : Representation A G P₂)
    (red₂ : P₂ →ₗ[A] V)
    (hρA₂ : IsResidueFieldLift ρl ρA₂ red₂) :
    ∃ e : ρA₁.Equiv ρA₂,
      red₂.comp e.toLinearMap = red₁ := by
  letI : Module A[G] P₁ := Module.compHom P₁ ρA₁.asAlgebraHom.toRingHom
  letI : IsScalarTower A A[G] P₁ :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA₁.asAlgebraHom (algebraMap A A[G] a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA₁.asAlgebraHom.commutes a) x
  letI : Module A[G] P₂ := Module.compHom P₂ ρA₂.asAlgebraHom.toRingHom
  letI : IsScalarTower A A[G] P₂ :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA₂.asAlgebraHom (algebraMap A A[G] a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA₂.asAlgebraHom.commutes a) x
  letI : Module k[G] V := Module.compHom V ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k k[G] V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k k[G] a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρl.asAlgebraHom.commutes a) x
  have hproj₁ : Module.Projective A[G] P₁ :=
    free_groupAlgebra_module_projective_of_order_prime_to_p
      (A := A) (p := p) (G := G) (P := P₁) hG
  have hproj₂ : Module.Projective A[G] P₂ :=
    free_groupAlgebra_module_projective_of_order_prime_to_p
      (A := A) (p := p) (G := G) (P := P₂) hG
  have hred₁ : red₁.IsResidueFieldReduction G := by
    simpa [IsResidueFieldLift] using hρA₁
  have hred₂ : red₂.IsResidueFieldReduction G := by
    simpa [IsResidueFieldLift] using hρA₂
  -- Compare the two lifts through the identity on the common residue representation, and lift
  -- that exact comparison back upstairs.
  obtain ⟨eLin, heLin⟩ :=
    exact_groupAlgebra_linearEquiv_of_common_reduction
      (A := A) (G := G)
      (P := P₁) (Pbar := V) (f := red₁) hred₁
      (P' := P₂) (f' := red₂) hred₂
  let eInter : ρA₁.IntertwiningMap ρA₂ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule
      (ρ := ρA₁) (σ := ρA₂)).symm eLin.toLinearMap
  refine ⟨Representation.Equiv.mk (eLin.restrictScalars A) eInter.isIntertwining', ?_⟩
  -- Forgetting the `A[G]`-linearity gives exactly the reduction identity promised by the lifted
  -- comparison.
  simpa using heLin

end

end Representation

end
