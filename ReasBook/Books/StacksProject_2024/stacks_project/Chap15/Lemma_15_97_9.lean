import Mathlib
import StacksProject_2024.Chap10.Definition_10_78_1
import StacksProject_2024.Chap15.Lemma_15_96_7
import StacksProject_2024.Chap15.Lemma_15_97_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape
open scoped nonZeroDivisors
open scoped EtaReductionDecompositionIdeal

universe u

section

variable {A : Type u} [CommRing A]

private abbrev baseChange
    {B : Type u} [CommRing B] [Algebra A B] :
    NatModuleCochainComplex A ⥤ NatModuleCochainComplex B :=
  Functor.mapHomologicalComplex (ModuleCat.extendScalars (algebraMap A B)) (up ℕ)

/- Domain-style sampling:
- primary domain: commutative algebra of principal quotients and localizations for the
  Berthelot-Ogus `η_f` construction;
- sampled owner declarations:
  `principalIdeal`,
  `NatModuleCochainComplex.etaReductionDecompositionIdeal`,
  `ModFSquared.Nat.cyclesReductionSurjective`,
  `ModFSquared.Nat.bockstein`,
  `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`;
- best owner abstraction:
  `source-facing`: the sum ideal `J(M^\bullet, f)`, the quotient ring
    `C = (A / fA) / J(M^\bullet, f)`, and the vanishing set `E`;
  `core/canonical`: the principal quotient `A ⧸ principalIdeal f`, ideal images under
    `Ideal.Quotient.mk`, together with the localized Berthelot-Ogus reduction owners
    `ModFSquared.Nat.cyclesReductionSurjective` and `ModFSquared.Nat.bockstein`;
  `bridge/view`: the localized extension-by-zero complex of `M`;
- primitive data vs derived API: the primitive data are the canonical principal quotient
  `A ⧸ principalIdeal f`, the conditional degreewise ideals `J_i(M^\bullet, f)`, the sum ideal,
  and the quotient ring `C`; the vanishing criterion and the localization / finite presentation /
  finite locally free statements are derived API built from those owners. -/

section

variable (f : A) (M : NatModuleCochainComplex A)
variable [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]

/-- The set `E` from Lemma `15.97.9`, formulated for a complex of finite free `A`-modules as the
primes containing `f` where every localized map `Ker(d^i mod f^2) → Ker(d^i mod f)` is
surjective in every nonnegative degree. When `f` is a nonzerodivisor in `A`, flatness of
localization makes its image a nonzerodivisor in each `Aₚ`, so Lemma `15.96.7` identifies the same
locus with vanishing of the localized Bockstein operators. -/
def etaReductionVanishingSet : Set (PrimeSpectrum A) :=
  { p : PrimeSpectrum A |
      let Aₚ := Localization.AtPrime p.asIdeal
      letI : CommRing Aₚ := inferInstance
      letI : Algebra A Aₚ := inferInstance
      let baseChangeAₚ : NatModuleCochainComplex A ⥤ NatModuleCochainComplex Aₚ := baseChange
      f ∈ p.asIdeal ∧
        ∀ i : ℕ,
          ModFSquared.Nat.cyclesReductionSurjective (algebraMap A Aₚ f) (baseChangeAₚ.obj M) i }

section

variable (hf : f ∈ nonZeroDivisors A)
variable (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)

/-- The ideal `J(M^\bullet, f) = \sum_i J_i(M^\bullet, f)` in `A / fA`, expressed as the supremum
of the conditional degreewise ideals from Lemma `15.97.8`. -/
def etaReductionDecompositionIdealSum :
    Ideal (A ⧸ principalIdeal f) :=
  ⨆ i : ℕ, J[f]_(i)(M ; hf, hI i)

/-- The quotient ring `C = (A / fA) / J(M^\bullet, f)`. -/
abbrev etaReductionDecompositionQuotient :=
  (A ⧸ principalIdeal f) ⧸ etaReductionDecompositionIdealSum f M hf hI

private abbrev etaReductionDecompositionPrime
    (p : PrimeSpectrum A) (hpf : f ∈ p.asIdeal) :=
  let hpV : p ∈ PrimeSpectrum.zeroLocus (principalIdeal f : Set A) :=
    (PrimeSpectrum.mem_zeroLocus p (principalIdeal f : Set A)).2 <| by
      simpa [principalIdeal] using (Ideal.span_singleton_le_iff_mem p.asIdeal).2 hpf
  (principalIdeal f).primeSpectrumQuotientOrderIsoZeroLocus.symm ⟨p, hpV⟩

/-- The localization of `J(M^\bullet, f)` at a prime `p` containing `f`. -/
def etaReductionDecompositionIdealSumLocalization
    (p : PrimeSpectrum A) (hpf : f ∈ p.asIdeal) :
    Ideal (Localization.AtPrime (etaReductionDecompositionPrime f p hpf).asIdeal) :=
  Ideal.map
    (algebraMap (A ⧸ principalIdeal f)
      (Localization.AtPrime (etaReductionDecompositionPrime f p hpf).asIdeal))
    (etaReductionDecompositionIdealSum f M hf hI)

/-- Helper for Lemma 15.97.9: a finite supremum of finitely generated ideals is finitely
generated. -/
private lemma ideal_fg_finset_sup
    {ι : Type*} (t : Finset ι) (J : ι → Ideal (A ⧸ principalIdeal f))
    (hJ : ∀ i ∈ t, (J i).FG) :
    (t.sup J).FG := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      -- The empty supremum is the zero ideal.
      simpa using (Submodule.fg_bot : (⊥ : Ideal (A ⧸ principalIdeal f)).FG)
  | @insert a s ha ih =>
      -- Insert one more summand and use closure of finite generation under binary suprema.
      have hsup : (s.sup J).FG := by
        exact ih fun i hi ↦ hJ i (by simp [hi])
      simpa [Finset.sup_insert, ha] using Submodule.FG.sup (hJ a (by simp)) hsup

/-- Helper for Lemma 15.97.9: if the degree-`i` term of `M` is zero, then the degree-`i`
decomposition ideal `J_i(M^\bullet, f)` is trivial. -/
private lemma etaReductionDecompositionIdeal_eq_bot_of_subsingleton_term
    (i : ℕ) [Subsingleton (M.X i)] :
    J[f]_(i)(M ; hf, hI i) = ⊥ := by
  -- The source of the reduced pair map is zero in degree `i`, so the splitting condition holds
  -- after every base change; uniqueness of the defining universal property then forces `J_i = 0`.
  apply NatModuleCochainComplex.etaReductionDecompositionIdeal_eq_of_property
    (M := M) (f := f) (i := i)
  · exact NatModuleCochainComplex.etaReductionDecompositionIdeal_property
      (M := M) (f := f) (i := i) hf (hI i)
  · intro B _ _ _
    constructor
    · intro _
      -- Over any target algebra, the base-changed source remains zero, so the image is
      -- `⊥.prod ⊥`.
      refine ⟨⊥, ⊥, ?_, ?_⟩
      · intro x y _
        exact Subsingleton.elim x y
      · ext z
        constructor
        · rintro ⟨x, rfl⟩
          rw [Submodule.mem_prod]
          constructor <;> simp
        · intro hz
          rw [Submodule.mem_prod] at hz
          have hz1 : z.1 = 0 := by simpa using hz.1
          have hz2 : z.2 = 0 := by simpa using hz.2
          refine ⟨0, ?_⟩
          ext <;> simp [hz1, hz2]
    · intro _
      exact bot_le

-- Proof sketch: each degreewise ideal `J_i(M^\bullet, f)` is finitely generated by the universal
-- splitting criterion from Lemma `15.97.7`, applied to the split monomorphism from Lemma
-- `15.97.5`; boundedness implies `J_i(M^\bullet, f) = 0` for all sufficiently large `i`, so the
-- supremum `J(M^\bullet, f)` is a finite sum of finitely generated ideals.
/-- Lemma 15.97.9 (1): if `M^\bullet` is bounded above, then the ideal
`J(M^\bullet, f) = \sum_i J_i(M^\bullet, f)` of `A / fA` is finitely generated. -/
theorem etaReductionDecompositionIdealSum_fg
    (hbounded : M.IsBoundedAbove) :
    (etaReductionDecompositionIdealSum f M hf hI).FG := by
  classical
  rcases hbounded with ⟨b, hb⟩
  let J : ℕ → Ideal (A ⧸ principalIdeal f) := fun i ↦ J[f]_(i)(M ; hf, hI i)
  have hJfg : ∀ i : ℕ, (J i).FG := by
    intro i
    exact NatModuleCochainComplex.etaReductionDecompositionIdeal_fg
      (M := M) (f := f) (i := i) hf (hI i)
  have hvanish : ∀ i : ℕ, b < i → J i = ⊥ := by
    intro i hi
    have hzeroExt : CategoryTheory.Limits.IsZero ((M.extend embeddingUpNat).X (i : ℤ)) :=
      (show CochainComplex.IsStrictlyLE (M.extend embeddingUpNat) (b : ℤ) from hb)
        .isZero_of_isStrictlyLE (b : ℤ) (i : ℤ) (by exact_mod_cast hi)
    have hzero : CategoryTheory.Limits.IsZero (M.X i) := by
      exact CategoryTheory.Limits.IsZero.of_iso hzeroExt (M.extendXIso embeddingUpNat rfl)
    letI : Subsingleton (M.X i) := ModuleCat.subsingleton_of_isZero hzero
    exact etaReductionDecompositionIdeal_eq_bot_of_subsingleton_term
      (f := f) (M := M) (hf := hf) (hI := hI) i
  have hsum :
      etaReductionDecompositionIdealSum f M hf hI =
        (Finset.range (b + 1)).sup J := by
    apply le_antisymm
    · -- Degrees above the chosen bound contribute nothing.
      rw [etaReductionDecompositionIdealSum]
      refine iSup_le ?_
      intro i
      by_cases hi : i < b + 1
      · exact Finset.le_sup hi
      · have hbi : b < i := by omega
        simpa [J, hvanish i hbi] using (bot_le : (⊥ : Ideal (A ⧸ principalIdeal f)) ≤ _)
    · -- Every bounded degree still appears in the original supremum.
      rw [etaReductionDecompositionIdealSum]
      refine Finset.sup_le ?_
      intro i hi
      exact le_iSup J i
  -- After truncating to finitely many degrees, finite generation follows by induction on the
  -- finite supremum.
  have hfgFinite : ((Finset.range (b + 1)).sup J).FG := by
    exact ideal_fg_finset_sup (f := f) (t := Finset.range (b + 1)) (J := J)
      (fun i hi ↦ hJfg i)
  simpa [hsum] using hfgFinite

-- Proof sketch: `C` is the quotient of `A / fA` by the finitely generated ideal from part `(1)`,
-- and quotient maps by finitely generated ideals are ring maps of finite presentation.
/-- Lemma 15.97.9 (2): if `M^\bullet` is bounded above, then the quotient ring
`C = (A / fA) / J(M^\bullet, f)` is finitely presented over `A / fA`, so the canonical map
`A / fA → C` is surjective of finite presentation. -/
theorem etaReductionDecompositionQuotient_finitePresentation
    (hbounded : M.IsBoundedAbove) :
    Algebra.FinitePresentation (A ⧸ principalIdeal f)
      (etaReductionDecompositionQuotient f M hf hI) :=
  by
    -- Part `(1)` gives finite generation of the quotient ideal, and the standard quotient
    -- instance upgrades that to finite presentation of the quotient algebra.
    letI :
        Algebra.FinitePresentation (A ⧸ principalIdeal f)
          (etaReductionDecompositionQuotient f M hf hI) :=
      Algebra.FinitePresentation.quotient
        (etaReductionDecompositionIdealSum_fg (f := f) (M := M) (hf := hf) (hI := hI) hbounded)
    infer_instance

-- Proof sketch: the localized kernel-surjectivity hypothesis gives the direct-sum decomposition
-- in each degree via Lemma `15.96.8`; under the global nonzerodivisor hypothesis, flatness of
-- localization makes the image of `f` a nonzerodivisor in `Aₚ`, so Lemma `15.96.7` applies at
-- `p`. The universal property of the ideals `J_i(M^\bullet, f)` then forces every localized
-- `J_i` to vanish, hence so does their sum.
/-- Lemma 15.97.9 (3): if `M^\bullet` is bounded above and `p` belongs to the vanishing set
`E`, then the localization of `J(M^\bullet, f)` at the corresponding prime of `A / fA` is zero. -/
theorem etaReductionDecompositionIdealSumLocalization_eq_bot_of_mem_etaReductionVanishingSet
    (hbounded : M.IsBoundedAbove)
    (p : PrimeSpectrum A) (hp : p ∈ etaReductionVanishingSet f M) :
    etaReductionDecompositionIdealSumLocalization f M hf hI p hp.1 = ⊥ := sorry

end

end

section

variable (f : A) (M : NatModuleCochainComplex A)
variable [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]

-- Proof sketch: after localizing at `p`, the assumed freeness of the nat-indexed cohomology of
-- `M` is transported internally to the bounded-above owner complex `M.extend embeddingUpNat`,
-- with negative degrees handled by the vanishing of the extension outside `ℕ`. Lemma `15.97.4`
-- then gives the power-of-`f` description of the determinantal ideals, hence the localized
-- `f`-torsion in homology vanishes. Flatness of localization then keeps the image of `f` a
-- nonzerodivisor, so Lemma `15.96.7` gives surjectivity of
-- `Ker(d^i mod f^2) → Ker(d^i mod f)` in every nonnegative degree.
/-- Lemma 15.97.9 (4): if `f` is a nonzerodivisor, `M^\bullet` is bounded above, `p` contains
`f`, and all localized cohomology modules `H^i(M^\bullet)_𝔭` in nonnegative degrees are free over
`A_𝔭`, then `p` belongs to the vanishing set `E`. -/
theorem mem_etaReductionVanishingSet_of_localizedHomology_free
    (hf : f ∈ nonZeroDivisors A)
    (hbounded : M.IsBoundedAbove)
    (p : PrimeSpectrum A) (hpf : f ∈ p.asIdeal)
    (hcohom :
      ∀ i : ℕ,
        Module.Free (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal (M.homology i))) :
    p ∈ etaReductionVanishingSet f M := sorry

end

section

variable (f : A) (M : NatModuleCochainComplex A)
variable [∀ i : ℕ, Module.Free A (M.X i)] [∀ i : ℕ, Module.Finite A (M.X i)]
variable (hf : f ∈ nonZeroDivisors A)
variable (hI : ∀ i : ℕ, (M.etaDeterminantalIdeal f i).IsPrincipal)

-- Proof sketch: after quotienting by `J(M^\bullet, f)`, every degreewise reduced map
-- `(1, d^i)` identifies its source with a product of submodules by the defining universal property
-- of `J_i`; the differential then splits off matching direct summands degreewise, so each
-- cohomology module is a quotient of a finite locally free module by a direct summand and hence is
-- finite locally free.
/-- Lemma 15.97.9 (5): if `M^\bullet` is bounded above, then the cohomology modules of
`η_f M^\bullet ⊗_A C`, where `C = (A / fA) / J(M^\bullet, f)`, are finite locally free
`C`-modules. -/
theorem etaFComplexOverDecompositionQuotient_homology_finiteLocallyFree
    (hbounded : M.IsBoundedAbove)
    (i : ℕ) :
    let C := etaReductionDecompositionQuotient f M hf hI
    letI : CommRing C := inferInstance
    letI : Algebra A C := inferInstance
    let baseChangeC : NatModuleCochainComplex A ⥤ NatModuleCochainComplex C := baseChange
    Module.FiniteLocallyFree C ((baseChangeC.obj (η[f] M)).homology i) :=
  sorry

end

end
