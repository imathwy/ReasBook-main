import Mathlib
import StacksProject_2024.Chap10.Definition_10_103_12
import StacksProject_2024.Chap10.Definition_10_157_1
import StacksProject_2024.Chap10.Lemma_10_99_2
import StacksProject_2024.Chap10.Lemma_10_103_6
import StacksProject_2024.Chap10.Lemma_10_40_6
import StacksProject_2024.Chap10.Lemma_10_115_2
import StacksProject_2024.Chap10.Lemma_10_112_7
import StacksProject_2024.Chap10.Lemma_10_68_5
import StacksProject_2024.Chap10.Lemma_10_72_3
import StacksProject_2024.Chap10.Lemma_10_72_5
import StacksProject_2024.Chap10.Lemma_10_103_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped TensorProduct

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Module.LocallyCohenMacaulay

/-
Source/core/bridge triage:
* source-facing: local Cohen-Macaulayness of a finite module over a Noetherian ring;
* core/canonical: `Module.LocallyCohenMacaulay R M` from `Definition_10_103_12`;
* bridge/view: the polynomial-base-change closure theorem for that owner.

Primitive data are only the module `M` and the owner hypothesis
`Module.LocallyCohenMacaulay R M`. The primewise Cohen-Macaulay localizations of the polynomial
base change are derived API from the resulting owner instance, so the theorem should return
`Module.LocallyCohenMacaulay` directly instead of a parallel family of explicit equalities.
-/

/-- Helper for Lemma 10.103.13: on the polynomial-module model, a polynomial whose leading
coefficient is a unit has trivial kernel. -/
private theorem polynomialModule_eq_zero_of_smul_eq_zero_of_isUnit_leadingCoeff
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (f : Polynomial A) (hf : IsUnit f.leadingCoeff) {g : PolynomialModule A N}
    (hfg : f • g = 0) : g = 0 := by
  by_contra hg
  classical
  let n : ℕ := g.support.max' (Finsupp.support_nonempty_iff.mpr hg)
  have hn_mem : n ∈ g.support := Finset.max'_mem _ _
  have hgn : g n ≠ 0 := Finsupp.mem_support_iff.mp hn_mem
  have htop :
      (f • g) (f.natDegree + n) = f.leadingCoeff • g n := by
    -- At the top index `natDegree f + n`, every antidiagonal summand but the leading one
    -- vanishes, either because the coefficient of `f` is above its degree or because the
    -- corresponding coefficient of `g` lies above the support maximum `n`.
    rw [PolynomialModule.smul_apply]
    calc
      ∑ a ∈ Finset.antidiagonal (f.natDegree + n), f.coeff a.1 • g a.2
          = ∑ a ∈ Finset.antidiagonal (f.natDegree + n),
              if a = (f.natDegree, n) then f.leadingCoeff • g n else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rcases a with ⟨i, j⟩
            by_cases hmain : (i, j) = (f.natDegree, n)
            · rcases Prod.mk.inj hmain with ⟨rfl, rfl⟩
              simp [Polynomial.coeff_natDegree]
            · have hij : i + j = f.natDegree + n := by
                simpa using (Finset.mem_antidiagonal.mp ha)
              have hterm_zero : f.coeff i • g j = 0 := by
                by_cases hi : i = f.natDegree
                · have hj : j = n := by
                    omega
                  exact False.elim (hmain (by simp [hi, hj]))
                · rcases lt_or_gt_of_ne hi with hi_lt | hi_gt
                  · have hj_gt : n < j := by
                      omega
                    have hgj : g j = 0 := by
                      by_contra hgj
                      have hj_mem : j ∈ g.support := Finsupp.mem_support_iff.mpr hgj
                      exact (not_lt_of_ge (Finset.le_max' _ _ hj_mem)) hj_gt
                    simp [hgj]
                  · simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi_gt]
              simp [hmain, hterm_zero]
      _ = f.leadingCoeff • g n := by
          simp [Finset.mem_antidiagonal]
  have hzero : f.leadingCoeff • g n = 0 := by
    simpa [hfg] using htop.symm
  exact hgn ((hf.smul_eq_zero).1 hzero)

/-- Helper for Lemma 10.103.13: transporting the polynomial-module comparison shows that a
polynomial with unit leading coefficient is a nonzerodivisor on the polynomial tensor module. -/
private theorem polynomial_tensor_isSMulRegular_of_isUnit_leadingCoeff
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (f : Polynomial A) (hf : IsUnit f.leadingCoeff) :
    IsSMulRegular ((Polynomial A) ⊗[A] N) f := by
  let e := PolynomialModule.polynomialTensorProductLEquivPolynomialModule A N
  have hreg : IsSMulRegular (PolynomialModule A N) f := by
    intro x y hxy
    have hzero : f • (x - y) = 0 := by
      simpa [smul_sub, hxy]
    exact sub_eq_zero.mp <|
      polynomialModule_eq_zero_of_smul_eq_zero_of_isUnit_leadingCoeff (N := N) f hf hzero
  -- The tensor-product model and the polynomial-module model carry the same `A[X]`-action.
  exact (LinearEquiv.isSMulRegular_congr e f).2 hreg

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.103.13: Cohen-Macaulayness is unchanged by an `R`-linear equivalence over
the same local ring. -/
private theorem cohenMacaulay_of_linearEquiv [IsLocalRing R]
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (e : N ≃ₗ[R] N') [h : Module.CohenMacaulay R N] : Module.CohenMacaulay R N' := by
  let _ : Module.Finite R N' := Module.Finite.equiv e
  -- Transport both invariants appearing in the owner definition across the linear equivalence.
  exact ⟨by
    rw [← Module.supportDim_eq_of_equiv e, ← moduleDepth_eq_of_equiv e, h.supportDim_eq_moduleDepth]⟩

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.103.13: local Cohen-Macaulayness is unchanged by an `R`-linear
equivalence over the same Noetherian ring. -/
private theorem locallyCohenMacaulay_of_linearEquiv
    {N N' : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (e : N ≃ₗ[R] N') [h : Module.LocallyCohenMacaulay R N] :
    Module.LocallyCohenMacaulay R N' := by
  let _ : Module.Finite R N' := Module.Finite.equiv e
  refine ⟨fun p ↦ ?_⟩
  let ep : LocalizedModule.AtPrime p.asIdeal N ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule.AtPrime p.asIdeal N' :=
    LinearEquiv.ofBijective (LocalizedModule.map p.asIdeal.primeCompl e.toLinearMap)
      ⟨LocalizedModule.map_injective p.asIdeal.primeCompl e.toLinearMap e.injective,
        LocalizedModule.map_surjective p.asIdeal.primeCompl e.toLinearMap e.surjective⟩
  -- Localize the linear equivalence and reuse the localized Cohen-Macaulay owner.
  let _ :
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) :=
    h.localizedModule_cohenMacaulay p
  exact cohenMacaulay_of_linearEquiv ep

/-- Helper for Lemma 10.103.13: over a Noetherian local ring, a finite module with
zero-dimensional support is already Cohen-Macaulay. -/
private theorem cohen_macaulay_of_supportDim_zero_local
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hdim : Module.supportDim A N = 0) : Module.CohenMacaulay A N := by
  refine Module.CohenMacaulay.mk ?_
  let _ : Nontrivial N := by
    simp [← Module.supportDim_ne_bot_iff_nontrivial A, hdim]
  have hdepth_le : WithBot.some (moduleDepth A N : ℕ∞) ≤ 0 := by
    -- In dimension zero the standard depth bound forces the depth to be zero as well.
    rw [← hdim]
    exact depth_le_supportDim
  have hdepth_eq : moduleDepth A N = 0 := by
    simpa using hdepth_le
  -- With both invariants equal to zero, the owner equality is immediate.
  simpa [hdepth_eq] using hdim

/-- Helper for Lemma 10.103.13: a locally Cohen-Macaulay module has full support. -/
private theorem support_eq_univ_of_locallyCohenMacaulay
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (hCM : Module.LocallyCohenMacaulay A N) :
    Module.support A N = Set.univ := by
  ext p
  constructor
  · intro _
    exact Set.mem_univ p
  · intro _
    let hlocal : Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal N) :=
      hCM.localizedModule_cohenMacaulay p
    have hsupportDim_ne_bot :
        Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal N) ≠ ⊥ := by
      -- The Cohen-Macaulay equality makes the localized support dimension an actual value, so the
      -- localized module is nonzero and hence the prime is in the original support.
      rw [hlocal.supportDim_eq_moduleDepth]
      simp
    have hnontrivial :
        Nontrivial (LocalizedModule.AtPrime p.asIdeal N) :=
      (Module.supportDim_ne_bot_iff_nontrivial
        (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N)).mp
        hsupportDim_ne_bot
    simpa [LocalizedModule.AtPrime] using
      (Module.mem_support_iff (R := A) (M := N) (p := p)).mpr hnontrivial

/-- Helper for Lemma 10.103.13: polynomial base change of a locally Cohen-Macaulay module has full
support. -/
private theorem support_eq_univ_polynomial_tensor_of_locallyCohenMacaulay
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (hCM : Module.LocallyCohenMacaulay A N) :
    Module.support (Polynomial A) ((Polynomial A) ⊗[A] N) = Set.univ := by
  -- The base-change support formula pulls back the already-full support of `N`.
  rw [Module.Lemma_10_40_6, support_eq_univ_of_locallyCohenMacaulay hCM]
  ext q
  simp

/-- Helper for Chap10 Lemma 10 103 13: full support identifies support dimension with the
ambient Krull dimension. -/
private theorem supportDim_eq_ringKrullDim_of_support_eq_univ
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Finite A N] (hsupp : Module.support A N = Set.univ) :
    Module.supportDim A N = ringKrullDim A := by
  -- Replace the module support by the whole spectrum, then forget the `Set.univ` subtype by the
  -- standard order isomorphism.
  have hsupport :
      Order.krullDim (Module.support A N) = Order.krullDim (PrimeSpectrum A) := by
    rw [hsupp]
    exact
      Order.krullDim_eq_of_orderIso
        (OrderIso.Set.univ : (Set.univ : Set (PrimeSpectrum A)) ≃o PrimeSpectrum A)
  simpa [Module.supportDim, ringKrullDim] using hsupport

/-- Helper for Chap10 Lemma 10 103 13: full support remains full after localizing at a prime. -/
private theorem support_localizedModuleAtPrime_eq_univ_of_support_eq_univ
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Finite A N] (hsupp : Module.support A N = Set.univ) (p : PrimeSpectrum A) :
    Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) =
      Set.univ := by
  let e := LocalizedModule.equivTensorProduct p.asIdeal.primeCompl N
  have hsupport_tensor :
      Module.support (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal N) =
        Module.support (Localization.AtPrime p.asIdeal)
          ((Localization.AtPrime p.asIdeal) ⊗[A] N) := by
    -- Move to the tensor-product model where Lemma `10.40.6` computes support.
    simpa using
      (LinearEquiv.support_eq (R := Localization.AtPrime p.asIdeal) e)
  rw [hsupport_tensor, Module.Lemma_10_40_6, hsupp]
  ext q
  simp

/-- Helper for Lemma 10.103.13: after adjoining one variable to `A`, tensoring `M` directly over
`R` agrees with first base-changing `M` to `A` and then extending scalars from `A` to
`A[X]`. -/
private noncomputable def polynomial_tensor_baseChange_linearEquiv
    {A : Type*} [CommRing A] [Algebra R A] :
    ((Polynomial A) ⊗[R] M) ≃ₗ[Polynomial A]
      ((Polynomial A) ⊗[A] (A ⊗[R] M)) := by
  -- Insert the redundant `A`-tensor factor and then reassociate so the one-variable theorem can
  -- be applied to the already base-changed module `A ⊗[R] M`.
  let eInsert :
      ((Polynomial A) ⊗[R] M) ≃ₗ[Polynomial A]
        (((Polynomial A) ⊗[A] A) ⊗[R] M) :=
    TensorProduct.AlgebraTensorModule.congr
      (Algebra.TensorProduct.rid A (Polynomial A) (Polynomial A)).symm.toLinearEquiv
      (LinearEquiv.refl R M)
  let eAssoc :
      (((Polynomial A) ⊗[A] A) ⊗[R] M) ≃ₗ[Polynomial A]
        ((Polynomial A) ⊗[A] (A ⊗[R] M)) :=
    TensorProduct.AlgebraTensorModule.assoc R A (Polynomial A) (Polynomial A) A M
  exact eInsert.trans eAssoc

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.103.13: an `R`-algebra equivalence identifies the prime complements of
corresponding prime ideals. -/
private theorem primeCompl_map_eq_of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    Submonoid.map e.toMulEquiv (PrimeSpectrum.comap e.toRingHom q).asIdeal.primeCompl =
      q.asIdeal.primeCompl := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    -- Re-express membership in the contracted prime so the image element can be read in `q`.
    simpa [PrimeSpectrum.comap_asIdeal] using ha
  · intro hb
    refine ⟨e.symm b, ?_, by simp⟩
    -- Pulling `b` back along `e` lands outside the contracted prime for the same reason.
    simpa [PrimeSpectrum.comap_asIdeal] using hb

/-- Helper for Lemma 10.103.13: localizing corresponding prime ideals along an `R`-algebra
equivalence gives an `R`-algebra equivalence of the local rings. -/
private noncomputable def localizationAtPrime_algEquiv_of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    Localization.AtPrime (PrimeSpectrum.comap e.toRingHom q).asIdeal ≃ₐ[R]
      Localization.AtPrime q.asIdeal :=
  -- This is the ring-side transport required by the source-local comparison at each prime.
  Localization.localAlgEquiv
    (I := (PrimeSpectrum.comap e.toRingHom q).asIdeal)
    (J := q.asIdeal)
    e
    (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q)

/-- Helper for Lemma 10.103.13: after localizing corresponding prime ideals along an `R`-algebra
equivalence, the localized tensor modules agree over the localized source ring. -/
private noncomputable def localized_tensor_linearEquiv_of_algEquiv_atPrime
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    let p := PrimeSpectrum.comap e.toRingHom q
    let eLoc := localizationAtPrime_algEquiv_of_algEquiv (R := R) e q
    let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
      eLoc.toRingHom.toAlgebra
    let _ :
        Module (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) :=
      Module.compHom (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) eLoc.toRingHom
    LocalizedModule.AtPrime p.asIdeal (A ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
      LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M) := by
  let p := PrimeSpectrum.comap e.toRingHom q
  let eLoc := localizationAtPrime_algEquiv_of_algEquiv (R := R) e q
  let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    eLoc.toRingHom.toAlgebra
  let _ : IsScalarTower R (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algHom eLoc.toAlgHom
  let _ :
      Module (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) :=
    Module.compHom (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) eLoc.toRingHom
  let _ :
      Module (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal ⊗[R] M) :=
    Module.compHom (Localization.AtPrime q.asIdeal ⊗[R] M) eLoc.toRingHom
  let eLocLinear :
      Localization.AtPrime p.asIdeal ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime q.asIdeal :=
    { __ := eLoc.toAddEquiv
      map_smul' := fun a x ↦ by
        -- On the codomain, the `Localization.AtPrime p.asIdeal`-action is induced by `eLoc`.
        simpa [Algebra.smul_def] using eLoc.map_mul a x }
  -- Rewrite both localizations as literal tensor base changes over `R`.
  let eLeft :
      LocalizedModule.AtPrime p.asIdeal (A ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime p.asIdeal ⊗[R] M :=
    (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl (A ⊗[R] M)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R A (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) M)
  let eMid :
      Localization.AtPrime p.asIdeal ⊗[R] M ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime q.asIdeal ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.congr eLocLinear (LinearEquiv.refl R M)
  let eRightB :
      LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M) ≃ₗ[Localization.AtPrime q.asIdeal]
        Localization.AtPrime q.asIdeal ⊗[R] M :=
    (LocalizedModule.equivTensorProduct q.asIdeal.primeCompl (B ⊗[R] M)).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange
        R B (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal) M)
  let eRight :
      LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
        Localization.AtPrime q.asIdeal ⊗[R] M :=
    { __ := eRightB.toAddEquiv
      map_smul' := fun a x ↦ by
        -- The q-side comparison is `B_q`-linear, hence also `A_p`-linear after restricting
        -- scalars along `eLoc`.
        change
          eRightB ((algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal) a) • x) =
            (algebraMap (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime q.asIdeal) a) • eRightB x
        exact
          eRightB.map_smul (algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal) a) x }
  -- The middle `TensorProduct.congr` is the only nontrivial transport; the outer equivalences are
  -- the canonical localized-module-to-tensor-product comparisons.
  exact eLeft.trans <| eMid.trans eRight.symm

omit [IsNoetherianRing R] in
/-- Helper for Lemma 10.103.13: an `R`-algebra equivalence between scalar-extension rings should
transport local Cohen-Macaulayness of the corresponding tensor-base-changed module. -/
private theorem locallyCohenMacaulay_tensor_of_algEquiv
    {A : Type*} [CommRing A] [Algebra R A] [IsNoetherianRing A]
    {B : Type*} [CommRing B] [Algebra R B] [IsNoetherianRing B]
    (e : A ≃ₐ[R] B) (h : Module.LocallyCohenMacaulay A (A ⊗[R] M)) :
    Module.LocallyCohenMacaulay B (B ⊗[R] M) := by
  let _ : Algebra A B := e.toRingHom.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algHom e.toAlgHom
  let eBaseChange :
      (B ⊗[R] M) ≃ₗ[B] (B ⊗[A] (A ⊗[R] M)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B M).symm
  let _ : Module.Finite B (B ⊗[A] (A ⊗[R] M)) := inferInstance
  let _ : Module.Finite B (B ⊗[R] M) := Module.Finite.equiv eBaseChange.symm
  refine ⟨fun q ↦ ?_⟩
  let p := PrimeSpectrum.comap e.toRingHom q
  let eLoc := localizationAtPrime_algEquiv_of_algEquiv (R := R) e q
  let _ : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    eLoc.toRingHom.toAlgebra
  let _ : IsScalarTower R (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algHom eLoc.toAlgHom
  let _ :
      Module (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) :=
    Module.compHom (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) eLoc.toRingHom
  let _ :
      IsScalarTower (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) :=
    IsScalarTower.restrictScalars (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M))
  let eqv :
      LocalizedModule.AtPrime p.asIdeal (A ⊗[R] M) ≃ₗ[Localization.AtPrime p.asIdeal]
        LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M) :=
    localized_tensor_linearEquiv_of_algEquiv_atPrime (R := R) (M := M) e q
  let _ :
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (A ⊗[R] M)) :=
    h.localizedModule_cohenMacaulay p
  have hrestrict :
      Module.CohenMacaulay (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M)) := by
    -- First move the localized owner across the canonical localized tensor comparison.
    exact cohenMacaulay_of_linearEquiv eqv
  have hsurj :
      Function.Surjective
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
    -- The localized algebra equivalence identifies the target local ring with a quotient-free copy
    -- of the source one, so the induced local map is surjective.
    simpa using eLoc.surjective
  -- Then upgrade from the restricted `A_p`-module view back to the genuine `B_q`-module owner.
  exact
    (Module.cohenMacaulay_iff_restrictScalars_of_surjective
      (R := Localization.AtPrime p.asIdeal)
      (S := Localization.AtPrime q.asIdeal)
      (N := LocalizedModule.AtPrime q.asIdeal (B ⊗[R] M))
      hsurj).2 hrestrict

/-- Helper for Lemma 10.103.13: localizing the one-variable scalar extension at a maximal ideal
identifies it with tensoring the localized coefficient ring with the localized source module. -/
private noncomputable def localized_polynomial_tensor_equiv_atMaximal
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    LocalizedModule.AtPrime m.asIdeal ((Polynomial A) ⊗[A] N) ≃ₗ[Sm]
      Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  let _ : IsScalarTower A Ap Sm := .of_algebraMap_eq <| by
    intro x
    change (algebraMap (Polynomial A) Sm) (Polynomial.C x) =
      (algebraMap Ap Sm) ((algebraMap A Ap) x)
    exact
      (Localization.localRingHom_to_map (I := p.asIdeal) (J := m.asIdeal)
        (f := Polynomial.C) rfl x).symm
  let eLocalized :
      LocalizedModule.AtPrime m.asIdeal ((Polynomial A) ⊗[A] N) ≃ₗ[Sm]
        Sm ⊗[Polynomial A] ((Polynomial A) ⊗[A] N) :=
    -- First rewrite localization at `m` as tensoring with the local ring `Sm`.
    LocalizedModule.equivTensorProduct m.asIdeal.primeCompl ((Polynomial A) ⊗[A] N)
  let eCancelPolynomial :
      Sm ⊗[Polynomial A] ((Polynomial A) ⊗[A] N) ≃ₗ[Sm] Sm ⊗[A] N :=
    -- Cancel the intermediate polynomial-ring base change.
    TensorProduct.AlgebraTensorModule.cancelBaseChange A (Polynomial A) Sm Sm N
  let eInsertLocalization :
      Sm ⊗[A] N ≃ₗ[Sm] Sm ⊗[Ap] (Ap ⊗[A] N) :=
    -- Reinsert the coefficient localization so the source module appears as `N_p`.
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A Ap Sm Sm N).symm
  let eLocalizedSource :
      Sm ⊗[Ap] (Ap ⊗[A] N) ≃ₗ[Sm] Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Sm Sm)
      (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl N).symm
  exact eLocalized.trans <| eCancelPolynomial.trans <| eInsertLocalization.trans eLocalizedSource

/-- Helper for Lemma 10.103.13: the closed fiber of the local map `A_p → A[X]_m` has Krull
dimension `1`. -/
private theorem ringKrullDim_closedFiber_polynomial_atMaximal_eq_one
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    ringKrullDim (Sm ⧸ Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap)) = 1 := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  let _ : IsScalarTower A Ap Sm := .of_algebraMap_eq <| by
    intro x
    change (algebraMap (Polynomial A) Sm) (Polynomial.C x) =
      (algebraMap Ap Sm) ((algebraMap A Ap) x)
    exact
      (Localization.localRingHom_to_map (I := p.asIdeal) (J := m.asIdeal)
        (f := Polynomial.C) rfl x).symm
  have hformula :
      ringKrullDim Sm =
        ringKrullDim Ap + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) := by
    -- The quotient form of Lemma `10.112.7` expresses the local dimension by base plus fiber.
    simpa [p, Ap, Sm] using
      ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_quotient_of_hasGoingDown
        (R := A) (S := Polynomial A) m.toPrimeSpectrum
  have hSm :
      ringKrullDim Sm = p.asIdeal.height + 1 := by
    -- Identify `dim(Sm)` with the height of `m`, then use the polynomial height jump formula.
    calc
      ringKrullDim Sm = m.asIdeal.height := by
        simpa [Sm] using (IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal Sm)
      _ = p.asIdeal.height + 1 := by
        simpa [p] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞))
            (Polynomial.height_eq_height_add_one (p := p.asIdeal) (P := m.asIdeal))
  have hAp : ringKrullDim Ap = p.asIdeal.height := by
    -- The contracted base localization has dimension equal to the height of `p`.
    simpa [Ap] using (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal Ap)
  have hfiber :
      ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) = 1 := by
    let d : ℕ := p.asIdeal.height.toNat
    have hd : (d : WithBot ℕ∞) = p.asIdeal.height := by
      have hneTop : p.asIdeal.height ≠ ⊤ := ne_of_lt (Ideal.height_lt_top Ideal.IsPrime.ne_top')
      simpa [d] using
        (congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm).symm
    have hformula' :
        p.asIdeal.height + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) =
          p.asIdeal.height + 1 := by
      calc
        p.asIdeal.height + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) =
            ringKrullDim Ap + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) := by
              rw [hAp]
        _ = ringKrullDim Sm := hformula.symm
        _ = p.asIdeal.height + 1 := hSm
    have hformula'' :
        (d : WithBot ℕ∞) + ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) =
          d + 1 := by
      simpa [hd] using hformula'
    exact (ENat.WithBot.natCast_add_cancel (a := ringKrullDim
      (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal)) (b := (1 : WithBot ℕ∞)) (c := d)).1
      hformula''
  have hmap :
      Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap) =
        Ideal.map (algebraMap A Sm) p.asIdeal := by
    -- The maximal ideal of `Ap` is exactly the extension of `p`, so the two fiber ideals agree.
    calc
      Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap) =
          Ideal.map (algebraMap Ap Sm) (Ideal.map (algebraMap A Ap) p.asIdeal) := by
            rw [Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
      _ = Ideal.map ((algebraMap Ap Sm).comp (algebraMap A Ap)) p.asIdeal := by
            rw [Ideal.map_map]
      _ = Ideal.map (algebraMap A Sm) p.asIdeal := by
            simp [IsScalarTower.algebraMap_eq A Ap Sm]
  simpa [p, Ap, Sm] using
    calc
      ringKrullDim (Sm ⧸ Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap)) =
          ringKrullDim (Sm ⧸ Ideal.map (algebraMap A Sm) p.asIdeal) := by
            rw [hmap]
      _ = 1 := hfiber

/-- Helper for Lemma 10.103.13: once the source quotient over `A_p` has zero-dimensional support,
its tensor base change to `A[X]_m` has support dimension `1`. -/
private theorem supportDim_tensor_of_zeroDim_local_eq_one_atMaximal
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : MaximalSpectrum (Polynomial A))
    {Q0 : Type*} [AddCommGroup Q0]
    [Module (Localization.AtPrime (PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum).asIdeal) Q0]
    [Module.Finite (Localization.AtPrime (PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum).asIdeal)
      Q0]
    (hQ0 :
      Module.supportDim
          (Localization.AtPrime (PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum).asIdeal)
          Q0 = 0) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    Module.supportDim Sm (Sm ⊗[Ap] Q0) = 1 := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  have hsupp :
      Module.support Sm (Sm ⊗[Ap] Q0) =
        PrimeSpectrum.zeroLocus (Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap)) := by
    -- Base change sends support to the inverse image of support over `A_p`; the zero-dimensional
    -- hypothesis says that source support is exactly the closed point.
    rw [Module.Lemma_10_40_6,
      support_of_supportDim_eq_zero (R := Ap) (N := Q0) (by simpa [p, Ap] using hQ0),
      PrimeSpectrum.preimage_comap_zeroLocus]
    simp [Ideal.map]
  -- The support is the closed fiber, whose dimension was computed in the previous helper.
  calc
    Module.supportDim Sm (Sm ⊗[Ap] Q0) =
        Order.krullDim
          (PrimeSpectrum.zeroLocus (Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap))) := by
          rw [Module.supportDim, hsupp]
    _ = ringKrullDim (Sm ⧸ Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap)) := by
          rw [ringKrullDim_quotient]
    _ = 1 := by
          simpa [p, Ap, Sm] using ringKrullDim_closedFiber_polynomial_atMaximal_eq_one (A := A) m

/-- Helper for Chap10 Lemma 10 103 13: every regular sequence over a local ring is contained in
the maximal ideal. -/
private theorem isRegular_ofList_le_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A]
    {P : Type*} [AddCommGroup P] [Module A P]
    {rs : List A} (hreg : RingTheory.Sequence.IsRegular P rs) :
    Ideal.ofList rs ≤ IsLocalRing.maximalIdeal A := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  -- A regular-sequence element outside the maximal ideal is a unit, forcing the quotient by the
  -- generated ideal to be zero, contrary to regularity.
  by_contra hx_not_mem
  change x ∉ IsLocalRing.maximalIdeal A at hx_not_mem
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx_not_mem
  have hx_unit : IsUnit x := not_not.mp hx_not_mem
  have hx_mem : x ∈ Ideal.ofList rs := Ideal.subset_span hx
  have htop : Ideal.ofList rs = ⊤ :=
    Ideal.eq_top_of_isUnit_mem (Ideal.ofList rs) hx_mem hx_unit
  have hsmul : Ideal.ofList rs • (⊤ : Submodule A P) = ⊤ := by
    simp [htop]
  exact hreg.top_ne_smul hsmul.symm

/-- Helper for Chap10 Lemma 10 103 13: a regular sequence gives a lower bound for module depth. -/
private theorem length_le_moduleDepth_of_isRegular
    {A : Type*} [CommRing A] [IsLocalRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    {rs : List A} (hreg : RingTheory.Sequence.IsRegular P rs) :
    (rs.length : ℕ∞) ≤ moduleDepth A P := by
  by_cases htop : IsLocalRing.maximalIdeal A • (⊤ : Submodule A P) = ⊤
  · -- If the maximal ideal acts surjectively, the depth is infinite.
    rw [show moduleDepth A P = ⊤ from
      Ideal.depth_eq_top_of_smul_top (IsLocalRing.maximalIdeal A) P htop]
    exact le_top
  · -- Otherwise the depth is the supremum of lengths of regular sequences in the maximal ideal.
    rw [show moduleDepth A P =
        sSup (Ideal.regularSequenceLengths (IsLocalRing.maximalIdeal A) P) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (IsLocalRing.maximalIdeal A) P htop]
    exact le_sSup
      ⟨rs, hreg, isRegular_ofList_le_maximalIdeal hreg, by simp⟩

/-- Helper for Chap10 Lemma 10 103 13: a finite module with a regular sequence whose length is the
support dimension is Cohen-Macaulay. -/
private theorem cohenMacaulay_of_supportDim_eq_length_of_isRegular
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P]
    {rs : List A} (hdim : Module.supportDim A P = rs.length)
    (hreg : RingTheory.Sequence.IsRegular P rs) : Module.CohenMacaulay A P := by
  let _ : Nontrivial P := hreg.nontrivial
  have hdepth_le :
      WithBot.some (moduleDepth A P : ℕ∞) ≤ Module.supportDim A P :=
    depth_le_supportDim
  have hlen_le : (rs.length : ℕ∞) ≤ moduleDepth A P :=
    length_le_moduleDepth_of_isRegular hreg
  have hsupport_le :
      Module.supportDim A P ≤ WithBot.some (moduleDepth A P : ℕ∞) := by
    -- The supplied full-length regular sequence gives the reverse inequality.
    rw [hdim]
    exact WithBot.coe_le_coe.2 hlen_le
  exact ⟨le_antisymm hsupport_le hdepth_le⟩

/-- Helper for Chap10 Lemma 10 103 13: the explicit polynomial map from the localized coefficient
polynomial ring to the maximal localization sends the variable to the localized polynomial
variable. -/
private noncomputable def polynomialAtPrimeToAtMaximalAlgHom
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    Polynomial Ap →ₐ[Ap] Sm :=
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  Polynomial.aeval (algebraMap (Polynomial A) Sm Polynomial.X)

/-- Helper for Chap10 Lemma 10 103 13: the explicit maximal-local polynomial map sends `X` to
the localized polynomial variable. -/
private theorem polynomialAtPrimeToAtMaximalAlgHom_X
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    polynomialAtPrimeToAtMaximalAlgHom m Polynomial.X =
      algebraMap (Polynomial A) Sm Polynomial.X := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  -- This is the computation rule that prevents the closed-fiber variable from normalizing to the
  -- wrong inferred algebra-map spelling.
  exact Polynomial.aeval_X (algebraMap (Polynomial A) Sm Polynomial.X)

/-- Helper for Chap10 Lemma 10 103 13: localizing a polynomial ring at a maximal ideal raises
the dimension of the contracted coefficient localization by one. -/
private theorem ringKrullDim_polynomialAtMaximal_eq_base_add_one
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    ringKrullDim Sm = ringKrullDim Ap + 1 := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  have hSm : ringKrullDim Sm = p.asIdeal.height + 1 := by
    -- The maximal localization has dimension equal to the height of the chosen maximal ideal,
    -- and the polynomial height formula computes that height over the contraction.
    calc
      ringKrullDim Sm = m.asIdeal.height := by
        simpa [Sm] using (IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal Sm)
      _ = p.asIdeal.height + 1 := by
        simpa [p] using
          congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞))
            (Polynomial.height_eq_height_add_one (p := p.asIdeal) (P := m.asIdeal))
  have hAp : ringKrullDim Ap = p.asIdeal.height := by
    -- The coefficient localization has dimension equal to the contracted prime height.
    simpa [Ap] using (IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal Ap)
  simpa [p, Ap, Sm] using
    calc
      ringKrullDim Sm = p.asIdeal.height + 1 := hSm
      _ = ringKrullDim Ap + 1 := by rw [hAp]

/-- Helper for Chap10 Lemma 10 103 13: the Krull dimension of a Noetherian local ring is
represented by a natural number. -/
private theorem localNoetherian_ringKrullDim_eq_nat
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ n : ℕ, ringKrullDim A = n := by
  -- Isolate the finite-dimensional local-ring fact so later regular-sequence choices can work
  -- with the `Nat`-valued depth API.
  have hbot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim A).unbot hbot).toNat
  have hneTop : (ringKrullDim A).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim' : ((ringKrullDim A).unbot hbot : WithBot ℕ∞) = n := by
    simpa [n] using
      congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
  refine ⟨n, ?_⟩
  calc
    ringKrullDim A = (ringKrullDim A).unbot hbot := by
      exact (WithBot.coe_unbot (ringKrullDim A) hbot).symm
    _ = n := hdim'

/-- Helper for Chap10 Lemma 10 103 13: a locally Cohen-Macaulay module gives a
dimension-realizing regular sequence after localizing at any prime. -/
private theorem fullRegularSequence_atPrime_of_locallyCohenMacaulay
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {N : Type v} [AddCommGroup N] [Module A N]
    (hCM : Module.LocallyCohenMacaulay A N) (p : PrimeSpectrum A) :
    let Ap := Localization.AtPrime p.asIdeal
    let Np := LocalizedModule.AtPrime p.asIdeal N
    ∃ d : ℕ, ringKrullDim Ap = d ∧
      ∃ rs : List Ap,
        RingTheory.Sequence.IsRegular Np rs ∧
          Ideal.ofList rs ≤ IsLocalRing.maximalIdeal Ap ∧ rs.length = d := by
  let Ap := Localization.AtPrime p.asIdeal
  let Np := LocalizedModule.AtPrime p.asIdeal N
  let _ : Module.Finite A N := hCM.toFinite
  let hlocal : Module.CohenMacaulay Ap Np := hCM.localizedModule_cohenMacaulay p
  have hsuppA : Module.support A N = Set.univ :=
    support_eq_univ_of_locallyCohenMacaulay hCM
  have hsuppNp : Module.support Ap Np = Set.univ :=
    support_localizedModuleAtPrime_eq_univ_of_support_eq_univ hsuppA p
  have hdimNp : Module.supportDim Ap Np = ringKrullDim Ap :=
    supportDim_eq_ringKrullDim_of_support_eq_univ hsuppNp
  obtain ⟨d, hd⟩ := localNoetherian_ringKrullDim_eq_nat (A := Ap)
  have hdepth : moduleDepth Ap Np = d := by
    -- The Cohen-Macaulay equality and full support identify the localized depth with `dim A_p`.
    have hdepth_cast : ((moduleDepth Ap Np : ℕ∞) : WithBot ℕ∞) = d := by
      calc
        ((moduleDepth Ap Np : ℕ∞) : WithBot ℕ∞) = Module.supportDim Ap Np :=
          hlocal.supportDim_eq_moduleDepth.symm
        _ = ringKrullDim Ap := hdimNp
        _ = d := hd
    exact WithBot.coe_inj.mp hdepth_cast
  let _ : Small.{u} Np := Module.Finite.small (R := Ap) (M := Np)
  let eShrink : Shrink.{u} Np ≃ₗ[Ap] Np := Shrink.linearEquiv Ap Np
  have hdepthShrink : moduleDepth Ap (Shrink.{u} Np) = d := by
    -- The depth-realizing regular-sequence theorem is same-universe, so first move to the
    -- shrunken finite module and preserve depth by linear equivalence.
    rw [moduleDepth_eq_of_equiv eShrink]
    exact hdepth
  let _ : Nontrivial Np := by
    -- The localized Cohen-Macaulay equality makes the support dimension non-bottom, hence the
    -- localized module is nonzero.
    refine (Module.supportDim_ne_bot_iff_nontrivial Ap Np).mp ?_
    rw [hlocal.supportDim_eq_moduleDepth]
    simp
  obtain ⟨rs, hregShrink, hle, hlen⟩ :=
    exists_regularSequence_of_length_eq_moduleDepth (R := Ap) (M := Shrink.{u} Np)
      hdepthShrink
  have hreg : RingTheory.Sequence.IsRegular Np rs := by
    -- Regularity is invariant under the same linear equivalence, while the sequence remains in
    -- the coefficient local ring.
    exact (eShrink.isRegular_congr rs).1 hregShrink
  exact ⟨d, hd, rs, hreg, hle, hlen⟩

/-- Helper for Chap10 Lemma 10 103 13: the maximal-local tensor model has full support, so its
support dimension is the Krull dimension of `A[X]_m`. -/
private theorem supportDim_tensor_atMaximal_eq_ringKrullDim
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (hCM : Module.LocallyCohenMacaulay A N) (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    Module.supportDim Sm (Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N) = ringKrullDim Sm := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  let _ : Module.Finite A N := hCM.toFinite
  have hsuppA : Module.support A N = Set.univ :=
    support_eq_univ_of_locallyCohenMacaulay hCM
  have hsuppNp : Module.support Ap (LocalizedModule.AtPrime p.asIdeal N) = Set.univ :=
    support_localizedModuleAtPrime_eq_univ_of_support_eq_univ hsuppA p
  have hsuppTensor :
      Module.support Sm (Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N) = Set.univ := by
    -- Move through the base-change support formula and use full support of the source
    -- localization.
    rw [Module.Lemma_10_40_6, hsuppNp]
    ext q
    simp
  exact supportDim_eq_ringKrullDim_of_support_eq_univ hsuppTensor

/-- Helper for Chap10 Lemma 10 103 13: a full-length regular sequence on the maximal-local
tensor model gives the desired Cohen-Macaulay owner for that model. -/
private theorem cohenMacaulay_tensor_atMaximal_of_full_regularSequence
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (hCM : Module.LocallyCohenMacaulay A N) (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    ∀ {rs : List Sm},
      RingTheory.Sequence.IsRegular (Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N) rs →
        ringKrullDim Sm = rs.length →
          Module.CohenMacaulay Sm (Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N) := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  let _ : Module.Finite A N := hCM.toFinite
  dsimp
  intro rs hreg hlen
  change RingTheory.Sequence.IsRegular (Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N) rs at hreg
  change ringKrullDim Sm = rs.length at hlen
  change Module.CohenMacaulay Sm (Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N)
  have hsupport :
      Module.supportDim Sm (Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N) = rs.length := by
    -- The previous support computation identifies the tensor model support with `Spec Sm`; the
    -- supplied regular sequence has exactly that dimension.
    calc
      Module.supportDim Sm (Sm ⊗[Ap] LocalizedModule.AtPrime p.asIdeal N) = ringKrullDim Sm := by
        simpa [p, Ap, Sm] using supportDim_tensor_atMaximal_eq_ringKrullDim hCM m
      _ = rs.length := hlen
  exact cohenMacaulay_of_supportDim_eq_length_of_isRegular hsupport hreg

/-- Helper for Chap10 Lemma 10 103 13: mapping a regular sequence along an algebra map only
changes the scalar spelling of its action on the same module. -/
private theorem isRegular_map_algebraMap_iff_of_scalarTower
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {P : Type*} [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
    (rs : List A) :
    RingTheory.Sequence.IsRegular P (rs.map (algebraMap A B)) ↔
      RingTheory.Sequence.IsRegular P rs := by
  -- The identity additive equivalence intertwines the two actions by the scalar tower law.
  exact
    (AddEquiv.refl P).isRegular_congr <|
      List.forall₂_map_left_iff.mpr <|
        List.forall₂_same.mpr fun r _ => algebraMap_smul B r

/-- Helper for Chap10 Lemma 10 103 13: a local algebra map sends a list contained in the source
maximal ideal to a list contained in the target maximal ideal. -/
private theorem ofList_map_algebraMap_le_maximalIdeal_of_localHom
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] {rs : List A}
    (hrs : Ideal.ofList rs ≤ IsLocalRing.maximalIdeal A) :
    Ideal.ofList (rs.map (algebraMap A B)) ≤ IsLocalRing.maximalIdeal B := by
  -- The generated ideal maps to the generated ideal of the mapped list, and a local map sends
  -- the source maximal ideal into the target maximal ideal.
  simpa [Ideal.map_ofList] using
    (Ideal.map_mono (f := algebraMap A B) hrs).trans
      (IsLocalRing.map_maximalIdeal_le (algebraMap A B))

/-- Helper for Chap10 Lemma 10 103 13: a regular sequence on the coefficient localization remains
regular after the flat local base change to the maximal localization of the polynomial ring. -/
private theorem isRegular_tensor_atMaximal_of_sourceRegularSequence
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let Np := LocalizedModule.AtPrime p.asIdeal N
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    ∀ {rs : List Ap},
      RingTheory.Sequence.IsRegular Np rs →
        RingTheory.Sequence.IsRegular (Sm ⊗[Ap] Np) (rs.map (algebraMap Ap Sm)) := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  let Np := LocalizedModule.AtPrime p.asIdeal N
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let fLoc : Ap →+* Sm := Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl
  let _ : Algebra Ap Sm := fLoc.toAlgebra
  let _ : IsLocalHom (algebraMap Ap Sm) := by
    -- The algebra map is the canonical local homomorphism between the two localizations.
    change IsLocalHom fLoc
    exact Localization.isLocalHom_localRingHom (I := p.asIdeal) (J := m.asIdeal) Polynomial.C rfl
  let _ : Module.Flat Ap Sm := by
    -- Polynomial extension is free, hence flat; localizing the flat map keeps it flat.
    have hCflat : (Polynomial.C : A →+* Polynomial A).Flat := by
      change (algebraMap A (Polynomial A)).Flat
      rw [RingHom.flat_algebraMap_iff]
      exact Module.Flat.of_free
    have hflat : fLoc.Flat := RingHom.Flat.localRingHom hCflat m.asIdeal p.asIdeal rfl
    rw [RingHom.Flat] at hflat
    exact hflat
  dsimp
  intro rs hrs
  -- Apply the flat-local regular-sequence theorem to the canonical map `A_p -> A[X]_m`.
  exact
    (isRegular_iff_isRegular_tensorBaseChange_of_flat_localHom
      (R := Ap) (S := Sm) (M := Np)).1 hrs

/-- Helper for Chap10 Lemma 10 103 13: the submodule generated by a mapped list in a tensor
base-change is the tensor-side extension of the source-list submodule. -/
private theorem ofList_map_smul_top_eq_idealMap_ofList_smul_top
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {M : Type*} [AddCommGroup M] [Module A M] (rs : List A) :
    (Ideal.ofList (rs.map (algebraMap A B)) • (⊤ : Submodule B (B ⊗[A] M))) =
      (Ideal.map (algebraMap A B) (Ideal.ofList rs) •
        (⊤ : Submodule B (B ⊗[A] M))) := by
  -- The mapped list and the mapped source ideal generate the same ideal in the target ring.
  rw [Ideal.map_ofList]

/-- Helper for Chap10 Lemma 10 103 13: quotienting the tensor base change by a mapped source list
is canonically the tensor base change of the source quotient. -/
private noncomputable def tensorQuotientOfListMapEquiv
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {M : Type*} [AddCommGroup M] [Module A M] (rs : List A) :
    ((B ⊗[A] M) ⧸
      (Ideal.ofList (rs.map (algebraMap A B)) • (⊤ : Submodule B (B ⊗[A] M)))) ≃ₗ[B]
        B ⊗[A] (M ⧸ (Ideal.ofList rs • (⊤ : Submodule A M))) :=
  (Submodule.quotEquivOfEq _ _
    (ofList_map_smul_top_eq_idealMap_ofList_smul_top (B := B) (M := M) rs)).trans
      (TensorProduct.tensorQuotMapSMulEquivTensorQuot M B (Ideal.ofList rs))

/-- Helper for Chap10 Lemma 10 103 13: if a target element is regular and its principal quotient
is flat over the base, then it remains regular after tensoring with a finite base module. -/
private theorem isSMulRegular_tensor_of_regular_flat_quotSMulTop
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {P : Type*} [AddCommGroup P] [Module B P] [Module A P] [IsScalarTower A B P]
    [Module.Finite B P] {t : B}
    (ht : IsSMulRegular P t) (hflat : Module.Flat A (QuotSMulTop t P)) :
    IsSMulRegular (P ⊗[A] M) t := by
  let u : P →ₗ[A] P := (LinearMap.lsmul B P t).restrictScalars A
  have hu : Function.Injective u := by
    -- Forgetting to `A`-linearity does not change the underlying multiplication by `t`.
    intro x y hxy
    apply ht
    simpa [u] using hxy
  let K : Submodule B P := Ideal.span ({t} : Set B) • (⊤ : Submodule B P)
  have hrange :
      LinearMap.range (LinearMap.lsmul B P t) = K := by
    -- The range of multiplication by `t` is the pointwise submodule `tP`.
    dsimp [K]
    rw [Submodule.ideal_span_singleton_smul]
    ext n
    constructor
    · rintro ⟨m, rfl⟩
      exact Submodule.smul_mem_pointwise_smul m t (⊤ : Submodule B P) trivial
    · intro hn
      rcases (Submodule.mem_smul_pointwise_iff_exists n t (⊤ : Submodule B P)).1 hn with
        ⟨m, -, hm⟩
      exact ⟨m, by simpa [LinearMap.lsmul_apply] using hm⟩
  have hflatRange : Module.Flat A (P ⧸ LinearMap.range u) := by
    -- Rewrite the assumed flatness of `P/tP` through the range of the restricted map.
    have hflatSmul : Module.Flat A (P ⧸ K.restrictScalars A) := by
      let eSpan : (P ⧸ K) ≃ₗ[B] QuotSMulTop t P :=
        Submodule.quotEquivOfEq _ _ (by
          dsimp [K, QuotSMulTop]
          rw [Submodule.ideal_span_singleton_smul])
      let _ : Module.Flat A (P ⧸ K) := by
        let _ : Module.Flat A (QuotSMulTop t P) := hflat
        exact Module.Flat.of_linearEquiv (eSpan.restrictScalars A)
      let e : (P ⧸ K.restrictScalars A) ≃ₗ[A] P ⧸ K :=
        Submodule.Quotient.restrictScalarsEquiv A K
      exact Module.Flat.of_linearEquiv e
    rw [LinearMap.range_restrictScalars, hrange]
    exact hflatSmul
  have huTensor : Function.Injective (u.lTensor M) :=
    LinearMap.lTensor_injective_of_exact_of_flat
      (Submodule.mkQ (LinearMap.range u))
      (Submodule.mkQ_surjective _)
      u
      hu
      (LinearMap.exact_map_mkQ_range u)
      M
  have huRTensor : Function.Injective (u.rTensor M) := by
    -- Switch from left tensoring to the right-tensor spelling used by `P ⊗[A] M`.
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    exact huTensor
  have huRTensor_eq :
      u.rTensor M = (LinearMap.lsmul B (P ⊗[A] M) t).restrictScalars A := by
    -- Both endomorphisms send a pure tensor to `(t • p) ⊗ m`.
    ext p m
    simp [u, TensorProduct.smul_tmul']
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro z hz
  apply huRTensor
  -- Injectivity of the tensorized multiplication map is exactly regularity on the tensor product.
  simpa [huRTensor_eq] using hz

/-- Helper for Chap10 Lemma 10 103 13: a ring-level regular flat parameter is regular on the
quotient by any mapped source sequence in the tensor base change. -/
private theorem isSMulRegular_mappedSourceQuotient_of_regular_flat_quotSMulTop
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (rs : List A) {t : B}
    (ht : IsSMulRegular B t) (hflat : Module.Flat A (QuotSMulTop t B)) :
    IsSMulRegular
      ((B ⊗[A] M) ⧸
        (Ideal.ofList (rs.map (algebraMap A B)) • (⊤ : Submodule B (B ⊗[A] M)))) t := by
  let Q0 := M ⧸ (Ideal.ofList rs • (⊤ : Submodule A M))
  have htTensor : IsSMulRegular (B ⊗[A] Q0) t := by
    -- Apply the flat-principal-quotient tensor lemma with the self-module `B`.
    exact isSMulRegular_tensor_of_regular_flat_quotSMulTop
      (A := A) (B := B) (M := Q0) (P := B) ht hflat
  let e := tensorQuotientOfListMapEquiv (B := B) (M := M) rs
  -- Transport regularity back through the canonical quotient/base-change equivalence.
  exact (LinearEquiv.isSMulRegular_congr e t).2 htTensor

/-- Helper for Chap10 Lemma 10 103 13: after mapping a full source regular sequence to the
polynomial maximal localization, the quotient has the one-dimensional closed-fiber support. -/
private theorem supportDim_quotient_mapped_source_regularSequence_eq_one_atMaximal
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (hCM : Module.LocallyCohenMacaulay A N) (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let Np := LocalizedModule.AtPrime p.asIdeal N
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    ∀ {d : ℕ} {rs : List Ap},
      ringKrullDim Ap = d →
        RingTheory.Sequence.IsRegular Np rs →
          rs.length = d →
            Module.supportDim Sm
                ((Sm ⊗[Ap] Np) ⧸
                  (Ideal.ofList (rs.map (algebraMap Ap Sm)) •
                    (⊤ : Submodule Sm (Sm ⊗[Ap] Np)))) = 1 := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  let Np := LocalizedModule.AtPrime p.asIdeal N
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  let _ : Module.Finite A N := hCM.toFinite
  dsimp
  intro d rs hdAp hrs hlenrs
  have hdimSm : ringKrullDim Sm = d + 1 := by
    -- The maximal polynomial localization has exactly one more dimension than the coefficient
    -- localization, and the source sequence realizes the coefficient dimension.
    calc
      ringKrullDim Sm = ringKrullDim Ap + 1 := by
        simpa [p, Ap, Sm] using ringKrullDim_polynomialAtMaximal_eq_base_add_one (A := A) m
      _ = d + 1 := by
        have hdAp' : ringKrullDim Ap = d := by
          simpa [p, Ap] using hdAp
        rw [hdAp']
  have hsourceOnTensor :
      RingTheory.Sequence.IsRegular (Sm ⊗[Ap] Np) (rs.map (algebraMap Ap Sm)) := by
    -- Regularity of the source sequence survives the flat local base change `A_p -> A[X]_m`.
    simpa [p, Ap, Sm, Np] using
      isRegular_tensor_atMaximal_of_sourceRegularSequence (N := N) m hrs
  have hsupportTensor :
      Module.supportDim Sm (Sm ⊗[Ap] Np) = d + 1 := by
    -- The tensor model has full support, so its support dimension is the polynomial-local Krull
    -- dimension computed above.
    calc
      Module.supportDim Sm (Sm ⊗[Ap] Np) = ringKrullDim Sm := by
        simpa [p, Ap, Sm, Np] using supportDim_tensor_atMaximal_eq_ringKrullDim hCM m
      _ = d + 1 := hdimSm
  have hdrop :
      Module.supportDim Sm
          ((Sm ⊗[Ap] Np) ⧸
            (Ideal.ofList (rs.map (algebraMap Ap Sm)) •
              (⊤ : Submodule Sm (Sm ⊗[Ap] Np)))) +
        d = d + 1 := by
    -- Quotienting by the mapped regular sequence lowers support dimension by its source length.
    have hsupportTensor' :
        Module.supportDim Sm (Sm ⊗[Ap] Np) = rs.length + 1 := by
      simpa [hlenrs] using hsupportTensor
    rw [← hlenrs]
    simpa [List.length_map, hsupportTensor'] using
      (Module.supportDim_add_length_eq_supportDim_of_isRegular
        (M := Sm ⊗[Ap] Np) (rs := rs.map (algebraMap Ap Sm)) hsourceOnTensor)
  cases hquot :
      Module.supportDim Sm
        ((Sm ⊗[Ap] Np) ⧸
          (Ideal.ofList (rs.map (algebraMap Ap Sm)) •
            (⊤ : Submodule Sm (Sm ⊗[Ap] Np)))) with
  | bot =>
      -- The dimension-drop equality rules out bottom support for the quotient.
      have hbot : (⊥ : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞) + 1 := by
        simpa [hquot] using hdrop
      cases hbot
  | coe q =>
      have hcancel :
          ((q : ℕ∞) : WithBot ℕ∞) = (1 : WithBot ℕ∞) := by
        exact
          (ENat.WithBot.natCast_add_cancel
            (a := ((q : ℕ∞) : WithBot ℕ∞)) (b := (1 : WithBot ℕ∞)) (c := d)).1 <| by
            simpa [hquot, add_comm, add_left_comm, add_assoc] using hdrop
      -- After cancellation, the quotient support dimension is exactly the closed-fiber dimension.
      exact hquot.trans hcancel

/-- Helper for Chap10 Lemma 10 103 13: a quotient-regular parameter extends a verified regular
prefix, and the local permutation theorem moves the new parameter to the front. -/
private theorem isRegular_cons_of_regular_prefix_and_smulRegular_quotient
    {A : Type*} [CommRing A] [IsLocalRing A]
    {P : Type*} [AddCommGroup P] [Module A P] [Module.Finite A P] [IsNoetherian A P]
    {rs : List A} {t : A}
    (hprefix : RingTheory.Sequence.IsRegular P rs)
    (hrs : Ideal.ofList rs ≤ IsLocalRing.maximalIdeal A)
    (ht : t ∈ IsLocalRing.maximalIdeal A)
    (hquot : IsSMulRegular
      (P ⧸ (Ideal.ofList rs • (⊤ : Submodule A P))) t) :
    RingTheory.Sequence.IsRegular P (t :: rs) := by
  letI : Nontrivial P := hprefix.nontrivial
  let Q := P ⧸ (Ideal.ofList rs • (⊤ : Submodule A P))
  have hquotQ :
      IsSMulRegular Q (Ideal.Quotient.mk (Ideal.ofList rs) t) := by
    -- The quotient module has the same scalar action whether `t` is read in `A` or in
    -- `A / Ideal.ofList rs`.
    exact (isSMulRegular_algebraMap_iff (A := A ⧸ Ideal.ofList rs) (M := Q) (r := t)).2
      hquot
  have hweak : RingTheory.Sequence.IsWeaklyRegular P (rs ++ [t]) := by
    -- Append the singleton tail using the regularity of `t` on the prefix quotient.
    rw [RingTheory.Sequence.isWeaklyRegular_append_iff' (M := P) rs [t]]
    constructor
    · exact hprefix.toIsWeaklyRegular
    · simpa [Q] using
        (RingTheory.Sequence.isWeaklyRegular_singleton_iff
          (M := Q) (Ideal.Quotient.mk (Ideal.ofList rs) t)).mpr hquotQ
  have hmem : ∀ r ∈ rs ++ [t], r ∈ IsLocalRing.maximalIdeal A := by
    -- The prefix is already in the maximal ideal, and the new parameter is chosen there.
    intro r hr
    rw [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hrs (Ideal.subset_span hr)
    · exact ht
  have happ : RingTheory.Sequence.IsRegular P (rs ++ [t]) := by
    -- In a local ring, weak regularity plus maximal-ideal containment gives regularity.
    exact RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal P hmem hweak
  have hperm : List.Perm (rs ++ [t]) (t :: rs) := by
    simpa using (List.perm_middle : List.Perm (rs ++ t :: []) (t :: (rs ++ [])))
  -- Finally put the new regular parameter in the head position required by the downstream theorem.
  exact IsLocalRing.isRegular_of_perm happ hperm

/-- Helper for Chap10 Lemma 10 103 13: ring regularity is scalar regularity for the self-module
over a commutative ring. -/
private theorem isSMulRegular_selfModule_of_isRegular
    {A : Type*} [CommRing A] {a : A} (h : IsRegular a) : IsSMulRegular A a := by
  -- Both regularity predicates say that multiplication by `a` has zero kernel.
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left] at h
  simpa [Algebra.smul_def, mul_comm] using h

/-- Helper for Chap10 Lemma 10 103 13: a one-dimensional local domain contains a regular
nonunit. -/
private theorem exists_regular_nonunit_of_local_domain_ringKrullDim_eq_one
    {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    (hdim : ringKrullDim A = 1) :
    ∃ x : A, IsRegular x ∧ ¬ IsUnit x := by
  have hnotField : ¬ IsField A :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain (R := A)).mp hdim |>.1
  have hm_ne_bot : IsLocalRing.maximalIdeal A ≠ ⊥ := by
    -- If the maximal ideal vanished, the local domain would be a field, contradicting dimension
    -- one.
    intro hm
    exact hnotField ((IsLocalRing.isField_iff_maximalIdeal_eq (R := A)).2 hm)
  obtain ⟨x, hxmem, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm_ne_bot
  refine ⟨x, ?_, ?_⟩
  · -- In a domain, every nonzero element is regular.
    simpa [isRegular_iff_ne_zero] using hx0
  · -- Membership in the maximal ideal of a local ring is exactly nonunitness.
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hxmem

/-- Helper for Chap10 Lemma 10 103 13: the closed-fiber ideal of
`A_p → A[X]_m` is the localization of the contracted prime from `A`. -/
private theorem closedFiber_polynomialAtMaximal_map_maximal_eq
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap) =
      Ideal.map (algebraMap A Sm) p.asIdeal := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  let _ : IsScalarTower A Ap Sm := .of_algebraMap_eq <| by
    intro x
    change (algebraMap (Polynomial A) Sm) (Polynomial.C x) =
      (algebraMap Ap Sm) ((algebraMap A Ap) x)
    exact
      (Localization.localRingHom_to_map (I := p.asIdeal) (J := m.asIdeal)
        (f := Polynomial.C) rfl x).symm
  -- Rewrite the maximal ideal of `A_p` as the extension of `p`, then compose the two maps.
  calc
    Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap) =
        Ideal.map (algebraMap Ap Sm) (Ideal.map (algebraMap A Ap) p.asIdeal) := by
          rw [Localization.AtPrime.map_eq_maximalIdeal (I := p.asIdeal)]
    _ = Ideal.map ((algebraMap Ap Sm).comp (algebraMap A Ap)) p.asIdeal := by
          rw [Ideal.map_map]
    _ = Ideal.map (algebraMap A Sm) p.asIdeal := by
          simp [IsScalarTower.algebraMap_eq A Ap Sm]

/-- Helper for Chap10 Lemma 10 103 13: the polynomial closed fiber
`A[X]_m / p A[X]_m` is a domain. -/
private theorem closedFiber_polynomialAtMaximal_isDomain
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    IsDomain (Sm ⧸ Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap)) := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  change IsDomain (Sm ⧸ Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap))
  have hmapLocal :
      Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap) =
        Ideal.map (algebraMap A Sm) p.asIdeal := by
    simpa [p, Ap, Sm] using closedFiber_polynomialAtMaximal_map_maximal_eq (A := A) m
  have hprimeA : (Ideal.map (algebraMap A Sm) p.asIdeal).IsPrime := by
    have hCpPrime : (Ideal.map Polynomial.C p.asIdeal : Ideal (Polynomial A)).IsPrime := by
      infer_instance
    letI : (Ideal.map Polynomial.C p.asIdeal : Ideal (Polynomial A)).IsPrime := hCpPrime
    have hCp_le_m : Ideal.map Polynomial.C p.asIdeal ≤ m.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      change p.asIdeal ≤ p.asIdeal
      exact le_rfl
    have hlocPrime :
        (Ideal.map (algebraMap (Polynomial A) Sm)
          (Ideal.map Polynomial.C p.asIdeal)).IsPrime := by
      -- The extension of the prime `pA[X]` remains prime after localizing at `m`.
      exact Ideal.isPrime_map_of_isLocalizationAtPrime (q := m.asIdeal) (S := Sm)
        (p := Ideal.map Polynomial.C p.asIdeal) hCp_le_m
    have hmapA :
        Ideal.map (algebraMap (Polynomial A) Sm) (Ideal.map Polynomial.C p.asIdeal) =
          Ideal.map (algebraMap A Sm) p.asIdeal := by
      rw [Ideal.map_map]
      simp [IsScalarTower.algebraMap_eq A (Polynomial A) Sm]
    rwa [hmapA] at hlocPrime
  rw [hmapLocal]
  exact Ideal.Quotient.isDomain (Ideal.map (algebraMap A Sm) p.asIdeal)

/-- Helper for Chap10 Lemma 10 103 13: the one-dimensional polynomial closed fiber contains a
regular nonunit. -/
private theorem closedFiber_polynomialAtMaximal_exists_regular_nonunit
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : MaximalSpectrum (Polynomial A)) :
    let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
    let Ap := Localization.AtPrime p.asIdeal
    let Sm := Localization.AtPrime m.asIdeal
    let _ : Algebra Ap Sm :=
      (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
    ∃ x : Sm ⧸ Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap),
      IsRegular x ∧ ¬ IsUnit x := by
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  let I : Ideal Sm := Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap)
  change ∃ x : Sm ⧸ I, IsRegular x ∧ ¬ IsUnit x
  have hdomain : IsDomain (Sm ⧸ I) := by
    simpa [p, Ap, Sm, I] using closedFiber_polynomialAtMaximal_isDomain (A := A) m
  letI : IsDomain (Sm ⧸ I) := hdomain
  have hnontrivial : Nontrivial (Sm ⧸ I) := inferInstance
  letI : Nontrivial (Sm ⧸ I) := hnontrivial
  letI : IsLocalRing (Sm ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hdim : ringKrullDim (Sm ⧸ I) = 1 := by
    -- The preceding dimension computation is exactly the dimension of this quotient fiber.
    simpa [p, Ap, Sm, I] using ringKrullDim_closedFiber_polynomial_atMaximal_eq_one (A := A) m
  exact exists_regular_nonunit_of_local_domain_ringKrullDim_eq_one (A := Sm ⧸ I) hdim

/-- Helper for Chap10 Lemma 10 103 13: a regular nonunit in the closed fiber lifts to an upstairs
parameter whose principal quotient is flat over the base. -/
private theorem exists_regular_flat_principal_quotient_of_closedFiber_regular_nonunit
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [IsNoetherianRing B] [Module.Flat A B]
    (hfiber :
      ∃ x : B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A),
        IsRegular x ∧ ¬ IsUnit x) :
    ∃ t : B,
      t ∈ IsLocalRing.maximalIdeal B ∧
        IsSMulRegular B t ∧ Module.Flat A (QuotSMulTop t B) := by
  obtain ⟨x, hxReg, hxNonunit⟩ := hfiber
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hfiberReg : IsRegular
      (Ideal.Quotient.mk
        (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) t) := by
    -- The chosen closed-fiber element is already regular in the ring sense.
    exact hxReg
  obtain ⟨hflatSpan, htRegularRing⟩ :=
    flat_quotient_and_nonZeroDivisor_of_fiber_nonZeroDivisor (R := A) (S := B) t hfiberReg
  have htMax : t ∈ IsLocalRing.maximalIdeal B := by
    -- A unit lift would make the closed-fiber class a unit, contradicting the choice of `x`.
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro htUnit
    exact hxNonunit (htUnit.map
      (Ideal.Quotient.mk (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))))
  have htRegular : IsSMulRegular B t :=
    isSMulRegular_selfModule_of_isRegular htRegularRing
  have hflatQuotSMul : Module.Flat A (QuotSMulTop t B) := by
    -- Replace the ring quotient `B/(t)` from Lemma 10.99.2 by the owner quotient
    -- `QuotSMulTop t B` used by regular-sequence API.
    let eSpan : (B ⧸ Ideal.span ({t} : Set B)) ≃ₗ[B] QuotSMulTop t B :=
      Submodule.quotEquivOfEq _ _ (by
        simp [← Submodule.ideal_span_singleton_smul])
    exact Module.Flat.of_linearEquiv (eSpan.restrictScalars A).symm
  exact ⟨t, htMax, htRegular, hflatQuotSMul⟩

/-- Chap10 Lemma 10 103 13 (Lemma 10.103.13): the source-faithful maximal-local one-variable
polynomial step. -/
private theorem polynomial_atMaximal
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (hCM : Module.LocallyCohenMacaulay A N) (m : MaximalSpectrum (Polynomial A)) :
    Module.CohenMacaulay (Localization.AtPrime m.asIdeal)
      (LocalizedModule.AtPrime m.asIdeal ((Polynomial A) ⊗[A] N)) := by
  -- Route correction: keep the proof in the tensor model `Sm ⊗[Ap] Np` and postpone the
  -- localization/tensor equivalence until the final line.
  let p := PrimeSpectrum.comap Polynomial.C m.toPrimeSpectrum
  let Ap := Localization.AtPrime p.asIdeal
  let Sm := Localization.AtPrime m.asIdeal
  let Np := LocalizedModule.AtPrime p.asIdeal N
  have hlie : m.asIdeal.LiesOver p.asIdeal := by
    refine ⟨?_⟩
    change Ideal.comap Polynomial.C m.asIdeal = p.asIdeal
    rfl
  let _ : m.asIdeal.LiesOver p.asIdeal := hlie
  let _ : Algebra Ap Sm :=
    (Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl).toAlgebra
  let _ : Module.Finite A N := hCM.toFinite
  let eModel :
      LocalizedModule.AtPrime m.asIdeal ((Polynomial A) ⊗[A] N) ≃ₗ[Sm] Sm ⊗[Ap] Np := by
    -- The earlier equivalence identifies the target localization with the stable tensor model.
    simpa [p, Ap, Sm, Np] using localized_polynomial_tensor_equiv_atMaximal (N := N) m
  have hmodel : Module.CohenMacaulay Sm (Sm ⊗[Ap] Np) := by
    obtain ⟨d, hdAp, rs, hrs, _hrsMax, hlenrs⟩ :=
      fullRegularSequence_atPrime_of_locallyCohenMacaulay (A := A) (N := N) hCM p
    have hdimSm : ringKrullDim Sm = d + 1 := by
      -- The polynomial maximal localization has dimension one more than the coefficient
      -- localization, and the chosen source sequence realizes the coefficient dimension.
      calc
        ringKrullDim Sm = ringKrullDim Ap + 1 := by
          simpa [p, Ap, Sm] using ringKrullDim_polynomialAtMaximal_eq_base_add_one (A := A) m
        _ = d + 1 := by rw [hdAp]
    have hregularOnTensor :
        ∃ t : Sm,
          RingTheory.Sequence.IsRegular (Sm ⊗[Ap] Np) (t :: rs.map (algebraMap Ap Sm)) := by
      have hsourceOnTensor :
          RingTheory.Sequence.IsRegular (Sm ⊗[Ap] Np) (rs.map (algebraMap Ap Sm)) := by
        -- First record the source part of the sequence by canonical flat-local base change; the
        -- polynomial closed-fiber parameter is added separately below.
        simpa [p, Ap, Sm, Np] using
          isRegular_tensor_atMaximal_of_sourceRegularSequence (N := N) m hrs
      let fLoc : Ap →+* Sm := Localization.localRingHom p.asIdeal m.asIdeal Polynomial.C rfl
      let _ : IsLocalHom (algebraMap Ap Sm) := by
        -- The mapped source list is available for a future permutation step because the scalar
        -- map is the canonical local map between the two local rings.
        change IsLocalHom fLoc
        exact
          Localization.isLocalHom_localRingHom
            (I := p.asIdeal) (J := m.asIdeal) Polynomial.C rfl
      have hsourceMax :
          Ideal.ofList (rs.map (algebraMap Ap Sm)) ≤ IsLocalRing.maximalIdeal Sm := by
        -- This is the maximal-ideal side condition needed if the missing parameter is appended
        -- after the source sequence and then permuted to the front.
        exact ofList_map_algebraMap_le_maximalIdeal_of_localHom _hrsMax
      have hsourceQuotSupport :
          Module.supportDim Sm
              ((Sm ⊗[Ap] Np) ⧸
                (Ideal.ofList (rs.map (algebraMap Ap Sm)) •
                  (⊤ : Submodule Sm (Sm ⊗[Ap] Np)))) = 1 := by
        -- The quotient by the verified source regular sequence is exactly one-dimensional; the
        -- remaining task is to find a regular parameter on this quotient.
        simpa [p, Ap, Sm, Np] using
          supportDim_quotient_mapped_source_regularSequence_eq_one_atMaximal
            (N := N) hCM m hdAp hrs hlenrs
      have hquotientParameter :
          ∃ t : Sm,
            t ∈ IsLocalRing.maximalIdeal Sm ∧
              IsSMulRegular
                ((Sm ⊗[Ap] Np) ⧸
                  (Ideal.ofList (rs.map (algebraMap Ap Sm)) •
                    (⊤ : Submodule Sm (Sm ⊗[Ap] Np)))) t := by
        have hringParameter :
            ∃ t : Sm,
              t ∈ IsLocalRing.maximalIdeal Sm ∧
                IsSMulRegular Sm t ∧ Module.Flat Ap (QuotSMulTop t Sm) := by
          let _ : Module.Flat Ap Sm := by
            -- Polynomial extension is flat, and the canonical map between the two localizations
            -- is the corresponding localized flat map.
            have hCflat : (Polynomial.C : A →+* Polynomial A).Flat := by
              change (algebraMap A (Polynomial A)).Flat
              rw [RingHom.flat_algebraMap_iff]
              exact Module.Flat.of_free
            have hflat : fLoc.Flat := RingHom.Flat.localRingHom hCflat m.asIdeal p.asIdeal rfl
            rw [RingHom.Flat] at hflat
            exact hflat
          have hfiberParameter :
              ∃ x : Sm ⧸ Ideal.map (algebraMap Ap Sm) (IsLocalRing.maximalIdeal Ap),
                IsRegular x ∧ ¬ IsUnit x := by
            -- The closed fiber is a one-dimensional local domain, so its maximal ideal supplies
            -- the regular nonunit needed by the flat quotient lifting lemma.
            exact closedFiber_polynomialAtMaximal_exists_regular_nonunit (A := A) m
          -- Lemma 10.99.2 lifts the regular closed-fiber class to a flat regular parameter.
          exact exists_regular_flat_principal_quotient_of_closedFiber_regular_nonunit
            (A := Ap) (B := Sm) hfiberParameter
        obtain ⟨t, htMax, htReg, htFlat⟩ := hringParameter
        -- The ring-level flat parameter stays regular after quotienting the tensor model by the
        -- mapped source regular sequence.
        exact ⟨t, htMax,
          isSMulRegular_mappedSourceQuotient_of_regular_flat_quotSMulTop
            (A := Ap) (B := Sm) (M := Np) (rs := rs) htReg htFlat⟩
      obtain ⟨t, htMax, htQuot⟩ := hquotientParameter
      -- The remaining assembly is now formal: append the quotient-regular parameter and permute it
      -- to the front of the sequence required by `cohenMacaulay_tensor_atMaximal_of_full_regularSequence`.
      exact ⟨t,
        isRegular_cons_of_regular_prefix_and_smulRegular_quotient
          hsourceOnTensor hsourceMax htMax htQuot⟩
    obtain ⟨t, htreg⟩ := hregularOnTensor
    have hlenFull : ringKrullDim Sm = (t :: rs.map (algebraMap Ap Sm)).length := by
      -- Once the monic-first regular sequence exists, its length is exactly `dim Ap + 1`.
      simpa [List.length_map, hlenrs] using hdimSm
    exact cohenMacaulay_tensor_atMaximal_of_full_regularSequence hCM m htreg hlenFull
  let _ : Module.CohenMacaulay Sm (Sm ⊗[Ap] Np) := hmodel
  -- Finally transport Cohen-Macaulayness from the tensor model back to the target localization.
  exact cohenMacaulay_of_linearEquiv eModel.symm

/-- Helper for Chap10 Lemma 10 103 13: contracting the extension of a smaller prime to a larger
prime localization recovers the smaller prime. -/
private theorem comap_map_of_le_atPrime
    {B : Type*} [CommRing B]
    {q m : Ideal B} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) :
    Ideal.comap (algebraMap B (Localization.AtPrime m))
      (Ideal.map (algebraMap B (Localization.AtPrime m)) q) = q := by
  -- The prime complement of `m` is disjoint from `q` because `q ≤ m`, so localization preserves
  -- the prime by extension-contraction.
  exact IsLocalization.comap_map_of_isPrime_disjoint m.primeCompl (Localization.AtPrime m)
    (I := q) inferInstance (by
      rw [Set.disjoint_left]
      intro x hxm hxq
      exact hxm (hqm hxq))

/-- Helper for Chap10 Lemma 10 103 13: the two-step local ring `(B_m)_{qB_m}` is canonically
equivalent to the one-step local ring `B_q`. -/
private noncomputable def localizationAtPrime_ringEquiv_of_le
    {B : Type*} [CommRing B]
    {q m : Ideal B} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) :
    let Bm := Localization.AtPrime m
    let qm : Ideal Bm := Ideal.map (algebraMap B Bm) q
    letI : qm.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime
      (S := Bm) (q := m) hqm
    Localization.AtPrime q ≃ₐ[B] Localization.AtPrime qm := by
  let Bm := Localization.AtPrime m
  let qm : Ideal Bm := Ideal.map (algebraMap B Bm) q
  letI : qm.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime
    (S := Bm) (q := m) hqm
  have hcomap : Ideal.comap (algebraMap B Bm) qm = q := by
    simpa [Bm, qm] using comap_map_of_le_atPrime (q := q) (m := m) hqm
  -- Mathlib's localization-localization equivalence has the contracted prime as source; the
  -- previous lemma rewrites that source to `q`.
  let eDomain : Localization.AtPrime q ≃ₐ[B]
      Localization.AtPrime (Ideal.comap (algebraMap B Bm) qm) :=
    Localization.localAlgEquiv q (Ideal.comap (algebraMap B Bm) qm)
      (AlgEquiv.refl (R := B) (A₁ := B)) (by simpa using hcomap.symm)
  let eDouble : Localization.AtPrime (Ideal.comap (algebraMap B Bm) qm) ≃ₐ[B]
      Localization.AtPrime qm :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := m.primeCompl) qm
  exact eDomain.trans eDouble

/-- Helper for Chap10 Lemma 10 103 13: the iterated localized module over `(B_m)_{qB_m}` is the
one-step localized module over `B_q`, viewed by restriction through the ring equivalence. -/
private noncomputable def localizedModule_doubleLocalization_linearEquiv_of_le
    {B : Type*} [CommRing B]
    {P : Type*} [AddCommGroup P] [Module B P]
    {q m : Ideal B} [q.IsPrime] [m.IsPrime] (hqm : q ≤ m) :
    let Bm := Localization.AtPrime m
    let qm : Ideal Bm := Ideal.map (algebraMap B Bm) q
    letI : qm.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime
      (S := Bm) (q := m) hqm
    let Qm := Localization.AtPrime qm
    let Bq := Localization.AtPrime q
    let eRing : Bq ≃ₐ[B] Qm := localizationAtPrime_ringEquiv_of_le hqm
    let _ : Algebra Qm Bq := eRing.symm.toRingHom.toAlgebra
    let _ : Module Qm (LocalizedModule.AtPrime q P) :=
      Module.compHom (LocalizedModule.AtPrime q P) eRing.symm.toRingHom
    LocalizedModule.AtPrime qm (LocalizedModule.AtPrime m P) ≃ₗ[Qm]
      LocalizedModule.AtPrime q P := by
  let Bm := Localization.AtPrime m
  let qm : Ideal Bm := Ideal.map (algebraMap B Bm) q
  letI : qm.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime
    (S := Bm) (q := m) hqm
  let Qm := Localization.AtPrime qm
  let Bq := Localization.AtPrime q
  let eRing : Bq ≃ₐ[B] Qm := localizationAtPrime_ringEquiv_of_le hqm
  let _ : Algebra Qm Bq := eRing.symm.toRingHom.toAlgebra
  let _ : IsScalarTower B Qm Bq := IsScalarTower.of_algHom eRing.symm.toAlgHom
  let _ : Module Qm (LocalizedModule.AtPrime q P) :=
    Module.compHom (LocalizedModule.AtPrime q P) eRing.symm.toRingHom
  let _ : IsScalarTower Qm Bq (LocalizedModule.AtPrime q P) :=
    IsScalarTower.restrictScalars Qm Bq (LocalizedModule.AtPrime q P)
  let _ : Module Qm (Bq ⊗[B] P) :=
    Module.compHom (Bq ⊗[B] P) eRing.symm.toRingHom
  let _ : IsScalarTower Qm Bq (Bq ⊗[B] P) :=
    IsScalarTower.restrictScalars Qm Bq (Bq ⊗[B] P)
  let ePm : LocalizedModule.AtPrime m P ≃ₗ[Bm] Bm ⊗[B] P :=
    LocalizedModule.equivTensorProduct m.primeCompl P
  let eLeft :
      LocalizedModule.AtPrime qm (LocalizedModule.AtPrime m P) ≃ₗ[Qm]
        Qm ⊗[B] P :=
    (LocalizedModule.equivTensorProduct qm.primeCompl (LocalizedModule.AtPrime m P)).trans <|
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Qm Qm) ePm).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange B Bm Qm Qm P)
  let eMidRing : Qm ≃ₗ[Qm] Bq :=
    { __ := eRing.symm.toAddEquiv
      map_smul' := by
        -- The middle tensor comparison only changes the scalar ring through the inverse
        -- algebra equivalence.
        intro a x
        change eRing.symm (a * x) = eRing.symm a * eRing.symm x
        exact eRing.symm.map_mul a x }
  let eMid : Qm ⊗[B] P ≃ₗ[Qm] Bq ⊗[B] P :=
    TensorProduct.AlgebraTensorModule.congr eMidRing (LinearEquiv.refl B P)
  let eRightB :
      LocalizedModule.AtPrime q P ≃ₗ[Bq] Bq ⊗[B] P :=
    LocalizedModule.equivTensorProduct q.primeCompl P
  let eRight :
      LocalizedModule.AtPrime q P ≃ₗ[Qm] Bq ⊗[B] P :=
    { __ := eRightB.toAddEquiv
      map_smul' := by
        -- The one-step comparison is `B_q`-linear, hence also linear over `(B_m)_{qB_m}` after
        -- restricting scalars along the ring equivalence.
        intro a x
        change eRightB ((algebraMap Qm Bq a) • x) =
          (algebraMap Qm Bq a) • eRightB x
        exact eRightB.map_smul (algebraMap Qm Bq a) x }
  -- Both sides are now in the stable tensor normal form over `B`; compose the three comparisons.
  exact eLeft.trans <| eMid.trans eRight.symm

/-- Helper for Chap10 Lemma 10 103 13: Cohen-Macaulayness at all maximal localizations descends
to Cohen-Macaulayness at an arbitrary prime localization when the module has full support. -/
private theorem cohenMacaulay_atPrime_of_forall_maximal
    {B : Type*} [CommRing B] [IsNoetherianRing B]
    {P : Type*} [AddCommGroup P] [Module B P] [Module.Finite B P]
    (hsupp : Module.support B P = Set.univ)
    (hmax : ∀ m : MaximalSpectrum B,
      Module.CohenMacaulay (Localization.AtPrime m.asIdeal)
        (LocalizedModule.AtPrime m.asIdeal P))
    (q : PrimeSpectrum B) :
    Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal P) := by
  -- First pass from the arbitrary prime to a maximal ideal above it; the induced prime in the
  -- maximal localization is the one whose further localization should recover `B_q`.
  obtain ⟨mI, hmI, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.2.1
  let m : MaximalSpectrum B := ⟨mI, hmI⟩
  let q_m : Ideal (Localization.AtPrime m.asIdeal) :=
    Ideal.map (algebraMap B (Localization.AtPrime m.asIdeal)) q.asIdeal
  haveI : q_m.IsPrime := by
    exact Ideal.isPrime_map_of_isLocalizationAtPrime
      (S := Localization.AtPrime m.asIdeal) (q := m.asIdeal) hqm
  let qMax : PrimeSpectrum (Localization.AtPrime m.asIdeal) := ⟨q_m, inferInstance⟩
  have hsupp_m :
      Module.support (Localization.AtPrime m.asIdeal)
          (LocalizedModule.AtPrime m.asIdeal P) =
        Set.univ :=
    support_localizedModuleAtPrime_eq_univ_of_support_eq_univ hsupp m.toPrimeSpectrum
  have hqMax_support :
      qMax ∈ Module.support (Localization.AtPrime m.asIdeal)
        (LocalizedModule.AtPrime m.asIdeal P) := by
    -- Full support after the first localization supplies the support hypothesis needed to
    -- localize the maximal Cohen-Macaulay owner.
    rw [hsupp_m]
    exact Set.mem_univ qMax
  letI :
      Module.CohenMacaulay (Localization.AtPrime m.asIdeal)
        (LocalizedModule.AtPrime m.asIdeal P) := hmax m
  have hloc_m :
      Module.LocallyCohenMacaulay (Localization.AtPrime m.asIdeal)
        (LocalizedModule.AtPrime m.asIdeal P) :=
    Module.locallyCohenMacaulay_of_cohenMacaulay
      (R := Localization.AtPrime m.asIdeal)
      (M := LocalizedModule.AtPrime m.asIdeal P) hsupp_m
  have hdouble :
      Module.CohenMacaulay (Localization.AtPrime q_m)
        (LocalizedModule.AtPrime q_m (LocalizedModule.AtPrime m.asIdeal P)) := by
    -- Localizing the Cohen-Macaulay module over `B_m` gives Cohen-Macaulayness over the
    -- two-step localization.
    exact hloc_m.localizedModule_cohenMacaulay qMax
  let Qm := Localization.AtPrime q_m
  let Bq := Localization.AtPrime q.asIdeal
  let eRing : Bq ≃ₐ[B] Qm := localizationAtPrime_ringEquiv_of_le hqm
  let _ : Algebra Qm Bq := eRing.symm.toRingHom.toAlgebra
  let _ : IsScalarTower B Qm Bq := IsScalarTower.of_algHom eRing.symm.toAlgHom
  let _ : Module Qm (LocalizedModule.AtPrime q.asIdeal P) :=
    Module.compHom (LocalizedModule.AtPrime q.asIdeal P) eRing.symm.toRingHom
  let _ : IsScalarTower Qm Bq (LocalizedModule.AtPrime q.asIdeal P) :=
    IsScalarTower.restrictScalars Qm Bq (LocalizedModule.AtPrime q.asIdeal P)
  have hrestrict :
      Module.CohenMacaulay Qm (LocalizedModule.AtPrime q.asIdeal P) := by
    let _ : Module.CohenMacaulay Qm
        (LocalizedModule.AtPrime q_m (LocalizedModule.AtPrime m.asIdeal P)) := hdouble
    -- First carry Cohen-Macaulayness across the module equivalence while staying over the
    -- two-step local ring.
    exact cohenMacaulay_of_linearEquiv
      (localizedModule_doubleLocalization_linearEquiv_of_le (P := P) hqm)
  have hsurj : Function.Surjective (algebraMap Qm Bq) := by
    -- The inverse of the canonical ring equivalence is the scalar map used for restriction.
    simpa using eRing.symm.surjective
  -- Finally upgrade the restricted `Qm`-module owner to the genuine `B_q`-module owner.
  exact
    (Module.cohenMacaulay_iff_restrictScalars_of_surjective
      (R := Qm) (S := Bq) (N := LocalizedModule.AtPrime q.asIdeal P) hsurj).2 hrestrict

-- Proof sketch: the source argument first proves the one-variable statement over `A[X]` for an
-- arbitrary locally Cohen-Macaulay `A`-module, and only afterward iterates it through the
-- last-variable identification for `MvPolynomial`.
/-- Helper for Lemma 10.103.13: the source-faithful one-variable step for polynomial scalar
extension. -/
private theorem polynomial
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N]
    (hCM : Module.LocallyCohenMacaulay A N) :
    Module.LocallyCohenMacaulay (Polynomial A) ((Polynomial A) ⊗[A] N) := by
  let _ : Module.Finite A N := hCM.toFinite
  have hsupp :
      Module.support (Polynomial A) ((Polynomial A) ⊗[A] N) = Set.univ :=
    support_eq_univ_polynomial_tensor_of_locallyCohenMacaulay hCM
  refine ⟨fun q ↦ ?_⟩
  -- The arbitrary-prime case is now reduced to the maximal-local theorem plus the generic
  -- maximal-to-prime localization bridge.
  exact cohenMacaulay_atPrime_of_forall_maximal hsupp
    (fun m ↦ polynomial_atMaximal hCM m) q

-- Proof sketch: argue by induction on the number of variables, reducing from
-- `MvPolynomial (Fin (n + 1)) R` to a one-variable polynomial extension over
-- `MvPolynomial (Fin n) R`. For the one-variable step, localize at a prime of `A[X]`, pull back a
-- maximal regular sequence from `A_p`, identify the quotient support in the closed fiber, and use
-- `polynomial_tensor_isSMulRegular_of_isUnit_leadingCoeff` for the final nonzerodivisor step.
/-- Helper for Chap10 Lemma 10 103 13: if `M` is locally Cohen-Macaulay over a Noetherian
ring `R`, then its scalar extension to `R[x₁, …, xₙ]`, represented canonically by
`MvPolynomial (Fin n) R ⊗[R] M`, is locally Cohen-Macaulay. -/
@[stacks 0AAI]
theorem mvPolynomial (hCM : Module.LocallyCohenMacaulay R M) (n : ℕ) :
    Module.LocallyCohenMacaulay (MvPolynomial (Fin n) R) ((MvPolynomial (Fin n) R) ⊗[R] M) := by
  -- Route correction: the source proof is local and one-variable at each step, so the remaining
  -- blocker is now isolated into the named one-variable theorem and the algebra-equivalence
  -- transport between successive polynomial presentations.
  induction n with
  | zero =>
      let e₀ : R ≃ₐ[R] MvPolynomial (Fin 0) R := (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm
      -- First rewrite `M` as `R ⊗[R] M`, then transport that local Cohen-Macaulay owner across
      -- the zero-variable algebra equivalence.
      let hTensor : Module.LocallyCohenMacaulay R (R ⊗[R] M) := by
        let _ : Module.LocallyCohenMacaulay R M := hCM
        exact locallyCohenMacaulay_of_linearEquiv
          (((TensorProduct.comm R R M).trans (TensorProduct.rid R M)).symm)
      exact locallyCohenMacaulay_tensor_of_algEquiv (R := R) (M := M) e₀ hTensor
  | succ n ih =>
      let A := MvPolynomial (Fin n) R
      let eLast : Polynomial A ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
        (noetherNormalizationLastVariableEquiv (R := R) (n := n)).symm
      let eAssoc :
          ((Polynomial A) ⊗[R] M) ≃ₗ[Polynomial A]
            ((Polynomial A) ⊗[A] (A ⊗[R] M)) :=
        polynomial_tensor_baseChange_linearEquiv (R := R) (M := M) (A := A)
      -- Apply the one-variable theorem over the `n`-variable coefficient ring and then undo the
      -- canonical reassociation of the tensor module.
      let hPolyAssoc :
          Module.LocallyCohenMacaulay (Polynomial A)
            ((Polynomial A) ⊗[A] (A ⊗[R] M)) :=
        polynomial (A := A) (N := A ⊗[R] M) ih
      let hPoly :
          Module.LocallyCohenMacaulay (Polynomial A) ((Polynomial A) ⊗[R] M) := by
        let _ :
            Module.LocallyCohenMacaulay (Polynomial A)
              ((Polynomial A) ⊗[A] (A ⊗[R] M)) := hPolyAssoc
        exact locallyCohenMacaulay_of_linearEquiv (R := Polynomial A) eAssoc.symm
      -- Transport the polynomial-ring statement back to the canonical `MvPolynomial` presentation
      -- of the next stage.
      exact locallyCohenMacaulay_tensor_of_algEquiv (R := R) (M := M) eLast hPoly

end Module.LocallyCohenMacaulay

end
