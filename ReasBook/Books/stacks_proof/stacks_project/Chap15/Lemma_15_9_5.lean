import Mathlib
import StacksProject_2024.Chap10.Lemma_10_21_5
import StacksProject_2024.Chap10.Example_10_143_12
import StacksProject_2024.Chap10.Lemma_10_143_8
import StacksProject_2024.Chap10.Lemma_10_143_9
import StacksProject_2024.Chap15.Lemma_15_9_1
import StacksProject_2024.Chap15.Lemma_15_9_4

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open scoped TensorProduct

universe u

namespace Algebra

section

variable {A : Type u} [CommRing A]

/-- Helper for Lemma 15.9.5: the extended ideal `I B` is contained in the kernel of any
surjective factorization map `B → A ⧸ I` over `A`. -/
lemma ideal_map_le_universal_factorization_ker
    {B : Type u} [CommRing B] [Algebra A B]
    (I : Ideal A) (φ : B →ₐ[A] A ⧸ I) :
    Ideal.map (algebraMap A B) I ≤ RingHom.ker φ.toRingHom := by
  -- Every element of `I` vanishes after applying the quotient map to `A ⧸ I`.
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change φ (algebraMap A B a) = 0
  rw [φ.commutes]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

/-- Helper for Lemma 15.9.5: the quotient map induced by a surjective `A`-algebra morphism
`B → A ⧸ I` is still a surjection after modding out by `I B`. -/
lemma descended_quotient_map_over_quotient_base
    {B : Type u} [CommRing B] [Algebra A B]
    (I : Ideal A) (φ : B →ₐ[A] A ⧸ I) (hφsurj : Function.Surjective φ) :
    ∃ φbarA : (B ⧸ Ideal.map (algebraMap A B) I) →ₐ[A] A ⧸ I,
      Function.Surjective φbarA := by
  let J : Ideal B := Ideal.map (algebraMap A B) I
  let φbarA : (B ⧸ J) →ₐ[A] A ⧸ I :=
    Ideal.Quotient.liftₐ J φ fun _ hb ↦
      RingHom.mem_ker.mp (ideal_map_le_universal_factorization_ker (A := A) I φ hb)
  have hφbar_surj : Function.Surjective φbarA := by
    intro x
    obtain ⟨b, rfl⟩ := hφsurj x
    refine ⟨Ideal.Quotient.mk J b, ?_⟩
    simp [φbarA]
  exact ⟨φbarA, hφbar_surj⟩

/-- Helper for Lemma 15.9.5: the canonical quotient descent of a factorization map
`φ : B → A ⧸ I`. -/
noncomputable abbrev canonical_descended_quotient_map
    {B : Type u} [CommRing B] [Algebra A B]
    (I : Ideal A) (φ : B →ₐ[A] A ⧸ I) :
    (B ⧸ Ideal.map (algebraMap A B) I) →ₐ[A] A ⧸ I :=
  Ideal.Quotient.liftₐ (Ideal.map (algebraMap A B) I) φ fun _ hb ↦
    RingHom.mem_ker.mp (ideal_map_le_universal_factorization_ker (A := A) I φ hb)

/-- Helper for Lemma 15.9.5: the canonical descended quotient map agrees with `φ` on quotient
classes represented by elements of `B`. -/
lemma canonical_descended_quotient_map_mk
    {B : Type u} [CommRing B] [Algebra A B]
    (I : Ideal A) (φ : B →ₐ[A] A ⧸ I) (b : B) :
    canonical_descended_quotient_map (A := A) (B := B) I φ
      (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) b) = φ b := by
  -- Evaluate the quotient lift on a chosen representative.
  simp [canonical_descended_quotient_map]

/-- Helper for Lemma 15.9.5: if a class `e : B / I B` is invertible after descending `φ`, then
any chosen lift `e0 : B` already maps to a unit in `A / I`. -/
lemma lifted_idempotent_maps_to_localized_unit
    {B : Type u} [CommRing B] [Algebra A B]
    (I : Ideal A) (φ : B →ₐ[A] A ⧸ I)
    (e : B ⧸ Ideal.map (algebraMap A B) I) (e0 : B)
    (he0 : Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) e0 = e)
    (heunit : IsUnit (canonical_descended_quotient_map (A := A) (B := B) I φ e)) :
    IsUnit (φ e0) := by
  -- Replace the quotient class `e` by the chosen representative `e0`.
  rw [← he0] at heunit
  simpa using heunit

/-- Helper for Lemma 15.9.5: the original factorization map `φ : B → A / I` extends to the
away-localization at a lift `e0` of a quotient element whose descended image is invertible. -/
noncomputable def localization_lift_of_factorization
    {B : Type u} [CommRing B] [Algebra A B]
    (I : Ideal A) (φ : B →ₐ[A] A ⧸ I)
    {e : B ⧸ Ideal.map (algebraMap A B) I} {e0 : B}
    (he0 : Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) e0 = e)
    (heunit : IsUnit (canonical_descended_quotient_map (A := A) (B := B) I φ e)) :
    Localization.Away e0 →ₐ[A] A ⧸ I := by
  letI : Algebra B (A ⧸ I) := φ.toRingHom.toAlgebra
  letI : IsScalarTower A B (A ⧸ I) :=
    IsScalarTower.of_algebraMap_eq' <|
      RingHom.ext fun a ↦ by
        change algebraMap A (A ⧸ I) a = φ (algebraMap A B a)
        simpa using (φ.commutes a).symm
  let huLift : IsUnit (φ e0) :=
    lifted_idempotent_maps_to_localized_unit (A := A) (B := B) I φ e e0 he0 heunit
  let ψB : Localization.Away e0 →ₐ[B] A ⧸ I :=
    { toRingHom := IsLocalization.Away.lift e0 huLift
      commutes' := by
        intro b
        -- The localization lift agrees with the original `B`-algebra map on `B`.
        change IsLocalization.Away.lift e0 huLift (algebraMap B (Localization.Away e0) b) = φ b
        simpa using IsLocalization.Away.lift_eq e0 huLift b }
  -- Restrict scalars back along `A → B`.
  exact ψB.restrictScalars A

/-- Helper for Lemma 15.9.5: the away-localization lift of `φ` agrees with `φ` on the base ring
`B`. -/
lemma localization_lift_of_factorization_algebraMap
    {B : Type u} [CommRing B] [Algebra A B]
    (I : Ideal A) (φ : B →ₐ[A] A ⧸ I)
    {e : B ⧸ Ideal.map (algebraMap A B) I} {e0 : B}
    (he0 : Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) e0 = e)
    (heunit : IsUnit (canonical_descended_quotient_map (A := A) (B := B) I φ e))
    (b : B) :
    localization_lift_of_factorization (A := A) (B := B) I φ he0 heunit
      (algebraMap B (Localization.Away e0) b) = φ b := by
  letI : Algebra B (A ⧸ I) := φ.toRingHom.toAlgebra
  letI : IsScalarTower A B (A ⧸ I) :=
    IsScalarTower.of_algebraMap_eq' <|
      RingHom.ext fun a ↦ by
        change algebraMap A (A ⧸ I) a = φ (algebraMap A B a)
        simpa using (φ.commutes a).symm
  -- Unfold the restricted localization lift and evaluate it on a base element.
  dsimp [localization_lift_of_factorization]
  change IsLocalization.Away.lift e0
      (lifted_idempotent_maps_to_localized_unit (A := A) (B := B) I φ e e0 he0 heunit)
      (algebraMap B (Localization.Away e0) b) = φ b
  simpa using IsLocalization.Away.lift_eq e0
    (lifted_idempotent_maps_to_localized_unit (A := A) (B := B) I φ e e0 he0 heunit) b

/-- Helper for Lemma 15.9.5: the quotient `B / I B` of an étale `A`-algebra remains étale over
`A / I` via the canonical quotient-tensor comparison. -/
lemma quotient_source_etale_over_quotient
    {B : Type u} [CommRing B] [Algebra A B] [Etale A B]
    (I : Ideal A) :
    Algebra.Etale (A ⧸ I) (B ⧸ Ideal.map (algebraMap A B) I) := by
  -- Transport the base-changed étale structure across the owner equivalence.
  let e : (B ⧸ Ideal.map (algebraMap A B) I) ≃ₐ[A ⧸ I] TensorProduct A (A ⧸ I) B :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  letI : Algebra.Etale (A ⧸ I) (TensorProduct A (A ⧸ I) B) :=
    Algebra.Etale.baseChange A B (A ⧸ I)
  exact Algebra.Etale.of_equiv e.symm

/-- Helper for Lemma 15.9.5: extending the quotient ideal `I B` further along a tower
`A → B → A'` agrees with extending `I` directly to `A'`. -/
lemma localized_extended_ideal_eq
    {B A' : Type u} [CommRing B] [CommRing A'] [Algebra A B] [Algebra B A'] [Algebra A A']
    [IsScalarTower A B A'] (I : Ideal A) :
    Ideal.map (algebraMap B A') (Ideal.map (algebraMap A B) I) =
      Ideal.map (algebraMap A A') I := by
  -- Collapse the iterated ideal extension along the algebra tower `A → B → A'`.
  rw [Ideal.map_map]
  simp [IsScalarTower.algebraMap_eq A B A']

/-- Helper for Lemma 15.9.5: an away-localization at an idempotent is canonically the quotient by
the complementary principal ideal. -/
noncomputable def idempotent_away_quotient_algEquiv
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {e : R}
    (he : IsIdempotentElem e)
    (hS : IsLocalization.Away e S) :
    (R ⧸ Ideal.span ({1 - e} : Set R)) ≃ₐ[R] S := by
  letI := hS
  letI : IsLocalization.Away e (R ⧸ Ideal.span ({1 - e} : Set R)) := by
    -- Repackage the quotient by `⟨1 - e⟩` as the standard away-localization at `e`.
    simpa using
      (quotient_isLocalization_Away_one_sub_of_idempotent_generator
        (R := R) (I := Ideal.span ({1 - e} : Set R)) (e := 1 - e) he.one_sub
        (by simp : Ideal.span ({1 - e} : Set R) = R ∙ (1 - e)))
  -- Both codomains realize the same localization of `R` away from `e`.
  exact IsLocalization.algEquiv (Submonoid.powers e)
    (R ⧸ Ideal.span ({1 - e} : Set R)) S

/-- Helper for Lemma 15.9.5: the kernel of an away-localization at an idempotent is the
complementary principal ideal. -/
lemma descended_localization_kernel_eq_span_one_sub
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {e : R}
    (he : IsIdempotentElem e)
    (hS : IsLocalization.Away e S) :
    RingHom.ker (algebraMap R S) = Ideal.span ({1 - e} : Set R) := by
  let φ : (R ⧸ Ideal.span ({1 - e} : Set R)) ≃ₐ[R] S :=
    idempotent_away_quotient_algEquiv (R := R) (S := S) he hS
  -- Compare kernel membership by transporting along the quotient-away equivalence.
  ext x
  constructor
  · intro hx
    have hcomm :
        φ (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x) = algebraMap R S x := by
      simpa using φ.commutes x
    have hx' : φ (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x) = 0 := by
      exact hcomm.trans (RingHom.mem_ker.mp hx)
    have hmk :
        Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x = 0 := by
      apply φ.injective
      simpa using hx'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hmk
  · intro hx
    have hmk :
        Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have hcomm :
        φ (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x) = algebraMap R S x := by
      simpa using φ.commutes x
    -- Rewrite the canonical quotient map back to `S` through the quotient equivalence.
    have hx' : φ (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x) = φ 0 :=
      congrArg φ hmk
    have hx0 : algebraMap R S x = 0 := by
      calc
        algebraMap R S x = φ (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) x) := hcomm.symm
        _ = φ 0 := hx'
        _ = 0 := by simp
    exact RingHom.mem_ker.mpr hx0

/-- Helper for Lemma 15.9.5: an idempotent element that is also a unit must be `1`. -/
lemma eq_one_of_isUnit_of_isIdempotentElem
    {R : Type*} [CommRing R] {x : R}
    (hxid : IsIdempotentElem x) (hxunit : IsUnit x) :
    x = 1 := by
  rcases hxunit with ⟨u, rfl⟩
  -- Multiply the idempotent relation by `u⁻¹` to cancel the extra factor.
  have huidem : ((u : R) * (u : R)) = (u : R) := by
    simpa [pow_two] using hxid.eq
  have huinv : (u : R) * ↑u⁻¹ = 1 := by
    simpa using u.mul_inv
  calc
    (u : R) = (u : R) * 1 := by simp
    _ = (u : R) * ((u : R) * ↑u⁻¹) := by rw [huinv.symm]
    _ = ((u : R) * (u : R)) * ↑u⁻¹ := by rw [mul_assoc]
    _ = (u : R) * ↑u⁻¹ := by rw [huidem]
    _ = 1 := huinv

/-- Helper for Lemma 15.9.5: in the degenerate case `A / I = 0`, a trivial localization already
provides the required lifted factorization. -/
lemma subsingleton_quotient_factorization_witness
    (I : Ideal A) (f : A[X]) (gbar hbar : (A ⧸ I)[X]) (hf : f.Monic)
    [Subsingleton (A ⧸ I)] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (quotientAlgEquiv : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (g' h' : A'[X]),
        g'.Monic ∧
          h'.Monic ∧
          f.map (algebraMap A A') = g' * h' ∧
          gbar.map quotientAlgEquiv.toRingHom =
            g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) ∧
          hbar.map quotientAlgEquiv.toRingHom =
            h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) := by
  have hzeroUnit : IsUnit (0 : A ⧸ I) := by
    -- In the zero ring every element, in particular `0`, agrees with `1`.
    rw [show (0 : A ⧸ I) = 1 by exact Subsingleton.elim _ _]
    exact isUnit_one
  obtain ⟨u, quotientAlgEquiv, -⟩ :=
    exists_quotientAlgEquiv_localizationAway_of_isUnit_quotient
      (A := A) (I := I) (u_bar := 0) hzeroUnit
  let A' : Type u := Localization.Away u
  let g' : A'[X] := f.map (algebraMap A A')
  let h' : A'[X] := 1
  have hg' : g'.Monic := by
    -- Monicity is preserved by polynomial base change.
    simpa [g'] using hf.map (algebraMap A A')
  have hh' : h'.Monic := by
    simp [h']
  have hmul : f.map (algebraMap A A') = g' * h' := by
    -- The trivial factorization uses the unit polynomial.
    simp [g', h']
  have hsub :
      Subsingleton (A' ⧸ Ideal.map (algebraMap A A') I) := by
    refine ⟨?_⟩
    intro x y
    rcases quotientAlgEquiv.surjective x with ⟨x0, rfl⟩
    rcases quotientAlgEquiv.surjective y with ⟨y0, rfl⟩
    simpa using (Subsingleton.elim x0 y0)
  letI : Subsingleton (A' ⧸ Ideal.map (algebraMap A A') I) := hsub
  have hgred :
      gbar.map quotientAlgEquiv.toRingHom =
        g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) := by
    -- The target polynomial ring is subsingleton, so every two reductions agree.
    exact Subsingleton.elim _ _
  have hhred :
      hbar.map quotientAlgEquiv.toRingHom =
        h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) := by
    -- The same subsingleton argument closes the second reduction identity.
    exact Subsingleton.elim _ _
  exact ⟨A', inferInstance, inferInstance, inferInstance, quotientAlgEquiv, g', h',
    hg', hh', hmul, hgred, hhred⟩

/-- Helper for Lemma 15.9.5: the given factorization modulo `I` defines the canonical surjective
map from the universal coprime factorization ring of `f`, together with the universal lifted
factors whose reductions are `gbar` and `hbar`. -/
lemma universal_factorization_algebra_map
    (I : Ideal A) (f : A[X]) (gbar hbar : (A ⧸ I)[X]) (hf : f.Monic) (hgbar : gbar.Monic)
    (hhbar : hbar.Monic) (hfactor : f.map (Ideal.Quotient.mk I) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) [Nontrivial (A ⧸ I)] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Etale A B)
      (φ : B →ₐ[A] A ⧸ I) (_ : Function.Surjective φ) (gU hU : B[X]),
        gU.Monic ∧
          hU.Monic ∧
          f.map (algebraMap A B) = gU * hU ∧
          gbar = gU.map φ.toRingHom ∧
          hbar = hU.map φ.toRingHom := by
  -- The universal coprime factorization ring already packages the textbook étale localization.
  have hn : f.natDegree = gbar.natDegree + hbar.natDegree := by
    -- Taking nat-degrees of the residue factorization identifies the universal degree parameters.
    calc
      f.natDegree = (f.map (Ideal.Quotient.mk I)).natDegree := by
        symm
        simpa using hf.natDegree_map (Ideal.Quotient.mk I)
      _ = gbar.natDegree + hbar.natDegree := by
        simpa [hfactor, hgbar.natDegree_mul hhbar] using congr(($hfactor).natDegree)
  let pf : MonicDegreeEq A f.natDegree := .mk f hf rfl
  let pg : MonicDegreeEq (A ⧸ I) gbar.natDegree := .mk gbar hgbar rfl
  let ph : MonicDegreeEq (A ⧸ I) hbar.natDegree := .mk hbar hhbar rfl
  let B : Type u := Polynomial.UniversalCoprimeFactorizationRing
    gbar.natDegree hbar.natDegree hn pf
  let φ : B →ₐ[A] A ⧸ I :=
    (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
      (A ⧸ I) gbar.natDegree hbar.natDegree hn pf).symm
      ⟨(pg, ph), hfactor.symm, hcoprime⟩
  let gU : B[X] :=
    (Polynomial.UniversalCoprimeFactorizationRing.factor₁
      gbar.natDegree hbar.natDegree hn pf).1
  let hU : B[X] :=
    (Polynomial.UniversalCoprimeFactorizationRing.factor₂
      gbar.natDegree hbar.natDegree hn pf).1
  have hφsurj : Function.Surjective φ := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨algebraMap A B a, ?_⟩
    -- Surjectivity is inherited from the quotient map `A → A ⧸ I`.
    simp [φ]
  have hgU : gU.Monic := by
    simpa [gU] using
      (Polynomial.UniversalCoprimeFactorizationRing.factor₁
        gbar.natDegree hbar.natDegree hn pf).monic
  have hhU : hU.Monic := by
    simpa [hU] using
      (Polynomial.UniversalCoprimeFactorizationRing.factor₂
        gbar.natDegree hbar.natDegree hn pf).monic
  have hmul : f.map (algebraMap A B) = gU * hU := by
    -- The universal factors multiply to the base-changed polynomial `f`.
    simpa [gU, hU] using
      (Polynomial.UniversalCoprimeFactorizationRing.factor₁_mul_factor₂
        gbar.natDegree hbar.natDegree hn pf).symm
  have hφpair :
      (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
        (A ⧸ I) gbar.natDegree hbar.natDegree hn pf φ) =
        ⟨(pg, ph), hfactor.symm, hcoprime⟩ := by
    exact (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
      (A ⧸ I) gbar.natDegree hbar.natDegree hn pf).apply_symm_apply
        ⟨(pg, ph), hfactor.symm, hcoprime⟩
  have hgred_monic :
      (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
        (A ⧸ I) gbar.natDegree hbar.natDegree hn pf φ).1.1 = pg := by
    exact congr(($hφpair).1.1)
  have hhred_monic :
      (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
        (A ⧸ I) gbar.natDegree hbar.natDegree hn pf φ).1.2 = ph := by
    exact congr(($hφpair).1.2)
  have hfst :
      (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
        (A ⧸ I) gbar.natDegree hbar.natDegree hn pf φ).1.1 =
        (Polynomial.UniversalCoprimeFactorizationRing.factor₁
          gbar.natDegree hbar.natDegree hn pf).map φ.toRingHom := by
    -- The first represented factor is the image of the universal first factor.
    simpa [gU] using
      (Polynomial.UniversalCoprimeFactorizationRing.homEquiv_comp_fst
        (m := gbar.natDegree) (k := hbar.natDegree) (hn := hn) (p := pf)
        (f := AlgHom.id A B) (g := φ))
  have hsnd :
      (Polynomial.UniversalCoprimeFactorizationRing.homEquiv
        (A ⧸ I) gbar.natDegree hbar.natDegree hn pf φ).1.2 =
        (Polynomial.UniversalCoprimeFactorizationRing.factor₂
          gbar.natDegree hbar.natDegree hn pf).map φ.toRingHom := by
    -- The second represented factor is the image of the universal second factor.
    simpa [hU] using
      (Polynomial.UniversalCoprimeFactorizationRing.homEquiv_comp_snd
        (m := gbar.natDegree) (k := hbar.natDegree) (hn := hn) (p := pf)
        (f := AlgHom.id A B) (g := φ))
  have hgred : gbar = gU.map φ.toRingHom := by
    -- Reading back the first component of the representing pair recovers `gbar`.
    calc
      gbar = pg.1 := by rfl
      _ = ((Polynomial.UniversalCoprimeFactorizationRing.homEquiv
          (A ⧸ I) gbar.natDegree hbar.natDegree hn pf φ).1.1).1 := by
            simpa using congrArg Subtype.val hgred_monic.symm
      _ = gU.map φ.toRingHom := by
            simpa using congrArg Subtype.val hfst
  have hhred : hbar = hU.map φ.toRingHom := by
    -- Reading back the second component of the representing pair recovers `hbar`.
    calc
      hbar = ph.1 := by rfl
      _ = ((Polynomial.UniversalCoprimeFactorizationRing.homEquiv
          (A ⧸ I) gbar.natDegree hbar.natDegree hn pf φ).1.2).1 := by
            simpa using congrArg Subtype.val hhred_monic.symm
      _ = hU.map φ.toRingHom := by
            simpa using congrArg Subtype.val hsnd
  exact ⟨B, inferInstance, inferInstance, inferInstance, φ, hφsurj, gU, hU,
    hgU, hhU, hmul, hgred, hhred⟩

-- Proof sketch: use the universal coprime factorization algebra for the monic polynomial `f`. The
-- given factorization over `A ⧸ I` yields an `A`-algebra map from this universal algebra to
-- `A ⧸ I`. By Example `10.143.12` the universal algebra is étale at every point over the kernel of
-- that map; Lemma `15.9.4` gives a localization `B_g` that is étale over `A` and still maps onto
-- `A ⧸ I`. Applying Lemmas `10.143.8` and `10.143.9` to the induced quotient map produces an
-- idempotent localization whose reduction modulo `I` is isomorphic to `A ⧸ I`, and the universal
-- factorization descends to the required lifted monic factorization.
/-- Lemma 15.9.5: if a monic polynomial `f ∈ A[X]` has a factorization modulo `I` as a product of
monic coprime factors `ḡ * h̄`, then after an étale base change `A → A'` inducing an isomorphism
`A ⧸ I ≃ A' ⧸ IA'`, the polynomial `f` factors as a product of monic lifts `g' * h'` whose
reductions modulo `IA'` recover the given factorization. -/
@[stacks 0ALH]
theorem exists_etale_lift_factorization_of_monic_mod_ideal
    (I : Ideal A) (f : A[X]) (gbar hbar : (A ⧸ I)[X]) (hf : f.Monic) (hgbar : gbar.Monic)
    (hhbar : hbar.Monic) (hfactor : f.map (Ideal.Quotient.mk I) = gbar * hbar)
    (hcoprime : IsCoprime gbar hbar) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : Etale A A')
      (quotientAlgEquiv : (A ⧸ I) ≃ₐ[A ⧸ I] (A' ⧸ Ideal.map (algebraMap A A') I))
      (g' h' : A'[X]),
        g'.Monic ∧
          h'.Monic ∧
          f.map (algebraMap A A') = g' * h' ∧
          gbar.map quotientAlgEquiv.toRingHom =
            g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) ∧
          hbar.map quotientAlgEquiv.toRingHom =
            h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) :=
  by
    classical
    by_cases htriv : Subsingleton (A ⧸ I)
    · -- In the zero-quotient case, the trivial factorization already works after a localization.
      let _ : Subsingleton (A ⧸ I) := htriv
      exact subsingleton_quotient_factorization_witness (A := A) I f gbar hbar hf
    · let _ : Nontrivial (A ⧸ I) := not_subsingleton_iff_nontrivial.mp htriv
      obtain ⟨B, _, _, _, φ, hφsurj, gU, hU, hgU, hhU, hmul, hgred, hhred⟩ :=
        universal_factorization_algebra_map I f gbar hbar hf hgbar hhbar hfactor hcoprime
      let J : Ideal B := Ideal.map (algebraMap A B) I
      let φbarA : (B ⧸ J) →ₐ[A] A ⧸ I := canonical_descended_quotient_map (A := A) I φ
      have hφbar_surj : Function.Surjective φbarA := by
        intro x
        obtain ⟨b, rfl⟩ := hφsurj x
        refine ⟨Ideal.Quotient.mk J b, ?_⟩
        -- The canonical descended map still hits every quotient class.
        simpa [J, φbarA] using
          (canonical_descended_quotient_map_mk (A := A) (B := B) I φ b)
      let σ : (B ⧸ J) →ₐ[A ⧸ I] A ⧸ I :=
        AlgHom.extendScalarsOfSurjective (Ideal.Quotient.mkₐ_surjective A I) φbarA
      letI : Algebra (B ⧸ J) (A ⧸ I) := σ.toRingHom.toAlgebra
      letI : IsScalarTower (A ⧸ I) (B ⧸ J) (A ⧸ I) :=
        IsScalarTower.of_algebraMap_eq fun x ↦ by
          change x = σ (algebraMap (A ⧸ I) (B ⧸ J) x)
          simpa using (σ.commutes x).symm
      have hEtaleQ : Algebra.Etale (A ⧸ I) (B ⧸ J) :=
        quotient_source_etale_over_quotient (A := A) (B := B) I
      have hEtaleσ : Algebra.Etale (B ⧸ J) (A ⧸ I) :=
        by
          letI : Algebra.Etale (A ⧸ I) (A ⧸ I) := by infer_instance
          -- The common-base owner theorem upgrades the descended quotient map to an étale map.
          simpa using
            (Algebra.etale_of_etale_over_common_base : Algebra.Etale (B ⧸ J) (A ⧸ I))
      have hσsurj : Function.Surjective (algebraMap (B ⧸ J) (A ⧸ I)) := by
        intro x
        obtain ⟨y, hy⟩ := hφbar_surj x
        exact ⟨y, by simpa [σ] using hy⟩
      obtain ⟨e, he, hloc⟩ :=
        exists_idempotent_localizationAway_of_surjective_of_flat_of_finitePresentation
          (R := B ⧸ J) (S := A ⧸ I) hσsurj
      obtain ⟨e0, he0⟩ := Ideal.Quotient.mk_surjective e
      let A' : Type u := Localization.Away e0
      letI : Algebra B A' := inferInstance
      letI : Algebra A A' := inferInstance
      letI : IsScalarTower A B A' := inferInstance
      have hJmap : Ideal.map (algebraMap B A') J = Ideal.map (algebraMap A A') I := by
        -- This fixes the quotient ideal on the localization side to the theorem's exact codomain.
        simpa [J] using localized_extended_ideal_eq (A := A) (B := B) (A' := A') I
      have hEtaleA' : Etale A A' := by
        -- The localized universal factorization algebra remains étale over `A`.
        letI : Etale B A' := Algebra.Etale.of_isLocalizationAway e0
        infer_instance
      let K : Ideal A' := Ideal.map (algebraMap A A') I
      have hkerσ :
          RingHom.ker σ.toRingHom = Ideal.span ({1 - e} : Set (B ⧸ J)) := by
        -- The descended quotient map is the away-localization of `B ⧸ J` at the idempotent `e`.
        exact
          descended_localization_kernel_eq_span_one_sub
            (R := B ⧸ J) (S := A ⧸ I) (e := e) he hloc
      let τ : (B ⧸ J) →ₐ[A] (A' ⧸ K) :=
        Ideal.quotientMapₐ K (IsScalarTower.toAlgHom A B A') <| by
          -- Rewrite the source extended ideal to the theorem's exact target ideal.
          rw [show K = Ideal.map (algebraMap B A') J by simpa [K] using hJmap.symm]
          exact Ideal.le_comap_map
      have hτe : τ e = 1 := by
        -- The lift `e0` stays idempotent modulo `K`, and it is already a unit in `A'`.
        have he0_idem_mem : e0 ^ 2 - e0 ∈ J := by
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          calc
            Ideal.Quotient.mk J (e0 ^ 2 - e0)
                = (Ideal.Quotient.mk J e0) ^ 2 - Ideal.Quotient.mk J e0 := by
                    simp [pow_two]
            _ = e ^ 2 - e := by simpa [he0]
            _ = 0 := by simpa [pow_two, he.eq]
        have hclass_idem :
            IsIdempotentElem (Ideal.Quotient.mk K (algebraMap B A' e0)) := by
          -- Push the lifted idempotent relation to the exact target quotient.
          refine sub_eq_zero.mp ?_
          have hzero :
              Ideal.Quotient.mk K (algebraMap B A' (e0 ^ 2 - e0)) = 0 := by
            apply Ideal.Quotient.eq_zero_iff_mem.mpr
            rw [show K = Ideal.map (algebraMap B A') J by simpa [K] using hJmap.symm]
            exact Ideal.mem_map_of_mem (algebraMap B A') he0_idem_mem
          simpa [K, pow_two, map_sub] using hzero
        have hclass_unit :
            IsUnit (Ideal.Quotient.mk K (algebraMap B A' e0)) := by
          exact (IsLocalization.Away.algebraMap_isUnit e0).map (Ideal.Quotient.mk K)
        have hclass_one :
            Ideal.Quotient.mk K (algebraMap B A' e0) = 1 := by
          exact eq_one_of_isUnit_of_isIdempotentElem hclass_idem hclass_unit
        -- Evaluate `τ` on the chosen lift of `e` and replace the target class by `1`.
        calc
          τ e = Ideal.Quotient.mk K (algebraMap B A' e0) := by
            rw [← he0]
            simp [τ, K]
          _ = 1 := hclass_one
      have hτsurj : Function.Surjective τ := by
        intro y
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj e0 z
        have hclass_one : Ideal.Quotient.mk K (algebraMap B A' e0) = 1 := by
          calc
            Ideal.Quotient.mk K (algebraMap B A' e0) = τ e := by
              rw [← he0]
              simp [τ, K]
            _ = 1 := hτe
        refine ⟨Ideal.Quotient.mk J b, ?_⟩
        -- Clear the denominator in `A'` and then kill the resulting power of `e0` in the quotient.
        calc
          τ (Ideal.Quotient.mk J b) = Ideal.Quotient.mk K (algebraMap B A' b) := by
            simp [τ, K]
          _ = Ideal.Quotient.mk K z * (Ideal.Quotient.mk K (algebraMap B A' e0)) ^ n := by
            symm
            simpa [K, map_mul, map_pow] using congrArg (Ideal.Quotient.mk K) hb
          _ = Ideal.Quotient.mk K z * 1 := by simp [hclass_one]
          _ = Ideal.Quotient.mk K z := by simp
      -- Route correction: the old proof stalled because the quotient on the localization side was
      -- still written over `B`. The ideal rewrite above pins the target to the theorem's exact
      -- quotient ring before building the localization comparison. The source-faithful skeleton is
      -- now reduced to proving that the target quotient has the same kernel `⟨1 - e⟩`.
      have hspan_le_kerτ :
          Ideal.span ({1 - e} : Set (B ⧸ J)) ≤ RingHom.ker τ.toRingHom := by
        -- Since `τ e = 1`, the complementary generator `1 - e` maps to `0`.
        refine (Ideal.span_singleton_le_iff_mem _).2 ?_
        rw [RingHom.mem_ker]
        calc
          τ (1 - e) = 1 - τ e := by simp
          _ = 0 := by simp [hτe]
      have he_unit :
          IsUnit (canonical_descended_quotient_map (A := A) (B := B) I φ e) := by
        -- The localization structure on `A ⧸ I` already inverts the distinguished idempotent.
        simpa [σ, φbarA, canonical_descended_quotient_map] using
          (IsLocalization.Away.algebraMap_isUnit e :
            IsUnit (algebraMap (B ⧸ J) (A ⧸ I) e))
      let ψ0 : A' →ₐ[A] A ⧸ I :=
        localization_lift_of_factorization (A := A) (B := B) I φ he0 he_unit
      let ψ : (A' ⧸ K) →ₐ[A] A ⧸ I :=
        Ideal.Quotient.liftₐ K ψ0 fun z hz ↦
          RingHom.mem_ker.mp (ideal_map_le_universal_factorization_ker (A := A) I ψ0 hz)
      have hψτ :
          ψ.toRingHom.comp τ.toRingHom = φbarA.toRingHom := by
        apply Ideal.Quotient.ringHom_ext
        ext b
        -- Follow the source route on quotient generators: both maps send `b` to `φ b`.
        change ψ0 (algebraMap B A' b) = φbarA (Ideal.Quotient.mk J b)
        rw [canonical_descended_quotient_map_mk]
        simpa [ψ0] using
          (localization_lift_of_factorization_algebraMap
            (A := A) (B := B) I φ he0 he_unit b)
      have hkerτ :
          RingHom.ker τ.toRingHom = Ideal.span ({1 - e} : Set (B ⧸ J)) := by
        apply le_antisymm
        · intro x hx
          have hτx : τ x = 0 := RingHom.mem_ker.mp hx
          have hxσ : φbarA x = 0 := by
            -- Compose with the descended localization map `ψ` to move from `ker τ` to `ker φbarA`.
            have hcompx := congrArg (fun f => f x) hψτ
            calc
              φbarA x = ψ (τ x) := hcompx.symm
              _ = ψ 0 := by rw [hτx]
              _ = 0 := by simp
          have hxkerσ : x ∈ RingHom.ker φbarA.toRingHom := RingHom.mem_ker.mpr hxσ
          have hxkerσ' : x ∈ RingHom.ker σ.toRingHom := by
            simpa [σ] using hxkerσ
          rw [hkerσ] at hxkerσ'
          exact hxkerσ'
        · simpa using hspan_le_kerτ
      let Q : Type u := (B ⧸ J) ⧸ Ideal.span ({1 - e} : Set (B ⧸ J))
      let τbar : (B ⧸ J) →ₐ[A ⧸ I] A' ⧸ K :=
        AlgHom.extendScalarsOfSurjective (Ideal.Quotient.mkₐ_surjective A I) τ
      have hτbar_surj : Function.Surjective τbar := by
        -- Extending scalars does not change the underlying surjective function of `τ`.
        simpa [τbar] using hτsurj
      have hkerτbar :
          RingHom.ker τbar.toRingHom = Ideal.span ({1 - e} : Set (B ⧸ J)) := by
        -- The `A ⧸ I`-linear version of `τ` has the same kernel as the original map.
        simpa [τbar] using hkerτ
      let qResidue : Q ≃ₐ[A ⧸ I] A ⧸ I :=
        (Ideal.quotientEquivAlgOfEq (A ⧸ I) hkerσ.symm).trans
          (Ideal.quotientKerAlgEquivOfSurjective hσsurj)
      let qTarget : Q ≃ₐ[A ⧸ I] A' ⧸ K :=
        (Ideal.quotientEquivAlgOfEq (A ⧸ I) hkerτbar.symm).trans
          (Ideal.quotientKerAlgEquivOfSurjective hτbar_surj)
      let quotientAlgEquiv : (A ⧸ I) ≃ₐ[A ⧸ I] A' ⧸ K := qResidue.symm.trans qTarget
      have hqResidue_mk (x : B ⧸ J) :
          qResidue (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set (B ⧸ J))) x) = φbarA x := by
        -- The residue-side comparison sends a quotient class back to its image under `φbarA`.
        calc
          qResidue (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set (B ⧸ J))) x)
              = (Ideal.quotientKerAlgEquivOfSurjective hσsurj)
                  ((Ideal.quotientEquivAlgOfEq (A ⧸ I) hkerσ.symm)
                    (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set (B ⧸ J))) x)) := by
                      rfl
          _ = (Ideal.quotientKerAlgEquivOfSurjective hσsurj)
                (Ideal.Quotient.mk (RingHom.ker σ.toRingHom) x) := by
                  rw [Ideal.quotientEquivAlgOfEq_mk]
          _ = algebraMap (B ⧸ J) (A ⧸ I) x := by
                change (Ideal.quotientKerAlgEquivOfSurjective hσsurj)
                    (Ideal.Quotient.mk (RingHom.ker (algebraMap (B ⧸ J) (A ⧸ I))) x) =
                  algebraMap (B ⧸ J) (A ⧸ I) x
                exact Ideal.quotientKerAlgEquivOfSurjective_mk hσsurj x
          _ = φbarA x := by
                rfl
      have hqTarget_mk (x : B ⧸ J) :
          qTarget (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set (B ⧸ J))) x) = τ x := by
        -- The localization-side comparison sends the same quotient class to its image under `τ`.
        calc
          qTarget (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set (B ⧸ J))) x)
              = (Ideal.quotientKerAlgEquivOfSurjective hτbar_surj)
                  ((Ideal.quotientEquivAlgOfEq (A ⧸ I) hkerτbar.symm)
                    (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set (B ⧸ J))) x)) := by
                      rfl
          _ = (Ideal.quotientKerAlgEquivOfSurjective hτbar_surj)
                (Ideal.Quotient.mk (RingHom.ker τbar.toRingHom) x) := by
                  rw [Ideal.quotientEquivAlgOfEq_mk]
          _ = τbar x := by
                exact Ideal.quotientKerAlgEquivOfSurjective_mk hτbar_surj x
          _ = τ x := by
                rfl
      have hqCompare_apply (x : B ⧸ J) : quotientAlgEquiv (φbarA x) = τ x := by
        -- Both quotient equivalences are evaluated on the same representative of `x`.
        have hsymm :
            qResidue.symm (φbarA x) =
              Ideal.Quotient.mk (Ideal.span ({1 - e} : Set (B ⧸ J))) x := by
          apply qResidue.injective
          simp [hqResidue_mk]
        calc
          quotientAlgEquiv (φbarA x) = qTarget (qResidue.symm (φbarA x)) := by rfl
          _ = qTarget (Ideal.Quotient.mk (Ideal.span ({1 - e} : Set (B ⧸ J))) x) := by
              rw [hsymm]
          _ = τ x := hqTarget_mk x
      let g' : A'[X] := gU.map (algebraMap B A')
      let h' : A'[X] := hU.map (algebraMap B A')
      have hg' : g'.Monic := by
        -- Monicity survives the base change from `B` to `A'`.
        simpa [g'] using hgU.map (algebraMap B A')
      have hh' : h'.Monic := by
        -- The same base-change argument handles the second factor.
        simpa [h'] using hhU.map (algebraMap B A')
      have hmulA' : f.map (algebraMap A A') = g' * h' := by
        -- Base change the universal factorization `f = gU * hU` along `B → A'`.
        simpa [g', h', Polynomial.map_map, IsScalarTower.algebraMap_eq A B A'] using
          congrArg (Polynomial.map (algebraMap B A')) hmul
      let gJ : (B ⧸ J)[X] := gU.map (Ideal.Quotient.mk J)
      let hJ : (B ⧸ J)[X] := hU.map (Ideal.Quotient.mk J)
      have hgredJ : gbar = gJ.map φbarA.toRingHom := by
        -- First descend `gU` to `B ⧸ J`, then apply the quotient map `φbarA`.
        simpa [gJ, φbarA, Polynomial.map_map] using hgred
      have hhredJ : hbar = hJ.map φbarA.toRingHom := by
        -- The same normalization works for `hU`.
        simpa [hJ, φbarA, Polynomial.map_map] using hhred
      have hτ_comp_mk :
          τ.toRingHom.comp (Ideal.Quotient.mk J) =
            (Ideal.Quotient.mk K).comp (algebraMap B A') := by
        -- On coefficients from `B`, the quotient map `τ` is the canonical reduction modulo `K`.
        ext b
        simp [τ]
      have hgτ : gJ.map τ.toRingHom = g'.map (Ideal.Quotient.mk K) := by
        -- Reducing the lifted factor `g'` modulo `K` is the same as applying `τ`.
        calc
          gJ.map τ.toRingHom = gU.map (τ.toRingHom.comp (Ideal.Quotient.mk J)) := by
            simp [gJ, Polynomial.map_map]
          _ = gU.map ((Ideal.Quotient.mk K).comp (algebraMap B A')) := by
              rw [hτ_comp_mk]
          _ = g'.map (Ideal.Quotient.mk K) := by
              simp [g', Polynomial.map_map]
      have hhτ : hJ.map τ.toRingHom = h'.map (Ideal.Quotient.mk K) := by
        -- The same quotient computation identifies the reduction of `h'`.
        calc
          hJ.map τ.toRingHom = hU.map (τ.toRingHom.comp (Ideal.Quotient.mk J)) := by
            simp [hJ, Polynomial.map_map]
          _ = hU.map ((Ideal.Quotient.mk K).comp (algebraMap B A')) := by
              rw [hτ_comp_mk]
          _ = h'.map (Ideal.Quotient.mk K) := by
              simp [h', Polynomial.map_map]
      have hgredTarget :
          gbar.map quotientAlgEquiv.toRingHom = g'.map (Ideal.Quotient.mk K) := by
        -- Transport the first reduced factor across the quotient comparison.
        calc
          gbar.map quotientAlgEquiv.toRingHom =
              (gJ.map φbarA.toRingHom).map quotientAlgEquiv.toRingHom := by
                rw [hgredJ]
          _ = gJ.map (quotientAlgEquiv.toRingHom.comp φbarA.toRingHom) := by
                rw [Polynomial.map_map]
          _ = gJ.map τ.toRingHom := by
                congr 1
                ext x
                exact hqCompare_apply x
          _ = g'.map (Ideal.Quotient.mk K) := hgτ
      have hhredTarget :
          hbar.map quotientAlgEquiv.toRingHom = h'.map (Ideal.Quotient.mk K) := by
        -- Transport the second reduced factor across the same comparison.
        calc
          hbar.map quotientAlgEquiv.toRingHom =
              (hJ.map φbarA.toRingHom).map quotientAlgEquiv.toRingHom := by
                rw [hhredJ]
          _ = hJ.map (quotientAlgEquiv.toRingHom.comp φbarA.toRingHom) := by
                rw [Polynomial.map_map]
          _ = hJ.map τ.toRingHom := by
                congr 1
                ext x
                exact hqCompare_apply x
          _ = h'.map (Ideal.Quotient.mk K) := hhτ
      have hgredA' :
          gbar.map quotientAlgEquiv.toRingHom =
            g'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) := by
        -- Rewrite the target quotient ideal back to the theorem statement's exact form.
        simpa [K] using hgredTarget
      have hhredA' :
          hbar.map quotientAlgEquiv.toRingHom =
            h'.map (Ideal.Quotient.mk (Ideal.map (algebraMap A A') I)) := by
        -- The same ideal rewrite handles the second factor.
        simpa [K] using hhredTarget
      exact ⟨Localization.Away e0, inferInstance, inferInstance,
        hEtaleA', quotientAlgEquiv, g', h',
        hg', hh', hmulA', hgredA', hhredA'⟩

end

end Algebra
