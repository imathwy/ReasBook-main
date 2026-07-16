import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_63_1
import stacks_proof.stacks_project.Chap10.Lemma_10_63_18
import stacks_proof.stacks_project.Chap10.Lemma_10_66_2
import stacks_proof.stacks_project.Chap10.Lemma_10_66_5
import stacks_proof.stacks_project.Chap10.Lemma_10_15_5
import stacks_proof.stacks_project.Chap10.Lemma_10_23_1
import stacks_proof.stacks_project.Chap10.Lemma_10_72_2
import stacks_proof.stacks_project.Chap10.Lemma_10_82_13
import stacks_proof.stacks_project.Chap10.Proposition_10_102_9
import stacks_proof.stacks_project.Chap15.Definition_15_15_1
import stacks_proof.stacks_project.Chap15.Lemma_15_3_3
import stacks_proof.stacks_project.Chap15.Lemma_15_15_2
import stacks_proof.stacks_project.Chap15.Lemma_15_15_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise
open RingTheory.Sequence

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

namespace Ideal

/-- In a Noetherian local ring, the length-`1` source-style condition for `I` is equivalent to the
owner depth inequality `1 ≤ I.depth R`. -/
theorem eq_top_or_exists_isRegular_iff_one_le_depth (I : Ideal R) :
    (I = ⊤ ∨ ∃ x ∈ I, IsRegular x) ↔ (1 : WithTop ℕ) ≤ I.depth R := by
  constructor
  · rintro (hI | ⟨x, hxI, hxreg⟩)
    · exact (eq_top_or_exists_regularSequence_of_length_iff_le_depth I 1).mp <| Or.inl hI
    · by_cases hxunit : IsUnit x
      · exact
          (eq_top_or_exists_regularSequence_of_length_iff_le_depth I 1).mp <|
            Or.inl (I.eq_top_of_isUnit_mem hxI hxunit)
      · refine (eq_top_or_exists_regularSequence_of_length_iff_le_depth I 1).mp ?_
        refine Or.inr ⟨[x], ?_, ?_, by simp⟩
        · have hxsmul : IsSMulRegular R x := hxreg.left.isSMulRegular
          have hxsmul_ne_top : x • (⊤ : Ideal R) ≠ ⊤ := by
            intro htop
            apply hxunit
            have hspanTop : Ideal.span ({x} : Set R) = ⊤ := by
              calc
                Ideal.span ({x} : Set R) = Ideal.span ({x} : Set R) • (⊤ : Ideal R) := by simp
                _ = x • (⊤ : Ideal R) := by rw [Submodule.ideal_span_singleton_smul]
                _ = ⊤ := htop
            exact Ideal.span_singleton_eq_top.mp hspanTop
          let _ : Nontrivial (QuotSMulTop x R) := Submodule.Quotient.nontrivial_iff.2 <| by
            simpa [QuotSMulTop] using hxsmul_ne_top
          refine IsRegular.cons hxsmul ?_
          simpa using IsRegular.nil R (QuotSMulTop x R)
        · simpa using (Ideal.span_singleton_le_iff_mem I).2 hxI
  · rintro hdepth
    rcases (eq_top_or_exists_regularSequence_of_length_iff_le_depth I 1).mpr hdepth with
      hI | ⟨rs, hrs, hrs_le, hrs_len⟩
    · exact .inl hI
    · rcases List.length_eq_one_iff.mp hrs_len with ⟨x, rfl⟩
      have hxsmul : IsSMulRegular R x := by
        exact ((isRegular_cons_iff R x []).mp (by simpa using hrs)).1
      refine .inr ⟨x, ?_, ?_⟩
      · exact hrs_le (Ideal.subset_span (by simp : x ∈ {r | r ∈ ([x] : List R)}))
      · refine ⟨hxsmul.isLeftRegular, ?_⟩
        simpa [IsRightRegular, IsSMulRegular, smul_eq_mul, mul_comm] using hxsmul

end Ideal

end

namespace LinearMap

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {m n : ℕ}

open CategoryTheory CategoryTheory.Limits ChainComplex HomologicalComplex

/- Domain triage:
* primary domain: injectivity criteria for maps of finite free modules over a local ring, governed
  upstream by the Buchsbaum--Eisenbud exactness criterion for finite free complexes;
* sampled owner declarations of the same kind:
  `LinearMap.exteriorRank`,
  `LinearMap.rankMinorIdeal`,
  `Ideal.eq_top_or_exists_regularSequence_of_length_iff_le_depth`,
  `FiniteFreeComplex.exactInPositiveDegrees_iff_buchsbaumEisenbud_depth_criterion`;
* core/canonical owner: the Chapter 10 Buchsbaum--Eisenbud criterion, specialized here to a
  two-term complex, with the Noetherian ideal-theoretic clause canonically expressed via
  `Ideal.depth`;
* source-facing layer: the injectivity criterion with annihilator zero and its regular-element
  reformulation below;
* bridge/view layer: the depth reformulation and the local length-`1` regular-sequence bridge
  between `Ideal.depth` and `I(φ) = ⊤ ∨ ∃ x ∈ I(φ), IsRegular x`.

Primitive data are only the map `φ`, its owner invariants `exteriorRank φ` and `I(φ)`, and the
ambient local-ring hypotheses. The annihilator and nonzerodivisor conditions are derived API, so
this file should reuse the chapter owner abstraction instead of introducing a parallel determinantal
package.
-/

/-- Helper for Lemma 15.15.6: the standard-coordinate matrix of a linear map on `R^m` recovers
the original map via `Matrix.toLin'`. -/
private lemma toLin'_toMatrix_basisFun
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).toLin' = φ := by
  -- Both maps are determined by their values on coordinate vectors.
  ext x i
  simp [Matrix.toLin'_apply, LinearMap.toMatrix, dotProduct]

/-- Helper for Lemma 15.15.6: localizing `R^r` at a prime `p` identifies it with coordinate
functions over `Localization.AtPrime p`. -/
private def localizedFreeSectionsAtPrimeEquivR
    {p : Ideal R} [p.IsPrime] (r : ℕ) :
    LocalizedModule.AtPrime p (Fin r → R) ≃ₗ[R] (Fin r → Localization.AtPrime p) :=
  IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl (Fin r → R))
    (LinearMap.pi fun i : Fin r ↦
      (Algebra.linearMap R (Localization.AtPrime p)).comp (LinearMap.proj i))

/-- Helper for Lemma 15.15.6: on denominator-`1` generators, the localized free-module
identification applies the localization map coordinatewise. -/
private theorem localizedFreeSectionsAtPrimeEquivR_mk_apply
    {p : Ideal R} [p.IsPrime] (r : ℕ) (v : Fin r → R) (i : Fin r) :
    localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) r
        ((LocalizedModule.mkLinearMap p.primeCompl (Fin r → R)) v) i =
      algebraMap R (Localization.AtPrime p) (v i) := by
  -- Evaluate the universal localization comparison on a standard free generator.
  simpa [localizedFreeSectionsAtPrimeEquivR] using
    congrFun
      (IsLocalizedModule.linearEquiv_apply p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl (Fin r → R))
        (LinearMap.pi fun j : Fin r ↦
          (Algebra.linearMap R (Localization.AtPrime p)).comp (LinearMap.proj j))
        v)
      i

/-- Helper for Lemma 15.15.6: after identifying prime-localized free modules with coordinate
functions, the localized map agrees pointwise with the mapped matrix. -/
private theorem localized_coordinate_map_apply
    {p : Ideal R} [p.IsPrime]
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (x : LocalizedModule.AtPrime p (Fin m → R)) :
    let eSource := localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) m
    let eTarget := localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) n
    eTarget (LocalizedModule.map p.primeCompl φ x) =
      (((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).map
          (algebraMap R (Localization.AtPrime p))).toLin') (eSource x) := by
  let Rp := Localization.AtPrime p
  let f := LocalizedModule.mkLinearMap p.primeCompl (Fin m → R)
  let g := LocalizedModule.mkLinearMap p.primeCompl (Fin n → R)
  let eSource := localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) m
  let eTarget := localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) n
  let uLoc : (Fin m → Rp) →ₗ[Rp] (Fin n → Rp) :=
    ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).map
      (algebraMap R Rp)).toLin'
  obtain ⟨⟨v, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective p.primeCompl f x
  -- Clear the single localization denominator and compare the resulting numerator formula.
  apply (IsUnit.smul_left_cancel (IsLocalization.map_units Rp s)).mp
  calc
    (algebraMap R Rp s) • eTarget (LocalizedModule.map p.primeCompl φ (IsLocalizedModule.mk' f v s))
        = eTarget ((s : R) • LocalizedModule.map p.primeCompl φ
            (IsLocalizedModule.mk' f v s)) := by
              simpa [Algebra.smul_def] using
                (eTarget.map_smul (s : R)
                  (LocalizedModule.map p.primeCompl φ (IsLocalizedModule.mk' f v s))).symm
    _ = eTarget (LocalizedModule.map p.primeCompl φ
          ((s : R) • IsLocalizedModule.mk' f v s)) := by
            congr 1
            simpa using
              (LocalizedModule.map p.primeCompl φ).map_smul (s : R)
                (IsLocalizedModule.mk' f v s)
    _ = eTarget (LocalizedModule.map p.primeCompl φ (f v)) := by
          simp [IsLocalizedModule.mk'_smul]
    _ = eTarget (g (φ v)) := by
          simpa [f, g] using
            congrArg
              (fun h : (Fin m → R) →ₗ[R] LocalizedModule.AtPrime p (Fin n → R) ↦ h v)
              (IsLocalizedModule.map_comp p.primeCompl f g φ)
    _ = uLoc (eSource (f v)) := by
          ext i
          calc
            eTarget (g (φ v)) i = algebraMap R Rp ((φ v) i) := by
              simpa [g] using
                localizedFreeSectionsAtPrimeEquivR_mk_apply (R := R) (p := p) n (φ v) i
            _ = (uLoc (fun j ↦ algebraMap R Rp (v j))) i := by
              simp [uLoc, Matrix.toLin'_apply, LinearMap.toMatrix, dotProduct]
            _ = uLoc (eSource (f v)) i := by
              congr 1
              ext j
              simpa [f] using
                localizedFreeSectionsAtPrimeEquivR_mk_apply (R := R) (p := p) m v j
    _ = uLoc (eSource ((s : R) • IsLocalizedModule.mk' f v s)) := by
          simp [IsLocalizedModule.mk'_smul]
    _ = uLoc ((s : R) • eSource (IsLocalizedModule.mk' f v s)) := by
          congr 1
          simpa using eSource.map_smul (s : R) (IsLocalizedModule.mk' f v s)
    _ = uLoc ((algebraMap R Rp s) • eSource (IsLocalizedModule.mk' f v s)) := by
          simp [Algebra.smul_def]
    _ = (algebraMap R Rp s) • uLoc (eSource (IsLocalizedModule.mk' f v s)) := by
          simpa using
            (uLoc.map_smul (algebraMap R Rp s) (eSource (IsLocalizedModule.mk' f v s))).symm

/-- Helper for Lemma 15.15.6: localizing an injective free-module map at a prime and then
expressing it in coordinates preserves injectivity. -/
private theorem localized_coordinate_map_injective
    {p : Ideal R} [p.IsPrime]
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hφ : Function.Injective φ) :
    Function.Injective
      ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).map
        (algebraMap R (Localization.AtPrime p))).toLin' := by
  let eSource := localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) m
  let eTarget := localizedFreeSectionsAtPrimeEquivR (R := R) (p := p) n
  let uLoc :
      (Fin m → Localization.AtPrime p) →ₗ[Localization.AtPrime p]
        (Fin n → Localization.AtPrime p) :=
    ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).map
      (algebraMap R (Localization.AtPrime p))).toLin'
  have hkerLocalized :
      LinearMap.ker (LocalizedModule.map p.primeCompl φ) = ⊥ := by
    -- Localization preserves the zero kernel of the original injective map.
    calc
      LinearMap.ker (LocalizedModule.map p.primeCompl φ) =
        Submodule.localized'
          (Localization.AtPrime p) p.primeCompl
          (LocalizedModule.mkLinearMap p.primeCompl (Fin m → R))
          (LinearMap.ker φ) := by
            symm
            simpa using
              (LinearMap.localized'_ker_eq_ker_localizedMap
                (S := Localization.AtPrime p)
                (p := p.primeCompl)
                (f := LocalizedModule.mkLinearMap p.primeCompl (Fin m → R))
                (f' := LocalizedModule.mkLinearMap p.primeCompl (Fin n → R))
                (g := φ))
      _ = ⊥ := by
            simpa [LinearMap.ker_eq_bot.mpr hφ]
  have hLocalized : Function.Injective (LocalizedModule.map p.primeCompl φ) :=
    LinearMap.ker_eq_bot.mp hkerLocalized
  intro x y hxy
  have hpre :
      eTarget.toLinearMap (LocalizedModule.map p.primeCompl φ (eSource.symm x)) =
        eTarget.toLinearMap (LocalizedModule.map p.primeCompl φ (eSource.symm y)) := by
    -- Compare the two localized vectors through the pointwise coordinate bridge.
    calc
      eTarget.toLinearMap (LocalizedModule.map p.primeCompl φ (eSource.symm x)) = uLoc x := by
        simpa [uLoc, eSource, eTarget] using
          localized_coordinate_map_apply (R := R) (p := p) φ (x := eSource.symm x)
      _ = uLoc y := hxy
      _ = eTarget.toLinearMap (LocalizedModule.map p.primeCompl φ (eSource.symm y)) := by
        symm
        simpa [uLoc, eSource, eTarget] using
          localized_coordinate_map_apply (R := R) (p := p) φ (x := eSource.symm y)
  exact eSource.symm.injective <| hLocalized <| eTarget.injective hpre

/-- Helper for Lemma 15.15.6: the free quotient equivalence sends a quotient representative to
its coordinatewise residue classes. -/
private theorem free_pi_quotient_equiv_apply_mkQ
    {S : Type*} [CommRing S] (I : Ideal S) (r : ℕ) (x : Fin r → S) :
    free_pi_quotient_equiv (R := S) (I := I) r ((I • (⊤ : Submodule S (Fin r → S))).mkQ x) =
      fun i ↦ Ideal.Quotient.mk I (x i) := by
  -- Unfold the quotient comparison only on a quotient representative.
  simp [free_pi_quotient_equiv, free_pi_quotient_map]

/-- Helper for Lemma 15.15.6: after quotienting by an ideal and identifying free quotients with
coordinate functions, the quotient map attached to a matrix is the concrete closed-fiber matrix
map. -/
private theorem closedFiber_matrix_map_apply
    {S : Type*} [CommRing S] (I : Ideal S) (B : Matrix (Fin n) (Fin m) S)
    (x : Fin m → S ⧸ I) :
    let eSource := free_pi_quotient_equiv (R := S) (I := I) m
    let eTarget := free_pi_quotient_equiv (R := S) (I := I) n
    eTarget ((B.toLin').quotientMapByIdeal I (eSource.symm x)) =
      ((B.map (Ideal.Quotient.mk I)).toLin') x := by
  let eSource := free_pi_quotient_equiv (R := S) (I := I) m
  let eTarget := free_pi_quotient_equiv (R := S) (I := I) n
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule S (Fin m → S))) (eSource.symm x)
  have hx :
      x = fun i ↦ Ideal.Quotient.mk I (y i) := by
    -- Replace the abstract quotient element by an explicit coordinate representative.
    calc
      x = eSource (eSource.symm x) := by simp [eSource]
      _ = eSource ((I • (⊤ : Submodule S (Fin m → S))).mkQ y) := by rw [hy]
      _ = fun i ↦ Ideal.Quotient.mk I (y i) := by
            simp [eSource, free_pi_quotient_equiv, free_pi_quotient_map]
  calc
    eTarget ((B.toLin').quotientMapByIdeal I (eSource.symm x))
        = eTarget ((B.toLin').quotientMapByIdeal I
            ((I • (⊤ : Submodule S (Fin m → S))).mkQ y)) := by
              rw [hy]
    _ = eTarget ((I • (⊤ : Submodule S (Fin n → S))).mkQ (B.toLin' y)) := by
          rw [quotientMapByIdeal_apply_mkQ]
    _ = fun i ↦ Ideal.Quotient.mk I ((B.toLin' y) i) := by
          simp [eTarget, free_pi_quotient_equiv_apply_mkQ]
    _ = ((B.map (Ideal.Quotient.mk I)).toLin') (fun i ↦ Ideal.Quotient.mk I (y i)) := by
          ext i
          simp [Matrix.toLin'_apply, dotProduct]
    _ = ((B.map (Ideal.Quotient.mk I)).toLin') x := by
          rw [hx]

/-- Helper for Lemma 15.15.6: universal injectivity of the localized coordinate matrix map forces
the corresponding closed-fiber matrix map to be injective. -/
private theorem injective_closedFiber_matrix_map_of_localized_universallyInjective
    {p : Ideal R} [p.IsPrime]
    (A : Matrix (Fin n) (Fin m) R)
    (huLoc : UniversallyInjective ((A.map (algebraMap R (Localization.AtPrime p))).toLin')) :
    Function.Injective
      ((A.map
          ((Ideal.Quotient.mk (maximalIdeal (Localization.AtPrime p))).comp
            (algebraMap R (Localization.AtPrime p)))).toLin') := by
  let Rp := Localization.AtPrime p
  let I : Ideal Rp := maximalIdeal Rp
  let θ : R →+* Rp ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R Rp)
  let uLoc : (Fin m → Rp) →ₗ[Rp] (Fin n → Rp) := (A.map (algebraMap R Rp)).toLin'
  let eSource := free_pi_quotient_equiv (R := Rp) (I := I) m
  let eTarget := free_pi_quotient_equiv (R := Rp) (I := I) n
  have hquot : Function.Injective (uLoc.quotientMapByIdeal I) :=
    injective_quotientMapByIdeal_of_universallyInjective uLoc huLoc I
  intro x y hxy
  have hpre :
      eTarget (uLoc.quotientMapByIdeal I (eSource.symm x)) =
        eTarget (uLoc.quotientMapByIdeal I (eSource.symm y)) := by
    -- Compare the quotient map with the explicit closed-fiber matrix map on both vectors.
    calc
      eTarget (uLoc.quotientMapByIdeal I (eSource.symm x)) = ((A.map θ).toLin') x := by
        simpa [uLoc, θ, eSource, eTarget] using
          closedFiber_matrix_map_apply (I := I) (B := A.map (algebraMap R Rp)) (x := x)
      _ = ((A.map θ).toLin') y := hxy
      _ = eTarget (uLoc.quotientMapByIdeal I (eSource.symm y)) := by
        symm
        simpa [uLoc, θ, eSource, eTarget] using
          closedFiber_matrix_map_apply (I := I) (B := A.map (algebraMap R Rp)) (x := y)
  exact eSource.symm.injective <| hquot <| eTarget.injective hpre

namespace Ideal

/-- Helper for Lemma 15.15.6: weak association at a prime localizes to the auto-associated
structure on the local ring `R_𝔭`. -/
private theorem isAutoAssociatedRing_atPrime_of_isWeaklyAssociatedToModule
    {p : Ideal R} [p.IsPrime] (hp : Ideal.IsWeaklyAssociatedToModule R R p) :
    IsAutoAssociatedRing (Localization.AtPrime p) := by
  -- Repackage the localized weak-association clause as the owner `IsAutoAssociatedRing`
  -- predicate on `R_𝔭`.
  rw [isAutoAssociatedRing_iff]
  exact
    (isWeaklyAssociatedToModule_iff_isWeaklyAssociatedToModule_maximalIdeal_atPrime
      (R := R) (M := R) (𝔭 := p)).mp hp

end Ideal

namespace Matrix

/-- Helper for Lemma 15.15.6: forming the `r × r` minor ideal commutes with a ring map. -/
private theorem minorIdeal_map_eq
    {S : Type*} [CommRing S] (σ : R →+* S) {ι κ : Type*} (r : ℕ) (A : Matrix ι κ R) :
    Ideal.map σ (Matrix.minorIdeal r A) = Matrix.minorIdeal r (A.map σ) := by
  classical
  -- Unfold the owner definition and identify the image of each determinant generator.
  unfold Matrix.minorIdeal
  rw [Ideal.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨p, rfl⟩, rfl⟩
    refine ⟨p, ?_⟩
    have hsub :
        σ.mapMatrix (A.submatrix p.1 p.2) = (A.map σ).submatrix p.1 p.2 := by
      ext i j
      rfl
    simpa [hsub] using (RingHom.map_det σ (A.submatrix p.1 p.2)).symm
  · rintro ⟨p, hp⟩
    refine ⟨(A.submatrix p.1 p.2).det, ?_, ?_⟩
    · exact ⟨p, rfl⟩
    · have hsub :
          σ.mapMatrix (A.submatrix p.1 p.2) = (A.map σ).submatrix p.1 p.2 := by
        ext i j
        rfl
      calc
        σ (A.submatrix p.1 p.2).det = ((A.map σ).submatrix p.1 p.2).det := by
          simpa [hsub] using RingHom.map_det σ (A.submatrix p.1 p.2)
        _ = y := hp

end Matrix

namespace Ideal

/-- Helper for Lemma 15.15.6: a weakly associated prime of the annihilator ideal of `J` contains
`J` itself. -/
private theorem le_of_mem_weaklyAssociatedPrimes_annihilator
    (J p : Ideal R) (hp : p ∈ weaklyAssociatedPrimes R J.annihilator) :
    J ≤ p := by
  -- Unpack the weakly associated witness inside `J.annihilator` and observe that each element of
  -- `J` kills that witness, hence belongs to its torsion ideal.
  rw [mem_weaklyAssociatedPrimes_iff] at hp
  rcases hp with ⟨x, hx⟩
  intro y hy
  have hy_tors : y ∈ Ideal.torsionOf R J.annihilator x := by
    rw [Ideal.mem_torsionOf_iff]
    ext
    simpa [mul_comm] using (Submodule.mem_annihilator.mp x.2) y hy
  exact hx.1.2 hy_tors

/-- Helper for Lemma 15.15.6: a weakly associated prime of the annihilator ideal of `J` is also
weakly associated to the regular module `R`. -/
private theorem isWeaklyAssociatedToModule_of_mem_weaklyAssociatedPrimes_annihilator
    (J p : Ideal R) (hp : p ∈ weaklyAssociatedPrimes R J.annihilator) :
    Ideal.IsWeaklyAssociatedToModule R R p := by
  rw [mem_weaklyAssociatedPrimes_iff] at hp ⊢
  rcases hp with ⟨x, hx⟩
  refine ⟨x.1, ?_⟩
  -- The annihilator ideal is a submodule of `R`, so the same witness works in the ambient module.
  simpa [Ideal.mem_torsionOf_iff] using hx

/-- Helper for Lemma 15.15.6: if `J` is contained in a prime `p`, then the image of `J` in the
residue field of `R_p` is zero. -/
private theorem map_residue_map_eq_bot_of_le_prime
    {p J : Ideal R} [p.IsPrime] (hJp : J ≤ p) :
    Ideal.map ((IsLocalRing.residue (Localization.AtPrime p)).comp
        (algebraMap R (Localization.AtPrime p))) J =
      (⊥ : Ideal (IsLocalRing.ResidueField (Localization.AtPrime p))) := by
  let Rp := Localization.AtPrime p
  let σ : R →+* IsLocalRing.ResidueField Rp := (IsLocalRing.residue Rp).comp (algebraMap R Rp)
  -- First reduce the vanishing claim to containment in the kernel of the residue-field map.
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro x hxJ
  -- Then map `x` into `R_p`, use `J ≤ p`, and identify the image of `p` with the maximal ideal.
  change algebraMap R Rp x ∈ RingHom.ker (IsLocalRing.residue Rp)
  rw [IsLocalRing.ker_residue]
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp]
  exact Ideal.mem_map_of_mem (algebraMap R Rp) (hJp hxJ)

end Ideal

/-- Helper for Lemma 15.15.6: over a field, an injective map has unit maximal-minor ideal. -/
private theorem maximal_minorIdeal_eq_top_of_injective_over_field
    {K : Type*} [Field K] (ψ : (Fin m → K) →ₗ[K] (Fin n → K))
    (hψ : Function.Injective ψ) :
    Matrix.minorIdeal m
        (LinearMap.toMatrix (Pi.basisFun K (Fin m)) (Pi.basisFun K (Fin n)) ψ) = ⊤ := by
  let A : Matrix (Fin n) (Fin m) K :=
    LinearMap.toMatrix (Pi.basisFun K (Fin m)) (Pi.basisFun K (Fin n)) ψ
  obtain ⟨g, hg⟩ :=
    LinearMap.exists_leftInverse_of_injective ψ (LinearMap.ker_eq_bot.mpr hψ)
  let B : Matrix (Fin m) (Fin n) K :=
    LinearMap.toMatrix (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin m)) g
  have hBA : B * A = (1 : K) • (1 : Matrix (Fin m) (Fin m) K) := by
    -- Translate the left inverse into the standard-coordinate matrix identity `B * A = 1`.
    simpa [A, B, hg] using
      (LinearMap.toMatrix_comp
        (Pi.basisFun K (Fin m))
        (Pi.basisFun K (Fin n))
        (Pi.basisFun K (Fin m))
        g ψ).symm
  have hone : (1 : K) ∈ Matrix.minorIdeal m A := by
    -- The Cramer-style determinantal lemma now forces `1 ^ m = 1` into the maximal-minor ideal.
    simpa using (pow_mem_minorIdeal_of_mul_eq_smul_one A B hBA)
  rw [Ideal.eq_top_iff_one]
  exact hone

/-- Helper for Lemma 15.15.6: if the requested minor size exceeds the number of rows, then the
corresponding minor ideal is zero. -/
private theorem minorIdeal_eq_bot_of_lt_rows (A : Matrix (Fin n) (Fin m) R) (hmn : n < m) :
    Matrix.minorIdeal m A = ⊥ := by
  classical
  -- There are no row embeddings `Fin m ↪ Fin n`, so every would-be generator is impossible.
  rw [Matrix.minorIdeal, Ideal.span_eq_bot]
  rintro x ⟨⟨e₁, e₂⟩, rfl⟩
  exact False.elim <| Nat.not_le_of_lt hmn (Fintype.card_le_of_embedding e₁)

/-- Helper for Lemma 15.15.6: vanishing of the top exterior-power map forces every maximal minor
of the standard matrix of `φ` to vanish. -/
private theorem det_submatrix_eq_zero_of_exteriorPower_map_eq_zero
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hzero : exteriorPower.map m φ = 0)
    (e₁ : Fin m ↪ Fin n) (e₂ : Fin m ↪ Fin m) :
    ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).submatrix e₁ e₂).det =
      0 := by
  let bdom := Module.Basis.exteriorPower m (Pi.basisFun R (Fin m))
  let bcod := Module.Basis.exteriorPower m (Pi.basisFun R (Fin n))
  let sdom : Set.powersetCard (Fin m) m := Set.powersetCard.ofFinEmbEquiv.symm e₂
  let scod : Set.powersetCard (Fin n) m := Set.powersetCard.ofFinEmbEquiv.symm e₁
  have happly :
      exteriorPower.map m φ (bdom sdom) = 0 := by
    -- Evaluate the zero map on the basis vector indexed by the chosen source embedding.
    simpa [hzero]
  have hcoeff :
      bcod.repr (exteriorPower.map m φ (bdom sdom)) scod = 0 := by
    simpa [happly]
  -- Expand both basis elements as `ιMulti` generators and read off the chosen matrix coefficient.
  have hdom :
      (bdom sdom : ⋀[R]^m (Fin m → R)) =
        exteriorPower.ιMulti R m (fun i ↦ Pi.single (e₂ i) (1 : R)) := by
    apply Subtype.ext
    simpa [bdom, sdom] using
      (ExteriorAlgebra.basis_apply_powersetCard
        (b := Pi.basisFun R (Fin m))
        (s := sdom)).symm
  have hcod :
      bcod.repr
          (exteriorPower.ιMulti R m (fun i ↦ φ (Pi.single (e₂ i) (1 : R)))) scod =
        ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).submatrix e₁ e₂).det := by
    simpa [bcod, scod, exteriorPower.basis_repr_apply, LinearMap.toMatrix_apply, Pi.single_apply]
  -- `exteriorPower.map_apply_ιMulti` turns the coefficient into the requested determinant.
  rw [hdom, exteriorPower.map_apply_ιMulti] at hcoeff
  simpa [hcod] using hcoeff

/-- Helper for Lemma 15.15.6: if the annihilator of the maximal-minor ideal is zero, then `φ`
already has full exterior rank and the same annihilator conclusion for `I(φ)`. -/
private theorem exteriorRank_eq_and_annihilator_rankMinorIdeal_eq_bot_of_maximal_minor_annihilator
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hannm :
      (Matrix.minorIdeal m
        (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ)).annihilator =
        (⊥ : Ideal R)) :
    exteriorRank φ = m ∧
      (I(φ)).annihilator = (⊥ : Ideal R) := by
  let A : Matrix (Fin n) (Fin m) R :=
    LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ
  have hmn : m ≤ n := by
    by_contra hmn
    have hbot : Matrix.minorIdeal m A = ⊥ := minorIdeal_eq_bot_of_lt_rows A (Nat.lt_of_not_ge hmn)
    have htop : (Matrix.minorIdeal m A).annihilator = (⊤ : Ideal R) := by
      simpa [hbot]
    exact Ideal.top_ne_bot <| by simpa [A] using hannm.trans htop.symm
  have htop_map : exteriorPower.map m φ ≠ 0 := by
    intro hzero
    have hminor_zero :
        ∀ e₁ : Fin m ↪ Fin n, ∀ e₂ : Fin m ↪ Fin m, (A.submatrix e₁ e₂).det = 0 := by
      intro e₁ e₂
      simpa [A] using det_submatrix_eq_zero_of_exteriorPower_map_eq_zero (φ := φ) hzero e₁ e₂
    have hbot : Matrix.minorIdeal m A = ⊥ := by
      classical
      rw [Matrix.minorIdeal, Ideal.span_eq_bot]
      rintro x ⟨⟨e₁, e₂⟩, rfl⟩
      exact hminor_zero e₁ e₂
    have htop : (Matrix.minorIdeal m A).annihilator = (⊤ : Ideal R) := by
      simpa [hbot]
    exact Ideal.top_ne_bot <| by simpa [A] using hannm.trans htop.symm
  have hrank_ge : m ≤ exteriorRank φ := by
    -- Since the top exterior-power map is nonzero and `m ≤ min m n`, `m` is below the find-greatest
    -- value defining the exterior rank.
    exact Nat.le_findGreatest (by simpa [hmn] using hmn) htop_map
  have hrank_le : exteriorRank φ ≤ m := by
    exact le_trans (exteriorRank_le_min φ) (min_le_left _ _)
  have hrank : exteriorRank φ = m := le_antisymm hrank_le hrank_ge
  have hann : (I(φ)).annihilator = (⊥ : Ideal R) := by
    -- Once the exterior rank is `m`, the rank-minor ideal is exactly the maximal-minor ideal.
    simpa [LinearMap.rankMinorIdeal, hrank, A] using hannm
  exact ⟨hrank, hann⟩

/-- Helper for Lemma 15.15.6: if `J` is contained in a prime `p`, then its image in the closed
fiber of `R_p` is zero. -/
private theorem map_closedFiber_quotient_eq_bot_of_le_prime
    {p J : Ideal R} [p.IsPrime] (hJp : J ≤ p) :
    let Rp := Localization.AtPrime p
    let I : Ideal Rp := maximalIdeal Rp
    let θ : R →+* Rp ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R Rp)
    Ideal.map θ J = (⊥ : Ideal (Rp ⧸ I)) := by
  dsimp
  -- The quotient map kills exactly the maximal ideal of `R_p`, and `J` maps into that ideal.
  rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  intro x hxJ
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
  exact Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) (hJp hxJ)

/-- Helper for Lemma 15.15.6: the remaining source-faithful step is to show that injectivity of
`φ` forces the annihilator of the maximal-minor ideal of its matrix to vanish. -/
private theorem annihilator_maximal_minorIdeal_eq_bot_of_injective
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hφ : Function.Injective φ) :
    (Matrix.minorIdeal m
      (LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ)).annihilator =
      (⊥ : Ideal R) := by
  let A : Matrix (Fin n) (Fin m) R :=
    LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ
  let J : Ideal R := Matrix.minorIdeal m A
  have hEmpty : weaklyAssociatedPrimes R J.annihilator = ∅ := by
    -- Route correction: keep the weakly-associated-prime contradiction, but route the
    -- localization and closed-fiber transports through the local pointwise bridge lemmas so the
    -- quotient-model API stays concrete without importing the stalled bridge bundle.
    refine Set.eq_empty_iff_forall_not_mem.mpr ?_
    intro p hp
    have hpWeak : Ideal.IsWeaklyAssociatedToModule R R p :=
      Ideal.isWeaklyAssociatedToModule_of_mem_weaklyAssociatedPrimes_annihilator J p hp
    haveI : p.IsPrime := hpWeak.isPrime
    let Rp := Localization.AtPrime p
    let I : Ideal Rp := maximalIdeal Rp
    let θ : R →+* Rp ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R Rp)
    let uLoc : (Fin m → Rp) →ₗ[Rp] (Fin n → Rp) := (A.map (algebraMap R Rp)).toLin'
    let _ : IsAutoAssociatedRing Rp :=
      Ideal.isAutoAssociatedRing_atPrime_of_isWeaklyAssociatedToModule hpWeak
    have hLocInj : Function.Injective uLoc := by
      -- First pass to the prime localization and rewrite it as the coordinatewise matrix map.
      simpa [A, uLoc] using localized_coordinate_map_injective (R := R) (p := p) φ hφ
    have huLoc :
        UniversallyInjective uLoc := by
      -- Over the auto-associated local ring `R_p`, injectivity is equivalent to universal
      -- injectivity by the earlier Chapter 15 criterion.
      exact
        (universallyInjective_iff_injective_of_projective_of_proper_fg_ideal_annihilator_ne_bot
          (R := Rp)
          (N := Fin m → Rp)
          (M := Fin n → Rp)
          (hP := fun {K} hK hKtop ↦
            IsAutoAssociatedRing.annihilator_ne_bot_of_fg_of_ne_top hK hKtop)
          uLoc).2 hLocInj
    let _ : Field (Rp ⧸ I) := Ideal.Quotient.field I
    have hClosedInj : Function.Injective ((A.map θ).toLin') :=
      injective_closedFiber_matrix_map_of_localized_universallyInjective
        (R := R) (p := p) A huLoc
    have hTop : Matrix.minorIdeal m (A.map θ) = ⊤ := by
      -- Over the closed fiber field, an injective map has unit maximal-minor ideal.
      exact maximal_minorIdeal_eq_top_of_injective_over_field ((A.map θ).toLin') hClosedInj
    have hJle : J ≤ p := Ideal.le_of_mem_weaklyAssociatedPrimes_annihilator J p hp
    have hMapBot : Ideal.map θ J = (⊥ : Ideal (Rp ⧸ I)) :=
      map_closedFiber_quotient_eq_bot_of_le_prime (R := R) (p := p) hJle
    have hMapTop : Ideal.map θ J = (⊤ : Ideal (Rp ⧸ I)) := by
      -- Transport the closed-fiber maximal-minor computation back to the image of `J`.
      simpa [J, A] using (Matrix.minorIdeal_map_eq (σ := θ) (r := m) A).trans hTop
    exact Ideal.top_ne_bot <| hMapTop.trans hMapBot.symm
  have hSubsingleton : Subsingleton J.annihilator := by
    -- An ideal with no weakly associated primes must be the zero module.
    exact
      (subsingleton_iff_weaklyAssociatedPrimes_eq_empty :
        Subsingleton J.annihilator ↔ weaklyAssociatedPrimes R J.annihilator = ∅).2 hEmpty
  -- Translate the subsingleton ideal back to the equality `Ann(J) = 0`.
  ext x
  constructor
  · intro hx
    rw [Ideal.mem_bot]
    exact hSubsingleton.elim x 0
  · intro hx
    rw [Ideal.mem_bot] at hx
    simpa [hx] using (show (0 : R) ∈ J.annihilator from zero_mem _)

/-- Helper for Lemma 15.15.6: full exterior rank together with trivial annihilator of `I(φ)`
forces injectivity by the Cramer-style kernel annihilation argument. -/
private theorem injective_of_exteriorRank_eq_and_annihilator_rankMinorIdeal_eq_bot
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hrank : exteriorRank φ = m)
    (hann : (I(φ)).annihilator = (⊥ : Ideal R)) :
    Function.Injective φ := by
  let A : Matrix (Fin n) (Fin m) R :=
    LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ
  rw [← LinearMap.ker_eq_bot]
  ext x
  constructor
  · intro hx
    ext i
    have hAx : A.toLin' x = 0 := by
      -- Translate the kernel equation into the standard-coordinate matrix model.
      simpa [LinearMap.mem_ker, A, toLin'_toMatrix_basisFun (φ := φ)] using hx
    have hcoord_ann : x i ∈ (I(φ)).annihilator := by
      rw [Submodule.mem_annihilator]
      intro f hf
      have hf_minor : f ∈ Matrix.minorIdeal m A := by
        simpa [LinearMap.rankMinorIdeal, hrank, A] using hf
      rcases exists_mul_eq_smul_one_of_mem_minorIdeal A hf_minor with ⟨B, hBA⟩
      have hBA_lin :
          ((B * A).toLin' : (Fin m → R) →ₗ[R] (Fin m → R)) =
            ((f • (1 : Matrix (Fin m) (Fin m) R)).toLin' : (Fin m → R) →ₗ[R] (Fin m → R)) := by
        simpa using
          congrArg
            (fun M : Matrix (Fin m) (Fin m) R =>
              (M.toLin' : (Fin m → R) →ₗ[R] (Fin m → R)))
            hBA
      have hfx_lin : ((f • (1 : Matrix (Fin m) (Fin m) R)).toLin') x = 0 := by
        -- Compose the left-inverse-up-to-`f` identity with the kernel vector `x`.
        calc
          ((f • (1 : Matrix (Fin m) (Fin m) R)).toLin') x = ((B * A).toLin') x := by
            rw [← hBA_lin]
          _ = B.toLin' (A.toLin' x) := by
            simp [LinearMap.comp_apply, Matrix.toLin'_mul]
          _ = 0 := by simp [hAx]
      have hfx : f • x = 0 := by
        -- The scalar matrix `f • 1` acts as scalar multiplication by `f`.
        simpa [Matrix.toLin'_one] using hfx_lin
      simpa [smul_eq_mul, mul_comm] using congrFun hfx i
    have hxi_bot : x i ∈ (⊥ : Ideal R) := by
      simpa [hann] using hcoord_ann
    simpa [Ideal.mem_bot] using hxi_bot
  · intro hx
    have hx0 : x = 0 := by simpa using hx
    simpa [LinearMap.mem_ker, hx0]

/-- Helper for Lemma 15.15.6: injectivity should force full exterior rank together with trivial
annihilator of `I(φ)` via the source-faithful weakly-associated-prime localization argument. -/
private theorem exteriorRank_eq_and_annihilator_rankMinorIdeal_eq_bot_of_injective
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hφ : Function.Injective φ) :
    exteriorRank φ = m ∧
      (I(φ)).annihilator = (⊥ : Ideal R) := by
  -- Route correction: first prove the maximal-minor ideal has trivial annihilator, then convert
  -- that concrete matrix statement into the claimed exterior-rank and rank-minor-ideal statement.
  exact
    exteriorRank_eq_and_annihilator_rankMinorIdeal_eq_bot_of_maximal_minor_annihilator
      φ (annihilator_maximal_minorIdeal_eq_bot_of_injective φ hφ)

-- Proof sketch: for the forward implication, reduce to weakly associated primes of the local
-- ring and use the auto-associated criteria from the preceding lemmas to show that the rank-minor
-- ideal survives in every weakly associated residue field, forcing full exterior rank and trivial
-- annihilator. For the converse, use the full-rank condition to write the identity on `R^m`
-- locally through finitely many maximal minors, and then the trivial annihilator of the rank-minor
-- ideal kills every kernel element.
/-- Lemma 15.15.6: for a map `φ : R^m → R^n` of finite free modules over a local ring, `φ` is
injective if and only if it has exterior rank `m` and the annihilator of its rank-minor ideal
`I(φ)` is zero. -/
@[stacks 00MX]
theorem injective_iff_exteriorRank_eq_and_annihilator_rankMinorIdeal_eq_bot
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      exteriorRank φ = m ∧
        (I(φ)).annihilator = (⊥ : Ideal R) := by
  constructor
  · intro hφ
    -- The forward implication is isolated in the dedicated localization helper.
    exact exteriorRank_eq_and_annihilator_rankMinorIdeal_eq_bot_of_injective φ hφ
  · rintro ⟨hrank, hann⟩
    -- The converse is the direct Cramer-style kernel annihilation argument.
    exact
      injective_of_exteriorRank_eq_and_annihilator_rankMinorIdeal_eq_bot
        φ hrank hann

section Noetherian

variable [IsNoetherianRing R]

/-- Helper for Lemma 15.15.6: over a Noetherian local ring, trivial annihilator of an ideal is
equivalent to the owner depth inequality `1 ≤ depth`. -/
private theorem Ideal.annihilator_eq_bot_iff_one_le_depth (I : Ideal R) :
    I.annihilator = (⊥ : Ideal R) ↔ (1 : WithTop ℕ) ≤ I.depth R := by
  constructor
  · intro hann
    by_cases hI : I = ⊤
    · -- The unit ideal has depth at least `1` by the length-`1` source criterion.
      exact (Ideal.eq_top_or_exists_isRegular_iff_one_le_depth I).mp <| Or.inl hI
    · have havoid : ∀ 𝔮 ∈ associatedPrimes R R, ¬ I ≤ 𝔮 := by
        intro 𝔮 h𝔮 hI𝔮
        rcases
            (Ideal.isAssociatedToModule_iff_isAssociatedPrime R R 𝔮).mpr
              (AssociatedPrimes.mem_iff.mp h𝔮) with
          ⟨hprime, x, rfl⟩
        have hx_ann : x ∈ I.annihilator := by
          -- Any element of `I` lies in the exact annihilator `Ann_R(x)`, so `x` is killed by `I`.
          rw [Submodule.mem_annihilator]
          intro y hy
          simpa [Ideal.mem_torsionOf_iff, smul_eq_mul, mul_comm] using hI𝔮 hy
        have hx_zero : x = 0 := by
          have : x ∈ (⊥ : Ideal R) := by simpa [hann] using hx_ann
          simpa [Ideal.mem_bot] using this
        have htorsion_top : Ideal.torsionOf R R x = ⊤ := by
          ext y
          simp [hx_zero, Ideal.mem_torsionOf_iff]
        exact hprime.ne_top <| by simpa [htorsion_top]
      rcases
          (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes (R := R) (M := R)
            (I := I)).mpr havoid with
        ⟨x, hxI, hxsmul⟩
      have hxreg : IsRegular x := by
        refine ⟨hxsmul.isLeftRegular, ?_⟩
        simpa [IsRightRegular, IsSMulRegular, smul_eq_mul, mul_comm] using hxsmul
      -- Convert the regular-element witness back to the owner depth statement.
      exact (Ideal.eq_top_or_exists_isRegular_iff_one_le_depth I).mp <| Or.inr ⟨x, hxI, hxreg⟩
  · intro hdepth
    rcases (Ideal.eq_top_or_exists_isRegular_iff_one_le_depth I).mpr hdepth with
      hI | ⟨x, hxI, hxreg⟩
    · -- The annihilator of the unit ideal is always zero.
      have hann_top : (⊤ : Ideal R).annihilator = (⊥ : Ideal R) := by
        ext a
        constructor
        · intro ha
          rw [Ideal.mem_bot]
          simpa using (Submodule.mem_annihilator.mp ha) (1 : R) (by simp)
        · intro ha
          rw [Ideal.mem_bot] at ha
          simpa [ha] using (show (0 : R) ∈ (⊤ : Ideal R).annihilator from zero_mem _)
      simpa [hI] using hann_top
    · -- A nonzerodivisor inside `I` forces every annihilator element to vanish.
      ext a
      constructor
      · intro ha
        have hax : a * x = 0 := (Submodule.mem_annihilator.mp ha) x hxI
        have hxa : x * a = 0 := by simpa [mul_comm] using hax
        have ha0 : a = 0 := hxreg.left <| by simpa using hxa
        rw [Ideal.mem_bot]
        exact ha0
      · intro ha
        rw [Ideal.mem_bot] at ha
        simpa [ha] using (show (0 : R) ∈ I.annihilator from zero_mem _)

/-- Helper for Lemma 15.15.6: the two-term chain complex attached to `φ` has its single
nonzero differential in degrees `1 → 0`. -/
private abbrev two_term_rel : (ComplexShape.down ℕ).Rel 1 0 := rfl

/-- Helper for Lemma 15.15.6: the double complex model of `φ` is zero in degrees above `1`. -/
private lemma two_term_complex_isZero_toChainComplex_X
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    ∀ i : ℕ, 1 < i →
      IsZero ((HomologicalComplex.double (ModuleCat.ofHom φ) two_term_rel).X i)
  | i, hi => by
      have hi0 : i ≠ 0 := by omega
      have hi1 : i ≠ 1 := by omega
      simpa [two_term_rel] using
        (HomologicalComplex.isZero_double_X (ModuleCat.ofHom φ) two_term_rel i hi1 hi0)

/-- Helper for Lemma 15.15.6: the degree-`0` term of the two-term complex is the target
`R^n`. -/
private noncomputable def two_term_degree_zero_iso
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (HomologicalComplex.double (ModuleCat.ofHom φ) two_term_rel).X 0 ≅
      ModuleCat.of R (Fin n → R) :=
  doubleXIso₁ (ModuleCat.ofHom φ) two_term_rel (Nat.succ_ne_zero 0)

/-- Helper for Lemma 15.15.6: the degree-`1` term of the two-term complex is the source
`R^m`. -/
private noncomputable def two_term_degree_one_iso
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (HomologicalComplex.double (ModuleCat.ofHom φ) two_term_rel).X 1 ≅
      ModuleCat.of R (Fin m → R) :=
  doubleXIso₀ (ModuleCat.ofHom φ) two_term_rel

/-- Helper for Lemma 15.15.6: the Buchsbaum-Eisenbud owner theorem is applied to the finite free
complex with terms `R^m` in degree `1`, `R^n` in degree `0`, and differential `φ`. -/
private noncomputable def two_term_complex
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) : FiniteFreeComplex R 1 where
  toChainComplex := HomologicalComplex.double (ModuleCat.ofHom φ) two_term_rel
  isZero_toChainComplex_X := two_term_complex_isZero_toChainComplex_X (φ := φ)
  rank
    | ⟨0, _⟩ => n
    | ⟨1, _⟩ => m
  termIso
    | ⟨0, _⟩ => two_term_degree_zero_iso (φ := φ)
    | ⟨1, _⟩ => two_term_degree_one_iso (φ := φ)

/-- Helper for Lemma 15.15.6: the displayed differential of the two-term finite free complex is
exactly `φ`. -/
private lemma two_term_complex_differential_eq
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (two_term_degree_one_iso φ).inv ≫
        (HomologicalComplex.double (ModuleCat.ofHom φ) two_term_rel).d 1 0 ≫
        (two_term_degree_zero_iso φ).hom =
      ModuleCat.ofHom φ := by
  -- The `double` owner differential is the unique map placed in degree `1 → 0`.
  simp [two_term_degree_zero_iso, two_term_degree_one_iso, HomologicalComplex.double_d]

/-- Helper for Lemma 15.15.6: the displayed differential of the two-term finite free complex is
exactly `φ`. -/
private lemma two_term_complex_diffAt_zero
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (two_term_complex φ).diffAt ⟨0, by decide⟩ = φ := by
  -- The chosen coordinate identifications were built from the `double` owner isomorphisms.
  simpa [two_term_complex, FiniteFreeComplex.diffAt, FiniteFreeComplex.differential] using
    congrArg ModuleCat.Hom.hom (two_term_complex_differential_eq (φ := φ))

/-- Helper for Lemma 15.15.6: the alternating rank at the unique positive degree of the two-term
complex is the source rank `m`. -/
private lemma two_term_complex_alternatingRank_zero
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (two_term_complex φ).alternatingRank ⟨0, by decide⟩ = (m : ℤ) := by
  -- Only the rank in degree `1` contributes to the singleton alternating sum.
  change List.alternatingSum [((two_term_complex φ).rank ⟨1, by decide⟩ : ℤ)] = (m : ℤ)
  simp [two_term_complex]

/-- Helper for Lemma 15.15.6: exactness in the unique positive degree of the two-term complex is
equivalent to injectivity of `φ`. -/
private lemma two_term_complex_exactInPositiveDegrees_iff_injective
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    (two_term_complex φ).ExactInPositiveDegrees ↔ Function.Injective φ := by
  let C := two_term_complex φ
  constructor
  · intro hExact
    -- Read the unique positive-degree Buchsbaum-Eisenbud condition back on `φ`.
    rcases
        (FiniteFreeComplex.exactInPositiveDegrees_iff_buchsbaumEisenbud_depth_criterion C).mp
          hExact
          ⟨0, by decide⟩ with
      ⟨hrank, hdepth⟩
    have hrankφ : exteriorRank φ = m := by
      rw [two_term_complex_diffAt_zero (φ := φ),
        two_term_complex_alternatingRank_zero (φ := φ)] at hrank
      exact Int.ofNat.inj hrank
    have hannφ : (I(φ)).annihilator = (⊥ : Ideal R) := by
      have hdepthφ : (1 : WithTop ℕ) ≤ (I(φ)).depth R := by
        rwa [two_term_complex_diffAt_zero (φ := φ)] at hdepth
      exact (Ideal.annihilator_eq_bot_iff_one_le_depth (R := R) (I := I(φ))).mpr hdepthφ
    -- The earlier non-Noetherian criterion now closes injectivity directly.
    exact
      (injective_iff_exteriorRank_eq_and_annihilator_rankMinorIdeal_eq_bot (φ := φ)).mpr
        ⟨hrankφ, hannφ⟩
  · intro hφ
    rcases
        (injective_iff_exteriorRank_eq_and_annihilator_rankMinorIdeal_eq_bot (φ := φ)).mp hφ with
      ⟨hrankφ, hannφ⟩
    have hrankφ' : (exteriorRank φ : ℤ) = (m : ℤ) := by
      exact_mod_cast hrankφ
    have hdepthφ : (1 : WithTop ℕ) ≤ (I(φ)).depth R := by
      exact (Ideal.annihilator_eq_bot_iff_one_le_depth (R := R) (I := I(φ))).mp hannφ
    -- Repackage those two owner invariants into exactness of the two-term complex.
    refine
      (FiniteFreeComplex.exactInPositiveDegrees_iff_buchsbaumEisenbud_depth_criterion C).mpr ?_
    intro i
    obtain ⟨i, hi⟩ := i
    have hi0 : i = 0 := by omega
    subst hi0
    constructor
    · rw [two_term_complex_diffAt_zero (φ := φ),
        two_term_complex_alternatingRank_zero (φ := φ)]
      exact hrankφ'
    · rw [two_term_complex_diffAt_zero (φ := φ)]
      exact hdepthφ

-- Proof sketch: this is the `i = 0` depth form of the Chapter 10 Buchsbaum--Eisenbud owner
-- specialized to the two-term complex attached to `φ`, where `1 ≤ depth I(φ)` is the canonical
-- owner-side replacement for the length-`1` regular-sequence clause.
/-- Companion owner-style reformulation: over a Noetherian local ring, injectivity is equivalently
detected by full exterior rank together with positive depth of the rank-minor ideal. -/
theorem injective_iff_exteriorRank_eq_and_one_le_depth_rankMinorIdeal
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      exteriorRank φ = m ∧
        (1 : WithTop ℕ) ≤ (I(φ)).depth R := by
  rw [injective_iff_exteriorRank_eq_and_annihilator_rankMinorIdeal_eq_bot]
  constructor
  · rintro ⟨hrank, hann⟩
    refine ⟨hrank, ?_⟩
    exact (Ideal.annihilator_eq_bot_iff_one_le_depth (R := R) (I := I(φ))).mp hann
  · rintro ⟨hrank, hdepth⟩
    refine ⟨hrank, ?_⟩
    exact (Ideal.annihilator_eq_bot_iff_one_le_depth (R := R) (I := I(φ))).mpr hdepth

-- Proof sketch: combine the owner-style depth criterion above with the Noetherian local bridge
-- identifying positive depth with either `I(φ) = ⊤` or the presence of a regular element in
-- `I(φ)`.
/-- In a Noetherian local ring, injectivity is equivalently detected by full exterior rank together
with the rank-minor ideal being the unit ideal or containing a nonzerodivisor. -/
theorem injective_iff_exteriorRank_eq_and_rankMinorIdeal_eq_top_or_exists_isRegular
    (φ : (Fin m → R) →ₗ[R] (Fin n → R)) :
    Function.Injective φ ↔
      exteriorRank φ = m ∧
        (I(φ) = ⊤ ∨ ∃ x ∈ I(φ), IsRegular x) := by
  rw [injective_iff_exteriorRank_eq_and_one_le_depth_rankMinorIdeal]
  rw [Ideal.eq_top_or_exists_isRegular_iff_one_le_depth]

end Noetherian

end

end LinearMap
