import Mathlib
import StacksProject_2024.Chap10.Definition_10_32_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Smooth R S]

/-- Helper for Lemma 10.138.17: a finitely generated subideal of a locally nilpotent ideal is
nilpotent. -/
lemma isNilpotent_of_fg_le_of_isLocallyNilpotent {I J : Ideal A}
    (hJfg : J.FG) (hJI : J ≤ I) (hI : I.IsLocallyNilpotent) :
    IsNilpotent J := by
  -- Local nilpotence places every element of `J` in the nilradical.
  have hJnilrad : J ≤ nilradical A := by
    intro x hx
    exact (Ideal.isLocallyNilpotent_iff I).mp hI x (hJI hx)
  -- Finite generation upgrades elementwise nilpotence to nilpotence of the ideal.
  exact (Ideal.FG.isNilpotent_iff_le_nilradical hJfg).2 hJnilrad

/- Domain-style sampling:
- primary domain: infinitesimal lifting for smooth algebras across quotient maps by locally
  nilpotent ideals;
- sampled owner declarations: the chapter owner `Ideal.IsLocallyNilpotent`, together with
  mathlib's `Algebra.FormallySmooth.exists_lift` and the owner field
  `Algebra.Smooth.formallySmooth`;
- best owner abstraction: `Smooth R S` is the source-facing ambient owner, while local nilpotence
  should be expressed through `Ideal.IsLocallyNilpotent` rather than restating the containment
  `I ≤ nilradical A`.

Source/core/bridge triage:
- `source-facing`: the theorem below, which matches Lemma `10.138.17`;
- `core/canonical`: `Algebra.FormallySmooth.exists_lift`;
- `bridge/view`: the reduction from a locally nilpotent ideal to a nilpotent ideal inside a
  finite type subalgebra used in the proof sketch.
-/

-- Proof sketch: smoothness gives formal smoothness together with finite presentation. Descend the
-- given map `S → A ⧸ I` and finitely many chosen lifts of generators to a finite type
-- `ℤ`-subalgebra `A₀ ⊆ A`; then `I ∩ A₀` is nilpotent because `A₀` is Noetherian, so the
-- infinitesimal lifting theorem for formally smooth algebras applies to produce a lift into `A₀`,
-- hence into `A`.
/-- Lemma 10.138.17: if `R → S` is smooth and `I` is a locally nilpotent ideal of the
`R`-algebra `A`, then every commutative square
`S → A ⧸ I ← A` over `R` admits a lift `S → A`. In canonical form, the locally nilpotent
hypothesis is expressed by the chapter owner `I.IsLocallyNilpotent`. -/
@[stacks 07K4]
theorem smooth_exists_lift_of_quotient_by_locally_nilpotent
    (I : Ideal A) (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := by
  classical
  obtain ⟨n, φ, hφ, hkerφfg⟩ := Algebra.FinitePresentation.out (R := R) (A := S)
  let qI : A →ₐ[R] A ⧸ I := Ideal.Quotient.mkₐ R I
  -- Choose lifts in `A` of the images of the finitely many presentation variables.
  have hliftX : ∀ i : Fin n, ∃ a : A, qI a = f (φ (MvPolynomial.X i)) := by
    intro i
    exact Ideal.Quotient.mkₐ_surjective R I (f (φ (MvPolynomial.X i)))
  choose a ha using hliftX
  let ψ : MvPolynomial (Fin n) R →ₐ[R] A := MvPolynomial.aeval a
  have hqIψ : qI.comp ψ = f.comp φ := by
    -- The chosen lifts make the two maps agree on the polynomial generators.
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    simpa [qI, ψ] using ha i
  let J : Ideal A := (RingHom.ker φ.toRingHom).map ψ.toRingHom
  have hker_le_comap_I : RingHom.ker φ.toRingHom ≤ I.comap ψ.toRingHom := by
    intro p hp
    -- Relations of the presentation map into `I` because they vanish after quotienting by `I`.
    rw [RingHom.mem_ker] at hp
    have hp' : φ p = 0 := hp
    change ψ p ∈ I
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by
      simpa [qI, AlgHom.comp_apply, hp'] using AlgHom.congr_fun hqIψ p)
  have hJ_le_I : J ≤ I := by
    exact Ideal.map_le_iff_le_comap.mpr hker_le_comap_I
  have hJfg : J.FG := Ideal.FG.map hkerφfg ψ.toRingHom
  have hJnil : IsNilpotent J :=
    isNilpotent_of_fg_le_of_isLocallyNilpotent hJfg hJ_le_I hI
  let qJ : A →ₐ[R] A ⧸ J := Ideal.Quotient.mkₐ R J
  have hker_le_comap_J : RingHom.ker φ.toRingHom ≤ RingHom.ker ((qJ.comp ψ).toRingHom) := by
    intro p hp
    -- Modding out by the defect ideal kills the images of all presentation relations.
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem ψ.toRingHom hp)
  let g : S →ₐ[R] A ⧸ J := AlgHom.liftOfSurjective φ hφ (qJ.comp ψ) hker_le_comap_J
  have hg_comp : g.comp φ = qJ.comp ψ := by
    -- This is the defining descent property of `AlgHom.liftOfSurjective`.
    exact AlgHom.liftOfSurjective_comp φ hφ (qJ.comp ψ) hker_le_comap_J
  have hg_mod_I : (Ideal.Quotient.factorₐ R hJ_le_I).comp g = f := by
    -- After passing from `A ⧸ J` to `A ⧸ I`, the descended map is the original quotient map.
    apply AlgHom.ext
    intro s
    obtain ⟨p, rfl⟩ := hφ s
    exact AlgHom.congr_fun (by
      calc
        (((Ideal.Quotient.factorₐ R hJ_le_I).comp g).comp φ)
            = (Ideal.Quotient.factorₐ R hJ_le_I).comp (g.comp φ) := by
                rw [AlgHom.comp_assoc]
        _ = (Ideal.Quotient.factorₐ R hJ_le_I).comp (qJ.comp ψ) := by
              rw [hg_comp]
        _ = ((Ideal.Quotient.factorₐ R hJ_le_I).comp qJ).comp ψ := by
              rw [AlgHom.comp_assoc]
        _ = qI.comp ψ := by
              rw [Ideal.Quotient.factorₐ_comp_mk]
        _ = f.comp φ := hqIψ) p
  obtain ⟨f', hf'⟩ := FormallySmooth.exists_lift (R := R) (A := S) (B := A) J hJnil g
  refine ⟨f', ?_⟩
  -- The nilpotent lift over `A ⧸ J` also lifts the original map over `A ⧸ I`.
  calc
    qI.comp f' = ((Ideal.Quotient.factorₐ R hJ_le_I).comp qJ).comp f' := by
      rw [Ideal.Quotient.factorₐ_comp_mk]
    _ = (Ideal.Quotient.factorₐ R hJ_le_I).comp (qJ.comp f') := by
          rw [AlgHom.comp_assoc]
    _ = (Ideal.Quotient.factorₐ R hJ_le_I).comp g := by rw [hf']
    _ = f := hg_mod_I

end

end Algebra
