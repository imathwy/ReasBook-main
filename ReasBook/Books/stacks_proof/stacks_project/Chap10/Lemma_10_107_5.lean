import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open LocalizedModule
open Algebra.TensorProduct
open CategoryTheory
open scoped TensorProduct

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

private theorem algHom_eq_of_forall_localizationAtPrime_isEpi
    (h :
      ∀ p : PrimeSpectrum R,
        Algebra.IsEpi (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] S))
    {T : Type*} [CommRing T] [Algebra R T] (f g : S →ₐ[R] T) :
    f = g := by
  ext s
  apply sub_eq_zero.mp
  refine Module.eq_zero_of_localization_maximal
    (fun P _ ↦ LocalizedModule.AtPrime P T)
    (fun P _ ↦
      (LocalizedModule.mkLinearMap P.primeCompl T : T →ₗ[R] LocalizedModule.AtPrime P T))
    (f s - g s)
    fun P _ ↦ ?_
  let A := Localization.AtPrime P
  let B := A ⊗[R] S
  let C := A ⊗[R] T
  let fA : B →ₐ[A] C :=
    { toRingHom := Algebra.TensorProduct.map (AlgHom.id R A) f
      commutes' := by
        intro a
        change (Algebra.TensorProduct.map (AlgHom.id R A) f) (a ⊗ₜ[R] (1 : S)) = a ⊗ₜ[R] (1 : T)
        simp }
  let gA : B →ₐ[A] C :=
    { toRingHom := Algebra.TensorProduct.map (AlgHom.id R A) g
      commutes' := by
        intro a
        change (Algebra.TensorProduct.map (AlgHom.id R A) g) (a ⊗ₜ[R] (1 : S)) = a ⊗ₜ[R] (1 : T)
        simp }
  have hs : fA (1 ⊗ₜ[R] s) = gA (1 ⊗ₜ[R] s) := by
    letI : Algebra.IsEpi A B := h ⟨P, inferInstance⟩
    have hB :
        (1 : B) ⊗ₜ[A] (1 ⊗ₜ[R] s) = (1 ⊗ₜ[R] s) ⊗ₜ[A] (1 : B) :=
      (Algebra.isEpi_iff_forall_one_tmul_eq A B).mp inferInstance (1 ⊗ₜ[R] s)
    have :=
      congr(Algebra.TensorProduct.lift fA gA (fun _ _ ↦ .all _ _) $hB)
    simpa [fA, gA, A, B, C] using this.symm
  have hs_map :
      (Algebra.TensorProduct.map (AlgHom.id R A) f) (1 ⊗ₜ[R] s) =
        (Algebra.TensorProduct.map (AlgHom.id R A) g) (1 ⊗ₜ[R] s) := by
    simpa [fA, gA] using hs
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul] at hs_map
  have hmk :
      LocalizedModule.mkLinearMap P.primeCompl T (f s) =
        LocalizedModule.mkLinearMap P.primeCompl T (g s) := by
    apply (equivTensorProduct P.primeCompl T).injective
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply]
    rw [LocalizedModule.equivTensorProduct_apply_mk, LocalizedModule.equivTensorProduct_apply_mk]
    rw [Localization.mk_one_eq_algebraMap]
    simpa using hs_map
  simpa [map_sub] using sub_eq_zero.mpr hmk

/-- Lemma 10.107.5: a ring map `R → S` is an epimorphism if and only if, for every prime ideal
`𝔭` of `R`, the localized map `R_𝔭 → S_𝔭` is an epimorphism. Here `S_𝔭` is expressed canonically
as the base change `Localization.AtPrime p.asIdeal ⊗[R] S`. -/
-- Proof sketch: if `R → S` is an epimorphism, base change along `R → R_𝔭` preserves epimorphisms,
-- using the tensor-product description of localization. Conversely, if every localized map is an
-- epimorphism, compare any two `R`-algebra maps out of `S`; their localizations agree for every
-- prime of `R`, hence they are equal by the local criterion detected on all prime localizations.
@[stacks 04VS]
lemma algebra_isEpi_iff_forall_localizationAtPrime :
    Algebra.IsEpi R S ↔
      ∀ p : PrimeSpectrum R,
        Algebra.IsEpi (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] S) := by
  constructor
  · intro h p
    letI : Algebra.IsEpi R S := h
    letI : Epi (CommRingCat.ofHom (algebraMap R S)) :=
      (CommRingCat.epi_iff_epi).2 inferInstance
    exact (CommRingCat.epi_iff_epi).1 <| by
      simpa using
        (CommRingCat.isPushout_tensorProduct R (Localization.AtPrime p.asIdeal) S).epi_inl_of_epi
  · intro h
    refine (Algebra.isEpi_iff_forall_one_tmul_eq R S).mpr fun s ↦ ?_
    simpa using
      (congrArg (fun φ : S →ₐ[R] S ⊗[R] S ↦ φ s) <|
        algHom_eq_of_forall_localizationAtPrime_isEpi h includeLeft includeRight).symm

end
