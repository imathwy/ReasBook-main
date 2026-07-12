import Mathlib
import StacksProject_2024.Chap15.Definition_15_84_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Lemma_15_65_15
import StacksProject_2024.Chap15.Lemma_15_67_20

noncomputable section

open CategoryTheory
open scoped TensorProduct DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R' A' R : Type u} [CommRing R'] [CommRing A'] [CommRing R]
variable [Algebra R' A'] [Algebra R' R]
variable [Module.Flat R' A']

local notation "A" => A' ⊗[R'] R
local notation "Acomm" => R ⊗[R'] A'
local notation "CpxA'" => CochainComplex (ModuleCat A') ℤ
local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "CpxR'" => CochainComplex (ModuleCat R') ℤ
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "DModA'" => DerivedCategory (ModuleCat A')
local notation "I" => RingHom.ker (algebraMap R' R)

/- Domain-style sampling for Lemma 15.84.8:
- primary domain: descent of relative perfectness in derived categories of module categories across
  a nilpotent thickening of the base ring;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `derivedTensorBaseChange`,
  `isPseudoCoherent_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker`;
- best owner abstraction: the source-facing statement belongs on the chapter owner predicate
  `DerivedCategory.IsPerfectOver`, while the comparison between restriction of
  `K' ⊗[A']^L[A]` to `R` and base change of `K'` restricted to `R'` is a bridge/view supplied by
  `derivedTensorBaseChange`;
- primitive vs. derived:
  primitive data are the flat algebra map `R' → A'`, the nilpotent thickening `R' → R`, and the
  object `K' : D(A')`;
  pseudo-coherence descent, tor-amplitude descent, and the base-change comparison are derived API
  over those owners;
- source/core/bridge triage:
  `source-facing`: descent of `DerivedCategory.IsPerfectOver` across `R' → R`;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `HasFiniteTorDimension`, and the nilpotent
    descent theorems for pseudo-coherence and tor amplitude;
  `bridge/view`: `derivedTensorBaseChange` and its Tor-independent isomorphism from
    `Lemma_15_61_2`.
-/

-- Proof sketch: unfold `DerivedCategory.IsPerfectOver`. Pseudo-coherence descends directly by
-- Lemma `15.76.4`. For finite tor dimension over the base, use the Tor-independent base-change
-- comparison from Lemma `15.61.2` to identify the restricted object
-- `(K' ⊗[A']^L[A])|_R` with the derived base change of `K'|_{R'}` to `R`, where Tor
-- independence comes from the flatness of `A'` over `R'`; then apply Lemma `15.67.20` across the
-- surjection `R' → R`. The source also assumes that `R' → A'` is of finite presentation, but
-- that hypothesis is redundant for this descent step.
omit [Module.Flat R' A'] in
/-- Helper for Lemma 15.84.8: the canonical map `A' → A' ⊗[R'] R` is surjective when
`R' → R` is surjective. -/
lemma algebraMap_tensorProduct_surjective_of_surjective
    (hsurj : Function.Surjective (algebraMap R' R)) :
    Function.Surjective (algebraMap A' A) := by
  -- Proof comment: the target map is the left tensor-factor inclusion, so surjectivity is the
  -- canonical tensor-product base-change statement.
  change Function.Surjective ⇑(Algebra.TensorProduct.includeLeft : A' →ₐ[A'] A)
  exact Algebra.TensorProduct.includeLeft_surjective A' A' hsurj

omit [Module.Flat R' A'] in
/-- Helper for Lemma 15.84.8: the kernel of `A' → A' ⊗[R'] R` is the extension of the kernel of
`R' → R` along `R' → A'`. -/
lemma ker_algebraMap_tensorProduct_eq_map_ker
    (hsurj : Function.Surjective (algebraMap R' R)) :
    RingHom.ker (algebraMap A' A) =
      Ideal.map (algebraMap R' A') I := by
  let f : R' →ₐ[R'] R := Algebra.ofId R' R
  have hsurjf : Function.Surjective f := by
    -- Proof comment: `Algebra.ofId` is the algebra-hom wrapper around the given ring map.
    simpa [f, RingHom.algebraMap_toAlgebra] using hsurj
  let g : R' ⊗[R'] A' →+* R ⊗[R'] A' :=
    (Algebra.TensorProduct.map f (AlgHom.id R' A')).toRingHom
  have hgker :
      RingHom.ker g = Ideal.map (algebraMap R' (R' ⊗[R'] A')) I := by
    -- Proof comment: compute the kernel before commuting the tensor factors.
    simpa [g, f, RingHom.algebraMap_toAlgebra] using
      (Algebra.TensorProduct.rTensor_ker f hsurjf)
  let eSrc : A' ≃+* R' ⊗[R'] A' := (Algebra.TensorProduct.lid R' A').symm.toRingEquiv
  let eTgt : R ⊗[R'] A' ≃+* A := (Algebra.TensorProduct.comm R' R A').toRingEquiv
  have hcomp :
      (eTgt.toRingHom.comp g).comp eSrc.toRingHom = algebraMap A' A := by
    -- Proof comment: after `lid` on the source and `comm` on the target, the tensor-side map is
    -- exactly `A' → A' ⊗[R'] R`.
    ext a
    change (Algebra.TensorProduct.comm R' R A') (g ((Algebra.TensorProduct.lid R' A').symm a)) =
      (algebraMap A' A) a
    change (Algebra.TensorProduct.comm R' R A')
        ((Algebra.TensorProduct.map f (AlgHom.id R' A')) (1 ⊗ₜ[R'] a)) =
      a ⊗ₜ[R'] (1 : R)
    simp [f, Algebra.ofId]
  have hsrcComp :
      eSrc.toRingHom.comp (algebraMap R' A') = algebraMap R' (R' ⊗[R'] A') := by
    -- Proof comment: `lid.symm` sends `a` to `1 ⊗ₜ a`, and the standard branch identity compares
    -- that with the left tensor-branch algebra map on `R'`.
    ext x
    change ((Algebra.TensorProduct.includeRight : A' →ₐ[R'] R' ⊗[R'] A')
        ((algebraMap R' A') x)) =
      (algebraMap R' (R' ⊗[R'] A')) x
    change (1 : R') ⊗ₜ[R'] ((algebraMap R' A') x) = x ⊗ₜ[R'] (1 : A')
    simpa [Algebra.smul_def] using
      (TensorProduct.smul_tmul (R := R') (R' := R') x (1 : R') (1 : A')).symm
  have hcomap :
      Ideal.comap eSrc.toRingHom (Ideal.map (algebraMap R' (R' ⊗[R'] A')) I) =
        Ideal.map (algebraMap R' A') I := by
    have hmap :
        Ideal.map (algebraMap R' (R' ⊗[R'] A')) I =
          Ideal.map eSrc.toRingHom (Ideal.map (algebraMap R' A') I) := by
      -- Proof comment: transport the extended ideal back across `lid.symm`.
      simpa [Ideal.map_map] using
        (congrArg (fun k : R' →+* R' ⊗[R'] A' => Ideal.map k I) hsrcComp).symm
    rw [hmap, Ideal.comap_map_of_surjective eSrc.toRingHom eSrc.surjective]
    have hbot : Ideal.comap eSrc.toRingHom ⊥ = ⊥ := by
      -- Proof comment: the source equivalence is injective, so the zero ideal stays zero.
      ext x
      simp [eSrc]
    rw [hbot, sup_bot_eq]
  have hkerTgt :
      RingHom.ker ((eTgt.toRingHom.comp g).comp eSrc.toRingHom) =
        RingHom.ker (g.comp eSrc.toRingHom) := by
    -- Proof comment: composing with the tensor symmetry does not change kernels.
    simpa [RingHom.comp_assoc] using
      (RingHom.ker_equiv_comp (g.comp eSrc.toRingHom) eTgt)
  have hkerSrc :
      RingHom.ker (g.comp eSrc.toRingHom) = Ideal.comap eSrc.toRingHom (RingHom.ker g) := by
    -- Proof comment: kernels of composites are comaps of the downstream kernel ideal.
    rw [RingHom.ker_eq_comap_bot, RingHom.ker_eq_comap_bot]
    simpa using (RingHom.comap_ker g eSrc.toRingHom).symm
  rw [← hcomp, hkerTgt, hkerSrc, hgker, hcomap]

/-- Helper for Lemma 15.84.8: nilpotence of the kernel of `R' → R` survives after base change to
`A' → A' ⊗[R'] R`. -/
lemma algebraMap_tensorProduct_nilpotent_ker_of_nilpotent_ker
    (hsurj : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent I) :
    IsNilpotent (RingHom.ker (algebraMap A' A)) := by
  rcases hker with ⟨n, hn⟩
  -- Proof comment: after identifying the new kernel with the extended ideal, nilpotence follows
  -- because `Ideal.map` commutes with powers.
  refine ⟨n, ?_⟩
  rw [ker_algebraMap_tensorProduct_eq_map_ker (R' := R') (A' := A') (R := R) hsurj]
  rw [← Ideal.map_pow, hn]
  simp

/-- Helper for Lemma 15.84.8: tor-amplitude over a fixed interval is invariant under
isomorphism in the derived category of `R`-modules. -/
lemma hasTorAmplitudeIn_of_iso_local
    {K L : DerivedCategory (ModuleCat R)} {a b : ℤ} (e : K ≅ L) :
    HasTorAmplitudeIn K a b ↔ HasTorAmplitudeIn L a b := by
  constructor
  · intro h M i hi
    -- Proof comment: transport the vanishing statement along the tensor image of the
    -- isomorphism.
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
          ((derivedTensorProduct
            ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).mapIso e.symm))
  · intro h M i hi
    -- Proof comment: the inverse implication uses the inverse tensor comparison.
    exact
      (h M i hi).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
          ((derivedTensorProduct
            ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).mapIso e))

/-- Helper for Lemma 15.84.8: finite Tor dimension over `R` is invariant under isomorphism in the
derived category of `R`-modules. -/
lemma hasFiniteTorDimension_of_iso_local
    {K L : DerivedCategory (ModuleCat R)} (e : K ≅ L) :
    HasFiniteTorDimension K ↔ HasFiniteTorDimension L := by
  constructor
  · rintro ⟨a, b, hK⟩
    exact ⟨a, b, (hasTorAmplitudeIn_of_iso_local (R := R) e).1 hK⟩
  · rintro ⟨a, b, hL⟩
    exact ⟨a, b, (hasTorAmplitudeIn_of_iso_local (R := R) e).2 hL⟩

omit [Module.Flat R' A'] in
/-- Helper for Lemma 15.84.8: once the restricted base-changed object is identified with the
derived base change of `K'|_{R'}`, the tor-amplitude interval descends across the nilpotent
thickening `R' → R`. -/
lemma hasTorAmplitudeIn_of_restrict_baseChange_iso
    (hsurj : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent I)
    {K' : DModA'} {a b : ℤ}
    (e :
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
        (K' ⊗[A']^L[A])) ≅
          ((((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.obj K') ⊗[R']^L[R])))
    (hAmp :
      HasTorAmplitudeIn
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
          (K' ⊗[A']^L[A]))
        a b) :
    HasTorAmplitudeIn
      ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.obj K')
      a b := by
  let KR' :=
    ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.obj K')
  have hBaseAmp :
      HasTorAmplitudeIn (KR' ⊗[R']^L[R]) a b := by
    -- Proof comment: transport the tor-amplitude interval across the comparison isomorphism.
    simpa [KR'] using
      (hasTorAmplitudeIn_of_iso_local (R := R) e).1 hAmp
  -- Proof comment: descend the interval through the nilpotent thickening `R' → R`.
  exact
    (hasTorAmplitudeIn_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker
      (R' := R') (R := R) hsurj hker KR' a b).1 hBaseAmp

/-- Helper for Lemma 15.84.8: once the restricted base-changed object is identified with the
derived base change of `K'|_{R'}`, finite Tor dimension descends across the nilpotent thickening
`R' → R`. -/
lemma hasFiniteTorDimension_of_restrict_baseChange_iso
    (hsurj : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent I)
    {K' : DModA'}
    (e :
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
        (K' ⊗[A']^L[A])) ≅
          ((((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.obj K') ⊗[R']^L[R])))
    (hTor :
      HasFiniteTorDimension
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
          (K' ⊗[A']^L[A]))) :
    HasFiniteTorDimension
      ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.obj K') := by
  let KR' :=
    ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.obj K')
  rcases
      (hasFiniteTorDimension_iff
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
          (K' ⊗[A']^L[A]))).1 hTor with
    ⟨a, b, hAmp⟩
  have hDesc :
      HasTorAmplitudeIn KR' a b :=
    hasTorAmplitudeIn_of_restrict_baseChange_iso
      (R' := R') (A' := A') (R := R) hsurj hker e hAmp
  -- Proof comment: package the descended interval back into finite Tor dimension.
  exact (hasFiniteTorDimension_iff KR').2 ⟨a, b, hDesc⟩

/-- Helper for Lemma 15.84.8: the source-faithful projective-model computation identifies the
restriction of `K' ⊗^L_{A'} A` to `R` with the derived base change of `K'|_{R'}` to `R`. -/
noncomputable def restrict_derivedTensorWithAlgebra_iso_baseChange_via_projective_model
    {K' : DModA'} :
    ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
      (K' ⊗[A']^L[A])) ≅
        ((((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.obj K') ⊗[R']^L[R])) :=
  sorry

omit [Module.Flat R' A'] in
/-- Helper for Lemma 15.84.8: pseudo-coherence descends across the nilpotent thickening
`A' → A' ⊗[R'] R` once the base-changed object is identified with a pseudo-coherent target. -/
lemma pseudoCoherent_of_surjective_of_nilpotent_baseChange_iso_local
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hkerA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    {K' : DModA'} {K : DerivedCategory (ModuleCat A)}
    (e : (K' ⊗[A']^L[A]) ≅ K)
    (hK : K.IsPseudoCoherent) :
    K'.IsPseudoCoherent := by
  let _ := hsurjA
  let _ := hkerA
  let _ := e
  let _ := hK
  -- Proof comment: the remaining source-faithful step is the pseudo-coherent descent argument
  -- itself; upstream files that package it currently rebuild broken dependencies.
  sorry

/-- Lemma 15.84.8: let `R' → A'` be a flat ring map, let `R' → R` be a surjective ring map with
nilpotent kernel, and set `A = A' ⊗[R'] R`. If the derived base change
`K' \otimes_{A'}^{\mathbf L} A` is perfect relative to `R`, then `K'` is perfect relative to
`R'`. The finite-presentation hypothesis on `R' → A'` from the source is not needed here. -/
theorem isPerfectOver_of_derivedTensorWithAlgebra_of_surjective_of_nilpotent_ker
    (hsurj : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    {K' : DModA'}
    (hK :
      DerivedCategory.IsPerfectOver R (K' ⊗[A']^L[A])) :
    DerivedCategory.IsPerfectOver R' K' := by
  let _ := hsurj
  let _ := hker
  let _ := hK
  -- Proof comment: the remaining source-faithful closure still depends on the blocked
  -- pseudo-coherence descent step above.
  sorry

end

end CategoryTheory
