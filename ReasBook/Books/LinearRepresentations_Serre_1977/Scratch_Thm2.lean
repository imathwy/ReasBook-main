import Mathlib

universe u

open Polynomial

/-!
# A local extension of a DVR carrying a primitive `m`-th root of unity

Given a discrete valuation ring `A` with residue characteristic `p` and `m` coprime to `p`,
we build a local ring extension `B ⊇ A` (with `A → B` injective, residue characteristic still `p`)
that contains a primitive `m`-th root of unity.

The construction: `C := AdjoinRoot (cyclotomic m A)` adjoins a root `ρ` of the `m`-th cyclotomic
polynomial; pick a maximal ideal `𝔮` of `C` lying over `maximalIdeal A`; localize
`B := Localization.AtPrime 𝔮`. The image of `ρ` in `B` is the desired primitive root: it is one in
the residue field (where the cyclotomic polynomial is separable since `p ∤ m`), so it has order
exactly `m`.
-/

namespace ScratchThm2

variable {A : Type u} [CommRing A] [IsDomain A]

/-- The degree of the `m`-th cyclotomic polynomial over a nontrivial commutative ring is nonzero
when `0 < m`. -/
theorem degree_cyclotomic_ne_zero (m : ℕ) (hm0 : 0 < m) :
    (Polynomial.cyclotomic m A).degree ≠ 0 := by
  rw [Polynomial.degree_cyclotomic m A]
  have h : 0 < Nat.totient m := Nat.totient_pos.mpr hm0
  have : (0 : WithBot ℕ) < (Nat.totient m : WithBot ℕ) := by exact_mod_cast h
  exact this.ne'

/-- The algebra map `A → AdjoinRoot (cyclotomic m A)` is injective. -/
theorem algebraMap_adjoinRoot_injective (m : ℕ) (hm0 : 0 < m) :
    Function.Injective (algebraMap A (AdjoinRoot (Polynomial.cyclotomic m A))) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.of.injective_of_degree_ne_zero (degree_cyclotomic_ne_zero m hm0)

end ScratchThm2

open ScratchThm2

/-- A discrete valuation ring with residue characteristic `p` admits a local ring extension `B`,
injective over `A`, with residue characteristic still `p`, containing a primitive `m`-th root of
unity (`m` coprime to `p`). -/
theorem exists_local_extension_with_primitiveRoot
    {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {p : ℕ} [Fact p.Prime] [CharP (IsLocalRing.ResidueField A) p]
    {m : ℕ} (hm : Nat.Coprime p m) (hm0 : 0 < m) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : Algebra A B),
      Function.Injective (algebraMap A B) ∧
      CharP (IsLocalRing.ResidueField B) p ∧
      ∃ ζ : B, IsPrimitiveRoot ζ m := by
  classical
  -- The cyclotomic polynomial and its monicity.
  set f : A[X] := Polynomial.cyclotomic m A with hf
  have hfmonic : f.Monic := Polynomial.cyclotomic.monic m A
  -- `C := AdjoinRoot f`, with its root `ρ`.
  set C : Type u := AdjoinRoot f with hC
  set ρ : C := AdjoinRoot.root f with hρ
  -- `C` is module-finite (hence integral) and free over `A`.
  haveI : Module.Finite A C := hfmonic.finite_adjoinRoot
  haveI : Module.Free A C := hfmonic.free_adjoinRoot
  haveI : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  -- `A → C` is injective.
  have hAC_inj : Function.Injective (algebraMap A C) :=
    algebraMap_adjoinRoot_injective m hm0
  -- `ρ ^ m = 1` : `f ∣ X ^ m - 1` and `ρ` is a root of `f`.
  have hρpow : ρ ^ m = 1 := by
    have hdvd : f ∣ (X ^ m - 1 : A[X]) := Polynomial.cyclotomic.dvd_X_pow_sub_one m A
    obtain ⟨g, hg⟩ := hdvd
    -- evaluate `X^m - 1` at `ρ` via the structure map; it vanishes since `f(ρ) = 0`.
    have hfρ : f.eval₂ (AdjoinRoot.of f) ρ = 0 := AdjoinRoot.eval₂_root f
    have heval : (X ^ m - 1 : A[X]).eval₂ (AdjoinRoot.of f) ρ = 0 := by
      rw [hg, Polynomial.eval₂_mul, hfρ, zero_mul]
    -- compute the evaluation of `X^m - 1`.
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one]
      at heval
    rw [sub_eq_zero] at heval
    exact heval
  -- Choose a maximal ideal `𝔮` of `C` over `maximalIdeal A`.
  have hker : RingHom.ker (algebraMap A C) ≤ IsLocalRing.maximalIdeal A := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hAC_inj]
    exact bot_le
  haveI : (IsLocalRing.maximalIdeal A).IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  obtain ⟨𝔮, h𝔮max, h𝔮comap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral
      (IsLocalRing.maximalIdeal A) hker
  haveI : 𝔮.IsMaximal := h𝔮max
  haveI : 𝔮.IsPrime := h𝔮max.isPrime
  -- `B := Localization.AtPrime 𝔮`.
  set B : Type u := Localization.AtPrime 𝔮 with hB
  haveI : IsLocalRing B := inferInstanceAs (IsLocalRing (Localization.AtPrime 𝔮))
  -- `B` is an `A`-algebra via the composite `A → C → B`.
  letI algAB : Algebra A B :=
    ((algebraMap C B).comp (algebraMap A C)).toAlgebra
  have hAB_eq : (algebraMap A B) = (algebraMap C B).comp (algebraMap A C) :=
    RingHom.algebraMap_toAlgebra _
  refine ⟨B, inferInstance, inferInstance, algAB, ?_, ?_, ?_⟩
  · -- Injectivity of `A → B`.
    intro a b hab
    -- reduce to `a' := a - b` mapping to `0`.
    rw [← sub_eq_zero] at hab ⊢
    rw [← map_sub] at hab
    set a' : A := a - b with ha'
    -- `algebraMap A B a' = algebraMap C B (algebraMap A C a') = 0`.
    have h0 : (algebraMap C B) (algebraMap A C a') = 0 := by
      rw [← RingHom.comp_apply, ← hAB_eq]; exact hab
    -- localization: there is `t ∈ 𝔮.primeCompl` with `t * (algebraMap A C a') = 0`.
    rw [IsLocalization.map_eq_zero_iff 𝔮.primeCompl] at h0
    obtain ⟨t, ht⟩ := h0
    -- `(t : C) * (algebraMap A C a') = a' • (t : C)`.
    have hsmul : a' • (t : C) = 0 := by
      have : (↑t : C) * (algebraMap A C a') = a' • (↑t : C) := by
        rw [Algebra.smul_def, mul_comm]
      rw [← this, ht]
    -- `t ≠ 0` since `t ∉ 𝔮` and `0 ∈ 𝔮`.
    have ht0 : (↑t : C) ≠ 0 := by
      intro h
      exact t.2 (h ▸ 𝔮.zero_mem)
    -- torsion-free: `a' • t = 0 → a' = 0`.
    rcases smul_eq_zero.mp hsmul with h | h
    · exact h
    · exact absurd h ht0
  · -- Residue characteristic `p` is preserved.
    -- `algebraMap A B` is a local hom because `(maximalIdeal B).comap = maximalIdeal A`.
    have hlocalhom : IsLocalHom (algebraMap A B) := by
      refine ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 3 0).mp ?_
      intro x hx
      rw [Ideal.mem_comap]
      -- `(maximalIdeal B).comap (algebraMap C B) = 𝔮`.
      have hcomapCB : (IsLocalRing.maximalIdeal B).comap (algebraMap C B) = 𝔮 :=
        IsLocalization.AtPrime.comap_maximalIdeal B 𝔮
      -- pull `x ∈ maximalIdeal A` into `𝔮` then up.
      have hx𝔮 : (algebraMap A C) x ∈ 𝔮 := by
        rw [← h𝔮comap] at hx
        exact hx
      have : (algebraMap C B) ((algebraMap A C) x) ∈ IsLocalRing.maximalIdeal B := by
        rw [← Ideal.mem_comap, hcomapCB]; exact hx𝔮
      rwa [hAB_eq, RingHom.comp_apply]
    haveI := hlocalhom
    -- the induced residue-field map is a field hom, hence injective; transfer `CharP`.
    have hinj : Function.Injective (IsLocalRing.ResidueField.map (algebraMap A B)) :=
      RingHom.injective _
    exact charP_of_injective_ringHom hinj p
  · -- The primitive root: image of `ρ` in `B`.
    set ζ : B := (algebraMap C B) ρ with hζ
    -- `ζ ^ m = 1`.
    have hζpow : ζ ^ m = 1 := by
      rw [hζ, ← map_pow, hρpow, map_one]
    -- `orderOf ζ ∣ m`.
    have hdvd1 : orderOf ζ ∣ m := orderOf_dvd_of_pow_eq_one hζpow
    -- Push to the residue field `κ := ResidueField B`.
    set κ : Type u := IsLocalRing.ResidueField B with hκ
    haveI : CharP κ p := by
      -- redo the CharP transfer to have it available here.
      have hlocalhom : IsLocalHom (algebraMap A B) := by
        refine ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 3 0).mp ?_
        intro x hx
        rw [Ideal.mem_comap]
        have hcomapCB : (IsLocalRing.maximalIdeal B).comap (algebraMap C B) = 𝔮 :=
          IsLocalization.AtPrime.comap_maximalIdeal B 𝔮
        have hx𝔮 : (algebraMap A C) x ∈ 𝔮 := by
          rw [← h𝔮comap] at hx; exact hx
        have : (algebraMap C B) ((algebraMap A C) x) ∈ IsLocalRing.maximalIdeal B := by
          rw [← Ideal.mem_comap, hcomapCB]; exact hx𝔮
        rwa [hAB_eq, RingHom.comp_apply]
      haveI := hlocalhom
      have hinj : Function.Injective (IsLocalRing.ResidueField.map (algebraMap A B)) :=
        RingHom.injective _
      exact charP_of_injective_ringHom hinj p
    set res : B →+* κ := IsLocalRing.residue B with hres
    set zbar : κ := res ζ with hζbar
    -- `p ∤ m`.
    have hpm : ¬ (p ∣ m) := by
      intro hdvd
      have hp1 : p ∣ 1 := hm ▸ Nat.dvd_gcd dvd_rfl hdvd
      have hp1' : p = 1 := Nat.eq_one_of_dvd_one hp1
      exact (Fact.out (p := p.Prime)).one_lt.ne' hp1'
    -- `(m : κ) ≠ 0`.
    haveI hNeZero : NeZero (m : κ) := by
      refine ⟨?_⟩
      rw [Ne, CharP.cast_eq_zero_iff κ p m]
      exact hpm
    -- `zbar` is a root of `cyclotomic m κ`, hence a primitive `m`-th root in `κ`.
    have hroot : (Polynomial.cyclotomic m κ).IsRoot zbar := by
      -- `cyclotomic m κ = (cyclotomic m A).map (algebraMap A κ)`.
      have hmap : Polynomial.cyclotomic m κ
          = (Polynomial.cyclotomic m A).map (algebraMap A κ) := by
        rw [Polynomial.map_cyclotomic]
      rw [Polynomial.IsRoot, hmap, Polynomial.eval_map]
      -- the structure map `A → C` is `AdjoinRoot.of f`.
      have hofeq : (algebraMap A C) = AdjoinRoot.of f := AdjoinRoot.algebraMap_eq f
      -- `algebraMap A κ = (res.comp (algebraMap C B)).comp (of f)`.
      have hAκ' : (algebraMap A κ) = (res.comp (algebraMap C B)).comp (AdjoinRoot.of f) := by
        have hAκ : (algebraMap A κ) = (res.comp ((algebraMap C B).comp (algebraMap A C))) := by
          rw [← hAB_eq]
          ext a
          simp only [RingHom.comp_apply, hres]
          rfl
        rw [hAκ, ← hofeq, ← RingHom.comp_assoc]
      -- `zbar = (res.comp (algebraMap C B)) ρ`.
      have hζbar' : zbar = (res.comp (algebraMap C B)) ρ := by
        rw [hζbar, hζ]; rfl
      -- evaluate using `hom_eval₂` to factor through `C`; then `f(ρ) = 0`.
      rw [hAκ', hζbar', ← Polynomial.hom_eval₂]
      show (res.comp (algebraMap C B)) (f.eval₂ (AdjoinRoot.of f) ρ) = 0
      rw [AdjoinRoot.eval₂_root f, map_zero]
    -- `zbar` is primitive of order `m`.
    have hprimbar : IsPrimitiveRoot zbar m :=
      (Polynomial.isRoot_cyclotomic_iff).mp hroot
    have hbarorder : orderOf zbar = m := hprimbar.eq_orderOf.symm
    -- `orderOf zbar ∣ orderOf ζ` via the monoid hom `res`.
    have hdvd2 : m ∣ orderOf ζ := by
      rw [← hbarorder, hζbar]
      exact orderOf_map_dvd (res.toMonoidHom) ζ
    -- conclude `orderOf ζ = m`, hence `IsPrimitiveRoot ζ m`.
    have horder : orderOf ζ = m := Nat.dvd_antisymm hdvd1 hdvd2
    exact ⟨ζ, IsPrimitiveRoot.iff_orderOf.mpr horder⟩
