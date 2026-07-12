import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Noetherian.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Submodule

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable (S : Submonoid A)

local notation "Aₛ" => Localization S
local notation "Mₛ" => LocalizedModule S M

/-
Domain-style sampling:
- primary domain: commutative algebra of finite modules over a Noetherian ring, localized modules,
  and scalar-torsion submodules;
- sampled owner API:
  `Submodule.torsionBy`,
  `Submodule.mem_torsionBy_iff`,
  `Module.primaryComponent_principalIdeal_eq_fPowerTorsion`,
  `mem_fPowerTorsion_iff_localizedAway_eq_zero`,
  `isSMulRegular_iff_torsionBy_eq_bot`,
  `Module.Finite.quotient`;
- best owner abstraction: `Submodule.torsionBy`; the chapter's principal-power notation
  `M[f^n]`/`M[f^∞]` from Definition `15.89.1` is only a source-facing bridge to this owner, and
  the kernel-of-`LinearMap.lsmul` phrasing is only the low-level bridge/view;
- primitive data: the ambient ring/module, the localization `Localization S`, and the scalar `π`;
  the kernel of scalar multiplication is derived from the owner `Submodule.torsionBy`, so it
  should not remain the public surface.

Layer triage:
- `source-facing`: Ogoma's stabilization lemma itself;
- `core/canonical`: `Submodule.torsionBy`;
- `bridge/view`: `LinearMap.ker (LinearMap.lsmul ...)`.
-/

-- Proof sketch: Let `K = M[π]` and let `K'` be the preimage in `M` of
-- `(S⁻¹M)[π^2]`. The hypothesis says that `K'/K` localizes to zero. Since
-- `K'/K` is a finite `A`-module over a Noetherian ring, some `s ∈ S` annihilates `K'/K`,
-- and then the same denominator works after replacing `s` by any positive power.

/-- Helper for Lemma 16.10.1 (Ogoma): a finite module whose localization is trivial is
annihilated by a single denominator from the multiplicative set. -/
lemma exists_denominator_smul_eq_zero_of_localized_subsingleton
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hsub : Subsingleton (LocalizedModule S N)) :
    ∃ s : S, ∀ x : N, (s : A) • x = 0 := by
  classical
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' A N
  have hkill_basis :
      ∀ i : Fin n, ∃ s : S, (s : A) • g (Pi.basisFun A (Fin n) i) = 0 := by
    intro i
    rcases (LocalizedModule.subsingleton_iff (S := S) (M := N)).mp hsub
        (g (Pi.basisFun A (Fin n) i)) with ⟨s, hs, hzero⟩
    exact ⟨⟨s, hs⟩, hzero⟩
  choose s hs using hkill_basis
  let s0 : S := ∏ i, s i
  refine ⟨s0, ?_⟩
  intro x
  obtain ⟨y, rfl⟩ := hg x
  -- It suffices to check the scaled presentation map on the standard basis.
  have hmap : ((s0 : A) • g : (Fin n → A) →ₗ[A] N) = 0 := by
    apply (Pi.basisFun A (Fin n)).ext
    intro i
    have hdiv : (s i : A) ∣ (s0 : A) := by
      simpa [s0] using
        (Finset.dvd_prod_of_mem (fun j ↦ (s j : A)) (Finset.mem_univ i))
    rcases hdiv with ⟨c, hc⟩
    change (s0 : A) • g (Pi.basisFun A (Fin n) i) = 0
    have hc' : (s0 : A) = c * (s i : A) := by
      simpa [s0, mul_comm] using hc
    rw [hc', mul_smul, hs i, smul_zero]
  simpa [s0] using LinearMap.congr_fun hmap y

/-- Helper for Lemma 16.10.1 (Ogoma): the `A`-torsion submodule of the localized module agrees
with the `Aₛ`-torsion submodule obtained from the image of the scalar. -/
lemma localized_torsionBy_eq_restrictScalars (π : A) :
    torsionBy A Mₛ π = (torsionBy Aₛ Mₛ (algebraMap A Aₛ π)).restrictScalars A := by
  ext x
  change π • x = 0 ↔ (algebraMap A Aₛ π) • x = 0
  simp

/-- Helper for Lemma 16.10.1 (Ogoma): one denominator sends every element whose localization is
`π²`-torsion into the global `π`-torsion submodule. -/
lemma exists_common_denominator_for_local_square_torsion (π : A)
    (htors :
      torsionBy Aₛ Mₛ (algebraMap A Aₛ π) = torsionBy Aₛ Mₛ ((algebraMap A Aₛ π) ^ 2)) :
    ∃ s0 : S, ∀ x : M,
      x ∈ Submodule.comap (LocalizedModule.mkLinearMap S M) (torsionBy A Mₛ (π ^ 2)) →
        (s0 : A) • x ∈ torsionBy A M π := by
  let mkM : M →ₗ[A] Mₛ := LocalizedModule.mkLinearMap S M
  let K : Submodule A M := torsionBy A M π
  let K' : Submodule A M := Submodule.comap mkM (torsionBy A Mₛ (π ^ 2))
  have htorsA : torsionBy A Mₛ π = torsionBy A Mₛ (π ^ 2) := by
    calc
      torsionBy A Mₛ π = (torsionBy Aₛ Mₛ (algebraMap A Aₛ π)).restrictScalars A := by
        simpa using localized_torsionBy_eq_restrictScalars (S := S) (M := M) π
      _ = (torsionBy Aₛ Mₛ ((algebraMap A Aₛ π) ^ 2)).restrictScalars A := by
        simpa using congrArg (Submodule.restrictScalars A) htors
      _ = (torsionBy Aₛ Mₛ (algebraMap A Aₛ (π ^ 2))).restrictScalars A := by
        rw [show algebraMap A Aₛ (π ^ 2) = (algebraMap A Aₛ π) ^ 2 by simp]
      _ = torsionBy A Mₛ (π ^ 2) := by
        have hloc2 :=
          localized_torsionBy_eq_restrictScalars (S := S) (M := M) (π ^ 2)
        exact hloc2.symm
  have hK_le : K ≤ K' := by
    intro x hx
    rw [Submodule.mem_comap]
    rw [Submodule.mem_torsionBy_iff] at hx ⊢
    have hπ : mkM (π • x) = 0 := by
      simpa [mkM] using congrArg mkM hx
    calc
      (π ^ 2) • mkM x = π • (mkM (π • x)) := by
        simp [pow_two, smul_smul, mkM]
      _ = 0 := by rw [hπ, smul_zero]
  let K₀ : Submodule A K' := K.comap K'.subtype
  have hsub :
      Subsingleton (LocalizedModule S (K' ⧸ K₀)) := by
    rw [LocalizedModule.subsingleton_iff (S := S) (M := K' ⧸ K₀)]
    intro q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective K₀ q
    have hx' : (x : M) ∈ K' := x.property
    have hlocal_square :
        mkM (x : M) ∈ torsionBy A Mₛ (π ^ 2) := by
      change mkM (x : M) ∈ torsionBy A Mₛ (π ^ 2) at hx'
      exact hx'
    have hlocal : mkM (x : M) ∈ torsionBy A Mₛ π := by
      rw [htorsA]
      exact hlocal_square
    rw [Submodule.mem_torsionBy_iff] at hlocal
    have hmkpi : mkM (π • (x : M)) = 0 := by
      calc
        mkM (π • (x : M)) = π • mkM (x : M) := by simp [mkM]
        _ = 0 := hlocal
    obtain ⟨s, hsx⟩ := (IsLocalizedModule.eq_zero_iff (S := S) (f := mkM)).mp hmkpi
    have hs_mem_K : (s : A) • (x : M) ∈ K := by
      change π • ((s : A) • (x : M)) = 0
      calc
        π • ((s : A) • (x : M)) = (s : A) • (π • (x : M)) := by
          simp [smul_smul, mul_comm]
        _ = 0 := hsx
    have hs_mem_K₀ : ((s : A) • x : K') ∈ K₀ := by
      simpa [K₀] using hs_mem_K
    refine ⟨(s : A), s.2, ?_⟩
    change Submodule.mkQ K₀ (((s : A) • x : K')) = 0
    exact (Submodule.Quotient.mk_eq_zero K₀).2 hs_mem_K₀
  obtain ⟨s0, hs0⟩ :=
    exists_denominator_smul_eq_zero_of_localized_subsingleton
      (S := S) (A := A) (N := K' ⧸ K₀) hsub
  refine ⟨s0, ?_⟩
  intro x hx
  have hzero : (s0 : A) • Submodule.mkQ K₀ ⟨x, hx⟩ = 0 := by
    exact hs0 (Submodule.mkQ K₀ ⟨x, hx⟩)
  have hs_mem_K₀ : ((s0 : A) • (⟨x, hx⟩ : K') : K') ∈ K₀ := by
    change Submodule.mkQ K₀ (((s0 : A) • (⟨x, hx⟩ : K') : K')) = 0 at hzero
    exact (Submodule.Quotient.mk_eq_zero K₀).1 hzero
  simpa [K₀, K] using hs_mem_K₀

/-- Helper for Lemma 16.10.1 (Ogoma): if `((s0^m) * π)^2` kills `x`, then after localization the
element `π² • x` already vanishes. -/
lemma localized_pi_square_zero_of_scaled_square_zero (π : A) (s0 : S) (m : ℕ) {x : M}
    (hx : ((((s0 : A) ^ m) * π) ^ 2) • x = 0) :
    (LocalizedModule.mkLinearMap S M) ((π ^ 2) • x) = 0 := by
  let mkM : M →ₗ[A] Mₛ := LocalizedModule.mkLinearMap S M
  have hloc :
      (((s0 ^ (m * 2) : S) : A)) • mkM ((π ^ 2) • x) = 0 := by
    -- Rewrite the scaled square as one denominator factor times `π² • x`.
    simpa [mkM, pow_mul, pow_two, smul_smul, mul_assoc, mul_left_comm, mul_comm] using
      congrArg mkM hx
  exact
    LocalizedModule.eq_zero_of_smul_eq_zero
      (((s0 ^ (m * 2) : S) : A))
      (s0 ^ (m * 2)).2
      (mkM ((π ^ 2) • x))
      hloc

/-- Helper for Lemma 16.10.1 (Ogoma): the square-torsion stage for `((s0^m) * π)` is contained in
the next torsion stage. -/
lemma scaled_square_torsion_le_next (π : A) (s0 : S)
    (hs0 : ∀ x : M,
      x ∈ Submodule.comap (LocalizedModule.mkLinearMap S M) (torsionBy A Mₛ (π ^ 2)) →
        (s0 : A) • x ∈ torsionBy A M π) :
    ∀ m : ℕ,
      torsionBy A M ((((s0 : A) ^ m) * π) ^ 2) ≤
        torsionBy A M (((s0 : A) ^ (m + 1)) * π) := by
  intro m x hx
  rw [Submodule.mem_torsionBy_iff] at hx ⊢
  have hlocal :
      x ∈ Submodule.comap (LocalizedModule.mkLinearMap S M) (torsionBy A Mₛ (π ^ 2)) := by
    rw [Submodule.mem_comap]
    rw [Submodule.mem_torsionBy_iff]
    calc
      (π ^ 2) • (LocalizedModule.mkLinearMap S M x)
          = (LocalizedModule.mkLinearMap S M) ((π ^ 2) • x) := by
              simp [LocalizedModule.mkLinearMap]
      _ = 0 := localized_pi_square_zero_of_scaled_square_zero (S := S) π s0 m hx
  have hs_mem :
      (s0 : A) • x ∈ torsionBy A M π := hs0 x hlocal
  rw [Submodule.mem_torsionBy_iff] at hs_mem
  -- After one more multiplication by `(s0 : A)^m`, this is exactly the next torsion stage.
  simpa [pow_succ, smul_smul, mul_assoc, mul_left_comm, mul_comm] using
    congrArg (((s0 : A) ^ m) • ·) hs_mem

/-- Helper for Lemma 16.10.1 (Ogoma): once the torsion chain for `((s0^m) * π)` stabilizes, the
`s^n * π`-torsion agrees with its square-torsion for every positive power of a stabilizing
denominator. -/
lemma stable_power_torsion_eq_square (π : A) (s0 : S)
    (hsq : ∀ m : ℕ,
      torsionBy A M ((((s0 : A) ^ m) * π) ^ 2) ≤
        torsionBy A M (((s0 : A) ^ (m + 1)) * π)) :
    ∃ N : ℕ, ∀ n : ℕ+,
      torsionBy A M ((((s0 : A) ^ N) ^ (n : ℕ)) * π) =
        torsionBy A M ((((((s0 : A) ^ N) ^ (n : ℕ)) * π) ^ 2)) := by
  let F : ℕ →o Submodule A M :=
    { toFun := fun m ↦ torsionBy A M (((s0 : A) ^ m) * π)
      monotone' := by
        intro m k hmk
        exact
          Submodule.torsionBy_le_torsionBy_of_dvd
            (((s0 : A) ^ m) * π)
            (((s0 : A) ^ k) * π)
            (by
              simpa [mul_comm, mul_left_comm, mul_assoc] using
                mul_dvd_mul_right (pow_dvd_pow (s0 : A) hmk) π) }
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance F
  refine ⟨N, ?_⟩
  intro n
  let m : ℕ := N * (n : ℕ)
  have hm_ge : N ≤ m := by
    simpa [m] using Nat.le_mul_of_pos_right N n.pos
  have hm1_ge : N ≤ m + 1 := le_trans hm_ge (Nat.le_succ _)
  have hFm : F N = F m := hN m hm_ge
  have hFm1 : F N = F (m + 1) := hN (m + 1) hm1_ge
  have hstable : F m = F (m + 1) := hFm.symm.trans hFm1
  have hlower :
      F m ≤ torsionBy A M ((((s0 : A) ^ m) * π) ^ 2) := by
    exact
      Submodule.torsionBy_le_torsionBy_of_dvd
        (((s0 : A) ^ m) * π)
        ((((s0 : A) ^ m) * π) ^ 2)
        ⟨((s0 : A) ^ m) * π, by simp [pow_two, mul_assoc]⟩
  have hstage :
      torsionBy A M (((s0 : A) ^ m) * π) =
        torsionBy A M ((((s0 : A) ^ m) * π) ^ 2) := by
    apply le_antisymm
    · exact hlower
    · exact (hsq m).trans hstable.ge
  -- Re-express the stabilized index as a power of `((s0 : A) ^ N)`.
  simpa [F, m, pow_mul] using hstage

/-- Lemma 16.10.1 (Ogoma): if the `π`-torsion and `π^2`-torsion submodules of `S⁻¹M` agree, then
some `s ∈ S` makes the `s^n * π`-torsion and `(s^n * π)^2`-torsion submodules of `M` agree for
every positive integer `n`. -/
theorem exists_mem_submonoid_torsionBy_eq_of_localized (π : A)
    (htors :
      torsionBy Aₛ Mₛ (algebraMap A Aₛ π) = torsionBy Aₛ Mₛ ((algebraMap A Aₛ π) ^ 2)) :
    ∃ s : S, ∀ n : ℕ+,
      torsionBy A M (((s : A) ^ (n : ℕ)) * π) =
        torsionBy A M ((((s : A) ^ (n : ℕ)) * π) ^ 2) := by
  obtain ⟨s0, hs0⟩ :=
    exists_common_denominator_for_local_square_torsion (S := S) (M := M) π htors
  have hsq :
      ∀ m : ℕ,
        torsionBy A M ((((s0 : A) ^ m) * π) ^ 2) ≤
          torsionBy A M (((s0 : A) ^ (m + 1)) * π) :=
    scaled_square_torsion_le_next (S := S) (M := M) π s0 hs0
  obtain ⟨N, hN⟩ := stable_power_torsion_eq_square (S := S) (M := M) π s0 hsq
  refine ⟨s0 ^ N, ?_⟩
  intro n
  -- Repackage the stabilized power of `s0` as a single denominator in `S`.
  simpa using hN n

end
