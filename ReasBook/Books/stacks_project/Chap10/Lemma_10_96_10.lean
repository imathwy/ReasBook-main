import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open AdicCompletion Submodule

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (K : Submodule R M)
variable [IsPrecomplete I M]

-- Domain-style sampling:
-- * primary domain: adic completion / `I`-adic precompleteness and completeness of modules and
--   quotients.
-- * source-facing layer: the quotient criterion for `IsAdicComplete I (M ⧸ K)`.
-- * core/canonical owners: `IsPrecomplete I _` for surjectivity of the completion map, and
--   `IsAdicComplete I _` for the target quotient-completeness statement.
-- * sampled upstream declarations:
--   `IsPrecomplete`,
--   `IsAdicComplete`,
--   `AdicCompletion.of_surjective_iff`,
--   `isHausdorff_iff`,
--   `IsHausdorff.iInf_pow_smul`,
--   `Submodule.comap_map_mkQ`.
-- * primitive data: the quotient map `Submodule.mkQ K`.
-- * derived API: precompleteness of `M ⧸ K`, Hausdorffness of `M ⧸ K`, and the intersection
--   criterion transported through the quotient-submodule correspondence.
-- Proof sketch: apply Lemma `10.96.1` to the quotient map `M → M ⧸ K`. Since `M` is already
-- `I`-adically precomplete, surjectivity of the induced map `M^∧ → (M ⧸ K)^∧` is equivalent to
-- surjectivity of the completion map `(M ⧸ K) → (M ⧸ K)^∧`. The kernel of that completion map is
-- exactly `(⨅ n, K ⊔ I ^ n • ⊤) / K`, so bijectivity is equivalent to
-- `K = ⨅ n, K ⊔ I ^ n • (⊤ : Submodule R M)`.
/-- Lemma 10.96.10: if `M` is `I`-adically precomplete, then a submodule `K` is the intersection
of the submodules `K + I ^ n M` if and only if the quotient module `M ⧸ K` is `I`-adically
complete. -/
theorem submodule_eq_iInf_sup_pow_smul_top_iff_isAdicComplete_quotient :
    K = ⨅ n : ℕ, K ⊔ I ^ n • (⊤ : Submodule R M) ↔ IsAdicComplete I (M ⧸ K) := by
  have hquot_precomplete : IsPrecomplete I (M ⧸ K) := by
    rw [← AdicCompletion.of_surjective_iff]
    intro y
    obtain ⟨x, rfl⟩ := AdicCompletion.map_surjective I (Submodule.mkQ_surjective K) y
    obtain ⟨m, rfl⟩ := AdicCompletion.of_surjective I M x
    exact ⟨Submodule.mkQ K m, by rw [AdicCompletion.map_of]⟩
  have hcomap_pow (n : ℕ) :
      Submodule.comap (Submodule.mkQ K) (I ^ n • (⊤ : Submodule R (M ⧸ K))) =
        K ⊔ I ^ n • (⊤ : Submodule R M) := by
    have hmap : Submodule.map (Submodule.mkQ K) (I ^ n • (⊤ : Submodule R M)) =
        I ^ n • (⊤ : Submodule R (M ⧸ K)) := by
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    rw [← hmap, Submodule.comap_map_mkQ]
  constructor
  · intro hK
    rw [isAdicComplete_iff]
    refine ⟨?_, hquot_precomplete⟩
    rw [isHausdorff_iff]
    rintro ⟨m⟩ hm
    have hm_mem : ∀ n : ℕ, Submodule.mkQ K m ∈ I ^ n • (⊤ : Submodule R (M ⧸ K)) :=
      fun n ↦ SModEq.zero.1 (hm n)
    have hm' : m ∈ ⨅ n : ℕ, K ⊔ I ^ n • (⊤ : Submodule R M) := by
      rw [Submodule.mem_iInf]
      intro n
      rw [← hcomap_pow n, Submodule.mem_comap]
      exact hm_mem n
    have hmK : m ∈ K := by
      rw [hK]
      exact hm'
    change (Submodule.Quotient.mk m : M ⧸ K) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hmK
  · intro hquot
    have hhaus : IsHausdorff I (M ⧸ K) := hquot.toIsHausdorff
    have hbot : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R (M ⧸ K))) = ⊥ :=
      IsHausdorff.iInf_pow_smul hhaus
    have hcomap := congrArg (Submodule.comap (Submodule.mkQ K)) hbot
    rw [Submodule.comap_iInf] at hcomap
    simp only [Submodule.comap_bot, Submodule.ker_mkQ] at hcomap
    simpa [hcomap_pow] using hcomap.symm

end
