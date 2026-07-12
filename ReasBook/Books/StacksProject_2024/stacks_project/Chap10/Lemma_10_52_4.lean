import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section Length

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] [IsLocalRing R]

/- Domain triage:
- primary domain: finite-length modules over a local ring, with the owner abstractions
  `IsFiniteLength R M`, `IsArtinian R M`, the canonical ideal `maximalIdeal R`, and Nakayama's
  lemma for finitely generated submodules;
- primitive data: the local ring `R`, the module `M`, and the finite-length hypothesis `hM`;
- derived API: the descending chain `((maximalIdeal R)^n) • ⊤` and the eventual vanishing claim. -/

-- Proof sketch: finite module length implies that `M` is Artinian, so the descending chain
-- `⊤ ≥ maximalIdeal R • ⊤ ≥ (maximalIdeal R)^2 • ⊤ ≥ ⋯` stabilizes. If the stable term were
-- nonzero, Nakayama's lemma over the local ring `R` would force it to vanish, a contradiction.
/-- Lemma 10.52.4: if an `R`-module over a local ring has finite length, then some power of the
maximal ideal annihilates it. -/
theorem exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength
    (hM : IsFiniteLength R M) :
    ∃ n : ℕ, ((maximalIdeal R) ^ n) • (⊤ : Submodule R M) = ⊥ := by
  obtain ⟨hNoeth, hArt⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  haveI : IsNoetherian R M := hNoeth
  haveI : IsArtinian R M := hArt
  let powers : ℕ →o (Submodule R M)ᵒᵈ :=
    ⟨fun n ↦ (((maximalIdeal R) ^ n) • (⊤ : Submodule R M) : Submodule R M), fun _ _ h ↦
      Submodule.pow_smul_top_le (maximalIdeal R) M h⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes powers
  have hEq : ((maximalIdeal R) ^ n : Ideal R) • (⊤ : Submodule R M) =
      maximalIdeal R • (((maximalIdeal R) ^ n : Ideal R) • (⊤ : Submodule R M)) := by
    calc
      ((maximalIdeal R) ^ n : Ideal R) • (⊤ : Submodule R M) =
          ((maximalIdeal R) ^ (n + 1) : Ideal R) • (⊤ : Submodule R M) := by
            simpa using hn (n + 1) n.le_succ
      _ = maximalIdeal R • (((maximalIdeal R) ^ n : Ideal R) • (⊤ : Submodule R M)) := by
            rw [pow_succ', mul_smul]
  refine ⟨n, ?_⟩
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) _
    (IsNoetherian.noetherian _) hEq.le (IsLocalRing.maximalIdeal_le_jacobson _)

end Length
