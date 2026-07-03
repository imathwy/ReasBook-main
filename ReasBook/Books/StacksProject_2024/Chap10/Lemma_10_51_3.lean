import Mathlib
import stacks_project.Chap10.Lemma_10_51_2_Artin_Rees

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open scoped Pointwise

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace LinearMap

/-- A fixed Artin-Rees bound for a linear map with respect to an ideal `I`. -/
def IsArtinReesBound (f : M →ₗ[R] N) (I : Ideal R) (c : ℕ) : Prop :=
  ∀ n ≥ c,
    f.range ⊓ I ^ n • ⊤ ≤ Submodule.map f (I ^ (n - c) • ⊤)

-- Proof sketch: if `y ∈ f(M) ∩ I^n N`, choose `x` with `f x = y`. Then
-- `x ∈ f ⁻¹(I^n N)`, so the preimage equality writes `x = k + x'` with
-- `k ∈ ker f` and `x' ∈ I^(n - c) f ⁻¹(I^c N)`. Applying `f` kills `k`
-- and places `y = f x'` inside `f(I^(n - c) M)`.
/-- Any Artin-Rees equality for the preimages `f ⁻¹(I^n N)` yields an Artin-Rees bound for `f`. -/
theorem isArtinReesBound_of_preimage_pow_smul_eq
    (I : Ideal R) {f : M →ₗ[R] N} {c : ℕ}
    (hc : ∀ n ≥ c,
      Submodule.comap f (I ^ n • ⊤) =
        LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤)) :
    f.IsArtinReesBound I c := by
  intro n hn
  -- Map the source-side cutoff formula forward along `f`.
  calc
    f.range ⊓ I ^ n • (⊤ : Submodule R N) =
        Submodule.map f (Submodule.comap f (I ^ n • (⊤ : Submodule R N))) := by
      rw [Submodule.map_comap_eq]
    _ = Submodule.map f
          (LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N))) := by
      rw [hc n hn]
    _ = Submodule.map f
          (LinearMap.ker f) ⊔
            Submodule.map f
              (I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N))) := by
      rw [Submodule.map_sup]
    _ = Submodule.map f
          (I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N))) := by
      have hmap_ker : Submodule.map f (LinearMap.ker f) = ⊥ := by
        rw [← LinearMap.le_ker_iff_map]
      simp [hmap_ker]
    _ ≤ Submodule.map f (I ^ (n - c) • (⊤ : Submodule R M)) := by
      -- Then enlarge the cutoff submodule in the source to all of `M`.
      exact Submodule.map_mono (smul_mono_right _ le_top)

end LinearMap

namespace Ideal

/-- Helper for Lemma 10.51.3: an Artin-Rees cutoff on `f.range` pulls back to the corresponding
cutoff formula for the preimages of the powers of `I`. -/
lemma comap_pow_smul_eq_of_range_cutoff
    (I : Ideal R) {f : M →ₗ[R] N} {c n : ℕ}
    (hcut :
      I ^ n • (⊤ : Submodule R N) ⊓ f.range =
        I ^ (n - c) • (I ^ c • (⊤ : Submodule R N) ⊓ f.range)) :
    Submodule.comap f (I ^ n • (⊤ : Submodule R N)) =
      LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)) := by
  -- Rewrite the preimage as the pullback of its image in the range of `f`.
  calc
    Submodule.comap f (I ^ n • (⊤ : Submodule R N)) =
        Submodule.comap f
          (Submodule.map f (Submodule.comap f (I ^ n • (⊤ : Submodule R N)))) := by
      rw [Submodule.comap_map_eq_self (LinearMap.ker_le_comap f)]
    _ = Submodule.comap f (I ^ n • (⊤ : Submodule R N) ⊓ f.range) := by
      rw [Submodule.map_comap_eq, inf_comm]
    _ = Submodule.comap f (I ^ (n - c) • (I ^ c • (⊤ : Submodule R N) ⊓ f.range)) := by
      rw [hcut]
    _ = Submodule.comap f
          (I ^ (n - c) •
            Submodule.map f (Submodule.comap f (I ^ c • (⊤ : Submodule R N)))) := by
      rw [Submodule.map_comap_eq, inf_comm]
    _ = Submodule.comap f
          (Submodule.map f
            (I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)))) := by
      rw [← Submodule.map_smul'']
    _ = LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N)) := by
      simpa [sup_comm] using
        (Submodule.comap_map_eq f
          (I ^ (n - c) • Submodule.comap f (I ^ c • (⊤ : Submodule R N))))

-- Proof sketch: apply Lemma 10.51.2 to `f.range ≤ N`; this gives the inclusion
-- `f.range ⊓ I^n N ≤ I^(n - c) • f.range`. Pulling the powers of `I` back
-- along `f` gives the corresponding equality for `f ⁻¹(I^n N)`, and `Submodule.map_smul''`
-- identifies `I^(n - c) • f.range` with `f(I^(n - c) M)`.
/-- A linear map into a finite module over a Noetherian ring has an Artin-Rees constant for the
inverse images of the powers of `I`. -/
theorem exists_exact_preimage_pow_smul_eq [IsNoetherianRing R] [Module.Finite R N]
    (I : Ideal R) (f : M →ₗ[R] N) :
    ∃ c : ℕ, ∀ n ≥ c,
      Submodule.comap f (I ^ n • ⊤) =
        LinearMap.ker f ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤) := by
  obtain ⟨c, _hc_pos, hc⟩ := I.exists_pos_pow_inf_eq_pow_smul f.range
  refine ⟨c, ?_⟩
  intro n hn
  -- Apply Artin-Rees to the image submodule and pull the cutoff back along `f`.
  exact comap_pow_smul_eq_of_range_cutoff (I := I) (f := f) (c := c) (n := n) <| by
    simpa [inf_comm] using hc n hn

-- Proof sketch: specialize the owner theorem above to the exact sequence
-- `0 → K → M → N`, then rewrite `LinearMap.ker f` as `K` using exactness.
/-- Lemma 10.51.3: if `0 → K → M → N` is an exact sequence of finite modules over a Noetherian
ring and `I` is an ideal of `R`, then there is a single Artin-Rees constant controlling both the
preimages `f ⁻¹(I^n N)` and the intersections `f(M) ∩ I^n N`. -/
theorem exists_artin_rees_constant_of_exact [IsNoetherianRing R] [Module.Finite R N]
    (I : Ideal R) {K : Submodule R M} {f : M →ₗ[R] N}
    (h_exact : Function.Exact K.subtype f) :
    ∃ c : ℕ,
      (∀ n ≥ c,
        Submodule.comap f (I ^ n • ⊤) = K ⊔ I ^ (n - c) • Submodule.comap f (I ^ c • ⊤)) ∧
        f.IsArtinReesBound I c := by
  obtain ⟨c, hc⟩ := exists_exact_preimage_pow_smul_eq (I := I) (f := f)
  refine ⟨c, ?_⟩
  refine ⟨?_, LinearMap.isArtinReesBound_of_preimage_pow_smul_eq (I := I) (f := f) hc⟩
  intro n hn
  -- Exactness identifies the kernel term with the given submodule `K`.
  simpa [h_exact.linearMap_ker_eq, Submodule.range_subtype] using hc n hn

end Ideal

end
