import Mathlib
import StacksProject_2024.Chap10.Lemma_10_82_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

/-
Layering for this item:
* primary domain: commutative algebra, specifically Nakayama-style statements for submodules,
  quotient maps, and localization away from one element;
* core/canonical owners sampled for this file:
  `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`,
  `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`,
  `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup`,
  `LinearMap.quotientMapByIdeal`;
* source-facing layer: the top/range/span specializations that match the numbered Stacks item;
* bridge/view layer: quotient-map surjectivity and away-localization conclusions.

Primitive data are the ideal, the relevant submodules, and the underlying linear map; the quotient
and localization statements are derived API built from those owner abstractions.
-/

section

open LinearMap
open LocalizedModule
open scoped Pointwise

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

section

variable (I : Ideal R)

local notation "IM" => I • (⊤ : Submodule R M)

private theorem le_jacobson_bot_of_le_ring_jacobson
    {I : Ideal R} (hIjac : I ≤ Ring.jacobson R) :
    I ≤ Ideal.jacobson (⊥ : Ideal R) := by
  simpa [Ideal.jacobson_bot] using hIjac

/-- Lemma 10.20.1 (Nakayama's lemma) (1): if `M` is finite and `IM = M`, then some element
`r ∈ 1 + I` annihilates `M`. -/
-- Proof sketch: apply `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` to the top
-- submodule of `M`, using `Module.Finite.fg_top` to obtain finite generation.
theorem exists_sub_one_mem_and_smul_eq_zero_of_ideal_smul_top_eq_top
    [Module.Finite R M] (hIM : IM = ⊤) :
    ∃ r : R, r - 1 ∈ I ∧ ∀ m : M, r • m = 0 := by
  simpa using
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I (⊤ : Submodule R M)
      Module.Finite.fg_top (by simp [hIM])

/-- Lemma 10.20.1 (Nakayama's lemma) (2): if `M` is finite, `IM = M`, and `I` lies in the
Jacobson radical of `R`, then `M` is the zero module. -/
-- Proof sketch: apply `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` to the top submodule of
-- `M`, using `Module.Finite.fg_top` and the hypothesis `I • ⊤ = ⊤`; then translate
-- `⊤ = ⊥` to `Subsingleton M` via `Submodule.subsingleton_iff`.
theorem subsingleton_of_ideal_smul_top_eq_top_of_le_ring_jacobson
    [Module.Finite R M] (hIM : IM = ⊤) (hIjac : I ≤ Ring.jacobson R) : Subsingleton M := by
  refine (Submodule.subsingleton_iff R).mp ?_
  refine subsingleton_of_bot_eq_top ?_
  symm
  have htop : (⊤ : Submodule R M) ≤ Ring.jacobson R • (⊤ : Submodule R M) := by
    exact hIM.ge.trans <| Submodule.smul_mono hIjac le_rfl
  exact Submodule.FG.eq_bot_of_le_jacobson_smul Module.Finite.fg_top htop

/-- Lemma 10.20.1 (Nakayama's lemma) (3): if `N ⊔ I • N' = M` and `N'` is finite, then some
`r ∈ 1 + I` satisfies `rM ⊆ N`, and localizing away from `r` makes `N` equal to the whole
localized module. -/
-- Proof sketch: apply `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup` with `P = ⊤`,
-- then use `Submodule.localized₀_le_localized₀_of_smul_le` and `Submodule.localized₀_top`.
theorem exists_sub_one_mem_and_smul_top_le_of_sup_eq_top
    (I : Ideal R) (N N' : Submodule R M) (hN' : N'.FG) (hMN : N ⊔ I • N' = ⊤) :
    ∃ r : R,
      r - 1 ∈ I ∧ r • (⊤ : Submodule R M) ≤ N ∧ N.localized (Submonoid.powers r) = ⊤ := by
  have hN'le : N' ≤ (⊤ : Submodule R M) := le_top
  have hsup : (⊤ : Submodule R M) ≤ N ⊔ I • N' := by rw [hMN]
  obtain ⟨r, hrI, hrN⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hN' hN'le hsup
  refine ⟨r, hrI, hrN, top_unique ?_⟩
  have hrpow : r ∈ Submonoid.powers r := ⟨1, by simp⟩
  have hlocalized :
      (⊤ : Submodule R M).localized (Submonoid.powers r) ≤
        N.localized (Submonoid.powers r) := by
    let x : Submonoid.powers r := ⟨r, hrpow⟩
    simpa [Submodule.localized] using
      (Submodule.localized'_le_localized'_of_smul_le
        (Localization (Submonoid.powers r))
        (Submonoid.powers r)
        (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
        x hrN)
  simpa using hlocalized

/-- Lemma 10.20.1 (Nakayama's lemma) (4): if `N ⊔ I • N' = M`, `N'` is finite, and `I` lies in
the Jacobson radical of `R`, then `N = M`. -/
-- Proof sketch: apply `Submodule.smul_le_of_le_smul_of_le_jacobson_bot` after rewriting
-- `hMN` as the inclusion `N' ≤ N ⊔ I • N'`, then conclude from `I • N' ≤ N`.
theorem eq_top_of_sup_eq_top_of_le_ring_jacobson
    (I : Ideal R) (N N' : Submodule R M) (hN' : N'.FG) (hMN : N ⊔ I • N' = ⊤)
    (hIjac : I ≤ Ring.jacobson R) :
    N = ⊤ := by
  have hsmul : I • N' ≤ N :=
    Submodule.smul_le_of_le_smul_of_le_jacobson_bot hN'
      (le_jacobson_bot_of_le_ring_jacobson hIjac) (hMN ▸ le_top)
  exact top_unique <| by
    simpa [hMN] using (sup_le le_rfl hsmul : N ⊔ I • N' ≤ N)

/-- Lemma 10.20.1 (Nakayama's lemma) (5): if `M` is finite and the induced map
`N / I N → M / I M` is surjective, then after localizing away some `r ∈ 1 + I` the map
`N_r → M_r` is surjective. -/
-- Proof sketch: surjectivity of the induced quotient map identifies the quotient image of
-- `LinearMap.range g` with all of `M / I M`, equivalently
-- `LinearMap.range g ⊔ I • ⊤ = ⊤`. Apply clause (3) to `LinearMap.range g` and `⊤`, then use
-- `LinearMap.range_localizedMap_eq_localized₀_range` to read the localized range equality as
-- surjectivity of the localized map.
theorem exists_sub_one_mem_and_localizedAwayMap_surjective_of_quotientMap_surjective
    (g : N →ₗ[R] M) [Module.Finite R M] (hquot : Function.Surjective (g.quotientMapByIdeal I)) :
    ∃ r : R,
      r - 1 ∈ I ∧ Function.Surjective ((LocalizedModule.map (Submonoid.powers r)) g) := sorry

/-- Lemma 10.20.1 (Nakayama's lemma) (6): if `M` is finite, the induced map
`N / I N → M / I M` is surjective, and `I` lies in the Jacobson radical, then `g` is
surjective. -/
-- Proof sketch: surjectivity of the induced quotient map is equivalent to
-- `LinearMap.range g ⊔ I • ⊤ = ⊤`. Apply clause (4) to `LinearMap.range g` and `⊤`, then read
-- `LinearMap.range g = ⊤` as surjectivity of `g`.
theorem surjective_of_quotientMap_surjective_of_le_ring_jacobson
    (g : N →ₗ[R] M) [Module.Finite R M] (hquot : Function.Surjective (g.quotientMapByIdeal I))
    (hIjac : I ≤ Ring.jacobson R) : Function.Surjective g := sorry

/-- Lemma 10.20.1 (Nakayama's lemma) (7): if a finite set of elements generates `M / IM` and `M`
is finite, then after localizing away some `r ∈ 1 + I` it generates `M_r`. -/
-- Proof sketch: apply clause (5) to the linear map from the free module on the finite set `s`.
-- The hypothesis says that the quotient images of the elements of `s` span `M / I M`, and the
-- conclusion identifies generation of the localization with the localized span being `⊤`.
theorem exists_sub_one_mem_and_span_localized_eq_top_of_quotient_span_eq_top
    [Module.Finite R M] (s : Finset M)
    (hgen : Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' (s : Set M)) = ⊤) :
    ∃ r : R,
      r - 1 ∈ I ∧ (Submodule.span R (s : Set M)).localized (Submonoid.powers r) = ⊤ := sorry

/-- Lemma 10.20.1 (Nakayama's lemma) (8): if a finite set of elements generates `M / IM`, `M` is
finite, and `I` lies in the Jacobson radical, then it generates `M`. -/
-- Proof sketch: apply clause (6) to the linear map from the free module on the finite set `s`.
-- The quotient images of the elements of `s` spanning `M / I M` exactly says that the induced
-- quotient map is surjective, and surjectivity of the original map is equivalent to
-- `Submodule.span R (s : Set M) = ⊤`.
theorem span_eq_top_of_quotient_span_eq_top_of_le_ring_jacobson
    [Module.Finite R M] (s : Finset M)
    (hgen : Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' (s : Set M)) = ⊤)
    (hIjac : I ≤ Ring.jacobson R) :
    Submodule.span R (s : Set M) = ⊤ := sorry

end

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

section

variable (I : Ideal R)

local notation "IM" => I • (⊤ : Submodule R M)

/-- Lemma 10.20.1 (Nakayama's lemma) (9): if `IM = M` and `I` is nilpotent, then `M` is the zero
module. -/
-- Proof sketch: if `I ^ n = 0`, then `M = I • M` implies inductively `M = I ^ n • M = 0`.
theorem subsingleton_of_ideal_smul_top_eq_top_of_isNilpotent
    (hIM : IM = ⊤) (hI : IsNilpotent I) :
    Subsingleton M := sorry

/-- Lemma 10.20.1 (Nakayama's lemma) (10): if `N ⊔ I • N' = M` and `I` is nilpotent, then
`N = M`. -/
-- Proof sketch: pass to the quotient by `N`; there the hypothesis becomes `I • Q = Q`, and the
-- nilpotence of `I` forces `Q = 0`, hence `N = M`.
theorem eq_top_of_sup_eq_top_of_isNilpotent
    (I : Ideal R) (N N' : Submodule R M) (hMN : N ⊔ I • N' = ⊤) (hI : IsNilpotent I) :
    N = ⊤ := sorry

/-- Lemma 10.20.1 (Nakayama's lemma) (11): if the image of `g : N → M` generates `M / IM` and
`I` is nilpotent, then `g` is surjective. -/
-- Proof sketch: let `Q` be the cokernel of `g`. Surjectivity modulo `I` says `I • Q = Q`, and
-- nilpotence of `I` forces `Q = 0`, so `g` is surjective.
theorem surjective_of_quotientMap_surjective_of_isNilpotent
    (g : N →ₗ[R] M) (hquot : Function.Surjective (g.quotientMapByIdeal I))
    (hI : IsNilpotent I) : Function.Surjective g := sorry

/-- Lemma 10.20.1 (Nakayama's lemma) (12): if a set `s` of elements of `M` generates `M / IM`
and `I` is nilpotent, then `s` generates `M`. -/
-- Proof sketch: apply clause (11) to the canonical map from the free module on `s`; the quotient
-- generation hypothesis says the induced map modulo `I` is surjective, and surjectivity of the
-- original map is exactly `Submodule.span R s = ⊤`.
theorem span_eq_top_of_quotient_span_eq_top_of_isNilpotent
    (s : Set M) (hgen : Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' s) = ⊤)
    (hI : IsNilpotent I) :
    Submodule.span R s = ⊤ := sorry

end

end

end
