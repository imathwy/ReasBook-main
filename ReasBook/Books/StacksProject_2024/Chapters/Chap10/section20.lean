import Mathlib
import Mathlib.RingTheory.Ideal.Cotangent

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_20_1_Nakayama_s_lemma (from Chap10) -/
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

section HelperLemmas

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Helper for Lemma 10.20.1 (Nakayama's lemma): the induced map modulo `I` is surjective exactly
when the image of `g` together with `IM` generates the target module. -/
private theorem quotientMapByIdeal_surjective_iff_range_sup_ideal_smul_top_eq_top
    (I : Ideal R) (g : N →ₗ[R] M) :
    Function.Surjective (g.quotientMapByIdeal I) ↔
      LinearMap.range g ⊔ I • (⊤ : Submodule R M) = ⊤ := by
  -- Compare the range of the quotient map with the quotient image of `LinearMap.range g`.
  have hrange :
      LinearMap.range (g.quotientMapByIdeal I) =
        Submodule.map (I • (⊤ : Submodule R M)).mkQ (LinearMap.range g) := by
    calc
      LinearMap.range (g.quotientMapByIdeal I)
          = LinearMap.range ((g.quotientMapByIdeal I).comp (I • (⊤ : Submodule R N)).mkQ) := by
              symm
              exact LinearMap.range_comp_of_range_eq_top _
                (Submodule.range_mkQ (p := I • (⊤ : Submodule R N)))
      _ = Submodule.map (I • (⊤ : Submodule R M)).mkQ (LinearMap.range g) := by
            rw [LinearMap.quotientMapByIdeal, Submodule.mapQ_mkQ, LinearMap.range_comp]
  rw [← LinearMap.range_eq_top, hrange, Submodule.map_mkQ_eq_top, sup_comm]

/-- Helper for Lemma 10.20.1 (Nakayama's lemma): generation after quotienting by `IM` is
equivalent to the original span plus `IM` being all of `M`. -/
private theorem quotient_span_eq_top_iff_span_sup_ideal_smul_top_eq_top
    (I : Ideal R) (s : Set M) :
    Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' s) = ⊤ ↔
      Submodule.span R s ⊔ I • (⊤ : Submodule R M) = ⊤ := by
  -- Push the span through the quotient map and use the standard `map_mkQ_eq_top` criterion.
  rw [← Submodule.map_span, Submodule.map_mkQ_eq_top, sup_comm]

/-- Helper for Lemma 10.20.1 (Nakayama's lemma): the free cover on a subset has range equal to
the span of that subset. -/
private theorem range_linearCombination_subtype_eq_span (s : Set M) :
    LinearMap.range (Finsupp.linearCombination R (fun x : s ↦ (x : M))) =
      Submodule.span R s := by
  -- This is the canonical range computation for `Finsupp.linearCombination`.
  symm
  exact Finsupp.span_eq_range_linearCombination (R := R) (s := s)

/-- Helper for Lemma 10.20.1 (Nakayama's lemma): once `IM = M`, the same holds for every power of
`I`. -/
private theorem pow_smul_top_eq_top_of_smul_top_eq_top
    {I : Ideal R} (hIM : I • (⊤ : Submodule R M) = ⊤) :
    ∀ n : ℕ, (I ^ n) • (⊤ : Submodule R M) = ⊤
  | 0 => by
      -- The zeroth power acts as the identity on the top submodule.
      simpa [Submodule.pow_zero]
  | n + 1 => by
      -- Rewrite one more power of `I` as one further smul by `I`.
      rw [I.pow_succ, Submodule.mul_smul, hIM,
        pow_smul_top_eq_top_of_smul_top_eq_top hIM n]

end HelperLemmas

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
      r - 1 ∈ I ∧ Function.Surjective ((LocalizedModule.map (Submonoid.powers r)) g) := by
  -- Rewrite the quotient hypothesis into the standard `range ⊔ IM = M` form.
  have hsup : LinearMap.range g ⊔ I • (⊤ : Submodule R M) = ⊤ :=
    (quotientMapByIdeal_surjective_iff_range_sup_ideal_smul_top_eq_top (I := I) g).1 hquot
  -- Apply the submodule form of Nakayama to the image of `g`.
  obtain ⟨r, hrI, hrange, hlocalized⟩ :=
    exists_sub_one_mem_and_smul_top_le_of_sup_eq_top I (LinearMap.range g) (⊤ : Submodule R M)
      Module.Finite.fg_top hsup
  refine ⟨r, hrI, ?_⟩
  intro y
  -- Every localized element of `M` lies in the localization of `LinearMap.range g`.
  have hy : y ∈ (LinearMap.range g).localized (Submonoid.powers r) := by
    rw [hlocalized]
    exact Submodule.mem_top
  rw [Submodule.localized, Submodule.mem_localized'] at hy
  rcases hy with ⟨m, hm, s, rfl⟩
  rcases hm with ⟨n, rfl⟩
  refine ⟨IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (Submonoid.powers r) N) n s, ?_⟩
  -- The localized representative is visibly the image of the corresponding domain element.
  exact IsLocalizedModule.map_mk'
    (S := Submonoid.powers r)
    (f := LocalizedModule.mkLinearMap (Submonoid.powers r) N)
    (g := LocalizedModule.mkLinearMap (Submonoid.powers r) M)
    g n s

/-- Lemma 10.20.1 (Nakayama's lemma) (6): if `M` is finite, the induced map
`N / I N → M / I M` is surjective, and `I` lies in the Jacobson radical, then `g` is
surjective. -/
-- Proof sketch: surjectivity of the induced quotient map is equivalent to
-- `LinearMap.range g ⊔ I • ⊤ = ⊤`. Apply clause (4) to `LinearMap.range g` and `⊤`, then read
-- `LinearMap.range g = ⊤` as surjectivity of `g`.
theorem surjective_of_quotientMap_surjective_of_le_ring_jacobson
    (g : N →ₗ[R] M) [Module.Finite R M] (hquot : Function.Surjective (g.quotientMapByIdeal I))
    (hIjac : I ≤ Ring.jacobson R) : Function.Surjective g := by
  -- Rewrite the quotient hypothesis into the standard `range ⊔ IM = M` form.
  have hsup : LinearMap.range g ⊔ I • (⊤ : Submodule R M) = ⊤ :=
    (quotientMapByIdeal_surjective_iff_range_sup_ideal_smul_top_eq_top (I := I) g).1 hquot
  -- Apply the Jacobson-radical form of Nakayama to the image of `g`.
  have hrange_top : LinearMap.range g = ⊤ :=
    eq_top_of_sup_eq_top_of_le_ring_jacobson I (LinearMap.range g) (⊤ : Submodule R M)
      Module.Finite.fg_top hsup hIjac
  exact LinearMap.range_eq_top.1 hrange_top

/-- Lemma 10.20.1 (Nakayama's lemma) (7): if a finite set of elements generates `M / IM` and `M`
is finite, then after localizing away some `r ∈ 1 + I` it generates `M_r`. -/
-- Proof sketch: apply clause (5) to the linear map from the free module on the finite set `s`.
-- The hypothesis says that the quotient images of the elements of `s` span `M / I M`, and the
-- conclusion identifies generation of the localization with the localized span being `⊤`.
theorem exists_sub_one_mem_and_span_localized_eq_top_of_quotient_span_eq_top
    [Module.Finite R M] (s : Finset M)
    (hgen : Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' (s : Set M)) = ⊤) :
    ∃ r : R,
      r - 1 ∈ I ∧ (Submodule.span R (s : Set M)).localized (Submonoid.powers r) = ⊤ := by
  let π : ((↑(s : Set M)) →₀ R) →ₗ[R] M :=
    Finsupp.linearCombination R (fun x : ↑(s : Set M) ↦ (x : M))
  -- Translate the quotient spanning hypothesis into the quotient-map hypothesis for `π`.
  have hsup : LinearMap.range π ⊔ I • (⊤ : Submodule R M) = ⊤ := by
    rw [range_linearCombination_subtype_eq_span (R := R) (s := (s : Set M))]
    exact (quotient_span_eq_top_iff_span_sup_ideal_smul_top_eq_top (R := R) (I := I)
      (s := (s : Set M))).1 hgen
  have hquot : Function.Surjective (π.quotientMapByIdeal I) :=
    (quotientMapByIdeal_surjective_iff_range_sup_ideal_smul_top_eq_top (I := I) π).2 hsup
  obtain ⟨r, hrI, hsurj⟩ :=
    exists_sub_one_mem_and_localizedAwayMap_surjective_of_quotientMap_surjective (I := I) π hquot
  have hrange_localized :
      (LinearMap.range π).localized (Submonoid.powers r) =
        LinearMap.range ((LocalizedModule.map (Submonoid.powers r)) π) := by
    -- Localization commutes with ranges for the free-cover map.
    simpa [π, Submodule.localized] using
      (LinearMap.localized'_range_eq_range_localizedMap
        (S := Localization (Submonoid.powers r))
        (p := Submonoid.powers r)
        (f := LocalizedModule.mkLinearMap (Submonoid.powers r) (((↑(s : Set M)) →₀ R)))
        (f' := LocalizedModule.mkLinearMap (Submonoid.powers r) M)
        π)
  refine ⟨r, hrI, ?_⟩
  -- Surjectivity of the localized free-cover is exactly the localized spanning statement.
  calc
    (Submodule.span R (s : Set M)).localized (Submonoid.powers r)
      = (LinearMap.range π).localized (Submonoid.powers r) := by
          rw [← range_linearCombination_subtype_eq_span (R := R) (s := (s : Set M))]
    _ = LinearMap.range ((LocalizedModule.map (Submonoid.powers r)) π) := hrange_localized
    _ = ⊤ := LinearMap.range_eq_top.2 hsurj

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
    Submodule.span R (s : Set M) = ⊤ := by
  let π : ((↑(s : Set M)) →₀ R) →ₗ[R] M :=
    Finsupp.linearCombination R (fun x : ↑(s : Set M) ↦ (x : M))
  -- Translate the quotient spanning hypothesis into the quotient-map hypothesis for `π`.
  have hsup : LinearMap.range π ⊔ I • (⊤ : Submodule R M) = ⊤ := by
    rw [range_linearCombination_subtype_eq_span (R := R) (s := (s : Set M))]
    exact (quotient_span_eq_top_iff_span_sup_ideal_smul_top_eq_top (R := R) (I := I)
      (s := (s : Set M))).1 hgen
  have hquot : Function.Surjective (π.quotientMapByIdeal I) :=
    (quotientMapByIdeal_surjective_iff_range_sup_ideal_smul_top_eq_top (I := I) π).2 hsup
  have hsurj : Function.Surjective π :=
    surjective_of_quotientMap_surjective_of_le_ring_jacobson (I := I) π hquot hIjac
  -- Surjectivity of the free-cover is equivalent to spanning by `s`.
  rw [← range_linearCombination_subtype_eq_span (R := R) (s := (s : Set M))]
  exact LinearMap.range_eq_top.2 hsurj

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
    Subsingleton M := by
  rcases hI with ⟨n, hn⟩
  -- Push the equality `IM = M` through all powers of `I`, then use the nilpotent power.
  have hpow : (I ^ n) • (⊤ : Submodule R M) = ⊤ :=
    pow_smul_top_eq_top_of_smul_top_eq_top (M := M) hIM n
  exact (Submodule.subsingleton_iff R).mp <|
    subsingleton_of_bot_eq_top <| by
      simpa [hn] using hpow

/-- Lemma 10.20.1 (Nakayama's lemma) (10): if `N ⊔ I • N' = M` and `I` is nilpotent, then
`N = M`. -/
-- Proof sketch: pass to the quotient by `N`; there the hypothesis becomes `I • Q = Q`, and the
-- nilpotence of `I` forces `Q = 0`, hence `N = M`.
theorem eq_top_of_sup_eq_top_of_isNilpotent
    (I : Ideal R) (N N' : Submodule R M) (hMN : N ⊔ I • N' = ⊤) (hI : IsNilpotent I) :
    N = ⊤ := by
  -- Pass to the quotient by `N`, where the hypothesis becomes `I • Q = Q`.
  have hquot_smul : I • Submodule.map N.mkQ N' = ⊤ := by
    rw [← Submodule.map_smul'', Submodule.map_mkQ_eq_top, hMN]
  have hquot_top : I • (⊤ : Submodule R (M ⧸ N)) = ⊤ := by
    apply top_unique
    have hle : I • Submodule.map N.mkQ N' ≤ I • (⊤ : Submodule R (M ⧸ N)) :=
      smul_mono_right I
        (show Submodule.map N.mkQ N' ≤ (⊤ : Submodule R (M ⧸ N)) from le_top)
    calc
      (⊤ : Submodule R (M ⧸ N)) = I • Submodule.map N.mkQ N' := by
        symm
        exact hquot_smul
      _ ≤ I • (⊤ : Submodule R (M ⧸ N)) := hle
  have hsub : Subsingleton (M ⧸ N) :=
    subsingleton_of_ideal_smul_top_eq_top_of_isNilpotent I hquot_top hI
  exact Submodule.Quotient.subsingleton_iff.mp hsub

/-- Lemma 10.20.1 (Nakayama's lemma) (11): if the image of `g : N → M` generates `M / IM` and
`I` is nilpotent, then `g` is surjective. -/
-- Proof sketch: let `Q` be the cokernel of `g`. Surjectivity modulo `I` says `I • Q = Q`, and
-- nilpotence of `I` forces `Q = 0`, so `g` is surjective.
theorem surjective_of_quotientMap_surjective_of_isNilpotent
    (g : N →ₗ[R] M) (hquot : Function.Surjective (g.quotientMapByIdeal I))
    (hI : IsNilpotent I) : Function.Surjective g := by
  -- Rewrite the quotient hypothesis into the standard `range ⊔ IM = M` form.
  have hsup : LinearMap.range g ⊔ I • (⊤ : Submodule R M) = ⊤ :=
    (quotientMapByIdeal_surjective_iff_range_sup_ideal_smul_top_eq_top (I := I) g).1 hquot
  have hrange_top : LinearMap.range g = ⊤ :=
    eq_top_of_sup_eq_top_of_isNilpotent I (LinearMap.range g) (⊤ : Submodule R M) hsup hI
  exact LinearMap.range_eq_top.1 hrange_top

/-- Lemma 10.20.1 (Nakayama's lemma) (12): if a set `s` of elements of `M` generates `M / IM`
and `I` is nilpotent, then `s` generates `M`. -/
-- Proof sketch: apply clause (11) to the canonical map from the free module on `s`; the quotient
-- generation hypothesis says the induced map modulo `I` is surjective, and surjectivity of the
-- original map is exactly `Submodule.span R s = ⊤`.
theorem span_eq_top_of_quotient_span_eq_top_of_isNilpotent
    (s : Set M) (hgen : Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' s) = ⊤)
    (hI : IsNilpotent I) :
    Submodule.span R s = ⊤ := by
  let π : (s →₀ R) →ₗ[R] M :=
    Finsupp.linearCombination R (fun x : s ↦ (x : M))
  -- Translate the quotient spanning hypothesis into the quotient-map hypothesis for `π`.
  have hsup : LinearMap.range π ⊔ I • (⊤ : Submodule R M) = ⊤ := by
    rw [range_linearCombination_subtype_eq_span (R := R) (s := s)]
    exact (quotient_span_eq_top_iff_span_sup_ideal_smul_top_eq_top (R := R) (I := I)
      (s := s)).1 hgen
  have hquot : Function.Surjective (π.quotientMapByIdeal I) :=
    (quotientMapByIdeal_surjective_iff_range_sup_ideal_smul_top_eq_top (I := I) π).2 hsup
  have hsurj : Function.Surjective π :=
    surjective_of_quotientMap_surjective_of_isNilpotent (I := I) π hquot hI
  -- Surjectivity of the free-cover is equivalent to spanning by `s`.
  rw [← range_linearCombination_subtype_eq_span (R := R) (s := s)]
  exact LinearMap.range_eq_top.2 hsurj

end

end

end

/-! ### Lemma_10_20_2 (from Chap10) -/
universe u v

noncomputable section

section

open IsLocalizedModule
open LocalizedModule
open scoped Pointwise

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (S : Submonoid R) (I : Ideal R)

local notation "IM" => I • (⊤ : Submodule R M)
local notation "Rs" => Localization S
local notation "Ms" => LocalizedModule S M
local notation "Sbar" => Algebra.algebraMapSubmonoid (R ⧸ I) S
local notation "IS" => Ideal.map (algebraMap R Rs) I
local notation "mkQIM" => Submodule.mkQ (I • (⊤ : Submodule R M))
local notation "ISM" => IS • (⊤ : Submodule Rs Ms)
local notation "mkQISM" => Submodule.mkQ ISM
local notation "Away" => LocalizedModule.Away

/-- Helper for Lemma 10.20.2: the inverse quotient-localization comparison sends the localized
class of `m` to the quotient class of the localized numerator. -/
private lemma away_quotient_equiv_symm_apply_mk
    (s : S) (m : M) :
    (localizedQuotientEquiv (Submonoid.powers s.1) (IM : Submodule R M)).symm
      (LocalizedModule.mkLinearMap (Submonoid.powers s.1) (M ⧸ IM) (Submodule.Quotient.mk m)) =
        Submodule.Quotient.mk (LocalizedModule.mkLinearMap (Submonoid.powers s.1) M m) := by
  -- Compute the canonical quotient-localization equivalence on one generator before taking spans.
  simpa [localizedQuotientEquiv, Submodule.toLocalizedQuotient] using
    (IsLocalizedModule.linearEquiv_symm_apply
      (S := Submonoid.powers s.1)
      (f := (IM : Submodule R M).toLocalizedQuotient (Submonoid.powers s.1))
      (g := LocalizedModule.mkLinearMap (Submonoid.powers s.1) (M ⧸ IM))
      (x := Submodule.Quotient.mk m))

/-- Helper for Lemma 10.20.2: localizing the quotient `M / IM` away from `s` is the same as
quotienting the away-localized module `M_s` by the localized ideal submodule. -/
private noncomputable abbrev away_quotient_linear_equiv
    (s : S) :
    Away s.1 (M ⧸ IM) ≃ₗ[Localization.Away s.1]
      (Away s.1 M ⧸
        ((Ideal.map (algebraMap R (Localization.Away s.1)) I) •
          (⊤ : Submodule (Localization.Away s.1) (Away s.1 M)))) := by
  have hlocalized :
      ((IM : Submodule R M)).localized (Submonoid.powers s.1) =
        ((Ideal.map (algebraMap R (Localization.Away s.1)) I) •
          (⊤ : Submodule (Localization.Away s.1) (Away s.1 M))) := by
    -- Rewrite the localized `IM` submodule into the standard `I_s M_s` form.
    rw [Submodule.localized, Submodule.localized'_smul, Ideal.localized'_eq_map,
      Submodule.localized'_top]
  exact (localizedQuotientEquiv (Submonoid.powers s.1) (IM : Submodule R M)).symm.trans
    (Submodule.quotEquivOfEq _ _ hlocalized)

/-- Helper for Lemma 10.20.2: the product denominator `sf` lies in `S + I` once `f` differs from
an `s`-power by an element of `I`. -/
lemma mul_mem_submonoid_add_ideal_of_mem_powers_add_ideal
    {s f : R} (hs : s ∈ S) (hf : f ∈ ((Submonoid.powers s : Set R) + (I : Set R))) :
    s * f ∈ ((S : Set R) + (I : Set R)) := by
  rcases hf with ⟨t, ht, i, hi, rfl⟩
  rcases Submonoid.mem_powers_iff t s |>.mp ht with ⟨n, rfl⟩
  refine ⟨s ^ (n + 1), S.pow_mem hs (n + 1), s * i, I.mul_mem_left _ hi, ?_⟩
  ring

/-- Helper for Lemma 10.20.2: if `r` divides the away-denominator `x`, then multiplication by `r`
is invertible on the away-localized module `M_x`. -/
private theorem away_moduleEnd_isUnit_of_dvd
    (x r : R) (h : r ∣ x) :
    IsUnit (algebraMap R (Module.End R (Away x M)) r) := by
  -- First read divisibility inside the localized ring `R_x`, then transport the unit to module
  -- endomorphisms via left scalar multiplication.
  have h' : IsUnit (algebraMap R (Localization.Away x) r) :=
    IsLocalization.Away.isUnit_of_dvd x h
  let lsmulAway : Localization.Away x →ₐ[R] Module.End R (Away x M) :=
    Algebra.lsmul R R (Away x M)
  simpa [Algebra.smul_def] using h'.map lsmulAway

/-- Helper for Lemma 10.20.2: the canonical ring map `R_s → R_{s f}` used in the source proof's
final denominator-clearing step. -/
private noncomputable def away_product_right_ring_hom
    (s f : R) :
    Localization.Away s →+* Localization.Away (s * f) :=
  IsLocalization.Away.awayToAwayRight
    (S := Localization.Away s)
    (P := Localization.Away (s * f))
    s
    f

/-- Helper for Lemma 10.20.2: the map `R_s → R_{s f}` sends the image of an element of `R` to its
obvious image in `R_{s f}`. -/
private theorem away_product_right_ring_hom_apply
    (s f r : R) :
    away_product_right_ring_hom (R := R) s f (algebraMap R (Localization.Away s) r) =
      algebraMap R (Localization.Away (s * f)) r := by
  -- This is the defining computation rule for the canonical away-to-away comparison.
  simp [away_product_right_ring_hom, IsLocalization.Away.awayToAwayRight_eq]

/-- Helper for Lemma 10.20.2: if `g` is associated to `f / 1` in `R_s`, then its image in
`R_{s f}` is a unit. -/
private theorem away_product_right_ring_hom_isUnit_of_associated
    (s f : R) {g : Localization.Away s}
    (hgassoc : Associated (algebraMap R (Localization.Away s) f) g) :
    IsUnit (away_product_right_ring_hom (R := R) s f g) := by
  have hf :
      IsUnit
        (away_product_right_ring_hom (R := R) s f
          (algebraMap R (Localization.Away s) f)) := by
    -- The element `f / 1` maps to `f / 1` in `R_{s f}`, and `f` divides `s f`.
    rw [away_product_right_ring_hom_apply]
    exact IsLocalization.Away.isUnit_of_dvd (s * f) (by
      simpa [mul_comm] using (dvd_mul_right f s))
  exact (hgassoc.map (away_product_right_ring_hom (R := R) s f).toMonoidHom).isUnit hf

/-- Helper for Lemma 10.20.2: every power of `s` acts invertibly on `M_(s f)`, so the canonical
map `M_s → M_(s f)` is defined by the localization universal property. -/
private theorem away_product_right_moduleEnd_isUnit
    (s f : R) (x : Submonoid.powers s) :
    IsUnit (algebraMap R (Module.End R (Away (s * f) M)) x.1) := by
  have hs :
      IsUnit (algebraMap R (Module.End R (Away (s * f) M)) s) :=
    away_moduleEnd_isUnit_of_dvd (R := R) (M := M) (s * f) s (dvd_mul_right s f)
  rcases Submonoid.mem_powers_iff x.1 s |>.mp x.2 with ⟨n, hn⟩
  -- Since `s` divides `s f`, the element `s` is already invertible on `M_(s f)`, hence so is
  -- every power of `s`.
  rw [← hn]
  simpa using hs.pow n

/-- Helper for Lemma 10.20.2: the canonical module map `M_s → M_{s f}` from the source proof's
final denominator-clearing step. -/
private noncomputable def away_product_right_linear_map
    (s f : R) :
    Away s M →ₗ[R] Away (s * f) M :=
  LocalizedModule.lift (Submonoid.powers s)
    (LocalizedModule.mkLinearMap (Submonoid.powers (s * f)) M)
    (away_product_right_moduleEnd_isUnit (R := R) (M := M) s f)

/-- Helper for Lemma 10.20.2: the canonical map `M_s → M_{s f}` sends each generator `m / 1` to
the corresponding generator in `M_{s f}`. -/
private theorem away_product_right_linear_map_apply_mk
    (s f : R) (m : M) :
    away_product_right_linear_map (R := R) (M := M) s f
      (LocalizedModule.mkLinearMap (Submonoid.powers s) M m) =
        LocalizedModule.mkLinearMap (Submonoid.powers (s * f)) M m := by
  -- Evaluate the localization lift on the canonical numerator `m / 1`.
  simpa [away_product_right_linear_map] using
    (LocalizedModule.lift_mk_one
      (S := Submonoid.powers s)
      (g := LocalizedModule.mkLinearMap (Submonoid.powers (s * f)) M)
      (h := away_product_right_moduleEnd_isUnit (R := R) (M := M) s f)
      (m := m))

/-- Helper for Lemma 10.20.2: the symmetric canonical ring map `R_f → R_{s f}`. -/
private noncomputable def away_product_left_ring_hom
    (s f : R) :
    Localization.Away f →+* Localization.Away (s * f) :=
  IsLocalization.Away.awayToAwayLeft
    (S := Localization.Away f)
    (P := Localization.Away (s * f))
    f
    s

/-- Helper for Lemma 10.20.2: the map `R_f → R_{s f}` also agrees with the obvious image of each
element of `R`. -/
private theorem away_product_left_ring_hom_apply
    (s f r : R) :
    away_product_left_ring_hom (R := R) s f (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.Away (s * f)) r := by
  -- Again, evaluate the canonical away-to-away comparison on an original numerator.
  simp [away_product_left_ring_hom, IsLocalization.Away.awayToAwayLeft_eq]

/-
Layering for this item:
* source-facing statement: generators of the localization of `M / IM` at `S` already generate some
  away-localization `M_f` for `f ∈ S + I`.
* core/canonical owners: `localizedQuotientEquiv`, `Localization.algEquiv`, and
  `exists_sub_one_mem_and_span_localized_eq_top_of_quotient_span_eq_top`.
* bridge/view: transport the generation hypothesis across the canonical quotient-localization
  equivalences, apply the owner theorem over `Localization S`, and clear denominators in the
  resulting element of `1 + IS`.
-/

/-- Helper for Lemma 10.20.2: in a finite module, if finitely many elements generate after
localizing at a multiplicative set, then one denominator already suffices. -/
lemma exists_single_denominator_of_localized_span_eq_top
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    [Module.Finite A N] {T : Submonoid A} {n : ℕ} (y : Fin n → N)
    (hgen : (Submodule.span A (Set.range y)).localized T = ⊤) :
    ∃ t : T, (Submodule.span A (Set.range y)).localized (Submonoid.powers t.1) = ⊤ := by
  classical
  let P : Submodule A N := Submodule.span A (Set.range y)
  obtain ⟨m, z, hz⟩ := Module.Finite.exists_fin (R := A) (M := N)
  have hu : ∀ i : Fin m, ∃ u : T, u.1 • z i ∈ P := by
    intro i
    have hzi : LocalizedModule.mkLinearMap T N (z i) ∈ P.localized T := by
      simpa [P, hgen] using
        (show LocalizedModule.mkLinearMap T N (z i) ∈
          (⊤ : Submodule (Localization T) (LocalizedModule T N)) from trivial)
    rcases (Submodule.mem_localized'
        (S := Localization T)
        (p := T)
        (f := LocalizedModule.mkLinearMap T N)
        (M' := P)
        (LocalizedModule.mkLinearMap T N (z i))).mp hzi with ⟨x, hx, s, hs⟩
    have hs' :
        LocalizedModule.mkLinearMap T N x =
          LocalizedModule.mkLinearMap T N (s • z i) := by
      -- Rewrite the localized equality into an equality of localized numerators.
      have hxeq :
          IsLocalizedModule.mk' (LocalizedModule.mkLinearMap T N) x s =
            LocalizedModule.mkLinearMap T N (z i) := hs
      simpa using
        (IsLocalizedModule.mk'_eq_iff
          (f := LocalizedModule.mkLinearMap T N)).mp hxeq
    rcases (IsLocalizedModule.eq_iff_exists T (LocalizedModule.mkLinearMap T N)).mp hs' with
      ⟨c, hc⟩
    refine ⟨c * s, ?_⟩
    have hcx : c • x ∈ P := P.smul_mem c hx
    -- The common numerator relation now lives back in the original module.
    rw [show ((c * s : T) : A) • z i = c • x by
      simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hc.symm]
    exact hcx
  choose u hu using hu
  let t : T := Finset.univ.prod u
  have htgen : ∀ i : Fin m, t.1 • z i ∈ P := by
    intro i
    have hui : (u i).1 • z i ∈ P := hu i
    have hmul :
        ((Finset.univ.erase i).prod u : T).1 • ((u i).1 • z i) ∈ P :=
      P.smul_mem ((Finset.univ.erase i).prod u).1 hui
    rw [show t = ((Finset.univ.erase i).prod u : T) * u i by
      simpa [t] using
        (Finset.prod_erase_mul (s := Finset.univ) (f := u) (a := i) (by simp)).symm]
    simpa [t, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hsmul : t.1 • (⊤ : Submodule A N) ≤ P := by
    -- Once every generator lands in `P` after multiplying by `t`, the whole module does.
    rw [← hz, Submodule.smul_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, ⟨i, rfl⟩, rfl⟩
    simpa using htgen i
  refine ⟨t, top_unique ?_⟩
  have hlocalized :
      (⊤ : Submodule A N).localized (Submonoid.powers t.1) ≤
        P.localized (Submonoid.powers t.1) := by
    let tp : Submonoid.powers t.1 := ⟨t.1, ⟨1, by simp⟩⟩
    -- Inverting `t` makes the inclusion `t • ⊤ ≤ P` enough to recover all of the localization.
    simpa [Submodule.localized] using
      (Submodule.localized'_le_localized'_of_smul_le
        (Localization (Submonoid.powers t.1))
        (Submonoid.powers t.1)
        (LocalizedModule.mkLinearMap (Submonoid.powers t.1) N)
        tp
        hsmul)
  simpa [P] using hlocalized

/-- Helper for Lemma 10.20.2: the quotient-generation hypothesis over `S` already holds after
localizing away from one element of `S`. -/
lemma exists_quotient_single_denominator
    [Module.Finite R M] {n : ℕ} (x : Fin n → M)
    (hgen :
      (Submodule.span (R ⧸ I) (Set.range (mkQIM ∘ x))).localized Sbar = ⊤) :
    ∃ s : S,
      (Submodule.span (R ⧸ I) (Set.range (mkQIM ∘ x))).localized
        (Submonoid.powers (algebraMap R (R ⧸ I) s.1)) = ⊤ := by
  let P : Submodule (R ⧸ I) (M ⧸ IM) := Submodule.span (R ⧸ I) (Set.range (mkQIM ∘ x))
  letI : Module.Finite (R ⧸ I) (M ⧸ IM) := inferInstance
  obtain ⟨t, ht⟩ :=
    exists_single_denominator_of_localized_span_eq_top
      (A := R ⧸ I)
      (N := M ⧸ IM)
      (T := Sbar)
      (y := mkQIM ∘ x)
      hgen
  rcases t with ⟨t, htmem⟩
  rcases htmem with ⟨s, hs, rfl⟩
  exact ⟨⟨s, hs⟩, by simpa [P] using ht⟩

/-- Helper for Lemma 10.20.2: if `g - 1` lies in the localized ideal, then clearing one
denominator rewrites `g` as an associate of an element of `S + I`. -/
lemma exists_mem_submonoid_add_ideal_associated_of_sub_one_mem_localized_ideal
    {g : Rs} (hg : g - 1 ∈ IS) :
    ∃ f : R, f ∈ ((S : Set R) + (I : Set R)) ∧ Associated (algebraMap R Rs f) g := by
  rcases (IsLocalization.mem_map_algebraMap_iff
      (M := S)
      (S := Rs)
      (R := R)
      (I := I)
      (z := g - 1)).mp hg with ⟨⟨i, s⟩, hs⟩
  refine ⟨s.1 + i.1, ?_, ?_⟩
  · exact ⟨s.1, s.2, i.1, i.2, by simp⟩
  · have hmul :
        g * algebraMap R Rs s =
          algebraMap R Rs (s.1 + i.1) := by
      -- Clearing the denominator converts `g - 1 ∈ I_S` into a numerator in `S + I`.
      calc
        g * algebraMap R Rs s
            = (g - 1) * algebraMap R Rs s + algebraMap R Rs s := by ring
        _ = algebraMap R Rs i.1 + algebraMap R Rs s := by rw [hs]
        _ = algebraMap R Rs (s.1 + i.1) := by simp [map_add, add_comm]
    exact (Associated.of_eq hmul.symm).trans <|
      (associated_mul_unit_right g (algebraMap R Rs s) (IsLocalization.map_units Rs s)).symm

/-- Helper for Lemma 10.20.2: on a finite index type, the set-theoretic range of a family is the
underlying set of its `Finset.univ.image`. -/
private lemma set_range_eq_univ_image
    {α : Type*} [DecidableEq α] {n : ℕ} (y : Fin n → α) :
    Set.range y = (Finset.univ.image y : Set α) := by
  ext z
  simp

/-- Helper for Lemma 10.20.2: the canonical away-quotient comparison sends each localized
quotient generator to the quotient class of the localized numerator. -/
private lemma away_quotient_linear_equiv_apply_generator
    {n : ℕ} (x : Fin n → M) (s : S) (i : Fin n) :
    away_quotient_linear_equiv (S := S) (I := I) (M := M) s
      (LocalizedModule.mkLinearMap (Submonoid.powers s.1) (M ⧸ IM)
        (mkQIM (x i))) =
        (Submodule.mkQ
          (((Ideal.map (algebraMap R (Localization.Away s.1)) I) •
            (⊤ : Submodule (Localization.Away s.1) (Away s.1 M)))))
          (LocalizedModule.mkLinearMap (Submonoid.powers s.1) M (x i)) := by
  -- Compute the quotient-localization comparison on generators before comparing spans.
  simp only [away_quotient_linear_equiv, LinearEquiv.trans_apply]
  have hmk :
      (localizedQuotientEquiv (Submonoid.powers s.1) (IM : Submodule R M)).symm
        (LocalizedModule.mkLinearMap (Submonoid.powers s.1) (M ⧸ IM) (mkQIM (x i))) =
          Submodule.Quotient.mk (LocalizedModule.mkLinearMap (Submonoid.powers s.1) M (x i)) := by
    simpa using away_quotient_equiv_symm_apply_mk (S := S) (I := I) (s := s) (m := x i)
  rw [hmk]
  rw [Submodule.quotEquivOfEq_mk]
  rfl

/-- Helper for Lemma 10.20.2: after clearing to one denominator `s ∈ S`, the quotient-generation
statement matches the exact Nakayama input over `Localization.Away s`. -/
private lemma away_quotient_span_eq_top_of_quotient_single_denominator
    {n : ℕ} (x : Fin n → M) (s : S)
    (hsquot :
      (Submodule.span (R ⧸ I) (Set.range (mkQIM ∘ x))).localized
        (Submonoid.powers (algebraMap R (R ⧸ I) s.1)) = ⊤) :
    Submodule.span (Localization.Away s.1)
      ((Submodule.mkQ
          (((Ideal.map (algebraMap R (Localization.Away s.1)) I) •
            (⊤ : Submodule (Localization.Away s.1) (Away s.1 M))))) ''
        Set.range (LocalizedModule.mkLinearMap (Submonoid.powers s.1) M ∘ x)) = ⊤ := by
  -- TODO for Lemma 10.20.2: transport `hsquot` from the localization of `M / IM` over
  -- `(R / I)_(s̄)` to the direct away chart `Away s (M / IM)` over `R_s`, then map it across
  -- `away_quotient_linear_equiv` using `away_quotient_linear_equiv_apply_generator`.
  -- The remaining blocker is the missing clean module bridge from
  -- `Away (algebraMap R (R ⧸ I) s.1) (M ⧸ IM)` to `Away s.1 (M ⧸ IM)` over `Localization.Away s.1`.
  sorry

/-- Helper for Lemma 10.20.2: if every power of `r` already acts invertibly on `N`, then the
canonical map `N → N_r` is inverse to the localization collapse map. -/
private theorem away_localized_by_unit_left_inv
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (r : A)
    (h : ∀ x : Submonoid.powers r, IsUnit (algebraMap A (Module.End A N) x)) :
    (LocalizedModule.lift (Submonoid.powers r) (.id : N →ₗ[A] N) h).comp
      (LocalizedModule.mkLinearMap (Submonoid.powers r) N) = .id := by
  -- The localization lift is defined to be inverse to the canonical localization map.
  simpa using
    (LocalizedModule.lift_comp (Submonoid.powers r) (.id : N →ₗ[A] N) h)

/-- Helper for Lemma 10.20.2: if every power of `r` already acts invertibly on `N`, then every
localized numerator comes from `N` itself. -/
private theorem away_localized_by_unit_right_inv
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (r : A)
    (h : ∀ x : Submonoid.powers r, IsUnit (algebraMap A (Module.End A N) x)) :
    (LocalizedModule.mkLinearMap (Submonoid.powers r) N).comp
      (LocalizedModule.lift (Submonoid.powers r) (.id : N →ₗ[A] N) h) = .id := by
  -- Check the collapse map on the canonical fractions `n / r^k`.
  ext x
  induction x using LocalizedModule.induction_on with
  | _ n s =>
      rw [LinearMap.comp_apply, LocalizedModule.lift_mk, LocalizedModule.mkLinearMap_apply,
        LinearMap.id_apply]
      change LocalizedModule.mk ((h s).unit⁻¹.val n) 1 = LocalizedModule.mk n s
      rw [LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      have hs :
          n = (s : A) • ((h s).unit⁻¹.val n) :=
        (Module.End.algebraMap_isUnit_inv_apply_eq_iff (S := A) (h s) n
          ((h s).unit⁻¹.val n)).mp rfl
      simpa [Submonoid.smul_def] using hs.symm

/-- Helper for Lemma 10.20.2: localizing away from a unit does not change the module. -/
private noncomputable abbrev away_localized_by_unit_equiv
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (r : A)
    (h : ∀ x : Submonoid.powers r, IsUnit (algebraMap A (Module.End A N) x)) :
    Away r N ≃ₗ[A] N :=
  LinearEquiv.ofLinear
    (LocalizedModule.lift (Submonoid.powers r) (.id : N →ₗ[A] N) h)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) N)
    (away_localized_by_unit_left_inv r h)
    (away_localized_by_unit_right_inv r h)

/-- Helper for Lemma 10.20.2: a localized spanning statement is the same as the explicit span of
the canonical away-chart generators. -/
private lemma localized_span_eq_top_iff_explicit_away_span_eq_top
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (r : A) (y : Set N) :
    (Submodule.span A y).localized (Submonoid.powers r) = ⊤ ↔
      Submodule.span (Localization.Away r)
        ((LocalizedModule.mkLinearMap (Submonoid.powers r) N) '' y) = ⊤ := by
  -- Expand the localized span once so later chart comparisons can work with concrete generators.
  rw [Submodule.localized, Submodule.localized'_span]

/-- Helper for Lemma 10.20.2: the canonical map into the iterated localization
`S⁻¹((S')⁻¹N)`. -/
private noncomputable abbrev iterated_localized_module_mkLinearMap
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (S S' : Submonoid A) :
    N →ₗ[A] LocalizedModule S (LocalizedModule S' N) :=
  (LocalizedModule.mkLinearMap S (LocalizedModule S' N)).comp
    (LocalizedModule.mkLinearMap S' N)

/-- Helper for Lemma 10.20.2: invertible endomorphisms stay invertible after localizing a module. -/
private theorem localized_moduleEnd_isUnit
    {A : Type*} [CommRing A] (S : Submonoid A)
    {N : Type*} [AddCommGroup N] [Module A N] {r : A}
    (h : IsUnit (algebraMap A (Module.End A N) r)) :
    IsUnit (algebraMap A (Module.End A (LocalizedModule S N)) r) := by
  let localizedEnd :
      Module.End A (LocalizedModule S N) :=
    IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N) (LocalizedModule.mkLinearMap S N)
      (algebraMap A (Module.End A N) r)
  have hbij : Function.Bijective localizedEnd := by
    have hbij₀ : Function.Bijective (algebraMap A (Module.End A N) r) :=
      (Module.End.isUnit_iff _).mp h
    constructor
    · exact
        IsLocalizedModule.map_injective (S := S) (f := LocalizedModule.mkLinearMap S N)
          (g := LocalizedModule.mkLinearMap S N)
          (h := algebraMap A (Module.End A N) r) hbij₀.1
    · exact
        IsLocalizedModule.map_surjective (S := S) (f := LocalizedModule.mkLinearMap S N)
          (g := LocalizedModule.mkLinearMap S N)
          (h := algebraMap A (Module.End A N) r) hbij₀.2
  have hEq :
      localizedEnd = algebraMap A (Module.End A (LocalizedModule S N)) r := by
    ext x
    induction x using LocalizedModule.induction_on with
    | _ n s =>
        simp [localizedEnd, IsLocalizedModule.map_LocalizedModules, LocalizedModule.smul'_mk]
  rw [← hEq]
  exact (Module.End.isUnit_iff _).2 hbij

/-- Helper for Lemma 10.20.2: iterated localization is localization at the supremum of the two
submonoids. -/
private instance iterated_localized_module_isLocalizedModule_sup
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (S S' : Submonoid A) :
    IsLocalizedModule (S ⊔ S') (iterated_localized_module_mkLinearMap (A := A) (N := N) S S') := by
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · intro x
    rcases Submonoid.mem_sup.mp x.2 with ⟨s, hs, s', hs', hss'⟩
    have hx : (x : A) = s * s' := by
      simpa using hss'.symm
    -- Elements from `S` are inverted by the outer localization, and elements from `S'` stay
    -- invertible after localizing the module a second time.
    have hsUnit :
        IsUnit
          (algebraMap A (Module.End A (LocalizedModule S (LocalizedModule S' N))) s) :=
      IsLocalizedModule.map_units (f := LocalizedModule.mkLinearMap S (LocalizedModule S' N))
        ⟨s, hs⟩
    have hs'Unit₀ :
        IsUnit (algebraMap A (Module.End A (LocalizedModule S' N)) s') :=
      IsLocalizedModule.map_units (f := LocalizedModule.mkLinearMap S' N) ⟨s', hs'⟩
    have hs'Unit :
        IsUnit
          (algebraMap A (Module.End A (LocalizedModule S (LocalizedModule S' N))) s') :=
      localized_moduleEnd_isUnit (S := S) hs'Unit₀
    rw [hx]
    rw [map_mul]
    exact hsUnit.mul hs'Unit
  · intro m
    -- Clear the outer denominator first, then the inner one, and multiply them in the supremum.
    obtain ⟨⟨p, s⟩, hs⟩ :=
      IsLocalizedModule.surj S (LocalizedModule.mkLinearMap S (LocalizedModule S' N)) m
    obtain ⟨⟨x, s'⟩, hs'⟩ :=
      IsLocalizedModule.surj S' (LocalizedModule.mkLinearMap S' N) p
    refine ⟨⟨x, ⟨s.1 * s'.1, Submonoid.mul_mem_sup s.2 s'.2⟩⟩, ?_⟩
    change (s.1 * s'.1 : A) • m =
      (LocalizedModule.mkLinearMap S (LocalizedModule S' N))
        ((LocalizedModule.mkLinearMap S' N) x)
    calc
      (s.1 * s'.1 : A) • m = (s'.1 * s.1 : A) • m := by rw [mul_comm]
      _ = s'.1 • (s • m) := by
        change (s'.1 * s.1 : A) • m = (s'.1 : A) • ((s : A) • m)
        rw [smul_smul]
      _ = s'.1 • (LocalizedModule.mkLinearMap S (LocalizedModule S' N) p) := by rw [hs]
      _ = (LocalizedModule.mkLinearMap S (LocalizedModule S' N)) (s'.1 • p) := by
        rw [LinearMap.map_smul_of_tower]
      _ = (LocalizedModule.mkLinearMap S (LocalizedModule S' N))
            ((LocalizedModule.mkLinearMap S' N) x) := by
        simpa using congrArg (LocalizedModule.mkLinearMap S (LocalizedModule S' N)) hs'
  · intro x₁ x₂ h
    -- Equality upstairs clears in the outer localization and then in the inner localization.
    obtain ⟨s, hs⟩ :=
      IsLocalizedModule.exists_of_eq (S := S)
        (f := LocalizedModule.mkLinearMap S (LocalizedModule S' N)) h
    have hs'₀ :
        (LocalizedModule.mkLinearMap S' N) (s • x₁) =
          (LocalizedModule.mkLinearMap S' N) (s • x₂) := by
      simpa [LinearMap.map_smul_of_tower] using hs
    obtain ⟨s', hs'⟩ :=
      IsLocalizedModule.exists_of_eq (S := S')
        (f := LocalizedModule.mkLinearMap S' N) hs'₀
    refine ⟨⟨s.1 * s'.1, Submonoid.mul_mem_sup s.2 s'.2⟩, ?_⟩
    change (s.1 * s'.1 : A) • x₁ = (s.1 * s'.1 : A) • x₂
    calc
      (s.1 * s'.1 : A) • x₁ = (s'.1 * s.1 : A) • x₁ := by rw [mul_comm]
      _ = s'.1 • (s • x₁) := by
        change (s'.1 * s.1 : A) • x₁ = (s'.1 : A) • ((s : A) • x₁)
        rw [smul_smul]
      _ = s'.1 • (s • x₂) := by simpa using hs'
      _ = (s'.1 * s.1 : A) • x₂ := by
        change (s'.1 : A) • ((s : A) • x₂) = (s'.1 * s.1 : A) • x₂
        rw [smul_smul]
      _ = (s.1 * s'.1 : A) • x₂ := by rw [mul_comm]

/-- Helper for Lemma 10.20.2: direct localization away from `ab` is also localization at the
supremum of the two principal submonoids. -/
private instance mkLinearMap_isLocalizedModule_sup_away_mul
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (a b : A) :
    IsLocalizedModule (Submonoid.powers a ⊔ Submonoid.powers b)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N) := by
  refine
    IsLocalizedModule.of_exists_mul_mem (S := Submonoid.powers (a * b))
      (T := Submonoid.powers a ⊔ Submonoid.powers b) ?_ ?_
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N)
  · intro x hx
    rcases (Submonoid.mem_powers_iff x (a * b)).mp hx with ⟨n, rfl⟩
    simpa [mul_pow] using
      (Submonoid.mul_mem_sup
        (show a ^ n ∈ Submonoid.powers a from ⟨n, rfl⟩)
        (show b ^ n ∈ Submonoid.powers b from ⟨n, rfl⟩))
  · intro x
    rcases Submonoid.mem_sup.mp x.2 with ⟨y, hy, z, hz, hyz⟩
    have hx : (x : A) = y * z := by
      simpa using hyz.symm
    rcases (Submonoid.mem_powers_iff y a).mp hy with ⟨m, rfl⟩
    rcases (Submonoid.mem_powers_iff z b).mp hz with ⟨n, rfl⟩
    refine ⟨a ^ n * b ^ m, ?_⟩
    rw [hx]
    refine ⟨m + n, ?_⟩
    simp [pow_add, mul_pow, mul_assoc, mul_left_comm]

/-- Helper for Lemma 10.20.2: the symmetric supremum description of direct localization away from
`ab`. -/
private instance mkLinearMap_isLocalizedModule_sup_away_mul'
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (a b : A) :
    IsLocalizedModule (Submonoid.powers b ⊔ Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N) := by
  simpa [sup_comm, mul_comm] using
    (mkLinearMap_isLocalizedModule_sup_away_mul (A := A) (N := N) a b :
      IsLocalizedModule (Submonoid.powers a ⊔ Submonoid.powers b)
        (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N))

/-- Helper for Lemma 10.20.2: reindex direct away-localizations along an equality of the
denominator. -/
private noncomputable abbrev away_eq_linear_equiv
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    {a b : A} (h : a = b) :
    Away a N ≃ₗ[A] Away b N :=
  h.rec (LinearEquiv.refl A (Away a N))

/-- Helper for Lemma 10.20.2: equality transport between away localizations fixes canonical
numerators. -/
private theorem away_eq_linear_equiv_apply_mk
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    {a b : A} (h : a = b) (n : N) :
    away_eq_linear_equiv (A := A) (N := N) h
      (LocalizedModule.mkLinearMap (Submonoid.powers a) N n) =
        LocalizedModule.mkLinearMap (Submonoid.powers b) N n := by
  -- The reindexing equivalence is definitionally trivial after substituting the denominator.
  subst h
  rfl

/-- Helper for Lemma 10.20.2: localizing first away from `a` and then away from `b` agrees with
direct localization away from `ab`. -/
private noncomputable abbrev away_mul_linear_equiv
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (a b : A) :
    Away b (Away a N) ≃ₗ[A] Away (a * b) N :=
  IsLocalizedModule.linearEquiv (Submonoid.powers b ⊔ Submonoid.powers a)
    (iterated_localized_module_mkLinearMap (A := A) (N := N)
      (Submonoid.powers b) (Submonoid.powers a))
    (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N)

/-- Helper for Lemma 10.20.2: the direct-versus-iterated away-localization comparison sends a
double canonical numerator to the corresponding direct numerator. -/
private theorem away_mul_linear_equiv_apply_mk_mk
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (a b : A) (n : N) :
    away_mul_linear_equiv (A := A) (N := N) a b
      (LocalizedModule.mkLinearMap (Submonoid.powers b) (Away a N)
        (LocalizedModule.mkLinearMap (Submonoid.powers a) N n)) =
        LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N n := by
  -- Evaluate the universal-property comparison on the canonical double numerator.
  simpa [away_mul_linear_equiv, iterated_localized_module_mkLinearMap, LinearMap.comp_apply] using
    (IsLocalizedModule.linearEquiv_apply
      (S := Submonoid.powers b ⊔ Submonoid.powers a)
      (f := iterated_localized_module_mkLinearMap (A := A) (N := N)
        (Submonoid.powers b) (Submonoid.powers a))
      (g := LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) N)
      n)

/-- Helper for Lemma 10.20.2: if `g` is associated to `f / 1` in `R_s`, then localizing
`M_s` away from `g` is canonically the same as localizing away from `f / 1`. -/
private noncomputable abbrev away_change_denominator_linear_equiv_of_associated
    (s0 f0 : R) {g : Localization.Away s0}
    (hgassoc : Associated (algebraMap R (Localization.Away s0) f0) g) :
    Away g (Away s0 M) ≃ₗ[Localization.Away s0]
      Away (algebraMap R (Localization.Away s0) f0) (Away s0 M) :=
  by
    classical
    let u : Units (Localization.Away s0) := Classical.choose hgassoc
    have hu : (algebraMap R (Localization.Away s0) f0) * (u : Localization.Away s0) = g :=
      Classical.choose_spec hgassoc
    let huEnd :
        ∀ x : Submonoid.powers (u : Localization.Away s0),
          IsUnit
            (algebraMap (Localization.Away s0)
              (Module.End (Localization.Away s0)
                (Away (algebraMap R (Localization.Away s0) f0) (Away s0 M))) x) := by
      intro x
      rcases (Submonoid.mem_powers_iff x.1 (u : Localization.Away s0)).mp x.2 with ⟨n, hn⟩
      let lsmulA :
          Localization.Away s0 →ₐ[Localization.Away s0]
            Module.End (Localization.Away s0)
              (Away (algebraMap R (Localization.Away s0) f0) (Away s0 M)) :=
        Algebra.lsmul _ _ _
      simpa [hn, Algebra.smul_def] using (u.isUnit.pow n).map lsmulA
    -- Rewrite the denominator `g` as `(f0 / 1) * u`, split the product chart, then collapse the
    -- remaining localization at the unit `u`.
    exact
      (away_eq_linear_equiv (A := Localization.Away s0) (N := Away s0 M) hu.symm).trans
        ((away_mul_linear_equiv
            (A := Localization.Away s0)
            (N := Away s0 M)
            (algebraMap R (Localization.Away s0) f0)
            (u : Localization.Away s0)).symm.trans
          (away_localized_by_unit_equiv
            (A := Localization.Away s0)
            (N := Away (algebraMap R (Localization.Away s0) f0) (Away s0 M))
            (u : Localization.Away s0)
            huEnd))

/-- Helper for Lemma 10.20.2: collapsing localization at a unit fixes canonical numerators. -/
private theorem away_localized_by_unit_equiv_apply_mk
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (r : A)
    (h : ∀ x : Submonoid.powers r, IsUnit (algebraMap A (Module.End A N) x))
    (n : N) :
    away_localized_by_unit_equiv (A := A) (N := N) r h
      (LocalizedModule.mkLinearMap (Submonoid.powers r) N n) = n := by
  -- Evaluate the collapse equivalence on a canonical localized numerator.
  have hcomp := away_localized_by_unit_left_inv (A := A) (N := N) r h
  simpa [away_localized_by_unit_equiv, LinearMap.comp_apply] using
    congrArg (fun F => F n) hcomp

/-- Helper for Lemma 10.20.2: the associated-denominator equivalence sends each canonical numerator
on the `g`-chart to the same numerator on the `(f / 1)`-chart. -/
private lemma away_change_denominator_linear_equiv_of_associated_apply_mk
    (s0 f0 : R) {g : Localization.Away s0}
    (hgassoc : Associated (algebraMap R (Localization.Away s0) f0) g)
    (m : Away s0 M) :
    away_change_denominator_linear_equiv_of_associated
      (R := R) (M := M) s0 f0 hgassoc
      (LocalizedModule.mkLinearMap (Submonoid.powers g) (Away s0 M) m) =
        LocalizedModule.mkLinearMap
          (Submonoid.powers (algebraMap R (Localization.Away s0) f0))
          (Away s0 M) m := by
  classical
  let u : Units (Localization.Away s0) := Classical.choose hgassoc
  have hu : (algebraMap R (Localization.Away s0) f0) * (u : Localization.Away s0) = g :=
    Classical.choose_spec hgassoc
  let huEnd :
      ∀ x : Submonoid.powers (u : Localization.Away s0),
        IsUnit
          (algebraMap (Localization.Away s0)
            (Module.End (Localization.Away s0)
              (Away (algebraMap R (Localization.Away s0) f0) (Away s0 M))) x) := by
    intro x
    rcases (Submonoid.mem_powers_iff x.1 (u : Localization.Away s0)).mp x.2 with ⟨n, hn⟩
    let lsmulA :
        Localization.Away s0 →ₐ[Localization.Away s0]
          Module.End (Localization.Away s0)
            (Away (algebraMap R (Localization.Away s0) f0) (Away s0 M)) :=
      Algebra.lsmul _ _ _
    simpa [hn, Algebra.smul_def] using (u.isUnit.pow n).map lsmulA
  have hmul :
      away_mul_linear_equiv
          (A := Localization.Away s0)
          (N := Away s0 M)
          (algebraMap R (Localization.Away s0) f0)
          (u : Localization.Away s0)
          (LocalizedModule.mkLinearMap (Submonoid.powers (u : Localization.Away s0))
            (Away (algebraMap R (Localization.Away s0) f0) (Away s0 M))
            (LocalizedModule.mkLinearMap
              (Submonoid.powers (algebraMap R (Localization.Away s0) f0))
              (Away s0 M) m)) =
        LocalizedModule.mkLinearMap
          (Submonoid.powers
            ((algebraMap R (Localization.Away s0) f0) * (u : Localization.Away s0)))
          (Away s0 M) m := by
    -- Compute the product-chart comparison on the canonical double numerator.
    simpa using
      away_mul_linear_equiv_apply_mk_mk
        (A := Localization.Away s0)
        (N := Away s0 M)
        (algebraMap R (Localization.Away s0) f0)
        (u : Localization.Away s0)
        m
  have hmul_symm :
      (away_mul_linear_equiv
          (A := Localization.Away s0)
          (N := Away s0 M)
          (algebraMap R (Localization.Away s0) f0)
          (u : Localization.Away s0)).symm
        (LocalizedModule.mkLinearMap
          (Submonoid.powers
            ((algebraMap R (Localization.Away s0) f0) * (u : Localization.Away s0)))
          (Away s0 M) m) =
        LocalizedModule.mkLinearMap (Submonoid.powers (u : Localization.Away s0))
          (Away (algebraMap R (Localization.Away s0) f0) (Away s0 M))
          (LocalizedModule.mkLinearMap
            (Submonoid.powers (algebraMap R (Localization.Away s0) f0))
            (Away s0 M) m) := by
    simpa using
      (congrArg
        ((away_mul_linear_equiv
            (A := Localization.Away s0)
            (N := Away s0 M)
            (algebraMap R (Localization.Away s0) f0)
            (u : Localization.Away s0)).symm)
        hmul).symm
  -- Route correction: replace `g` by `(f0 / 1) * u`, split off the unit factor, and then
  -- collapse the localization at `u`.
  change
    (((away_eq_linear_equiv (A := Localization.Away s0) (N := Away s0 M) hu.symm).trans
        ((away_mul_linear_equiv
            (A := Localization.Away s0)
            (N := Away s0 M)
            (algebraMap R (Localization.Away s0) f0)
            (u : Localization.Away s0)).symm.trans
          (away_localized_by_unit_equiv
            (A := Localization.Away s0)
            (N := Away (algebraMap R (Localization.Away s0) f0) (Away s0 M))
            (u : Localization.Away s0)
            huEnd)))
      (LocalizedModule.mkLinearMap (Submonoid.powers g) (Away s0 M) m)) =
      LocalizedModule.mkLinearMap
        (Submonoid.powers (algebraMap R (Localization.Away s0) f0))
        (Away s0 M) m
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
  rw [away_eq_linear_equiv_apply_mk (A := Localization.Away s0) (N := Away s0 M) hu.symm m]
  rw [hmul_symm]
  exact away_localized_by_unit_equiv_apply_mk
    (A := Localization.Away s0)
    (N := Away (algebraMap R (Localization.Away s0) f0) (Away s0 M))
    (u : Localization.Away s0)
    huEnd
    (LocalizedModule.mkLinearMap
      (Submonoid.powers (algebraMap R (Localization.Away s0) f0))
      (Away s0 M) m)

/-- Helper for Lemma 10.20.2: a unit in the scalar ring acts invertibly on every module over that
ring. -/
private theorem moduleEnd_isUnit_of_isUnit
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N] {a : A}
    (ha : IsUnit a) :
    IsUnit (algebraMap A (Module.End A N) a) := by
  -- Transport the unit from the scalar ring into endomorphisms via scalar multiplication.
  let lsmulA : A →ₐ[A] Module.End A N := Algebra.lsmul A A N
  simpa [Algebra.smul_def] using ha.map lsmulA

/-- Helper for Lemma 10.20.2: transporting the `g`-chart spanning statement across the associated
denominator change and then collapsing the product chart yields the desired direct away-localized
span statement. -/
private lemma away_product_chart_collapse_eq_top
    {n : ℕ} (x : Fin n → M) (s : S) {f0 : R} {g : Localization.Away s.1}
    (hgassoc : Associated (algebraMap R (Localization.Away s.1) f0) g)
    (hgspan :
      Submodule.span (Localization.Away g)
        (Set.range
          (LocalizedModule.mkLinearMap (Submonoid.powers g)
            (Away s.1 M) ∘
            (LocalizedModule.mkLinearMap (Submonoid.powers s.1) M ∘ x))) = ⊤) :
    (Submodule.span R (Set.range x)).localized (Submonoid.powers (s.1 * f0)) = ⊤ := by
  sorry

/-- Lemma 10.20.2: if the images of finitely many elements of a finite `R`-module generate the
localization of `M / IM` at `S`, then those elements already generate some away-localization `M_f`
for an element `f ∈ S + I`. -/
-- Proof sketch: use the canonical quotient-localization identifications
-- `localizedQuotientEquiv` and `Localization.algEquiv` to rewrite the hypothesis as a generation
-- statement for `(M_S) / I_S M_S`, where `M_S` is the localization of `M` at `S` and
-- `I_S = I · Localization S`. Apply the owner theorem
-- `exists_sub_one_mem_and_span_localized_eq_top_of_quotient_span_eq_top` from
-- Lemma `10.20.1` over the localized ring `Localization S`. Finally clear the denominator of the
-- resulting element `g ∈ 1 + I_S` to rewrite the away-localization `(M_S)_g` as `M_f` for some
-- `f ∈ S + I`.
theorem exists_mem_submonoid_add_ideal_and_span_localizedAway_eq_top_of_quotient_span_eq_top
    [Module.Finite R M] {n : ℕ} (x : Fin n → M)
    (hgen :
      (Submodule.span (R ⧸ I) (Set.range (mkQIM ∘ x))).localized Sbar = ⊤) :
    ∃ f : R, f ∈ ((S : Set R) + (I : Set R)) ∧
      (Submodule.span R (Set.range x)).localized (Submonoid.powers f) = ⊤ := by
  classical
  -- Route correction: localizing at all of `S` first obscures the source proof and leaves no
  -- reason for `R_f` to invert every element of `S`. We first clear the finitely many quotient
  -- denominators to a single `s ∈ S`, exactly as in the source argument.
  obtain ⟨s, hsquot⟩ := exists_quotient_single_denominator (S := S) (I := I) x hgen
  let xs : Fin n → Away s.1 M :=
    LocalizedModule.mkLinearMap (Submonoid.powers s.1) M ∘ x
  let sx : Finset (Away s.1 M) := Finset.univ.image xs
  let J : Ideal (Localization.Away s.1) := Ideal.map (algebraMap R (Localization.Away s.1)) I
  have hsaway :
      Submodule.span (Localization.Away s.1)
        ((Submodule.mkQ (J • (⊤ : Submodule (Localization.Away s.1) (Away s.1 M)))) ''
          Set.range xs) = ⊤ := by
    -- Rewrite the quotient-side hypothesis as the exact localized Nakayama input over `R_s`.
    simpa [xs, J] using
      away_quotient_span_eq_top_of_quotient_single_denominator
        (S := S) (I := I) (M := M) x s hsquot
  have hsaway_finset :
      Submodule.span (Localization.Away s.1)
        ((Submodule.mkQ (J • (⊤ : Submodule (Localization.Away s.1) (Away s.1 M)))) ''
          (sx : Set (Away s.1 M))) = ⊤ := by
    -- Pass from the ranged family to the finite set needed by Lemma 10.20.1.
    have hset : Set.range xs = (sx : Set (Away s.1 M)) := by
      simpa [sx] using (set_range_eq_univ_image (y := xs))
    rw [← hset]
    exact hsaway
  obtain ⟨g, hgI, hgspan⟩ :=
    exists_sub_one_mem_and_span_localized_eq_top_of_quotient_span_eq_top
      (R := Localization.Away s.1)
      (M := Away s.1 M)
      (I := J)
      sx
      hsaway_finset
  obtain ⟨f0, hf0, hgassoc⟩ :=
    exists_mem_submonoid_add_ideal_associated_of_sub_one_mem_localized_ideal
      (R := R)
      (S := Submonoid.powers s.1)
      (I := I)
      (g := g)
      hgI
  have hgspan' :
      Submodule.span (Localization.Away g)
        (Set.range (LocalizedModule.mkLinearMap (Submonoid.powers g) (Away s.1 M) ∘ xs)) = ⊤ := by
    have hset : (sx : Set (Away s.1 M)) = Set.range xs := by
      ext y
      simp [sx]
    have haway :
        Submodule.span (Localization.Away g)
          ((LocalizedModule.mkLinearMap (Submonoid.powers g) (Away s.1 M)) ''
            (sx : Set (Away s.1 M))) = ⊤ := by
      exact
        (localized_span_eq_top_iff_explicit_away_span_eq_top
          (A := Localization.Away s.1)
          (N := Away s.1 M)
          g
          (sx : Set (Away s.1 M))).mp hgspan
    simpa [hset, Set.range_comp] using haway
  refine ⟨s.1 * f0, ?_, ?_⟩
  · -- The final witness lies in `S + I` because `f0` differs from an `s`-power by an element of
    -- `I`, and multiplying by `s` clears the remaining denominator.
    exact
      mul_mem_submonoid_add_ideal_of_mem_powers_add_ideal
        (S := S) (I := I) s.2 hf0
  · -- Collapse the remaining iterated-away chart to the direct away-localization `M_(s f0)`.
    exact
      away_product_chart_collapse_eq_top
        (R := R) (M := M) (S := S) x s hgassoc
        (by simpa [xs] using hgspan')

end

/-! ### Lemma_10_20_3 (from Chap10) -/
universe u v

open Ideal IsLocalRing

section

/-
Layering for this item:
* source-facing statement: a finite local ring homomorphism is surjective once the induced maps on
  residue fields and cotangent spaces are surjective and the target maximal ideal is finitely
  generated.
* core/canonical owners: `surjective_of_quotientMap_surjective_of_le_ring_jacobson`,
  `ResidueField.map`, and `Ideal.mapCotangent`.
* bridge/view: the residue-field and cotangent-space maps are the quotient maps to which the owner
  Nakayama criterion is applied.
-/

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- Helper for Lemma 10.20.3: the image of the maximal ideal of the source local ring lies in the
maximal ideal of the target local ring. -/
private theorem map_maximalIdeal_le_maximalIdeal :
    Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B := by
  -- A local homomorphism pulls back the target maximal ideal to the source maximal ideal.
  rw [Ideal.map_le_iff_le_comap]
  simpa using le_of_eq (maximalIdeal_comap (algebraMap A B)).symm

/-- Helper for Lemma 10.20.3: cotangent-space surjectivity gives surjectivity of the quotient map
for the inclusion `Ideal.map (algebraMap A B) (maximalIdeal A) ↪ maximalIdeal B`. -/
private theorem map_maximalIdeal_subtype_quotient_surjective_of_cotangent_surjective
    (hcot :
      Function.Surjective
        (mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
          (maximalIdeal_comap (algebraMap A B)).symm.le)) :
    Function.Surjective
      ((Submodule.inclusion (map_maximalIdeal_le_maximalIdeal (A := A) (B := B))).quotientMapByIdeal
        (maximalIdeal B)) := by
  intro x
  obtain ⟨y, hy⟩ := hcot x
  obtain ⟨a, rfl⟩ := (maximalIdeal A).toCotangent_surjective y
  let aI : Ideal.map (algebraMap A B) (maximalIdeal A) :=
    ⟨algebraMap A B a, Ideal.mem_map_of_mem (algebraMap A B) a.2⟩
  refine ⟨Submodule.Quotient.mk aI, ?_⟩
  -- The quotient map is the same canonical cotangent map on representatives.
  have himage :
      (maximalIdeal B).toCotangent
          ⟨algebraMap A B a, map_maximalIdeal_le_maximalIdeal (A := A) (B := B) aI.2⟩ = x := by
    simpa [aI] using
      (Ideal.mapCotangent_toCotangent (I₁ := maximalIdeal A) (I₂ := maximalIdeal B)
        (f := Algebra.ofId A B) (h := (maximalIdeal_comap (algebraMap A B)).symm.le) a).trans hy
  simpa [LinearMap.quotientMapByIdeal, aI] using himage

/-- Helper for Lemma 10.20.3: the cotangent-space hypothesis forces the image of the source
maximal ideal to equal the target maximal ideal. -/
private theorem map_maximalIdeal_eq_maximalIdeal_of_cotangent_surjective
    (hfg : (maximalIdeal B).FG)
    (hcot :
      Function.Surjective
        (mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
          (maximalIdeal_comap (algebraMap A B)).symm.le)) :
    Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B := by
  let ι : Ideal.map (algebraMap A B) (maximalIdeal A) →ₗ[B] maximalIdeal B :=
    Submodule.inclusion (map_maximalIdeal_le_maximalIdeal (A := A) (B := B))
  have hquot : Function.Surjective (ι.quotientMapByIdeal (maximalIdeal B)) :=
    map_maximalIdeal_subtype_quotient_surjective_of_cotangent_surjective
      (A := A) (B := B) hcot
  letI : Module.Finite B (maximalIdeal B) := Module.Finite.of_fg hfg
  have hsurj : Function.Surjective ι := by
    -- Apply Nakayama over `B` to the inclusion of the mapped maximal ideal.
    refine surjective_of_quotientMap_surjective_of_le_ring_jacobson
      (R := B) (I := maximalIdeal B) ι hquot ?_
    simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using
      (show maximalIdeal B ≤ maximalIdeal B from le_rfl)
  apply le_antisymm (map_maximalIdeal_le_maximalIdeal (A := A) (B := B))
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  -- Surjectivity of the inclusion means every element of `maximalIdeal B` already comes from the
  -- mapped ideal.
  have hy_val : y.1 = x := congrArg Subtype.val hy
  simpa [hy_val] using y.2

/-- Helper for Lemma 10.20.3: once the mapped maximal ideal is the target maximal ideal, the
quotient map induced by `algebraMap A B` is exactly the residue-field map. -/
private theorem algebraMap_quotient_surjective_of_residueField_surjective_of_map_maximalIdeal_eq
    (hres : Function.Surjective (ResidueField.map (algebraMap A B)))
    (hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B) :
    Function.Surjective ((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A)) := by
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A B) =
        Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A)) := by
    simp [Ideal.smul_top_eq_map]
  let e₁ :
      (B ⧸ (maximalIdeal A • (⊤ : Submodule A B))) ≃ₗ[A]
        (B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A))) :=
    Submodule.quotEquivOfEq _ _ hsmul
  let e₂ :
      B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A)) →
        ResidueField B :=
    Ideal.quotEquivOfEq hmap
  have he₂inj : Function.Injective e₂ := (Ideal.quotEquivOfEq hmap).injective
  intro x
  obtain ⟨y, hy⟩ := hres (e₂ (e₁ x))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hquotientMap :
      ((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A)) (Submodule.Quotient.mk a) =
        (Submodule.Quotient.mk (algebraMap A B a) :
          B ⧸ (maximalIdeal A • (⊤ : Submodule A B))) := by
    rfl
  have htransport :
      e₁
          (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
            (Submodule.Quotient.mk a)) =
        (Submodule.Quotient.mk (algebraMap A B a) :
          B ⧸ Submodule.restrictScalars A (Ideal.map (algebraMap A B) (maximalIdeal A))) := by
    rw [hquotientMap]
    simpa [e₁] using
      (Submodule.quotEquivOfEq_mk hsmul (algebraMap A B a))
  have hleft :
      e₂
          (e₁
            (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
              (Submodule.Quotient.mk a))) =
        ResidueField.map (algebraMap A B) (residue A a) := by
    rw [htransport]
    calc
      e₂ (Submodule.Quotient.mk (algebraMap A B a))
        = residue B (algebraMap A B a) := by
            simpa [e₂, IsLocalRing.ResidueField] using
              (Ideal.quotEquivOfEq_mk hmap (algebraMap A B a))
      _ = ResidueField.map (algebraMap A B) (residue A a) := by
            symm
            exact IsLocalRing.ResidueField.map_residue (algebraMap A B) a
  have hy' :
      e₂
          (e₁
            (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
              (Submodule.Quotient.mk a))) =
        e₂ (e₁ x) :=
    hleft.trans hy
  refine ⟨Submodule.Quotient.mk a, ?_⟩
  have hquot :
      e₁
          (((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A))
            (Submodule.Quotient.mk a)) =
        e₁ x :=
    he₂inj hy'
  -- After transporting the codomain quotient to the residue field of `B`, the induced quotient
  -- map becomes the canonical residue-field map.
  exact e₁.injective hquot

/-- Lemma 10.20.3: a finite local ring homomorphism is surjective if the target maximal ideal is
finitely generated, the induced map on residue fields is surjective, and the induced map on
cotangent spaces `CotangentSpace A → CotangentSpace B`, given by the canonical map
`mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
  (maximalIdeal_comap (algebraMap A B)).symm.le`, is surjective. -/
-- Proof sketch: apply
-- `surjective_of_quotientMap_surjective_of_le_ring_jacobson` from Lemma `10.20.1` to the
-- `A`-linear map `algebraMap A B`; surjectivity on residue fields identifies the needed quotient
-- map with `ResidueField.map (algebraMap A B)`. Apply the same owner theorem again to the induced
-- map `maximalIdeal A →ₗ[A] maximalIdeal B`; the quotient map in this second step is exactly the
-- canonical cotangent map `mapCotangent ...`, and `hfg` supplies the finite-generation input for
-- `maximalIdeal B`.
theorem surjective_of_localHom_finite_surjective_residueFieldMap_surjective_maximalIdealCotangentMap
    (hf : Module.Finite A B) (hfg : (maximalIdeal B).FG)
    (hres : Function.Surjective (ResidueField.map (algebraMap A B)))
    (hcot :
      Function.Surjective
        (mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
          (maximalIdeal_comap (algebraMap A B)).symm.le)) :
    Function.Surjective (algebraMap A B) := by
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    map_maximalIdeal_eq_maximalIdeal_of_cotangent_surjective
      (A := A) (B := B) hfg hcot
  have hquot :
      Function.Surjective ((Algebra.linearMap A B).quotientMapByIdeal (maximalIdeal A)) :=
    algebraMap_quotient_surjective_of_residueField_surjective_of_map_maximalIdeal_eq
      (A := A) (B := B) hres hmap
  -- Apply Nakayama over `A` to the structural map `A → B`.
  refine surjective_of_quotientMap_surjective_of_le_ring_jacobson
    (R := A) (I := maximalIdeal A) (Algebra.linearMap A B) hquot ?_
  simpa [IsLocalRing.ringJacobson_eq_maximalIdeal] using
    (show maximalIdeal A ≤ maximalIdeal A from le_rfl)

end
