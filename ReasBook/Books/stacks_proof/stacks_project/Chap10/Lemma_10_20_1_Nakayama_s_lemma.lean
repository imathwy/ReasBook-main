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
@[stacks 00DV]
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
@[stacks 00DV]
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
@[stacks 00DV]
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
@[stacks 00DV]
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
@[stacks 00DV]
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
@[stacks 00DV]
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
@[stacks 00DV]
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
@[stacks 00DV]
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
@[stacks 00DV]
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
@[stacks 00DV]
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
@[stacks 00DV]
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
@[stacks 00DV]
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
