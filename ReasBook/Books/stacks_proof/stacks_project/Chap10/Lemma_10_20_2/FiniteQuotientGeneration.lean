import Mathlib
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

/-- Helper for Lemma 10.20.2: the map on quotients modulo `I` induced by an `R`-linear map. -/
abbrev quotientMapByIdealLocal
    {N : Type*} [AddCommGroup N] [Module R N]
    (g : N →ₗ[R] M) :
    N ⧸ (I • (⊤ : Submodule R N)) →ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
  (I • (⊤ : Submodule R N)).mapQ (I • (⊤ : Submodule R M)) g
    (Submodule.smul_top_le_comap_smul_top I g)

/-- Helper for Lemma 10.20.2: the induced quotient map is surjective exactly when the range of the
original map together with `I M` generates the target. -/
theorem quotientMapByIdeal_surjective_iff_range_sup_ideal_smul_top_eq_top
    {N : Type*} [AddCommGroup N] [Module R N]
    (g : N →ₗ[R] M) :
    Function.Surjective (quotientMapByIdealLocal (I := I) g) ↔
      LinearMap.range g ⊔ I • (⊤ : Submodule R M) = ⊤ := by
  -- Compare the quotient-map range with the quotient image of `LinearMap.range g`.
  have hrange :
      LinearMap.range (quotientMapByIdealLocal (I := I) g) =
        Submodule.map (I • (⊤ : Submodule R M)).mkQ (LinearMap.range g) := by
    calc
      LinearMap.range (quotientMapByIdealLocal (I := I) g)
          = LinearMap.range
              ((quotientMapByIdealLocal (I := I) g).comp (I • (⊤ : Submodule R N)).mkQ) := by
              symm
              exact LinearMap.range_comp_of_range_eq_top _
                (Submodule.range_mkQ (p := I • (⊤ : Submodule R N)))
      _ = Submodule.map (I • (⊤ : Submodule R M)).mkQ (LinearMap.range g) := by
            rw [quotientMapByIdealLocal, Submodule.mapQ_mkQ, LinearMap.range_comp]
  rw [← LinearMap.range_eq_top, hrange, Submodule.map_mkQ_eq_top, sup_comm]

/-- Helper for Lemma 10.20.2: generation modulo `I M` is equivalent to the original span together
with `I M` being all of `M`. -/
theorem quotient_span_eq_top_iff_span_sup_ideal_smul_top_eq_top
    (s : Set M) :
    Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' s) = ⊤ ↔
      Submodule.span R s ⊔ I • (⊤ : Submodule R M) = ⊤ := by
  -- Push the span through the quotient map.
  rw [← Submodule.map_span, Submodule.map_mkQ_eq_top, sup_comm]

/-- Helper for Lemma 10.20.2: the free cover on a subset has range equal to the span of that
subset. -/
theorem range_linearCombination_subtype_eq_span
    (s : Set M) :
    LinearMap.range (Finsupp.linearCombination R (fun x : s ↦ (x : M))) =
      Submodule.span R s := by
  -- This is the canonical range computation for the free cover.
  symm
  exact Finsupp.span_eq_range_linearCombination (R := R) (s := s)

/-- Helper for Lemma 10.20.2: if `N ⊔ I • N' = M` with `N'` finite, then after localizing away
some `r ∈ 1 + I`, the localized submodule `N_r` is all of `M_r`. -/
theorem exists_sub_one_mem_and_smul_top_le_of_sup_eq_top
    {N N' : Submodule R M}
    (hN' : N'.FG) (hMN : N ⊔ I • N' = ⊤) :
    ∃ r : R,
      r - 1 ∈ I ∧ r • (⊤ : Submodule R M) ≤ N ∧ N.localized (Submonoid.powers r) = ⊤ := by
  have hN'le : N' ≤ (⊤ : Submodule R M) := le_top
  have hsup : (⊤ : Submodule R M) ≤ N ⊔ I • N' := by
    rw [hMN]
  obtain ⟨r, hrI, hrN⟩ :=
    Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hN' hN'le hsup
  refine ⟨r, hrI, hrN, top_unique ?_⟩
  have hlocalized :
      (⊤ : Submodule R M).localized (Submonoid.powers r) ≤
        N.localized (Submonoid.powers r) := by
    let x : Submonoid.powers r := ⟨r, ⟨1, by simp⟩⟩
    -- Inverting `r` turns the inclusion `r M ⊆ N` into generation by `N`.
    simpa [Submodule.localized] using
      (Submodule.localized'_le_localized'_of_smul_le
        (Localization (Submonoid.powers r))
        (Submonoid.powers r)
        (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
        x
        hrN)
  simpa using hlocalized

/-- Helper for Lemma 10.20.2: surjectivity modulo `I` implies surjectivity after localizing away
from one element of `1 + I`. -/
theorem exists_sub_one_mem_and_localizedAwayMap_surjective_of_quotientMap_surjective
    {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R M] (g : N →ₗ[R] M)
    (hquot : Function.Surjective (quotientMapByIdealLocal (I := I) g)) :
    ∃ r : R,
      r - 1 ∈ I ∧ Function.Surjective ((LocalizedModule.map (Submonoid.powers r)) g) := by
  have hsup : LinearMap.range g ⊔ I • (⊤ : Submodule R M) = ⊤ :=
    (quotientMapByIdeal_surjective_iff_range_sup_ideal_smul_top_eq_top
      (R := R) (M := M) (I := I) g).1 hquot
  obtain ⟨r, hrI, hrange, hlocalized⟩ :=
    exists_sub_one_mem_and_smul_top_le_of_sup_eq_top
      (R := R)
      (M := M)
      (I := I)
      (N := LinearMap.range g)
      (N' := ⊤)
      Module.Finite.fg_top
      hsup
  refine ⟨r, hrI, ?_⟩
  intro y
  have hy : y ∈ (LinearMap.range g).localized (Submonoid.powers r) := by
    rw [hlocalized]
    exact Submodule.mem_top
  rw [Submodule.localized, Submodule.mem_localized'] at hy
  rcases hy with ⟨m, hm, s, rfl⟩
  rcases hm with ⟨n, rfl⟩
  refine ⟨IsLocalizedModule.mk' (LocalizedModule.mkLinearMap (Submonoid.powers r) N) n s, ?_⟩
  -- The localized representative is visibly the image of the corresponding numerator.
  exact IsLocalizedModule.map_mk'
    (S := Submonoid.powers r)
    (f := LocalizedModule.mkLinearMap (Submonoid.powers r) N)
    (g := LocalizedModule.mkLinearMap (Submonoid.powers r) M)
    g
    n
    s

/-- Helper for Lemma 10.20.2: a finite spanning family in `M / I M` already spans some away
localization `M_r` with `r ∈ 1 + I`. -/
theorem exists_sub_one_mem_and_span_localized_eq_top_of_quotient_span_eq_top
    [Module.Finite R M] (s : Finset M)
    (hgen : Submodule.span R ((I • (⊤ : Submodule R M)).mkQ '' (s : Set M)) = ⊤) :
    ∃ r : R,
      r - 1 ∈ I ∧ (Submodule.span R (s : Set M)).localized (Submonoid.powers r) = ⊤ := by
  let π : ((↑(s : Set M)) →₀ R) →ₗ[R] M :=
    Finsupp.linearCombination R (fun x : ↑(s : Set M) ↦ (x : M))
  have hsup : LinearMap.range π ⊔ I • (⊤ : Submodule R M) = ⊤ := by
    rw [range_linearCombination_subtype_eq_span (R := R) (M := M) (s := (s : Set M))]
    exact
      (quotient_span_eq_top_iff_span_sup_ideal_smul_top_eq_top
        (R := R) (M := M) (I := I) (s := (s : Set M))).1 hgen
  have hquot : Function.Surjective (quotientMapByIdealLocal (I := I) π) :=
    (quotientMapByIdeal_surjective_iff_range_sup_ideal_smul_top_eq_top
      (R := R) (M := M) (I := I) π).2 hsup
  obtain ⟨r, hrI, hsurj⟩ :=
    exists_sub_one_mem_and_localizedAwayMap_surjective_of_quotientMap_surjective
      (R := R)
      (M := M)
      (I := I)
      π
      hquot
  have hrange_localized :
      (LinearMap.range π).localized (Submonoid.powers r) =
        LinearMap.range ((LocalizedModule.map (Submonoid.powers r)) π) := by
    -- Localization commutes with ranges for the free cover map.
    simpa [π, Submodule.localized] using
      (LinearMap.localized'_range_eq_range_localizedMap
        (S := Localization (Submonoid.powers r))
        (p := Submonoid.powers r)
        (f := LocalizedModule.mkLinearMap (Submonoid.powers r) (((↑(s : Set M)) →₀ R)))
        (f' := LocalizedModule.mkLinearMap (Submonoid.powers r) M)
        π)
  refine ⟨r, hrI, ?_⟩
  -- Surjectivity of the localized free cover is exactly the localized spanning statement.
  calc
    (Submodule.span R (s : Set M)).localized (Submonoid.powers r)
        = (LinearMap.range π).localized (Submonoid.powers r) := by
            rw [← range_linearCombination_subtype_eq_span (R := R) (M := M) (s := (s : Set M))]
    _ = LinearMap.range ((LocalizedModule.map (Submonoid.powers r)) π) := hrange_localized
    _ = ⊤ := LinearMap.range_eq_top.2 hsurj

end
