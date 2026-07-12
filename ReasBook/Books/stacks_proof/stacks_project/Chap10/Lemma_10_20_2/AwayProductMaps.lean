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

/-- Helper for Lemma 10.20.2: the inverse quotient-localization comparison sends the localized
class of `m` to the quotient class of the localized numerator. -/
lemma away_quotient_equiv_symm_apply_mk
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
noncomputable abbrev away_quotient_linear_equiv
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
theorem away_moduleEnd_isUnit_of_dvd
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
noncomputable def away_product_right_ring_hom
    (s f : R) :
    Localization.Away s →+* Localization.Away (s * f) :=
  IsLocalization.Away.awayToAwayRight
    (S := Localization.Away s)
    (P := Localization.Away (s * f))
    s
    f

/-- Helper for Lemma 10.20.2: the map `R_s → R_{s f}` sends the image of an element of `R` to its
obvious image in `R_{s f}`. -/
theorem away_product_right_ring_hom_apply
    (s f r : R) :
    away_product_right_ring_hom (R := R) s f (algebraMap R (Localization.Away s) r) =
      algebraMap R (Localization.Away (s * f)) r := by
  -- This is the defining computation rule for the canonical away-to-away comparison.
  simp [away_product_right_ring_hom, IsLocalization.Away.awayToAwayRight_eq]

/-- Helper for Lemma 10.20.2: if `g` is associated to `f / 1` in `R_s`, then its image in
`R_{s f}` is a unit. -/
theorem away_product_right_ring_hom_isUnit_of_associated
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
theorem away_product_right_moduleEnd_isUnit
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
noncomputable def away_product_right_linear_map
    (s f : R) :
    Away s M →ₗ[R] Away (s * f) M :=
  LocalizedModule.lift (Submonoid.powers s)
    (LocalizedModule.mkLinearMap (Submonoid.powers (s * f)) M)
    (away_product_right_moduleEnd_isUnit (R := R) (M := M) s f)

/-- Helper for Lemma 10.20.2: the canonical map `M_s → M_{s f}` sends each generator `m / 1` to
the corresponding generator in `M_{s f}`. -/
theorem away_product_right_linear_map_apply_mk
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
noncomputable def away_product_left_ring_hom
    (s f : R) :
    Localization.Away f →+* Localization.Away (s * f) :=
  IsLocalization.Away.awayToAwayLeft
    (S := Localization.Away f)
    (P := Localization.Away (s * f))
    f
    s

/-- Helper for Lemma 10.20.2: the map `R_f → R_{s f}` also agrees with the obvious image of each
element of `R`. -/
theorem away_product_left_ring_hom_apply
    (s f r : R) :
    away_product_left_ring_hom (R := R) s f (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.Away (s * f)) r := by
  -- Again, evaluate the canonical away-to-away comparison on an original numerator.
  simp [away_product_left_ring_hom, IsLocalization.Away.awayToAwayLeft_eq]

end
