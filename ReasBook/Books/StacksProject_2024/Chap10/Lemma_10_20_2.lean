import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

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
