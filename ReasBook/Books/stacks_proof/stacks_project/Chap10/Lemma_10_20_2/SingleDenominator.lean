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
lemma set_range_eq_univ_image
    {α : Type*} [DecidableEq α] {n : ℕ} (y : Fin n → α) :
    Set.range y = (Finset.univ.image y : Set α) := by
  ext z
  simp

/-- Helper for Lemma 10.20.2: a localized spanning statement is the same as the explicit span of
the canonical away-chart generators. -/
lemma localized_span_eq_top_iff_explicit_away_span_eq_top
    {A : Type*} [CommRing A] {N : Type*} [AddCommGroup N] [Module A N]
    (r : A) (y : Set N) :
    (Submodule.span A y).localized (Submonoid.powers r) = ⊤ ↔
      Submodule.span (Localization.Away r)
        ((LocalizedModule.mkLinearMap (Submonoid.powers r) N) '' y) = ⊤ := by
  -- Expand the localized span once so later chart comparisons can work with concrete generators.
  rw [Submodule.localized, Submodule.localized'_span]

end
