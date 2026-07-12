import Mathlib
import Mathlib.Tactic.StacksAttribute
import StacksProject_2024.Chap10.Lemma_10_20_2.Index

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
local notation "Sbar" => Algebra.algebraMapSubmonoid (R ⧸ I) S
local notation "mkQIM" => Submodule.mkQ (I • (⊤ : Submodule R M))

/-- Helper for Chap10 Lemma 10 20 2: membership in the quotient span is equivalent to membership
in the original span plus `I • ⊤`. -/
private lemma quotient_span_mem_iff_mem_span_sup_ideal_smul_top
    {n : ℕ} (x : Fin n → M) (m : M) :
    mkQIM m ∈ Submodule.span (R ⧸ I) (Set.range (mkQIM ∘ x)) ↔
      m ∈ Submodule.span R (Set.range x) ⊔ IM := by
  let P : Submodule R M := Submodule.span R (Set.range x)
  have hspanR :
      (Submodule.span (R ⧸ I) (Set.range (mkQIM ∘ x))).restrictScalars R =
        Submodule.span R (Set.range (mkQIM ∘ x)) := by
    exact Submodule.restrictScalars_span R (R ⧸ I) Ideal.Quotient.mk_surjective _
  have hmapP : Submodule.map mkQIM P = Submodule.span R (Set.range (mkQIM ∘ x)) := by
    dsimp [P]
    rw [Submodule.map_span]
    congr 1
    ext y
    simp [Set.range_comp]
  constructor
  · intro hm
    have hmR : mkQIM m ∈ Submodule.span R (Set.range (mkQIM ∘ x)) := by
      rw [← hspanR]
      exact hm
    have hmcomap : m ∈ Submodule.comap mkQIM (Submodule.map mkQIM P) := by
      simpa [hmapP] using hmR
    rw [Submodule.comap_map_mkQ] at hmcomap
    simpa [P, sup_comm] using hmcomap
  · intro hm
    have hmcomap : m ∈ Submodule.comap mkQIM (Submodule.map mkQIM P) := by
      rw [Submodule.comap_map_mkQ]
      simpa [P, sup_comm] using hm
    have hmR : mkQIM m ∈ Submodule.span R (Set.range (mkQIM ∘ x)) := by
      simpa [hmapP] using hmcomap
    rw [← hspanR] at hmR
    exact hmR

/-- Helper for Chap10 Lemma 10 20 2: localized quotient generation gives one denominator whose
multiple of `⊤` lies in the span plus `I • ⊤`. -/
private lemma exists_submonoid_smul_top_le_span_sup_ideal_smul_top_of_quotient_span_localized_eq_top
    [Module.Finite R M] {n : ℕ} (x : Fin n → M)
    (hgen :
      (Submodule.span (R ⧸ I) (Set.range (mkQIM ∘ x))).localized Sbar = ⊤) :
    ∃ t : S, t.1 • (⊤ : Submodule R M) ≤
      Submodule.span R (Set.range x) ⊔ IM := by
  classical
  let Pq : Submodule (R ⧸ I) (M ⧸ IM) :=
    Submodule.span (R ⧸ I) (Set.range (mkQIM ∘ x))
  let Qsub : Submodule R M := Submodule.span R (Set.range x) ⊔ IM
  obtain ⟨m, z, hz⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hclear : ∀ i : Fin m, ∃ u : S, u.1 • z i ∈ Qsub := by
    intro i
    have hzi : LocalizedModule.mkLinearMap Sbar (M ⧸ IM) (mkQIM (z i)) ∈
        Pq.localized Sbar := by
      simpa [Pq, hgen] using
        (show LocalizedModule.mkLinearMap Sbar (M ⧸ IM) (mkQIM (z i)) ∈
          (⊤ : Submodule (Localization Sbar) (LocalizedModule Sbar (M ⧸ IM))) from trivial)
    rcases (Submodule.mem_localized'
        (S := Localization Sbar)
        (p := Sbar)
        (f := LocalizedModule.mkLinearMap Sbar (M ⧸ IM))
        (M' := Pq)
        (LocalizedModule.mkLinearMap Sbar (M ⧸ IM) (mkQIM (z i)))).mp hzi with
      ⟨q, hq, sbar, hsbar⟩
    have hqeq :
        LocalizedModule.mkLinearMap Sbar (M ⧸ IM) q =
          LocalizedModule.mkLinearMap Sbar (M ⧸ IM) (sbar • mkQIM (z i)) := by
      have hmk :
          IsLocalizedModule.mk' (LocalizedModule.mkLinearMap Sbar (M ⧸ IM)) q sbar =
            LocalizedModule.mkLinearMap Sbar (M ⧸ IM) (mkQIM (z i)) := hsbar
      have hmk' :
          LocalizedModule.mkLinearMap Sbar (M ⧸ IM) q =
            sbar • LocalizedModule.mkLinearMap Sbar (M ⧸ IM) (mkQIM (z i)) :=
        (IsLocalizedModule.mk'_eq_iff
          (f := LocalizedModule.mkLinearMap Sbar (M ⧸ IM))).mp hmk
      have hmap_smul :
          LocalizedModule.mkLinearMap Sbar (M ⧸ IM) (sbar • mkQIM (z i)) =
            sbar • LocalizedModule.mkLinearMap Sbar (M ⧸ IM) (mkQIM (z i)) := by
        change LocalizedModule.mkLinearMap Sbar (M ⧸ IM) ((sbar : R ⧸ I) • mkQIM (z i)) =
          (sbar : R ⧸ I) • LocalizedModule.mkLinearMap Sbar (M ⧸ IM) (mkQIM (z i))
        exact LinearMap.map_smul (LocalizedModule.mkLinearMap Sbar (M ⧸ IM)) (sbar : R ⧸ I)
          (mkQIM (z i))
      rw [hmap_smul]
      exact hmk'
    rcases (IsLocalizedModule.eq_iff_exists Sbar
        (LocalizedModule.mkLinearMap Sbar (M ⧸ IM))).mp hqeq with
      ⟨c, hc⟩
    let d : Sbar := c * sbar
    rcases d.2 with ⟨u0, hu0, hud⟩
    refine ⟨⟨u0, hu0⟩, ?_⟩
    have hdmem : d.1 • mkQIM (z i) ∈ Pq := by
      have hcq : c • q ∈ Pq := Pq.smul_mem c hq
      have hcd : c • q = d.1 • mkQIM (z i) := by
        change (c : R ⧸ I) • q = ((c : R ⧸ I) * (sbar : R ⧸ I)) • mkQIM (z i)
        simpa [Submonoid.smul_def, smul_smul] using hc
      rw [hcd] at hcq
      exact hcq
    have hu_eq : mkQIM ((u0 : R) • z i) = d.1 • mkQIM (z i) := by
      rw [map_smul]
      change (algebraMap R (R ⧸ I)) u0 • mkQIM (z i) = d.1 • mkQIM (z i)
      rw [hud]
    have hu_mem : mkQIM (((⟨u0, hu0⟩ : S) : R) • z i) ∈ Pq := by
      rw [hu_eq]
      exact hdmem
    exact (quotient_span_mem_iff_mem_span_sup_ideal_smul_top (I := I) x _).1 hu_mem
  choose u hu using hclear
  let t : S := Finset.univ.prod u
  have htgen : ∀ i : Fin m, t.1 • z i ∈ Qsub := by
    intro i
    have ht_eq : (t : R) = ((Finset.univ.erase i).prod fun j => (u j : R)) * (u i : R) := by
      dsimp [t]
      simpa [Finset.sdiff_singleton_eq_erase] using
        (Finset.prod_eq_prod_diff_singleton_mul (s := Finset.univ) (i := i)
          (Finset.mem_univ i) (fun j => (u j : R)))
    rw [ht_eq, mul_smul]
    exact Qsub.smul_mem _ (hu i)
  refine ⟨t, ?_⟩
  rw [← Submodule.singleton_set_smul (N := (⊤ : Submodule R M)) t.1]
  refine Submodule.set_smul_le _ _ _ ?_
  intro r y hr hy
  rcases hr with rfl
  have hyspan : y ∈ Submodule.span R (Set.range z) := by
    simpa [hz] using hy
  refine Submodule.span_induction
    (s := Set.range z)
    (p := fun y _ => t.1 • y ∈ Qsub)
    ?_ ?_ ?_ ?_ hyspan
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    exact htgen i
  · simpa using Qsub.zero_mem
  · intro y₁ y₂ _ _ hy₁ hy₂
    simpa [smul_add] using Qsub.add_mem hy₁ hy₂
  · intro a y _ hy
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using Qsub.smul_mem a hy

/-- Helper for Chap10 Lemma 10 20 2: if a submonoid multiple of `⊤` is contained in
`P ⊔ I • ⊤`, then a scalar from `S + I` sends `⊤` into `P`. -/
private lemma exists_mem_submonoid_add_ideal_and_smul_top_le_of_submonoid_smul_top_le_sup
    [Module.Finite R M] (P : Submodule R M) (t : S)
    (ht : t.1 • (⊤ : Submodule R M) ≤ P ⊔ IM) :
    ∃ f : R, f ∈ ((S : Set R) + (I : Set R)) ∧
      f • (⊤ : Submodule R M) ≤ P := by
  classical
  let Q := M ⧸ P
  let μ : Module.End R Q := (LinearMap.lsmul R Q) t.1
  have hrange : LinearMap.range μ ≤ I • (⊤ : Submodule R Q) := by
    intro q hq
    rcases hq with ⟨z, rfl⟩
    rcases P.mkQ_surjective z with ⟨m, rfl⟩
    have htm : t.1 • m ∈ P ⊔ IM := by
      exact ht (Submodule.smul_mem_pointwise_smul m t.1 (⊤ : Submodule R M) trivial)
    rcases (Submodule.mem_sup.mp htm) with ⟨p, hp, im, him, hpim⟩
    have himq : P.mkQ im ∈ I • (⊤ : Submodule R Q) := by
      exact Submodule.smul_top_le_comap_smul_top I P.mkQ him
    have hqeq : μ (P.mkQ m) = P.mkQ im := by
      calc
        μ (P.mkQ m) = P.mkQ (t.1 • m) := by simp [μ]
        _ = P.mkQ (p + im) := by rw [hpim]
        _ = P.mkQ im := by simp [map_add, hp]
    rw [hqeq]
    exact himq
  obtain ⟨p, hpmonic, hpcoeff, hpaeval⟩ :=
    LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul R μ I hrange
  let d := p.natDegree
  have hmap_p : p.map (Ideal.Quotient.mk I) = Polynomial.X ^ d := by
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
    by_cases hk : k = d
    · subst k
      simp [d, hpmonic.coeff_natDegree]
    · have hcoeffI : p.coeff k ∈ I := by
        by_cases hlt : k < d
        · exact Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hlt) (hpcoeff k)
        · have hgt : d < k := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hk)
          have hcoeff0 : p.coeff k = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by simpa [d] using hgt)
          simp [hcoeff0]
      have hqcoeff : (Ideal.Quotient.mk I) (p.coeff k) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 hcoeffI
      simp [hk, hqcoeff]
  let f : R := p.eval t.1
  have hdiffI : f - t.1 ^ d ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hquot_eval : (Ideal.Quotient.mk I) f = (Ideal.Quotient.mk I) (t.1 ^ d) := by
      dsimp [f]
      calc
        (Ideal.Quotient.mk I) (p.eval t.1)
            = Polynomial.eval ((Ideal.Quotient.mk I) t.1) (p.map (Ideal.Quotient.mk I)) := by
                rw [Polynomial.eval_map]
                exact (Polynomial.eval₂_at_apply (Ideal.Quotient.mk I) t.1).symm
        _ = Polynomial.eval ((Ideal.Quotient.mk I) t.1) (Polynomial.X ^ d) := by
              rw [hmap_p]
        _ = (Ideal.Quotient.mk I) (t.1 ^ d) := by simp
    rw [map_sub, hquot_eval, sub_self]
  have hfmem : f ∈ ((S : Set R) + (I : Set R)) := by
    refine ⟨t.1 ^ d, S.pow_mem t.2 d, f - t.1 ^ d, hdiffI, ?_⟩
    ring
  have hzero_eval : algebraMap R (Module.End R Q) f = 0 := by
    have hμ : μ = algebraMap R (Module.End R Q) t.1 := by
      apply LinearMap.ext
      intro z
      rw [Module.algebraMap_end_apply]
      rfl
    calc
      algebraMap R (Module.End R Q) f
          = Polynomial.eval₂ (algebraMap R (Module.End R Q)) μ p := by
              dsimp [f]
              rw [hμ]
              exact (Polynomial.eval₂_at_apply (algebraMap R (Module.End R Q)) t.1).symm
      _ = (Polynomial.aeval μ) p := by rw [Polynomial.aeval_def]
      _ = 0 := hpaeval
  have hfle : f • (⊤ : Submodule R M) ≤ P := by
    rw [← Submodule.singleton_set_smul (N := (⊤ : Submodule R M)) f]
    refine Submodule.set_smul_le _ _ _ ?_
    intro a m ha hm
    rcases ha with rfl
    have hz : P.mkQ (f • m) = 0 := by
      have happ := LinearMap.congr_fun hzero_eval (P.mkQ m)
      simpa using happ
    exact (Submodule.Quotient.mk_eq_zero P).1 (by simpa using hz)
  exact ⟨f, hfmem, hfle⟩

/-- Chap10 Lemma 10 20 2: if the images of finitely many elements of a finite `R`-module generate the
localization of `M / IM` at `S`, then those elements already generate some away-localization `M_f`
for an element `f ∈ S + I`. -/
@[stacks 0GLX]
theorem exists_mem_submonoid_add_ideal_and_span_localizedAway_eq_top_of_quotient_span_eq_top
    [Module.Finite R M] {n : ℕ} (x : Fin n → M)
    (hgen :
      (Submodule.span (R ⧸ I) (Set.range (mkQIM ∘ x))).localized Sbar = ⊤) :
    ∃ f : R, f ∈ ((S : Set R) + (I : Set R)) ∧
      (Submodule.span R (Set.range x)).localized (Submonoid.powers f) = ⊤ := by
  classical
  let P : Submodule R M := Submodule.span R (Set.range x)
  obtain ⟨t, ht⟩ :=
    exists_submonoid_smul_top_le_span_sup_ideal_smul_top_of_quotient_span_localized_eq_top
      (S := S) (I := I) x hgen
  obtain ⟨f, hfmem, hfle⟩ :=
    exists_mem_submonoid_add_ideal_and_smul_top_le_of_submonoid_smul_top_le_sup
      (S := S) (I := I) P t ht
  have hloc : P.localized (Submonoid.powers f) = ⊤ := by
    have hleloc := Submodule.localized'_le_localized'_of_smul_le
      (S := Localization (Submonoid.powers f))
      (p := Submonoid.powers f)
      (f := LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (P := (⊤ : Submodule R M))
      (Q := P)
      ⟨f, Submonoid.mem_powers f⟩ hfle
    rw [eq_top_iff]
    intro y hy
    exact hleloc (by simpa [Submodule.localized] using hy)
  exact ⟨f, hfmem, by simpa [P] using hloc⟩

end
