import Mathlib
import stacks_project.Chap10.Definition_10_153_1
import stacks_project.Chap10.Lemma_10_106_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open IsLocalRing Polynomial

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable (R : I → Type u) [∀ i, CommRing (R i)]
variable (φ : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R (φ · · ·)]
variable [∀ i j hij, IsLocalHom (φ i j hij)]

local notation "R∞" => Ring.DirectLimit R (fun i j h ↦ φ i j h)

/-- Helper for Lemma 10.154.8: any finite family of elements of the direct limit already appears at
one stage. -/
lemma exists_stage_family :
    ∀ n : ℕ, ∀ a : Fin n → R∞, ∃ i, ∃ b : Fin n → R i, ∀ m, Ring.DirectLimit.of R (φ · · ·) i (b m) = a m
  | 0, a => by
      let i : I := Classical.arbitrary I
      refine ⟨i, fun m => Fin.elim0 m, ?_⟩
      intro m
      exact Fin.elim0 m
  | n + 1, a => by
      -- Descend the tail first, then enlarge to a common upper bound with the head coefficient.
      obtain ⟨i, b, hb⟩ := exists_stage_family n (fun m : Fin n ↦ a m.succ)
      obtain ⟨j, x, hx⟩ := Ring.DirectLimit.exists_of (G := R) (f := fun i j h ↦ φ i j h) (a 0)
      obtain ⟨k, hjk, hik⟩ := exists_ge_ge j i
      refine ⟨k, Fin.cons (φ j k hjk x) (fun m ↦ φ i k hik (b m)), ?_⟩
      intro m
      refine Fin.cases ?_ ?_ m
      · simpa using (show Ring.DirectLimit.of R (φ · · ·) k (φ j k hjk x) = a 0 by
          rw [Ring.DirectLimit.of_f, hx])
      · intro m
        simpa using (show Ring.DirectLimit.of R (φ · · ·) k (φ i k hik (b m)) = a m.succ by
          rw [Ring.DirectLimit.of_f, hb m])

/-- Helper for Lemma 10.154.8: a monic polynomial over the direct limit is already defined over one
stage by a monic polynomial. -/
lemma exists_stage_monic_polynomial (f : R∞[X]) (hf : f.Monic) :
    ∃ i, ∃ f_i : (R i)[X], f_i.Monic ∧ Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i) f_i = f := by
  -- Descend the coefficients below the top degree and rebuild the stage polynomial via
  -- `Monic.as_sum`, which preserves monicity by construction.
  let n := f.natDegree
  obtain ⟨i, c, hc⟩ := exists_stage_family R φ n (fun m ↦ f.coeff m)
  let f_i : (R i)[X] := X ^ n + Finset.univ.sum (fun m : Fin n ↦ C (c m) * X ^ (m : ℕ))
  refine ⟨i, f_i, ?_, ?_⟩
  · -- The lower-degree tail has degree `< n`, so adjoining `X ^ n` yields a monic polynomial.
    have hdeg :
        degree (∑ m : Fin n, C (c m) * X ^ (m : ℕ)) < n :=
      degree_sum_fin_lt (fun m ↦ c m)
    dsimp [f_i]
    exact monic_X_pow_add hdeg
  · -- Map the rebuilt stage polynomial to the direct limit and compare with `Monic.as_sum`.
    dsimp [f_i]
    calc
      Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i)
          (X ^ n + Finset.univ.sum (fun m : Fin n ↦ C (c m) * X ^ (m : ℕ)))
          = X ^ n + Finset.univ.sum (fun m : Fin n ↦ C (f.coeff (m : ℕ)) * X ^ (m : ℕ)) := by
              simp [Polynomial.map_add, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow,
                hc]
      _ = X ^ n + Finset.sum (Finset.range n) (fun m ↦ C (f.coeff m) * X ^ m) := by
            simpa using
              ((Fin.sum_univ_eq_sum_range (fun m ↦ C (f.coeff m) * X ^ m)) n)
      _ = f := by
            simpa [n] using hf.as_sum.symm

section ResidueField

variable [∀ i, IsLocalRing (R i)]

/-- Helper for Lemma 10.154.8: the induced maps on stage residue fields form a directed system. -/
instance residueFieldDirectedSystem :
    DirectedSystem (fun i : I => ResidueField (R i))
      (fun i j hij => IsLocalRing.ResidueField.map (φ i j hij)) where
  map_self := by
    intro i x
    have hφ : φ i i le_rfl = RingHom.id (R i) := by
      ext y
      simpa using (DirectedSystem.map_self' (f := φ) y)
    simpa [hφ] using (IsLocalRing.ResidueField.map_id_apply (R := R i) x)
  map_map := by
    intro k j i hij hjk x
    have hφ :
        (φ j k hjk).comp (φ i j hij) = φ i k (hij.trans hjk) := by
      ext y
      simpa using (DirectedSystem.map_map' (f := φ) hij hjk y)
    calc
      IsLocalRing.ResidueField.map (φ j k hjk) (IsLocalRing.ResidueField.map (φ i j hij) x)
          = IsLocalRing.ResidueField.map ((φ j k hjk).comp (φ i j hij)) x := by
              simpa using (IsLocalRing.ResidueField.map_map (φ i j hij) (φ j k hjk) x)
      _ = IsLocalRing.ResidueField.map (φ i k (hij.trans hjk)) x := by
            simpa [hφ]

/-- Helper for Lemma 10.154.8: every residue-field element of the direct limit comes from one stage
residue field. -/
lemma exists_stage_residue_field_element (a₀ : ResidueField R∞) :
    ∃ i, ∃ a_i : ResidueField (R i),
      IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i) a_i = a₀ := by
  -- Lift the residue-field element to the direct-limit ring, then descend that ring element.
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective a₀
  obtain ⟨i, x_i, hx_i⟩ := Ring.DirectLimit.exists_of (G := R) (f := fun i j h ↦ φ i j h) x
  refine ⟨i, IsLocalRing.residue (R i) x_i, ?_⟩
  calc
    IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i) (IsLocalRing.residue (R i) x_i)
        = IsLocalRing.residue R∞ (Ring.DirectLimit.of R (φ · · ·) i x_i) := by
            exact IsLocalRing.ResidueField.map_residue
              (Ring.DirectLimit.of R (φ · · ·) i) x_i
    _ = IsLocalRing.residue R∞ x := by rw [hx_i]

/-- Helper for Lemma 10.154.8: every polynomial over the direct-limit residue field is already
defined over one stage residue field. -/
lemma exists_stage_residue_polynomial (g : (ResidueField R∞)[X]) :
    ∃ i, ∃ g_i : (ResidueField (R i))[X],
      Polynomial.map (IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)) g_i = g := by
  -- Descend coefficients by polynomial induction, combining stages via directedness.
  induction g using Polynomial.induction_on with
  | C a =>
      obtain ⟨i, a_i, ha_i⟩ := exists_stage_residue_field_element R φ a
      refine ⟨i, C a_i, ?_⟩
      simpa [ha_i]
  | add g₁ g₂ ih₁ ih₂ =>
      obtain ⟨i₁, g₁i, hg₁i⟩ := ih₁
      obtain ⟨i₂, g₂i, hg₂i⟩ := ih₂
      obtain ⟨i, h₁i, h₂i⟩ := exists_ge_ge i₁ i₂
      let g_i : (ResidueField (R i))[X] :=
        g₁i.map (IsLocalRing.ResidueField.map (φ i₁ i h₁i))
          + g₂i.map (IsLocalRing.ResidueField.map (φ i₂ i h₂i))
      have hcomp₁ :
          (Ring.DirectLimit.of R (φ · · ·) i).comp (φ i₁ i h₁i)
            = Ring.DirectLimit.of R (φ · · ·) i₁ := by
        ext x
        simp [Ring.DirectLimit.of_f]
      have hcomp₂ :
          (Ring.DirectLimit.of R (φ · · ·) i).comp (φ i₂ i h₂i)
            = Ring.DirectLimit.of R (φ · · ·) i₂ := by
        ext x
        simp [Ring.DirectLimit.of_f]
      refine ⟨i, g_i, ?_⟩
      dsimp [g_i]
      have hrescomp₁ :
          (IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)).comp
              (IsLocalRing.ResidueField.map (φ i₁ i h₁i))
            = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i₁) := by
        ext x
        calc
          IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
              (IsLocalRing.ResidueField.map (φ i₁ i h₁i) x)
              = IsLocalRing.ResidueField.map
                  ((Ring.DirectLimit.of R (φ · · ·) i).comp (φ i₁ i h₁i)) x := by
                    simpa using (IsLocalRing.ResidueField.map_map
                      (φ i₁ i h₁i) (Ring.DirectLimit.of R (φ · · ·) i) x)
          _ = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i₁) x := by
                simpa [hcomp₁]
      have hrescomp₂ :
          (IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)).comp
              (IsLocalRing.ResidueField.map (φ i₂ i h₂i))
            = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i₂) := by
        ext x
        calc
          IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
              (IsLocalRing.ResidueField.map (φ i₂ i h₂i) x)
              = IsLocalRing.ResidueField.map
                  ((Ring.DirectLimit.of R (φ · · ·) i).comp (φ i₂ i h₂i)) x := by
                    simpa using (IsLocalRing.ResidueField.map_map
                      (φ i₂ i h₂i) (Ring.DirectLimit.of R (φ · · ·) i) x)
          _ = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i₂) x := by
                simpa [hcomp₂]
      rw [Polynomial.map_add, Polynomial.map_map, Polynomial.map_map, hrescomp₁, hrescomp₂, hg₁i, hg₂i]
  | monomial n a _ =>
      obtain ⟨i, a_i, ha_i⟩ := exists_stage_residue_field_element R φ a
      refine ⟨i, C a_i * X ^ (n + 1), ?_⟩
      simp [ha_i, Polynomial.map_mul, Polynomial.map_pow]

/-- Helper for Lemma 10.154.8: simple roots over the residue field of the direct limit descend to
one stage and lift there. -/
lemma directedSystem_directLimit_simple_root_lift
    [∀ i, HenselianLocalRing (R i)] :
    ∀ f : R∞[X], f.Monic → ∀ a₀ : ResidueField R∞, aeval a₀ f = 0 →
      aeval a₀ (Polynomial.derivative f) ≠ 0 →
      ∃ a : R∞, f.IsRoot a ∧ IsLocalRing.residue R∞ a = a₀ := by
  intro f hf a₀ ha₀ hderiv
  -- Descend the monic polynomial and the residue-field root to a common stage.
  obtain ⟨i_f, f_i, hf_i_monic, hf_i⟩ := exists_stage_monic_polynomial R φ f hf
  obtain ⟨i_a, a_i, ha_i⟩ := exists_stage_residue_field_element R φ a₀
  obtain ⟨i, hfi, hai⟩ := exists_ge_ge i_f i_a
  let f_stage : (R i)[X] := f_i.map (φ i_f i hfi)
  let a_stage : ResidueField (R i) := IsLocalRing.ResidueField.map (φ i_a i hai) a_i
  have hcomp_f :
      (Ring.DirectLimit.of R (φ · · ·) i).comp (φ i_f i hfi)
        = Ring.DirectLimit.of R (φ · · ·) i_f := by
    ext x
    simp [Ring.DirectLimit.of_f]
  have hcomp_a :
      (Ring.DirectLimit.of R (φ · · ·) i).comp (φ i_a i hai)
        = Ring.DirectLimit.of R (φ · · ·) i_a := by
    ext x
    simp [Ring.DirectLimit.of_f]
  have hf_stage :
      Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i) f_stage = f := by
    dsimp [f_stage]
    rw [Polynomial.map_map, hcomp_f, hf_i]
  have ha_stage :
      IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i) a_stage = a₀ := by
    dsimp [a_stage]
    calc
      IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
          (IsLocalRing.ResidueField.map (φ i_a i hai) a_i)
          = IsLocalRing.ResidueField.map
              ((Ring.DirectLimit.of R (φ · · ·) i).comp (φ i_a i hai)) a_i := by
                simpa using (IsLocalRing.ResidueField.map_map
                  (φ i_a i hai) (Ring.DirectLimit.of R (φ · · ·) i) a_i)
      _ = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i_a) a_i := by
            simpa [hcomp_a]
      _ = a₀ := ha_i
  have hψ_injective :
      Function.Injective
        (IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)) :=
    RingHom.injective _
  have hroot_stage_map :
      IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i) (aeval a_stage f_stage) = 0 := by
    have hroot_stage_eq :
        IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i) (aeval a_stage f_stage)
          = aeval a₀ f := by
      simpa [hf_stage, ha_stage] using
        (Polynomial.map_aeval_eq_aeval_map
          (φ := Ring.DirectLimit.of R (φ · · ·) i)
          (ψ := IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i))
          (h := (IsLocalRing.ResidueField.map_comp_residue
            (Ring.DirectLimit.of R (φ · · ·) i)).symm)
          (p := f_stage) (a := a_stage))
    exact hroot_stage_eq.trans ha₀
  have hroot_stage : aeval a_stage f_stage = 0 := by
    apply hψ_injective
    simpa using hroot_stage_map
  have hderiv_stage_map :
      IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
        (aeval a_stage (Polynomial.derivative f_stage))
        = aeval a₀ (Polynomial.derivative f) := by
    have hderiv_stage_eq :
        IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
          (aeval a_stage (Polynomial.derivative f_stage))
          = aeval a₀ (Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i)
              (Polynomial.derivative f_stage)) := by
      simpa [ha_stage] using
      (Polynomial.map_aeval_eq_aeval_map
        (φ := Ring.DirectLimit.of R (φ · · ·) i)
        (ψ := IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i))
        (h := (IsLocalRing.ResidueField.map_comp_residue
          (Ring.DirectLimit.of R (φ · · ·) i)).symm)
        (p := Polynomial.derivative f_stage) (a := a_stage))
    have hmap_deriv :
        Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i) (Polynomial.derivative f_stage)
          = Polynomial.derivative f := by
      calc
        Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i) (Polynomial.derivative f_stage)
            = Polynomial.derivative (Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i) f_stage) := by
                simpa using
                  (Polynomial.derivative_map
                    (p := f_stage) (f := Ring.DirectLimit.of R (φ · · ·) i))
        _ = Polynomial.derivative f := by rw [hf_stage]
    calc
      IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
        (aeval a_stage (Polynomial.derivative f_stage))
          = aeval a₀ (Polynomial.map (Ring.DirectLimit.of R (φ · · ·) i)
              (Polynomial.derivative f_stage)) := hderiv_stage_eq
      _ = aeval a₀ (Polynomial.derivative f) := by rw [hmap_deriv]
  have hderiv_stage : aeval a_stage (Polynomial.derivative f_stage) ≠ 0 := by
    intro hzero
    apply hderiv
    rw [← hderiv_stage_map, hzero, map_zero]
  have hstage_lift :
      ∀ g : (R i)[X], g.Monic → ∀ b : ResidueField (R i), aeval b g = 0 →
        aeval b (Polynomial.derivative g) ≠ 0 →
        ∃ x : R i, g.IsRoot x ∧ IsLocalRing.residue (R i) x = b :=
    ((HenselianLocalRing.TFAE (R i)).out 0 1).mp
      (show HenselianLocalRing (R i) from inferInstance)
  obtain ⟨x_i, hx_i, hres_i⟩ := hstage_lift f_stage (hf_i_monic.map (φ i_f i hfi))
    a_stage hroot_stage hderiv_stage
  refine ⟨Ring.DirectLimit.of R (φ · · ·) i x_i, ?_, ?_⟩
  · -- Map the lifted stage root forward to the direct limit.
    rw [← hf_stage]
    exact hx_i.map
  · -- Compare residues through the induced residue-field map of the canonical cocone map.
    calc
      IsLocalRing.residue R∞ (Ring.DirectLimit.of R (φ · · ·) i x_i)
          = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
              (IsLocalRing.residue (R i) x_i) := by
                symm
                exact IsLocalRing.ResidueField.map_residue
                  (Ring.DirectLimit.of R (φ · · ·) i) x_i
      _ = IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i) a_stage := by
            rw [hres_i]
      _ = a₀ := ha_stage

/-- Helper for Lemma 10.154.8: if every stage is strictly henselian, then the residue field of the
direct limit is separably algebraically closed. -/
lemma isSepClosed_residueField_directLimit
    [∀ i, StrictHenselianLocalRing (R i)] : IsSepClosed (ResidueField R∞) := by
  -- Descend one separable polynomial to a stage, solve it there, and map the root forward.
  refine (IsSepClosed.of_exists_root (k := ResidueField R∞)) ?_
  intro p hpmonic hpirr hpsep
  obtain ⟨i, p_i, hp_i⟩ := exists_stage_residue_polynomial R φ p
  let ψ : ResidueField (R i) →+* ResidueField R∞ :=
    IsLocalRing.ResidueField.map (Ring.DirectLimit.of R (φ · · ·) i)
  have hψ_injective : Function.Injective ψ := RingHom.injective ψ
  have hpdeg_i : p_i.degree ≠ 0 := by
    intro hpzero
    have hpzero' : p.degree = 0 := by
      rw [← hp_i, Polynomial.degree_map_eq_of_injective hψ_injective, hpzero]
    exact (degree_pos_of_irreducible hpirr).ne' hpzero'
  have hpsep_i : p_i.Separable := by
    have hpsep_map : (p_i.map ψ).Separable := by simpa [ψ, hp_i] using hpsep
    exact (Polynomial.separable_map ψ).mp hpsep_map
  obtain ⟨x_i, hx_i⟩ := IsSepClosed.exists_root p_i hpdeg_i hpsep_i
  refine ⟨ψ x_i, ?_⟩
  have hx_map : (p_i.map ψ).eval (ψ x_i) = 0 := by
    calc
      (p_i.map ψ).eval (ψ x_i) = ψ (p_i.eval x_i) := by
        simpa using (Polynomial.eval_map_apply (p := p_i) ψ x_i)
      _ = 0 := by rw [hx_i, map_zero]
  simpa [ψ, hp_i] using hx_map

end ResidueField

-- Proof sketch: reuse the upstream direct-limit local-ring instance from Lemma `10.106.8` to put
-- a local-ring structure on `R∞`. For Hensel lifting, descend a monic polynomial over `R∞` and a
-- simple root in the residue field to a sufficiently large stage, apply the henselian property
-- there, and map the lifted root forward to the colimit.
/-- Lemma 10.154.8 (1): a filtered colimit of henselian local rings along local homomorphisms is
henselian. -/
instance directedSystem_directLimit_henselianLocalRing
    [∀ i, HenselianLocalRing (R i)] : HenselianLocalRing R∞ := by
  -- Use the residue-field formulation of Hensel's lemma and the direct stagewise descent above.
  exact ((HenselianLocalRing.TFAE R∞).out 1 0).mp
    (directedSystem_directLimit_simple_root_lift R φ)

-- Proof sketch: identify the residue field of `R∞` with the filtered colimit of the stage residue
-- fields along the induced maps; then every separable polynomial over the colimit residue field is
-- defined over some stage residue field, where it already splits because that field is separably
-- algebraically closed. Together with part (1), this gives the canonical Chapter 10 owner
-- `StrictHenselianLocalRing`.
/-- Lemma 10.154.8 (2): if the stage local rings are strictly henselian, then the filtered colimit
is strictly henselian; equivalently, its residue field is separably algebraically closed. -/
instance directedSystem_directLimit_strictHenselianLocalRing
    [∀ i, StrictHenselianLocalRing (R i)] : StrictHenselianLocalRing R∞ := by
  refine { toHenselianLocalRing := inferInstance, toIsSepClosed := ?_ }
  -- The strictness reduces to separable closedness of the direct-limit residue field.
  exact isSepClosed_residueField_directLimit R φ

end
