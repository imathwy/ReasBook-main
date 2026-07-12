import Mathlib
import Papers.OnSomeLocalRings_Maassaran_2025.Sections.section02_part2

namespace SomeLocalRings

variable {𝕜 : Type*} [Field 𝕜]
variable {A B : Type*} [Ring A] [Ring B] [Algebra 𝕜 A] [Algebra 𝕜 B]

/--
If `P` is irreducible and `Q` has smaller degree, then a nonzero `Q'` has no roots among the roots
of `P` in an algebraic closure.
-/
lemma derivative_nonroot_on_roots_of_irreducible_of_natDegree_lt
    (P Q : Polynomial 𝕜) (hP : Irreducible P) (hdeg : Q.natDegree < P.natDegree)
    (hQ' : Q.derivative ≠ 0) :
    ∀ α : AlgebraicClosure 𝕜,
      (P.map (algebraMap 𝕜 (AlgebraicClosure 𝕜))).IsRoot α →
        ¬ ((Q.derivative.map (algebraMap 𝕜 (AlgebraicClosure 𝕜))).IsRoot α) := by
  classical
  intro α hPα hQα
  have hnot : ¬ IsCoprime P Q.derivative := by
    intro hcop
    have hiff :=
      (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed 𝕜
        (AlgebraicClosure 𝕜) P Q.derivative).1 hcop
    have htest := hiff α
    have hP0 : (Polynomial.aeval α) P = 0 := by
      have : Polynomial.eval α (P.map (algebraMap 𝕜 (AlgebraicClosure 𝕜))) = 0 := by
        simpa [Polynomial.IsRoot] using hPα
      have : Polynomial.eval₂ (algebraMap 𝕜 (AlgebraicClosure 𝕜)) α P = 0 := by
        simpa [Polynomial.eval_map] using this
      simpa [Polynomial.aeval_def] using this
    have hQ0 : (Polynomial.aeval α) Q.derivative = 0 := by
      have : Polynomial.eval α (Q.derivative.map (algebraMap 𝕜 (AlgebraicClosure 𝕜))) = 0 := by
        simpa [Polynomial.IsRoot] using hQα
      have : Polynomial.eval₂ (algebraMap 𝕜 (AlgebraicClosure 𝕜)) α Q.derivative = 0 := by
        simpa [Polynomial.eval_map] using this
      simpa [Polynomial.aeval_def] using this
    cases htest with
    | inl h => exact h hP0
    | inr h => exact h hQ0
  have hPdvd : P ∣ Q.derivative := (hP.dvd_iff_not_isCoprime).2 hnot
  have hle : P.natDegree ≤ Q.derivative.natDegree :=
    Polynomial.natDegree_le_of_dvd hPdvd hQ'
  have hQdeg0 : Q.natDegree ≠ 0 := by
    intro hQ0
    have hQconst : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hQ0
    have : Q.derivative = 0 := by
      rw [hQconst]
      simp
    exact hQ' this
  have hdeg' : Q.derivative.natDegree < P.natDegree :=
    lt_trans (Polynomial.natDegree_derivative_lt hQdeg0) hdeg
  exact (not_lt_of_ge hle) hdeg'

/--
Proposition 2.7
Assume `𝕜` is a field and `P₁, P₂` are irreducible polynomials in `𝕜[X]`. Let
`f : 𝕜[X]/(P₁) ≃+* 𝕜[X]/(P₂)` be a ring isomorphism stabilizing `𝕜`. Let `S_f` be as in
Proposition 2.4, so that `(σ_f^X(P₁)) ∘ Q_f = S_f * P₂` for some `Q_f ∈ 𝕜[X]`. Then `S_f` is
coprime to `P₂` if and only if the formal derivative `Q_f'` is nonzero.
-/
theorem proposition_2_7
    (P₁ P₂ : Polynomial 𝕜) (hP₁ : Irreducible P₁) (hP₂ : Irreducible P₂)
    (f :
      (Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜))) ≃+*
        (Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))))
    (σ_f : 𝕜 ≃+* 𝕜)
    (hf :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
        (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁} : Set (Polynomial 𝕜)))
        (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂} : Set (Polynomial 𝕜))) f.toRingHom σ_f)
    (σX : Polynomial 𝕜 ≃+* Polynomial 𝕜)
    (hσX :
      σX Polynomial.X = Polynomial.X ∧
        RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜) (B := Polynomial 𝕜)
          σX.toRingHom σ_f)
    (Qf Sf : Polynomial 𝕜) (hQfdeg : Qf.natDegree < P₁.natDegree)
    (hSf : (σX P₁).comp Qf = Sf * P₂) :
    IsCoprime Sf P₂ ↔ Qf.derivative ≠ 0 := by
  classical
  -- Work in an algebraic closure to use root multiplicities.
  let K := AlgebraicClosure 𝕜
  let i : 𝕜 →+* K := algebraMap 𝕜 K
  let p : Polynomial K := (σX P₁).map i
  let P : Polynomial K := P₂.map i
  let s : Polynomial K := Sf.map i
  let q : Polynomial K := Qf.map i
  have hp0 : p ≠ 0 := by
    have : σX P₁ ≠ 0 := by
      simpa using (σX.injective.ne_iff.2 hP₁.ne_zero)
    simpa [p] using (Polynomial.map_ne_zero (f := i) this)
  have hP0 : P ≠ 0 := by
    simpa [P] using (Polynomial.map_ne_zero (f := i) hP₂.ne_zero)
  have hcompK : p.comp q = s * P := by
    simpa [p, q, s, P, Polynomial.map_comp, map_mul] using congrArg (Polynomial.map i) hSf
  have hdeg₁₂ : P₁.natDegree = P₂.natDegree :=
    prop2_4_natDegree_eq (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf
  have hσX_eq : σX = Polynomial.mapEquiv σ_f :=
    polynomialRingEquiv_eq_mapEquiv_of_fix_X_of_stabilizesBaseFieldWith (𝕜 := 𝕜) σ_f σX
      hσX.1 hσX.2
  have hdegσ : (σX P₁).natDegree = P₁.natDegree := by
    simp [hσX_eq, Polynomial.mapEquiv_apply]
  have hdegpP : p.natDegree = P.natDegree := by
    simp [p, P, Polynomial.natDegree_map_eq_of_injective (RingHom.injective i), hdegσ, hdeg₁₂]
  have hdegqP : Qf.natDegree < P₂.natDegree := by
    simpa [hdeg₁₂] using hQfdeg
  have hP6 :=
    proposition_2_6 (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf σX hσX Qf Sf hSf
  have hroot_map :
      ∀ {α : K}, (P₂.map i).IsRoot α →
        ((σX P₁).map i).IsRoot ((Polynomial.aeval α) Qf) := by
    intro α hα
    have hα' : (P₂.map (algebraMap 𝕜 K)).IsRoot α := by
      simpa [i] using hα
    have h := hP6.1 (K := K) (α := α) hα'
    simpa [i] using h
  rcases hP6.2 with ⟨e, he⟩
  have sum_rootMultiplicity_eq_natDegree (r : Polynomial K) :
      (∑ a ∈ r.roots.toFinset, Polynomial.rootMultiplicity a r) = r.natDegree := by
    classical
    have hcard : r.natDegree = r.roots.card :=
      Polynomial.Splits.natDegree_eq_card_roots (f := r) (IsAlgClosed.splits r)
    calc
      (∑ a ∈ r.roots.toFinset, Polynomial.rootMultiplicity a r)
          = ∑ a ∈ r.roots.toFinset, r.roots.count a := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              simp
      _ = r.roots.card := by
              simpa using (Multiset.toFinset_sum_count_eq r.roots)
      _ = r.natDegree := by
              simp [hcard]
  have sum_eval_rootMultiplicity_eq_natDegree_p :
      (∑ a ∈ P.roots.toFinset,
      Polynomial.rootMultiplicity (Polynomial.eval a q) p) = p.natDegree := by
    classical
    have hP_isRoot_of_mem : ∀ {a : K}, a ∈ P.roots.toFinset → P.IsRoot a := by
      intro a ha
      have : a ∈ P.roots := by simpa [Multiset.mem_toFinset] using ha
      exact (Polynomial.mem_roots hP0).1 this
    have hP_mem_of_isRoot : ∀ {a : K}, P.IsRoot a → a ∈ P.roots.toFinset := by
      intro a ha
      have : a ∈ P.roots := (Polynomial.mem_roots hP0).2 ha
      simpa [Multiset.mem_toFinset] using this
    have hp_isRoot_of_mem : ∀ {b : K}, b ∈ p.roots.toFinset → p.IsRoot b := by
      intro b hb
      have : b ∈ p.roots := by simpa [Multiset.mem_toFinset] using hb
      exact (Polynomial.mem_roots hp0).1 this
    have hp_mem_of_isRoot : ∀ {b : K}, p.IsRoot b → b ∈ p.roots.toFinset := by
      intro b hb
      have : b ∈ p.roots := (Polynomial.mem_roots hp0).2 hb
      simpa [Multiset.mem_toFinset] using this
    have hsum_bij :
        (∑ a ∈ P.roots.toFinset, Polynomial.rootMultiplicity (Polynomial.eval a q) p) =
          (∑ b ∈ p.roots.toFinset, Polynomial.rootMultiplicity b p) := by
      classical
      refine Finset.sum_bij
        (s := P.roots.toFinset) (t := p.roots.toFinset)
        (f := fun a => Polynomial.rootMultiplicity (Polynomial.eval a q) p)
        (g := fun b => Polynomial.rootMultiplicity b p)
        (i := fun a ha => (e ⟨a, hP_isRoot_of_mem ha⟩).1)
        (hi := ?_) (i_inj := ?_) (i_surj := ?_) (h := ?_)
      · intro a ha
        exact hp_mem_of_isRoot (e ⟨a, hP_isRoot_of_mem ha⟩).2
      · intro a₁ ha₁ a₂ ha₂ hEq
        have h₁ : P.IsRoot a₁ := hP_isRoot_of_mem ha₁
        have h₂ : P.IsRoot a₂ := hP_isRoot_of_mem ha₂
        have : e ⟨a₁, h₁⟩ = e ⟨a₂, h₂⟩ := by
          ext
          simpa using hEq
        have : (⟨a₁, h₁⟩ : {x : K // P.IsRoot x}) = ⟨a₂, h₂⟩ := e.injective this
        simpa using congrArg Subtype.val this
      · intro b hb
        have hb' : p.IsRoot b := hp_isRoot_of_mem hb
        refine ⟨(e.symm ⟨b, hb'⟩).1, ?_⟩
        refine ⟨hP_mem_of_isRoot (e.symm ⟨b, hb'⟩).2, ?_⟩
        have heq : e (e.symm ⟨b, hb'⟩) = ⟨b, hb'⟩ := e.apply_symm_apply ⟨b, hb'⟩
        -- Align the root proof coming from membership with the one coming from `e.symm`.
        have hsub :
            (⟨(e.symm ⟨b, hb'⟩).1,
                hP_isRoot_of_mem (hP_mem_of_isRoot (e.symm ⟨b, hb'⟩).2)⟩ :
              {x : K // P.IsRoot x}) =
              (e.symm ⟨b, hb'⟩) := by
          ext
          rfl
        have hval : (e (e.symm ⟨b, hb'⟩)).1 = b := congrArg Subtype.val heq
        have hval' :
            (e
                (⟨(e.symm ⟨b, hb'⟩).1,
                    hP_isRoot_of_mem (hP_mem_of_isRoot (e.symm ⟨b, hb'⟩).2)⟩ :
                  {x : K // P.IsRoot x})).1 =
              (e (e.symm ⟨b, hb'⟩)).1 :=
          congrArg Subtype.val (congrArg e hsub)
        exact hval'.trans hval
      · intro a ha
        have hE :
            (e ⟨a, hP_isRoot_of_mem ha⟩).1 = (Polynomial.aeval a) Qf :=
          he ⟨a, hP_isRoot_of_mem ha⟩
        have hEval : (Polynomial.aeval a) Qf = Polynomial.eval a q := by
          simp [q, i, Polynomial.aeval_def, Polynomial.eval_map]
        -- `f a = g (i a ha)` after rewriting the image.
        simp [hE.trans hEval]
    simpa [hsum_bij] using (sum_rootMultiplicity_eq_natDegree p)
  have hP₂_natDegree_ne_zero : P₂.natDegree ≠ 0 := by
    intro h0
    have hconst : P₂ = Polynomial.C (P₂.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    have hcoeff0 : P₂.coeff 0 ≠ 0 := by
      intro hc
      have : P₂ = 0 := by
        calc
          P₂ = Polynomial.C (P₂.coeff 0) := hconst
          _ = Polynomial.C 0 := by simp [hc]
          _ = 0 := by simp
      exact hP₂.ne_zero this
    have hunitC : IsUnit (Polynomial.C (P₂.coeff 0)) :=
      (Polynomial.isUnit_C).2 ((isUnit_iff_ne_zero).2 hcoeff0)
    have : IsUnit P₂ := by
      rw [hconst]
      exact hunitC
    exact hP₂.not_isUnit this
  have hP_natDegree_pos : 0 < P.natDegree := by
    have : P.natDegree ≠ 0 := by
      simpa [P, Polynomial.natDegree_map_eq_of_injective (RingHom.injective i)]
        using hP₂_natDegree_ne_zero
    exact Nat.pos_of_ne_zero this
  constructor
  · intro hcop
    have hcopK : IsCoprime s P := by
      -- Map coprimality from `𝕜[X]` to `K[X]`.
      simpa [s, P] using (hcop.map (Polynomial.mapRingHom i))
    have hs0 : s ≠ 0 := by
      intro hs0
      rcases hcopK with ⟨u, v, huv⟩
      have hunit : IsUnit P := by
        refine (isUnit_iff_exists_inv').2 ?_
        refine ⟨v, ?_⟩
        simpa [hs0] using huv
      exact (Polynomial.not_isUnit_of_natDegree_pos P hP_natDegree_pos) hunit
    have hmul_ne : s * P ≠ 0 := mul_ne_zero hs0 hP0
    have hs_notroot : ∀ α : K, P.IsRoot α → ¬ s.IsRoot α := by
      intro α hPα hsα
      rcases hcopK with ⟨u, v, huv⟩
      have huv' := congrArg (Polynomial.eval α) huv
      have hs0' : Polynomial.eval α s = 0 := by simpa [Polynomial.IsRoot] using hsα
      have hP0' : Polynomial.eval α P = 0 := by simpa [Polynomial.IsRoot] using hPα
      have : (0 : K) = 1 := by
        convert huv' using 1 <;> simp [Polynomial.eval_add, Polynomial.eval_mul, hs0', hP0']
      exact zero_ne_one this
    have hRM_s_zero :
        ∀ α : K, P.IsRoot α → Polynomial.rootMultiplicity α s = 0 := by
      intro α hPα
      exact Polynomial.rootMultiplicity_eq_zero (hs_notroot α hPα)
    by_contra hQ'
    have hQ0 : Qf.derivative = 0 := by
      simpa using hQ'
    have hqder0 : q.derivative = 0 := by
      simp [q, hQ0, Polynomial.derivative_map]
    have hineq :
        ∀ α : K, α ∈ P.roots.toFinset →
          2 * Polynomial.rootMultiplicity (Polynomial.eval α q) p ≤
            Polynomial.rootMultiplicity α P := by
      intro α hα
      have hPα : P.IsRoot α := by
        have : α ∈ P.roots := by simpa [Multiset.mem_toFinset] using hα
        exact (Polynomial.mem_roots hP0).1 this
      have hRM_P_pos : 0 < Polynomial.rootMultiplicity α P :=
        (Polynomial.rootMultiplicity_pos hP0).2 (by simpa [Polynomial.IsRoot] using hPα)
      have hRM_comp :
          Polynomial.rootMultiplicity α (p.comp q) =
            Polynomial.rootMultiplicity (Polynomial.eval α q) p *
              Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) :=
        rootMultiplicity_comp_eq_mul (p := p) (q := q) (a := α) hp0
      have hRM_mul :
          Polynomial.rootMultiplicity α (s * P) =
            Polynomial.rootMultiplicity α s + Polynomial.rootMultiplicity α P :=
        Polynomial.rootMultiplicity_mul (x := α) hmul_ne
      have hEq :
          Polynomial.rootMultiplicity (Polynomial.eval α q) p *
              Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) =
            Polynomial.rootMultiplicity α P := by
        have hRM_s : Polynomial.rootMultiplicity α s = 0 := hRM_s_zero α hPα
        have hEq' :
            Polynomial.rootMultiplicity (Polynomial.eval α q) p *
                Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) =
              Polynomial.rootMultiplicity α s + Polynomial.rootMultiplicity α P := by
          simpa [hRM_comp, hRM_mul] using congrArg (Polynomial.rootMultiplicity α) hcompK
        simpa [hRM_s] using hEq'
      have hp_root : p.IsRoot (Polynomial.eval α q) := by
        have hPα' : (P₂.map i).IsRoot α := by simpa [P] using hPα
        have hp_root' : p.IsRoot ((Polynomial.aeval α) Qf) := by
          have : ((σX P₁).map i).IsRoot ((Polynomial.aeval α) Qf) := hroot_map (α := α) hPα'
          simpa [p] using this
        have hEval : (Polynomial.aeval α) Qf = Polynomial.eval α q := by
          simp [q, i, Polynomial.aeval_def, Polynomial.eval_map]
        simpa [hEval] using hp_root'
      have hRM_eval_pos : 0 < Polynomial.rootMultiplicity (Polynomial.eval α q) p :=
        (Polynomial.rootMultiplicity_pos hp0).2 (by simpa [Polynomial.IsRoot] using hp_root)
      have hRM_sub_ne_one :
          Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) ≠ 1 := by
        intro h1
        have hnotroot :
            ¬ q.derivative.IsRoot α :=
          (rootMultiplicity_sub_C_eval_eq_one_iff (q := q) (a := α)).1 h1
        exact hnotroot (by simp [hqder0, Polynomial.IsRoot])
      have hRM_sub_pos :
          0 < Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) := by
        have :
            0 < Polynomial.rootMultiplicity (Polynomial.eval α q) p *
                Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) := by
          simpa [hEq] using hRM_P_pos
        exact Nat.pos_of_mul_pos_left this
      have hRM_sub_ge_two :
          2 ≤ Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) := by
        have hge1 : 1 ≤ Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) :=
          Nat.succ_le_iff.2 hRM_sub_pos
        have hgt1 : 1 < Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) :=
          lt_of_le_of_ne hge1 (Ne.symm hRM_sub_ne_one)
        exact (Nat.succ_le_iff).2 hgt1
      have hle :
          Polynomial.rootMultiplicity (Polynomial.eval α q) p * 2 ≤
            Polynomial.rootMultiplicity (Polynomial.eval α q) p *
              Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) :=
        Nat.mul_le_mul_left _ hRM_sub_ge_two
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, hEq] using hle
    have hsum_le :
        (∑ α ∈ P.roots.toFinset, 2 * Polynomial.rootMultiplicity (Polynomial.eval α q) p) ≤
          (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α P) := by
      refine Finset.sum_le_sum ?_
      intro α hα
      exact hineq α hα
    have hdeg_le : 2 * p.natDegree ≤ P.natDegree := by
      have hsum_le' :
          2 * (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity (Polynomial.eval α q) p) ≤
            (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α P) := by
        simpa [Finset.mul_sum, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum_le
      simpa [sum_eval_rootMultiplicity_eq_natDegree_p, sum_rootMultiplicity_eq_natDegree]
        using hsum_le'
    have hmul_le : 2 * P.natDegree ≤ P.natDegree := by
      simpa [hdegpP] using hdeg_le
    have : P.natDegree = 0 :=
      Nat.eq_zero_of_mul_le (by decide : 2 ≤ 2) (by simpa [Nat.mul_comm] using hmul_le)
    exact (Nat.ne_of_gt hP_natDegree_pos) this
  · intro hQ'
    have hQ'K : q.derivative ≠ 0 := by
      have : (Qf.derivative.map i) ≠ 0 := Polynomial.map_ne_zero (f := i) hQ'
      simpa [q, Polynomial.derivative_map] using this
    have hq_nonconst : q ≠ Polynomial.C (q.coeff 0) := by
      intro hqC
      have : q.derivative = 0 := by
        rw [hqC]
        simp
      exact hQ'K (by simpa using this)
    have hpcomp : p.comp q ≠ 0 := by
      intro h0
      rcases (Polynomial.comp_eq_zero_iff (p := p) (q := q)).1 h0 with hp | hrest
      · exact hp0 hp
      · exact hq_nonconst hrest.2
    have hmul_ne : s * P ≠ 0 := by
      simpa [hcompK] using hpcomp
    have hs0 : s ≠ 0 := by
      intro hs0
      exact hmul_ne (by simp [hs0])
    have hRM_q_one :
        ∀ α : K, P.IsRoot α →
          Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) = 1 := by
      intro α hPα
      have hPα' : (P₂.map i).IsRoot α := by simpa [P] using hPα
      have hnot : ¬ ((Qf.derivative.map i).IsRoot α) :=
        derivative_nonroot_on_roots_of_irreducible_of_natDegree_lt (𝕜 := 𝕜)
          (P := P₂) (Q := Qf) hP₂ hdegqP hQ' α hPα'
      have hnot' : ¬ q.derivative.IsRoot α := by
        simpa [q, Polynomial.derivative_map] using hnot
      exact (rootMultiplicity_sub_C_eval_eq_one_iff (q := q) (a := α)).2 hnot'
    have hEq_root :
        ∀ α : K, P.IsRoot α →
          Polynomial.rootMultiplicity (Polynomial.eval α q) p =
            Polynomial.rootMultiplicity α s + Polynomial.rootMultiplicity α P := by
      intro α hPα
      have hRM_comp :
          Polynomial.rootMultiplicity α (p.comp q) =
            Polynomial.rootMultiplicity (Polynomial.eval α q) p *
              Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) :=
        rootMultiplicity_comp_eq_mul (p := p) (q := q) (a := α) hp0
      have hRM_mul :
          Polynomial.rootMultiplicity α (s * P) =
            Polynomial.rootMultiplicity α s + Polynomial.rootMultiplicity α P :=
        Polynomial.rootMultiplicity_mul (x := α) hmul_ne
      have hEq :
          Polynomial.rootMultiplicity (Polynomial.eval α q) p *
              Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) =
            Polynomial.rootMultiplicity α s + Polynomial.rootMultiplicity α P := by
        simpa [hRM_comp, hRM_mul] using congrArg (Polynomial.rootMultiplicity α) hcompK
      simpa [hRM_q_one α hPα] using hEq
    have hsum_eq :
        (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity (Polynomial.eval α q) p) =
          (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α s) +
            (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α P) := by
      classical
      have :
          (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity (Polynomial.eval α q) p) =
            (∑ α ∈ P.roots.toFinset,
              (Polynomial.rootMultiplicity α s + Polynomial.rootMultiplicity α P)) := by
        refine Finset.sum_congr rfl ?_
        intro α hα
        have hPα : P.IsRoot α := by
          have : α ∈ P.roots := by simpa [Multiset.mem_toFinset] using hα
          exact (Polynomial.mem_roots hP0).1 this
        simpa using hEq_root α hPα
      simpa [Finset.sum_add_distrib] using this
    have hsum_s :
        (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α s) = 0 := by
      have hsumP :
          (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α P) = P.natDegree :=
        sum_rootMultiplicity_eq_natDegree P
      have hsump :
          (∑ α ∈ P.roots.toFinset,
          Polynomial.rootMultiplicity (Polynomial.eval α q) p) = p.natDegree :=
        sum_eval_rootMultiplicity_eq_natDegree_p
      have hmain :
          p.natDegree =
            (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α s) + P.natDegree := by
        calc
          p.natDegree
              = (∑ α ∈ P.roots.toFinset,
                Polynomial.rootMultiplicity (Polynomial.eval α q) p) := hsump.symm
          _ = (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α s) +
                (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α P) := hsum_eq
          _ = (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α s) + P.natDegree := by
                simp [hsumP]
      have hmain' :
          0 + P.natDegree =
            (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α s) + P.natDegree := by
        simpa [hdegpP] using hmain
      have : 0 = (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α s) :=
        Nat.add_right_cancel hmain'
      simpa using this.symm
    have hRM_s_zero :
        ∀ α : K, α ∈ P.roots.toFinset → Polynomial.rootMultiplicity α s = 0 := by
      have hiff :
          (∑ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α s) = 0 ↔
            ∀ α ∈ P.roots.toFinset, Polynomial.rootMultiplicity α s = 0 :=
        (Finset.sum_eq_zero_iff
          (s := P.roots.toFinset) (f := fun α => Polynomial.rootMultiplicity α s))
      exact hiff.1 hsum_s
    have hnotdvd : ¬ P₂ ∣ Sf := by
      intro hdiv
      have hdivK : P ∣ s := by
        have : (P₂.map i) ∣ (Sf.map i) :=
          (Polynomial.map_dvd_map' (f := i) (x := P₂) (y := Sf)).2 hdiv
        simpa [P, s] using this
      have hdegP0 : P.degree ≠ 0 := by
        intro hdeg0
        have hle : P.degree ≤ 0 := le_of_eq hdeg0
        have : P.natDegree = 0 := (Polynomial.natDegree_eq_zero_iff_degree_le_zero).2 hle
        exact (Nat.ne_of_gt hP_natDegree_pos) this
      rcases IsAlgClosed.exists_root (p := P) hdegP0 with ⟨α, hαroot⟩
      have hαmem : α ∈ P.roots.toFinset := by
        have : α ∈ P.roots := (Polynomial.mem_roots hP0).2 hαroot
        simpa [Multiset.mem_toFinset] using this
      rcases hdivK with ⟨t, ht⟩
      have hsroot : s.IsRoot α := by
        -- `s = P * t` and `P(α) = 0`.
        have : Polynomial.eval α s = 0 := by
          calc
            Polynomial.eval α s = Polynomial.eval α (P * t) := by simp [ht]
            _ = Polynomial.eval α P * Polynomial.eval α t := by
                  simp [Polynomial.eval_mul]
            _ = 0 := by
                  have hαP : Polynomial.eval α P = 0 := by
                    simpa [Polynomial.IsRoot] using hαroot
                  simp [hαP]
        simpa [Polynomial.IsRoot] using this
      have hpos : 0 < Polynomial.rootMultiplicity α s :=
        (Polynomial.rootMultiplicity_pos hs0).2 hsroot
      have : Polynomial.rootMultiplicity α s = 0 := hRM_s_zero α hαmem
      exact (Nat.ne_of_gt hpos) this
    have : IsCoprime P₂ Sf := (hP₂.isCoprime_or_dvd Sf).resolve_right hnotdvd
    exact this.symm

  /-
  -- Work in an algebraic closure to use root multiplicities.
  let K := AlgebraicClosure 𝕜
  let i : 𝕜 →+* K := algebraMap 𝕜 K
  let p : Polynomial K := (σX P₁).map i
  let P : Polynomial K := P₂.map i
  let s : Polynomial K := Sf.map i
  let q : Polynomial K := Qf.map i
  have hp0 : p ≠ 0 := by
    simpa [p] using (Polynomial.map_ne_zero.2 (σX.injective.ne_iff.2 hP₁.ne_zero))
  have hP0 : P ≠ 0 := by
    simpa [P] using (Polynomial.map_ne_zero.2 hP₂.ne_zero)
  have hcompK : p.comp q = s * P := by
    simpa [p, q, s, P, Polynomial.map_comp, map_mul] using congrArg (Polynomial.map i) hSf
  -- Degree comparison `natDegree P₁ = natDegree P₂`, and thus `natDegree q < natDegree P`.
  have hdeg₁₂ : P₁.natDegree = P₂.natDegree :=
    prop2_4_natDegree_eq (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf
  have hσX_eq : σX = Polynomial.mapEquiv σ_f :=
    polynomialRingEquiv_eq_mapEquiv_of_fix_X_of_stabilizesBaseFieldWith (𝕜 := 𝕜) σ_f σX
      hσX.1 hσX.2
  have hdegσ : (σX P₁).natDegree = P₁.natDegree := by
    simp [hσX_eq, Polynomial.mapEquiv_apply]
  have hdegqP : Qf.natDegree < P₂.natDegree := by
    simpa [hdeg₁₂] using hQfdeg

  -- Root bijection from Proposition 2.6 (in `K`).
  have hroots :=
    (proposition_2_6 (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf σX hσX Qf Sf hSf).2
  rcases hroots with ⟨e, he⟩

  -- A technical lemma: roots of `P₂` do not kill `Qf'` if `Qf' ≠ 0` and `deg Qf < deg P₂`.
  have hderiv_nonroot (hQ' : Qf.derivative ≠ 0) :
      ∀ α : K, (P.map i).IsRoot α → ¬ ((Qf.derivative.map i).IsRoot α) := by
    -- Note: `P.map i = P₂.map i` since `P = P₂.map i`; we keep the explicit `P₂` form.
    simpa [P, K, i] using
      derivative_nonroot_on_roots_of_irreducible_of_natDegree_lt (𝕜 := 𝕜)
        (P := P₂) (Q := Qf) hP₂ hdegqP hQ'

  constructor
  · intro hcop
    -- If `Qf' = 0`, then `Sf` cannot be coprime to `P₂` (degree/multiplicity obstruction).
    by_contra hQ'
    -- Map coprimality to `K[X]` and use the root criterion.
    have hcopK : IsCoprime s P := hcop.map i
    -- Choose a root `α` of `P` in `K`.
    have hdegP0 : P.degree ≠ 0 := by
      have hPdeg : 0 < P.natDegree := by
        -- An irreducible polynomial over a field is nonconstant.
        have : P₂.natDegree ≠ 0 := by
          intro h0
          have hconst : P₂ = Polynomial.C (P₂.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
          exact hP₂.not_unit (by simpa [hconst] using (Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2
            (Polynomial.coeff_C_ne_zero.2 (Polynomial.ne_zero_of_irreducible hP₂)))))
        -- Transfer to `K`.
        have hnat : P.natDegree = P₂.natDegree := by
          simpa [P] using (Polynomial.natDegree_map_eq_of_injective (algebraMap 𝕜 K)
            (RingHom.injective (algebraMap 𝕜 K)) (p := P₂))
        have : 0 < P.natDegree := Nat.pos_of_ne_zero (by simpa [hnat] using this)
        exact this
      -- `degree ≠ 0` follows from `natDegree > 0`.
      have : P.degree = (P.natDegree : WithBot ℕ) := by
        simpa [Polynomial.degree_eq_natDegree hP0]
      -- `0 < natDegree` implies `degree ≠ 0`.
      have : (P.degree ≠ 0) := by
        intro hdeg0
        have : P.natDegree = 0 := by
          -- If `degree = 0`, then `natDegree = 0`.
          have : (P.degree ≤ 0) := le_of_eq hdeg0
          exact (Polynomial.natDegree_eq_zero_iff_degree_le_zero).2 this
        exact Nat.lt_asymm hPdeg (by simpa [this] using Nat.lt_succ_self 0)
      exact this
    rcases IsAlgClosed.exists_root (p := P) hdegP0 with ⟨α, hαroot⟩
    -- Use the root criterion for coprimality to get that `s` does not vanish at `α`.
    have hsα :
        (Polynomial.aeval α) s ≠ 0 := by
      -- If `P(α)=0` then coprimality forces `s(α)≠0`.
      have hiff :=
        (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := 𝕜) (K := K) (p := Sf) (q := P₂)).1 hcop
      -- Rewrite in terms of mapped polynomials.
      have hPα : (Polynomial.aeval α) (P₂.map i) = 0 := by
        simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval₂_at, Polynomial.eval_map] using hαroot
      have hcase := hiff α
      cases hcase with
      | inl hs => simpa [s, Polynomial.aeval_def, Polynomial.eval₂_at, Polynomial.eval_map] using hs
      | inr hPne => exact (hPne (by simpa [P, Polynomial.aeval_def, Polynomial.eval₂_at, Polynomial.eval_map] using hPα)).elim
    -- But `Qf' = 0` contradicts coprimality via the multiplicity sum argument; we get a contradiction by
    -- showing `Qf'` must be nonzero from a root where the derivative does not vanish.
    -- Since `hQ' : ¬ Qf.derivative ≠ 0`, we have `Qf.derivative = 0`.
    have hQ0 : Qf.derivative = 0 := by
      classical
      by_contra hne
      exact hQ' hne
    -- Evaluate at `α` to see the derivative vanishes, contradicting `hsα` via the factorization argument.
    have : (Polynomial.aeval α) (Qf.derivative.map i) = 0 := by
      simp [hQ0]
    -- From the factorization argument below (implemented in the other direction), `s(α) ≠ 0` forces
    -- the derivative not to vanish at any root of `P`, contradiction.
    have hcontra :
        ¬ ((Qf.derivative.map i).IsRoot α) := by
      -- A root of `P` is mapped by `e` to a root of `p`, hence `q - C (q.eval α)` has multiplicity ≥ 1,
      -- and coprimality forces it to be exactly `1`.
      -- We reuse the general argument from the other direction by contradiction: if the derivative vanishes,
      -- then `rootMultiplicity` would be > 1.
      intro hroot
      -- Use `rootMultiplicity_sub_C_eval_eq_one_iff` to show the root multiplicity is not `1`.
      have hmul :
          Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) ≠ 1 := by
        have hiff :=
          (rootMultiplicity_sub_C_eval_eq_one_iff (q := q) (a := α)).1
        -- If `rootMultiplicity = 1` then the derivative does not vanish; but it does by `hroot`.
        intro heq
        have : ¬ (q.derivative.IsRoot α) := by
          exact (rootMultiplicity_sub_C_eval_eq_one_iff (q := q) (a := α)).1 (by simpa [q] using heq)
        -- Contradiction.
        exact this (by
          -- `q.derivative = (Qf.derivative).map i`.
          simpa [q, Polynomial.derivative_map] using hroot)
      -- But coprimality gives `rootMultiplicity α s = 0` so the multiplicity equation forces
      -- `rootMultiplicity ... = 1`, contradiction.
      have hsroot : ¬ s.IsRoot α := by
        intro hs0
        have : (Polynomial.aeval α) s = 0 := by
          simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hs0
        exact hsα (by simpa [Polynomial.aeval_def] using this)
      have hRM_s : Polynomial.rootMultiplicity α s = 0 :=
        Polynomial.rootMultiplicity_eq_zero hsroot
      have hRM_P : 0 < Polynomial.rootMultiplicity α P := by
        have : P.IsRoot α := hαroot
        exact (Polynomial.rootMultiplicity_pos hP0).2 (by simpa [Polynomial.IsRoot] using this)
      -- Root multiplicity of `p.comp q` at `α`.
      have hRM_comp :
          Polynomial.rootMultiplicity α (p.comp q) =
            Polynomial.rootMultiplicity (Polynomial.eval α q) p *
              Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) :=
        rootMultiplicity_comp_eq_mul (p := p) (q := q) (a := α) hp0
      -- Compare with `s * P`.
      have hmul_ne : s * P ≠ 0 := mul_ne_zero (by
        -- `s` is nonzero since it does not vanish at `α`.
        intro hs0
        have : (Polynomial.aeval α) s = 0 := by simpa [hs0]
        exact hsα this) hP0
      have hRM_mul :
          Polynomial.rootMultiplicity α (s * P) =
            Polynomial.rootMultiplicity α s + Polynomial.rootMultiplicity α P :=
        Polynomial.rootMultiplicity_mul (x := α) hmul_ne
      have hRM_eq : Polynomial.rootMultiplicity α (p.comp q) =
          Polynomial.rootMultiplicity α s + Polynomial.rootMultiplicity α P := by
        simpa [hcompK, hRM_mul] using congrArg (Polynomial.rootMultiplicity α) hcompK
      -- Since `P` contributes positively, this forces the other factor to be `1`, contradiction.
      have hbpos : 0 < Polynomial.rootMultiplicity (Polynomial.eval α q) p := by
        -- `Polynomial.eval α q` is a root of `p` by Proposition 2.6.
        have hαP2 : (P₂.map i).IsRoot α := by
          simpa [P] using hαroot
        have hroot' :=
          (proposition_2_6 (𝕜 := 𝕜) P₁ P₂ hP₁ hP₂ f σ_f hf σX hσX Qf Sf hSf).1 (K := K)
            (α := α) (by simpa [P] using hαP2)
        exact (Polynomial.rootMultiplicity_pos hp0).2 (by
          simpa [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def, q] using hroot')
      have hRM_q :
          Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) = 1 := by
        -- From `rm_p * rm_q = rm_s + rm_P` and `rm_s = 0`, deduce `rm_q = 1` by comparing sums.
        have hRM_eq' :
            Polynomial.rootMultiplicity (Polynomial.eval α q) p *
                Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) =
              Polynomial.rootMultiplicity α P := by
          -- Use `rm_s = 0`.
          have : Polynomial.rootMultiplicity α (p.comp q) =
              Polynomial.rootMultiplicity α P := by
            -- `rm_s = 0` implies `rm_comp = rm_P`.
            have hmul_ne : s * P ≠ 0 := mul_ne_zero (by
              intro hs0
              have : (Polynomial.aeval α) s = 0 := by simpa [hs0]
              exact hsα this) hP0
            have hRM_mul :
                Polynomial.rootMultiplicity α (s * P) =
                  Polynomial.rootMultiplicity α s + Polynomial.rootMultiplicity α P :=
              Polynomial.rootMultiplicity_mul (x := α) hmul_ne
            have hRM_mul0 : Polynomial.rootMultiplicity α (s * P) =
                Polynomial.rootMultiplicity α P := by
              simpa [hRM_s] using congrArg (fun n => n + Polynomial.rootMultiplicity α P) rfl
            -- Put together.
            simpa [hcompK, hRM_mul, hRM_s] using (congrArg (Polynomial.rootMultiplicity α) hcompK)
          -- Use the composition formula.
          simpa [hRM_comp] using this
        -- Now `rm_q` must be `1` since `rm_P = rm_p * rm_q` and degrees match.
        -- We only need that `rm_q` is positive to conclude `rm_q = 1` is forced by `hmul`.
        have hposq : 0 < Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) := by
          -- Otherwise the product would be zero.
          have : q - Polynomial.C (Polynomial.eval α q) ≠ 0 := by
            intro hz
            have : Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) = 0 := by
              simp [hz]
            have : Polynomial.rootMultiplicity α P = 0 := by
              simpa [this] using hRM_eq'
            exact (Nat.ne_of_gt hRM_P) this
          exact (Polynomial.rootMultiplicity_pos this).2 (by
            simp [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_eval, rfl])
        have hgeq : 1 ≤ Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) :=
          Nat.succ_le_iff.2 hposq
        -- If it were ≥ 2 then the product would be strictly larger than `rm_P`.
        have : Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) = 1 := by
          rcases Nat.lt_or_eq_of_le hgeq with hlt | heq
          · -- `1 < rm_q` impossible since then `rm_p * rm_q > rm_p`, but `rm_P = rm_p * rm_q`.
            have : Polynomial.rootMultiplicity (Polynomial.eval α q) p <
                Polynomial.rootMultiplicity (Polynomial.eval α q) p *
                  Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) := by
              exact Nat.lt_mul_of_one_lt_right hbpos hlt
            have hle : Polynomial.rootMultiplicity (Polynomial.eval α q) p *
                  Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) ≤
                Polynomial.rootMultiplicity α P := by
              exact le_of_eq hRM_eq'
            exact (not_lt_of_ge hle) this |>.elim
          · exact heq.symm
        exact this
      exact hmul (by simpa [hRM_q] using rfl)
    exact hcontra (by
      -- Turn the evaluation statement into an `IsRoot`.
      simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval₂_at, Polynomial.eval_map] using this)
  · intro hQ'
    -- If `Qf' ≠ 0`, show `Sf` and `P₂` are coprime by summing root multiplicities.
    -- In `K[X]`, show that every root `α` of `P` has `rootMultiplicity α s = 0`.
    have hno_deriv_root :
        ∀ α : K, P.IsRoot α → ¬ ((Qf.derivative.map i).IsRoot α) := by
      intro α hα
      have hα' : (P₂.map i).IsRoot α := by simpa [P] using hα
      exact hderiv_nonroot hQ' α hα'
    have hRM_q_one (α : K) (hα : P.IsRoot α) :
        Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) = 1 := by
      have hnot : ¬ (q.derivative.IsRoot α) := by
        -- `q.derivative = (Qf.derivative).map i`.
        have : ¬ ((Qf.derivative.map i).IsRoot α) := hno_deriv_root α hα
        simpa [q, Polynomial.derivative_map] using this
      exact (rootMultiplicity_sub_C_eval_eq_one_iff (q := q) (a := α)).2 hnot
    -- Compare root multiplicities at roots of `P`.
    have hsum :
        (∑ x ∈ P.roots.toFinset, Polynomial.rootMultiplicity x s) = 0 := by
      -- For each root `α` of `P`, we have `rm_p(β) = rm_s(α) + rm_P(α)` where `β = e(α)`.
      have hRM_point (α : K) (hα : α ∈ P.roots.toFinset) :
          Polynomial.rootMultiplicity ((e ⟨α, (by
              have : α ∈ P.roots := (Multiset.mem_toFinset.1 hα)
              simpa [Polynomial.mem_roots hP0] using this)⟩).1) p =
            Polynomial.rootMultiplicity α s + Polynomial.rootMultiplicity α P := by
        have hαroot : P.IsRoot α := by
          have : α ∈ P.roots := (Multiset.mem_toFinset.1 hα)
          simpa [Polynomial.mem_roots hP0] using this
        -- Use `rootMultiplicity_comp_eq_mul` and `hcompK`.
        have hmul_ne : s * P ≠ 0 := mul_ne_zero (by
          intro hs0
          -- If `s=0`, then `p.comp q = 0`, impossible since `p ≠ 0` and `q` nonconstant (since `Qf' ≠ 0`).
          have : p.comp q = 0 := by simpa [hcompK, hs0]
          have : p = 0 ∨ (Polynomial.eval (q.coeff 0) p = 0 ∧ q = Polynomial.C (q.coeff 0)) :=
            (Polynomial.comp_eq_zero_iff (p := p) (q := q)).1 this
          cases this with
          | inl hp => exact hp0 hp
          | inr h => exact (by
            -- A constant `q` would force `Qf.derivative = 0`.
            have : q.derivative = 0 := by
              rcases h with ⟨_, hqconst⟩
              simpa [hqconst] using (Polynomial.derivative_C (a := q.coeff 0) : (Polynomial.C (q.coeff 0)).derivative = 0)
            have : Qf.derivative = 0 := by
              -- Use injectivity of `map`.
              apply Polynomial.map_injective i (RingHom.injective i)
              simpa [q, Polynomial.derivative_map] using this
            exact hQ' this) )
        have hRM_mul :
            Polynomial.rootMultiplicity α (s * P) =
              Polynomial.rootMultiplicity α s + Polynomial.rootMultiplicity α P :=
          Polynomial.rootMultiplicity_mul (x := α) hmul_ne
        have hRM_eq : Polynomial.rootMultiplicity α (p.comp q) =
              Polynomial.rootMultiplicity α s + Polynomial.rootMultiplicity α P := by
          simpa [hcompK, hRM_mul] using congrArg (Polynomial.rootMultiplicity α) hcompK
        have hRM_comp :
            Polynomial.rootMultiplicity α (p.comp q) =
              Polynomial.rootMultiplicity (Polynomial.eval α q) p *
                Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) :=
          rootMultiplicity_comp_eq_mul (p := p) (q := q) (a := α) hp0
        have hb : (e ⟨α, hαroot⟩).1 = Polynomial.eval α q := by
          -- `he` gives `(e a).1 = aeval a.1 Qf`, and this equals `eval α q`.
          have := he ⟨α, hαroot⟩
          simpa [q, Polynomial.aeval_def, Polynomial.eval₂_at, Polynomial.eval_map] using this
        -- Use that `rootMultiplicity` of `q - C (q.eval α)` is `1`.
        have hq1 : Polynomial.rootMultiplicity α (q - Polynomial.C (Polynomial.eval α q)) = 1 :=
          hRM_q_one α hαroot
        -- Put together and simplify.
        simpa [hRM_eq, hRM_comp, hb, hq1, Nat.mul_one]
      -- Sum over all roots of `P`.
      have hsum_left :
          (∑ x ∈ P.roots.toFinset,
              Polynomial.rootMultiplicity ((e ⟨x, (by
                have : x ∈ P.roots := (Multiset.mem_toFinset.1 ‹x ∈ P.roots.toFinset›)
                simpa [Polynomial.mem_roots hP0] using this)⟩).1) p) =
            (∑ y ∈ p.roots.toFinset, Polynomial.rootMultiplicity y p) := by
        -- Use `Finset.sum_bij` with the bijection of roots given by `e`.
        refine Finset.sum_bij
          (i := fun x hx => (e ⟨x, (by
            have : x ∈ P.roots := (Multiset.mem_toFinset.1 hx)
            simpa [Polynomial.mem_roots hP0] using this)⟩).1)
          (hi := ?_) (i_inj := ?_) (i_surj := ?_) (h := ?_)
        · intro x hx
          -- Image is a root of `p`.
          have hxroot : P.IsRoot x := by
            have : x ∈ P.roots := (Multiset.mem_toFinset.1 hx)
            simpa [Polynomial.mem_roots hP0] using this
          have hyroot : p.IsRoot (e ⟨x, hxroot⟩).1 := (e ⟨x, hxroot⟩).2
          -- Convert `IsRoot` to membership in `roots.toFinset`.
          have : (e ⟨x, hxroot⟩).1 ∈ p.roots := by
            simpa [Polynomial.mem_roots hp0] using hyroot
          simpa [Multiset.mem_toFinset] using this
        · intro x₁ hx₁ x₂ hx₂ hEq
          have hx₁root : P.IsRoot x₁ := by
            have : x₁ ∈ P.roots := (Multiset.mem_toFinset.1 hx₁)
            simpa [Polynomial.mem_roots hP0] using this
          have hx₂root : P.IsRoot x₂ := by
            have : x₂ ∈ P.roots := (Multiset.mem_toFinset.1 hx₂)
            simpa [Polynomial.mem_roots hP0] using this
          have : e ⟨x₁, hx₁root⟩ = e ⟨x₂, hx₂root⟩ := by
            ext
            simpa using hEq
          simpa using congrArg Subtype.val (e.injective this)
        · intro y hy
          -- Surjectivity: use `e.symm`.
          have hyroot : p.IsRoot y := by
            have : y ∈ p.roots := (Multiset.mem_toFinset.1 hy)
            simpa [Polynomial.mem_roots hp0] using this
          let x := (e.symm ⟨y, hyroot⟩).1
          have hxroot : P.IsRoot x := (e.symm ⟨y, hyroot⟩).2
          have hxmem : x ∈ P.roots.toFinset := by
            have : x ∈ P.roots := by
              simpa [Polynomial.mem_roots hP0] using hxroot
            simpa [Multiset.mem_toFinset] using this
          refine ⟨x, hxmem, ?_⟩
          -- Show the image is exactly `y`.
          have : e ⟨x, hxroot⟩ = ⟨y, hyroot⟩ := by
            simpa [x] using (e.apply_symm_apply ⟨y, hyroot⟩)
          simpa using congrArg Subtype.val this
        · intro x hx
          rfl
      have hsum_p :
          (∑ y ∈ p.roots.toFinset, Polynomial.rootMultiplicity y p) = p.roots.card := by
        simpa [Polynomial.count_roots] using (Multiset.toFinset_sum_count_eq (s := p.roots))
      have hsum_P :
          (∑ x ∈ P.roots.toFinset, Polynomial.rootMultiplicity x P) = P.roots.card := by
        simpa [Polynomial.count_roots] using (Multiset.toFinset_sum_count_eq (s := P.roots))
      have hp_card : p.roots.card = p.natDegree := card_roots_eq_natDegree (k := K) (p := p)
      have hP_card : P.roots.card = P.natDegree := card_roots_eq_natDegree (k := K) (p := P)
      -- Now sum `hRM_point` and use the degree equality to force the `s`-sum to be `0`.
      have :
          (∑ x ∈ P.roots.toFinset,
              Polynomial.rootMultiplicity ((e ⟨x, (by
                have : x ∈ P.roots := (Multiset.mem_toFinset.1 ‹x ∈ P.roots.toFinset›)
                simpa [Polynomial.mem_roots hP0] using this)⟩).1) p) =
            (∑ x ∈ P.roots.toFinset,
                (Polynomial.rootMultiplicity x s + Polynomial.rootMultiplicity x P)) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        simpa using hRM_point x hx
      have hsump :
          (∑ x ∈ P.roots.toFinset,
              Polynomial.rootMultiplicity ((e ⟨x, (by
                have : x ∈ P.roots := (Multiset.mem_toFinset.1 ‹x ∈ P.roots.toFinset›)
                simpa [Polynomial.mem_roots hP0] using this)⟩).1) p) =
            p.natDegree := by
        calc
          _ = (∑ y ∈ p.roots.toFinset, Polynomial.rootMultiplicity y p) := hsum_left
          _ = p.roots.card := hsum_p
          _ = p.natDegree := hp_card
      have hsumPdeg :
          (∑ x ∈ P.roots.toFinset, Polynomial.rootMultiplicity x P) = P.natDegree := by
        calc
          _ = P.roots.card := hsum_P
          _ = P.natDegree := hP_card
      -- Use `p.natDegree = P.natDegree`.
      have hdegpP : p.natDegree = P.natDegree := by
        -- `natDegree` is preserved by `map` (injective) and `σX` has same degree as `P₁`.
        have hpdeg : p.natDegree = (σX P₁).natDegree := by
          simpa [p] using (Polynomial.natDegree_map_eq_of_injective i (RingHom.injective i) (p := σX P₁))
        have hPdeg : P.natDegree = P₂.natDegree := by
          simpa [P] using (Polynomial.natDegree_map_eq_of_injective i (RingHom.injective i) (p := P₂))
        simpa [hpdeg, hPdeg, hdegσ, hdeg₁₂]
      -- Finish by rewriting the sum of a sum.
      have hsum_add :
          (∑ x ∈ P.roots.toFinset,
              (Polynomial.rootMultiplicity x s + Polynomial.rootMultiplicity x P)) =
            (∑ x ∈ P.roots.toFinset, Polynomial.rootMultiplicity x s) +
              (∑ x ∈ P.roots.toFinset, Polynomial.rootMultiplicity x P) := by
        simp [Finset.sum_add_distrib]
      -- Put everything together.
      have : (∑ x ∈ P.roots.toFinset, Polynomial.rootMultiplicity x s) = p.natDegree - P.natDegree := by
        -- Use the equation of sums and rearrange.
        have := congrArg (fun n => n) (hsump.trans (this.trans (by
          simp [hsum_add, hsumPdeg])))
        -- At this point `simp` handles the arithmetic.
        simpa [hdegpP] using (by
          -- `hsump` already gives equality to `p.natDegree`.
          -- Rewrite and isolate.
          have : p.natDegree =
              (∑ x ∈ P.roots.toFinset, Polynomial.rootMultiplicity x s) + P.natDegree := by
            -- from `hsump` and `this` and `hsumPdeg`
            simpa [hsum_add, hsumPdeg] using (hsump.trans (this.trans rfl))
          -- isolate the sum
          exact Nat.add_left_cancel (by simpa using this))
      simpa [hdegpP] using this
    -- Now translate the vanishing of root multiplicities into coprimality.
    -- Use the root characterization in the algebraic closure.
    have hcopK : IsCoprime s P := by
      -- Use `isCoprime_iff_aeval_ne_zero_of_isAlgClosed`.
      have hiff :=
        (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := 𝕜) (K := K) (p := Sf) (q := P₂)).2
      refine hiff ?_
      intro α
      by_cases hPα : (P.map i).IsRoot α
      · -- If `P(α)=0`, then `s(α)≠0` since the root multiplicity of `s` at `α` is zero.
        have hmem : α ∈ P.roots.toFinset := by
          have : α ∈ P.roots := by
            simpa [Polynomial.mem_roots hP0] using hPα
          simpa [Multiset.mem_toFinset] using this
        have hRM0 : Polynomial.rootMultiplicity α s = 0 := by
          -- If the multiplicity were positive, it would contribute to the sum.
          have : (∑ x ∈ P.roots.toFinset, Polynomial.rootMultiplicity x s) = 0 := hsum
          have hle : Polynomial.rootMultiplicity α s ≤
              (∑ x ∈ P.roots.toFinset, Polynomial.rootMultiplicity x s) := by
            exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
          exact Nat.eq_zero_of_le_zero (le_trans hle (by simpa [this]))
        have hsα : (Polynomial.aeval α) s ≠ 0 := by
          intro hs0
          have hsroot : s.IsRoot α := by
            simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hs0
          have hpos : 0 < Polynomial.rootMultiplicity α s :=
            (Polynomial.rootMultiplicity_pos (by
              intro hsZ
              simpa [hsZ] using (Polynomial.rootMultiplicity_eq_zero (p := s) (x := α) (by
                intro; exact False.elim ?_)))).2 (by
              simpa [Polynomial.IsRoot] using hsroot)
          exact Nat.ne_of_gt hpos hRM0
        exact Or.inl (by simpa [s, Polynomial.aeval_def, Polynomial.eval₂_at, Polynomial.eval_map] using hsα)
      · exact Or.inr (by
          -- If `P(α) ≠ 0`, then `P₂(α) ≠ 0`.
          have hP2 : (Polynomial.aeval α) (P₂.map i) ≠ 0 := by
            intro h0
            apply hPα
            simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval₂_at, Polynomial.eval_map] using h0
          simpa [P, Polynomial.aeval_def, Polynomial.eval₂_at, Polynomial.eval_map] using hP2)
    -- Finally, bring back to `𝕜[X]`.
    -- Since `algebraMap` is injective, coprimality reflects.
    exact (isCoprime_of_isCoprime_map_of_injective i (RingHom.injective i)).1 hcopK
-/

/--
If a ring homomorphism `fX : 𝕜[X] → 𝕜[X]` stabilizes the base field via `σ_f`, then the induced
quotient map `𝕜[X]/(P₁^n) → 𝕜[X]/(P₂^n)` also stabilizes the base field via `σ_f`.
-/
lemma stabilizesBaseFieldWith_quotientMap_pow
    (P₁ P₂ : Polynomial 𝕜) (n : ℕ) (fX : Polynomial 𝕜 →+* Polynomial 𝕜) (σ_f : 𝕜 ≃+* 𝕜)
    (hfX :
      RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜) (A := Polynomial 𝕜) (B := Polynomial 𝕜) fX σ_f)
    (hIJn :
      (Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)) : Ideal (Polynomial 𝕜)) ≤
        Ideal.comap fX (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))) :
    RingHom.StabilizesBaseFieldWith (𝕜 := 𝕜)
      (A := Polynomial 𝕜 ⧸ Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
      (B := Polynomial 𝕜 ⧸ Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))
      (Ideal.quotientMap (I := Ideal.span ({P₁ ^ n} : Set (Polynomial 𝕜)))
        (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜))) fX hIJn)
      σ_f := by
  intro a
  simpa [RingHom.StabilizesBaseFieldWith, Ideal.quotientMap_mk, Ideal.Quotient.mk_algebraMap] using
    congrArg (Ideal.Quotient.mk (Ideal.span ({P₂ ^ n} : Set (Polynomial 𝕜)))) (hfX a)

end SomeLocalRings
