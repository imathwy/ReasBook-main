import StacksProject_2024.Chap10.Remark_10_69_7_Other_types_of_regular_sequences.SingletonDifferential

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Set
open scoped Pointwise TensorProduct

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the finite-family carried by a
cons list is the canonical `Fin.cons` head-plus-tail family. -/
theorem cons_list_get_eq_fin_cons {A : Type u} [CommRing A] (r : A) (rs : List A) :
    (r :: rs).get = Fin.cons r rs.get := by
  -- Proof comment: the zeroth entry is the head `r`, and every successor index reads from the
  -- tail list.
  ext i
  cases i using Fin.cases with
  | zero =>
      rfl
  | succ j =>
      rfl

/-- Helper for Remark 10.69.7 (Other types of regular sequences): mapping a cons list through a
ring homomorphism and then passing to the canonical finite family gives the expected `Fin.cons`
description. -/
theorem cons_map_list_get_eq_fin_cons {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (r : A) (rs : List A) :
    ((r :: rs).map φ).get = Fin.cons (φ r) ((rs.map φ).get) := by
  -- Proof comment: after mapping, the list still has head `φ r` and tail `rs.map φ`, so the
  -- canonical finite family is the same `Fin.cons` family as before.
  simpa using cons_list_get_eq_fin_cons (A := B) (r := φ r) (rs := rs.map φ)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the principal quotient module
`A / (r)` is canonically the same `A`-module as `QuotSMulTop r A`. -/
noncomputable def principal_quotient_linearEquiv_quotSMulTop
    {A : Type u} [CommRing A] (r : A) :
    QuotSMulTop r A ≃ₗ[A] A ⧸ Ideal.span ({r} : Set A) := by
  -- Proof comment: both sides are quotients of the regular module `A` by the same principal
  -- submodule, presented once as `r • ⊤` and once as `Ideal.span {r}`.
  refine Submodule.quotEquivOfEq _ _ ?_
  calc
    r • (⊤ : Submodule A A) = (Ideal.span ({r} : Set A) : Ideal A) • (⊤ : Submodule A A) := by
      simpa using (Submodule.ideal_span_singleton_smul r (⊤ : Submodule A A)).symm
    _ = (Ideal.span ({r} : Set A) : Ideal A) := by
      simpa using (Ideal.smul_top_eq_map (R := A) (S := A) (Ideal.span ({r} : Set A)))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): in positive degree, exactness of
the coefficient chain complex is equivalent to function exactness of the adjacent differentials. -/
theorem functionExact_of_exactAt_of_pos_degree {A : Type u} [CommRing A]
    (K : ChainComplex (ModuleCat A) ℕ) {j : ℕ} (hj : 1 ≤ j) (h : K.ExactAt j) :
    Function.Exact (K.d (j + 1) j).hom (K.d j (j - 1)).hom := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hsc : (K.sc' (k + 2) (k + 1) k).Exact := by
    -- Proof comment: rewrite exactness at degree `k + 1` to the explicit adjacent window
    -- `K.X (k + 2) → K.X (k + 1) → K.X k`.
    rw [← HomologicalComplex.exactAt_iff' (K := K) (i := k + 2) (j := k + 1) (k := k)]
    · exact h
    · simp
    · simp
  -- Proof comment: on `ModuleCat`, exactness of the short complex is exactly function exactness of
  -- the underlying linear maps.
  exact (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hsc

/-- Helper for Remark 10.69.7 (Other types of regular sequences): over `ModuleCat`, function
exactness of the underlying maps is exactly exactness of the short complex. -/
theorem shortComplex_exact_of_functionExact {A : Type u} [CommRing A]
    (S : ShortComplex (ModuleCat A)) (h : Function.Exact S.f.hom S.g.hom) :
    S.Exact := by
  -- Proof comment: this is the standard `ModuleCat` identification of categorical exactness with
  -- exactness of the underlying linear maps.
  exact (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr h

/-- Helper for Remark 10.69.7 (Other types of regular sequences): exactness of a normalized short
complex transports back to exactness at the corresponding degree of the ambient chain complex. -/
theorem exactAt_of_sc_iso_exact {A : Type u} [CommRing A]
    {T : ChainComplex (ModuleCat A) ℕ} {i : ℕ} {S : ShortComplex (ModuleCat A)}
    (e : T.sc i ≅ S) (hS : S.Exact) :
    T.ExactAt i := by
  -- Proof comment: rewrite exactness at degree `i` as exactness of `T.sc i`, then transport it
  -- across the given short-complex isomorphism.
  rw [HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_iso e.symm hS

/-- Helper for Remark 10.69.7 (Other types of regular sequences): exactness of an explicit
three-term `sc'` window transports back to exactness at the corresponding degree of the ambient
chain complex. -/
theorem exactAt_of_sc'_iso_exact {A : Type u} [CommRing A]
    {T : ChainComplex (ModuleCat A) ℕ} {i j k : ℕ} {S : ShortComplex (ModuleCat A)}
    (hi : (ComplexShape.down ℕ).prev j = i) (hk : (ComplexShape.down ℕ).next j = k)
    (e : T.sc' i j k ≅ S) (hS : S.Exact) :
    T.ExactAt j := by
  -- Proof comment: rewrite exactness at degree `j` as exactness of the explicit three-term
  -- window `T.sc' i j k`, then transport exactness across the given isomorphism.
  rw [HomologicalComplex.exactAt_iff' (K := T) (i := i) (j := j) (k := k) hi hk]
  exact ShortComplex.exact_of_iso e.symm hS

/-- Helper for Remark 10.69.7 (Other types of regular sequences): every tensorized Koszul term
inherits `r`-regularity from the coefficient module, because the Koszul term is a finite free
module. -/
theorem isSMulRegular_tensor_koszul_term_of_isSMulRegular {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] {r : A} {m : ℕ} (f : Fin m → A) (n : ℕ)
    (hr : IsSMulRegular M r) :
    IsSMulRegular
      (((HomologicalComplex.tensorObj (koszulComplexOn f)
          ((ChainComplex.single₀ (ModuleCat A)).obj (ModuleCat.of A M))).X n)) r := by
  let e := tensor_single₀_X_iso_tensorRight (K := koszulComplexOn f) (M := M) n
  have hright :
      IsSMulRegular
        (((tensoringRight (ModuleCat A)).obj (ModuleCat.of A M)).obj ((koszulComplexOn f).X n)) r :=
    by
    -- Proof comment: `K.X n` is the `n`th exterior power of a finite free module, hence flat, so
    -- tensoring with it preserves injectivity of multiplication by `r` on `M`.
    change IsSMulRegular (((koszulComplexOn f).X n : Type u) ⊗[A] M) r
    letI : Module.Free A (((koszulComplexOn f).X n : Type u)) := by
      change Module.Free A (⋀[A]^n (Fin m → A))
      infer_instance
    simpa using (IsSMulRegular.lTensor (((koszulComplexOn f).X n : Type u)) hr)
  -- Proof comment: transport the tensor-side regularity back across the degreewise `single₀`
  -- collapse isomorphism.
  exact (LinearEquiv.isSMulRegular_congr e.toLinearEquiv r).2 hright

/-- Helper for Remark 10.69.7 (Other types of regular sequences): a class in `QuotSMulTop r M`
is zero exactly when its representative is an `r`-multiple. -/
theorem quotSMulTop_mk_eq_zero_iff_exists_smul {A : Type u} [CommRing A]
    {M : Type u} [AddCommGroup M] [Module A M] {r : A} {x : M} :
    (Submodule.Quotient.mk x : QuotSMulTop r M) = 0 ↔ ∃ y : M, r • y = x := by
  constructor
  · intro hx
    -- Proof comment: exactness of `M --r→ M → M⧸rM` rewrites vanishing in the quotient as
    -- divisibility by `r`.
    rcases ((LinearMap.exact_smul_id_smul_top_mkQ (R := A) (M := M) r) x).mp hx with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa using hy
  · rintro ⟨y, rfl⟩
    -- Proof comment: every explicit `r`-multiple dies in the quotient by construction.
    simpa using
      (LinearMap.exact_smul_id_smul_top_mkQ (R := A) (M := M) r).apply_apply_eq_zero y

/-- Helper for Remark 10.69.7 (Other types of regular sequences): once the head/tail differential
has been normalized to the mapping-cone row
`(u, v) ↦ (d₂ u + r • v, - d₁ v)`, quotient exactness of `d₂, d₁` and `r`-regularity on the
target of `d₁` already give exactness of that row. -/
theorem functionExact_head_tail_row_of_quotient_exact_and_regular {A : Type u} [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {Uneg1 : Type u} [AddCommGroup Uneg1] [Module A Uneg1]
    {r : A}
    {d₂ : U₂ →ₗ[A] U₁} {d₁ : U₁ →ₗ[A] U₀} {d₀ : U₀ →ₗ[A] Uneg1}
    (hd₂₁ : d₁.comp d₂ = 0)
    (hd₁₀ : d₀.comp d₁ = 0)
    (hquot : Function.Exact (QuotSMulTop.map r d₂) (QuotSMulTop.map r d₁))
    (hreg : IsSMulRegular U₀ r) :
    Function.Exact
      (fun x : U₂ × U₁ ↦ (d₂ x.1 + r • x.2, - d₁ x.2))
      (fun y : U₁ × U₀ ↦ (d₁ y.1 + r • y.2, - d₀ y.2)) := by
  refine Function.Exact.of_comp_of_mem_range ?_ ?_
  · -- Proof comment: the normalized head/tail row is a genuine complex because the underlying
    -- tail differentials square to zero.
    funext x
    ext
    · have hd₂₁_apply : d₁ (d₂ x.1) = 0 := by
        simpa [LinearMap.comp_apply] using congrArg (fun f : U₂ →ₗ[A] U₀ ↦ f x.1) hd₂₁
      simpa [hd₂₁_apply]
    · have hd₁₀_apply : d₀ (d₁ x.2) = 0 := by
        simpa [LinearMap.comp_apply] using congrArg (fun f : U₁ →ₗ[A] Uneg1 ↦ f x.2) hd₁₀
      simpa [hd₁₀_apply]
  · intro y hy
    have hy₁ : d₁ y.1 + r • y.2 = 0 := by
      simpa using congrArg Prod.fst hy
    have hquot_zero :
        QuotSMulTop.map r d₁ (Submodule.Quotient.mk y.1 : QuotSMulTop r U₁) = 0 := by
      -- Proof comment: the first row equation says `d₁ y₁` becomes zero modulo `r`.
      rw [QuotSMulTop.map_apply_mk]
      rw [quotSMulTop_mk_eq_zero_iff_exists_smul (A := A) (M := U₀) (r := r)]
      refine ⟨-y.2, ?_⟩
      simpa using (eq_neg_of_add_eq_zero_left hy₁).symm
    rcases (hquot (Submodule.Quotient.mk y.1)).mp hquot_zero with ⟨aq, haq⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (r • (⊤ : Submodule A U₂)) aq
    have hdiff_zero :
        (Submodule.Quotient.mk (y.1 - d₂ a) : QuotSMulTop r U₁) = 0 := by
      -- Proof comment: quotient exactness identifies `y₁` with the image of some lifted tail
      -- element, so their difference is an `r`-multiple.
      have hclass :
          (Submodule.Quotient.mk y.1 : QuotSMulTop r U₁) =
            Submodule.Quotient.mk (d₂ a) := by
        simpa [QuotSMulTop.map_apply_mk] using haq.symm
      have hsub :
          (Submodule.Quotient.mk y.1 : QuotSMulTop r U₁) -
              Submodule.Quotient.mk (d₂ a) = 0 := by
        simpa using sub_eq_zero.mpr hclass
      simpa [sub_eq_add_neg] using hsub
    rcases (quotSMulTop_mk_eq_zero_iff_exists_smul
        (A := A) (M := U₁) (r := r) (x := y.1 - d₂ a)).mp hdiff_zero with ⟨b, hb⟩
    have hr_zero : r • (d₁ b + y.2) = 0 := by
      -- Proof comment: applying `d₁` to the lifted relation `y₁ - d₂ a = r • b` converts the
      -- quotient exactness witness into the desired second-component identity.
      calc
        r • (d₁ b + y.2) = r • d₁ b + r • y.2 := by simp [smul_add]
        _ = d₁ (r • b) + r • y.2 := by simp
        _ = d₁ (y.1 - d₂ a) + r • y.2 := by rw [hb]
        _ = (d₁ y.1 - d₁ (d₂ a)) + r • y.2 := by simp
        _ = d₁ y.1 + r • y.2 := by
          have hd₂₁_apply : d₁ (d₂ a) = 0 := by
            simpa [LinearMap.comp_apply] using congrArg (fun f : U₂ →ₗ[A] U₀ ↦ f a) hd₂₁
          rw [hd₂₁_apply]
          simp
        _ = 0 := hy₁
    have hsecond : y.2 = -d₁ b := by
      -- Proof comment: regularity of `r` on the target kills the residual `r`-torsion.
      apply eq_neg_of_add_eq_zero_left
      exact hreg.right_eq_zero_of_smul (by simpa [add_comm] using hr_zero)
    refine ⟨(a, b), ?_⟩
    ext
    · -- Proof comment: the first component is exactly the lifted quotient relation.
      calc
        d₂ a + r • b = d₂ a + (y.1 - d₂ a) := by rw [hb]
        _ = y.1 := by abel
    · -- Proof comment: the second component is the regularity-forced identity proved above.
      simpa [hsecond]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the normalized incoming
head/tail row map in degree `i ≥ 2` on the tensor-side product model. -/
noncomputable def head_tail_row_left_map {A : Type u} [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {r : A} (d₂ : U₂ →ₗ[A] U₁) (d₁ : U₁ →ₗ[A] U₀) :
    (U₂ × U₁) →ₗ[A] (U₁ × U₀) :=
  (((d₂.comp (LinearMap.fst A U₂ U₁)) + r • (LinearMap.snd A U₂ U₁)).prod
    ((-d₁).comp (LinearMap.snd A U₂ U₁)))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the normalized outgoing
head/tail row map in degree `i ≥ 2` on the tensor-side product model. -/
noncomputable def head_tail_row_right_map {A : Type u} [CommRing A]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {Uneg1 : Type u} [AddCommGroup Uneg1] [Module A Uneg1]
    {r : A} (d₁ : U₁ →ₗ[A] U₀) (d₀ : U₀ →ₗ[A] Uneg1) :
    (U₁ × U₀) →ₗ[A] (U₀ × Uneg1) :=
  (((d₁.comp (LinearMap.fst A U₁ U₀)) + r • (LinearMap.snd A U₁ U₀)).prod
    ((-d₀).comp (LinearMap.snd A U₁ U₀)))

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the normalized outgoing low-row
map in degree `1` on the tensor-side product model. -/
noncomputable def head_tail_low_row_right_map {A : Type u} [CommRing A]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {r : A} (d₁ : U₁ →ₗ[A] U₀) :
    (U₁ × U₀) →ₗ[A] U₀ :=
  (d₁.comp (LinearMap.fst A U₁ U₀)) + r • (LinearMap.snd A U₁ U₀)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the two normalized product-row
maps in degree `i ≥ 2` compose to zero whenever the tail differentials do. -/
theorem head_tail_row_maps_comp_zero {A : Type u} [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {Uneg1 : Type u} [AddCommGroup Uneg1] [Module A Uneg1]
    {r : A}
    {d₂ : U₂ →ₗ[A] U₁} {d₁ : U₁ →ₗ[A] U₀} {d₀ : U₀ →ₗ[A] Uneg1}
    (hd₂₁ : d₁.comp d₂ = 0) (hd₁₀ : d₀.comp d₁ = 0) :
    (head_tail_row_right_map (A := A) (r := r) d₁ d₀).comp
        (head_tail_row_left_map (A := A) (r := r) d₂ d₁) = 0 := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨u, v⟩
  ext <;> simp [head_tail_row_left_map, head_tail_row_right_map, LinearMap.comp_apply]
  · have hd₂₁_apply : d₁ (d₂ u) = 0 := by
      simpa [LinearMap.comp_apply] using congrArg (fun f : U₂ →ₗ[A] U₀ ↦ f u) hd₂₁
    simp [hd₂₁_apply]
  · have hd₁₀_apply : d₀ (d₁ v) = 0 := by
      simpa [LinearMap.comp_apply] using congrArg (fun f : U₁ →ₗ[A] Uneg1 ↦ f v) hd₁₀
    simp [hd₁₀_apply]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the normalized product-row maps
in degree `1` compose to zero whenever the tail differential squares to zero. -/
theorem head_tail_low_row_maps_comp_zero {A : Type u} [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {r : A}
    {d₂ : U₂ →ₗ[A] U₁} {d₁ : U₁ →ₗ[A] U₀}
    (hd₂₁ : d₁.comp d₂ = 0) :
    (head_tail_low_row_right_map (A := A) (r := r) d₁).comp
        (head_tail_row_left_map (A := A) (r := r) d₂ d₁) = 0 := by
  apply LinearMap.ext
  intro p
  rcases p with ⟨u, v⟩
  have hd₂₁_apply : d₁ (d₂ u) = 0 := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : U₂ →ₗ[A] U₀ ↦ f u) hd₂₁
  simp [head_tail_row_left_map, head_tail_low_row_right_map, LinearMap.comp_apply, hd₂₁_apply]

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the normalized degree-`i ≥ 2`
mapping-cone row as a short complex in `ModuleCat`. -/
noncomputable def head_tail_row_shortComplex {A : Type u} [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {Uneg1 : Type u} [AddCommGroup Uneg1] [Module A Uneg1]
    {r : A}
    (d₂ : U₂ →ₗ[A] U₁) (d₁ : U₁ →ₗ[A] U₀) (d₀ : U₀ →ₗ[A] Uneg1)
    (hd₂₁ : d₁.comp d₂ = 0) (hd₁₀ : d₀.comp d₁ = 0) :
    ShortComplex (ModuleCat A) :=
  ShortComplex.mk
    (ModuleCat.ofHom (head_tail_row_left_map (A := A) (r := r) d₂ d₁))
    (ModuleCat.ofHom (head_tail_row_right_map (A := A) (r := r) d₁ d₀))
    (by
      change ModuleCat.ofHom
          ((head_tail_row_right_map (A := A) (r := r) d₁ d₀).comp
            (head_tail_row_left_map (A := A) (r := r) d₂ d₁)) = 0
      rw [head_tail_row_maps_comp_zero (A := A) (r := r) hd₂₁ hd₁₀]
      rfl)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): the normalized degree-`1`
mapping-cone row as a short complex in `ModuleCat`. -/
noncomputable def head_tail_low_row_shortComplex {A : Type u} [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {r : A}
    (d₂ : U₂ →ₗ[A] U₁) (d₁ : U₁ →ₗ[A] U₀)
    (hd₂₁ : d₁.comp d₂ = 0) :
    ShortComplex (ModuleCat A) :=
  ShortComplex.mk
    (ModuleCat.ofHom (head_tail_row_left_map (A := A) (r := r) d₂ d₁))
    (ModuleCat.ofHom (head_tail_low_row_right_map (A := A) (r := r) d₁))
    (by
      change ModuleCat.ofHom
          ((head_tail_low_row_right_map (A := A) (r := r) d₁).comp
            (head_tail_row_left_map (A := A) (r := r) d₂ d₁)) = 0
      rw [head_tail_low_row_maps_comp_zero (A := A) (r := r) hd₂₁]
      rfl)

/-- Helper for Remark 10.69.7 (Other types of regular sequences): in degree `1`, once the
head/tail differential is normalized to the low row
`(u, v) ↦ (d₂ u + r • v, - d₁ v)`, quotient exactness of `d₂, d₁` and `r`-regularity on the
target of `d₁` already give exactness of the truncated row. -/
theorem functionExact_head_tail_low_row_of_quotient_exact_and_regular {A : Type u}
    [CommRing A]
    {U₂ : Type u} [AddCommGroup U₂] [Module A U₂]
    {U₁ : Type u} [AddCommGroup U₁] [Module A U₁]
    {U₀ : Type u} [AddCommGroup U₀] [Module A U₀]
    {r : A}
    {d₂ : U₂ →ₗ[A] U₁} {d₁ : U₁ →ₗ[A] U₀}
    (hd₂₁ : d₁.comp d₂ = 0)
    (hquot : Function.Exact (QuotSMulTop.map r d₂) (QuotSMulTop.map r d₁))
    (hreg : IsSMulRegular U₀ r) :
    Function.Exact
      (fun x : U₂ × U₁ ↦ (d₂ x.1 + r • x.2, - d₁ x.2))
      (fun y : U₁ × U₀ ↦ d₁ y.1 + r • y.2) := by
  refine Function.Exact.of_comp_of_mem_range ?_ ?_
  · -- Proof comment: the normalized low row is a complex because the tail differentials square
    -- to zero.
    funext x
    have hd₂₁_apply : d₁ (d₂ x.1) = 0 := by
      simpa [LinearMap.comp_apply] using congrArg (fun f : U₂ →ₗ[A] U₀ ↦ f x.1) hd₂₁
    simpa [hd₂₁_apply]
  · intro y hy
    have hy₁ : d₁ y.1 + r • y.2 = 0 := hy
    have hquot_zero :
        QuotSMulTop.map r d₁ (Submodule.Quotient.mk y.1 : QuotSMulTop r U₁) = 0 := by
      -- Proof comment: the row equation says `d₁ y₁` becomes zero modulo `r`.
      rw [QuotSMulTop.map_apply_mk]
      rw [quotSMulTop_mk_eq_zero_iff_exists_smul (A := A) (M := U₀) (r := r)]
      refine ⟨-y.2, ?_⟩
      simpa using (eq_neg_of_add_eq_zero_left hy₁).symm
    rcases (hquot (Submodule.Quotient.mk y.1)).mp hquot_zero with ⟨aq, haq⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (r • (⊤ : Submodule A U₂)) aq
    have hdiff_zero :
        (Submodule.Quotient.mk (y.1 - d₂ a) : QuotSMulTop r U₁) = 0 := by
      -- Proof comment: quotient exactness identifies `y₁` with the image of some lifted tail
      -- element, so their difference is an `r`-multiple.
      have hclass :
          (Submodule.Quotient.mk y.1 : QuotSMulTop r U₁) =
            Submodule.Quotient.mk (d₂ a) := by
        simpa [QuotSMulTop.map_apply_mk] using haq.symm
      have hsub :
          (Submodule.Quotient.mk y.1 : QuotSMulTop r U₁) -
              Submodule.Quotient.mk (d₂ a) = 0 := by
        simpa using sub_eq_zero.mpr hclass
      simpa [sub_eq_add_neg] using hsub
    rcases (quotSMulTop_mk_eq_zero_iff_exists_smul
        (A := A) (M := U₁) (r := r) (x := y.1 - d₂ a)).mp hdiff_zero with ⟨b, hb⟩
    have hr_zero : r • (d₁ b + y.2) = 0 := by
      -- Proof comment: applying `d₁` to the lifted relation `y₁ - d₂ a = r • b` converts the
      -- quotient exactness witness into the desired second-component identity.
      calc
        r • (d₁ b + y.2) = r • d₁ b + r • y.2 := by simp [smul_add]
        _ = d₁ (r • b) + r • y.2 := by simp
        _ = d₁ (y.1 - d₂ a) + r • y.2 := by rw [hb]
        _ = (d₁ y.1 - d₁ (d₂ a)) + r • y.2 := by simp
        _ = d₁ y.1 + r • y.2 := by
          have hd₂₁_apply : d₁ (d₂ a) = 0 := by
            simpa [LinearMap.comp_apply] using congrArg (fun f : U₂ →ₗ[A] U₀ ↦ f a) hd₂₁
          rw [hd₂₁_apply]
          simp
        _ = 0 := hy₁
    have hsecond : y.2 = -d₁ b := by
      -- Proof comment: regularity of `r` on the target kills the residual `r`-torsion.
      apply eq_neg_of_add_eq_zero_left
      exact hreg.right_eq_zero_of_smul (by simpa [add_comm] using hr_zero)
    refine ⟨(a, b), ?_⟩
    ext
    · -- Proof comment: the first component is exactly the lifted quotient relation.
      calc
        d₂ a + r • b = d₂ a + (y.1 - d₂ a) := by rw [hb]
        _ = y.1 := by abel
    · -- Proof comment: the second component is the regularity-forced identity proved above.
      simpa [hsecond]


end RingTheory.Sequence
