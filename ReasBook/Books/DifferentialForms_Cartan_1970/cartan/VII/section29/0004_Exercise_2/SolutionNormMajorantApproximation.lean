import DifferentialForms_Cartan_1970.cartan.VII.section29.«0004_Exercise_2».ScalarQuadraticTailBounds
import DifferentialForms_Cartan_1970.cartan.VII.section29.«0004_Exercise_2».SolutionNormMajorant
import DifferentialForms_Cartan_1970.cartan.VII.section29.«0004_Exercise_2».FormalImplicitExistence

open scoped BigOperators MvPowerSeries PowerSeries MvPowerSeries.WithPiTopology
open PowerSeries

universe u

section ScalarQuadraticMajorantExistence

variable {𝕜 : Type u} [NormedCommRing 𝕜]
variable {n p : ℕ}

/-- Helper for Cartan section29 0004_Exercise_2: once the source-facing coefficient induction is
carried out, the coefficientwise norm profile of a formal solution is dominated by the stabilized
scalar direct-limit majorant. -/
lemma solutionNormMajorant_step_le_scalarMajorantOperator
    (S : RecursiveImplicitSystem 𝕜 n p)
    (M R : NNReal)
    (hS : S.IsMajorizedBy M R)
    {x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (hx : FormalImplicitSolution S x)
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    (hA0 : MvPowerSeries.constantCoeff A = 0)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ)
    (hd : 0 < paramDegree d)
    (hA :
      ∀ j' e, paramDegree e < paramDegree d →
        (((solutionNormMajorant x j') e : NNReal) : ℝ) ≤
          (((MvPowerSeries.coeff e A : NNReal) : ℝ))) :
    (((solutionNormMajorant x j) d : NNReal) : ℝ) ≤
      MvPowerSeries.coeff d (scalarMajorantOperator (n := n) (p := p) M R A) := by
  -- Route correction: the scalar-stage recursion and limit transfer are already stable. The only
  -- remaining source-facing gap is the exact-degree comparison from `hx.eq_subst j` and the
  -- coefficient majorant data `hS` to the scalar operator coefficient at degree `d`.
  let trunc := truncatedSolution (n := n) (p := p) (paramDegree d) x
  let linearPart : MvPowerSeries (SystemIndex n p) 𝕜 :=
    ∑ i : Fin n,
      MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i) *
        MvPowerSeries.X (Sum.inr (Sum.inl i))
  let higherPart : MvPowerSeries (SystemIndex n p) 𝕜 :=
    MvPowerSeries.rename (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) (S.higher j)
  let outer : MvPowerSeries (ParamIndex n p) ℝ :=
    (MvPowerSeries.C (M : ℝ)) *
      (1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum (n := n) (p := p))⁻¹
  let linearMajorant : MvPowerSeries (ParamIndex n p) ℝ :=
    outer * paramYSum (n := n) (p := p)
  let higherMajorant : MvPowerSeries (ParamIndex n p) ℝ :=
    outer * scalarQuadraticTail (n := n) (p := p) (((n : ℕ) : ℝ) / (R : ℝ)) A
  have htoSeries : S j = linearPart + higherPart := by
    -- Split the recursive-system series into the linear `Γ(z) y` slice and the nonlinear tail.
    simp [RecursiveImplicitSystem.toSeries, linearPart, higherPart]
  have htruncSubst : MvPowerSeries.HasSubst (solutionSubst trunc) := by
    -- The cutoff family still has zero constant coefficients, so substitution remains admissible.
    simpa [trunc] using
      truncatedSolution_hasSubst (n := n) (p := p) (paramDegree d) x
  have hcoeff_eq :
      ‖MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst trunc) (S j))‖ =
        ‖MvPowerSeries.coeff d (x j)‖ := by
    -- Positive-degree coefficients are unchanged by passing from the full solution to its cutoff.
    have hcoeff_eq_raw :
        MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst trunc) (S j)) =
          MvPowerSeries.coeff d (x j) := by
      rw [hx.eq_subst j]
      exact coeff_subst_eq_of_truncatedSolution (n := n) (p := p) (S := S) (x := x)
        hx.constantCoeff_eq_zero j d hd
    simp [hcoeff_eq_raw]
  rw [solutionNormMajorant]
  change ‖MvPowerSeries.coeff d (x j)‖ ≤
    MvPowerSeries.coeff d (scalarMajorantOperator (n := n) (p := p) M R A)
  rw [← hcoeff_eq]
  rw [htoSeries, MvPowerSeries.subst_add htruncSubst]
  simp only [map_add]
  have hlinearCoeff_trunc (i : Fin n) :
      MvPowerSeries.subst (solutionSubst trunc)
        (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i)) =
        MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) := by
    -- The linear coefficient series only depends on the `z`-variables, so the truncated
    -- substitution acts there exactly like the canonical parameter-variable rename.
    calc
      MvPowerSeries.subst (solutionSubst trunc)
          (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i)) =
          MvPowerSeries.subst (solutionSubst trunc)
            (MvPowerSeries.subst
              (MvPowerSeries.X ∘ (zToSystem : Fin p → SystemIndex n p))
              (S.linearCoeff j i)) := by
                rw [← MvPowerSeries.rename_eq_subst]
      _ = MvPowerSeries.subst
            (fun s ↦
              MvPowerSeries.subst (solutionSubst trunc)
                ((MvPowerSeries.X ∘ (zToSystem : Fin p → SystemIndex n p)) s))
            (S.linearCoeff j i) := by
              rw [MvPowerSeries.subst_comp_subst_apply
                (MvPowerSeries.HasSubst.X_comp (zToSystem : Fin p → SystemIndex n p))
                htruncSubst]
      _ = MvPowerSeries.subst
            (MvPowerSeries.X ∘ (Sum.inr : Fin p → ParamIndex n p))
            (S.linearCoeff j i) := by
              congr 1
              funext s
              simpa [zToSystem] using
                (MvPowerSeries.subst_X htruncSubst
                  (s := (Sum.inr (Sum.inr s) : SystemIndex n p)))
      _ = MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) := by
            simpa using
              (MvPowerSeries.rename_eq_subst (f := (Sum.inr : Fin p → ParamIndex n p))
                (p := S.linearCoeff j i)).symm
  have hlinear_trunc :
      MvPowerSeries.subst (solutionSubst trunc) linearPart =
        ∑ i : Fin n,
          MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
            MvPowerSeries.X (Sum.inl i) := by
    -- Distribute substitution across the finite linear sum and simplify every summand to the
    -- explicit `Γ(z) Yᵢ` normal form that the coefficient comparison must bound next.
    calc
      MvPowerSeries.subst (solutionSubst trunc) linearPart =
          ∑ i : Fin n,
            MvPowerSeries.subst (solutionSubst trunc)
              (MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p) (S.linearCoeff j i) *
                MvPowerSeries.X (Sum.inr (Sum.inl i))) := by
                  rw [show linearPart =
                    ∑ i : Fin n,
                      MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                          (S.linearCoeff j i) *
                        MvPowerSeries.X (Sum.inr (Sum.inl i)) by
                    rfl]
                  simpa [MvPowerSeries.substAlgHom_apply] using
                    (map_sum (MvPowerSeries.substAlgHom htruncSubst)
                      (fun i : Fin n ↦
                        MvPowerSeries.rename (zToSystem : Fin p → SystemIndex n p)
                            (S.linearCoeff j i) *
                          MvPowerSeries.X (Sum.inr (Sum.inl i)))
                      Finset.univ)
      _ = ∑ i : Fin n,
            MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
              MvPowerSeries.X (Sum.inl i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [MvPowerSeries.subst_mul htruncSubst, hlinearCoeff_trunc]
                rw [MvPowerSeries.subst_X htruncSubst]
                simp [solutionSubst]
  have hlinear :
      ‖MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst trunc) linearPart)‖ ≤
        MvPowerSeries.coeff d linearMajorant := by
    -- Compare each `Γ(z) Yᵢ` summand with the common outer scalar factor, then sum the bounds.
    rw [hlinear_trunc]
    have hsumBound :
        ‖MvPowerSeries.coeff d
            (∑ i : Fin n,
              MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
                MvPowerSeries.X (Sum.inl i))‖ ≤
          ∑ i : Fin n,
            MvPowerSeries.coeff d (outer * MvPowerSeries.X (Sum.inl i)) := by
      calc
        ‖MvPowerSeries.coeff d
            (∑ i : Fin n,
              MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
                MvPowerSeries.X (Sum.inl i))‖ ≤
          ∑ i : Fin n,
            ‖MvPowerSeries.coeff d
                (MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
                  MvPowerSeries.X (Sum.inl i))‖ := by
              simpa using
                (norm_sum_le (s := Finset.univ)
                  (f := fun i : Fin n ↦
                    MvPowerSeries.coeff d
                      (MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p)
                          (S.linearCoeff j i) *
                        MvPowerSeries.X (Sum.inl i))))
        _ ≤ ∑ i : Fin n,
            MvPowerSeries.coeff d (outer * MvPowerSeries.X (Sum.inl i)) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hcoeffLinear :
                  MvPowerSeries.coeff d
                    ((MvPowerSeries.rename
                        (Sum.inr : Fin p → ParamIndex n p)
                        (S.linearCoeff j i)) *
                      MvPowerSeries.X (Sum.inl i)) =
                    if Finsupp.single (Sum.inl i) 1 ≤ d then
                      MvPowerSeries.coeff (d - Finsupp.single (Sum.inl i) 1)
                        (MvPowerSeries.rename
                          (Sum.inr : Fin p → ParamIndex n p)
                          (S.linearCoeff j i))
                    else
                      0 := by
                        simpa [MvPowerSeries.X] using
                          (MvPowerSeries.coeff_mul_monomial (m := d)
                            (n := Finsupp.single (Sum.inl i) 1)
                            (φ := MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p)
                              (S.linearCoeff j i))
                            (a := (1 : 𝕜)))
              have hcoeffOuter :
                  MvPowerSeries.coeff d (outer * MvPowerSeries.X (Sum.inl i)) =
                    if Finsupp.single (Sum.inl i) 1 ≤ d then
                      MvPowerSeries.coeff (d - Finsupp.single (Sum.inl i) 1) outer
                    else
                      0 := by
                        simpa [MvPowerSeries.X] using
                          (MvPowerSeries.coeff_mul_monomial (m := d)
                            (n := Finsupp.single (Sum.inl i) 1)
                            (φ := outer)
                            (a := (1 : ℝ)))
              rw [hcoeffLinear, hcoeffOuter]
              by_cases hdY : Finsupp.single (Sum.inl i) 1 ≤ d
              · simp [hdY]
                simpa [outer, paramZEmb] using
                  (linearCoeff_rename_coeff_le_outer (n := n) (p := p) S M R hS j i
                    (d - Finsupp.single (Sum.inl i) 1))
              · simp [hdY]
    calc
      ‖MvPowerSeries.coeff d
          (∑ i : Fin n,
            MvPowerSeries.rename (Sum.inr : Fin p → ParamIndex n p) (S.linearCoeff j i) *
              MvPowerSeries.X (Sum.inl i))‖ ≤
        ∑ i : Fin n,
          MvPowerSeries.coeff d (outer * MvPowerSeries.X (Sum.inl i)) :=
        hsumBound
      _ = MvPowerSeries.coeff d (outer * ∑ i : Fin n, MvPowerSeries.X (Sum.inl i)) := by
            simp [Finset.mul_sum]
      _ = MvPowerSeries.coeff d linearMajorant := by
            simp [linearMajorant, paramYSum]
  have hhigher :
      ‖MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst trunc) higherPart)‖ ≤
        MvPowerSeries.coeff d higherMajorant := by
    let a : ℝ := (((n : ℕ) : ℝ) / (R : ℝ))
    let higherSubst : Fin n ⊕ Fin p → MvPowerSeries (ParamIndex n p) 𝕜 :=
      fun s ↦ solutionSubst trunc (higherToSystem s)
    let G : ((Fin n ⊕ Fin p) →₀ ℕ) → 𝕜 :=
      fun m ↦
        MvPowerSeries.coeff m (S.higher j) *
          MvPowerSeries.coeff d (m.prod fun s q ↦ (higherSubst s) ^ q)
    let ownerCoeff : ℕ → ℝ :=
      fun qx ↦
        MvPowerSeries.coeff d
          (scalarOuterFactor (n := n) (p := p) M R *
            scaledMajorantPower (n := n) (p := p) a A qx)
    have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.zero_lt_of_lt j.2)
    have htrunc0 :
        ∀ j', MvPowerSeries.constantCoeff (trunc j') = 0 := by
      simpa [trunc] using
        (truncatedSolution_constantCoeff (n := n) (p := p) (paramDegree d) x)
    have htruncA :
        ∀ j' e, paramDegree e < paramDegree d →
          ‖MvPowerSeries.coeff e (trunc j')‖ ≤ (((MvPowerSeries.coeff e A : NNReal) : ℝ)) := by
      intro j' e he
      rw [coeff_truncatedSolution_eq_of_lt_paramDegree (n := n) (p := p) (paramDegree d) x
        hx.constantCoeff_eq_zero j' e he]
      simpa [solutionNormMajorant] using hA j' e he
    have hhigherSubst : MvPowerSeries.HasSubst higherSubst := by
      -- Restrict the admissible cutoff substitution to the `(x, z)` variables.
      refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
      intro s
      cases s with
      | inl i =>
          simpa [higherSubst, solutionSubst, higherToSystem] using htrunc0 i
      | inr k =>
          simp [higherSubst, solutionSubst, higherToSystem, zToSystem]
    have hhigher_trunc :
        MvPowerSeries.subst (solutionSubst trunc) higherPart =
          MvPowerSeries.subst higherSubst (S.higher j) := by
      -- Re-express the higher substitution on the smaller `(x, z)` variable family.
      calc
        MvPowerSeries.subst (solutionSubst trunc) higherPart =
            MvPowerSeries.subst (solutionSubst trunc)
              (MvPowerSeries.subst
                (MvPowerSeries.X ∘
                  (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p))
                (S.higher j)) := by
                  rw [show higherPart =
                    MvPowerSeries.rename
                      (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p) (S.higher j) by
                    rfl]
                  rw [← MvPowerSeries.rename_eq_subst]
        _ = MvPowerSeries.subst
              (fun s ↦
                MvPowerSeries.subst (solutionSubst trunc)
                  ((MvPowerSeries.X ∘
                    (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p)) s))
              (S.higher j) := by
                rw [MvPowerSeries.subst_comp_subst_apply
                  (MvPowerSeries.HasSubst.X_comp
                    (higherToSystem : Fin n ⊕ Fin p → SystemIndex n p))
                  htruncSubst]
        _ = MvPowerSeries.subst higherSubst (S.higher j) := by
              congr 1
              funext s
              change MvPowerSeries.subst (solutionSubst trunc)
                  (MvPowerSeries.X (higherToSystem s)) = higherSubst s
              rw [MvPowerSeries.subst_X htruncSubst]
    have hGfinite : G.HasFiniteSupport := by
      simpa [G, higherSubst, smul_eq_mul] using
        (MvPowerSeries.coeff_subst_finite hhigherSubst (S.higher j) d)
    have hcoeffHigher :
        MvPowerSeries.coeff d (MvPowerSeries.subst higherSubst (S.higher j)) =
          Finset.sum hGfinite.toFinset G := by
      calc
        MvPowerSeries.coeff d (MvPowerSeries.subst higherSubst (S.higher j)) =
            ∑ᶠ m, G m := by
              simpa [G, smul_eq_mul] using
                (MvPowerSeries.coeff_subst hhigherSubst (S.higher j) d)
        _ = Finset.sum hGfinite.toFinset G := by
              exact finsum_eq_sum G hGfinite
    have howner_nonneg : ∀ qx, 0 ≤ ownerCoeff qx := by
      intro qx
      dsimp [ownerCoeff]
      rw [MvPowerSeries.coeff_mul]
      refine Finset.sum_nonneg ?_
      intro e he
      exact mul_nonneg
        (outerCoeff_nonneg (n := n) (p := p) M R e.1)
        (coeffScaledMajorantPow_nonneg (n := n) (p := p) a (by positivity) A qx e.2)
    rw [hhigher_trunc, hcoeffHigher]
    calc
      ‖Finset.sum hGfinite.toFinset G‖ ≤
        Finset.sum hGfinite.toFinset (fun m ↦ ‖G m‖) := by
          simpa using
            (norm_sum_le (s := hGfinite.toFinset) (f := G))
      _ = ∑ qx ∈ hGfinite.toFinset.image xDegree,
            ∑ m ∈ hGfinite.toFinset with xDegree m = qx, ‖G m‖ := by
          symm
          exact Finset.sum_fiberwise_of_maps_to
            (s := hGfinite.toFinset) (t := hGfinite.toFinset.image xDegree) (g := xDegree)
            (fun m hm ↦ Finset.mem_image_of_mem xDegree hm)
            (fun m ↦ ‖G m‖)
      _ ≤ ∑ qx ∈ hGfinite.toFinset.image xDegree, ownerCoeff qx := by
          refine Finset.sum_le_sum ?_
          intro qx hq
          have hqx : 2 ≤ qx := by
            rcases Finset.mem_image.mp hq with ⟨m, hm, rfl⟩
            have hmne : G m ≠ 0 := hGfinite.mem_toFinset.mp hm
            by_contra hlt
            have hxle : xDegree m ≤ 1 := by
              omega
            have hzeroCoeff : MvPowerSeries.coeff m (S.higher j) = 0 := by
              exact S.higher_xDegree_ge_two j m hxle
            apply hmne
            simp [G, hzeroCoeff]
          simpa [G, higherSubst, ownerCoeff] using
            (higherSubstSlice_le_outerMulScaledMajorantPowCoeff
              (n := n) (p := p) S M R hS htrunc0 j d htruncA qx
              (hGfinite.toFinset.filter fun m ↦ xDegree m = qx) hqx
              (fun m hm ↦ (Finset.mem_filter.mp hm).2) hn)
      _ = ∑ qx ∈ (hGfinite.toFinset.image xDegree).filter
            (fun qx ↦ qx ∈ Finset.Icc 2 (paramDegree d)), ownerCoeff qx +
            ∑ qx ∈ (hGfinite.toFinset.image xDegree).filter
            (fun qx ↦ qx ∉ Finset.Icc 2 (paramDegree d)), ownerCoeff qx := by
          symm
          exact Finset.sum_filter_add_sum_filter_not
            (s := hGfinite.toFinset.image xDegree)
            (p := fun qx ↦ qx ∈ Finset.Icc 2 (paramDegree d))
            (f := ownerCoeff)
      _ = ∑ qx ∈ (hGfinite.toFinset.image xDegree).filter
            (fun qx ↦ qx ∈ Finset.Icc 2 (paramDegree d)), ownerCoeff qx + 0 := by
          congr 1
          apply Finset.sum_eq_zero
          intro qx hq
          have hqx : 2 ≤ qx := by
            have hqimage : qx ∈ hGfinite.toFinset.image xDegree := (Finset.mem_filter.mp hq).1
            rcases Finset.mem_image.mp hqimage with ⟨m, hm, rfl⟩
            have hmne : G m ≠ 0 := hGfinite.mem_toFinset.mp hm
            by_contra hlt
            have hxle : xDegree m ≤ 1 := by
              omega
            have hzeroCoeff : MvPowerSeries.coeff m (S.higher j) = 0 := by
              exact S.higher_xDegree_ge_two j m hxle
            apply hmne
            simp [G, hzeroCoeff]
          have hgt : paramDegree d < qx := by
            have hnot : qx ∉ Finset.Icc 2 (paramDegree d) := (Finset.mem_filter.mp hq).2
            by_contra hle
            exact hnot (Finset.mem_Icc.mpr ⟨hqx, le_of_not_gt hle⟩)
          simpa [ownerCoeff, scalarOuterFactor, scaledMajorantPower, a] using
            (coeffOuterMulScaledMajorantPow_eq_zero_of_paramDegree_lt
              (n := n) (p := p)
              (outer := scalarOuterFactor (n := n) (p := p) M R)
              (a := a) (A := A) hA0 qx d hgt)
      _ = ∑ qx ∈ (hGfinite.toFinset.image xDegree).filter
            (fun qx ↦ qx ∈ Finset.Icc 2 (paramDegree d)), ownerCoeff qx := by
          simp
      _ ≤ ∑ qx ∈ Finset.Icc 2 (paramDegree d), ownerCoeff qx := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by
              intro qx hq
              exact (Finset.mem_filter.mp hq).2)
            (fun qx hq hnot ↦ howner_nonneg qx)
      _ = MvPowerSeries.coeff d higherMajorant := by
          symm
          simpa [higherMajorant, outer, scalarOuterFactor, scaledMajorantPower, ownerCoeff, a] using
            (coeffHigherMajorant_eq_sum_Icc (n := n) (p := p)
              (outer := scalarOuterFactor (n := n) (p := p) M R)
              (a := a) hA0 d)
  -- Once the linear and nonlinear slices are bounded separately, the scalar operator normal form
  -- recombines them into the desired exact-degree majorant bound.
  calc
    ‖MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst trunc) linearPart) +
        MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst trunc) higherPart)‖
        ≤ ‖MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst trunc) linearPart)‖ +
            ‖MvPowerSeries.coeff d (MvPowerSeries.subst (solutionSubst trunc) higherPart)‖ := by
              exact norm_add_le _ _
    _ ≤ MvPowerSeries.coeff d linearMajorant + MvPowerSeries.coeff d higherMajorant := by
              exact add_le_add hlinear hhigher
    _ = MvPowerSeries.coeff d (linearMajorant + higherMajorant) := by
            simp
    _ = MvPowerSeries.coeff d (scalarMajorantOperator (n := n) (p := p) M R A) := by
          dsimp [linearMajorant, higherMajorant, outer]
          rw [← mul_add, scalarMajorantOperator_eq_outer_mul_inner (n := n) (p := p) M R A]
          simp [scalarMajorantInner]

/-- Helper for Cartan section29 0004_Exercise_2: the exact-degree source comparison feeds a
single-stage induction showing that every coefficient already inserted in the scalar approximant
dominates the corresponding coefficient of the formal solution norm profile. -/
lemma solutionNormMajorant_coeff_le_scalarMajorantApproximant
    (S : RecursiveImplicitSystem 𝕜 n p)
    (M R : NNReal)
    (hS : S.IsMajorizedBy M R)
    {x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (hx : FormalImplicitSolution S x) :
    ∀ N j d, paramDegree d ≤ N →
      (((solutionNormMajorant x j) d : NNReal) : ℝ) ≤
        (((MvPowerSeries.coeff d
            (scalarMajorantApproximant (n := n) (p := p) M R N) : NNReal) : ℝ))
  | 0, j, d, hd => by
      have hd0 : paramDegree d = 0 := Nat.eq_zero_of_le_zero hd
      have hdz : d = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) d).mp hd0
      subst hdz
      -- At stage `0`, both the formal solution norm profile and the scalar approximant have zero
      -- constant coefficient.
      change
        (((MvPowerSeries.constantCoeff (solutionNormMajorant x j) : NNReal) : ℝ)) ≤
          (((MvPowerSeries.constantCoeff
              (scalarMajorantApproximant (n := n) (p := p) M R 0) : NNReal) : ℝ))
      rw [solutionNormMajorant_constantCoeff_eq_zero (S := S) hx j,
        scalarMajorantApproximant_constantCoeff (n := n) (p := p) M R 0]
  | N + 1, j, d, hd => by
      by_cases hprev : paramDegree d ≤ N
      · -- Coefficients from earlier total degree stages persist unchanged at the next stage.
        calc
          (((solutionNormMajorant x j) d : NNReal) : ℝ) ≤
              (((MvPowerSeries.coeff d
                  (scalarMajorantApproximant (n := n) (p := p) M R N) : NNReal) : ℝ)) :=
            solutionNormMajorant_coeff_le_scalarMajorantApproximant S M R hS hx N j d hprev
          _ = (((MvPowerSeries.coeff d
                  (scalarMajorantApproximant (n := n) (p := p) M R (N + 1)) : NNReal) : ℝ)) := by
              congr 1
              symm
              exact scalarMajorantApproximant_coeff_step_eq (n := n) (p := p) M R N d
                (by omega)
      · have hdEq : paramDegree d = N + 1 := by omega
        have hdPos : 0 < paramDegree d := by omega
        have hprefix :
            ∀ j' e, paramDegree e < paramDegree d →
              (((solutionNormMajorant x j') e : NNReal) : ℝ) ≤
                (((MvPowerSeries.coeff e
                    (scalarMajorantApproximant (n := n) (p := p) M R N) : NNReal) : ℝ)) := by
          intro j' e he
          exact solutionNormMajorant_coeff_le_scalarMajorantApproximant S M R hS hx N j' e
            (by omega)
        -- The newly inserted degree comes from one exact-degree comparison against the scalar
        -- operator, then the `Real.toNNReal` readback at stage `N + 1`.
        calc
          (((solutionNormMajorant x j) d : NNReal) : ℝ) ≤
              MvPowerSeries.coeff d
                (scalarMajorantOperator (n := n) (p := p) M R
                  (scalarMajorantApproximant (n := n) (p := p) M R N)) := by
                exact solutionNormMajorant_step_le_scalarMajorantOperator
                  (n := n) (p := p) S M R hS hx
                  (scalarMajorantApproximant_constantCoeff (n := n) (p := p) M R N)
                  j d hdPos hprefix
          _ = (((MvPowerSeries.coeff d
                  (scalarMajorantApproximant (n := n) (p := p) M R (N + 1)) : NNReal) : ℝ)) := by
                symm
                exact scalarMajorantApproximant_coeff_insert_readback (n := n) (p := p)
                  M R N d hdEq
                  (scalarMajorantOperator_coeff_nonneg (n := n) (p := p) M R
                    (scalarMajorantApproximant_constantCoeff (n := n) (p := p) M R N) d)

/-- Helper for Cartan section29 0004_Exercise_2: once the stagewise comparison is available, the
stabilized scalar limit dominates the formal solution norm profile coefficientwise by reading the
target coefficient at stage `paramDegree d`. -/
lemma solutionNormMajorant_le_scalarMajorantLimit
    (S : RecursiveImplicitSystem 𝕜 n p)
    (M R : NNReal)
    (hS : S.IsMajorizedBy M R)
    {x : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    (hx : FormalImplicitSolution S x)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ) :
    (((solutionNormMajorant x j) d : NNReal) : ℝ) ≤
      (((scalarMajorantLimit (n := n) (p := p) M R) d : NNReal) : ℝ) := by
  -- Route correction: the direct-limit fixed-point half is already separated above. What remains
  -- here is only the transfer from the stagewise comparison to the stabilized limit coefficient.
  have hstage :
      (((solutionNormMajorant x j) d : NNReal) : ℝ) ≤
        (((MvPowerSeries.coeff d
            (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d)) : NNReal) : ℝ)) :=
    solutionNormMajorant_coeff_le_scalarMajorantApproximant (n := n) (p := p)
      S M R hS hx (paramDegree d) j d le_rfl
  have hlimit :
      (((MvPowerSeries.coeff d
          (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d)) : NNReal) : ℝ)) =
        (((scalarMajorantLimit (n := n) (p := p) M R) d : NNReal) : ℝ) := by
    simpa using congrArg (fun t : NNReal => (t : ℝ))
      (scalarMajorantLimit_coeff_eq_approximant (n := n) (p := p) M R d
        (N := paramDegree d) le_rfl).symm
  calc
    (((solutionNormMajorant x j) d : NNReal) : ℝ) ≤
        (((MvPowerSeries.coeff d
            (scalarMajorantApproximant (n := n) (p := p) M R (paramDegree d)) : NNReal) : ℝ)) :=
      hstage
    _ = (((scalarMajorantLimit (n := n) (p := p) M R) d : NNReal) : ℝ) := hlimit


end ScalarQuadraticMajorantExistence
