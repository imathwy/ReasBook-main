import Serre.Chap10.Exercise_10_10_5_5.BrauerPrelude

noncomputable section

universe u

open scoped Representation SubgroupInduction

namespace Representation

section

variable {G : Type} [Group G] [Finite G]

private noncomputable abbrev finiteGroupFintype : Fintype G := Fintype.ofFinite G
attribute [local instance] finiteGroupFintype

/-- A subgroup of a finite group is finite. -/
private noncomputable abbrev subgroupFintype (H : Subgroup G) : Fintype H := Fintype.ofFinite H
attribute [local instance] subgroupFintype

/-- Helper for Exercise 10-10.5-5: a one-dimensional finite-dimensional complex representation is
the representation attached to a degree-`1` character. -/
theorem exists_linear_character_of_fdRep_finrank_one
    (V : FDRep ℂ G) (hV : Module.finrank ℂ V = 1) :
    ∃ α : G →* ℂˣ, V.character = α.toRepresentation.character := by
  let scalarEquiv : ℂ ≃ₗ[ℂ] (V →ₗ[ℂ] V) := LinearEquiv.smul_id_of_finrank_eq_one hV
  have hscalar (c : ℂ) : scalarEquiv c = c • LinearMap.id := by
    exact LinearEquiv.smul_id_of_finrank_eq_one_apply hV c
  let α₀ : G → ℂ := fun g ↦ scalarEquiv.symm (V.ρ g)
  have hα₀_eq (g : G) : V.ρ g = α₀ g • LinearMap.id := by
    -- In degree `1`, every action map is scalar multiplication by a unique complex number.
    calc
      V.ρ g = scalarEquiv (α₀ g) := by
        simp [α₀]
      _ = α₀ g • LinearMap.id := hscalar _
  have hα₀_one : α₀ 1 = 1 := by
    -- The identity acts by the identity endomorphism, so its associated scalar is `1`.
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ 1) = V.ρ 1 := by
        simp [α₀]
      _ = (1 : V →ₗ[ℂ] V) := by
        simp
      _ = scalarEquiv 1 := by
        simpa using (hscalar (1 : ℂ)).symm
  have hα₀_mul (g h : G) : α₀ (g * h) = α₀ g * α₀ h := by
    -- Multiplicativity of the representation turns the scalar assignment into a linear character.
    apply scalarEquiv.injective
    calc
      scalarEquiv (α₀ (g * h)) = V.ρ (g * h) := by
        simp [α₀]
      _ = V.ρ g * V.ρ h := by
        simp
      _ = (α₀ g * α₀ h) • LinearMap.id := by
        rw [hα₀_eq, hα₀_eq]
        ext x
        simp [smul_smul, mul_comm]
      _ = scalarEquiv (α₀ g * α₀ h) := (hscalar _).symm
  have hα₀_ne_zero (g : G) : α₀ g ≠ 0 := by
    -- An invertible action map on a nonzero one-dimensional space cannot have scalar `0`.
    have hpos : 0 < Module.finrank ℂ V := by
      simpa [hV]
    letI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
    intro hg0
    have hzero : V.ρ g = 0 := by
      simp [hα₀_eq, hg0]
    have hone : (1 : V →ₗ[ℂ] V) ≠ 0 := one_ne_zero
    have hmul : V.ρ g * V.ρ g⁻¹ = (1 : V →ₗ[ℂ] V) := by
      simpa using (V.ρ.map_mul g g⁻¹).symm
    have hidzero : (1 : V →ₗ[ℂ] V) = 0 := by
      calc
        (1 : V →ₗ[ℂ] V) = V.ρ g * V.ρ g⁻¹ := hmul.symm
        _ = 0 := by
          rw [hzero]
          simp
    exact hone hidzero
  let α : G →* ℂˣ :=
    { toFun := fun g ↦ Units.mk0 (α₀ g) (hα₀_ne_zero g)
      map_one' := by
        ext
        exact hα₀_one
      map_mul' g h := by
        ext
        exact hα₀_mul g h }
  refine ⟨α, ?_⟩
  ext g
  -- Taking traces of the scalar action recovers the original character.
  rw [MonoidHom.toRepresentation_character_apply]
  calc
    V.character g = LinearMap.trace ℂ V (V.ρ g) := by
      rfl
    _ = LinearMap.trace ℂ V (α₀ g • LinearMap.id) := by
      rw [hα₀_eq]
    _ = α₀ g * LinearMap.trace ℂ V LinearMap.id := by
      simp [smul_eq_mul]
    _ = α₀ g * Module.finrank ℂ V := by
      simp [LinearMap.trace_id]
    _ = α₀ g := by
      simp [hV]
    _ = (α g : ℂ) := rfl

omit [Finite G] in
/-- Helper for Exercise 10-10.5-5: cyclicity of a quotient pulls back along a surjective
homomorphism to the corresponding quotient of inverse-image subgroups. -/
private theorem isCyclic_comap_quotient_of_surjective_local
    {Q : Type} [Group Q] (q : G →* Q) (hq : Function.Surjective q)
    {A B : Subgroup Q} [B.Normal]
    [IsCyclic (A ⧸ B.subgroupOf A)] :
    IsCyclic ((Subgroup.comap q A) ⧸ (Subgroup.comap q B).subgroupOf (Subgroup.comap q A)) := by
  -- Realize the pulled-back quotient as the quotient by the kernel of the restricted map to `A`.
  let qA : Subgroup.comap q A →* A :=
    { toFun := fun x ↦ ⟨q x, x.property⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro x y
        ext
        simp }
  let φ : Subgroup.comap q A →* A ⧸ B.subgroupOf A :=
    (QuotientGroup.mk' (B.subgroupOf A)).comp qA
  have hφ_surj : Function.Surjective φ := by
    -- Surjectivity comes from surjectivity of `q` and of the quotient map `A → A / B`.
    intro x
    rcases QuotientGroup.mk'_surjective (B.subgroupOf A) x with ⟨a, rfl⟩
    rcases hq a with ⟨y, hy⟩
    refine ⟨⟨y, by simp [hy, a.property]⟩, ?_⟩
    simp [φ, qA, hy]
  have hker : (Subgroup.comap q B).subgroupOf (Subgroup.comap q A) = φ.ker := by
    -- The kernel consists exactly of those elements whose `q`-image lands in `B`.
    ext x
    simp [φ, qA]
    rfl
  let e :
      ((Subgroup.comap q A) ⧸ (Subgroup.comap q B).subgroupOf (Subgroup.comap q A)) ≃*
        (A ⧸ B.subgroupOf A) :=
    QuotientGroup.liftEquiv
      ((Subgroup.comap q B).subgroupOf (Subgroup.comap q A)) hφ_surj hker
  exact (e.isCyclic).2 inferInstance

omit [Finite G] in
/-- Helper for Exercise 10-10.5-5: any subgroup contained in the center is normal. -/
private theorem normal_of_le_center_local {H : Subgroup G}
    (hH : H ≤ Subgroup.center G) :
    H.Normal := by
  -- Conjugation fixes every central element, so it preserves every subgroup of the center.
  constructor
  intro x hx g
  have hxC : x ∈ Subgroup.center G := hH hx
  rw [Subgroup.mem_center_iff] at hxC
  simpa [hxC g, mul_assoc] using hx

omit [Finite G] in
/-- Helper for Exercise 10-10.5-5: the cyclic subgroup generated by a central element remains
central. -/
private theorem zpowers_le_center_of_mem_center_local {z : G}
    (hz : z ∈ Subgroup.center G) :
    Subgroup.zpowers z ≤ Subgroup.center G := by
  -- Every power of a central element is central because commutation is stable under integer
  -- powers.
  intro x hx
  rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hcomm : Commute g z := (commute_iff_eq _ _).2 (Subgroup.mem_center_iff.mp hz g)
  exact (hcomm.zpow_right n).eq

omit [Finite G] in
/-- Helper for Exercise 10-10.5-5: in a `p`-elementary decomposition, the cyclic factor is
normal. -/
private theorem IsPElementaryDecomposition.cyclic_factor_normal_local
    {p : ℕ} {C P : Subgroup G} (hCP : IsPElementaryDecomposition p C P) :
    C.Normal := by
  -- Show that both complementary factors lie in the normalizer of `C`; their supremum is all of
  -- `G`, so the normalizer is the whole group.
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  have hPnorm : P ≤ Subgroup.normalizer (C : Set G) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      have hcomm : Commute (c : G) p := hCP.commute ⟨c, hc⟩ ⟨p, hp⟩
      have hconj : p * c * p⁻¹ = c := by
        calc
          p * c * p⁻¹ = c * p * p⁻¹ := by rw [hcomm.eq, mul_assoc]
          _ = c := by simp
      simpa [MulAut.conj_apply, hconj] using hc
    · intro hx
      refine ⟨x, hx, ?_⟩
      have hcomm : Commute x p := hCP.commute ⟨x, hx⟩ ⟨p, hp⟩
      have hconj : p * x * p⁻¹ = x := by
        calc
          p * x * p⁻¹ = x * p * p⁻¹ := by rw [hcomm.eq, mul_assoc]
          _ = x := by simp
      simp [MulAut.conj_apply, hconj]
  have hsup :
      C ⊔ P ≤ Subgroup.normalizer (C : Set G) :=
    sup_le Subgroup.le_normalizer hPnorm
  simpa [hCP.isComplement.sup_eq_top] using hsup

omit [Finite G] in
/-- Helper for Exercise 10-10.5-5: supersolvability lifts across a normal cyclic kernel. -/
private theorem isSupersolvable_of_normal_cyclic_subgroup_quotient_local
    (N : Subgroup G) [N.Normal] (hN : IsCyclic N)
    [IsSupersolvable (G ⧸ N)] :
    IsSupersolvable G := by
  let hsup : IsSupersolvable (G ⧸ N) := inferInstance
  letI : IsCyclic N := hN
  rcases hsup.supersolvable with ⟨n, f, hmono, hnormal, hcyclic, h0, hn⟩
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let g : ℕ → Subgroup G := fun i ↦
    match i with
    | 0 => ⊥
    | j + 1 => Subgroup.comap q (f j)
  -- Insert the cyclic kernel as the first nontrivial term, then pull back the supersolvable
  -- series from the quotient.
  refine ⟨?_⟩
  refine ⟨n + 1, g, ?_⟩
  refine ⟨?_, ⟨?_, ⟨?_, ?_, ?_⟩⟩⟩
  · refine monotone_nat_of_le_succ ?_
    intro i
    cases i with
    | zero =>
        simp [g, q, h0]
    | succ i =>
        exact Subgroup.comap_mono (hmono (Nat.le_succ i))
  · intro i hi
    cases i with
    | zero =>
        change (⊥ : Subgroup G).Normal
        infer_instance
    | succ i =>
        simpa [g] using (hnormal i (Nat.succ_lt_succ_iff.mp hi)).comap q
  · intro i hi
    cases i with
    | zero =>
        -- The first quotient is just the kernel `N` itself.
        change IsCyclic
          ((Subgroup.comap q (f 0)) ⧸
            ((⊥ : Subgroup G).subgroupOf (Subgroup.comap q (f 0))))
        let e0 : Subgroup.comap q (f 0) ≃* N :=
          { toFun := fun x ↦
              ⟨x, by
                simpa [q, h0, QuotientGroup.ker_mk' N] using x.property⟩
            invFun := fun x ↦
              ⟨x, by
                have hx : q x = 1 := by
                  exact (QuotientGroup.eq_one_iff _).2 x.property
                show q x ∈ f 0
                rw [h0, hx]
                simp⟩
            left_inv := by
              intro x
              ext
              rfl
            right_inv := by
              intro x
              ext
              rfl
            map_mul' := by
              intro x y
              rfl }
        have hker_cyclic : IsCyclic (Subgroup.comap q (f 0)) := by
          exact (e0.isCyclic).2 inferInstance
        letI : IsCyclic (Subgroup.comap q (f 0)) := hker_cyclic
        simpa using
          (isCyclic_of_surjective
            (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf (Subgroup.comap q (f 0))))
            (QuotientGroup.mk'_surjective
              ((⊥ : Subgroup G).subgroupOf (Subgroup.comap q (f 0)))))
    | succ i =>
        -- Later quotients are the pullbacks of the cyclic quotients in the quotient series.
        have hi' : i < n := Nat.succ_lt_succ_iff.mp hi
        letI : (f i).Normal := hnormal i hi'
        letI : IsCyclic (f (i + 1) ⧸ (f i).subgroupOf (f (i + 1))) := hcyclic i hi'
        simpa [g, q] using
          (isCyclic_comap_quotient_of_surjective_local q (QuotientGroup.mk'_surjective N)
            (A := f (i + 1)) (B := f i) :
            IsCyclic
              ((Subgroup.comap q (f (i + 1))) ⧸
                (Subgroup.comap q (f i)).subgroupOf (Subgroup.comap q (f (i + 1)))))
  · simp [g]
  · simp [g, q, hn]

/-- Helper for Exercise 10-10.5-5: every finite `p`-group is supersolvable. -/
private theorem isSupersolvable_of_isPGroup_local
    {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G) :
    IsSupersolvable G := by
  cases nonempty_fintype G
  classical
  revert ‹Group G›
  apply @Fintype.induction_subsingleton_or_nontrivial _ G _
  · intro G _ _ _ _
    -- A subsingleton group is cyclic, hence supersolvable.
    letI : Subsingleton G := inferInstance
    letI : IsCyclic G := isCyclic_of_subsingleton
    infer_instance
  · intro G _ _ ih _ hG
    -- Choose a nontrivial central element and quotient by its cyclic subgroup.
    have hcenter_nontrivial : Nontrivial (Subgroup.center G) := IsPGroup.center_nontrivial hG
    letI : Nontrivial (Subgroup.center G) := hcenter_nontrivial
    obtain ⟨z, hz_ne⟩ := exists_ne (1 : Subgroup.center G)
    let Z : Subgroup G := Subgroup.zpowers (z : G)
    have hz_center : (z : G) ∈ Subgroup.center G := z.property
    have hZ_le_center : Z ≤ Subgroup.center G := zpowers_le_center_of_mem_center_local hz_center
    letI : Z.Normal := normal_of_le_center_local hZ_le_center
    have hZ_ne_bot : Z ≠ ⊥ := by
      intro hZ
      apply hz_ne
      apply Subtype.ext
      have hz_mem : (z : G) ∈ Z := Subgroup.mem_zpowers (z : G)
      have hz_one : (z : G) = 1 := by
        simpa [Z, hZ] using hz_mem
      exact hz_one
    have hq_card : Fintype.card (G ⧸ Z) < Fintype.card G := by
      -- The quotient is strictly smaller because the cyclic kernel is nontrivial.
      simp only [← Nat.card_eq_fintype_card]
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z]
      apply lt_mul_of_one_lt_right
      · exact Nat.card_pos
      · exact (Subgroup.one_lt_card_iff_ne_bot Z).mpr hZ_ne_bot
    letI : IsSupersolvable (G ⧸ Z) := ih (G ⧸ Z) hq_card (hG.to_quotient Z)
    have hZ_cyclic : IsCyclic Z := inferInstance
    exact isSupersolvable_of_normal_cyclic_subgroup_quotient_local Z hZ_cyclic

/-- Helper for Exercise 10-10.5-5: a `p`-elementary finite group is supersolvable. -/
private theorem isSupersolvable_of_isPElementary_local
    {p : ℕ} (hG : IsPElementary p G) :
    IsSupersolvable G := by
  rcases hG with ⟨C, P, hCP⟩
  letI : Fact p.Prime := ⟨hCP.prime⟩
  letI : C.Normal := IsPElementaryDecomposition.cyclic_factor_normal_local hCP
  have hquot_p : IsPGroup p (G ⧸ C) := by
    let e : G ⧸ C ≃* P := hCP.isComplement.symm.QuotientMulEquiv
    exact hCP.isPGroup.of_surjective e.symm.toMonoidHom e.symm.surjective
  letI : IsSupersolvable (G ⧸ C) := isSupersolvable_of_isPGroup_local hquot_p
  -- The quotient by the cyclic factor is the `p`-group factor, so the cyclic-kernel lifting
  -- lemma closes the ambient group.
  exact isSupersolvable_of_normal_cyclic_subgroup_quotient_local C hCP.cyclic

/-- Helper for Exercise 10-10.5-5: an elementary finite group is supersolvable. -/
theorem elementary_group_isSupersolvable
    (hG : IsElementary G) :
    IsSupersolvable G := by
  -- Route correction: use Serre's exact bridge `elementary => p-elementary => p-group/cyclic
  -- kernel => supersolvable`, rather than searching for an unrelated nilpotent shortcut.
  rcases hG with ⟨p, hp⟩
  exact isSupersolvable_of_isPElementary_local hp

/-- Helper for irreducible_fdRepCharacterRing_mem_elementaryLinearCharacterSpan_of_isElementary:
an induced representation has degree equal to the subgroup index times the degree of the
inducing subrepresentation. -/
private theorem finrank_eq_index_mul_finrank_of_isInducedFromSubrepresentation_local
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    {H : Subgroup G}
    (W : Subrepresentation (ρ.comp H.subtype))
    (hInduced : ρ.IsInducedFromSubrepresentation H W) :
    Module.finrank ℂ V = H.index * Module.finrank ℂ W.toSubmodule := by
  classical
  letI : DecidableEq (G ⧸ H) := Classical.decEq _
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  have leftQuotientSubmodule_out_local (q : G ⧸ H) :
      ρ.leftQuotientSubmodule H W q = W.toSubmodule.map (ρ q.out) := by
    simpa [Quotient.out_eq q] using (ρ.leftQuotientSubmodule_mk H W q.out)
  have hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule H W) := by
    -- Unpack the Chapter `3` owner predicate into the corresponding internal direct sum.
    simpa [Representation.IsInducedFromSubrepresentation] using hInduced
  letI := DirectSum.IsInternal.chooseDecomposition (ρ.leftQuotientSubmodule H W) hInternal
  letI : ∀ q : G ⧸ H, Module.Free ℂ (ρ.leftQuotientSubmodule H W q) :=
    fun q ↦ Module.Free.of_divisionRing ℂ _
  let e := (DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule H W)).symm
  -- Compare `V` with the external direct sum of its coset translates and then transport each
  -- summand back to `W`.
  calc
    Module.finrank ℂ V =
        Module.finrank ℂ (DirectSum (G ⧸ H) fun q ↦ ρ.leftQuotientSubmodule H W q) := by
          exact e.finrank_eq.symm
    _ = ∑ q : G ⧸ H, Module.finrank ℂ (ρ.leftQuotientSubmodule H W q) := by
          exact Module.finrank_directSum (R := ℂ) (M := fun q ↦ ρ.leftQuotientSubmodule H W q)
    _ = ∑ _q : G ⧸ H, Module.finrank ℂ W.toSubmodule := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          let eW : W.toSubmodule ≃ₗ[ℂ] ρ.leftQuotientSubmodule H W q :=
            let eV : V ≃ₗ[ℂ] V := LinearEquiv.ofBijective (ρ q.out) (ρ.apply_bijective q.out)
            (eV.submoduleMap W.toSubmodule).trans
              (LinearEquiv.ofEq _ _ (leftQuotientSubmodule_out_local q).symm)
          simpa using eW.finrank_eq.symm
    _ = H.index * Module.finrank ℂ W.toSubmodule := by
          simp [Subgroup.index_eq_card]

end

end Representation
