import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.FixedIsotypicProjectiveExtension

universe u v w x

open scoped TensorProduct

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {h : ℕ}
variable {G : Type v} [Group G] [Finite G]
variable {V : Type x} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]

local notation "k" => IsLocalRing.ResidueField A
private noncomputable instance theorem171761TargetModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance theorem171761TargetScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: in Serre's successor-height quotient branch, the recursive
height witness on `H ⧸ N` already exposes the next normal step `M / N` whose order is either
prime to `p` or a `p`-power. -/
theorem exists_quotient_normal_step_of_psolvableHeight_succ
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (hquot : IsPSolvableOfHeight p (Nat.succ h) (H ⧸ N)) :
    ∃ Mbar : Subgroup (H ⧸ N),
      ∃ _ : Mbar.Normal,
        (Nat.Coprime p (Nat.card Mbar) ∨ IsPGroup p Mbar) ∧
          IsPSolvableOfHeight p h ((H ⧸ N) ⧸ Mbar) := by
  -- Unfold the successor-height witness once so the remaining work can focus on Serre's two
  -- quotient-side cases for the chosen step `M / N`.
  simpa [Nat.succ_eq_add_one] using IsPSolvableOfHeight.succ_iff.mp hquot

/-- Helper for Theorem 17-17.6-1: pulling back Serre's fixed quotient step `M̄ ≤ H ⧸ N` along the
quotient map recovers the literal subgroup `M ≤ H`, and the corresponding double quotient is
canonically `H ⧸ M`. -/
noncomputable def quotient_preimage_equiv_of_quotient_normal_step
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal] :
    ((H ⧸ N) ⧸ Mbar) ≃* H ⧸ Subgroup.comap (QuotientGroup.mk' N) Mbar := by
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  letI : M.Normal := by infer_instance
  have hNM : N ≤ M := QuotientGroup.le_comap_mk' N Mbar
  have hmap : M.map (QuotientGroup.mk' N) = Mbar := by
    -- The quotient map is surjective, so Serre's fixed step is recovered exactly after pullback.
    simpa [M] using
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) Mbar
  -- Route correction: normalize the iterated quotient first, then hand the remaining branch work
  -- to the source-faithful `p`-group / coprime split on the literal subgroup `M ≤ H`.
  exact
    (QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient N M hNM)

/-- Helper for Theorem 17-17.6-1: if Serre's quotient step `M̄ = M / N` has order prime to `p`,
then the literal pullback subgroup `M ≤ H` also has order prime to `p`, because `|M| = |M̄| |N|`.
-/
theorem coprime_card_preimage_of_quotient_normal_step
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (hNcop : Nat.Coprime p (Nat.card N))
    (Mbar : Subgroup (H ⧸ N))
    (hMbar_cop : Nat.Coprime p (Nat.card Mbar)) :
    Nat.Coprime p (Nat.card (Subgroup.comap (QuotientGroup.mk' N) Mbar)) := by
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  let φ : M →* H ⧸ N := (QuotientGroup.mk' N).comp M.subtype
  letI : (N.subgroupOf M).Normal := by infer_instance
  have hNM : N ≤ M := QuotientGroup.le_comap_mk' N Mbar
  have hker : φ.ker = N.subgroupOf M := by
    ext x
    change (QuotientGroup.mk' N ((x : M) : H) = 1) ↔ ((x : H) ∈ N)
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff ((x : M) : H)).mp hx
    · intro hx
      exact (QuotientGroup.eq_one_iff ((x : M) : H)).mpr hx
  have hrange : φ.range = Mbar := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hq
      rcases QuotientGroup.mk'_surjective N q with ⟨x, rfl⟩
      exact ⟨⟨x, hq⟩, rfl⟩
  have hcardNsub : Nat.card (N.subgroupOf M) = Nat.card N := by
    -- The pullback contains `N`, so the restricted kernel subgroup has the same cardinality.
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hcardMquot : Nat.card (M ⧸ N.subgroupOf M) = Nat.card Mbar := by
    -- The quotient of the literal pullback by `N` is exactly Serre's chosen step `M̄`.
    simpa [hker] using
      (Nat.card_congr
        (((QuotientGroup.quotientKerEquivRange φ).trans
            (MulEquiv.subgroupCongr hrange)).toEquiv))
  -- Route correction: keep Serre's literal subgroup `M` and use the exact cardinal factorization
  -- `|M| = |M / N| |N|` instead of introducing a transport-heavy surrogate subgroup.
  rw [show Nat.card M = Nat.card (M ⧸ N.subgroupOf M) * Nat.card (N.subgroupOf M) by
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf M)]
  rw [hcardMquot, hcardNsub]
  exact Nat.Coprime.mul_right hMbar_cop hNcop

/-- Helper for Theorem 17-17.6-1: if Serre's chosen quotient step `M̄ = M / N` has order prime to
`p`, then the literal pullback subgroup `M ≤ H` already gives a same-height recursive call on `H`.
-/
theorem
    exists_residueFieldLift_of_central_cyclic_coprime_kernel_coprime_preimage_branch
    {H : Type v} [Group H] [Finite H]
    {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (N : Subgroup H) [N.Normal]
    (hNcop : Nat.Coprime p (Nat.card N))
    (hrecLower :
      ∀ {G' : Type v} [Group G'] [Finite G']
        {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (hG' : IsPSolvableOfHeight p (Nat.succ h) G')
        (ρ' : Representation k G' V') [ρ'.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G' P)
            (red : P →ₗ[A] V'),
              IsResidueFieldLift ρ' ρA red)
    (τ : Representation k H W) [τ.IsIrreducible]
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal]
    (hMbar_cop : Nat.Coprime p (Nat.card Mbar))
    (hMquot :
      IsPSolvableOfHeight p h
        (H ⧸ Subgroup.comap (QuotientGroup.mk' N) Mbar)) :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A H P)
      (red : P →ₗ[A] W),
        IsResidueFieldLift τ ρA red := by
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  letI : M.Normal := by infer_instance
  have hMcop : Nat.Coprime p (Nat.card M) := by
    -- Serre's literal subgroup `M` inherits prime-to-`p` order from `M / N` and `N`.
    simpa [M] using
      coprime_card_preimage_of_quotient_normal_step
        (p := p) (N := N) hNcop Mbar hMbar_cop
  have hHsolv : IsPSolvableOfHeight p (Nat.succ h) H := by
    -- Reinsert the prime-to-`p` subgroup `M` as the first step in the height tower for `H`.
    refine IsPSolvableOfHeight.succ_iff.mpr ?_
    exact ⟨M, inferInstance, Or.inl hMcop, by simpa [M] using hMquot⟩
  -- The coprime branch is now exactly the recursive same-height call on `H`.
  exact hrecLower hHsolv τ

/-- Helper for Theorem 17-17.6-1: in Serre's `p`-group quotient branch, Schur-Zassenhaus may be
applied inside the literal pullback subgroup `M := preimage(M̄)` to split off a `p`-group
complement to `N`. This isolates the concrete subgroup data before the later quotient descent. -/
theorem pgroup_preimage_complement_data_of_quotient_normal_step
    (hp : Nat.Prime p)
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (hNcop : Nat.Coprime p (Nat.card N))
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal]
    (hMp : IsPGroup p Mbar) :
    ∃ P : Subgroup H,
      P ≤ Subgroup.comap (QuotientGroup.mk' N) Mbar ∧
      IsPGroup p P ∧
      Disjoint N P ∧
      N ⊔ P = Subgroup.comap (QuotientGroup.mk' N) Mbar := by
  letI : Fact p.Prime := ⟨hp⟩
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  let Nsub : Subgroup M := N.subgroupOf M
  letI : M.Normal := by infer_instance
  letI : Nsub.Normal := by infer_instance
  have hNM : N ≤ M := QuotientGroup.le_comap_mk' N Mbar
  let φ : M →* H ⧸ N := (QuotientGroup.mk' N).comp M.subtype
  have hker : φ.ker = Nsub := by
    ext x
    change (QuotientGroup.mk' N ((x : M) : H) = 1) ↔ ((x : H) ∈ N)
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff ((x : M) : H)).mp hx
    · intro hx
      exact (QuotientGroup.eq_one_iff ((x : M) : H)).mpr hx
  have hrange : φ.range = Mbar := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hq
      rcases QuotientGroup.mk'_surjective N q with ⟨x, rfl⟩
      exact ⟨⟨x, hq⟩, rfl⟩
  have hcardNsub : Nat.card Nsub = Nat.card N := by
    -- Passing to the subgroup-of-subgroup view does not change the kernel cardinality.
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hcardMquot : Nat.card (M ⧸ Nsub) = Nat.card Mbar := by
    -- The quotient of the literal pullback by `N` is exactly Serre's chosen quotient step `M̄`.
    simpa [hker] using
      (Nat.card_congr
        (((QuotientGroup.quotientKerEquivRange φ).trans
            (MulEquiv.subgroupCongr hrange)).toEquiv))
  have hindexNsub : Nsub.index = Nat.card Mbar := by
    rw [Subgroup.index_eq_card]
    exact hcardMquot
  have hcopNsub :
      Nat.Coprime (Nat.card Nsub) Nsub.index := by
    obtain ⟨n, hn⟩ := hMp.exists_card_eq
    rw [hcardNsub, hindexNsub, hn]
    exact hNcop.symm.pow_right n
  obtain ⟨Q, hQcomp⟩ := Subgroup.exists_right_complement'_of_coprime (N := Nsub) hcopNsub
  have hMquot_p : IsPGroup p (M ⧸ Nsub) := by
    -- Serre's quotient step `M / N` is literally the chosen `p`-group `M̄`.
    have hMquot_p' : IsPGroup p (M ⧸ φ.ker) := by
      exact
        hMp.of_equiv
          ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange)).symm
    exact hMquot_p'.of_equiv (QuotientGroup.quotientMulEquivOfEq hker)
  have hQp : IsPGroup p Q := by
    -- A complement to the prime-to-`p` subgroup `N` identifies with the quotient `M / N`.
    exact hMquot_p.of_equiv (hQcomp.symm.QuotientMulEquiv)
  let P : Subgroup H := Q.map M.subtype
  have hP_le_M : P ≤ M := by
    exact Subgroup.map_subtype_le Q
  have hP_disjoint : Disjoint N P := by
    have hdisj_map :
        Disjoint ((N.subgroupOf M).map M.subtype) (Q.map M.subtype) := by
      exact Subgroup.disjoint_map (f := M.subtype) Subtype.coe_injective hQcomp.disjoint
    have hmapN : (N.subgroupOf M).map M.subtype = N := by
      simpa [M] using Subgroup.map_subgroupOf_eq_of_le hNM
    simpa [P, hmapN] using hdisj_map
  have hP_sup : N ⊔ P = M := by
    have hmapN : (N.subgroupOf M).map M.subtype = N := by
      simpa [M] using Subgroup.map_subgroupOf_eq_of_le hNM
    calc
      N ⊔ P = (N.subgroupOf M).map M.subtype ⊔ Q.map M.subtype := by
        simp [P, hmapN]
      _ = ((N.subgroupOf M) ⊔ Q).map M.subtype := by
        rw [Subgroup.map_sup]
      _ = (⊤ : Subgroup M).map M.subtype := by rw [hQcomp.sup_eq_top]
      _ = M := by
        simpa [MonoidHom.range_eq_map] using M.range_subtype
  refine ⟨P, hP_le_M, ?_, hP_disjoint, hP_sup⟩
  -- The concrete complement subgroup `P ≤ H` is a `p`-group because it comes from the quotient
  -- `M / N ≃ M̄`, which is already the `p`-group step in Serre's recursion.
  simpa [P] using hQp.map M.subtype

/-- Helper for Theorem 17-17.6-1: once Serre's literal split `M = N × P` is fixed with `N`
central and of order prime to `p`, the complement `P` is already normal in `H`. The proof keeps
the source route: first show `P` is normal in `M` because conjugation by `n * p` reduces to
conjugation by `p`, then upgrade to `H` by identifying `P` with the unique Sylow `p`-subgroup of
`M`. -/
theorem normal_of_pgroup_preimage_complement
    (hp : Nat.Prime p)
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (hNcentral : N ≤ Subgroup.center H)
    (hNcop : Nat.Coprime p (Nat.card N))
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal]
    (P : Subgroup H)
    (hP_le :
      P ≤ Subgroup.comap (QuotientGroup.mk' N) Mbar)
    (hPp : IsPGroup p P)
    (hP_disjoint : Disjoint N P)
    (hP_sup :
      N ⊔ P = Subgroup.comap (QuotientGroup.mk' N) Mbar) :
    P.Normal := by
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  letI : M.Normal := by infer_instance
  let Nsub : Subgroup M := N.subgroupOf M
  let Psub : Subgroup M := P.subgroupOf M
  have hNM : N ≤ M := QuotientGroup.le_comap_mk' N Mbar
  have hN_le_normalizer : N ≤ Subgroup.normalizer P := by
    -- The central kernel `N` normalizes `P` because conjugation by `n ∈ N` is trivial.
    intro n hn
    rw [Subgroup.mem_normalizer_iff']
    intro x
    rw [(Subgroup.mem_center_iff.mp (hNcentral hn) x).symm]
  have hM_le_normalizer : M ≤ Subgroup.normalizer P := by
    -- Route correction: use the literal split `M = N ⊔ P` elementwise to show all of `M`
    -- normalizes `P`.
    let T : Subgroup H := Subgroup.normalizer P
    have hN_le_T : N ≤ T := hN_le_normalizer
    intro m hm
    have hmSup : m ∈ N ⊔ P := by
      simpa [M, hP_sup] using hm
    rcases (Subgroup.mem_sup_of_normal_left.mp hmSup) with ⟨n, hnN, u, huP, rfl⟩
    have hu_norm : u ∈ T := by
      exact (Subgroup.le_normalizer (H := P)) huP
    have hmul : n * u ∈ T := T.mul_mem (hN_le_T hnN) hu_norm
    simpa [T] using hmul
  have hPsub_normal : Psub.Normal := by
    -- Inside `M`, the complement `P` is normal because `M ≤ normalizer(P)`.
    exact Subgroup.normal_subgroupOf_of_le_normalizer hM_le_normalizer
  have hNsub_disjoint : Disjoint Nsub Psub := by
    -- The pullback split keeps the factors disjoint after passing to `M`.
    rw [Subgroup.disjoint_def]
    intro x hxN hxP
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hP_disjoint) hxN hxP
  have hNsub_sup_top : Nsub ⊔ Psub = ⊤ := by
    -- Any element of `M` already decomposes as an `N`-part times a `P`-part by the source split.
    ext x
    constructor
    · intro _
      simp
    · intro _
      have hxSup : ((x : M) : H) ∈ N ⊔ P := by
        simpa [M, hP_sup] using x.property
      rcases (Subgroup.mem_sup_of_normal_left.mp hxSup) with ⟨n, hnN, p, hpP, hnp⟩
      refine (Subgroup.mem_sup_of_normal_left).2 ?_
      exact ⟨⟨n, hNM hnN⟩, hnN, ⟨p, hP_le hpP⟩, hpP, Subtype.ext hnp⟩
  have hcomp : Nsub.IsComplement' Psub := by
    -- The restricted factors inside `M` are complementary in the exact Schur-Zassenhaus split.
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hNsub_disjoint ?_
    simpa [hNsub_sup_top] using (Subgroup.normal_mul Nsub Psub).symm
  have hPsub_p : IsPGroup p Psub := by
    -- Passing from `P ≤ H` to `P ≤ M` does not change the `p`-group structure.
    exact hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hP_le).symm
  have hcardNsub : Nat.card Nsub = Nat.card N := by
    -- The kernel subgroup keeps the same cardinality inside the pullback.
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hindexPsub : Psub.index = Nat.card Nsub := by
    -- In a complement decomposition, the index of `P` in `M` is the cardinality of `N`.
    exact hcomp.index_eq_card
  have hPsub_not_dvd : ¬ p ∣ Psub.index := by
    -- The prime-to-`p` order of `N` forces the complement index to be prime to `p`.
    rw [hindexPsub, hcardNsub]
    exact hp.coprime_iff_not_dvd.mp hNcop
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  let PsubSylow : Sylow p M := IsPGroup.toSylow (P := Psub) hPsub_p hPsub_not_dvd
  have hPsub_char : Psub.Characteristic := by
    -- A normal Sylow subgroup is characteristic, so Serre's complement is fixed by all
    -- automorphisms of `M`.
    exact
      Sylow.characteristic_of_normal PsubSylow
        (by simpa [IsPGroup.toSylow_coe (P := Psub) hPsub_p hPsub_not_dvd] using hPsub_normal)
  letI : Psub.Characteristic := hPsub_char
  have hmapPsub : Subgroup.map M.subtype Psub = P := by
    -- Mapping the restricted complement back into `H` recovers the literal subgroup `P`.
    simpa [Psub] using Subgroup.map_subgroupOf_eq_of_le hP_le
  -- Upgrade normality from `M` to `H` by characteristic transport along the normal pullback `M`.
  rw [← hmapPsub]
  exact ConjAct.normal_of_characteristic_of_normal (H := M) (K := Psub)

/-- Helper for Theorem 17-17.6-1: the quotient package attached to the concrete split
`M = N × P` in the `p`-group branch. -/
structure PgroupPreimageSplitQuotientData
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal]
    (P : Subgroup H) [P.Normal]
    where
  hN_image_central :
    N.map (QuotientGroup.mk' P) ≤ Subgroup.center (H ⧸ P)
  hN_image_cyclic :
    IsCyclic (N.map (QuotientGroup.mk' P))
  hN_image_coprime :
    Nat.Coprime p (Nat.card (N.map (QuotientGroup.mk' P)))
  hQuotientHeight :
    IsPSolvableOfHeight p (Nat.succ h) (H ⧸ P)
  quotientEquiv :
    ((H ⧸ P) ⧸ N.map (QuotientGroup.mk' P)) ≃*
      H ⧸ Subgroup.comap (QuotientGroup.mk' N) Mbar

noncomputable def central_cyclic_image_quotient_data_of_pgroup_preimage_split
    {H : Type v} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal]
    (hNcentral : N ≤ Subgroup.center H)
    (hNcyclic : IsCyclic N)
    (hNcop : Nat.Coprime p (Nat.card N))
    (Mbar : Subgroup (H ⧸ N)) [Mbar.Normal]
    (P : Subgroup H) [P.Normal]
    (hP_le :
      P ≤ Subgroup.comap (QuotientGroup.mk' N) Mbar)
    (hP_disjoint : Disjoint N P)
    (hP_sup :
      N ⊔ P = Subgroup.comap (QuotientGroup.mk' N) Mbar)
    (hMquot :
      IsPSolvableOfHeight p h
        (H ⧸ Subgroup.comap (QuotientGroup.mk' N) Mbar)) :
    PgroupPreimageSplitQuotientData
      (p := p) (h := h) (N := N) Mbar P := by
  let M : Subgroup H := Subgroup.comap (QuotientGroup.mk' N) Mbar
  let q : H →* H ⧸ P := QuotientGroup.mk' P
  let N' : Subgroup (H ⧸ P) := N.map q
  letI : N'.Normal := by infer_instance
  have hmapM : M.map q = N' := by
    -- Quotienting the split `M = N ⊔ P` by `P` kills exactly the `P`-factor.
    calc
      M.map q = (N ⊔ P).map q := by rw [hP_sup]
      _ = N.map q ⊔ P.map q := by rw [Subgroup.map_sup]
      _ = N.map q ⊔ ⊥ := by rw [QuotientGroup.map_mk'_self P]
      _ = N' := by simp [N']
  have hcomapN' : Subgroup.comap q N' = M := by
    -- The image subgroup `N'` pulls back to the original Serre step `M`.
    calc
      Subgroup.comap q N' = Subgroup.comap q (M.map q) := by rw [hmapM]
      _ = M := by
        rw [Subgroup.comap_map_eq_self]
        simpa [M, q, QuotientGroup.ker_mk'] using hP_le
  have hN'_central : N' ≤ Subgroup.center (H ⧸ P) := by
    -- Centrality of `N` survives after pushing it into the quotient by `P`.
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨n, hnN, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    rcases QuotientGroup.mk'_surjective P y with ⟨h, rfl⟩
    have hcomm : h * (n : H) = (n : H) * h := Subgroup.mem_center_iff.mp (hNcentral hnN) h
    simpa using congrArg (QuotientGroup.mk' P) hcomm
  let φ : N →* H ⧸ P := q.comp N.subtype
  have hφker : φ.ker = ⊥ := by
    -- Disjointness with `P` makes the quotient map injective on the central kernel `N`.
    rw [MonoidHom.ker_eq_bot_iff]
    intro n₁ n₂ hEq
    apply Subtype.ext
    have hmem :
        ((n₁ : N) : H) / (n₂ : H) ∈ P := by
      exact (QuotientGroup.eq_iff_div_mem).mp hEq
    have hdiv_one : ((n₁ : N) : H) / (n₂ : H) = 1 := by
      exact
        (Subgroup.disjoint_def.mp hP_disjoint)
          (by
            exact
              N.div_mem n₁.property n₂.property)
          hmem
    exact div_eq_one.mp hdiv_one
  have hφrange : φ.range = N' := by
    -- The restricted quotient map has image exactly `N.map q`.
    ext z
    constructor
    · rintro ⟨n, rfl⟩
      exact Subgroup.mem_map.mpr ⟨(n : N), n.property, rfl⟩
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨n, hnN, rfl⟩
      exact ⟨⟨n, hnN⟩, rfl⟩
  let eN : N ≃* N' :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
        ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hφrange)))
  have hN'_cyclic : IsCyclic N' := by
    -- Injectivity on `N` transports Serre's cyclic kernel to the quotient image `N'`.
    letI : IsCyclic N := hNcyclic
    exact isCyclic_of_surjective eN eN.surjective
  have hcardN' : Nat.card N' = Nat.card N := by
    -- The same restricted equivalence transports the cardinality of the kernel.
    exact (Nat.card_congr eN.toEquiv).symm
  have hN'_cop : Nat.Coprime p (Nat.card N') := by
    -- Coprimality with `p` is unchanged under the kernel-image equivalence.
    exact hcardN'.symm ▸ hNcop
  have hquotEquiv :
      ((H ⧸ P) ⧸ N') ≃* H ⧸ M := by
    -- Reuse the existing third-isomorphism step with kernel `P` and then rewrite the pullback
    -- subgroup back to the literal Serre step `M`.
    exact
      (quotient_preimage_equiv_of_quotient_normal_step (N := P) N').trans
        (QuotientGroup.quotientMulEquivOfEq hcomapN')
  have hQuotLower : IsPSolvableOfHeight p h ((H ⧸ P) ⧸ N') := by
    -- Transport Serre's lower-height witness through the concrete quotient equivalence.
    exact IsPSolvableOfHeight.of_equiv hquotEquiv.symm hMquot
  refine
    ⟨hN'_central, hN'_cyclic, hN'_cop, ?_, hquotEquiv⟩
  -- The quotient by `P` is again one Serre step above the lower-height quotient by `N'`.
  exact IsPSolvableOfHeight.succ_iff.mpr ⟨N', inferInstance, Or.inl hN'_cop, hQuotLower⟩

end

end Representation
