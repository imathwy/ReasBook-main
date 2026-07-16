import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Serre.Chap03.Definition_3_3_3_1
import LinearRepresentations_Serre_1977.Serre.Chap03.Exercise_3_3_3_6
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Serre.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Serre.Chap08.Definition_8_8_3_2
import LinearRepresentations_Serre_1977.Serre.Chap08.Exercise_8_8_3_9
import LinearRepresentations_Serre_1977.Serre.Chap10.Definition_10_10_1_3
import LinearRepresentations_Serre_1977.Serre.Chap10.MonomialCharacter
import LinearRepresentations_Serre_1977.Serre.Chap10.Theorem_10_10_5_2.BrauerInductionInfrastructure
import LinearRepresentations_Serre_1977.Serre.Chap10.Theorem_10_10_5_2.InducedModelEquivalence

noncomputable section

namespace Representation

open CategoryTheory Rep
open scoped Representation SubgroupInduction
open scoped BigOperators Pointwise

section

variable {G : Type} [Group G] [Finite G]

/-- A subgroup of a finite group is finite. -/
local instance theorem_10_10_5_2_quotient_reduction_fintype_of_finite : Fintype G := Fintype.ofFinite G

/-- A subgroup of a finite group is finite. -/
local instance theorem_10_10_5_2_quotient_reduction_subgroup_fintype_of_finite (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H
/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a monomial
finite-dimensional complex representation contributes a class in the monomial-character span. -/
theorem fdRepCharacterRing_mem_monomialCharacterSpan_of_isMonomial
    (V : FDRep ℂ G) (hmono : Representation.IsMonomial V.ρ) :
    fdRepCharacterRing V ∈ monomialCharacterSpan G := by
  have hmonchar : IsMonomialCharacter V.character :=
    Representation.isMonomialCharacter_of_isMonomial (ρ := V.ρ) hmono
  -- Bundle the character into `R(G)` and apply the span membership theorem.
  simpa [fdRepCharacterRing] using
    (Representation.mem_monomialCharacterSpan_of_isMonomialCharacter hmonchar)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the trivial coset
decomposition at `⊤` witnesses inducedness from the whole group. -/
lemma isInducedFromSubrepresentation_top_local
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.IsInducedFromSubrepresentation
      (⊤ : Subgroup G)
      (⊤ : Subrepresentation (ρ.comp (⊤ : Subgroup G).subtype)) := by
  classical
  let _ : DecidableEq (G ⧸ (⊤ : Subgroup G)) := Classical.decEq _
  letI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  -- With only one left coset, the induced decomposition has a single summand `⊤`.
  unfold Representation.IsInducedFromSubrepresentation
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_def]
    intro q
    have hbot :
        (⨆ j,
            ⨆ (_ : j ≠ q),
              ρ.leftQuotientSubmodule
                (⊤ : Subgroup G)
                (⊤ : Subrepresentation (ρ.comp (⊤ : Subgroup G).subtype))
                j) = ⊥ := by
      apply le_antisymm ?_ bot_le
      rw [iSup_le_iff]
      intro j
      rw [iSup_le_iff]
      intro hneq
      exfalso
      exact hneq (Subsingleton.elim _ _)
    have hqtop :
        ρ.leftQuotientSubmodule
          (⊤ : Subgroup G)
          (⊤ : Subrepresentation (ρ.comp (⊤ : Subgroup G).subtype))
          q = ⊤ := by
      refine Quotient.inductionOn' q ?_
      intro g
      rw [Representation.leftQuotientSubmodule_mk]
      change Submodule.map (ρ g) (⊤ : Submodule ℂ V) = ⊤
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.mpr (ρ.apply_bijective g).surjective
    rw [hbot, hqtop]
    exact disjoint_bot_right
  · apply top_unique
    intro x _
    have hqtop :
        ρ.leftQuotientSubmodule
          (⊤ : Subgroup G)
          (⊤ : Subrepresentation (ρ.comp (⊤ : Subgroup G).subtype))
          1 = ⊤ := by
      change
        ρ.leftQuotientSubmodule
            (⊤ : Subgroup G)
            (⊤ : Subrepresentation (ρ.comp (⊤ : Subgroup G).subtype))
            (QuotientGroup.mk 1) = ⊤
      rw [Representation.leftQuotientSubmodule_mk]
      change Submodule.map (ρ 1) (⊤ : Submodule ℂ V) = ⊤
      rw [Submodule.map_top]
      exact LinearMap.range_eq_top.mpr (ρ.apply_bijective 1).surjective
    have hx :
        x ∈
          ρ.leftQuotientSubmodule
            (⊤ : Subgroup G)
            (⊤ : Subrepresentation (ρ.comp (⊤ : Subgroup G).subtype))
            1 := by
      simpa [hqtop]
    exact
      le_iSup
        (fun q ↦
          ρ.leftQuotientSubmodule
            (⊤ : Subgroup G)
            (⊤ : Subrepresentation (ρ.comp (⊤ : Subgroup G).subtype))
            q)
        1 hx

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: quotienting by a
normal subgroup that acts trivially preserves irreducibility. -/
lemma isIrreducible_of_ofQuotient_of_isTrivial_local
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (S : Subgroup G) [S.Normal]
    [Representation.IsTrivial (ρ.comp S.subtype)] [ρ.IsIrreducible] :
    Representation.IsIrreducible (ρ.ofQuotient S) := by
  letI : Nontrivial (Subrepresentation (ρ.ofQuotient S)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  -- Any nonzero quotient-stable subspace is already a nonzero `ρ`-subrepresentation.
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W hW
  let W' : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        simpa using W.apply_mem_toSubmodule (g : G ⧸ S) hx }
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro hW'
    apply hW
    apply Subrepresentation.toSubmodule_injective
    simpa [W'] using congrArg Subrepresentation.toSubmodule hW'
  have hW'_top : W' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W').resolve_left hW'_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W'] using congrArg Subrepresentation.toSubmodule hW'_top

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the quotient map
restricts to a canonical homomorphism from the pulled-back subgroup `H.comap (G → G ⧸ N)` into
`H`. -/
theorem quotient_comap_subgroup_map_mem_local
    {Q : Type} [Group Q]
    {N : Subgroup Q} [N.Normal]
    (H : Subgroup (Q ⧸ N)) :
    ∀ y : H.comap (QuotientGroup.mk' N),
      ((QuotientGroup.mk' N).comp (H.comap (QuotientGroup.mk' N)).subtype) y ∈ H := by
  intro y
  exact y.2

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the quotient map
restricts to a canonical homomorphism from the pulled-back subgroup `H.comap (G → G ⧸ N)` into
`H`. -/
noncomputable def quotient_comap_subgroup_map_local
    {Q : Type} [Group Q]
    {N : Subgroup Q} [N.Normal]
    (H : Subgroup (Q ⧸ N)) :
    H.comap (QuotientGroup.mk' N) →* H :=
  (((QuotientGroup.mk' N).comp (H.comap (QuotientGroup.mk' N)).subtype).codRestrict H
    (quotient_comap_subgroup_map_mem_local H))

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a subrepresentation
downstairs on `H ≤ G ⧸ N` can be read as the same underlying submodule for the pulled-back
representation on `H.comap (G → G ⧸ N)`. -/
theorem quotient_comap_subrepresentation_apply_mem_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {N : Subgroup Q} [N.Normal]
    (σ : Representation ℂ (Q ⧸ N) V)
    (H : Subgroup (Q ⧸ N))
    (W : Subrepresentation (σ.comp H.subtype)) :
    ∀ g x, x ∈ W.toSubmodule →
      ((σ.comp (QuotientGroup.mk' N)).comp (H.comap (QuotientGroup.mk' N)).subtype) g x ∈
        W.toSubmodule := by
  intro g x hx
  let πH : H.comap (QuotientGroup.mk' N) →* H := quotient_comap_subgroup_map_local H
  -- The pulled-back action factors through the codomain element `πH g : H`.
  simpa [πH] using W.apply_mem_toSubmodule (πH g) hx

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a subrepresentation
downstairs on `H ≤ G ⧸ N` can be read as the same underlying submodule for the pulled-back
representation on `H.comap (G → G ⧸ N)`. -/
noncomputable def quotient_comap_subrepresentation_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {N : Subgroup Q} [N.Normal]
    (σ : Representation ℂ (Q ⧸ N) V)
    (H : Subgroup (Q ⧸ N))
    (W : Subrepresentation (σ.comp H.subtype)) :
    Subrepresentation
      ((σ.comp (QuotientGroup.mk' N)).comp (H.comap (QuotientGroup.mk' N)).subtype) where
  toSubmodule := W.toSubmodule
  apply_mem_toSubmodule := quotient_comap_subrepresentation_apply_mem_local σ H W

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: pulling the subgroup
witness back along the quotient map keeps the underlying one-dimensional vector space unchanged.
-/
@[simp] theorem quotient_comap_subrepresentation_finrank_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {N : Subgroup Q} [N.Normal]
    (σ : Representation ℂ (Q ⧸ N) V)
    (H : Subgroup (Q ⧸ N))
    (W : Subrepresentation (σ.comp H.subtype)) :
    Module.finrank ℂ (quotient_comap_subrepresentation_local σ H W).toSubmodule =
      Module.finrank ℂ W.toSubmodule :=
  rfl

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the quotient map
`G → G ⧸ N` identifies the left cosets of `H.comap (G → G ⧸ N)` in `G` with the left cosets of
`H` in `G ⧸ N`. -/
noncomputable def quotient_comap_leftCosetEquiv_local
    {Q : Type} [Group Q]
    {N : Subgroup Q} [N.Normal]
    (H : Subgroup (Q ⧸ N)) :
    Q ⧸ H.comap (QuotientGroup.mk' N) ≃ (Q ⧸ N) ⧸ H := by
  classical
  let q : Q →* Q ⧸ N := QuotientGroup.mk' N
  let s : Q ⧸ N → Q := fun x ↦ Classical.choose (QuotientGroup.mk'_surjective N x)
  have hs : ∀ x : Q ⧸ N, q (s x) = x := fun x ↦
    Classical.choose_spec (QuotientGroup.mk'_surjective N x)
  refine
    { toFun := Quotient.lift (fun g : Q ↦ ((g : Q ⧸ N) : (Q ⧸ N) ⧸ H)) ?_
      invFun := Quotient.lift (fun x : Q ⧸ N ↦ ((s x : Q) : Q ⧸ H.comap q)) ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro g₁ g₂ hgg
    apply Quotient.sound'
    show QuotientGroup.leftRel H (q g₁) (q g₂)
    simpa [QuotientGroup.leftRel_apply, q, Subgroup.mem_comap, map_mul] using hgg
  · intro x y hxy
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    show q ((s x)⁻¹ * s y) ∈ H
    rw [map_mul]
    simpa [QuotientGroup.leftRel_apply, hs x, hs y] using hxy
  · intro g
    refine Quotient.inductionOn' g ?_
    intro a
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    show q ((s (q a))⁻¹ * a) ∈ H
    rw [map_mul]
    simpa [hs (q a)] using (show ((q a)⁻¹ * q a) ∈ H by simp)
  · intro x
    refine Quotient.inductionOn' x ?_
    intro y
    change ((q (s y) : Q ⧸ N) : (Q ⧸ N) ⧸ H) = (y : (Q ⧸ N) ⧸ H)
    simp [q, hs]

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: after reindexing the
cosets by the quotient map, the upstairs left-quotient summands are literally the downstairs
summands. -/
theorem leftQuotientSubmodule_quotient_comap_eq_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {N : Subgroup Q} [N.Normal]
    (σ : Representation ℂ (Q ⧸ N) V)
    (H : Subgroup (Q ⧸ N))
    (W : Subrepresentation (σ.comp H.subtype))
    (q : Q ⧸ H.comap (QuotientGroup.mk' N)) :
    ((show Representation ℂ Q V from σ.comp (QuotientGroup.mk' N)).leftQuotientSubmodule
        (H.comap (QuotientGroup.mk' N))
        (quotient_comap_subrepresentation_local σ H W)
        q) =
      σ.leftQuotientSubmodule H W (quotient_comap_leftCosetEquiv_local H q) := by
  refine Quotient.inductionOn' q ?_
  intro g
  -- Both summands are the image of `W` under the same operator `σ ((QuotientGroup.mk' N) g)`.
  simp [quotient_comap_leftCosetEquiv_local, quotient_comap_subrepresentation_local]

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: pulling an induced
witness back along the quotient map preserves the Chapter 3 internal direct-sum decomposition. -/
lemma isInducedFromSubrepresentation_comp_quotient_mk_of_isInducedFromSubrepresentation_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {N : Subgroup Q} [N.Normal]
    (σ : Representation ℂ (Q ⧸ N) V)
    (H : Subgroup (Q ⧸ N))
    (W : Subrepresentation (σ.comp H.subtype))
    (hWinduced : σ.IsInducedFromSubrepresentation H W) :
    (show Representation ℂ Q V from σ.comp (QuotientGroup.mk' N)).IsInducedFromSubrepresentation
      (H.comap (QuotientGroup.mk' N))
      (quotient_comap_subrepresentation_local σ H W) := by
  classical
  let ρQ : Representation ℂ Q V := σ.comp (QuotientGroup.mk' N)
  let e := quotient_comap_leftCosetEquiv_local (Q := Q) (N := N) H
  let _ : DecidableEq (Q ⧸ H.comap (QuotientGroup.mk' N)) := Classical.decEq _
  let _ : DecidableEq ((Q ⧸ N) ⧸ H) := Classical.decEq _
  have hinternal :
      DirectSum.IsInternal (σ.leftQuotientSubmodule H W) := by
    -- Unpack the downstairs inducedness witness once so the upstairs proof can be a pure
    -- reindexing argument.
    simpa [Representation.IsInducedFromSubrepresentation] using hWinduced
  have hleft_fun :
      ρQ.leftQuotientSubmodule
          (H.comap (QuotientGroup.mk' N))
          (quotient_comap_subrepresentation_local σ H W) =
        σ.leftQuotientSubmodule H W ∘ e := by
    funext q
    simpa [ρQ, e, Function.comp] using
      leftQuotientSubmodule_quotient_comap_eq_local (Q := Q) (N := N) σ H W q
  have hindep :
      iSupIndep
        (ρQ.leftQuotientSubmodule
          (H.comap (QuotientGroup.mk' N))
          (quotient_comap_subrepresentation_local σ H W)) := by
    -- Route correction: transfer the Chapter 3 internal decomposition across the quotient-coset
    -- equivalence instead of comparing induced owners directly.
    rw [hleft_fun]
    exact hinternal.submodule_iSupIndep.comp e.injective
  have hspan :
      iSup
          (ρQ.leftQuotientSubmodule
            (H.comap (QuotientGroup.mk' N))
            (quotient_comap_subrepresentation_local σ H W)) =
        ⊤ := by
    -- The same reindexing carries the spanning statement upstairs.
    calc
      iSup
          (ρQ.leftQuotientSubmodule
            (H.comap (QuotientGroup.mk' N))
            (quotient_comap_subrepresentation_local σ H W)) =
        iSup (σ.leftQuotientSubmodule H W ∘ e) := by
          rw [hleft_fun]
      _ = iSup (σ.leftQuotientSubmodule H W) := by
          apply le_antisymm
          · rw [iSup_le_iff]
            intro q
            exact le_iSup (σ.leftQuotientSubmodule H W) (e q)
          · rw [iSup_le_iff]
            intro q
            simpa [Function.comp] using le_iSup (σ.leftQuotientSubmodule H W ∘ e) (e.symm q)
      _ = ⊤ := hinternal.submodule_iSup_eq_top
  -- Package the transported independence and spanning statements back into the Chapter 3 owner.
  unfold Representation.IsInducedFromSubrepresentation
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep hspan

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: monomiality for a
quotient representation pulls back along the quotient map by taking the inverse image of the
witnessing subgroup. -/
theorem isMonomial_comp_quotient_mk_of_isMonomial_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    {N : Subgroup Q} [N.Normal]
    (σ : Representation ℂ (Q ⧸ N) V)
    (hσ : σ.IsMonomial) :
    (show Representation ℂ Q V from σ.comp (QuotientGroup.mk' N)).IsMonomial := by
  rcases hσ with ⟨H, W, hWdim, hWinduced⟩
  let K : Subgroup Q := H.comap (QuotientGroup.mk' N)
  let W' :
      Subrepresentation
        (((show Representation ℂ Q V from σ.comp (QuotientGroup.mk' N)).comp K.subtype)) :=
    quotient_comap_subrepresentation_local σ H W
  refine ⟨K, W', ?_, ?_⟩
  · -- The quotient pullback does not change the underlying carrier of the witness subspace.
    calc
      Module.finrank ℂ W'.toSubmodule = Module.finrank ℂ W.toSubmodule := by
        simpa [W', K] using quotient_comap_subrepresentation_finrank_local σ H W
      _ = 1 := hWdim
  · -- The quotient branch closes directly at the internal direct-sum level.
    simpa [K, W'] using
      isInducedFromSubrepresentation_comp_quotient_mk_of_isInducedFromSubrepresentation_local
        (Q := Q) (N := N) σ H W hWinduced

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: if the quotient
representation by the kernel is monomial, then the original representation is monomial by pulling
the witness back along the quotient map. -/
theorem isMonomial_of_quotient_ker_isMonomial_local
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    [Representation.IsTrivial (ρ.comp ρ.ker.subtype)]
    (hquot : (ρ.ofQuotient ρ.ker).IsMonomial) :
    ρ.IsMonomial := by
  -- The quotient-pullback lemma applies to `ρ.ofQuotient ρ.ker`, and the resulting pulled-back
  -- representation is definitionally the original action `ρ`.
  simpa using
    (isMonomial_comp_quotient_mk_of_isMonomial_local
      (Q := G) (N := ρ.ker) (σ := ρ.ofQuotient ρ.ker) hquot)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a nontrivial finite
supersolvable group has a nontrivial normal cyclic subgroup. -/
lemma exists_nontrivial_normal_cyclic_subgroup_of_nontrivial_supersolvable_local
    {Q : Type} [Group Q] [IsSupersolvable Q] [Nontrivial Q] :
    ∃ B : Subgroup Q, B.Normal ∧ B ≠ ⊥ ∧ IsCyclic B := by
  classical
  let hsup : IsSupersolvable Q := inferInstance
  rcases hsup.supersolvable with ⟨n, f, _, hnormal, hcyclic, h0, hn⟩
  -- Pick the first nontrivial term in a supersolvable series.
  have hex : ∃ m, m ≤ n ∧ f m ≠ ⊥ := by
    refine ⟨n, le_rfl, ?_⟩
    simp [hn]
  let m := Nat.find hex
  have hm_le_n : m ≤ n := (Nat.find_spec hex).1
  have hm_ne_bot : f m ≠ ⊥ := (Nat.find_spec hex).2
  have hm_min : ∀ k, k < m → f k = ⊥ := by
    intro k hk
    by_contra hk_ne_bot
    have hk_witness : k ≤ n ∧ f k ≠ ⊥ :=
      ⟨Nat.le_trans (Nat.le_of_lt hk) hm_le_n, hk_ne_bot⟩
    exact Nat.find_min hex hk hk_witness
  have hm_ne_zero : m ≠ 0 := by
    intro hm0
    apply hm_ne_bot
    simp [m, hm0, h0]
  obtain ⟨k, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne_zero
  have hk1_le_n : k + 1 ≤ n := by
    simpa [m, hk_eq] using hm_le_n
  have hk_lt : k < n := Nat.lt_of_succ_le hk1_le_n
  have hk_bot : f k = ⊥ := hm_min k (by simp [m, hk_eq])
  have hk1_normal : (f (k + 1)).Normal := by
    by_cases hk1_lt_n : k + 1 < n
    · exact hnormal (k + 1) hk1_lt_n
    · have hk1_eq_n : k + 1 = n := le_antisymm hk1_le_n (Nat.le_of_not_gt hk1_lt_n)
      rw [hk1_eq_n, hn]
      infer_instance
  refine ⟨f (k + 1), hk1_normal, ?_, ?_⟩
  · simpa [m, hk_eq] using hm_ne_bot
  · letI : (f k).Normal := hnormal k hk_lt
    letI : ((f k).subgroupOf (f (k + 1))).Normal := (hnormal k hk_lt).subgroupOf (f (k + 1))
    let e : f (k + 1) ⧸ (f k).subgroupOf (f (k + 1)) ≃* f (k + 1) ⧸ (⊥ : Subgroup (f (k + 1))) :=
      QuotientGroup.quotientMulEquivOfEq (by simp [hk_bot])
    have hcyc_quot : IsCyclic (f (k + 1) ⧸ (⊥ : Subgroup (f (k + 1)))) :=
      e.isCyclic.mp (hcyclic k hk_lt)
    exact (QuotientGroup.quotientBot (G := f (k + 1))).isCyclic.mp hcyc_quot

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: ambient centrality
restricts to subgroup centrality. -/
lemma center_subgroupOf_le_center_local (A : Subgroup G) :
    (Subgroup.center G).subgroupOf A ≤ Subgroup.center A := by
  intro x hx
  change x.1 ∈ Subgroup.center G at hx
  -- Centrality in `G` implies centrality against every element of `A`.
  rw [Subgroup.mem_center_iff] at hx ⊢
  intro y
  exact Subtype.ext (hx y.1)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: pulling back a cyclic
subgroup of `G ⧸ Z(G)` yields a commutative subgroup of `G`. -/
lemma isMulCommutative_comap_center_of_isCyclic_local
    (B : Subgroup (G ⧸ Subgroup.center G)) (hB : IsCyclic B) :
    IsMulCommutative (B.comap (QuotientGroup.mk' (Subgroup.center G))) := by
  let q : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
  let A : Subgroup G := B.comap q
  have hmap : A.map q = B :=
    Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (Subgroup.center G)) B
  have hcyc : IsCyclic (A.map q) := by
    rw [hmap]
    exact hB
  let φ : A →* A.map q := q.subgroupMap A
  have hker : φ.ker ≤ Subgroup.center A := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxq : q x = 1 := by
      change ((φ x : A.map q) : G ⧸ Subgroup.center G) = 1
      simpa using congrArg Subtype.val hx
    have hxcenter : (x : G) ∈ Subgroup.center G := by
      exact
        (QuotientGroup.eq_one_iff (N := Subgroup.center G) (x := (x : G))).mp hxq
    exact center_subgroupOf_le_center_local A hxcenter
  letI : IsCyclic (A.map q) := hcyc
  -- The quotient image is cyclic and the kernel is central, so the pullback is abelian.
  rw [show B.comap (QuotientGroup.mk' (Subgroup.center G)) = A by rfl, isMulCommutative_iff]
  intro a b
  exact commutative_of_cyclic_center_quotient φ hker a b

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the pullback of a
nontrivial subgroup of `G ⧸ Z(G)` is not contained in `Z(G)`. -/
lemma comap_center_not_le_center_of_nontrivial_local
    (B : Subgroup (G ⧸ Subgroup.center G)) (hB : B ≠ ⊥) :
    ¬ B.comap (QuotientGroup.mk' (Subgroup.center G)) ≤ Subgroup.center G := by
  let q : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
  intro hle
  have hmap : (B.comap q).map q = B :=
    Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (Subgroup.center G)) B
  have hbot : (B.comap q).map q ≤ ⊥ := by
    calc
      (B.comap q).map q ≤ (Subgroup.center G).map q := Subgroup.map_mono hle
      _ = ⊥ := QuotientGroup.map_mk'_self (Subgroup.center G)
  -- If the pullback lay in the center, its image in the quotient would be trivial.
  apply hB
  rw [← hmap]
  exact le_antisymm hbot bot_le

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a nonabelian finite
supersolvable group has a normal commutative subgroup not contained in its center. -/
theorem exists_normal_commutative_subgroup_not_le_center_of_nonabelian_supersolvable_local
    [IsSupersolvable G] (hnonabelian : ¬ IsMulCommutative G) :
    ∃ A : Subgroup G, A.Normal ∧ IsMulCommutative A ∧ ¬ A ≤ Subgroup.center G := by
  have hcenter_ne_top : Subgroup.center G ≠ ⊤ := by
    intro hcenter_top
    apply hnonabelian
    exact Subgroup.center_eq_top_iff.mp hcenter_top
  letI : Nontrivial (G ⧸ Subgroup.center G) := QuotientGroup.nontrivial_iff.mpr hcenter_ne_top
  letI : IsSupersolvable (G ⧸ Subgroup.center G) :=
    supersolvable_quotient_of_supersolvable (Subgroup.center G)
  -- Follow the source route on the quotient by the center, then pull back the cyclic subgroup.
  obtain ⟨B, hBnormal, hBne, hBcyc⟩ :=
    exists_nontrivial_normal_cyclic_subgroup_of_nontrivial_supersolvable_local
      (Q := G ⧸ Subgroup.center G)
  refine ⟨B.comap (QuotientGroup.mk' (Subgroup.center G)), ?_, ?_, ?_⟩
  · exact Subgroup.Normal.comap hBnormal (QuotientGroup.mk' (Subgroup.center G))
  · exact isMulCommutative_comap_center_of_isCyclic_local B hBcyc
  · exact comap_center_not_le_center_of_nontrivial_local B hBne


end

end Representation
