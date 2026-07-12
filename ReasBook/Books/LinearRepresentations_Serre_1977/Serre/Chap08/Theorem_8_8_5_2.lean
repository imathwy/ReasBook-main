import Mathlib
import LinearRepresentations_Serre_1977.Chap03.Exercise_3_3_3_6
import LinearRepresentations_Serre_1977.Chap08.Definition_8_8_3_2
import LinearRepresentations_Serre_1977.Chap08.Exercise_8_8_3_9
import LinearRepresentations_Serre_1977.Chap08.Lemma_8_8_5_1
import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_1_1
import LinearRepresentations_Serre_1977.Chap08.Remark_8_8_1_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace Representation

open CategoryTheory Rep

section

variable {G : Type} [Group G] [Finite G] [IsSupersolvable G]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- Helper for Theorem 8-8.5-2: quotienting by a normal subgroup that acts trivially preserves
irreducibility because the quotient representation has exactly the same invariant subspaces. -/
lemma isIrreducible_of_ofQuotient_of_isTrivial
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
  -- Any nonzero quotient-stable subspace is already a nonzero `ρ`-subrepresentation, hence it
  -- must be all of `V`.
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

/-- Helper for Theorem 8-8.5-2: the top subrepresentation witnesses that any degree-`1`
irreducible representation of a commutative group is already monomial. -/
lemma isInducedFromSubrepresentation_top
    (ρ : Representation ℂ G V) :
    ρ.IsInducedFromSubrepresentation
      (⊤ : Subgroup G)
      (⊤ : Subrepresentation (ρ.comp (⊤ : Subgroup G).subtype)) := by
  classical
  let _ : DecidableEq (G ⧸ (⊤ : Subgroup G)) := Classical.decEq _
  letI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  -- With only one left coset, the Chapter 3 inducedness criterion reduces to the single summand
  -- `⊤`, so the internal direct sum is immediate.
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

/-- Helper for Theorem 8-8.5-2: on a commutative finite group, an irreducible complex
representation is already a degree-`1` subgroup representation. -/
lemma isMonomial_of_irreducible_of_isMulCommutative
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hcomm : IsMulCommutative G) :
    ρ.IsMonomial := by
  letI : IsMulCommutative G := hcomm
  letI : FiniteDimensional ℂ V := Representation.IsIrreducible.finiteDimensional_of_finite ρ
  -- The source proof closes the abelian branch by Schur's lemma: the irreducible space is
  -- one-dimensional, so the trivial left-coset decomposition at `⊤` is the monomial witness.
  refine ⟨⊤, ⊤, ?_, isInducedFromSubrepresentation_top ρ⟩
  change Module.finrank ℂ (⊤ : Submodule ℂ V) = 1
  rw [finrank_top]
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ

/-- Helper for Theorem 8-8.5-2: if the restriction to a normal commutative subgroup were isotypic,
then every element of that subgroup would act by a scalar, hence centrally under a faithful
representation. -/
lemma not_restriction_isotypic_of_faithful_of_not_le_center
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A]
    (hfaithful : Function.Injective ρ)
    (hA : ¬ A ≤ Subgroup.center G) :
    ¬ (let ρA : Representation ℂ A V := ρ.comp A.subtype
       letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
       IsIsotypic (MonoidAlgebra ℂ A) V) := by
  intro hisotypic
  obtain ⟨χ, hχ⟩ :=
    (restriction_isotypic_iff_exists_character_of_commutative_subgroup
      (ρ := ρ) (A := A)).mp hisotypic
  apply hA
  intro a ha
  let aA : A := ⟨a, ha⟩
  rw [Subgroup.mem_center_iff]
  intro g
  -- Scalar action on `a` forces `ρ (g * a)` and `ρ (a * g)` to agree; faithfulness then lifts
  -- the equality of operators back to the group.
  apply hfaithful
  calc
    ρ (g * a) = ρ g * ρ aA := by
      simpa [aA] using ρ.map_mul g (aA : A)
    _ = ρ g * ((χ aA : ℂ) • 1) := by
      rw [hχ aA]
    _ = ((χ aA : ℂ) • 1) * ρ g := by
      ext v
      simp
    _ = ρ aA * ρ g := by
      rw [hχ aA]
    _ = ρ (a * g) := by
      simpa [aA] using (ρ.map_mul (aA : A) g).symm

/-- Helper for Theorem 8-8.5-2: a `K`-stable subrepresentation inside the `H`-subrepresentation
`W` can be viewed as a subrepresentation of the ambient representation restricted to
`K.map H.subtype`. -/
noncomputable def ambient_subrepresentation_of_subgroup_chain
    (ρ : Representation ℂ G V)
    (H : Subgroup G)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype)) :
    Subrepresentation (ρ.comp (K.map H.subtype).subtype) where
  toSubmodule := U.toSubmodule.map W.toSubmodule.subtype
  apply_mem_toSubmodule := by
    intro g x hx
    let e : K ≃* K.map H.subtype :=
      K.equivMapOfInjective H.subtype H.subtype_injective
    rcases hx with ⟨y, hy, rfl⟩
    -- Rewrite the ambient `K.map H.subtype`-action through the canonical preimage in `K`.
    refine ⟨W.toRepresentation (e.symm g) y, U.apply_mem_toSubmodule (e.symm g) hy, ?_⟩
    change (ρ (((e.symm g : K) : H) : G) (y : W.toSubmodule) : V) = ρ (g : G) (y : W.toSubmodule)
    have hg : (((e.symm g : K) : H) : G) = (g : G) := by
      simpa [e] using
        (Subgroup.coe_equivMapOfInjective_apply K H.subtype H.subtype_injective (e.symm g)).symm
    simpa [hg]

/-- Helper for Theorem 8-8.5-2: passing from `U` to its ambient image in `V` does not change the
underlying complex dimension. -/
theorem ambient_subrepresentation_of_subgroup_chain_finrank
    (ρ : Representation ℂ G V)
    (H : Subgroup G)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype)) :
    Module.finrank ℂ
        (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toSubmodule =
      Module.finrank ℂ U.toSubmodule := by
  -- The ambient witness is just the image of `U` under the injective inclusion `W ↪ V`.
  change Module.finrank ℂ (U.toSubmodule.map W.toSubmodule.subtype) =
      Module.finrank ℂ U.toSubmodule
  simpa using
    (Submodule.finrank_map_subtype_eq (p := W.toSubmodule) (q := U.toSubmodule) (R := ℂ))

/-- Helper for Theorem 8-8.5-2: the ambient witness is the image of `U` under the inclusion
`W ↪ V`, viewed as a linear equivalence onto its image. -/
noncomputable def ambient_subrepresentation_of_subgroup_chain_linearEquiv
    (ρ : Representation ℂ G V)
    (H : Subgroup G)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype)) :
    U.toSubmodule ≃ₗ[ℂ] (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toSubmodule :=
  Submodule.equivMapOfInjective
    W.toSubmodule.subtype
    W.toSubmodule.subtype_injective
    U.toSubmodule

/-- Helper for Theorem 8-8.5-2: the ambient-image linear equivalence intertwines the original
`K`-action with the transported `K.map H.subtype`-action. -/
theorem ambient_subrepresentation_of_subgroup_chain_linearEquiv_isIntertwining
    (ρ : Representation ℂ G V)
    (H : Subgroup G)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype)) :
    ∀ k,
      (ambient_subrepresentation_of_subgroup_chain_linearEquiv ρ H W K U).toLinearMap ∘ₗ
          U.toRepresentation k =
        (((ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation.comp
            (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom) k) ∘ₗ
          (ambient_subrepresentation_of_subgroup_chain_linearEquiv ρ H W K U).toLinearMap := by
  intro k
  -- The subgroup-chain witness was defined so that the ambient `K.map H.subtype`-action is
  -- literally the transported `K`-action through the inclusion `W ↪ V`.
  ext u
  rfl

/-- Helper for Theorem 8-8.5-2: the ambient subgroup-chain witness realizes the original
`K`-representation after transport along `K ≃ K.map H.subtype`. -/
noncomputable def ambient_subrepresentation_of_subgroup_chain_rep_equiv
    (ρ : Representation ℂ G V)
    (H : Subgroup G)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype)) :
    U.toRepresentation.Equiv
      ((ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation.comp
        (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom) :=
  Representation.Equiv.mk
    (ambient_subrepresentation_of_subgroup_chain_linearEquiv ρ H W K U)
    (ambient_subrepresentation_of_subgroup_chain_linearEquiv_isIntertwining ρ H W K U)

/-- Helper for Theorem 8-8.5-2: restricting the mapped subgroup `K.map H.subtype` back to `H`
recovers the original subgroup `K`. -/
lemma subgroup_chain_inner_subgroup_eq
    (H : Subgroup G)
    (K : Subgroup H) :
    ((K.map H.subtype).subgroupOf H : Subgroup H) = K := by
  ext k
  change k.1 ∈ K.map H.subtype ↔ k ∈ K
  constructor
  · intro hk
    rcases hk with ⟨x, hx, hxk⟩
    have : x = k := by
      apply Subtype.ext
      simpa using hxk
    simpa [this] using hx
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- Helper for Theorem 8-8.5-2: the subgroup obtained by mapping `K ≤ H` into `G` still lies in
`H`. -/
lemma subgroup_chain_map_le
    (H : Subgroup G)
    (K : Subgroup H) :
    K.map H.subtype ≤ H := by
  intro x hx
  rcases hx with ⟨y, -, rfl⟩
  exact y.property

/-- Helper for Theorem 8-8.5-2: the mapped subgroup inclusion composed with the canonical
equivalence `K ≃ K.map H.subtype` is the original composite inclusion `K ≤ H ≤ G`. -/
lemma subgroup_chain_map_subtype_comp_eq
    (H : Subgroup G)
    (K : Subgroup H) :
    (K.map H.subtype).subtype.comp
        (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom =
      H.subtype.comp K.subtype := by
  ext k
  -- Both compositions send `k` to the same element of `G`.
  simpa using
    (Subgroup.coe_equivMapOfInjective_apply K H.subtype H.subtype_injective k)

/-- Helper for Theorem 8-8.5-2: restricting a representation equivalence along a subgroup keeps
the same underlying linear equivalence. -/
private theorem comp_subtype_equiv_isIntertwining
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K) :
    ∀ s, e.toLinearEquiv ∘ₗ (ρ.comp S.subtype) s = (σ.comp S.subtype) s ∘ₗ e.toLinearEquiv := by
  intro s
  -- Restriction does not change the intertwining identity; it only narrows the source group.
  simpa using e.isIntertwining' (s : K)

/-- Helper for Theorem 8-8.5-2: restricting a representation equivalence along a subgroup keeps
the same underlying linear equivalence. -/
private noncomputable def comp_subtype_equiv
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K) :
    Representation.Equiv (ρ.comp S.subtype) (σ.comp S.subtype) :=
  Representation.Equiv.mk e.toLinearEquiv (comp_subtype_equiv_isIntertwining e S)

/-- Helper for Theorem 8-8.5-2: restricting the equivalence does not change its action on
vectors. -/
@[simp] private theorem comp_subtype_equiv_apply
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K) (x : W) :
    comp_subtype_equiv e S x = e x :=
  rfl

/-- Helper for Theorem 8-8.5-2: a subrepresentation transports across a representation
equivalence by mapping its carrier through the underlying linear equivalence. -/
private theorem transported_subrepresentation_of_equiv_stable
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    ∀ g ⦃x : W'⦄, x ∈ U.toSubmodule.map e.toLinearMap → σ g x ∈ U.toSubmodule.map e.toLinearMap := by
  intro g x hx
  rcases hx with ⟨y, hy, rfl⟩
  -- Mapping a stable subspace through an intertwining equivalence preserves stability.
  refine ⟨ρ g y, U.apply_mem_toSubmodule g hy, ?_⟩
  simp [e.isIntertwining]

/-- Helper for Theorem 8-8.5-2: a subrepresentation transports across a representation
equivalence by mapping its carrier through the underlying linear equivalence. -/
private noncomputable def transported_subrepresentation_of_equiv
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    Subrepresentation σ where
  toSubmodule := U.toSubmodule.map e.toLinearMap
  apply_mem_toSubmodule := transported_subrepresentation_of_equiv_stable e U

/-- Helper for Theorem 8-8.5-2: the transported subrepresentation has the expected mapped
carrier. -/
@[simp] private theorem transported_subrepresentation_of_equiv_toSubmodule
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    (transported_subrepresentation_of_equiv e U).toSubmodule = U.toSubmodule.map e.toLinearMap :=
  rfl

/-- Helper for Theorem 8-8.5-2: transporting the inducing subrepresentation along an ambient
equivalence transports each left-coset summand by the same linear equivalence. -/
private theorem leftQuotientSubmodule_eq_map_of_equiv
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype)) (q : K ⧸ S) :
    σ.leftQuotientSubmodule S
        (transported_subrepresentation_of_equiv (comp_subtype_equiv e S) U) q =
      (ρ.leftQuotientSubmodule S U q).map e.toLinearMap := by
  refine Quotient.inductionOn' q ?_
  intro g
  -- Both quotient summands are the image of `U` under the same composite operator.
  rw [Representation.leftQuotientSubmodule_mk, Representation.leftQuotientSubmodule_mk]
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨ρ g u, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    · simp [e.isIntertwining]
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨e u, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    · simp [e.isIntertwining]

/-- Helper for Theorem 8-8.5-2: inducedness data is preserved when the ambient representation is
replaced by an equivalent one. -/
private theorem isInducedFromSubrepresentation_of_equiv
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U) :
    σ.IsInducedFromSubrepresentation S
      (transported_subrepresentation_of_equiv (comp_subtype_equiv e S) U) := by
  classical
  let _ : DecidableEq (K ⧸ S) := Classical.decEq _
  let U' := transported_subrepresentation_of_equiv (comp_subtype_equiv e S) U
  have hinternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule S U) := by
    -- Unpack the Chapter 3 owner so the proof can work directly with the quotient-indexed family.
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  have hleft_fun :
      σ.leftQuotientSubmodule S U' = fun q ↦ (ρ.leftQuotientSubmodule S U q).map e.toLinearMap := by
    funext q
    simpa [U'] using leftQuotientSubmodule_eq_map_of_equiv e S U q
  have hindep : iSupIndep (σ.leftQuotientSubmodule S U') := by
    -- The internal direct-sum independence transports along the injective linear equivalence `e`.
    rw [hleft_fun]
    exact LinearMap.iSupIndep_map e.toLinearMap e.injective hinternal.submodule_iSupIndep
  have hspan : iSup (σ.leftQuotientSubmodule S U') = ⊤ := by
    -- Surjectivity of `e` carries the spanning statement for the old family to the new one.
    calc
      iSup (σ.leftQuotientSubmodule S U') =
          iSup (fun q ↦ (ρ.leftQuotientSubmodule S U q).map e.toLinearMap) := by
            rw [hleft_fun]
      _ = (iSup (ρ.leftQuotientSubmodule S U)).map e.toLinearMap := by
            rw [Submodule.map_iSup]
      _ = ⊤ := by
            rw [hinternal.submodule_iSup_eq_top, Submodule.map_top]
            exact LinearMap.range_eq_top.mpr e.surjective
  -- Package the transported independence and spanning statements back into the Chapter 3 owner.
  unfold Representation.IsInducedFromSubrepresentation
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep hspan

/-- Helper for Theorem 8-8.5-2: induction along a source-group equivalence is just quotienting by
the same coinvariant relations after reindexing the source action. -/
private noncomputable def ind_equiv_of_source_equiv
    {K L : Type} [Group K] [Group L]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (f : K →* L) {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) :
    (Representation.ind f ρ).Equiv (Representation.ind f σ) := by
  let inducedSourceHom :
      (Representation.ind f ρ).IntertwiningMap (Representation.ind f σ) :=
    { toLinearMap := Representation.Coinvariants.map _ _
        (e.toLinearMap.lTensor _)
        (by
          simp [LinearMap.lTensor_comp_map, e.toIntertwiningMap.2,
            LinearMap.map_comp_lTensor])
      isIntertwining' := by
        intro g
        ext h a
        simp }
  let inducedSourceInv :
      (Representation.ind f σ).IntertwiningMap (Representation.ind f ρ) :=
    { toLinearMap := Representation.Coinvariants.map _ _
        (e.symm.toLinearMap.lTensor _)
        (by
          intro g
          ext x y
          simpa using
            congrArg
              (fun z ↦ (Finsupp.single (f g * x) (1 : ℂ)) ⊗ₜ[ℂ] z)
              (LinearMap.congr_fun (e.symm.toIntertwiningMap.2 g) y))
      isIntertwining' := by
        intro g
        ext h a
        simp }
  have hinduced_inv_hom :
      inducedSourceInv.toLinearMap ∘ₗ inducedSourceHom.toLinearMap = LinearMap.id := by
    -- The induced maps act by `e` and `e.symm` on each standard generator.
    apply Representation.IndV.hom_ext
    intro h
    ext a
    simp [inducedSourceHom, inducedSourceInv]
  have hinduced_hom_inv :
      inducedSourceHom.toLinearMap ∘ₗ inducedSourceInv.toLinearMap = LinearMap.id := by
    -- The same generator computation gives the inverse identity in the other direction.
    apply Representation.IndV.hom_ext
    intro h
    ext a
    simp [inducedSourceHom, inducedSourceInv]
  exact Representation.Equiv.mk
    (LinearEquiv.ofLinear inducedSourceHom.toLinearMap inducedSourceInv.toLinearMap
      hinduced_hom_inv hinduced_inv_hom)
    inducedSourceHom.isIntertwining'

/-- Helper for Theorem 8-8.5-2: reindexing the source group by an equivalence does not change the
coinvariant relations used in induction. -/
private theorem ind_ker_comp_equiv_eq
    {K L M : Type} [Group K] [Group L] [Group M]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (e : K ≃* L) (f : L →* M) (ρ : Representation ℂ L W) :
    Representation.Coinvariants.ker
        (Representation.tprod ((leftRegular ℂ M).comp (f.comp e.toMonoidHom))
          (ρ.comp e.toMonoidHom)) =
      Representation.Coinvariants.ker
        (Representation.tprod ((leftRegular ℂ M).comp f) ρ) := by
  -- Reindexing the source group only renames the same family of relations.
  unfold Representation.Coinvariants.ker
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨⟨g, v⟩, rfl⟩
    exact Submodule.subset_span ⟨(e g, v), rfl⟩
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨⟨g, v⟩, rfl⟩
    exact Submodule.subset_span ⟨(e.symm g, v), by simp⟩

/-- Helper for Theorem 8-8.5-2: induction along a source-group equivalence is just quotienting by
the same coinvariant relations after reindexing the source action. -/
private noncomputable def ind_equiv_of_comp_equiv
    {K L M : Type} [Group K] [Group L] [Group M]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (e : K ≃* L) (f : L →* M) (ρ : Representation ℂ L W) :
    (Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)).Equiv
      (Representation.ind f ρ) := by
  refine Representation.Equiv.mk
      (Submodule.quotEquivOfEq _ _ (ind_ker_comp_equiv_eq e f ρ)) ?_
  intro m
  -- The quotient equivalence acts identically on induced generators, so the target action
  -- commutes with it on the standard basis `IndV.mk`.
  apply Representation.IndV.hom_ext
  intro m'
  ext v
  simp only [LinearMap.comp_apply]
  change (Submodule.quotEquivOfEq _ _ (ind_ker_comp_equiv_eq e f ρ))
      (((Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) m)
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) m') v)) =
    ((Representation.ind f ρ) m)
      ((Submodule.quotEquivOfEq _ _ (ind_ker_comp_equiv_eq e f ρ))
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) m') v))
  have hleft :
      ((Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) m)
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) m') v) =
      (Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (m' * m⁻¹)) v := by
    exact Representation.ind_mk (φ := f.comp e.toMonoidHom) (ρ := ρ.comp e.toMonoidHom) m m' v
  have hright :
      ((Representation.ind f ρ) m)
        ((Representation.IndV.mk f ρ m') v) =
      (Representation.IndV.mk f ρ (m' * m⁻¹)) v := by
    exact Representation.ind_mk (φ := f) (ρ := ρ) m m' v
  have hsource :
      (Submodule.quotEquivOfEq
          (Representation.Coinvariants.ker
            (Representation.tprod ((leftRegular ℂ M).comp (f.comp e.toMonoidHom))
              (ρ.comp e.toMonoidHom)))
          (Representation.Coinvariants.ker
            (Representation.tprod ((leftRegular ℂ M).comp f) ρ))
          (ind_ker_comp_equiv_eq e f ρ))
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) m') v) =
      (Representation.IndV.mk f ρ m') v := by
    exact Submodule.quotEquivOfEq_mk _ _ (ind_ker_comp_equiv_eq e f ρ) _
  have hsource' :
      (Submodule.quotEquivOfEq
          (Representation.Coinvariants.ker
            (Representation.tprod ((leftRegular ℂ M).comp (f.comp e.toMonoidHom))
              (ρ.comp e.toMonoidHom)))
          (Representation.Coinvariants.ker
            (Representation.tprod ((leftRegular ℂ M).comp f) ρ))
          (ind_ker_comp_equiv_eq e f ρ))
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (m' * m⁻¹)) v) =
      (Representation.IndV.mk f ρ (m' * m⁻¹)) v := by
    exact Submodule.quotEquivOfEq_mk _ _ (ind_ker_comp_equiv_eq e f ρ) _
  rw [hleft, hsource', hsource, hright]

/-- Helper for Theorem 8-8.5-2: projection from `Ind_S^G(σ)` back to the unit-coset copy of the
source representation `σ`. -/
private noncomputable def induced_identity_copy_projection
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) :
    Representation.IndV S.subtype σ →ₗ[ℂ] W :=
  Representation.Coinvariants.lift _
    (TensorProduct.lift <|
      Finsupp.lift _ _ _ fun g ↦
        @dite _ (g ∈ S) ((Classical.decPred fun x : K ↦ x ∈ S) g)
          (fun hg ↦ σ ⟨g, hg⟩⁻¹)
          (fun _ ↦ 0))
    (fun s ↦ by
      -- Check the coinvariant relation on generators `δ_g ⊗ w`.
      ext g w
      by_cases hg : g ∈ S
      · have hsg : ((s : K) * g) ∈ S := S.mul_mem s.property hg
        have hmul : σ ⟨(s : K) * g, hsg⟩⁻¹ (σ s w) = σ ⟨g, hg⟩⁻¹ w := by
          have hsub : ((⟨(s : K) * g, hsg⟩⁻¹ : S) * s) = ⟨g, hg⟩⁻¹ := by
            ext
            simp [mul_assoc]
          calc
            σ ⟨(s : K) * g, hsg⟩⁻¹ (σ s w)
              = σ (((⟨(s : K) * g, hsg⟩⁻¹ : S) * s)) w := by
                  simp [Module.End.mul_apply, map_mul]
            _ = σ ⟨g, hg⟩⁻¹ w := by
                  rw [hsub]
        simpa [TensorProduct.lift.tmul, hg, hsg] using hmul
      · have hsng : ((s : K) * g) ∉ S := by
          intro hmem
          have htmp : ((s : K)⁻¹ * ((s : K) * g)) ∈ S :=
            S.mul_mem (S.inv_mem s.property) hmem
          have hg' : g ∈ S := by
            simpa [mul_assoc] using htmp
          exact hg hg'
        simp [TensorProduct.lift.tmul, hg, hsng])

/-- Helper for Theorem 8-8.5-2: the projection recovers the original vector on the unit-coset
generator of `Ind_S^G(σ)`. -/
private theorem induced_identity_copy_projection_apply_mk_one
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) (w : W) :
    induced_identity_copy_projection S σ (Representation.IndV.mk S.subtype σ 1 w) = w := by
  classical
  have hone : (1 : K) ∈ S := S.one_mem
  have hbase : σ ⟨1, hone⟩⁻¹ w = w := by
    have hsub : ((⟨1, hone⟩ : S)⁻¹) = 1 := by
      ext
      simp
    rw [hsub]
    exact LinearMap.congr_fun σ.map_one w
  -- Evaluating the quotient lift at the unit basis vector reduces to the identity on `W`.
  simpa [induced_identity_copy_projection, TensorProduct.lift.tmul, hone] using hbase

/-- Helper for Theorem 8-8.5-2: the unit-coset generator is injective, so its range is a faithful
copy of the source representation `σ`. -/
private theorem induced_identity_copy_mk_one_injective
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) :
    Function.Injective (Representation.IndV.mk S.subtype σ 1) := by
  intro x y hxy
  have hproj := congrArg (induced_identity_copy_projection S σ) hxy
  calc
    x = induced_identity_copy_projection S σ (Representation.IndV.mk S.subtype σ 1 x) := by
          symm
          exact induced_identity_copy_projection_apply_mk_one S σ x
    _ = induced_identity_copy_projection S σ (Representation.IndV.mk S.subtype σ 1 y) := hproj
    _ = y := induced_identity_copy_projection_apply_mk_one S σ y

/-- Helper for Theorem 8-8.5-2: the range of the unit-coset generator is stable under the
restricted `S`-action on `Ind_S^G(σ)`. -/
private theorem induced_identity_copy_apply_mem
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) (s : S)
    {x : Representation.IndV S.subtype σ}
    (hx : x ∈ LinearMap.range (Representation.IndV.mk S.subtype σ 1)) :
    ((Rep.ind S.subtype (Rep.of σ)).ρ.comp S.subtype) s x ∈
      LinearMap.range (Representation.IndV.mk S.subtype σ 1) := by
  rcases hx with ⟨w, rfl⟩
  -- Acting on the unit-coset copy just applies `σ s` to the source vector.
  refine ⟨σ s w, ?_⟩
  simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]

/-- Helper for Theorem 8-8.5-2: the unit-coset copy of `σ` inside `Ind_S^G(σ)`. -/
private noncomputable def induced_identity_copy_subrepresentation
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) :
    Subrepresentation ((Rep.ind S.subtype (Rep.of σ)).ρ.comp S.subtype) :=
  { toSubmodule := LinearMap.range (Representation.IndV.mk S.subtype σ 1)
    apply_mem_toSubmodule := induced_identity_copy_apply_mem S σ }

/-- Helper for Theorem 8-8.5-2: the source representation `σ` is equivariantly equivalent to its
unit-coset copy inside `Ind_S^G(σ)`. -/
private noncomputable def induced_identity_copy_equiv
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) :
    σ.Equiv (induced_identity_copy_subrepresentation S σ).toRepresentation := by
  let e :
      W ≃ₗ[ℂ] (induced_identity_copy_subrepresentation S σ).toSubmodule :=
    LinearEquiv.ofInjective
      (Representation.IndV.mk S.subtype σ 1)
      (induced_identity_copy_mk_one_injective S σ)
  refine Representation.Equiv.mk e ?_
  intro s
  -- Both sides are the same vector in `Ind_S^G(σ)` after transporting along the unit-coset copy.
  ext w
  change Representation.IndV.mk S.subtype σ 1 (σ s w) =
    ((Rep.ind S.subtype (Rep.of σ)).ρ.comp S.subtype) s (Representation.IndV.mk S.subtype σ 1 w)
  simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]

/-- Helper for Theorem 8-8.5-2: every vector in the unit-coset copy is the unit-coset generator
attached to its preimage under the explicit equivalence with `σ`. -/
private theorem induced_identity_copy_eq_mk_one_symm
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W)
    (u : (induced_identity_copy_subrepresentation S σ).toSubmodule) :
    (u : Representation.IndV S.subtype σ) =
      Representation.IndV.mk S.subtype σ 1 ((induced_identity_copy_equiv S σ).symm u) := by
  -- The explicit copy equivalence is defined by the unit-coset embedding `IndV.mk ... 1`.
  have hmk (w : W) :
      (((induced_identity_copy_equiv S σ).toLinearEquiv w :
          (induced_identity_copy_subrepresentation S σ).toSubmodule) :
        Representation.IndV S.subtype σ) =
        Representation.IndV.mk S.subtype σ 1 w := by
    rfl
  have hEq :
      (induced_identity_copy_equiv S σ).toLinearEquiv
          ((induced_identity_copy_equiv S σ).symm u) = u := by
    exact (induced_identity_copy_equiv S σ).toLinearEquiv.apply_symm_apply u
  have hEq_coe :
      (u : Representation.IndV S.subtype σ) =
        ((((induced_identity_copy_equiv S σ).toLinearEquiv
              ((induced_identity_copy_equiv S σ).symm u)) :
            (induced_identity_copy_subrepresentation S σ).toSubmodule) :
          Representation.IndV S.subtype σ) := by
    simpa using
      congrArg
        (fun z : (induced_identity_copy_subrepresentation S σ).toSubmodule ↦
          (z : Representation.IndV S.subtype σ))
        hEq.symm
  calc
    (u : Representation.IndV S.subtype σ) =
        ((((induced_identity_copy_equiv S σ).toLinearEquiv
              ((induced_identity_copy_equiv S σ).symm u)) :
            (induced_identity_copy_subrepresentation S σ).toSubmodule) :
          Representation.IndV S.subtype σ) :=
      hEq_coe
    _ = Representation.IndV.mk S.subtype σ 1 ((induced_identity_copy_equiv S σ).symm u) :=
      hmk _

/-- Helper for Theorem 8-8.5-2: `Ind_S^G(σ)` is induced from its unit-coset copy. -/
private theorem induced_identity_copy_is_induced_local
    {K : Type} [Group K] [Finite K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) :
    ((Rep.ind S.subtype (Rep.of σ)).ρ).IsInducedFromSubrepresentation
      S (induced_identity_copy_subrepresentation S σ) := by
  classical
  let C : Rep ℂ K := Rep.coind S.subtype (Rep.of σ)
  let e :
      ((Rep.ind S.subtype (Rep.of σ)).ρ).Equiv C.ρ :=
    Representation.equivOfIso (Rep.indCoindIso (Rep.of σ))
  let W₀ :
      Subrepresentation (C.ρ.comp S.subtype) :=
    Representation.supportedOnSubgroupSubrepresentation S σ
  have hW₀ :
      C.ρ.IsInducedFromSubrepresentation S W₀ := by
    -- The imported coinduced model already carries the Chapter 3 inducing witness.
    simpa [C, W₀] using
      (Representation.isInducedFrom_supportedOnSubgroupSubrepresentation (H := S) (θ := σ))
  have htransport :
      transported_subrepresentation_of_equiv (comp_subtype_equiv e.symm S) W₀ =
        induced_identity_copy_subrepresentation S σ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      let fy : K → W := (y : C)
      have hySupportSubgroup :
          Function.support fy ⊆ (S : Set K) := by
        simpa [C, W₀] using
          (Representation.mem_supportedOnSubgroupSubrepresentation_iff S σ y).mp hy
      have hySupportOrbit :
          Function.support fy ⊆ MulAction.orbit S (1 : K) := by
        intro u hu
        refine ⟨⟨u, hySupportSubgroup hu⟩, ?_⟩
        simp
      have hyImage :
          e.symm y =
            Representation.IndV.mk S.subtype σ 1
              (fy 1) := by
        change (Rep.of σ).coindToInd y =
          Representation.IndV.mk S.subtype σ 1
            (fy 1)
        simpa using
          (Rep.coindToInd_of_support_subset_orbit (A := Rep.of σ) (g := (1 : K))
            y hySupportOrbit)
      exact LinearMap.mem_range.mpr
        ⟨fy 1, hyImage.symm⟩
    · intro hx
      rcases LinearMap.mem_range.mp hx with ⟨w, rfl⟩
      let fw : W₀.toSubmodule :=
        ⟨Representation.subgroupSupportedFunction S σ w,
          Representation.subgroupSupportedFunction_mem_supportedOnSubgroupSubrepresentation S σ w⟩
      let ffw : K → W := (((fw : W₀.toSubmodule) : C) : K → W)
      have hfwSupportSubgroup :
          Function.support ffw ⊆ (S : Set K) := by
        simpa [C, W₀] using
          (Representation.mem_supportedOnSubgroupSubrepresentation_iff S σ
            ((fw : W₀.toSubmodule) : C)).mp fw.property
      have hfwSupportOrbit :
          Function.support ffw ⊆ MulAction.orbit S (1 : K) := by
        intro u hu
        refine ⟨⟨u, hfwSupportSubgroup hu⟩, ?_⟩
        simp
      have hfwImage :
          e.symm fw = Representation.IndV.mk S.subtype σ 1 w := by
        have hcoind :
            e.symm fw =
              Representation.IndV.mk S.subtype σ 1
                (ffw 1) := by
          change (Rep.of σ).coindToInd ((fw : W₀.toSubmodule) : C) =
            Representation.IndV.mk S.subtype σ 1
              (ffw 1)
          simpa using
            (Rep.coindToInd_of_support_subset_orbit (A := Rep.of σ) (g := (1 : K))
              (((fw : W₀.toSubmodule) : C)) hfwSupportOrbit)
        have hEval :
            ffw 1 = w := by
          calc
            ffw 1 = σ ⟨1, S.one_mem⟩ w := by
              simpa [fw] using
                (Representation.subgroupSupportedFunction_of_mem
                  (H := S) (θ := σ) w S.one_mem)
            _ = w := by
              have hone : σ ⟨1, S.one_mem⟩ = 1 := by
                change σ 1 = 1
                simpa using σ.map_one
              rw [hone]
              rfl
        rw [hEval] at hcoind
        exact hcoind
      exact Submodule.mem_map.mpr ⟨fw, fw.property, hfwImage⟩
  -- Transport the coinduced witness back across the `Ind ≃ Coind` comparison.
  simpa [htransport] using
    isInducedFromSubrepresentation_of_equiv e.symm S W₀ hW₀

/-- Helper for Theorem 8-8.5-2: the canonical map from the standard induced model attached to a
stable subrepresentation into the ambient representation. -/
private noncomputable abbrev inducedFromSubrepresentationHomLocal
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype)) :
    Rep.ind S.subtype (Rep.of U.toRepresentation) ⟶ Rep.of ρ :=
  (Rep.indResHomEquiv S.subtype (Rep.of U.toRepresentation) (Rep.of ρ)).symm
    ((Rep.res S.subtype (Rep.of ρ)).subtype U.toSubmodule U.apply_mem_toSubmodule)

/-- Helper for Theorem 8-8.5-2: evaluating the canonical induced map on `⟦g ⊗ u⟧` recovers the
ambient action `ρ g⁻¹ u`. -/
@[simp] private theorem inducedFromSubrepresentationHomLocal_mk
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (g : K) (u : U.toSubmodule) :
    (inducedFromSubrepresentationHomLocal ρ S U).hom
        (Representation.IndV.mk S.subtype U.toRepresentation g u) =
      ρ g⁻¹ u := by
  simpa [inducedFromSubrepresentationHomLocal] using
    congrArg (ρ g⁻¹)
      (show ((Rep.res S.subtype (Rep.of ρ)).subtype U.toSubmodule
          U.apply_mem_toSubmodule).hom u = (u : W) from rfl)

/-- Helper for Theorem 8-8.5-2: each coset summand of an induced representation is canonically
identified with the source subrepresentation by translation. -/
@[simp] private theorem left_quotient_submodule_out_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (q : K ⧸ S) :
    ρ.leftQuotientSubmodule S U q = U.toSubmodule.map (ρ q.out) := by
  simpa using (ρ.leftQuotientSubmodule_mk S U q.out)

/-- Helper for Theorem 8-8.5-2: each coset summand of an induced representation is canonically
identified with the source subrepresentation by translation. -/
private noncomputable def left_quotient_submodule_equiv_local
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (q : K ⧸ S) :
    U.toSubmodule ≃ₗ[ℂ] ρ.leftQuotientSubmodule S U q :=
  let e : W ≃ₗ[ℂ] W := LinearEquiv.ofBijective (ρ q.out) (ρ.apply_bijective q.out)
  (e.submoduleMap U.toSubmodule).trans
    (LinearEquiv.ofEq _ _ (left_quotient_submodule_out_local ρ S U q).symm)

/-- Helper for Theorem 8-8.5-2: the local coset-translation equivalence acts by `ρ q.out` on
vectors of the source subrepresentation. -/
@[simp] private theorem left_quotient_submodule_equiv_local_apply
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (q : K ⧸ S) (u : U.toSubmodule) :
    ((left_quotient_submodule_equiv_local ρ S U q u :
        ρ.leftQuotientSubmodule S U q) : W) =
      ρ q.out u := by
  simp [left_quotient_submodule_equiv_local]

/-- Helper for Theorem 8-8.5-2: the inverse local coset-translation equivalence acts by
`ρ q.out⁻¹` on vectors in the `q`-summand. -/
@[simp] private theorem left_quotient_submodule_equiv_local_symm_apply
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (q : K ⧸ S) (x : ρ.leftQuotientSubmodule S U q) :
    (((left_quotient_submodule_equiv_local ρ S U q).symm x : U.toSubmodule) : W) =
      ρ q.out⁻¹ x := by
  let e : W ≃ₗ[ℂ] W := LinearEquiv.ofBijective (ρ q.out) (ρ.apply_bijective q.out)
  change (((e.submoduleMap U.toSubmodule).symm
      ((LinearEquiv.ofEq _ _ (left_quotient_submodule_out_local ρ S U q).symm).symm x) :
        U.toSubmodule) :
        W) = ρ q.out⁻¹ x
  apply (ρ.apply_bijective q.out).injective
  simp [e]

/-- Helper for Theorem 8-8.5-2: extend a map defined on the inducing subrepresentation to a
single quotient summand by transporting to the chosen coset representative. -/
private noncomputable def left_quotient_submodule_extension_local
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype))
    (q : K ⧸ S) :
    ρ.leftQuotientSubmodule S U q →ₗ[ℂ] W' :=
  (ρ' q.out).comp
    (f.toLinearMap.comp (left_quotient_submodule_equiv_local ρ S U q).symm.toLinearMap)

/-- Helper for Theorem 8-8.5-2: the internal direct-sum decomposition of the coset translates of
`U` yields a linear extension of an `S`-equivariant map on `U`. -/
private noncomputable def extensionLinearMapLocal
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype)) :
    W →ₗ[ℂ] W' :=
  let _ : DecidableEq (K ⧸ S) := Classical.decEq _
  let hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule S U) := by
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  let _ := DirectSum.IsInternal.chooseDecomposition (ρ.leftQuotientSubmodule S U) hInternal
  (DirectSum.toModule ℂ (K ⧸ S) W'
      (left_quotient_submodule_extension_local ρ S U ρ' f)).comp
    (DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule S U)).toLinearMap

/-- Helper for Theorem 8-8.5-2: on a single quotient summand, the local extension is the
corresponding component extension. -/
private theorem extensionLinearMapLocal_apply_of_mem
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype))
    {x : W} {q : K ⧸ S} (hx : x ∈ ρ.leftQuotientSubmodule S U q) :
    extensionLinearMapLocal ρ S U hU ρ' f x =
      left_quotient_submodule_extension_local ρ S U ρ' f q ⟨x, hx⟩ := by
  classical
  let _ : DecidableEq (K ⧸ S) := Classical.decEq _
  have hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule S U) := by
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  let _ := DirectSum.IsInternal.chooseDecomposition (ρ.leftQuotientSubmodule S U) hInternal
  have hxdecomp :
      DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule S U) x =
        DirectSum.lof ℂ (K ⧸ S) (fun i ↦ ρ.leftQuotientSubmodule S U i) q ⟨x, hx⟩ := by
    simpa using
      (DirectSum.decomposeLinearEquiv_apply_coe
        (R := ℂ) (ι := K ⧸ S) (ℳ := ρ.leftQuotientSubmodule S U) q ⟨x, hx⟩)
  rw [extensionLinearMapLocal]
  simpa [LinearMap.comp_apply, DirectSum.toModule_lof] using
    congrArg (DirectSum.toModule ℂ (K ⧸ S) W'
      (left_quotient_submodule_extension_local ρ S U ρ' f)) hxdecomp

/-- Helper for Theorem 8-8.5-2: the local extension agrees with the original intertwiner on the
inducing subrepresentation. -/
private theorem extensionLinearMapLocal_extends
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype))
    (u : U.toSubmodule) :
    extensionLinearMapLocal ρ S U hU ρ' f u = f u := by
  classical
  let q : K ⧸ S := QuotientGroup.mk 1
  have hq_rel : QuotientGroup.leftRel S q.out 1 := by
    exact Quotient.exact' (by simp [q])
  rw [QuotientGroup.leftRel_apply] at hq_rel
  have hq_mem : q.out ∈ S := by
    simpa using S.inv_mem hq_rel
  let h : S := ⟨q.out, hq_mem⟩
  let uinv : U.toSubmodule := ⟨ρ q.out⁻¹ u, U.apply_mem_toSubmodule h⁻¹ u.property⟩
  have huq : (u : W) ∈ ρ.leftQuotientSubmodule S U q := by
    rw [left_quotient_submodule_out_local ρ S U q]
    exact Submodule.mem_map.mpr ⟨uinv, uinv.property, by
      change ρ q.out (ρ q.out⁻¹ u) = u
      simp⟩
  have hsymm :
      (left_quotient_submodule_equiv_local ρ S U q).symm ⟨u, huq⟩ = uinv := by
    ext
    simp [uinv]
  rw [extensionLinearMapLocal_apply_of_mem ρ S U hU ρ' f huq]
  change ρ' q.out (f ((left_quotient_submodule_equiv_local ρ S U q).symm ⟨u, huq⟩)) = f u
  rw [hsymm]
  have huint : f uinv = ρ' q.out⁻¹ (f u) := by
    simpa [h, uinv] using
      (Representation.IntertwiningMap.isIntertwining (f := f) (g := h⁻¹) (v := u))
  rw [huint]
  simp

/-- Helper for Theorem 8-8.5-2: the local extension constructed from the internal sum is
`K`-equivariant. -/
private theorem extensionLinearMapLocal_isIntertwining
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype)) :
    ∀ s : K, ∀ x : W,
      extensionLinearMapLocal ρ S U hU ρ' f (ρ s x) =
        ρ' s (extensionLinearMapLocal ρ S U hU ρ' f x) := by
  classical
  let ℳ : K ⧸ S → Submodule ℂ W := ρ.leftQuotientSubmodule S U
  let _ : DecidableEq (K ⧸ S) := Classical.decEq _
  have hInternal : DirectSum.IsInternal ℳ := by
    simpa [ℳ, Representation.IsInducedFromSubrepresentation] using hU
  let _ := DirectSum.IsInternal.chooseDecomposition ℳ hInternal
  intro s x
  refine DirectSum.Decomposition.inductionOn (ℳ := ℳ)
      (motive := fun x : W ↦
        extensionLinearMapLocal ρ S U hU ρ' f (ρ s x) =
          ρ' s (extensionLinearMapLocal ρ S U hU ρ' f x))
      ?_ ?_ ?_ x
  · simp [extensionLinearMapLocal]
  · intro q x
    let u : U.toSubmodule := (left_quotient_submodule_equiv_local ρ S U q).symm x
    have hx : (x : W) = ρ q.out u := by
      calc
        (x : W) =
            ((left_quotient_submodule_equiv_local ρ S U q u :
                ρ.leftQuotientSubmodule S U q) : W) := by
              exact congrArg
                (fun y : ρ.leftQuotientSubmodule S U q ↦ (y : W))
                ((left_quotient_submodule_equiv_local ρ S U q).apply_symm_apply x).symm
        _ = ρ q.out u := by simp
    have hq : QuotientGroup.leftRel S ((s • q).out) (s * q.out) := by
      apply Quotient.exact'
      calc
        ((s • q).out : K ⧸ S) = s • q := Quotient.out_eq' (s • q)
        _ = s • (q.out : K ⧸ S) := by
          exact congrArg (fun z : K ⧸ S ↦ s • z) (Quotient.out_eq' q).symm
        _ = (s * q.out : K ⧸ S) := rfl
    rw [QuotientGroup.leftRel_apply] at hq
    let t : S := ⟨((s • q).out)⁻¹ * (s * q.out), hq⟩
    let ut : U.toSubmodule := ⟨ρ t u, U.apply_mem_toSubmodule t u.property⟩
    have hsx : (ρ s x : W) = ρ (s • q).out ut := by
      calc
        ρ s x = ρ s (ρ q.out u) := by rw [hx]
        _ = ρ (s * q.out) u := by
          simp [Module.End.mul_apply, map_mul]
        _ = ρ ((s • q).out * t) u := by
          congr 1
          simp [t]
        _ = ρ (s • q).out (ρ t u) := by
          simp [Module.End.mul_apply, map_mul]
        _ = ρ (s • q).out ut := rfl
    have hsx_mem : ρ s x ∈ ρ.leftQuotientSubmodule S U (s • q) := by
      rw [left_quotient_submodule_out_local ρ S U (s • q)]
      exact Submodule.mem_map.mpr ⟨ut, ut.property, hsx.symm⟩
    have hsymm_smul :
        (left_quotient_submodule_equiv_local ρ S U (s • q)).symm ⟨ρ s x, hsx_mem⟩ = ut := by
      ext
      simp [ut, hsx]
    calc
      extensionLinearMapLocal ρ S U hU ρ' f (ρ s x) =
          left_quotient_submodule_extension_local ρ S U ρ' f (s • q) ⟨ρ s x, hsx_mem⟩ := by
            exact extensionLinearMapLocal_apply_of_mem ρ S U hU ρ' f hsx_mem
      _ = ρ' (s • q).out (f ut) := by
            simp [left_quotient_submodule_extension_local, hsymm_smul, ut]
      _ = ρ' (s * q.out) (f u) := by
            have hut_def : ut = U.toRepresentation t u := by
              ext
              rfl
            have hut : f ut = ρ' t (f u) := by
              rw [hut_def]
              exact Representation.IntertwiningMap.isIntertwining (f := f) (g := t) (v := u)
            rw [hut]
            calc
              ρ' (s • q).out (ρ' t (f u)) = ρ' (((s • q).out : K) * t) (f u) := by
                simp [Module.End.mul_apply, map_mul]
              _ = ρ' (s * q.out) (f u) := by
                congr 1
                simp [t]
      _ = ρ' s (ρ' q.out (f u)) := by
            calc
              ρ' (s * q.out) (f u) = ((ρ' s * ρ' q.out)) (f u) := by
                exact LinearMap.congr_fun (ρ'.map_mul s q.out) (f u)
              _ = ρ' s (ρ' q.out (f u)) := by
                simp [Module.End.mul_apply]
      _ = ρ' s (extensionLinearMapLocal ρ S U hU ρ' f x) := by
            congr 1
            simpa [left_quotient_submodule_extension_local, u] using
              (extensionLinearMapLocal_apply_of_mem ρ S U hU ρ' f (x := x) (q := q) x.property).symm
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Theorem 8-8.5-2: bundle the local extension as a `K`-equivariant intertwiner. -/
private noncomputable abbrev extensionIntertwiningMapLocal
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype)) :
    ρ.IntertwiningMap ρ' :=
  (extensionLinearMapLocal ρ S U hU ρ' f).intertwiningMap_of_isIntertwiningMap
    ρ ρ' (extensionLinearMapLocal_isIntertwining ρ S U hU ρ' f)

/-- Helper for Theorem 8-8.5-2: a `K`-equivariant extension is determined by its values on the
inducing subrepresentation because the coset translates form an internal direct sum. -/
private theorem extensionIntertwiningMapLocal_unique
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype))
    (F : ρ.IntertwiningMap ρ') (hF : ∀ u : U.toSubmodule, F u = f u) :
    F = extensionIntertwiningMapLocal ρ S U hU ρ' f := by
  classical
  apply IntertwiningMap.ext
  ext v
  let ℳ : K ⧸ S → Submodule ℂ W := ρ.leftQuotientSubmodule S U
  let _ : DecidableEq (K ⧸ S) := Classical.decEq _
  have hInternal : DirectSum.IsInternal ℳ := by
    simpa [ℳ, Representation.IsInducedFromSubrepresentation] using hU
  let _ := DirectSum.IsInternal.chooseDecomposition ℳ hInternal
  refine DirectSum.Decomposition.inductionOn (ℳ := ℳ)
      (motive := fun x : W ↦ F x = extensionIntertwiningMapLocal ρ S U hU ρ' f x)
      ?_ ?_ ?_ v
  · simp [extensionIntertwiningMapLocal, extensionLinearMapLocal]
  · intro q x
    let u : U.toSubmodule := (left_quotient_submodule_equiv_local ρ S U q).symm x
    have hx : (x : W) = ρ q.out u := by
      calc
        (x : W) =
            ((left_quotient_submodule_equiv_local ρ S U q u :
                ρ.leftQuotientSubmodule S U q) : W) := by
              exact congrArg
                (fun y : ρ.leftQuotientSubmodule S U q ↦ (y : W))
                ((left_quotient_submodule_equiv_local ρ S U q).apply_symm_apply x).symm
        _ = ρ q.out u := by simp
    calc
      F x = F (ρ q.out u) := by rw [hx]
      _ = ρ' q.out (F u) := by
            simpa using
              (Representation.IntertwiningMap.isIntertwining (f := F) (g := q.out) (v := u))
      _ = ρ' q.out (f u) := by rw [hF u]
      _ = left_quotient_submodule_extension_local ρ S U ρ' f q x := by
            simp [left_quotient_submodule_extension_local, u]
      _ = extensionIntertwiningMapLocal ρ S U hU ρ' f x := by
            symm
            simpa [extensionIntertwiningMapLocal] using
              extensionLinearMapLocal_apply_of_mem ρ S U hU ρ' f (x := x) (q := q) x.property
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Theorem 8-8.5-2: every `S`-equivariant map out of the inducing subrepresentation
extends uniquely to the ambient representation. -/
private theorem existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (ρ' : Representation ℂ K W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp S.subtype)) :
    ∃! F : ρ.IntertwiningMap ρ', ∀ u : U.toSubmodule, F u = f u := by
  refine ⟨extensionIntertwiningMapLocal ρ S U hU ρ' f, ?_, ?_⟩
  · intro u
    exact extensionLinearMapLocal_extends ρ S U hU ρ' f u
  · intro F hF
    exact extensionIntertwiningMapLocal_unique ρ S U hU ρ' f F hF

/-- Helper for Theorem 8-8.5-2: the tautological inclusion of a stable subrepresentation is an
intertwiner for the restricted action. -/
private def subrepresentation_inclusion_hom
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype)) :
    U.toRepresentation.IntertwiningMap (ρ.comp S.subtype) :=
  U.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap
    U.toRepresentation (ρ.comp S.subtype) fun s u ↦ rfl

/-- Helper for Theorem 8-8.5-2: the unit-coset embedding is an intertwiner from the source
representation into the restricted induced representation. -/
private noncomputable def induced_identity_copy_hom
    {K : Type} [Group K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup K) (σ : Representation ℂ S W) :
    σ.IntertwiningMap (((Rep.ind S.subtype (Rep.of σ)).ρ).comp S.subtype) :=
  (Representation.IndV.mk S.subtype σ 1).intertwiningMap_of_isIntertwiningMap
    σ (((Rep.ind S.subtype (Rep.of σ)).ρ).comp S.subtype) fun s w ↦ by
      -- The unit-coset generator transforms exactly by the source action.
      change Representation.IndV.mk S.subtype σ 1 (σ s w) =
        ((Rep.ind S.subtype (Rep.of σ)).ρ.comp S.subtype) s
          (Representation.IndV.mk S.subtype σ 1 w)
      simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]

/-- Helper for Theorem 8-8.5-2: a Chapter 3 inducedness witness identifies the representation
with the standard induced model built from the witnessing subrepresentation. -/
private noncomputable def equiv_induced_of_isInducedFromSubrepresentation
    {K : Type} [Group K] [Finite K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U) :
    ρ.Equiv ((Rep.ind S.subtype (Rep.of U.toRepresentation)).ρ) := by
  let σind : Representation ℂ K (Representation.IndV S.subtype U.toRepresentation) :=
    (Rep.ind S.subtype (Rep.of U.toRepresentation)).ρ
  let φ : σind.IntertwiningMap ρ := (inducedFromSubrepresentationHomLocal ρ S U).hom
  let iotaρ : U.toRepresentation.IntertwiningMap (ρ.comp S.subtype) :=
    subrepresentation_inclusion_hom ρ S U
  let iotaind : U.toRepresentation.IntertwiningMap (σind.comp S.subtype) :=
    induced_identity_copy_hom S U.toRepresentation
  classical
  let hψexists :=
    (existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation ρ S U hU σind iotaind).exists
  let ψ : ρ.IntertwiningMap σind := Classical.choose hψexists
  have hψ : ∀ u : U.toSubmodule, ψ u = iotaind u := Classical.choose_spec hψexists
  have hright :
      φ.comp ψ = (1 : ρ.IntertwiningMap ρ) := by
    apply (existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation
      ρ S U hU ρ iotaρ).unique
    · intro u
      calc
        (φ.comp ψ) u = φ (ψ u) := rfl
        _ = φ (iotaind u) := by rw [hψ u]
        _ = ρ 1⁻¹ u := by
              simpa [φ, iotaind, induced_identity_copy_hom] using
                inducedFromSubrepresentationHomLocal_mk ρ S U 1 u
        _ = u := by simp
    · intro u
      rfl
  let Uind : Subrepresentation (σind.comp S.subtype) :=
    induced_identity_copy_subrepresentation S U.toRepresentation
  let iotaUind : Uind.toRepresentation.IntertwiningMap (σind.comp S.subtype) :=
    subrepresentation_inclusion_hom σind S Uind
  have hUinduced : σind.IsInducedFromSubrepresentation S Uind :=
    induced_identity_copy_is_induced_local S U.toRepresentation
  have hleft :
      ψ.comp φ = (1 : σind.IntertwiningMap σind) := by
    apply (existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation
      σind S Uind hUinduced σind iotaUind).unique
    · intro u
      calc
        (ψ.comp φ) u = ψ (φ u) := rfl
        _ = ψ (ρ 1⁻¹ ((induced_identity_copy_equiv S U.toRepresentation).symm u)) := by
              rw [induced_identity_copy_eq_mk_one_symm S U.toRepresentation u]
              congr 1
              simpa [φ] using
                inducedFromSubrepresentationHomLocal_mk ρ S U 1
                  ((induced_identity_copy_equiv S U.toRepresentation).symm u)
        _ = ψ ((induced_identity_copy_equiv S U.toRepresentation).symm u) := by simp
        _ = iotaind ((induced_identity_copy_equiv S U.toRepresentation).symm u) := by
              rw [hψ ((induced_identity_copy_equiv S U.toRepresentation).symm u)]
        _ = u := by
              change Representation.IndV.mk S.subtype U.toRepresentation 1
                    ((induced_identity_copy_equiv S U.toRepresentation).symm u) = u
              simpa using (induced_identity_copy_eq_mk_one_symm S U.toRepresentation u).symm
    · intro u
      rfl
  have hleft_linear : ψ.toLinearMap ∘ₗ φ.toLinearMap = LinearMap.id := by
    simpa using congrArg IntertwiningMap.toLinearMap hleft
  have hright_linear : φ.toLinearMap ∘ₗ ψ.toLinearMap = LinearMap.id := by
    simpa using congrArg IntertwiningMap.toLinearMap hright
  exact Representation.Equiv.mk
    (LinearEquiv.ofLinear ψ.toLinearMap φ.toLinearMap hleft_linear hright_linear)
    ψ.isIntertwining'

/-- Helper for Theorem 8-8.5-2: induction in stages for a subgroup chain is equivalent to direct
induction from the composite inclusion. -/
private noncomputable def ind_subgroup_chain_equiv
    {K : Type} [Group K]
    (S : Subgroup K) (L : Subgroup S)
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ L W) :
    ((Rep.ind S.subtype (Rep.ind L.subtype (Rep.of ρ))).ρ).Equiv
      ((Rep.ind (S.subtype.comp L.subtype) (Rep.of ρ)).ρ) :=
  Representation.equivOfIso
    ((((indResAdjunction ℂ L.subtype).leftAdjointCompIso
          (indResAdjunction ℂ S.subtype)
          (indResAdjunction ℂ (S.subtype.comp L.subtype))
          (eqToIso rfl)).app (Rep.of ρ)))

/-- Helper for Theorem 8-8.5-2: transporting the subgroup-chain source action to
`K.map H.subtype` turns composite induction into induction from the mapped subgroup. -/
private noncomputable def ind_subgroup_chain_map_equiv
    (ρ : Representation ℂ G V)
    (H : Subgroup G)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype)) :
    ((Rep.ind (H.subtype.comp K.subtype) (Rep.of U.toRepresentation)).ρ).Equiv
      ((Rep.ind (K.map H.subtype).subtype
        (Rep.of (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation)).ρ) := by
  let eK : K ≃* K.map H.subtype :=
    K.equivMapOfInjective H.subtype H.subtype_injective
  let eU :
      U.toRepresentation.Equiv
        ((ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation.comp
          eK.toMonoidHom) :=
    ambient_subrepresentation_of_subgroup_chain_rep_equiv ρ H W K U
  let e₁ :
      ((Rep.ind (H.subtype.comp K.subtype) (Rep.of U.toRepresentation)).ρ).Equiv
        ((Rep.ind (H.subtype.comp K.subtype)
          (Rep.of
            ((ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation.comp
              eK.toMonoidHom))).ρ) :=
    ind_equiv_of_source_equiv (H.subtype.comp K.subtype) eU
  let e₂ :
      ((Rep.ind ((K.map H.subtype).subtype.comp eK.toMonoidHom)
        (Rep.of
          ((ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation.comp
            eK.toMonoidHom))).ρ).Equiv
        ((Rep.ind (K.map H.subtype).subtype
          (Rep.of (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation)).ρ) :=
    by
      simpa using
        (ind_equiv_of_comp_equiv eK
          (K.map H.subtype).subtype
          (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation)
  -- The mapped-subgroup model is just the composite-inclusion model after reindexing the source.
  exact e₁.trans (by
    simpa [subgroup_chain_map_subtype_comp_eq H K] using e₂)

/-- Helper for Theorem 8-8.5-2: induction along a source equivalence sends each standard induced
generator to the matching generator with the source vector transported by the inverse equivalence.
-/
private theorem ind_equiv_of_source_equiv_symm_mk
    {K L : Type} [Group K] [Group L]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (f : K →* L) {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (g : L) (x : W') :
    (ind_equiv_of_source_equiv f e).symm (Representation.IndV.mk f σ g x) =
      Representation.IndV.mk f ρ g (e.symm x) := by
  -- The inverse induced equivalence applies `e.symm` to the source factor of each generator.
  simp [ind_equiv_of_source_equiv]

/-- Helper for Theorem 8-8.5-2: the inverse of the standard-model equivalence recovers the source
vector on the unit-coset generator. -/
@[simp] private theorem equiv_induced_of_isInducedFromSubrepresentation_symm_mk_one
    {K : Type} [Group K] [Finite K]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype))
    (hU : ρ.IsInducedFromSubrepresentation S U)
    (u : U.toSubmodule) :
    (equiv_induced_of_isInducedFromSubrepresentation ρ S U hU).symm
        (Representation.IndV.mk S.subtype U.toRepresentation 1 u) =
      u := by
  -- The inverse linear map of `equiv_induced_of_isInducedFromSubrepresentation` is the canonical
  -- induced-to-ambient map `φ`, so evaluation at the unit generator is exactly the defining formula
  -- for `inducedFromSubrepresentationHomLocal`.
  change (inducedFromSubrepresentationHomLocal ρ S U).hom
      (Representation.IndV.mk S.subtype U.toRepresentation 1 u) = u
  simpa using inducedFromSubrepresentationHomLocal_mk ρ S U 1 u

/-- Helper for Theorem 8-8.5-2: transporting a restricted subrepresentation across an ambient
equivalence preserves the carrier dimension. -/
private theorem transported_subrepresentation_finrank_eq
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ)
    (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype)) :
    Module.finrank ℂ
        (transported_subrepresentation_of_equiv (comp_subtype_equiv e S) U).toSubmodule =
      Module.finrank ℂ U.toSubmodule := by
  have hUmap :
      (transported_subrepresentation_of_equiv (comp_subtype_equiv e S) U).toSubmodule =
        U.toSubmodule.map (comp_subtype_equiv e S).toLinearMap := by
    simpa using transported_subrepresentation_of_equiv_toSubmodule
      (comp_subtype_equiv e S) U
  let eU :
      U.toSubmodule ≃ₗ[ℂ]
        U.toSubmodule.map (comp_subtype_equiv e S).toLinearMap :=
    Submodule.equivMapOfInjective
      (comp_subtype_equiv e S).toLinearMap
      (comp_subtype_equiv e S).injective
      U.toSubmodule
  -- The transported carrier is the image of `U` under the restricted linear equivalence.
  calc
    Module.finrank ℂ
        (transported_subrepresentation_of_equiv (comp_subtype_equiv e S) U).toSubmodule =
          Module.finrank ℂ
            (U.toSubmodule.map (comp_subtype_equiv e S).toLinearMap) := by
          rw [hUmap]
    _ = Module.finrank ℂ U.toSubmodule := by
          exact eU.symm.finrank_eq

/-- Helper for Theorem 8-8.5-2: induction in stages yields an upstairs witness with the same
carrier dimension as the downstairs monomial witness. -/
lemma exists_induced_subgroup_chain_witness
    (ρ : Representation ℂ G V)
    (H : Subgroup G)
    (W : Subrepresentation (ρ.comp H.subtype))
    (K : Subgroup H)
    (U : Subrepresentation (W.toRepresentation.comp K.subtype))
    (hinduced : ρ.IsInducedFromSubrepresentation H W)
    (hUinduced : W.toRepresentation.IsInducedFromSubrepresentation K U) :
    ∃ U' : Subrepresentation (ρ.comp (K.map H.subtype).subtype),
      Module.finrank ℂ U'.toSubmodule = Module.finrank ℂ U.toSubmodule ∧
        ρ.IsInducedFromSubrepresentation (K.map H.subtype) U' := by
  let eW :
      W.toRepresentation.Equiv
        ((Rep.ind K.subtype (Rep.of U.toRepresentation)).ρ) :=
    equiv_induced_of_isInducedFromSubrepresentation W.toRepresentation K U hUinduced
  let eρ :
      ρ.Equiv
        ((Rep.ind H.subtype (Rep.of W.toRepresentation)).ρ) :=
    equiv_induced_of_isInducedFromSubrepresentation ρ H W hinduced
  let eindW :
      ((Rep.ind H.subtype (Rep.of W.toRepresentation)).ρ).Equiv
        ((Rep.ind H.subtype
          (Rep.of ((Rep.ind K.subtype (Rep.of U.toRepresentation)).ρ))).ρ) :=
    ind_equiv_of_source_equiv H.subtype eW
  let echain :
      ((Rep.ind H.subtype
        (Rep.of ((Rep.ind K.subtype (Rep.of U.toRepresentation)).ρ))).ρ).Equiv
        ((Rep.ind (H.subtype.comp K.subtype) (Rep.of U.toRepresentation)).ρ) :=
    ind_subgroup_chain_equiv H K U.toRepresentation
  let emap :
      ((Rep.ind (H.subtype.comp K.subtype) (Rep.of U.toRepresentation)).ρ).Equiv
        ((Rep.ind (K.map H.subtype).subtype
          (Rep.of (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation)).ρ) :=
    ind_subgroup_chain_map_equiv ρ H W K U
  let e :
      ρ.Equiv
        ((Rep.ind (K.map H.subtype).subtype
          (Rep.of (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation)).ρ) :=
    eρ.trans (eindW.trans (echain.trans emap))
  let Ustd :
      Subrepresentation
        ((((Rep.ind (K.map H.subtype).subtype
            (Rep.of (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation)).ρ).comp
            (K.map H.subtype).subtype)) :=
    induced_identity_copy_subrepresentation
      (K.map H.subtype)
      (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation
  have hstd :
      ((Rep.ind (K.map H.subtype).subtype
        (Rep.of (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation)).ρ).IsInducedFromSubrepresentation
          (K.map H.subtype) Ustd := by
    simpa [Ustd] using
      induced_identity_copy_is_induced_local
        (K.map H.subtype)
        (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation
  let Uambient : Subrepresentation (ρ.comp (K.map H.subtype).subtype) :=
    transported_subrepresentation_of_equiv
      (comp_subtype_equiv e.symm (K.map H.subtype)) Ustd
  have hUstd_dim :
      Module.finrank ℂ Ustd.toSubmodule = Module.finrank ℂ U.toSubmodule := by
    -- The standard unit-coset copy is equivalent to the ambient-image witness, which in turn has
    -- the same carrier dimension as the original `K`-stable subrepresentation `U`.
    calc
      Module.finrank ℂ Ustd.toSubmodule =
          Module.finrank ℂ
            (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toSubmodule := by
              exact
                (induced_identity_copy_equiv
                  (K.map H.subtype)
                  (ambient_subrepresentation_of_subgroup_chain ρ H W K U).toRepresentation).symm.toLinearEquiv.finrank_eq
      _ = Module.finrank ℂ U.toSubmodule := by
            simpa using ambient_subrepresentation_of_subgroup_chain_finrank ρ H W K U
  have hUambient_dim :
      Module.finrank ℂ Uambient.toSubmodule = Module.finrank ℂ U.toSubmodule := by
    -- Transport along the restricted equivalence preserves dimension, so `Uambient` inherits the
    -- same degree as the standard unit-coset copy.
    calc
      Module.finrank ℂ Uambient.toSubmodule = Module.finrank ℂ Ustd.toSubmodule := by
        simpa [Uambient] using
          transported_subrepresentation_finrank_eq e.symm (K.map H.subtype) Ustd
      _ = Module.finrank ℂ U.toSubmodule := hUstd_dim
  have hUambient_induced :
      ρ.IsInducedFromSubrepresentation (K.map H.subtype) Uambient := by
    -- The inducing family transports across the ambient equivalence `e.symm`.
    simpa [Uambient] using
      isInducedFromSubrepresentation_of_equiv e.symm (K.map H.subtype) Ustd hstd
  -- Route correction: use the transported unit-coset copy itself as the upstairs witness, rather
  -- than identifying it with the concrete ambient image of `U` inside `V`.
  exact ⟨Uambient, hUambient_dim, hUambient_induced⟩

/-- Helper for Theorem 8-8.5-2: induction in stages should convert a monomial witness for an
irreducible `H`-subrepresentation into a monomial witness for the ambient representation. -/
lemma isMonomial_of_induced_from_monomial_subrepresentation
    (ρ : Representation ℂ G V)
    (H : Subgroup G)
    (W : Subrepresentation (ρ.comp H.subtype))
    (hinduced : ρ.IsInducedFromSubrepresentation H W)
    (hmonomial : W.toRepresentation.IsMonomial) :
    ρ.IsMonomial := by
  rcases hmonomial with ⟨K, U, hUdim, hUinduced⟩
  rcases
      exists_induced_subgroup_chain_witness ρ H W K U hinduced hUinduced with
    ⟨U', hU'dim, hU'induced⟩
  refine ⟨K.map H.subtype, U', ?_, hU'induced⟩
  -- The transported subgroup-chain witness keeps the original one-dimensional carrier.
  calc
    Module.finrank ℂ U'.toSubmodule = Module.finrank ℂ U.toSubmodule := hU'dim
    _ = 1 := hUdim

/-- Helper for Theorem 8-8.5-2: a subrepresentation downstairs on `H ≤ G ⧸ N` can be read as the
same underlying submodule for the pulled-back representation on `H.comap (QuotientGroup.mk' N)`.
-/
theorem quotient_comap_subgroup_map_mem
    {N : Subgroup G} [N.Normal]
    (H : Subgroup (G ⧸ N)) :
    ∀ y : H.comap (QuotientGroup.mk' N),
      ((QuotientGroup.mk' N).comp (H.comap (QuotientGroup.mk' N)).subtype) y ∈ H := by
  intro y
  exact y.2

/-- Helper for Theorem 8-8.5-2: the quotient map restricts to a canonical homomorphism from the
pulled-back subgroup `H.comap (QuotientGroup.mk' N)` into `H`. -/
noncomputable def quotient_comap_subgroup_map
    {N : Subgroup G} [N.Normal]
    (H : Subgroup (G ⧸ N)) :
    H.comap (QuotientGroup.mk' N) →* H :=
  (((QuotientGroup.mk' N).comp (H.comap (QuotientGroup.mk' N)).subtype).codRestrict H
    (quotient_comap_subgroup_map_mem H))

/-- Helper for Theorem 8-8.5-2: a subrepresentation downstairs on `H ≤ G ⧸ N` can be read as the
same underlying submodule for the pulled-back representation on `H.comap (QuotientGroup.mk' N)`.
-/
noncomputable def quotient_comap_subrepresentation
    {N : Subgroup G} [N.Normal]
    (σ : Representation ℂ (G ⧸ N) V)
    (H : Subgroup (G ⧸ N))
    (W : Subrepresentation (σ.comp H.subtype)) :
    Subrepresentation
      ((σ.comp (QuotientGroup.mk' N)).comp (H.comap (QuotientGroup.mk' N)).subtype) where
  toSubmodule := W.toSubmodule
  apply_mem_toSubmodule := by
    intro g x hx
    let πH : H.comap (QuotientGroup.mk' N) →* H := quotient_comap_subgroup_map H
    -- The pulled-back action factors through the codomain element `πH g : H`.
    simpa [πH] using W.apply_mem_toSubmodule (πH g) hx

/-- Helper for Theorem 8-8.5-2: pulling the subgroup witness back along the quotient map keeps
the underlying one-dimensional vector space unchanged. -/
@[simp] theorem quotient_comap_subrepresentation_finrank
    {N : Subgroup G} [N.Normal]
    (σ : Representation ℂ (G ⧸ N) V)
    (H : Subgroup (G ⧸ N))
    (W : Subrepresentation (σ.comp H.subtype)) :
    Module.finrank ℂ (quotient_comap_subrepresentation σ H W).toSubmodule =
      Module.finrank ℂ W.toSubmodule :=
  rfl

/-- Helper for Theorem 8-8.5-2: quotient pullback leaves the underlying subspace unchanged, so
the identity map is the relevant linear equivalence. -/
noncomputable def quotient_comap_subrepresentation_linearEquiv
    {N : Subgroup G} [N.Normal]
    (σ : Representation ℂ (G ⧸ N) V)
    (H : Subgroup (G ⧸ N))
    (W : Subrepresentation (σ.comp H.subtype)) :
    W.toSubmodule ≃ₗ[ℂ] (quotient_comap_subrepresentation σ H W).toSubmodule :=
  LinearEquiv.refl ℂ W.toSubmodule

/-- Helper for Theorem 8-8.5-2: the quotient pullback simply transports the `H`-action along the
canonical map `H.comap (QuotientGroup.mk' N) → H`. -/
theorem quotient_comap_subrepresentation_linearEquiv_isIntertwining
    {N : Subgroup G} [N.Normal]
    (σ : Representation ℂ (G ⧸ N) V)
    (H : Subgroup (G ⧸ N))
    (W : Subrepresentation (σ.comp H.subtype)) :
    ∀ g,
      (quotient_comap_subrepresentation_linearEquiv σ H W).toLinearMap ∘ₗ
          (W.toRepresentation.comp (quotient_comap_subgroup_map H)) g =
        (quotient_comap_subrepresentation σ H W).toRepresentation g ∘ₗ
          (quotient_comap_subrepresentation_linearEquiv σ H W).toLinearMap := by
  intro g
  -- Here the pullback representation is defined on the same carrier, so the intertwining check is
  -- definitional after rewriting through `quotient_comap_subgroup_map H`.
  rfl

/-- Helper for Theorem 8-8.5-2: the quotient pullback witness is the original `H`-representation
transported along `H.comap (QuotientGroup.mk' N) → H`. -/
noncomputable def quotient_comap_subrepresentation_rep_equiv
    {N : Subgroup G} [N.Normal]
    (σ : Representation ℂ (G ⧸ N) V)
    (H : Subgroup (G ⧸ N))
    (W : Subrepresentation (σ.comp H.subtype)) :
    Representation.Equiv
      (W.toRepresentation.comp (quotient_comap_subgroup_map H))
      (quotient_comap_subrepresentation σ H W).toRepresentation :=
  Representation.Equiv.mk
    (quotient_comap_subrepresentation_linearEquiv σ H W)
    (quotient_comap_subrepresentation_linearEquiv_isIntertwining σ H W)

/-- Helper for Theorem 8-8.5-2: the quotient map `G → G ⧸ N` identifies the left cosets of
`H.comap (QuotientGroup.mk' N)` in `G` with the left cosets of `H` in `G ⧸ N`. -/
noncomputable def quotient_comap_leftCosetEquiv
    {N : Subgroup G} [N.Normal]
    (H : Subgroup (G ⧸ N)) :
    G ⧸ H.comap (QuotientGroup.mk' N) ≃ (G ⧸ N) ⧸ H := by
  classical
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let s : G ⧸ N → G := fun x ↦ Classical.choose (QuotientGroup.mk'_surjective N x)
  have hs : ∀ x : G ⧸ N, q (s x) = x := fun x ↦
    Classical.choose_spec (QuotientGroup.mk'_surjective N x)
  refine
    { toFun := Quotient.lift (fun g : G ↦ ((g : G ⧸ N) : (G ⧸ N) ⧸ H)) ?_
      invFun := Quotient.lift (fun x : G ⧸ N ↦ ((s x : G) : G ⧸ H.comap q)) ?_
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
    change ((q (s y) : G ⧸ N) : (G ⧸ N) ⧸ H) = (y : (G ⧸ N) ⧸ H)
    simp [q, hs]

/-- Helper for Theorem 8-8.5-2: after reindexing the cosets by the quotient map, the upstairs
left-quotient summands are literally the downstairs summands. -/
theorem leftQuotientSubmodule_quotient_comap_eq
    {N : Subgroup G} [N.Normal]
    (σ : Representation ℂ (G ⧸ N) V)
    (H : Subgroup (G ⧸ N))
    (W : Subrepresentation (σ.comp H.subtype))
    (q : G ⧸ H.comap (QuotientGroup.mk' N)) :
    ((show Representation ℂ G V from σ.comp (QuotientGroup.mk' N)).leftQuotientSubmodule
        (H.comap (QuotientGroup.mk' N))
        (quotient_comap_subrepresentation σ H W)
        q) =
      σ.leftQuotientSubmodule H W (quotient_comap_leftCosetEquiv H q) := by
  refine Quotient.inductionOn' q ?_
  intro g
  -- Both summands are the image of `W` under the same operator `σ ((QuotientGroup.mk' N) g)`.
  simp [quotient_comap_leftCosetEquiv, quotient_comap_subrepresentation]

/-- Helper for Theorem 8-8.5-2: pulling an induced witness back along the quotient map preserves
the Chapter 3 internal direct-sum decomposition. -/
lemma isInducedFromSubrepresentation_comp_quotient_mk_of_isInducedFromSubrepresentation
    {N : Subgroup G} [N.Normal]
    (σ : Representation ℂ (G ⧸ N) V)
    (H : Subgroup (G ⧸ N))
    (W : Subrepresentation (σ.comp H.subtype))
    (hWinduced : σ.IsInducedFromSubrepresentation H W) :
    (show Representation ℂ G V from σ.comp (QuotientGroup.mk' N)).IsInducedFromSubrepresentation
      (H.comap (QuotientGroup.mk' N))
      (quotient_comap_subrepresentation σ H W) := by
  classical
  let ρG : Representation ℂ G V := σ.comp (QuotientGroup.mk' N)
  let e := quotient_comap_leftCosetEquiv (N := N) H
  let _ : DecidableEq (G ⧸ H.comap (QuotientGroup.mk' N)) := Classical.decEq _
  let _ : DecidableEq ((G ⧸ N) ⧸ H) := Classical.decEq _
  have hinternal :
      DirectSum.IsInternal (σ.leftQuotientSubmodule H W) := by
    -- Unpack the downstairs inducedness witness once so the upstairs proof can be a pure
    -- reindexing argument.
    simpa [Representation.IsInducedFromSubrepresentation] using hWinduced
  have hleft_fun :
      ρG.leftQuotientSubmodule
          (H.comap (QuotientGroup.mk' N))
          (quotient_comap_subrepresentation σ H W) =
        σ.leftQuotientSubmodule H W ∘ e := by
    funext q
    simpa [ρG, e, Function.comp] using
      leftQuotientSubmodule_quotient_comap_eq (N := N) σ H W q
  have hindep :
      iSupIndep
        (ρG.leftQuotientSubmodule
          (H.comap (QuotientGroup.mk' N))
          (quotient_comap_subrepresentation σ H W)) := by
    -- Route correction: transfer the Chapter 3 internal decomposition across the quotient-coset
    -- equivalence instead of comparing induced owners directly.
    rw [hleft_fun]
    exact hinternal.submodule_iSupIndep.comp e.injective
  have hspan :
      iSup
          (ρG.leftQuotientSubmodule
            (H.comap (QuotientGroup.mk' N))
            (quotient_comap_subrepresentation σ H W)) =
        ⊤ := by
    -- The same reindexing carries the spanning statement upstairs.
    calc
      iSup
          (ρG.leftQuotientSubmodule
            (H.comap (QuotientGroup.mk' N))
            (quotient_comap_subrepresentation σ H W)) =
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

/-- Helper for Theorem 8-8.5-2: monomiality for a quotient representation should pull back along
the quotient map by taking the inverse image of the witnessing subgroup. -/
lemma isMonomial_comp_quotient_mk_of_isMonomial
    {N : Subgroup G} [N.Normal]
    (σ : Representation ℂ (G ⧸ N) V)
    (hσ : σ.IsMonomial) :
    (show Representation ℂ G V from σ.comp (QuotientGroup.mk' N)).IsMonomial := by
  rcases hσ with ⟨H, W, hWdim, hWinduced⟩
  let K : Subgroup G := H.comap (QuotientGroup.mk' N)
  let W' :
      Subrepresentation
        (((show Representation ℂ G V from σ.comp (QuotientGroup.mk' N)).comp K.subtype)) :=
    quotient_comap_subrepresentation σ H W
  refine ⟨K, W', ?_, ?_⟩
  · -- The quotient pullback does not change the underlying carrier of the witness subspace.
    calc
      Module.finrank ℂ W'.toSubmodule = Module.finrank ℂ W.toSubmodule := by
        simpa [W', K] using quotient_comap_subrepresentation_finrank σ H W
      _ = 1 := hWdim
  · -- The quotient branch closes directly at the internal direct-sum level.
    simpa [K, W'] using
      isInducedFromSubrepresentation_comp_quotient_mk_of_isInducedFromSubrepresentation
        σ H W hWinduced

/-- Helper for Theorem 8-8.5-2: if the quotient representation by the kernel is monomial, then
the original representation is monomial by pulling the witness back along the quotient map. -/
lemma isMonomial_of_quotient_ker_isMonomial
    (ρ : Representation ℂ G V)
    [Representation.IsTrivial (ρ.comp ρ.ker.subtype)]
    (hquot : (ρ.ofQuotient ρ.ker).IsMonomial) :
    ρ.IsMonomial := by
  -- The quotient-pullback lemma applies to `ρ.ofQuotient ρ.ker`, and the resulting pulled-back
  -- representation is definitionally the original action `ρ`.
  simpa using
    (isMonomial_comp_quotient_mk_of_isMonomial
      (σ := ρ.ofQuotient ρ.ker) hquot)

/- Source/core/bridge triage:
* `source-facing`: Serre's theorem that irreducible complex representations of finite
  supersolvable groups are monomial.
* `core/canonical`: `Representation.IsMonomial`, whose primitive data already packages the
  subgroup, one-dimensional subrepresentation, and induction witness.
* `bridge/view`: `Representation.IsInducedFromSubrepresentation` is internal owner data for
  `IsMonomial`, not a second public owner in this file.

Sampled owner declarations in this domain:
* `Representation.IsInducedFromSubrepresentation`
* `Representation.IsMonomial`
* `Representation.IsIrreducible.finiteDimensional_of_finite`
* `IsSupersolvable`

Primitive data versus derived API:
this theorem does not introduce new subgroup-level data. It only proves the canonical owner
property `ρ.IsMonomial`, so the theorem name should follow that owner instead of restating the
existential witness pattern already bundled upstream. -/

-- Proof sketch: argue by induction on the order of `G`. If `G` is abelian, every irreducible
-- finite-dimensional complex representation has degree `1`, so `ρ` itself is the required
-- subgroup representation. Otherwise, use Lemma `8-8.5-1` to find a normal abelian subgroup not
-- contained in the center, and apply Proposition `8-8.1-1` to obtain a proper subgroup `H` from
-- which `ρ` is induced. Since subgroups of supersolvable groups are supersolvable, the induction
-- hypothesis applied inside `H` gives a one-dimensional subgroup representation whose induction to
-- `H` yields the intermediate irreducible representation, and transitivity of induction then
-- identifies `ρ` with the induction of that degree-one representation. The finite-dimensionality
-- needed to speak about degree `1` is derived internally from `ρ.IsIrreducible` and `Finite G`
-- via `Representation.IsIrreducible.finiteDimensional_of_finite`.
/-- Theorem 8-8.5-2: every irreducible complex representation of a finite supersolvable group is
induced from a degree-`1` subrepresentation of a subgroup. -/
theorem isMonomial_of_irreducible_of_supersolvable
    {G : Type} [Group G] [Finite G] [IsSupersolvable G]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] :
    ρ.IsMonomial := by
  classical
  by_cases hfaithful : Function.Injective ρ
  · by_cases hcomm : IsMulCommutative G
    · exact isMonomial_of_irreducible_of_isMulCommutative ρ hcomm
    · obtain ⟨A, hAnormal, hAcomm, hAcenter⟩ :=
        exists_normal_commutative_subgroup_not_le_center_of_nonabelian_supersolvable hcomm
      letI : A.Normal := hAnormal
      letI : IsMulCommutative A := hAcomm
      rcases
          exists_proper_overgroup_irreducible_induced_or_restriction_isotypic
            ρ A with
        ⟨H, hAH, hHtop, W, hWirr, hInduced⟩ | hIsotypic
      · letI : W.toRepresentation.IsIrreducible := hWirr
        -- Recurse on the proper subgroup from Proposition `8-8.1-1`, then finish by induction
        -- in stages through the isolated helper above.
        have hWmonomial : W.toRepresentation.IsMonomial :=
          isMonomial_of_irreducible_of_supersolvable W.toRepresentation
        exact
          isMonomial_of_induced_from_monomial_subrepresentation
            ρ H W hInduced hWmonomial
      · exact
          False.elim <|
            not_restriction_isotypic_of_faithful_of_not_le_center
              ρ A hfaithful hAcenter hIsotypic
  · have hker_ne_bot : ρ.ker ≠ ⊥ := by
      intro hker_bot
      apply hfaithful
      exact (MonoidHom.ker_eq_bot_iff ρ).mp hker_bot
    letI : Representation.IsTrivial (ρ.comp ρ.ker.subtype) := by
      constructor
      intro g
      ext v
      simpa using LinearMap.congr_fun g.property v
    let σ : Representation ℂ (G ⧸ ρ.ker) V := ρ.ofQuotient ρ.ker
    letI : σ.IsIrreducible := isIrreducible_of_ofQuotient_of_isTrivial ρ ρ.ker
    -- Route correction: the nonfaithful branch is handled on the quotient first; the remaining
    -- gap is only the pullback of the monomial witness along `G → G ⧸ ρ.ker`.
    have hσmonomial : (ρ.ofQuotient ρ.ker).IsMonomial := by
      simpa [σ] using isMonomial_of_irreducible_of_supersolvable σ
    exact isMonomial_of_quotient_ker_isMonomial ρ hσmonomial
termination_by Nat.card G
decreasing_by
  · rw [← H.index_mul_card]
    exact
      lt_mul_of_one_lt_left Nat.card_pos
        (Subgroup.one_lt_index_of_ne_top hHtop.ne)
  · rw [← ρ.ker.index_eq_card, ← ρ.ker.index_mul_card]
    exact
      lt_mul_of_one_lt_right
        (Nat.pos_of_ne_zero ρ.ker.index_ne_zero_of_finite)
        (ρ.ker.one_lt_card_iff_ne_bot.mpr hker_ne_bot)

end

end Representation
