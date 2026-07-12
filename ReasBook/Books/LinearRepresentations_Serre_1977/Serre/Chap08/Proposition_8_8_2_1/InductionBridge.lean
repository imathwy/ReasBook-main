import LinearRepresentations_Serre_1977.Chap03.Exercise_3_3_3_6
import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_2_1.CharacterPacketCore

open CategoryTheory

universe u v w x

namespace Representation

noncomputable section

section SemidirectAbelian

open scoped Representation

variable {A : Type u} [CommGroup A]
variable {H : Type v} [Group H]
variable (φ : H →* MulAut A)

/-- Helper for Proposition 8-8.2-1: the explicit packet subgroup is the pullback of the
stabilizer along the right projection. -/
abbrev character_stabilizer_subgroup (χ : A →* ℂˣ) : Subgroup (A ⋊[φ] H) where
  carrier := {x | x.right ∈ H_[φ; χ]}
  one_mem' := by
    let _ := characterMulAction φ
    change ((1 : H) • χ : A →* ℂˣ) = χ
    simp
  mul_mem' := by
    let _ := characterMulAction φ
    intro x y hx hy
    change (((x.right * y.right : H) • χ : A →* ℂˣ) = χ)
    calc
      ((x.right * y.right : H) • χ : A →* ℂˣ) = (x.right : H) • ((y.right : H) • χ) := by
        simp [smul_smul]
      _ = (x.right : H) • χ := by rw [hy]
      _ = χ := hx
  inv_mem' := by
    let _ := characterMulAction φ
    intro x hx
    change ((x.right⁻¹ : H) • χ : A →* ℂˣ) = χ
    calc
      ((x.right⁻¹ : H) • χ : A →* ℂˣ) = (x.right⁻¹ : H) • ((x.right : H) • χ) := by
        rw [hx]
      _ = χ := by
        simp [smul_smul]

/-- Helper for Proposition 8-8.2-1: a surjective homomorphism identifies left cosets of a comap
subgroup with left cosets of the original subgroup. -/
noncomputable def comap_leftCosetEquiv_of_surjective
    {G K : Type*} [Group G] [Group K]
    (f : G →* K) (hf : Function.Surjective f) (L : Subgroup K) :
    G ⧸ L.comap f ≃ K ⧸ L := by
  classical
  let s : K → G := fun x ↦ Classical.choose (hf x)
  have hs : ∀ x : K, f (s x) = x := fun x ↦ Classical.choose_spec (hf x)
  refine
    { toFun := Quotient.lift (fun g : G ↦ ((f g : K) : K ⧸ L)) ?_
      invFun := Quotient.lift (fun x : K ↦ ((s x : G) : G ⧸ L.comap f)) ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro g₁ g₂ hgg
    apply Quotient.sound'
    show QuotientGroup.leftRel L (f g₁) (f g₂)
    simpa [QuotientGroup.leftRel_apply, Subgroup.mem_comap, map_mul] using hgg
  · intro x y hxy
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    show f ((s x)⁻¹ * s y) ∈ L
    rw [map_mul]
    simpa [QuotientGroup.leftRel_apply, hs x, hs y] using hxy
  · intro g
    refine Quotient.inductionOn' g ?_
    intro a
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    show f ((s (f a))⁻¹ * a) ∈ L
    rw [map_mul]
    have hone : (1 : K) ∈ L := by simp
    simpa [hs (f a)] using hone
  · intro x
    refine Quotient.inductionOn' x ?_
    intro y
    change ((f (s y) : K) : K ⧸ L) = (y : K ⧸ L)
    simp [hs]

/-- Helper for Proposition 8-8.2-1: the explicit packet subgroup is the pullback of the
stabilizer along the right projection. -/
@[simp] theorem character_stabilizer_subgroup_eq_comap
    (χ : A →* ℂˣ) :
    character_stabilizer_subgroup (φ := φ) χ =
      (H_[φ; χ]).comap (SemidirectProduct.rightHom : A ⋊[φ] H →* H) := by
  rfl

/-- Helper for Proposition 8-8.2-1: the quotient by the explicit packet subgroup is finite
because it identifies with the stabilizer quotient of `H`. -/
theorem character_stabilizer_subgroup_quotient_finite [Finite H]
    (χ : A →* ℂˣ) :
    Finite ((A ⋊[φ] H) ⧸ character_stabilizer_subgroup (φ := φ) χ) := by
  classical
  let equot :
      (A ⋊[φ] H) ⧸ character_stabilizer_subgroup (φ := φ) χ ≃ H ⧸ H_[φ; χ] := by
    simpa [character_stabilizer_subgroup_eq_comap (φ := φ) χ] using
      (comap_leftCosetEquiv_of_surjective
        (SemidirectProduct.rightHom : A ⋊[φ] H →* H)
        SemidirectProduct.rightHom_surjective
        (H_[φ; χ]))
  exact Finite.of_equiv (H ⧸ H_[φ; χ]) equot.symm

/-- Helper for Proposition 8-8.2-1: restricting a representation equivalence along a subgroup keeps
the same underlying linear equivalence. -/
theorem comp_subtype_equiv_isIntertwining
    {K : Type*} [Group K]
    {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K) :
    ∀ s, e.toLinearEquiv ∘ₗ (ρ.comp S.subtype) s = (σ.comp S.subtype) s ∘ₗ e.toLinearEquiv := by
  intro s
  simpa using e.isIntertwining' (s : K)

/-- Helper for Proposition 8-8.2-1: restricting a representation equivalence along a subgroup keeps
the same underlying linear equivalence. -/
noncomputable def comp_subtype_equiv
    {K : Type*} [Group K]
    {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K) :
    Representation.Equiv (ρ.comp S.subtype) (σ.comp S.subtype) :=
  Representation.Equiv.mk e.toLinearEquiv (comp_subtype_equiv_isIntertwining e S)

/-- Helper for Proposition 8-8.2-1: precomposing an irreducible representation with a group
equivalence preserves irreducibility because it does not change the stable subspaces, only the
indexing of the operators. -/
theorem isIrreducible_comp_of_mulEquiv_local
    {K : Type*} [Field K] {G : Type*} [Group G] {G₁ : Type*} [Group G₁]
    {W : Type*} [AddCommGroup W] [Module K W]
    (e : G ≃* G₁) (σ : Representation K G₁ W) [σ.IsIrreducible] :
    Representation.IsIrreducible (σ.comp e.toMonoidHom) := by
  classical
  letI : Nontrivial (Subrepresentation (σ.comp e.toMonoidHom)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    have h' : (⊥ : Subrepresentation σ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      simpa using congrArg Subrepresentation.toSubmodule h
    exact IsSimpleOrder.bot_ne_top h'
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro W' hW'
  let W'' : Subrepresentation σ :=
    { toSubmodule := W'.toSubmodule
      apply_mem_toSubmodule := by
        intro g x hx
        simpa using W'.apply_mem_toSubmodule (e.symm g) hx }
  have hW''_ne_bot : W'' ≠ ⊥ := by
    intro hW''
    apply hW'
    apply Subrepresentation.toSubmodule_injective
    simpa [W''] using congrArg Subrepresentation.toSubmodule hW''
  have hW''_top : W'' = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W'').resolve_left hW''_ne_bot
  apply Subrepresentation.toSubmodule_injective
  simpa [W''] using congrArg Subrepresentation.toSubmodule hW''_top

/-- Helper for Proposition 8-8.2-1: a subrepresentation transports across a representation
equivalence by mapping its carrier through the underlying linear equivalence. -/
theorem transported_subrepresentation_of_equiv_stable
    {K : Type*} [Group K]
    {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    ∀ g ⦃x : W'⦄, x ∈ U.toSubmodule.map e.toLinearMap → σ g x ∈ U.toSubmodule.map e.toLinearMap := by
  intro g x hx
  rcases hx with ⟨y, hy, rfl⟩
  refine ⟨ρ g y, U.apply_mem_toSubmodule g hy, ?_⟩
  simp [e.isIntertwining]

/-- Helper for Proposition 8-8.2-1: a subrepresentation transports across a representation
equivalence by mapping its carrier through the underlying linear equivalence. -/
noncomputable def transported_subrepresentation_of_equiv
    {K : Type*} [Group K]
    {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    Subrepresentation σ where
  toSubmodule := U.toSubmodule.map e.toLinearMap
  apply_mem_toSubmodule := transported_subrepresentation_of_equiv_stable e U

/-- Helper for Proposition 8-8.2-1: transporting the inducing subrepresentation along an ambient
equivalence transports each left-coset summand by the same linear equivalence. -/
theorem leftQuotientSubmodule_eq_map_of_equiv
    {K : Type*} [Group K]
    {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K)
    (U : Subrepresentation (ρ.comp S.subtype)) (q : K ⧸ S) :
    σ.leftQuotientSubmodule S
        (transported_subrepresentation_of_equiv (comp_subtype_equiv e S) U) q =
      (ρ.leftQuotientSubmodule S U q).map e.toLinearMap := by
  refine Quotient.inductionOn' q ?_
  intro g
  rw [Representation.leftQuotientSubmodule_mk, Representation.leftQuotientSubmodule_mk]
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨ρ g u, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    · simpa [comp_subtype_equiv] using LinearMap.congr_fun (e.isIntertwining' g) u
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Submodule.mem_map.mp hy with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨e u, ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
    · simpa [comp_subtype_equiv] using (LinearMap.congr_fun (e.isIntertwining' g) u).symm

/-- Helper for Proposition 8-8.2-1: inducedness data is preserved when the ambient
representation is replaced by an equivalent one. -/
theorem isInducedFromSubrepresentation_of_equiv
    {K : Type*} [Group K]
    {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
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
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  have hleft_fun :
      σ.leftQuotientSubmodule S U' = fun q ↦ (ρ.leftQuotientSubmodule S U q).map e.toLinearMap := by
    funext q
    simpa [U'] using leftQuotientSubmodule_eq_map_of_equiv e S U q
  have hindep : iSupIndep (σ.leftQuotientSubmodule S U') := by
    rw [hleft_fun]
    exact LinearMap.iSupIndep_map e.toLinearMap e.injective hinternal.submodule_iSupIndep
  have hspan : iSup (σ.leftQuotientSubmodule S U') = ⊤ := by
    calc
      iSup (σ.leftQuotientSubmodule S U') =
          iSup (fun q ↦ (ρ.leftQuotientSubmodule S U q).map e.toLinearMap) := by
            rw [hleft_fun]
      _ = (iSup (ρ.leftQuotientSubmodule S U)).map e.toLinearMap := by
            rw [Submodule.map_iSup]
      _ = ⊤ := by
            rw [hinternal.submodule_iSup_eq_top, Submodule.map_top]
            exact LinearMap.range_eq_top.mpr e.surjective
  unfold Representation.IsInducedFromSubrepresentation
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep hspan

/-- Helper for Proposition 8-8.2-1: ordinary induction from a finite-index subgroup is
finite-dimensional over `ℂ` as soon as the source is finite-dimensional. -/
theorem finiteDimensional_ind_of_finite_quotient
    {G : Type*} [Group G]
    {S : Subgroup G} [Finite (G ⧸ S)]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ S W) :
    FiniteDimensional ℂ (Rep.ind S.subtype (Rep.of σ)) := by
  classical
  letI : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  letI : DecidableEq (G ⧸ S) := Classical.decEq _
  let C : Rep ℂ G := Rep.coind S.subtype (Rep.of σ)
  let e : ((Rep.ind S.subtype (Rep.of σ)).ρ).Equiv C.ρ :=
    Representation.equivOfIso (Rep.indCoindIso (Rep.of σ))
  let W₀ : Subrepresentation (C.ρ.comp S.subtype) :=
    Representation.supportedOnSubgroupSubrepresentation S σ
  let U : Subrepresentation (((Rep.ind S.subtype (Rep.of σ)).ρ).comp S.subtype) :=
    transported_subrepresentation_of_equiv (comp_subtype_equiv e.symm S) W₀
  have hW₀ :
      C.ρ.IsInducedFromSubrepresentation S W₀ := by
    simpa [C, W₀] using
      (Representation.isInducedFrom_supportedOnSubgroupSubrepresentation (H := S) (θ := σ))
  have hU :
      ((Rep.ind S.subtype (Rep.of σ)).ρ).IsInducedFromSubrepresentation S U := by
    simpa [U] using isInducedFromSubrepresentation_of_equiv e.symm S W₀ hW₀
  let eU :
      W₀.toSubmodule ≃ₗ[ℂ] U.toSubmodule :=
    Submodule.equivMapOfInjective e.symm.toLinearMap e.symm.injective W₀.toSubmodule
  have hW₀finite : FiniteDimensional ℂ W₀.toSubmodule := by
    exact
      FiniteDimensional.of_injective
        (Representation.supportedOnSubgroupEquiv S σ).symm.toLinearMap
        (Representation.supportedOnSubgroupEquiv S σ).symm.injective
  letI : FiniteDimensional ℂ W₀.toSubmodule := hW₀finite
  letI : FiniteDimensional ℂ U.toSubmodule :=
    FiniteDimensional.of_injective eU.symm.toLinearMap eU.symm.injective
  letI : ∀ q : G ⧸ S,
      FiniteDimensional ℂ (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U q) :=
    fun q ↦ by
      have hleft :
          ((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U q =
            U.toSubmodule.map (((Rep.ind S.subtype (Rep.of σ)).ρ) q.out) := by
        simpa [Quotient.out_eq q] using
          (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule_mk S U q.out)
      let eUq :
          U.toSubmodule ≃ₗ[ℂ]
            ((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U q :=
        let eV : Rep.ind S.subtype (Rep.of σ) ≃ₗ[ℂ] Rep.ind S.subtype (Rep.of σ) :=
          LinearEquiv.ofBijective
            (((Rep.ind S.subtype (Rep.of σ)).ρ) q.out)
            (((Rep.ind S.subtype (Rep.of σ)).ρ).apply_bijective q.out)
        (eV.submoduleMap U.toSubmodule).trans
          (LinearEquiv.ofEq _ _ hleft.symm)
      exact FiniteDimensional.of_injective eUq.symm.toLinearMap eUq.symm.injective
  have hInternal :
      DirectSum.IsInternal (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U) := by
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  letI := DirectSum.IsInternal.chooseDecomposition
    (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U) hInternal
  letI : FiniteDimensional ℂ
      (DirectSum (G ⧸ S)
        fun q ↦ ((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U q) := by
    infer_instance
  let eDecomp :=
    (DirectSum.decomposeLinearEquiv
      (((Rep.ind S.subtype (Rep.of σ)).ρ).leftQuotientSubmodule S U)).symm
  exact FiniteDimensional.of_injective eDecomp.symm.toLinearMap eDecomp.symm.injective

/-- Helper for Proposition 8-8.2-1: the semidirect product over the stabilizer is identified with
the explicit subgroup of `A ⋊[φ] H` cut out by the stabilizer condition on the `H`-component. -/
noncomputable def character_stabilizer_subgroup_equiv
    (χ : A →* ℂˣ) :
    A ⋊[stabilizerAction φ χ] H_[φ; χ] ≃* character_stabilizer_subgroup (φ := φ) χ :=
  { toFun := fun x ↦
      ⟨stabilizerInclusion φ χ x, by
        let _ := characterMulAction φ
        change (((x.right : H) • χ : A →* ℂˣ) = χ)
        exact x.right.property⟩
    invFun := fun x ↦ ⟨x.1.left, ⟨x.1.right, x.2⟩⟩
    left_inv := by
      intro x
      ext <;> rfl
    right_inv := by
      intro x
      ext <;> rfl
    map_mul' := by
      intro x y
      ext <;> rfl }

/-- Helper for Proposition 8-8.2-1: the explicit packet subgroup remembers its second coordinate as
an element of the stabilizer. -/
noncomputable def character_stabilizer_projection
    (χ : A →* ℂˣ) :
    character_stabilizer_subgroup (φ := φ) χ →* H_[φ; χ] where
  toFun := fun x ↦ ⟨x.1.right, x.2⟩
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- Helper for Proposition 8-8.2-1: after rewriting the source of `θ[φ; χ, ρ]` on the explicit
subgroup of `A ⋊[φ] H`, the packet source is still irreducible. -/
theorem character_stabilizer_subgroup_source_isIrreducible
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [ρ.ρ.IsIrreducible] :
    Representation.IsIrreducible
      ((stabilizerRepresentation φ χ ρ).ρ.comp
        (character_stabilizer_subgroup_equiv (φ := φ) χ).symm.toMonoidHom) := by
  have hsource :
      (stabilizerRepresentation φ χ ρ).ρ.IsIrreducible :=
    stabilizerRepresentation_isIrreducible (φ := φ) χ ρ
  letI : (stabilizerRepresentation φ χ ρ).ρ.IsIrreducible := hsource
  exact
    isIrreducible_comp_of_mulEquiv_local
      (e := (character_stabilizer_subgroup_equiv (φ := φ) χ).symm)
      ((stabilizerRepresentation φ χ ρ).ρ)

/-- Helper for Proposition 8-8.2-1: the packet source rewritten on the explicit subgroup of
`A ⋊[φ] H`. -/
noncomputable abbrev theta_packet_source
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) :
    Rep.{w} ℂ (character_stabilizer_subgroup (φ := φ) χ) :=
  Rep.of
    ((stabilizerRepresentation φ χ ρ).ρ.comp
      (character_stabilizer_subgroup_equiv (φ := φ) χ).symm.toMonoidHom)

/-- Helper for Proposition 8-8.2-1: the second-coordinate projection from the explicit packet
subgroup onto the stabilizer is surjective. -/
theorem character_stabilizer_projection_surjective
    (χ : A →* ℂˣ) :
    Function.Surjective (character_stabilizer_projection (φ := φ) χ) := by
  intro h
  refine ⟨⟨⟨1, h⟩, h.property⟩, ?_⟩
  ext <;> rfl

/-- Helper for Proposition 8-8.2-1: the source inclusion of `θ` factors through the explicit
subgroup via the canonical stabilizer equivalence. -/
@[simp] theorem stabilizerInclusion_eq_subgroup_subtype_comp
    (χ : A →* ℂˣ) :
    stabilizerInclusion φ χ =
      (character_stabilizer_subgroup (φ := φ) χ).subtype.comp
        (character_stabilizer_subgroup_equiv (φ := φ) χ).toMonoidHom := by
  ext x <;> rfl

/-- Helper for Proposition 8-8.2-1: reindexing the induction source by a group equivalence does
not change the span of the induction coinvariant relations. -/
theorem ind_ker_comp_equiv_eq
    {G K L : Type*} [Group G] [Group K] [Group L]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (e : G ≃* K) (f : K →* L) (ρ : Representation ℂ K W) :
    Representation.Coinvariants.ker
        (Representation.tprod ((leftRegular ℂ L).comp (f.comp e.toMonoidHom))
          (ρ.comp e.toMonoidHom)) =
      Representation.Coinvariants.ker
        (Representation.tprod ((leftRegular ℂ L).comp f) ρ) := by
  unfold Representation.Coinvariants.ker
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨⟨g, v⟩, rfl⟩
    exact Submodule.subset_span ⟨(e g, v), rfl⟩
  · refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨⟨k, v⟩, rfl⟩
    exact Submodule.subset_span ⟨(e.symm k, v), by simp⟩

/-- Helper for Proposition 8-8.2-1: induction along a source-group equivalence is the same induced
representation after reindexing the coinvariant quotient. -/
noncomputable def ind_equiv_of_comp_equiv
    {G K L : Type*} [Group G] [Group K] [Group L]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (e : G ≃* K) (f : K →* L) (ρ : Representation ℂ K W) :
    (Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)).Equiv
      (Representation.ind f ρ) := by
  refine Representation.Equiv.mk
      (Submodule.quotEquivOfEq _ _ (ind_ker_comp_equiv_eq e f ρ)) ?_
  intro l
  apply Representation.IndV.hom_ext
  intro l'
  ext v
  simp only [LinearMap.comp_apply]
  change (Submodule.quotEquivOfEq _ _ (ind_ker_comp_equiv_eq e f ρ))
      (((Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) l)
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) l') v)) =
    ((Representation.ind f ρ) l)
      ((Submodule.quotEquivOfEq _ _ (ind_ker_comp_equiv_eq e f ρ))
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) l') v))
  have hleft :
      ((Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)) l)
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) l') v) =
      (Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (l' * l⁻¹)) v := by
    exact Representation.ind_mk (φ := f.comp e.toMonoidHom) (ρ := ρ.comp e.toMonoidHom) l l' v
  have hright :
      ((Representation.ind f ρ) l)
        ((Representation.IndV.mk f ρ l') v) =
      (Representation.IndV.mk f ρ (l' * l⁻¹)) v := by
    exact Representation.ind_mk (φ := f) (ρ := ρ) l l' v
  have hsource :
      (Submodule.quotEquivOfEq
          (Representation.Coinvariants.ker
            (Representation.tprod ((leftRegular ℂ L).comp (f.comp e.toMonoidHom))
              (ρ.comp e.toMonoidHom)))
          (Representation.Coinvariants.ker
            (Representation.tprod ((leftRegular ℂ L).comp f) ρ))
          (ind_ker_comp_equiv_eq e f ρ))
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) l') v) =
      (Representation.IndV.mk f ρ l') v := by
    exact Submodule.quotEquivOfEq_mk _ _ (ind_ker_comp_equiv_eq e f ρ) _
  have hsource' :
      (Submodule.quotEquivOfEq
          (Representation.Coinvariants.ker
            (Representation.tprod ((leftRegular ℂ L).comp (f.comp e.toMonoidHom))
              (ρ.comp e.toMonoidHom)))
          (Representation.Coinvariants.ker
            (Representation.tprod ((leftRegular ℂ L).comp f) ρ))
          (ind_ker_comp_equiv_eq e f ρ))
        ((Representation.IndV.mk (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom) (l' * l⁻¹)) v) =
      (Representation.IndV.mk f ρ (l' * l⁻¹)) v := by
    exact Submodule.quotEquivOfEq_mk _ _ (ind_ker_comp_equiv_eq e f ρ) _
  rw [hleft, hsource', hsource, hright]

/-- Helper for Proposition 8-8.2-1: rewriting the packet source as an explicit subgroup identifies
`θ[φ; χ, ρ]` with ordinary induction from the subgroup-side twisting representation. -/
noncomputable def theta_equiv_ind_character_stabilizer_subgroup
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) :
    (θ[φ; χ, ρ]).ρ.Equiv
      (Rep.ind (character_stabilizer_subgroup (φ := φ) χ).subtype
        (Rep.of
          ((stabilizerRepresentation φ χ ρ).ρ.comp
            (character_stabilizer_subgroup_equiv (φ := φ) χ).symm.toMonoidHom))).ρ := by
  simpa [Representation.theta, stabilizerInclusion_eq_subgroup_subtype_comp] using
    (ind_equiv_of_comp_equiv
      (character_stabilizer_subgroup_equiv (φ := φ) χ)
      (character_stabilizer_subgroup (φ := φ) χ).subtype
      ((stabilizerRepresentation φ χ ρ).ρ.comp
        (character_stabilizer_subgroup_equiv (φ := φ) χ).symm.toMonoidHom))

/-- Helper for Proposition 8-8.2-1: the local Mackey conjugation map for a subgroup of
`A ⋊[φ] H`, copied here because the Chapter 7 file cannot be imported into this workspace without a
declaration clash. -/
abbrev localMackeyConjMap
    (K : Subgroup (A ⋊[φ] H)) (s : A ⋊[φ] H) :
    K →* A ⋊[φ] H :=
  (MulAut.conj s⁻¹).toMonoidHom.comp K.subtype

/-- Helper for Proposition 8-8.2-1: the local Mackey subgroup `K ∩ sHs⁻¹` inside a subgroup `K`,
again kept file-local so the packet proof can use the Mackey shape without importing Chapter 7. -/
abbrev localMackeySubgroup
    (K H' : Subgroup (A ⋊[φ] H)) (s : A ⋊[φ] H) : Subgroup K :=
  H'.comap (localMackeyConjMap (φ := φ) K s)

/-- Helper for Proposition 8-8.2-1: the local conjugation homomorphism from the file-local Mackey
subgroup to the target subgroup. -/
abbrev localMackeyConjHom
    (K H' : Subgroup (A ⋊[φ] H)) (s : A ⋊[φ] H) :
    localMackeySubgroup (φ := φ) K H' s →* H' :=
  ((localMackeyConjMap (φ := φ) K s).restrict (localMackeySubgroup (φ := φ) K H' s)).codRestrict
    H' fun x ↦ x.2

/-- Helper for Proposition 8-8.2-1: the file-local Mackey twist along the conjugation homomorphism
above. This is the exact owner needed for the scalar-mismatch lemma below. -/
noncomputable abbrev localMackeyTwist
    (K H' : Subgroup (A ⋊[φ] H)) (W : Rep ℂ H') (s : A ⋊[φ] H) :
    Rep ℂ (localMackeySubgroup (φ := φ) K H' s) :=
  Rep.res (localMackeyConjHom (φ := φ) K H' s) W

/-- For finite `H`, Serre's induced representation `θ[φ; χ, ρ]` is finite-dimensional as soon as
`ρ` is. -/
noncomputable instance thetaFiniteDimensional [Finite H]
    (χ : A →* ℂˣ) (ρ : Rep.{w} ℂ H_[φ; χ]) [FiniteDimensional ℂ ρ] :
    FiniteDimensional ℂ (θ[φ; χ, ρ]) := by
  letI : Finite ((A ⋊[φ] H) ⧸ character_stabilizer_subgroup (φ := φ) χ) :=
    character_stabilizer_subgroup_quotient_finite (φ := φ) χ
  letI : FiniteDimensional ℂ (stabilizerRepresentation φ χ ρ) := by
    change FiniteDimensional ℂ ρ
    infer_instance
  letI :
      FiniteDimensional ℂ
        (Rep.ind (character_stabilizer_subgroup (φ := φ) χ).subtype
          (Rep.of
            ((stabilizerRepresentation φ χ ρ).ρ.comp
              (character_stabilizer_subgroup_equiv (φ := φ) χ).symm.toMonoidHom))) :=
    finiteDimensional_ind_of_finite_quotient
      (σ := (stabilizerRepresentation φ χ ρ).ρ.comp
        (character_stabilizer_subgroup_equiv (φ := φ) χ).symm.toMonoidHom)
  exact
    FiniteDimensional.of_injective
      (theta_equiv_ind_character_stabilizer_subgroup (φ := φ) χ ρ).toLinearMap
      (theta_equiv_ind_character_stabilizer_subgroup (φ := φ) χ ρ).injective

end SemidirectAbelian

end

end Representation
