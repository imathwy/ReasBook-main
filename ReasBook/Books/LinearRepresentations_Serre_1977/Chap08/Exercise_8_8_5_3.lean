import Mathlib
import LinearRepresentations_Serre_1977.Chap08.Definition_8_8_3_2
import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_2_1
import LinearRepresentations_Serre_1977.Chap08.Theorem_8_8_5_2

-- Declarations for this item will be appended below by the statement pipeline.

namespace Representation

open CategoryTheory Rep
open scoped Representation

section

variable {A H : Type} [CommGroup A] [Group H] [Finite A] [Finite H] [IsSupersolvable H]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (φ : H →* MulAut A)

/-- Helper for Exercise 8-8.5-3: the little-groups classification uses the contragredient action
of `H` on the character group `A →* ℂˣ`. -/
private instance characterMulActionInst : MulAction H (A →* ℂˣ) := by
  let _ : MulAction H A := MulAction.compHom A φ
  let _ : MulDistribMulAction H A := MulDistribMulAction.compHom A φ
  let _ : MulAction Hᵈᵐᵃ (A →* ℂˣ) := inferInstance
  exact MulAction.compHom (A →* ℂˣ)
    (show H →* Hᵈᵐᵃ from (MulEquiv.inv' H).toMonoidHom)

/-- Helper for Exercise 8-8.5-3: a semidirect product of two finite groups is finite. -/
private theorem semidirectProduct_finite :
    Finite (A ⋊[φ] H) := by
  let eprod : A ⋊[φ] H ≃ A × H :=
    { toFun := fun x ↦ (x.1, x.2)
      invFun := fun p ↦ ⟨p.1, p.2⟩
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro p
        cases p
        rfl }
  -- The semidirect product has the same underlying carrier as the finite cartesian product.
  exact Finite.of_equiv (A × H) eprod.symm

/- Source/core/bridge triage:
* `source-facing`: this exercise extends Theorem `8-8.5-2` from supersolvable groups to
  semidirect products `A ⋊[φ] H` with `A` abelian and `H` supersolvable.
* `core/canonical`: the reduction step is Proposition `8-8.2-1`, which writes an irreducible
  representation of the semidirect product as a little-groups packet `θ[φ; χ, τ]`.
* `bridge/view`: once the stabilizer representation `τ` is monomial by Theorem `8-8.5-2`, the
  remaining work is to transport that monomial witness to the packet `θ[φ; χ, τ]` and then across
  the final representation isomorphism.

Primitive data are the abelian kernel `A`, the supersolvable quotient `H`, the action `φ`, and the
ambient irreducible representation `ρ`. The current file should therefore first reduce to a
stabilizer subgroup via Proposition `8-8.2-1`, and only then invoke the supersolvable owner
theorem on that subgroup. -/

/-- Helper for Exercise 8-8.5-3: `Quotient.out` chooses one representative of each orbit of the
`H`-action on the character group of `A`. -/
lemma exists_character_orbit_representative_family :
    ∃ (ι : Type) (χ : ι → A →* ℂˣ),
      Representation.HasCharacterOrbitRepresentatives φ χ := by
  classical
  let _ : MulAction H (A →* ℂˣ) := characterMulActionInst (φ := φ)
  refine ⟨MulAction.orbitRel.Quotient H (A →* ℂˣ), fun q ↦ Quotient.out q, ?_⟩
  -- `Quotient.out` is a section of the quotient map, so the induced map on orbit classes is
  -- automatically bijective.
  dsimp [Representation.HasCharacterOrbitRepresentatives]
  constructor
  · intro q q' hqq'
    calc
      q = Quotient.mk'' (Quotient.out q) := (Quotient.out_eq q).symm
      _ = Quotient.mk'' (Quotient.out q') := hqq'
      _ = q' := Quotient.out_eq q'
  · intro q
    refine ⟨q, ?_⟩
    exact Quotient.out_eq q

/-- Helper for Exercise 8-8.5-3: restricting a representation equivalence along a subgroup keeps
the same underlying linear equivalence. -/
private theorem comp_subtype_equiv_isIntertwining
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K) :
    ∀ s, e.toLinearEquiv ∘ₗ (ρ.comp S.subtype) s = (σ.comp S.subtype) s ∘ₗ e.toLinearEquiv := by
  intro s
  simpa using e.isIntertwining' (s : K)

/-- Helper for Exercise 8-8.5-3: restricting a representation equivalence along a subgroup keeps
the same underlying linear equivalence. -/
private noncomputable def comp_subtype_equiv
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K) :
    Representation.Equiv (ρ.comp S.subtype) (σ.comp S.subtype) :=
  Representation.Equiv.mk e.toLinearEquiv (comp_subtype_equiv_isIntertwining e S)

/-- Helper for Exercise 8-8.5-3: restricting the equivalence does not change the underlying
linear map. -/
@[simp] private theorem comp_subtype_equiv_toLinearMap
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K) :
    (comp_subtype_equiv e S).toLinearMap = e.toLinearMap :=
  rfl

/-- Helper for Exercise 8-8.5-3: restricting the equivalence does not change its action on
vectors. -/
@[simp] private theorem comp_subtype_equiv_apply
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (S : Subgroup K) (x : W) :
    comp_subtype_equiv e S x = e x :=
  rfl

/-- Helper for Exercise 8-8.5-3: a subrepresentation transports across a representation
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

/-- Helper for Exercise 8-8.5-3: a subrepresentation transports across a representation
equivalence by mapping its carrier through the underlying linear equivalence. -/
private noncomputable def transported_subrepresentation_of_equiv
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    Subrepresentation σ where
  toSubmodule := U.toSubmodule.map e.toLinearMap
  apply_mem_toSubmodule := transported_subrepresentation_of_equiv_stable e U

/-- Helper for Exercise 8-8.5-3: the transported subrepresentation has the expected mapped
carrier. -/
@[simp] private theorem transported_subrepresentation_of_equiv_toSubmodule
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) (U : Subrepresentation ρ) :
    (transported_subrepresentation_of_equiv e U).toSubmodule = U.toSubmodule.map e.toLinearMap :=
  rfl

/-- Helper for Exercise 8-8.5-3: transporting the inducing subrepresentation along an ambient
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

/-- Helper for Exercise 8-8.5-3: inducedness data is preserved when the ambient representation is
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
    -- Unpack the Chapter `3` owner so the proof can work directly with the quotient-indexed family.
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
  -- Package the transported independence and spanning statements back into the Chapter `3` owner.
  unfold Representation.IsInducedFromSubrepresentation
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep hspan

/-- Helper for Exercise 8-8.5-3: monomiality should transport across an equivalence of ambient
representations. -/
lemma isMonomial_of_equiv
    {K : Type} [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ K W} {σ : Representation ℂ K W'}
    (e : ρ.Equiv σ) :
    ρ.IsMonomial → σ.IsMonomial := by
  intro hρ
  rcases hρ with ⟨S, U, hUdim, hUinduced⟩
  let U' := transported_subrepresentation_of_equiv (comp_subtype_equiv e S) U
  have hU'map :
      U'.toSubmodule = U.toSubmodule.map e.toLinearMap := by
    simpa [U'] using
      transported_subrepresentation_of_equiv_toSubmodule
        (comp_subtype_equiv e S) U
  -- Route correction: once the subrepresentation is pushed through `e`, the rest is a direct
  -- transport of the Chapter `3` owner data `IsInducedFromSubrepresentation`.
  refine ⟨S, U', ?_, ?_⟩
  · -- The transported witness has the same one-dimensional carrier via the restricted linear
    -- equivalence from `U` onto its image.
    let eU : U.toSubmodule ≃ₗ[ℂ] U.toSubmodule.map e.toLinearMap :=
      Submodule.equivMapOfInjective e.toLinearMap e.injective U.toSubmodule
    calc
      Module.finrank ℂ U'.toSubmodule = Module.finrank ℂ (U.toSubmodule.map e.toLinearMap) := by
        rw [hU'map]
      _ = Module.finrank ℂ U.toSubmodule := by
        exact eU.symm.finrank_eq
      _ = 1 := hUdim
  · -- The quotient-indexed inducing family is obtained by mapping the old family through `e`.
    simpa [U'] using isInducedFromSubrepresentation_of_equiv e S U hUinduced

/-- Helper for Exercise 8-8.5-3: the stabilizer acts on `A` through the restricted semidirect
product action used in the little-groups packet `θ[φ; χ, τ]`. -/
private abbrev character_stabilizer_action (χ : A →* ℂˣ) :
    H_[φ; χ] →* MulAut A :=
  φ.comp (Subgroup.subtype H_[φ; χ])

/-- Helper for Exercise 8-8.5-3: elements of the stabilizer fix the character `χ` after transport
through the given action. -/
private theorem character_stabilizer_apply
    (χ : A →* ℂˣ) (h : H_[φ; χ]) (a : A) :
    χ (φ h a) = χ a := by
  let _ := characterMulActionInst (φ := φ)
  have hη := congrArg (fun η : A →* ℂˣ ↦ η (φ h a)) h.property
  simpa using hη.symm

/-- Helper for Exercise 8-8.5-3: the private induction source of `θ[φ; χ, τ]` is the canonical
sub-semiproduct inclusion into `A ⋊[φ] H`. -/
private abbrev character_stabilizer_inclusion (χ : A →* ℂˣ) :
    A ⋊[character_stabilizer_action (φ := φ) χ] H_[φ; χ] →* A ⋊[φ] H :=
  SemidirectProduct.map (MonoidHom.id A) (Subgroup.subtype H_[φ; χ])
    (fun h ↦ by
      ext a
      rfl)

/-- Helper for Exercise 8-8.5-3: the little-groups packet uses the standard extension of `χ` to
the stabilizer semidirect product, trivial on the stabilizer factor. -/
private def character_stabilizer_character (χ : A →* ℂˣ) :
    A ⋊[character_stabilizer_action (φ := φ) χ] H_[φ; χ] →* ℂˣ :=
  SemidirectProduct.lift χ 1 fun h ↦ by
    ext a
    simp [character_stabilizer_apply (φ := φ) χ h a]

/-- Helper for Exercise 8-8.5-3: the stabilizer character only records the `A`-coordinate. -/
@[simp] private theorem character_stabilizer_character_apply (χ : A →* ℂˣ)
    (x : A ⋊[character_stabilizer_action (φ := φ) χ] H_[φ; χ]) :
    character_stabilizer_character (φ := φ) χ x = χ x.left := by
  change χ x.left * (1 : H_[φ; χ] →* ℂˣ) x.right = χ x.left
  simp

/-- Helper for Exercise 8-8.5-3: the source-side packet representation is the tensor twist by the
character `χ` on `A` and the given stabilizer representation `τ` on `H_[φ; χ]`. -/
private noncomputable def character_twist_representation
    (χ : A →* ℂˣ) (τ : Rep ℂ H_[φ; χ]) :
    Representation ℂ (A ⋊[character_stabilizer_action (φ := φ) χ] H_[φ; χ]) τ.V :=
  { toFun := fun x ↦ (character_stabilizer_character (φ := φ) χ x : ℂ) • τ.ρ x.right
    map_one' := by
      ext v
      simp [character_stabilizer_character]
    map_mul' := by
      intro x y
      ext v
      rw [SemidirectProduct.mul_def, map_mul]
      simp [character_stabilizer_character_apply, smul_smul, mul_assoc,
        character_stabilizer_apply, mul_comm] }

/-- Helper for Exercise 8-8.5-3: the image of the private stabilizer inclusion is the explicit
subgroup of `A ⋊[φ] H` whose second component lies in `H_[φ; χ]`. -/
private abbrev character_stabilizer_subgroup (χ : A →* ℂˣ) : Subgroup (A ⋊[φ] H) where
  carrier := {x | x.right ∈ H_[φ; χ]}
  one_mem' := by
    let _ := characterMulActionInst (φ := φ)
    change ((1 : H) • χ : A →* ℂˣ) = χ
    simp
  mul_mem' := by
    let _ := characterMulActionInst (φ := φ)
    intro x y hx hy
    change (((x.right * y.right : H) • χ : A →* ℂˣ) = χ)
    calc
      ((x.right * y.right : H) • χ : A →* ℂˣ) = (x.right : H) • ((y.right : H) • χ) := by
        simp [smul_smul]
      _ = (x.right : H) • χ := by rw [hy]
      _ = χ := hx
  inv_mem' := by
    let _ := characterMulActionInst (φ := φ)
    intro x hx
    change ((x.right⁻¹ : H) • χ : A →* ℂˣ) = χ
    calc
      ((x.right⁻¹ : H) • χ : A →* ℂˣ) = (x.right⁻¹ : H) • ((x.right : H) • χ) := by
        rw [hx]
      _ = χ := by
        simp [smul_smul]

/-- Helper for Exercise 8-8.5-3: the private semidirect-product source of `θ` is canonically the
explicit subgroup of `A ⋊[φ] H` cut out by the stabilizer condition. -/
private noncomputable def character_stabilizer_subgroup_equiv
    (χ : A →* ℂˣ) :
    A ⋊[character_stabilizer_action (φ := φ) χ] H_[φ; χ] ≃*
      character_stabilizer_subgroup (φ := φ) χ :=
  { toFun := fun x ↦
      ⟨character_stabilizer_inclusion (φ := φ) χ x, by
        let _ := characterMulActionInst (φ := φ)
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

/-- Helper for Exercise 8-8.5-3: the private stabilizer inclusion factors through the explicit
subgroup via the canonical subgroup equivalence. -/
@[simp] private theorem character_stabilizer_inclusion_eq_subgroup_subtype_comp
    (χ : A →* ℂˣ) :
    character_stabilizer_inclusion (φ := φ) χ =
      (character_stabilizer_subgroup (φ := φ) χ).subtype.comp
        (character_stabilizer_subgroup_equiv (φ := φ) χ).toMonoidHom := by
  ext x <;> rfl

/-- Helper for Exercise 8-8.5-3: after identifying the packet source with the explicit subgroup,
the twisting representation is just precomposition along that subgroup equivalence. -/
private noncomputable def character_twist_subgroup_representation
    (χ : A →* ℂˣ) (τ : Rep ℂ H_[φ; χ]) :
    Representation ℂ (character_stabilizer_subgroup (φ := φ) χ) τ.V :=
  (character_twist_representation (φ := φ) χ τ).comp
    (character_stabilizer_subgroup_equiv (φ := φ) χ).symm.toMonoidHom

/-- Helper for Exercise 8-8.5-3: transporting the subgroup-side twisting representation back
along the canonical equivalence recovers the original source-side twisting representation. -/
@[simp] private theorem character_twist_subgroup_representation_comp_equiv
    (χ : A →* ℂˣ) (τ : Rep ℂ H_[φ; χ]) :
    (character_twist_subgroup_representation (φ := φ) χ τ).comp
        (character_stabilizer_subgroup_equiv (φ := φ) χ).toMonoidHom =
      character_twist_representation (φ := φ) χ τ := by
  ext x
  rfl

/-- Helper for Exercise 8-8.5-3: rewriting the packet source as an explicit subgroup turns
`θ[φ; χ, τ]` into induction from the subgroup-side twisting representation. -/
private theorem ind_ker_comp_equiv_eq
    {G K L : Type} [Group G] [Group K] [Group L]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (e : G ≃* K) (f : K →* L) (ρ : Representation ℂ K W) :
    Representation.Coinvariants.ker
        (Representation.tprod ((leftRegular ℂ L).comp (f.comp e.toMonoidHom))
          (ρ.comp e.toMonoidHom)) =
      Representation.Coinvariants.ker
        (Representation.tprod ((leftRegular ℂ L).comp f) ρ) := by
  -- Reindexing the source group by an equivalence does not change the span of coinvariant
  -- relations: it only renames the same family of generators.
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

/-- Helper for Exercise 8-8.5-3: induction along a source-group equivalence is just quotienting by
the same coinvariant relations after reindexing the source action. -/
private noncomputable def ind_equiv_of_comp_equiv
    {G K L : Type} [Group G] [Group K] [Group L]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (e : G ≃* K) (f : K →* L) (ρ : Representation ℂ K W) :
    (Representation.ind (f.comp e.toMonoidHom) (ρ.comp e.toMonoidHom)).Equiv
      (Representation.ind f ρ) := by
  refine Representation.Equiv.mk
      (Submodule.quotEquivOfEq _ _ (ind_ker_comp_equiv_eq e f ρ)) ?_
  intro l
  -- The quotient equivalence acts identically on induced generators, so the target `L`-action
  -- commutes with it on the standard basis `IndV.mk`.
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

/-- Helper for Exercise 8-8.5-3: rewriting the packet source as an explicit subgroup turns
`θ[φ; χ, τ]` into induction from the subgroup-side twisting representation. -/
private noncomputable def ind_equiv_of_source_equiv
    {G K : Type} [Group G] [Group K]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (f : G →* K) {ρ : Representation ℂ G W} {σ : Representation ℂ G W'}
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

/-- Helper for Exercise 8-8.5-3: rewriting the packet source as an explicit subgroup turns
`θ[φ; χ, τ]` into induction from the subgroup-side twisting representation. -/
private noncomputable def theta_equiv_ind_character_stabilizer_subgroup
    (χ : A →* ℂˣ) (τ : Rep ℂ H_[φ; χ]) :
    (θ[φ; χ, τ]).ρ.Equiv
      (Rep.ind (character_stabilizer_subgroup (φ := φ) χ).subtype
        (Rep.of (character_twist_subgroup_representation (φ := φ) χ τ))).ρ :=
  by
  -- Route correction: instead of reasoning about the private source of `theta` abstractly,
  -- rewrite it as induction from the explicit subgroup sitting inside `A ⋊[φ] H`.
  -- The source-group equivalence only reindexes the coinvariant relations, so the induced packet
  -- is the same induced representation after transporting both the inclusion and source action.
  simpa [Representation.theta, character_stabilizer_inclusion_eq_subgroup_subtype_comp] using
    (ind_equiv_of_comp_equiv
      (character_stabilizer_subgroup_equiv (φ := φ) χ)
      (character_stabilizer_subgroup (φ := φ) χ).subtype
      (character_twist_subgroup_representation (φ := φ) χ τ))

/-- Helper for Exercise 8-8.5-3: the subgroup-side twisting representation should inherit
monomiality from the stabilizer representation `τ`. -/
private noncomputable def character_stabilizer_projection
    (χ : A →* ℂˣ) :
    character_stabilizer_subgroup (φ := φ) χ →* H_[φ; χ] where
  toFun := fun x ↦ ⟨x.1.right, x.2⟩
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- Helper for Exercise 8-8.5-3: the second-coordinate projection from the explicit packet
subgroup onto the stabilizer is surjective. -/
private theorem character_stabilizer_projection_surjective
    (χ : A →* ℂˣ) :
    Function.Surjective (character_stabilizer_projection (φ := φ) χ) := by
  intro h
  refine ⟨⟨⟨1, h⟩, h.property⟩, ?_⟩
  ext <;> rfl

/-- Helper for Exercise 8-8.5-3: a surjective homomorphism identifies left cosets of a comap
subgroup with left cosets of the original subgroup. -/
private noncomputable def comap_leftCosetEquiv_of_surjective
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
    have hone : (1 : K) ∈ L := by
      simp
    simpa [hs (f a)] using hone
  · intro x
    refine Quotient.inductionOn' x ?_
    intro y
    change ((f (s y) : K) : K ⧸ L) = (y : K ⧸ L)
    simp [hs]

/-- Helper for Exercise 8-8.5-3: pulling a subgroup witness back along a group homomorphism keeps
the same underlying vector subspace. -/
private noncomputable def comap_subrepresentation
    {G K : Type*} [Group G] [Group K]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : G →* K) (σ : Representation ℂ K W)
    (L : Subgroup K) (U : Subrepresentation (σ.comp L.subtype)) :
    Subrepresentation ((σ.comp f).comp (L.comap f).subtype) where
  toSubmodule := U.toSubmodule
  apply_mem_toSubmodule := by
    intro g x hx
    let fL : L.comap f →* L :=
      ((f.comp (L.comap f).subtype).codRestrict L fun y ↦ y.2)
    -- The pulled-back action factors through the corresponding element of `L`.
    simpa [fL] using U.apply_mem_toSubmodule (fL g) hx

/-- Helper for Exercise 8-8.5-3: pulling a subgroup witness back along a group homomorphism does
not change its complex dimension. -/
@[simp] private theorem comap_subrepresentation_finrank
    {G K : Type*} [Group G] [Group K]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : G →* K) (σ : Representation ℂ K W)
    (L : Subgroup K) (U : Subrepresentation (σ.comp L.subtype)) :
    Module.finrank ℂ (comap_subrepresentation f σ L U).toSubmodule =
      Module.finrank ℂ U.toSubmodule :=
  rfl

/-- Helper for Exercise 8-8.5-3: after reindexing cosets by a surjective map, the pulled-back
left-quotient summands are exactly the original ones. -/
private theorem leftQuotientSubmodule_comap_eq
    {G K : Type*} [Group G] [Group K]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : G →* K) (hf : Function.Surjective f) (σ : Representation ℂ K W)
    (L : Subgroup K) (U : Subrepresentation (σ.comp L.subtype))
    (q : G ⧸ L.comap f) :
    (Representation.leftQuotientSubmodule (σ.comp f)
        (L.comap f) (comap_subrepresentation f σ L U) q) =
      Representation.leftQuotientSubmodule σ L U
        (comap_leftCosetEquiv_of_surjective f hf L q) := by
  refine Quotient.inductionOn' q ?_
  intro g
  -- Both summands are the image of `U` under the same operator `σ (f g)`.
  rw [Representation.leftQuotientSubmodule_mk]
  change Submodule.map ((σ.comp f) g) (comap_subrepresentation f σ L U).toSubmodule =
    Submodule.map (σ (f g)) U.toSubmodule
  rfl

/-- Helper for Exercise 8-8.5-3: inducedness pulls back along a surjective homomorphism by
reindexing the left-coset family. -/
private theorem isInducedFromSubrepresentation_comp_of_surjective
    {G K : Type*} [Group G] [Group K]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : G →* K) (hf : Function.Surjective f) (σ : Representation ℂ K W)
    (L : Subgroup K) (U : Subrepresentation (σ.comp L.subtype))
    (hUinduced : σ.IsInducedFromSubrepresentation L U) :
    Representation.IsInducedFromSubrepresentation (σ.comp f)
      (L.comap f) (comap_subrepresentation f σ L U) := by
  classical
  let ρG : Representation ℂ G W := σ.comp f
  let e := comap_leftCosetEquiv_of_surjective f hf L
  let _ : DecidableEq (G ⧸ L.comap f) := Classical.decEq _
  let _ : DecidableEq (K ⧸ L) := Classical.decEq _
  have hinternal : DirectSum.IsInternal (σ.leftQuotientSubmodule L U) := by
    -- Unpack the induced witness once so the proof becomes a pure reindexing argument.
    simpa [Representation.IsInducedFromSubrepresentation] using hUinduced
  have hleft_fun :
      ρG.leftQuotientSubmodule (L.comap f) (comap_subrepresentation f σ L U) =
        σ.leftQuotientSubmodule L U ∘ e := by
    funext q
    simpa [ρG, e, Function.comp] using
      leftQuotientSubmodule_comap_eq f hf σ L U q
  have hindep :
      iSupIndep (ρG.leftQuotientSubmodule (L.comap f) (comap_subrepresentation f σ L U)) := by
    rw [hleft_fun]
    exact hinternal.submodule_iSupIndep.comp e.injective
  have hspan :
      iSup (ρG.leftQuotientSubmodule (L.comap f) (comap_subrepresentation f σ L U)) = ⊤ := by
    calc
      iSup (ρG.leftQuotientSubmodule (L.comap f) (comap_subrepresentation f σ L U)) =
          iSup (σ.leftQuotientSubmodule L U ∘ e) := by
            rw [hleft_fun]
      _ = iSup (σ.leftQuotientSubmodule L U) := by
            simpa [Function.comp] using
              (Equiv.iSup_comp (g := σ.leftQuotientSubmodule L U) e)
      _ = ⊤ := hinternal.submodule_iSup_eq_top
  -- Package the transported independence and spanning statements back into Chapter 3 owner data.
  unfold Representation.IsInducedFromSubrepresentation
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep hspan

/-- Helper for Exercise 8-8.5-3: monomiality also pulls back along a surjective homomorphism,
because the subgroup witness and its dimension are unchanged on the underlying vector space. -/
private theorem isMonomial_comp_of_surjective
    {G K : Type*} [Group G] [Group K]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (f : G →* K) (hf : Function.Surjective f) (σ : Representation ℂ K W) :
    σ.IsMonomial →
      Representation.IsMonomial (σ.comp f) := by
  intro hσ
  rcases hσ with ⟨L, U, hUdim, hUinduced⟩
  let U' : Subrepresentation ((σ.comp f).comp (L.comap f).subtype) :=
    comap_subrepresentation f σ L U
  refine ⟨L.comap f, U', ?_, ?_⟩
  · -- Pulling back the witness does not change its carrier, hence not its finrank.
    calc
      Module.finrank ℂ U'.toSubmodule = Module.finrank ℂ U.toSubmodule := by
        simpa [U'] using comap_subrepresentation_finrank f σ L U
      _ = 1 := hUdim
  · -- The Chapter 3 owner statement is exactly the surjective reindexing lemma above.
    simpa [U'] using
      isInducedFromSubrepresentation_comp_of_surjective f hf σ L U hUinduced

/-- Helper for Exercise 8-8.5-3: multiplying a linear map by a nonzero scalar does not change the
image of a submodule. -/
private theorem submodule_map_smul_eq
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (U : Submodule ℂ W) (T : W →ₗ[ℂ] W)
    (c : ℂ) (hc : c ≠ 0) :
    Submodule.map (c • T) U = Submodule.map T U := by
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨c • u, U.smul_mem c hu, ?_⟩
    simp [LinearMap.smul_apply]
  · intro hx
    rcases Submodule.mem_map.mp hx with ⟨u, hu, rfl⟩
    refine Submodule.mem_map.mpr ⟨c⁻¹ • u, U.smul_mem c⁻¹ hu, ?_⟩
    calc
      (c • T) (c⁻¹ • u) = c • T (c⁻¹ • u) := rfl
      _ = c • (c⁻¹ • T u) := by simp
      _ = (c * c⁻¹) • T u := by simp [smul_smul]
      _ = (1 : ℂ) • T u := by simp [hc]
      _ = T u := by simp

/-- Helper for Exercise 8-8.5-3: the subgroup-side twist acts by the stabilizer representation,
up to a scalar coming from the `A`-coordinate. -/
private theorem character_twist_subgroup_representation_apply
    (χ : A →* ℂˣ) (τ : Rep ℂ H_[φ; χ])
    (g : character_stabilizer_subgroup (φ := φ) χ) :
    character_twist_subgroup_representation (φ := φ) χ τ g =
      (χ g.1.left : ℂ) • τ.ρ (character_stabilizer_projection (φ := φ) χ g) := by
  change
    (character_stabilizer_character (φ := φ) χ
        ((character_stabilizer_subgroup_equiv (φ := φ) χ).symm g) : ℂ) •
      τ.ρ (((character_stabilizer_subgroup_equiv (φ := φ) χ).symm g).right) =
      (χ g.1.left : ℂ) • τ.ρ (character_stabilizer_projection (φ := φ) χ g)
  rw [character_stabilizer_character_apply]
  rfl

/-- Helper for Exercise 8-8.5-3: the twist uses the same underlying witness subspace after
pulling the stabilizer witness back along the second-coordinate projection. -/
private noncomputable def character_twist_comap_subrepresentation
    (χ : A →* ℂˣ) (τ : Rep ℂ H_[φ; χ])
    (K : Subgroup H_[φ; χ]) (U : Subrepresentation (τ.ρ.comp K.subtype)) :
    Subrepresentation
      ((character_twist_subgroup_representation (φ := φ) χ τ).comp
        (K.comap (character_stabilizer_projection (φ := φ) χ)).subtype) where
  toSubmodule := U.toSubmodule
  apply_mem_toSubmodule := by
    intro g x hx
    let πK : K.comap (character_stabilizer_projection (φ := φ) χ) →* K :=
      (((character_stabilizer_projection (φ := φ) χ).comp
        (K.comap (character_stabilizer_projection (φ := φ) χ)).subtype).codRestrict K
        fun y ↦ y.2)
    have hmem : τ.ρ (πK g) x ∈ U.toSubmodule := by
      simpa [πK] using U.apply_mem_toSubmodule (πK g) hx
    -- The extra `A`-factor acts by a scalar, so the same carrier stays stable.
    simpa [character_twist_subgroup_representation_apply, πK] using
      U.toSubmodule.smul_mem (χ g.1.1.left : ℂ) hmem

/-- Helper for Exercise 8-8.5-3: the twist does not change any left-coset summand, because it
only rescales the translated witness by a nonzero scalar. -/
private theorem leftQuotientSubmodule_character_twist_eq
    (χ : A →* ℂˣ) (τ : Rep ℂ H_[φ; χ])
    (K : Subgroup H_[φ; χ]) (U : Subrepresentation (τ.ρ.comp K.subtype))
    (q : character_stabilizer_subgroup (φ := φ) χ ⧸
        K.comap (character_stabilizer_projection (φ := φ) χ)) :
    (character_twist_subgroup_representation (φ := φ) χ τ).leftQuotientSubmodule
        (K.comap (character_stabilizer_projection (φ := φ) χ))
        (character_twist_comap_subrepresentation (φ := φ) χ τ K U) q =
      ((show Representation ℂ (character_stabilizer_subgroup (φ := φ) χ) τ.V from
          τ.ρ.comp (character_stabilizer_projection (φ := φ) χ)).leftQuotientSubmodule
        (K.comap (character_stabilizer_projection (φ := φ) χ))
        (comap_subrepresentation
          (character_stabilizer_projection (φ := φ) χ) τ.ρ K U) q) := by
  refine Quotient.inductionOn' q ?_
  intro g
  rw [Representation.leftQuotientSubmodule_mk, Representation.leftQuotientSubmodule_mk]
  have hχ_ne : (χ g.1.left : ℂ) ≠ 0 := Units.ne_zero (χ g.1.left)
  -- Route correction: compare the two translated summands at the submodule-image level instead of
  -- trying to package the scalar twist into a new quotient-family owner.
  simpa [character_twist_comap_subrepresentation, comap_subrepresentation,
    character_twist_subgroup_representation_apply, character_stabilizer_projection] using
    submodule_map_smul_eq U.toSubmodule
      (τ.ρ (character_stabilizer_projection (φ := φ) χ g))
      (χ g.1.left : ℂ) hχ_ne

/-- Helper for Exercise 8-8.5-3: if two restricted representations have the same left-coset
family, then inducedness for one of them transfers to the other. -/
private theorem isInducedFromSubrepresentation_of_leftQuotientSubmodule_eq
    {G : Type*} [Group G]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ σ : Representation ℂ G W}
    (L : Subgroup G)
    (U : Subrepresentation (ρ.comp L.subtype))
    (U' : Subrepresentation (σ.comp L.subtype))
    (hfamily : ρ.leftQuotientSubmodule L U = σ.leftQuotientSubmodule L U')
    (hUinduced : ρ.IsInducedFromSubrepresentation L U) :
    σ.IsInducedFromSubrepresentation L U' := by
  classical
  -- After rewriting the quotient-indexed family, the owner statement is literally unchanged.
  unfold Representation.IsInducedFromSubrepresentation at hUinduced ⊢
  simpa [hfamily] using hUinduced

/-- Helper for Exercise 8-8.5-3: after pulling the monomial witness for `τ` back along the
second-coordinate projection, the twist is still induced from the same carrier. -/
private theorem character_twist_subgroup_representation_isInducedFrom_lifted_subgroup
    (χ : A →* ℂˣ) (τ : Rep ℂ H_[φ; χ])
    (K : Subgroup H_[φ; χ]) (U : Subrepresentation (τ.ρ.comp K.subtype))
    (hUinduced : τ.ρ.IsInducedFromSubrepresentation K U) :
    (character_twist_subgroup_representation (φ := φ) χ τ).IsInducedFromSubrepresentation
      (K.comap (character_stabilizer_projection (φ := φ) χ))
      (character_twist_comap_subrepresentation (φ := φ) χ τ K U) := by
  let πχ := character_stabilizer_projection (φ := φ) χ
  let τχ : Representation ℂ (character_stabilizer_subgroup (φ := φ) χ) τ.V := τ.ρ.comp πχ
  let Upull :
      Subrepresentation
        (((show Representation ℂ (character_stabilizer_subgroup (φ := φ) χ) τ.V from
            τ.ρ.comp πχ).comp (K.comap πχ).subtype)) :=
    show Subrepresentation
        (((show Representation ℂ (character_stabilizer_subgroup (φ := φ) χ) τ.V from
            τ.ρ.comp πχ).comp (K.comap πχ).subtype)) from
      comap_subrepresentation πχ τ.ρ K U
  have hpull :
      τχ.IsInducedFromSubrepresentation (K.comap πχ) Upull := by
    -- First pull the Chapter 3 witness back along the surjective stabilizer projection.
    simpa [τχ, Upull] using
      isInducedFromSubrepresentation_comp_of_surjective πχ
        (character_stabilizer_projection_surjective (φ := φ) χ) τ.ρ K U hUinduced
  have hfamily :
      (τχ.leftQuotientSubmodule (K.comap πχ) Upull) =
      (character_twist_subgroup_representation (φ := φ) χ τ).leftQuotientSubmodule
        (K.comap πχ) (character_twist_comap_subrepresentation (φ := φ) χ τ K U) := by
    funext q
    symm
    simpa [πχ, τχ, Upull] using leftQuotientSubmodule_character_twist_eq (φ := φ) χ τ K U q
  -- The twist family is literally the pulled-back family after identifying the scalar images.
  exact isInducedFromSubrepresentation_of_leftQuotientSubmodule_eq
    (L := K.comap πχ) (U := Upull)
    (U' := character_twist_comap_subrepresentation (φ := φ) χ τ K U)
    hfamily hpull

/-- Helper for Exercise 8-8.5-3: the subgroup-side twisting representation should inherit
monomiality from the stabilizer representation `τ`. -/
lemma character_twist_subgroup_representation_isMonomial_of_isMonomial
    (χ : A →* ℂˣ) (τ : Rep ℂ H_[φ; χ]) [τ.ρ.IsIrreducible] :
    τ.ρ.IsMonomial →
      (character_twist_subgroup_representation (φ := φ) χ τ).IsMonomial := by
  intro hτmonomial
  rcases hτmonomial with ⟨K, U, hUdim, hUinduced⟩
  let πχ := character_stabilizer_projection (φ := φ) χ
  let Uχ :
      Subrepresentation
        ((character_twist_subgroup_representation (φ := φ) χ τ).comp (K.comap πχ).subtype) :=
    character_twist_comap_subrepresentation (φ := φ) χ τ K U
  -- The twist keeps the same one-dimensional carrier and only changes the ambient action by
  -- nonzero scalars on the quotient summands.
  refine ⟨K.comap πχ, Uχ, ?_, ?_⟩
  · simpa [Uχ] using hUdim
  · simpa [πχ, Uχ] using
      character_twist_subgroup_representation_isInducedFrom_lifted_subgroup
        (φ := φ) χ τ K U hUinduced

/-- Helper for Exercise 8-8.5-3: projection from `Ind_S^G(σ)` back to the unit-coset copy of the
source representation `σ`. -/
private noncomputable def induced_identity_copy_projection
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup G) (σ : Representation ℂ S W) :
    Representation.IndV S.subtype σ →ₗ[ℂ] W :=
  Representation.Coinvariants.lift _
    (TensorProduct.lift <|
      Finsupp.lift _ _ _ fun g ↦
        @dite _ (g ∈ S) ((Classical.decPred fun x : G ↦ x ∈ S) g)
          (fun hg ↦ σ ⟨g, hg⟩⁻¹)
          (fun _ ↦ 0))
    (fun s ↦ by
      -- Check the coinvariant relation on generators `δ_g ⊗ w`.
      ext g w
      by_cases hg : g ∈ S
      · have hsg : ((s : G) * g) ∈ S := S.mul_mem s.property hg
        have hmul : σ ⟨(s : G) * g, hsg⟩⁻¹ (σ s w) = σ ⟨g, hg⟩⁻¹ w := by
          have hsub : ((⟨(s : G) * g, hsg⟩⁻¹ : S) * s) = ⟨g, hg⟩⁻¹ := by
            ext
            simp [mul_assoc]
          calc
            σ ⟨(s : G) * g, hsg⟩⁻¹ (σ s w)
              = σ (((⟨(s : G) * g, hsg⟩⁻¹ : S) * s)) w := by
                  simp [Module.End.mul_apply, map_mul]
            _ = σ ⟨g, hg⟩⁻¹ w := by
                  rw [hsub]
        simpa [TensorProduct.lift.tmul, hg, hsg] using hmul
      · have hsng : ((s : G) * g) ∉ S := by
          intro hmem
          have htmp : ((s : G)⁻¹ * ((s : G) * g)) ∈ S :=
            S.mul_mem (S.inv_mem s.property) hmem
          have hg' : g ∈ S := by
            simpa [mul_assoc] using htmp
          exact hg hg'
        simp [TensorProduct.lift.tmul, hg, hsng])

/-- Helper for Exercise 8-8.5-3: the projection recovers the original vector on the unit-coset
generator of `Ind_S^G(σ)`. -/
private theorem induced_identity_copy_projection_apply_mk_one
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup G) (σ : Representation ℂ S W) (w : W) :
    induced_identity_copy_projection S σ (Representation.IndV.mk S.subtype σ 1 w) = w := by
  classical
  have hone : (1 : G) ∈ S := S.one_mem
  have hbase : σ ⟨1, hone⟩⁻¹ w = w := by
    have hsub : ((⟨1, hone⟩ : S)⁻¹) = 1 := by
      ext
      simp
    rw [hsub]
    exact LinearMap.congr_fun σ.map_one w
  -- Evaluating the quotient lift at the unit basis vector reduces to the identity on `W`.
  simpa [induced_identity_copy_projection, TensorProduct.lift.tmul, hone] using hbase

/-- Helper for Exercise 8-8.5-3: the unit-coset generator is injective, so its range is a faithful
copy of the source representation `σ`. -/
private theorem induced_identity_copy_mk_one_injective
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup G) (σ : Representation ℂ S W) :
    Function.Injective (Representation.IndV.mk S.subtype σ 1) := by
  intro x y hxy
  have hproj := congrArg (induced_identity_copy_projection S σ) hxy
  calc
    x = induced_identity_copy_projection S σ (Representation.IndV.mk S.subtype σ 1 x) := by
          symm
          exact induced_identity_copy_projection_apply_mk_one S σ x
    _ = induced_identity_copy_projection S σ (Representation.IndV.mk S.subtype σ 1 y) := hproj
    _ = y := induced_identity_copy_projection_apply_mk_one S σ y

/-- Helper for Exercise 8-8.5-3: the range of the unit-coset generator is stable under the
restricted `S`-action on `Ind_S^G(σ)`. -/
private theorem induced_identity_copy_apply_mem
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup G) (σ : Representation ℂ S W) (s : S)
    {x : Representation.IndV S.subtype σ}
    (hx : x ∈ LinearMap.range (Representation.IndV.mk S.subtype σ 1)) :
    ((Rep.ind S.subtype (Rep.of σ)).ρ.comp S.subtype) s x ∈
      LinearMap.range (Representation.IndV.mk S.subtype σ 1) := by
  rcases hx with ⟨w, rfl⟩
  -- Acting on the unit-coset copy just applies `σ s` to the source vector.
  refine ⟨σ s w, ?_⟩
  simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]

/-- Helper for Exercise 8-8.5-3: the unit-coset copy of `σ` inside `Ind_S^G(σ)`. -/
private noncomputable def induced_identity_copy_subrepresentation
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup G) (σ : Representation ℂ S W) :
    Subrepresentation ((Rep.ind S.subtype (Rep.of σ)).ρ.comp S.subtype) :=
  { toSubmodule := LinearMap.range (Representation.IndV.mk S.subtype σ 1)
    apply_mem_toSubmodule := induced_identity_copy_apply_mem S σ }

/-- Helper for Exercise 8-8.5-3: the source representation `σ` is equivariantly equivalent to its
unit-coset copy inside `Ind_S^G(σ)`. -/
private noncomputable def induced_identity_copy_equiv
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup G) (σ : Representation ℂ S W) :
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

/-- Helper for Exercise 8-8.5-3: precomposing with a representation equivalence identifies
intertwining spaces with the same codomain. -/
private noncomputable def intertwiningMapCongrLeft
    {G : Type} [Group G]
    {W W' U : Type}
    [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W']
    [AddCommGroup U] [Module ℂ U]
    {ρ : Representation ℂ G W} {σ : Representation ℂ G W'}
    (e : ρ.Equiv σ) (τ : Representation ℂ G U) :
    σ.IntertwiningMap τ ≃ₗ[ℂ] ρ.IntertwiningMap τ :=
  { toFun := fun f ↦ f.comp e.toIntertwiningMap
    invFun := fun f ↦ f.comp e.symm.toIntertwiningMap
    left_inv := by
      intro f
      ext x
      simp
    right_inv := by
      intro f
      ext x
      simp
    map_add' := by
      intro f g
      rfl
    map_smul' := by
      intro a f
      rfl }

/-- Helper for Exercise 8-8.5-3: induction along a subgroup chain is equivalent to direct
induction from the composite inclusion. -/
private noncomputable def ind_subgroup_chain_equiv
    {G : Type} [Group G]
    (S : Subgroup G) (K : Subgroup S)
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) :
    ((Rep.ind S.subtype (Rep.ind K.subtype (Rep.of ρ))).ρ).Equiv
      ((Rep.ind (S.subtype.comp K.subtype) (Rep.of ρ)).ρ) :=
  Representation.equivOfIso
    ((((indResAdjunction ℂ K.subtype).leftAdjointCompIso
          (indResAdjunction ℂ S.subtype)
          (indResAdjunction ℂ (S.subtype.comp K.subtype))
          (eqToIso rfl)).app (Rep.of ρ)))

/-- Helper for Exercise 8-8.5-3: every vector in the unit-coset copy is the unit-coset
generator attached to its preimage under the explicit equivalence with `σ`. -/
private theorem induced_identity_copy_eq_mk_one_symm
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup G) (σ : Representation ℂ S W)
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

/-- Helper for Exercise 8-8.5-3: restricting a `G`-intertwiner to a stable subrepresentation
produces an intertwiner for the subgroup action. -/
private theorem restrictIntertwiningMapLocal_isIntertwining
    {G : Type} [Group G]
    {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (S : Subgroup G)
    (W : Subrepresentation (ρ.comp S.subtype))
    (ρ' : Representation ℂ G V') (F : ρ.IntertwiningMap ρ') :
    ∀ s : S, ∀ w : W.toSubmodule,
      (F.toLinearMap.comp W.toSubmodule.subtype) (W.toRepresentation s w) =
        (ρ'.comp S.subtype) s ((F.toLinearMap.comp W.toSubmodule.subtype) w) := by
  intro s w
  simpa using congr($(F.isIntertwining' s) w)

/-- Helper for Exercise 8-8.5-3: the restriction operator on intertwining maps is linear. -/
private def restrictIntertwiningMapLocal
    {G : Type} [Group G]
    {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (S : Subgroup G)
    (W : Subrepresentation (ρ.comp S.subtype))
    (ρ' : Representation ℂ G V') :
    ρ.IntertwiningMap ρ' →ₗ[ℂ] W.toRepresentation.IntertwiningMap (ρ'.comp S.subtype) :=
  { toFun := fun F ↦
      (F.toLinearMap.comp W.toSubmodule.subtype).intertwiningMap_of_isIntertwiningMap
        W.toRepresentation (ρ'.comp S.subtype)
        (restrictIntertwiningMapLocal_isIntertwining ρ S W ρ' F)
    map_add' := by
      intro F F'
      ext w
      rfl
    map_smul' := by
      intro a F
      ext w
      rfl }

/-- Helper for Exercise 8-8.5-3: restricting and then evaluating at a vector of the stable
subrepresentation is just ordinary application of the ambient intertwiner. -/
@[simp] private theorem restrictIntertwiningMapLocal_apply
    {G : Type} [Group G]
    {V V' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ G V) (S : Subgroup G)
    (W : Subrepresentation (ρ.comp S.subtype))
    (ρ' : Representation ℂ G V') (F : ρ.IntertwiningMap ρ') (w : W.toSubmodule) :
    restrictIntertwiningMapLocal ρ S W ρ' F w = F w := by
  rfl

/-- Helper for Exercise 8-8.5-3: after transporting the unit-coset copy back to `σ`,
restriction of intertwiners is exactly Frobenius reciprocity, hence bijective. -/
private theorem induced_identity_copy_restrictIntertwiningMap_bijective_local
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup G) (σ : Representation ℂ S W) (ρ' : Rep ℂ G) :
    Function.Bijective
      (restrictIntertwiningMapLocal ((Rep.ind S.subtype (Rep.of σ)).ρ) S
        (induced_identity_copy_subrepresentation S σ) ρ'.ρ) := by
  let e :
      ((induced_identity_copy_subrepresentation S σ).toRepresentation.IntertwiningMap
          (ρ'.ρ.comp S.subtype)) ≃ₗ[ℂ]
        σ.IntertwiningMap (ρ'.ρ.comp S.subtype) :=
    intertwiningMapCongrLeft
      (ρ := σ)
      (σ := (induced_identity_copy_subrepresentation S σ).toRepresentation)
      (e := induced_identity_copy_equiv S σ)
      (τ := ρ'.ρ.comp S.subtype)
  let L :
      ((Rep.ind S.subtype (Rep.of σ)).ρ).IntertwiningMap ρ'.ρ →
        σ.IntertwiningMap (ρ'.ρ.comp S.subtype) :=
    fun F ↦
      (F.toLinearMap.comp
        (Representation.IndV.mk S.subtype σ 1)).intertwiningMap_of_isIntertwiningMap
        σ (ρ'.ρ.comp S.subtype) fun s x ↦ by
          have hcomm :
              F.toLinearMap (((Rep.ind S.subtype (Rep.of σ)).ρ.comp S.subtype) s
                  (Representation.IndV.mk S.subtype σ 1 x)) =
                (ρ'.ρ.comp S.subtype) s
                  (F.toLinearMap (Representation.IndV.mk S.subtype σ 1 x)) := by
            simpa using congr($(F.isIntertwining' s) (Representation.IndV.mk S.subtype σ 1 x))
          simpa [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul] using hcomm
  have hrestrict :
      ∀ F : ((Rep.ind S.subtype (Rep.of σ)).ρ).IntertwiningMap ρ'.ρ,
        e (restrictIntertwiningMapLocal ((Rep.ind S.subtype (Rep.of σ)).ρ) S
          (induced_identity_copy_subrepresentation S σ) ρ'.ρ F) = L F := by
    intro F
    -- Transporting along `induced_identity_copy_equiv` rewrites restriction to evaluation on
    -- `IndV.mk ... 1`.
    ext w
    rfl
  let extend :
      σ.IntertwiningMap (ρ'.ρ.comp S.subtype) →
        ((Rep.ind S.subtype (Rep.of σ)).ρ).IntertwiningMap ρ'.ρ :=
    fun f ↦
      { toLinearMap := Representation.Coinvariants.lift _
          (TensorProduct.lift <| Finsupp.lift _ _ _ fun g ↦ ρ'.ρ g⁻¹ ∘ₗ f.toLinearMap)
          fun g ↦ by
            -- The explicit extension respects the coinvariant relation by intertwining on `S`.
            simp only [Representation.tprod_apply, MonoidHom.coe_comp, Function.comp_apply,
              TensorProduct.lift_comp_map]
            congr 1
            ext
            simp [Representation.IntertwiningMap.isIntertwining]
        isIntertwining' := fun g ↦ by
          -- The extension intertwines the ambient action because the induced action only shifts
          -- the left-regular basis index.
          ext
          simp }
  have hleft : Function.LeftInverse extend L := by
    intro F
    -- Equality on the induced representation is checked on the standard generators `IndV.mk`.
    ext g a
    have hcomm :=
      congr($(F.isIntertwining' g⁻¹) (Representation.IndV.mk S.subtype σ 1 a))
    simpa [L, extend, Representation.IndV.mk] using hcomm.symm
  have hright : Function.RightInverse extend L := by
    intro f
    -- Evaluating the explicit extension at the unit generator recovers the original intertwiner.
    ext a
    simp [L, extend]
  have hL : Function.Bijective L := ⟨hleft.injective, hright.surjective⟩
  constructor
  · intro F F' hFF'
    apply hL.1
    simpa [hrestrict F, hrestrict F'] using congrArg e hFF'
  · intro f
    obtain ⟨F, hF⟩ := hL.2 (e f)
    refine ⟨F, ?_⟩
    apply e.injective
    simpa [hrestrict F] using hF

/-- Helper for Exercise 8-8.5-3: `Ind_S^G(σ)` is induced from its unit-coset copy. -/
private theorem induced_identity_copy_is_induced_local
    {G : Type} [Group G] [Finite G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup G) (σ : Representation ℂ S W) :
    ((Rep.ind S.subtype (Rep.of σ)).ρ).IsInducedFromSubrepresentation
      S (induced_identity_copy_subrepresentation S σ) :=
  by
  classical
  let C : Rep ℂ G := Rep.coind S.subtype (Rep.of σ)
  let e :
      ((Rep.ind S.subtype (Rep.of σ)).ρ).Equiv C.ρ :=
    Representation.equivOfIso (Rep.indCoindIso (Rep.of σ))
  let W₀ :
      Subrepresentation (C.ρ.comp S.subtype) :=
    Representation.supportedOnSubgroupSubrepresentation S σ
  have hW₀ :
      C.ρ.IsInducedFromSubrepresentation S W₀ := by
    -- The current import closure already packages the coinduced model as induced from the
    -- subgroup-supported copy `W₀`.
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
      let fy : G → W := (y : C)
      have hySupportSubgroup :
          Function.support fy ⊆ (S : Set G) := by
        simpa [C, W₀] using
          (Representation.mem_supportedOnSubgroupSubrepresentation_iff S σ y).mp hy
      have hySupportOrbit :
          Function.support fy ⊆ MulAction.orbit S (1 : G) := by
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
          (Rep.coindToInd_of_support_subset_orbit (A := Rep.of σ) (g := (1 : G))
            y hySupportOrbit)
      exact LinearMap.mem_range.mpr
        ⟨fy 1, hyImage.symm⟩
    · intro hx
      rcases LinearMap.mem_range.mp hx with ⟨w, rfl⟩
      let fw : W₀.toSubmodule :=
        ⟨Representation.subgroupSupportedFunction S σ w,
          Representation.subgroupSupportedFunction_mem_supportedOnSubgroupSubrepresentation S σ w⟩
      let ffw : G → W := (((fw : W₀.toSubmodule) : C) : G → W)
      have hfwSupportSubgroup :
          Function.support ffw ⊆ (S : Set G) := by
        simpa [C, W₀] using
          (Representation.mem_supportedOnSubgroupSubrepresentation_iff S σ
            ((fw : W₀.toSubmodule) : C)).mp fw.property
      have hfwSupportOrbit :
          Function.support ffw ⊆ MulAction.orbit S (1 : G) := by
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
            (Rep.coindToInd_of_support_subset_orbit (A := Rep.of σ) (g := (1 : G))
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
  -- Transport the current-owner inducedness statement back across the `Ind ≃ Coind` comparison.
  simpa [htransport] using
    isInducedFromSubrepresentation_of_equiv e.symm S W₀ hW₀

/-- Helper for Exercise 8-8.5-3: the canonical map from the standard induced model attached to a
stable subrepresentation into the ambient representation. -/
private noncomputable abbrev inducedFromSubrepresentationHomLocal
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype)) :
    Rep.ind H.subtype (Rep.of U.toRepresentation) ⟶ Rep.of ρ :=
  (Rep.indResHomEquiv H.subtype (Rep.of U.toRepresentation) (Rep.of ρ)).symm
    ((Rep.res H.subtype (Rep.of ρ)).subtype U.toSubmodule U.apply_mem_toSubmodule)

/-- Helper for Exercise 8-8.5-3: evaluating the canonical induced map on `⟦g ⊗ u⟧` recovers the
ambient action `ρ g⁻¹ u`. -/
@[simp] private theorem inducedFromSubrepresentationHomLocal_mk
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (g : G) (u : U.toSubmodule) :
    (inducedFromSubrepresentationHomLocal ρ H U).hom
        (Representation.IndV.mk H.subtype U.toRepresentation g u) =
      ρ g⁻¹ u := by
  simpa [inducedFromSubrepresentationHomLocal] using
    congrArg (ρ g⁻¹)
      (show ((Rep.res H.subtype (Rep.of ρ)).subtype U.toSubmodule
          U.apply_mem_toSubmodule).hom u = (u : W) from rfl)

/-- Helper for Exercise 8-8.5-3: each coset summand of an induced representation is canonically
identified with the source subrepresentation by translation. -/
@[simp] private theorem left_quotient_submodule_out_local
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (q : G ⧸ H) :
    ρ.leftQuotientSubmodule H U q = U.toSubmodule.map (ρ q.out) := by
  simpa using (ρ.leftQuotientSubmodule_mk H U q.out)

/-- Helper for Exercise 8-8.5-3: each coset summand of an induced representation is canonically
identified with the source subrepresentation by translation. -/
private noncomputable def left_quotient_submodule_equiv_local
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (q : G ⧸ H) :
    U.toSubmodule ≃ₗ[ℂ] ρ.leftQuotientSubmodule H U q :=
  let e : W ≃ₗ[ℂ] W := LinearEquiv.ofBijective (ρ q.out) (ρ.apply_bijective q.out)
  (e.submoduleMap U.toSubmodule).trans
    (LinearEquiv.ofEq _ _ (left_quotient_submodule_out_local ρ H U q).symm)

/-- Helper for Exercise 8-8.5-3: the local coset-translation equivalence acts by `ρ q.out` on
vectors of the source subrepresentation. -/
@[simp] private theorem left_quotient_submodule_equiv_local_apply
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (q : G ⧸ H) (u : U.toSubmodule) :
    ((left_quotient_submodule_equiv_local ρ H U q u :
        ρ.leftQuotientSubmodule H U q) : W) =
      ρ q.out u := by
  simp [left_quotient_submodule_equiv_local]

/-- Helper for Exercise 8-8.5-3: the inverse local coset-translation equivalence acts by
`ρ q.out⁻¹` on vectors in the `q`-summand. -/
@[simp] private theorem left_quotient_submodule_equiv_local_symm_apply
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (q : G ⧸ H) (x : ρ.leftQuotientSubmodule H U q) :
    (((left_quotient_submodule_equiv_local ρ H U q).symm x : U.toSubmodule) : W) =
      ρ q.out⁻¹ x := by
  let e : W ≃ₗ[ℂ] W := LinearEquiv.ofBijective (ρ q.out) (ρ.apply_bijective q.out)
  change (((e.submoduleMap U.toSubmodule).symm
      ((LinearEquiv.ofEq _ _ (left_quotient_submodule_out_local ρ H U q).symm).symm x) :
        U.toSubmodule) :
        W) = ρ q.out⁻¹ x
  apply (ρ.apply_bijective q.out).injective
  simp [e]

/-- Helper for Exercise 8-8.5-3: extend a map defined on the inducing subrepresentation to a
single quotient summand by transporting to the chosen coset representative. -/
private noncomputable def left_quotient_submodule_extension_local
    {G : Type} [Group G]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (ρ' : Representation ℂ G W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp H.subtype))
    (q : G ⧸ H) :
    ρ.leftQuotientSubmodule H U q →ₗ[ℂ] W' :=
  (ρ' q.out).comp
    (f.toLinearMap.comp (left_quotient_submodule_equiv_local ρ H U q).symm.toLinearMap)

/-- Helper for Exercise 8-8.5-3: the internal direct-sum decomposition of the coset translates of
`U` yields a linear extension of an `H`-equivariant map on `U`. -/
private noncomputable def extensionLinearMapLocal
    {G : Type} [Group G]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (hU : ρ.IsInducedFromSubrepresentation H U)
    (ρ' : Representation ℂ G W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp H.subtype)) :
    W →ₗ[ℂ] W' :=
  let _ : DecidableEq (G ⧸ H) := Classical.decEq _
  let hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule H U) := by
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  let _ := DirectSum.IsInternal.chooseDecomposition (ρ.leftQuotientSubmodule H U) hInternal
  (DirectSum.toModule ℂ (G ⧸ H) W'
      (left_quotient_submodule_extension_local ρ H U ρ' f)).comp
    (DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule H U)).toLinearMap

/-- Helper for Exercise 8-8.5-3: on a single quotient summand, the local extension is the
corresponding component extension. -/
private theorem extensionLinearMapLocal_apply_of_mem
    {G : Type} [Group G]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (hU : ρ.IsInducedFromSubrepresentation H U)
    (ρ' : Representation ℂ G W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp H.subtype))
    {x : W} {q : G ⧸ H} (hx : x ∈ ρ.leftQuotientSubmodule H U q) :
    extensionLinearMapLocal ρ H U hU ρ' f x =
      left_quotient_submodule_extension_local ρ H U ρ' f q ⟨x, hx⟩ := by
  classical
  let _ : DecidableEq (G ⧸ H) := Classical.decEq _
  have hInternal : DirectSum.IsInternal (ρ.leftQuotientSubmodule H U) := by
    simpa [Representation.IsInducedFromSubrepresentation] using hU
  let _ := DirectSum.IsInternal.chooseDecomposition (ρ.leftQuotientSubmodule H U) hInternal
  have hxdecomp :
      DirectSum.decomposeLinearEquiv (ρ.leftQuotientSubmodule H U) x =
        DirectSum.lof ℂ (G ⧸ H) (fun i ↦ ρ.leftQuotientSubmodule H U i) q ⟨x, hx⟩ := by
    simpa using
      (DirectSum.decomposeLinearEquiv_apply_coe
        (R := ℂ) (ι := G ⧸ H) (ℳ := ρ.leftQuotientSubmodule H U) q ⟨x, hx⟩)
  rw [extensionLinearMapLocal]
  simpa [LinearMap.comp_apply, DirectSum.toModule_lof] using
    congrArg (DirectSum.toModule ℂ (G ⧸ H) W'
      (left_quotient_submodule_extension_local ρ H U ρ' f)) hxdecomp

/-- Helper for Exercise 8-8.5-3: the local extension agrees with the original intertwiner on the
inducing subrepresentation. -/
private theorem extensionLinearMapLocal_extends
    {G : Type} [Group G]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (hU : ρ.IsInducedFromSubrepresentation H U)
    (ρ' : Representation ℂ G W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp H.subtype))
    (u : U.toSubmodule) :
    extensionLinearMapLocal ρ H U hU ρ' f u = f u := by
  classical
  let q : G ⧸ H := QuotientGroup.mk 1
  have hq_rel : QuotientGroup.leftRel H q.out 1 := by
    exact Quotient.exact' (by simp [q])
  rw [QuotientGroup.leftRel_apply] at hq_rel
  have hq_mem : q.out ∈ H := by
    simpa using H.inv_mem hq_rel
  let h : H := ⟨q.out, hq_mem⟩
  let uinv : U.toSubmodule := ⟨ρ q.out⁻¹ u, U.apply_mem_toSubmodule h⁻¹ u.property⟩
  have huq : (u : W) ∈ ρ.leftQuotientSubmodule H U q := by
    rw [left_quotient_submodule_out_local ρ H U q]
    exact Submodule.mem_map.mpr ⟨uinv, uinv.property, by
      change ρ q.out (ρ q.out⁻¹ u) = u
      simp⟩
  have hsymm :
      (left_quotient_submodule_equiv_local ρ H U q).symm ⟨u, huq⟩ = uinv := by
    ext
    simp [uinv]
  rw [extensionLinearMapLocal_apply_of_mem ρ H U hU ρ' f huq]
  change ρ' q.out (f ((left_quotient_submodule_equiv_local ρ H U q).symm ⟨u, huq⟩)) = f u
  rw [hsymm]
  have huint : f uinv = ρ' q.out⁻¹ (f u) := by
    simpa [h, uinv] using
      (Representation.IntertwiningMap.isIntertwining (f := f) (g := h⁻¹) (v := u))
  rw [huint]
  simp

/-- Helper for Exercise 8-8.5-3: the local extension constructed from the internal sum is
`G`-equivariant. -/
private theorem extensionLinearMapLocal_isIntertwining
    {G : Type} [Group G]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (hU : ρ.IsInducedFromSubrepresentation H U)
    (ρ' : Representation ℂ G W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp H.subtype)) :
    ∀ s : G, ∀ x : W,
      extensionLinearMapLocal ρ H U hU ρ' f (ρ s x) =
        ρ' s (extensionLinearMapLocal ρ H U hU ρ' f x) := by
  classical
  let ℳ : G ⧸ H → Submodule ℂ W := ρ.leftQuotientSubmodule H U
  let _ : DecidableEq (G ⧸ H) := Classical.decEq _
  have hInternal : DirectSum.IsInternal ℳ := by
    simpa [ℳ, Representation.IsInducedFromSubrepresentation] using hU
  let _ := DirectSum.IsInternal.chooseDecomposition ℳ hInternal
  intro s x
  refine DirectSum.Decomposition.inductionOn (ℳ := ℳ)
      (motive := fun x : W ↦
        extensionLinearMapLocal ρ H U hU ρ' f (ρ s x) =
          ρ' s (extensionLinearMapLocal ρ H U hU ρ' f x))
      ?_ ?_ ?_ x
  · simp [extensionLinearMapLocal]
  · intro q x
    let u : U.toSubmodule := (left_quotient_submodule_equiv_local ρ H U q).symm x
    have hx : (x : W) = ρ q.out u := by
      calc
        (x : W) =
            ((left_quotient_submodule_equiv_local ρ H U q u :
                ρ.leftQuotientSubmodule H U q) : W) := by
              exact congrArg
                (fun y : ρ.leftQuotientSubmodule H U q ↦ (y : W))
                ((left_quotient_submodule_equiv_local ρ H U q).apply_symm_apply x).symm
        _ = ρ q.out u := by simp
    have hq : QuotientGroup.leftRel H ((s • q).out) (s * q.out) := by
      apply Quotient.exact'
      calc
        ((s • q).out : G ⧸ H) = s • q := Quotient.out_eq' (s • q)
        _ = s • (q.out : G ⧸ H) := by
          exact congrArg (fun z : G ⧸ H ↦ s • z) (Quotient.out_eq' q).symm
        _ = (s * q.out : G ⧸ H) := rfl
    rw [QuotientGroup.leftRel_apply] at hq
    let t : H := ⟨((s • q).out)⁻¹ * (s * q.out), hq⟩
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
    have hsx_mem : ρ s x ∈ ρ.leftQuotientSubmodule H U (s • q) := by
      rw [left_quotient_submodule_out_local ρ H U (s • q)]
      exact Submodule.mem_map.mpr ⟨ut, ut.property, hsx.symm⟩
    have hsymm_smul :
        (left_quotient_submodule_equiv_local ρ H U (s • q)).symm ⟨ρ s x, hsx_mem⟩ = ut := by
      ext
      simp [ut, hsx]
    calc
      extensionLinearMapLocal ρ H U hU ρ' f (ρ s x) =
          left_quotient_submodule_extension_local ρ H U ρ' f (s • q) ⟨ρ s x, hsx_mem⟩ := by
            exact extensionLinearMapLocal_apply_of_mem ρ H U hU ρ' f hsx_mem
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
              ρ' (s • q).out (ρ' t (f u)) = ρ' (((s • q).out : G) * t) (f u) := by
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
      _ = ρ' s (extensionLinearMapLocal ρ H U hU ρ' f x) := by
            congr 1
            simpa [left_quotient_submodule_extension_local, u] using
              (extensionLinearMapLocal_apply_of_mem ρ H U hU ρ' f (x := x) (q := q) x.property).symm
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Exercise 8-8.5-3: bundle the local extension as a `G`-equivariant intertwiner. -/
private noncomputable abbrev extensionIntertwiningMapLocal
    {G : Type} [Group G]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (hU : ρ.IsInducedFromSubrepresentation H U)
    (ρ' : Representation ℂ G W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp H.subtype)) :
    ρ.IntertwiningMap ρ' :=
  (extensionLinearMapLocal ρ H U hU ρ' f).intertwiningMap_of_isIntertwiningMap
    ρ ρ' (extensionLinearMapLocal_isIntertwining ρ H U hU ρ' f)

/-- Helper for Exercise 8-8.5-3: a `G`-equivariant extension is determined by its values on the
inducing subrepresentation because the coset translates form an internal direct sum. -/
private theorem extensionIntertwiningMapLocal_unique
    {G : Type} [Group G]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (hU : ρ.IsInducedFromSubrepresentation H U)
    (ρ' : Representation ℂ G W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp H.subtype))
    (F : ρ.IntertwiningMap ρ') (hF : ∀ u : U.toSubmodule, F u = f u) :
    F = extensionIntertwiningMapLocal ρ H U hU ρ' f := by
  classical
  apply IntertwiningMap.ext
  ext v
  let ℳ : G ⧸ H → Submodule ℂ W := ρ.leftQuotientSubmodule H U
  let _ : DecidableEq (G ⧸ H) := Classical.decEq _
  have hInternal : DirectSum.IsInternal ℳ := by
    simpa [ℳ, Representation.IsInducedFromSubrepresentation] using hU
  let _ := DirectSum.IsInternal.chooseDecomposition ℳ hInternal
  refine DirectSum.Decomposition.inductionOn (ℳ := ℳ)
      (motive := fun x : W ↦ F x = extensionIntertwiningMapLocal ρ H U hU ρ' f x)
      ?_ ?_ ?_ v
  · simp [extensionIntertwiningMapLocal, extensionLinearMapLocal]
  · intro q x
    let u : U.toSubmodule := (left_quotient_submodule_equiv_local ρ H U q).symm x
    have hx : (x : W) = ρ q.out u := by
      calc
        (x : W) =
            ((left_quotient_submodule_equiv_local ρ H U q u :
                ρ.leftQuotientSubmodule H U q) : W) := by
              exact congrArg
                (fun y : ρ.leftQuotientSubmodule H U q ↦ (y : W))
                ((left_quotient_submodule_equiv_local ρ H U q).apply_symm_apply x).symm
        _ = ρ q.out u := by simp
    calc
      F x = F (ρ q.out u) := by rw [hx]
      _ = ρ' q.out (F u) := by
            simpa using
              (Representation.IntertwiningMap.isIntertwining (f := F) (g := q.out) (v := u))
      _ = ρ' q.out (f u) := by rw [hF u]
      _ = left_quotient_submodule_extension_local ρ H U ρ' f q x := by
            simp [left_quotient_submodule_extension_local, u]
      _ = extensionIntertwiningMapLocal ρ H U hU ρ' f x := by
            symm
            simpa [extensionIntertwiningMapLocal] using
              extensionLinearMapLocal_apply_of_mem ρ H U hU ρ' f (x := x) (q := q) x.property
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- Helper for Exercise 8-8.5-3: every `H`-equivariant map out of the inducing subrepresentation
extends uniquely to the ambient representation. -/
private theorem existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation
    {G : Type} [Group G]
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (hU : ρ.IsInducedFromSubrepresentation H U)
    (ρ' : Representation ℂ G W')
    (f : U.toRepresentation.IntertwiningMap (ρ'.comp H.subtype)) :
    ∃! F : ρ.IntertwiningMap ρ', ∀ u : U.toSubmodule, F u = f u := by
  refine ⟨extensionIntertwiningMapLocal ρ H U hU ρ' f, ?_, ?_⟩
  · intro u
    exact extensionLinearMapLocal_extends ρ H U hU ρ' f u
  · intro F hF
    exact extensionIntertwiningMapLocal_unique ρ H U hU ρ' f F hF

/-- Helper for Exercise 8-8.5-3: the tautological inclusion of a stable subrepresentation is an
intertwiner for the restricted action. -/
private theorem subrepresentation_inclusion_isIntertwining
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype)) :
    ∀ h : H, ∀ u : U.toSubmodule,
      U.toSubmodule.subtype (U.toRepresentation h u) =
        (ρ.comp H.subtype) h (U.toSubmodule.subtype u) := by
  intro h u
  rfl

/-- Helper for Exercise 8-8.5-3: bundle the tautological inclusion as an intertwiner for the
restricted action. -/
private abbrev subrepresentation_inclusion_hom
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype)) :
    U.toRepresentation.IntertwiningMap (ρ.comp H.subtype) :=
  U.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap
    U.toRepresentation (ρ.comp H.subtype)
    (subrepresentation_inclusion_isIntertwining ρ H U)

/-- Helper for Exercise 8-8.5-3: the unit-coset generator intertwines the source action with the
restricted induced action. -/
private theorem induced_identity_copy_mk_one_isIntertwining
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) :
    ∀ h, ∀ w,
      Representation.IndV.mk H.subtype σ 1 (σ h w) =
        ((Rep.ind H.subtype (Rep.of σ)).ρ.comp H.subtype) h
          (Representation.IndV.mk H.subtype σ 1 w) := by
  intro h w
  -- The unit-coset generator transforms exactly by the source action.
  simp [Representation.IndV.mk, ← Representation.Coinvariants.mk_inv_tmul]

/-- Helper for Exercise 8-8.5-3: bundle the unit-coset generator as an intertwiner into the
restricted induced representation. -/
private noncomputable abbrev induced_identity_copy_hom
    {G : Type} [Group G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) :
    σ.IntertwiningMap (((Rep.ind H.subtype (Rep.of σ)).ρ).comp H.subtype) :=
  (Representation.IndV.mk H.subtype σ 1).intertwiningMap_of_isIntertwiningMap
    σ (((Rep.ind H.subtype (Rep.of σ)).ρ).comp H.subtype)
    (induced_identity_copy_mk_one_isIntertwining H σ)

/-- Helper for Exercise 8-8.5-3: a Chapter 3 inducedness witness identifies the representation
with the standard induced model built from the witnessing subrepresentation. -/
private noncomputable def equiv_induced_of_isInducedFromSubrepresentation_proof
    {G : Type} [Group G] [Finite G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (hU : ρ.IsInducedFromSubrepresentation H U) :
    ρ.Equiv ((Rep.ind H.subtype (Rep.of U.toRepresentation)).ρ) := by
  let σind : Representation ℂ G (Representation.IndV H.subtype U.toRepresentation) :=
    (Rep.ind H.subtype (Rep.of U.toRepresentation)).ρ
  let φ : σind.IntertwiningMap ρ := (inducedFromSubrepresentationHomLocal ρ H U).hom
  let iotaρ : U.toRepresentation.IntertwiningMap (ρ.comp H.subtype) :=
    subrepresentation_inclusion_hom ρ H U
  let iotaind : U.toRepresentation.IntertwiningMap (σind.comp H.subtype) :=
    induced_identity_copy_hom H U.toRepresentation
  classical
  let hψexists :=
    (existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation ρ H U hU σind iotaind).exists
  let ψ : ρ.IntertwiningMap σind := Classical.choose hψexists
  have hψ : ∀ u : U.toSubmodule, ψ u = iotaind u := Classical.choose_spec hψexists
  have hright :
      φ.comp ψ = (1 : ρ.IntertwiningMap ρ) := by
    -- Both candidates extend the tautological inclusion of `U`, so uniqueness forces equality.
    apply (existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation
      ρ H U hU ρ iotaρ).unique
    · intro u
      calc
        (φ.comp ψ) u = φ (ψ u) := rfl
        _ = φ (iotaind u) := by rw [hψ u]
        _ = ρ 1⁻¹ u := by
              simpa [φ, iotaind, induced_identity_copy_hom] using
                inducedFromSubrepresentationHomLocal_mk ρ H U 1 u
        _ = u := by simp
    · intro u
      rfl
  let Uind : Subrepresentation (σind.comp H.subtype) :=
    induced_identity_copy_subrepresentation H U.toRepresentation
  let iotaUind : Uind.toRepresentation.IntertwiningMap (σind.comp H.subtype) :=
    subrepresentation_inclusion_hom σind H Uind
  have hUinduced : σind.IsInducedFromSubrepresentation H Uind :=
    induced_identity_copy_is_induced_local H U.toRepresentation
  have hleft :
      ψ.comp φ = (1 : σind.IntertwiningMap σind) := by
    -- The standard induced model is itself induced from the unit-coset copy, so the same
    -- extension uniqueness argument closes the inverse identity on that model.
    apply (existsUnique_intertwiningMapLocal_of_isInducedFromSubrepresentation
      σind H Uind hUinduced σind iotaUind).unique
    · intro u
      calc
        (ψ.comp φ) u = ψ (φ u) := rfl
        _ = ψ (ρ 1⁻¹ ((induced_identity_copy_equiv H U.toRepresentation).symm u)) := by
              rw [induced_identity_copy_eq_mk_one_symm H U.toRepresentation u]
              congr 1
              simpa [φ] using
                inducedFromSubrepresentationHomLocal_mk ρ H U 1
                  ((induced_identity_copy_equiv H U.toRepresentation).symm u)
        _ = ψ ((induced_identity_copy_equiv H U.toRepresentation).symm u) := by simp
        _ = iotaind ((induced_identity_copy_equiv H U.toRepresentation).symm u) := by
              rw [hψ ((induced_identity_copy_equiv H U.toRepresentation).symm u)]
        _ = u := by
              change Representation.IndV.mk H.subtype U.toRepresentation 1
                    ((induced_identity_copy_equiv H U.toRepresentation).symm u) = u
              simpa using (induced_identity_copy_eq_mk_one_symm H U.toRepresentation u).symm
    · intro u
      rfl
  have hleft_linear : ψ.toLinearMap ∘ₗ φ.toLinearMap = LinearMap.id := by
    simpa using congrArg IntertwiningMap.toLinearMap hleft
  have hright_linear : φ.toLinearMap ∘ₗ ψ.toLinearMap = LinearMap.id := by
    simpa using congrArg IntertwiningMap.toLinearMap hright
  -- Package the mutually inverse intertwiners into the required representation equivalence.
  exact Representation.Equiv.mk
    (LinearEquiv.ofLinear ψ.toLinearMap φ.toLinearMap hleft_linear hright_linear)
    ψ.isIntertwining'

/-- Helper for Exercise 8-8.5-3: a Chapter 3 inducedness witness identifies the representation
with the standard induced model built from the witnessing subrepresentation. -/
private noncomputable def equiv_induced_of_isInducedFromSubrepresentation
    {G : Type} [Group G] [Finite G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W)
    (H : Subgroup G)
    (U : Subrepresentation (ρ.comp H.subtype))
    (hU : ρ.IsInducedFromSubrepresentation H U) :
    ρ.Equiv ((Rep.ind H.subtype (Rep.of U.toRepresentation)).ρ) :=
  equiv_induced_of_isInducedFromSubrepresentation_proof ρ H U hU

/-- Helper for Exercise 8-8.5-3: transport a `K`-representation along the canonical equivalence
`K ≃ K.map S.subtype`. -/
private noncomputable def subgroup_map_representation
    {G : Type} [Group G]
    (S : Subgroup G) (K : Subgroup S)
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) :
    Representation ℂ (K.map S.subtype) W :=
  ρ.comp (K.equivMapOfInjective S.subtype S.subtype_injective).symm.toMonoidHom

/-- Helper for Exercise 8-8.5-3: transporting a `K`-representation to `K.map S.subtype` and then
pulling it back along the canonical equivalence recovers the original source action. -/
private theorem subgroup_map_representation_comp_eq
    {G : Type} [Group G]
    (S : Subgroup G) (K : Subgroup S)
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) :
    (subgroup_map_representation S K ρ).comp
        (K.equivMapOfInjective S.subtype S.subtype_injective).toMonoidHom =
      ρ := by
  let eK : K ≃* K.map S.subtype :=
    K.equivMapOfInjective S.subtype S.subtype_injective
  ext k x
  -- The transport uses `eK.symm` followed by `eK`, so the source element is unchanged.
  change ρ (eK.symm (eK k)) x = ρ k x
  simp

/-- Helper for Exercise 8-8.5-3: the canonical equivalence `K ≃ K.map S.subtype` only reindexes
the source action and therefore gives a representation equivalence on the same carrier. -/
private noncomputable def subgroup_map_representation_comp_equiv
    {G : Type} [Group G]
    (S : Subgroup G) (K : Subgroup S)
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) :
    ρ.Equiv
      ((subgroup_map_representation S K ρ).comp
        (K.equivMapOfInjective S.subtype S.subtype_injective).toMonoidHom) := by
  let eK : K ≃* K.map S.subtype :=
    K.equivMapOfInjective S.subtype S.subtype_injective
  refine Representation.Equiv.mk (LinearEquiv.refl ℂ W) ?_
  intro k
  -- The transported action is `ρ (eK.symm (eK k))`, which simplifies back to `ρ k`.
  ext x
  change ρ k x = ρ (eK.symm (eK k)) x
  simp

/-- Helper for Exercise 8-8.5-3: the mapped subgroup inclusion composed with
`K ≃ K.map S.subtype` is the original composite inclusion `K ≤ S ≤ G`. -/
private theorem subgroup_map_subtype_comp_eq
    {G : Type} [Group G]
    (S : Subgroup G) (K : Subgroup S) :
    (K.map S.subtype).subtype.comp
        (K.equivMapOfInjective S.subtype S.subtype_injective).toMonoidHom =
      S.subtype.comp K.subtype := by
  ext k
  -- Both sides send `k` to the same element of `G`.
  simpa using
    (Subgroup.coe_equivMapOfInjective_apply K S.subtype S.subtype_injective k)

/-- Helper for Exercise 8-8.5-3: induction from the composite inclusion `K ≤ S ≤ G` agrees with
induction from the mapped subgroup `K.map S.subtype ≤ G` after transporting the source action
across `K ≃ K.map S.subtype`. -/
private noncomputable def ind_subgroup_chain_map_equiv
    {G : Type} [Group G]
    (S : Subgroup G) (K : Subgroup S)
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) :
    ((Rep.ind (S.subtype.comp K.subtype) (Rep.of ρ)).ρ).Equiv
      ((Rep.ind (K.map S.subtype).subtype
        (Rep.of (subgroup_map_representation S K ρ))).ρ) :=
  by
  let eK : K ≃* K.map S.subtype :=
    K.equivMapOfInjective S.subtype S.subtype_injective
  let e₁ :
      ((Rep.ind (S.subtype.comp K.subtype) (Rep.of ρ)).ρ).Equiv
        ((Rep.ind (S.subtype.comp K.subtype)
          (Rep.of
            ((subgroup_map_representation S K ρ).comp eK.toMonoidHom))).ρ) :=
    ind_equiv_of_source_equiv (S.subtype.comp K.subtype)
      (subgroup_map_representation_comp_equiv S K ρ)
  let e₂ :
      ((Rep.ind ((K.map S.subtype).subtype.comp eK.toMonoidHom)
        (Rep.of
          ((subgroup_map_representation S K ρ).comp eK.toMonoidHom))).ρ).Equiv
        ((Rep.ind (K.map S.subtype).subtype
          (Rep.of (subgroup_map_representation S K ρ))).ρ) := by
      -- Reindexing the subgroup source changes only the domain labels of the induced generators.
      simpa using
        (ind_equiv_of_comp_equiv eK
          (K.map S.subtype).subtype
          (subgroup_map_representation S K ρ))
  -- Route correction: split the source-action transport from the subgroup-hom transport so the
  -- final equivalence is a clean composition of the two existing induced-model adapters.
  exact e₁.trans (by
    simpa [subgroup_map_subtype_comp_eq S K] using e₂)

/-- Helper for Exercise 8-8.5-3: inducing a monomial subgroup representation along a subgroup
inclusion should remain monomial in the ambient group. -/
lemma isMonomial_of_ind_subtype_of_isMonomial
    {G : Type} [Group G] [Finite G]
    {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Subgroup G) (σ : Representation ℂ S W) :
    σ.IsMonomial → ((Rep.ind S.subtype (Rep.of σ)).ρ).IsMonomial :=
  by
  intro hσ
  rcases hσ with ⟨K, U, hUdim, hUinduced⟩
  let eσ :
      σ.Equiv ((Rep.ind K.subtype (Rep.of U.toRepresentation)).ρ) :=
    equiv_induced_of_isInducedFromSubrepresentation σ K U hUinduced
  let eind :
      ((Rep.ind S.subtype (Rep.of σ)).ρ).Equiv
        ((Rep.ind S.subtype
          (Rep.of ((Rep.ind K.subtype (Rep.of U.toRepresentation)).ρ))).ρ) :=
    ind_equiv_of_source_equiv S.subtype eσ
  let echain :
      ((Rep.ind S.subtype
        (Rep.of ((Rep.ind K.subtype (Rep.of U.toRepresentation)).ρ))).ρ).Equiv
        ((Rep.ind (S.subtype.comp K.subtype) (Rep.of U.toRepresentation)).ρ) :=
    ind_subgroup_chain_equiv S K U.toRepresentation
  let emap :
      ((Rep.ind (S.subtype.comp K.subtype) (Rep.of U.toRepresentation)).ρ).Equiv
        ((Rep.ind (K.map S.subtype).subtype
          (Rep.of (subgroup_map_representation S K U.toRepresentation))).ρ) :=
    ind_subgroup_chain_map_equiv S K U.toRepresentation
  let e :
      ((Rep.ind S.subtype (Rep.of σ)).ρ).Equiv
        ((Rep.ind (K.map S.subtype).subtype
          (Rep.of (subgroup_map_representation S K U.toRepresentation))).ρ) :=
    eind.trans (echain.trans emap)
  let Ustd :
      Subrepresentation
        ((((Rep.ind (K.map S.subtype).subtype
            (Rep.of (subgroup_map_representation S K U.toRepresentation))).ρ).comp
            (K.map S.subtype).subtype)) :=
    induced_identity_copy_subrepresentation
      (K.map S.subtype) (subgroup_map_representation S K U.toRepresentation)
  have hUstd_dim : Module.finrank ℂ Ustd.toSubmodule = 1 := by
    -- The standard unit-coset copy has the same carrier dimension as the source representation.
    calc
      Module.finrank ℂ Ustd.toSubmodule =
          Module.finrank ℂ U.toSubmodule := by
            exact
              (induced_identity_copy_equiv
                (K.map S.subtype)
                (subgroup_map_representation S K U.toRepresentation)).symm.toLinearEquiv.finrank_eq
      _ = 1 := hUdim
  have hUstd_induced :
      ((Rep.ind (K.map S.subtype).subtype
        (Rep.of (subgroup_map_representation S K U.toRepresentation))).ρ).IsInducedFromSubrepresentation
          (K.map S.subtype) Ustd := by
    -- The explicit induced model is induced from its unit-coset copy by construction.
    simpa [Ustd] using
      induced_identity_copy_is_induced_local
        (K.map S.subtype) (subgroup_map_representation S K U.toRepresentation)
  let Uambient :
      Subrepresentation
        ((((Rep.ind S.subtype (Rep.of σ)).ρ).comp (K.map S.subtype).subtype)) :=
    transported_subrepresentation_of_equiv
      (comp_subtype_equiv e.symm (K.map S.subtype)) Ustd
  have hUambient_dim : Module.finrank ℂ Uambient.toSubmodule = 1 := by
    -- Transporting along the restricted ambient equivalence preserves the one-dimensional carrier.
    have hUambient_map :
        Uambient.toSubmodule =
          Ustd.toSubmodule.map
            (comp_subtype_equiv e.symm (K.map S.subtype)).toLinearMap := by
      simpa [Uambient] using
        transported_subrepresentation_of_equiv_toSubmodule
          (comp_subtype_equiv e.symm (K.map S.subtype)) Ustd
    let eU :
        Ustd.toSubmodule ≃ₗ[ℂ]
          Ustd.toSubmodule.map
            (comp_subtype_equiv e.symm (K.map S.subtype)).toLinearMap :=
      Submodule.equivMapOfInjective
        (comp_subtype_equiv e.symm (K.map S.subtype)).toLinearMap
        (comp_subtype_equiv e.symm (K.map S.subtype)).injective
        Ustd.toSubmodule
    calc
      Module.finrank ℂ Uambient.toSubmodule =
          Module.finrank ℂ
            (Ustd.toSubmodule.map
              (comp_subtype_equiv e.symm (K.map S.subtype)).toLinearMap) := by
            rw [hUambient_map]
      _ = Module.finrank ℂ Ustd.toSubmodule := by
            exact eU.symm.finrank_eq
      _ = 1 := hUstd_dim
  have hUambient_induced :
      ((Rep.ind S.subtype (Rep.of σ)).ρ).IsInducedFromSubrepresentation
        (K.map S.subtype) Uambient := by
    -- The inducing family transports along the ambient equivalence `e.symm`.
    simpa [Uambient] using
      isInducedFromSubrepresentation_of_equiv e.symm (K.map S.subtype) Ustd hUstd_induced
  -- Route correction: package the transported unit-coset copy directly as the monomial witness
  -- upstairs instead of asking Lean to infer it through the generic transport theorem.
  exact ⟨K.map S.subtype, Uambient, hUambient_dim, hUambient_induced⟩

/-- Helper for Exercise 8-8.5-3: once the stabilizer representation is monomial, the associated
little-groups packet `θ[φ; χ, τ]` should also be monomial. -/
lemma theta_isMonomial_of_characterStabilizer_monomial
    (χ : A →* ℂˣ) (τ : Rep.{0, 0, 0} ℂ H_[φ; χ]) [τ.ρ.IsIrreducible] :
    τ.ρ.IsMonomial → (θ[φ; χ, τ]).ρ.IsMonomial :=
  by
  intro hτmonomial
  let Sχ : Subgroup (A ⋊[φ] H) := character_stabilizer_subgroup (φ := φ) χ
  let τχ : Representation ℂ Sχ τ.V :=
    character_twist_subgroup_representation (φ := φ) χ τ
  let _ : Finite (A ⋊[φ] H) := semidirectProduct_finite (φ := φ)
  have htwist :
      τχ.IsMonomial := by
    -- The stabilizer-side twist preserves the one-dimensional inducing carrier from `τ`.
    simpa [τχ] using
      character_twist_subgroup_representation_isMonomial_of_isMonomial
        (φ := φ) χ τ hτmonomial
  have hinduced :
      (Rep.ind Sχ.subtype (Rep.of τχ)).ρ.IsMonomial := by
    -- Once the subgroup-side twist is monomial, induction to the ambient semidirect product
    -- keeps that monomial witness via the subgroup-chain transport proved above.
    exact isMonomial_of_ind_subtype_of_isMonomial Sχ τχ htwist
  let eθ : (θ[φ; χ, τ]).ρ.Equiv (Rep.ind Sχ.subtype (Rep.of τχ)).ρ := by
    -- Rebuild the packet/induced equivalence locally so the carrier universe of `τ` stays
    -- polymorphic.
    simpa [Sχ, τχ, Representation.theta,
      character_stabilizer_inclusion_eq_subgroup_subtype_comp] using
      (ind_equiv_of_comp_equiv
        (character_stabilizer_subgroup_equiv (φ := φ) χ)
        Sχ.subtype τχ)
  -- The packet model is equivalent to this explicit induced representation.
  exact
    isMonomial_of_equiv
      eθ.symm
      hinduced

/-- Exercise 8-8.5-3: every irreducible finite-dimensional complex representation of a finite
group of the form `A ⋊[φ] H`, with `A` abelian and `H` supersolvable, is induced from a
degree-`1` subrepresentation of a subgroup. -/
theorem
    isMonomial_of_irreducible_of_semidirectProduct_of_supersolvable
    (ρ : Representation ℂ (A ⋊[φ] H) V) [ρ.IsIrreducible] :
    ρ.IsMonomial := by
  classical
  obtain ⟨ι, χ, hχ⟩ := exists_character_orbit_representative_family (φ := φ)
  -- The little-groups classification reduces the ambient irreducible representation to one
  -- packet `θ[φ; χ i, τ]` for a stabilizer representation `τ`.
  obtain ⟨i, τ, hτirr, hIso⟩ :=
    Representation.exists_iso_theta_of_isIrreducible (φ := φ) χ hχ (Rep.of ρ)
  obtain ⟨e⟩ := hIso
  letI : τ.ρ.IsIrreducible := hτirr
  -- The stabilizer subgroup is a subgroup of the given supersolvable group `H`, so the previous
  -- supersolvable theorem should apply directly to `τ`.
  have hτmonomial : τ.ρ.IsMonomial :=
    by
      -- Subgroups of supersolvable groups are supersolvable, so the Chapter `8` owner theorem
      -- applies to the stabilizer representation without any further reduction.
      exact Representation.isMonomial_of_irreducible_of_supersolvable τ.ρ
  have hθmonomial : (θ[φ; χ i, τ]).ρ.IsMonomial :=
    theta_isMonomial_of_characterStabilizer_monomial (φ := φ) (χ := χ i) τ hτmonomial
  -- The packet is isomorphic to the original irreducible representation, so the last step is
  -- transport of the monomial witness across that equivalence.
  simpa using
    isMonomial_of_equiv (Representation.equivOfIso e) hθmonomial

end

end Representation
