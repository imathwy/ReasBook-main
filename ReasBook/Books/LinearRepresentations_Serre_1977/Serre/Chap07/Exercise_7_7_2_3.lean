import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap12.Proposition_12_12_1_1
import LinearRepresentations_Serre_1977.Serre.FiniteToFintype

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Representation

noncomputable section

universe u v w w' uK

section

open Representation Rep

variable {H : Type u} [Group H]
variable {G : Type v} [Group G]

section FiniteCharacterPairing

variable [Finite H] [Finite G]

/-- Helper for Exercise 7-7.2-3: the tensor-level map used in Frobenius reciprocity is
compatible with the defining coinvariant relation for induction. -/
private theorem frobenius_tensor_relation
    {K : Type uK} [Field K]
    {V : Type w} [AddCommGroup V] [Module K V]
    {W : Type w'} [AddCommGroup W] [Module K W]
    (α : H →* G) (E : Representation K G V) (θ : Representation K H W)
    (f : θ.IntertwiningMap (E.comp α)) (g : H) (x : G) (y : W) :
    (((((Finsupp.lift (W →ₗ[K] V) K G) fun h ↦ E h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
          (Representation.leftRegular K G) (α g)).compl₂
        (θ g) ∘ₗ Finsupp.lsingle x)
      (1 : K))
    y =
    ((((Finsupp.lift (W →ₗ[K] V) K G) fun h ↦ E h⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
        Finsupp.lsingle x)
      (1 : K)) y := by
  -- Expand the tensor relation on a pure tensor and rewrite the inner `H`-action via `f`.
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.compl₂_apply,
    Finsupp.lsingle_apply, Representation.ofMulAction_single, smul_eq_mul,
    Finsupp.lift_apply, map_mul, mul_inv_rev, zero_smul, Finsupp.sum_single_index, one_smul,
    IntertwiningMap.toLinearMap_apply, Module.End.mul_apply]
  have hg := LinearMap.congr_fun (f.2 g) y
  simp only [LinearMap.comp_apply] at hg
  change (E x⁻¹) ((E (α g)⁻¹) (f.toLinearMap ((θ g) y))) = (E x⁻¹) (f.toLinearMap y)
  rw [hg]
  simp

/-- Helper for Exercise 7-7.2-3: Frobenius reciprocity gives a linear equivalence between the
intertwining maps `Ind_α θ ⟶ E` and `θ ⟶ Res_α E` without passing through the `Rep` wrapper. -/
private def frobenius_intertwining_equiv
    {K : Type uK} [Field K]
    {V : Type w} [AddCommGroup V] [Module K V]
    {W : Type w'} [AddCommGroup W] [Module K W]
    (α : H →* G) (E : Representation K G V) (θ : Representation K H W) :
    ((ind α θ).IntertwiningMap E) ≃ₗ[K] θ.IntertwiningMap (E.comp α) where
  toFun f :=
    { toLinearMap := f.toLinearMap ∘ₗ IndV.mk α θ 1
      isIntertwining' := fun g => by
        -- Evaluate the induced intertwiner on the canonical generator `IndV.mk α θ 1`.
        ext x
        have hf := LinearMap.congr_fun (f.2 (α g)) (IndV.mk α θ 1 x)
        simpa [← Representation.Coinvariants.mk_inv_tmul] using hf }
  invFun f :=
    { toLinearMap := Representation.Coinvariants.lift _
        (TensorProduct.lift <| Finsupp.lift _ _ _ fun h => E h⁻¹ ∘ₗ f.toLinearMap)
        (fun g => by
          -- The tensor-level formula descends because the defining relation is exactly the
          -- previous helper theorem.
          simp only [Representation.tprod_apply, MonoidHom.coe_comp, Function.comp_apply,
            TensorProduct.lift_comp_map]
          congr 1
          ext x y
          exact frobenius_tensor_relation α E θ f g x y)
      isIntertwining' := fun g => by
        -- On coinvariant classes, the induced action is the explicit inverse translation action.
        ext x
        simp }
  left_inv f := by
    -- Evaluating back on the canonical induced generators recovers `f`.
    ext h a
    have hf := LinearMap.congr_fun (f.2 h⁻¹) (IndV.mk α θ 1 a)
    simpa using hf.symm
  right_inv f := by
    -- The descended map sends `IndV.mk α θ 1` back to the original intertwiner.
    ext x
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- Proof sketch: rewrite both pairings by
-- `Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply`, identify each side
-- with the finrank of an intertwining space using
-- `Representation.card_inv_mul_sum_char_mul_char_eq_finrank`, and then apply Frobenius
-- reciprocity in the form `Rep.indResHomEquiv α`.
/-- Exercise 7-7.2-3 (1): for a homomorphism `α : H →* G`, Frobenius reciprocity for characters
identifies the pairing of `θ.character` with the restricted character `(E.comp α).character` on
`H` with the pairing of the induced character `(ind α θ).character` with `E.character` on `G`.
The source complex statement is the specialization `K = ℂ`. -/
theorem groupFunctionPairing_character_comp_eq_character_ind
    {K : Type uK} [Field K] [Invertible (Nat.card H : K)] [Invertible (Nat.card G : K)]
    {V : Type w} [AddCommGroup V] [Module K V]
    {W : Type w'} [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (α : H →* G) (E : Representation K G V)
    (θ : Representation K H W) :
    ⟪θ.character, Representation.character (E.comp α)⟫ =
      ⟪(ind α θ).character, E.character⟫ := by
  -- Route correction: work directly with the underlying Frobenius formulas on intertwining maps
  -- instead of transporting through `Rep.indResHomEquiv`, which is where the mixed-universe
  -- object-level elaboration was getting stuck.
  letI : FiniteDimensional K (G →₀ K) := by
    infer_instance
  letI : FiniteDimensional K (TensorProduct K (G →₀ K) W) := by
    infer_instance
  letI : FiniteDimensional K (IndV α θ) :=
    FiniteDimensional.of_surjective (Representation.Coinvariants.mk _)
      (Representation.Coinvariants.mk_surjective _)
  -- Rewrite both character pairings as finranks of intertwining spaces.
  calc
    ⟪θ.character, Representation.character (E.comp α)⟫ =
        Module.finrank K (θ.IntertwiningMap (E.comp α)) := by
          simpa using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap K θ
              (E.comp α))
    _ = Module.finrank K ((ind α θ).IntertwiningMap E) := by
          -- Insert the Frobenius reciprocity equivalence on intertwining spaces.
          have hdim : Module.finrank K (θ.IntertwiningMap (E.comp α)) =
              Module.finrank K ((ind α θ).IntertwiningMap E) :=
            (frobenius_intertwining_equiv α E θ).symm.finrank_eq
          simpa [hdim]
    _ = ⟪(ind α θ).character, E.character⟫ := by
          symm
          simpa using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap K
              (ind α θ) E)

end FiniteCharacterPairing

section Surjective

open QuotientGroup

variable {k : Type uK} [CommRing k]
variable {W : Type w'} [AddCommGroup W] [Module k W]

-- Source/core/bridge triage for the surjective comparison:
-- * source-facing: the canonical comparison between `ind α θ` and the quotient action on the
--   `α.ker`-coinvariants of `θ`.
-- * core/canonical owners sampled upstream: `Representation.ind`,
--   `Representation.quotientToCoinvariants`, `Rep.indResHomEquiv`, and
--   `Representation.char_iso`.
-- * primitive data: the homomorphism `α`, its surjectivity, and the source representation `θ`.
-- * bridge/view: the transported quotient action
--   `θ.quotientToCoinvariantsAlongSurjective α hα`.
-- * derived API: the comparison equivalence and its character consequence.

/-- The quotient action on the `α.ker`-coinvariants of `θ`, transported from `H ⧸ α.ker` to `G`
through the first isomorphism theorem attached to a surjective `α : H →* G`. -/
noncomputable abbrev Representation.quotientToCoinvariantsAlongSurjective
    (θ : Representation k H W) (α : H →* G) (hα : Function.Surjective α) :
    Representation k G (Coinvariants (θ.comp α.ker.subtype)) :=
  (quotientToCoinvariants θ α.ker).comp
    (quotientKerEquivOfSurjective α hα).symm.toMonoidHom

/-- The quotient action on the `α.ker`-invariants of `θ`, transported from `H ⧸ α.ker` to `G`
through the first isomorphism theorem attached to a surjective `α : H →* G`. -/
noncomputable abbrev Representation.quotientToInvariantsAlongSurjective
    (θ : Representation k H W) (α : H →* G) (hα : Function.Surjective α) :
    Representation k G (Representation.invariants (θ.comp α.ker.subtype)) :=
  (quotientToInvariants θ α.ker).comp
    (quotientKerEquivOfSurjective α hα).symm.toMonoidHom

/-- Helper for Exercise 7-7.2-3: under the first isomorphism theorem, the chosen quotient class
of `α h` is represented by `h` itself. -/
@[simp] private theorem quotientKerEquivOfSurjective_symm_apply_mk
    (α : H →* G) (hα : Function.Surjective α) (h : H) :
    (quotientKerEquivOfSurjective α hα).symm (α h) = QuotientGroup.mk h := by
  apply (quotientKerEquivOfSurjective α hα).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- Helper for Exercise 7-7.2-3: acting on `ker α`-coinvariants by the inverse quotient class of
`h` sends the class of `θ h x` back to the class of `x`. -/
private theorem quotientToCoinvariants_inv_apply_mk_apply
    (α : H →* G) (θ : Representation k H W) (h : H) (x : W) :
    ((θ.quotientToCoinvariants α.ker) (QuotientGroup.mk h)⁻¹)
      (Coinvariants.mk (θ.comp α.ker.subtype) (θ h x)) =
    Coinvariants.mk (θ.comp α.ker.subtype) x := by
  -- Rewrite the quotient action through `toCoinvariants`, where the computation is direct.
  rw [← QuotientGroup.mk_inv]
  change ((θ.toCoinvariants α.ker) h⁻¹) (Coinvariants.mk (θ.comp α.ker.subtype) (θ h x)) = _
  rw [Representation.toCoinvariants_mk]
  simp

/-- Helper for Exercise 7-7.2-3: moving the `H`-action from the coefficient vector into the
`G`-coordinate of the induced generator produces the expected inverse `α h`. -/
private theorem ind_mk_one_apply
    (α : H →* G) (θ : Representation k H W) (h : H) (x : W) :
    IndV.mk α θ 1 (θ h x) = IndV.mk α θ ((α h)⁻¹) x := by
  -- This is exactly the defining coinvariant relation in the tensor model of `IndV α θ`.
  change Coinvariants.mk (Representation.tprod ((Representation.leftRegular k G).comp α) θ)
      (Finsupp.single (1 : G) (1 : k) ⊗ₜ[k] θ h x) =
    Coinvariants.mk (Representation.tprod ((Representation.leftRegular k G).comp α) θ)
      (Finsupp.single ((α h)⁻¹) (1 : k) ⊗ₜ[k] x)
  symm
  simpa using
    (Representation.Coinvariants.mk_inv_tmul
      (ρ := (Representation.leftRegular k G).comp α)
      (τ := θ)
      (x := Finsupp.single (1 : G) (1 : k))
      (y := x)
      (g := h))

/-- Helper for Exercise 7-7.2-3: when `h ∈ ker α`, the previous induced-generator identity
specializes to a fixed unit-coset generator. -/
private theorem ind_mk_one_apply_ker
    (α : H →* G) (θ : Representation k H W) (n : α.ker) (x : W) :
    IndV.mk α θ 1 (θ n x) = IndV.mk α θ 1 x := by
  -- In the kernel case, the translated `G`-coordinate is still the unit element.
  have hn : (α ↑n : G)⁻¹ = 1 := by
    simp [show α ↑n = (1 : G) from n.property]
  simpa [hn] using ind_mk_one_apply α θ (n : H) x

/-- Helper for Exercise 7-7.2-3: the explicit inverse candidate sends a `ker α`-coinvariant class
to the unit-coset generator in the induced module. -/
private noncomputable def coinvariants_ker_to_ind_linear
    (α : H →* G) (θ : Representation k H W) :
    Coinvariants (θ.comp α.ker.subtype) →ₗ[k] IndV α θ :=
  Coinvariants.lift _ (IndV.mk α θ 1) fun n ↦ by
    -- The lift is well defined because `ker α` acts trivially on the unit-coset generator.
    ext x
    simpa using ind_mk_one_apply_ker α θ n x

/-- Helper for Exercise 7-7.2-3: the explicit inverse candidate sends a representative class to
the corresponding unit-coset induced generator. -/
@[simp] private theorem coinvariants_ker_to_ind_linear_apply_mk
    (α : H →* G) (θ : Representation k H W) (x : W) :
    coinvariants_ker_to_ind_linear α θ (Coinvariants.mk (θ.comp α.ker.subtype) x) =
      IndV.mk α θ 1 x := by
  -- Evaluate the quotient lift on a chosen representative.
  simp [coinvariants_ker_to_ind_linear]

/-- Helper for Exercise 7-7.2-3: the explicit inverse candidate intertwines the quotient action
on `ker α`-coinvariants with the induced `G`-action. -/
private theorem coinvariants_ker_to_ind_linear_intertwines
    (α : H →* G) (hα : Function.Surjective α) (θ : Representation k H W) (g : G) :
    coinvariants_ker_to_ind_linear α θ ∘ₗ (θ.quotientToCoinvariantsAlongSurjective α hα) g =
      (ind α θ) g ∘ₗ coinvariants_ker_to_ind_linear α θ := by
  obtain ⟨h, rfl⟩ := hα g
  -- Reduce the intertwining check to coinvariant classes of actual vectors.
  apply Coinvariants.hom_ext
  ext x
  simp only [LinearMap.comp_apply, Representation.quotientToCoinvariantsAlongSurjective,
    MonoidHom.coe_comp, Function.comp_apply, coinvariants_ker_to_ind_linear_apply_mk]
  have hq :
      (quotientKerEquivOfSurjective α hα).symm.toMonoidHom (α h) = QuotientGroup.mk h := by
    simpa using quotientKerEquivOfSurjective_symm_apply_mk α hα h
  rw [hq]
  -- Once the quotient action is rewritten on representatives, the induced-generator identity
  -- finishes the comparison.
  simp only [Representation.quotientToCoinvariants, Representation.toCoinvariants]
  simpa [Representation.ind_mk] using ind_mk_one_apply α θ h x

-- Proof sketch: let `N = α.ker`, use the first isomorphism theorem
-- `QuotientGroup.quotientKerEquivOfSurjective α hα : H ⧸ N ≃* G`, and compare the induced
-- representation `Representation.ind α θ` with the quotient action of `H ⧸ N` on the
-- `N`-coinvariants `Representation.Coinvariants (θ.comp N.subtype)`.
private noncomputable def ind_along_surjective_to_quotientToCoinvariants_hom
    (α : H →* G) (hα : Function.Surjective α) (θ : Representation k H W) :
    (ind α θ).IntertwiningMap (θ.quotientToCoinvariantsAlongSurjective α hα) := by
  classical
  refine
    { toLinearMap :=
        Coinvariants.lift _ (TensorProduct.lift <|
          Finsupp.lift _ _ _ fun g ↦
            θ.quotientToCoinvariantsAlongSurjective α hα g⁻¹ ∘ₗ
              Coinvariants.mk (θ.comp α.ker.subtype)) ?_
      isIntertwining' := ?_ }
  · intro h
    -- Check the tensor relation on pure tensors `single g ⊗ x`; after that, everything is a
    -- direct simplification to the quotient-action identity on `ker α`-coinvariants.
    ext g x
    simp only [quotientToCoinvariantsAlongSurjective, MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, map_inv,
      Representation.tprod_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
      TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_self,
      TensorProduct.curry_apply, TensorProduct.map_tmul, Representation.ofMulAction_single,
      smul_eq_mul, TensorProduct.lift.tmul, Finsupp.lift_apply, map_mul, mul_inv_rev,
      zero_smul, Finsupp.sum_single_index, one_smul, Module.End.mul_apply,
      quotientKerEquivOfSurjective_symm_apply_mk, quotientToCoinvariants_inv_apply_mk_apply]
  · intro g
    -- Both sides agree on the canonical induced generators `IndV.mk α θ g x`.
    ext x
    simp [Representation.quotientToCoinvariantsAlongSurjective]

@[simp] private theorem ind_along_surjective_to_quotientToCoinvariants_hom_apply_mk
    (α : H →* G) (hα : Function.Surjective α) (θ : Representation k H W)
    (g : G) (x : W) :
    ind_along_surjective_to_quotientToCoinvariants_hom α hα θ (IndV.mk α θ g x) =
      θ.quotientToCoinvariantsAlongSurjective α hα g⁻¹
        (Coinvariants.mk (θ.comp α.ker.subtype) x) := by
  -- Unfold the induced generator and evaluate the quotient lift on the corresponding tensor.
  simp [ind_along_surjective_to_quotientToCoinvariants_hom]

private theorem ind_along_surjective_to_quotientToCoinvariants_hom_bijective
    (α : H →* G) (hα : Function.Surjective α) (θ : Representation k H W) :
    Function.Bijective
      (ind_along_surjective_to_quotientToCoinvariants_hom α hα θ).toLinearMap := by
  let Finv : Coinvariants (θ.comp α.ker.subtype) →ₗ[k] IndV α θ :=
    coinvariants_ker_to_ind_linear α θ
  have hright :
      (ind_along_surjective_to_quotientToCoinvariants_hom α hα θ).toLinearMap ∘ₗ Finv =
        LinearMap.id := by
    -- The forward comparison followed by the explicit inverse is the identity on quotient classes.
    apply Coinvariants.hom_ext
    ext x
    simpa [Finv, coinvariants_ker_to_ind_linear_apply_mk] using
      ind_along_surjective_to_quotientToCoinvariants_hom_apply_mk α hα θ (1 : G) x
  have hleft :
      Finv ∘ₗ (ind_along_surjective_to_quotientToCoinvariants_hom α hα θ).toLinearMap =
        LinearMap.id := by
    -- The induced module is generated by the canonical maps `IndV.mk α θ g`.
    apply Representation.IndV.hom_ext (φ := α) (ρ := θ)
    intro g
    ext x
    calc
      (Finv ∘ₗ (ind_along_surjective_to_quotientToCoinvariants_hom α hα θ).toLinearMap)
          (IndV.mk α θ g x) =
          Finv (((θ.quotientToCoinvariantsAlongSurjective α hα) g⁻¹)
            (Coinvariants.mk (θ.comp α.ker.subtype) x)) := by
            simpa [LinearMap.comp_apply] using congrArg Finv
              (ind_along_surjective_to_quotientToCoinvariants_hom_apply_mk α hα θ g x)
      _ = ((ind α θ) g⁻¹) (Finv (Coinvariants.mk (θ.comp α.ker.subtype) x)) := by
        exact LinearMap.congr_fun
          (coinvariants_ker_to_ind_linear_intertwines α hα θ g⁻¹)
          (Coinvariants.mk (θ.comp α.ker.subtype) x)
      _ = ((ind α θ) g⁻¹) (IndV.mk α θ 1 x) := by
        simp [Finv, coinvariants_ker_to_ind_linear_apply_mk]
      _ = IndV.mk α θ g x := by
        simp
  refine ⟨?_, ?_⟩
  · intro x y hxy
    calc
      x =
          (Finv ∘ₗ (ind_along_surjective_to_quotientToCoinvariants_hom α hα θ).toLinearMap) x := by
            simpa [LinearMap.comp_apply] using
              (LinearMap.congr_fun hleft x).symm
      _ =
          (Finv ∘ₗ (ind_along_surjective_to_quotientToCoinvariants_hom α hα θ).toLinearMap) y := by
            simpa [LinearMap.comp_apply] using congrArg Finv hxy
      _ = y := by
        simpa [LinearMap.comp_apply] using LinearMap.congr_fun hleft y
  · intro y
    refine ⟨Finv y, ?_⟩
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun hright y

/-- Exercise 7-7.2-3 (2): if `α : H →* G` is surjective and `N = ker α`, then the induced
representation `Ind_α W` is canonically equivalent to the representation of `G ≃ H ⧸ N` obtained
from the action of `H ⧸ N` on the `N`-coinvariants of `W`. -/
noncomputable def ind_along_surjective_equiv_comp_quotientToCoinvariants
    (α : H →* G) (hα : Function.Surjective α) (θ : Representation k H W) :
    (ind α θ).Equiv (θ.quotientToCoinvariantsAlongSurjective α hα) :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective
      (ind_along_surjective_to_quotientToCoinvariants_hom α hα θ).toLinearMap
      (ind_along_surjective_to_quotientToCoinvariants_hom_bijective α hα θ))
    (ind_along_surjective_to_quotientToCoinvariants_hom α hα θ).isIntertwining'

@[simp] theorem ind_along_surjective_equiv_comp_quotientToCoinvariants_apply_mk
    (α : H →* G) (hα : Function.Surjective α) (θ : Representation k H W)
    (g : G) (x : W) :
    ind_along_surjective_equiv_comp_quotientToCoinvariants α hα θ (IndV.mk α θ g x) =
      θ.quotientToCoinvariantsAlongSurjective α hα g⁻¹
        (Coinvariants.mk (θ.comp α.ker.subtype) x) :=
  ind_along_surjective_to_quotientToCoinvariants_hom_apply_mk α hα θ g x

/-- Helper for Exercise 7-7.2-3: averaging over a finite group is unchanged after translating the
input by any group element. -/
private theorem averageMap_apply_group_action
    {K : Type uK} [Field K]
    {N : Type u} [Group N] [Fintype N]
    {X : Type w} [AddCommGroup X] [Module K X]
    [Invertible (Fintype.card N : K)]
    (ρ : Representation K N X) (g : N) (x : X) :
    Representation.averageMap ρ (ρ g x) = Representation.averageMap ρ x := by
  -- Expand the average and reindex by right multiplication with `g`.
  simp [Representation.averageMap, GroupAlgebra.average, map_sum]
  congr 1
  calc
    ∑ h : N, ρ h (ρ g x) = ∑ h : N, ρ (h * g) x := by
      refine Fintype.sum_congr (fun h : N ↦ ρ h (ρ g x)) (fun h : N ↦ ρ (h * g) x) ?_
      intro h
      simp [map_mul]
    _ = ∑ h : N, ρ h x := by
      exact Fintype.sum_bijective (fun h : N ↦ h * g) (Group.mulRight_bijective g)
        (fun h : N ↦ ρ (h * g) x) (fun h : N ↦ ρ h x) fun h ↦ by
          rfl

/-- Helper for Exercise 7-7.2-3: averaging on coinvariants lands in the invariant subspace. -/
private noncomputable def coinvariants_to_invariants_of_averageMap
    {K : Type uK} [Field K]
    {N : Type u} [Group N] [Fintype N]
    {X : Type w} [AddCommGroup X] [Module K X]
    [Invertible (Fintype.card N : K)]
    (ρ : Representation K N X) :
    Coinvariants ρ →ₗ[K] Representation.invariants ρ :=
  Coinvariants.lift ρ
    { toFun := fun x ↦ ⟨Representation.averageMap ρ x, Representation.averageMap_invariant ρ x⟩
      map_add' := by simp
      map_smul' := by simp }
    fun g ↦ by
      -- The average depends only on the coinvariant class.
      ext x
      exact averageMap_apply_group_action ρ g x

/-- Helper for Exercise 7-7.2-3: the invariant inclusion followed by the quotient map gives the
inverse candidate from invariants back to coinvariants. -/
private noncomputable def invariants_to_coinvariants
    {K : Type uK} [Field K]
    {N : Type u} [Group N]
    {X : Type w} [AddCommGroup X] [Module K X]
    (ρ : Representation K N X) :
    Representation.invariants ρ →ₗ[K] Coinvariants ρ :=
  Coinvariants.mk ρ ∘ₗ Submodule.subtype _

/-- Helper for Exercise 7-7.2-3: sending a coinvariant class to its averaged representative and
then quotienting again is the identity. -/
private theorem invariants_to_coinvariants_left_inv
    {K : Type uK} [Field K]
    {N : Type u} [Group N] [Fintype N]
    {X : Type w} [AddCommGroup X] [Module K X]
    [Invertible (Fintype.card N : K)]
    (ρ : Representation K N X) :
    invariants_to_coinvariants ρ ∘ₗ coinvariants_to_invariants_of_averageMap ρ = LinearMap.id := by
  -- It is enough to check the composition on representative vectors.
  apply Coinvariants.hom_ext
  ext x
  change Coinvariants.mk ρ (Representation.averageMap ρ x) = Coinvariants.mk ρ x
  calc
    Coinvariants.mk ρ (Representation.averageMap ρ x) =
        (Fintype.card N : K)⁻¹ • ∑ g : N, Coinvariants.mk ρ (ρ g x) := by
          simp [Representation.averageMap, GroupAlgebra.average, map_sum]
    _ = (Fintype.card N : K)⁻¹ • ∑ g : N, Coinvariants.mk ρ x := by
          congr 2
          ext g
          simp
    _ = Coinvariants.mk ρ x := by
          rw [Finset.sum_const, Finset.card_univ]
          rw [← Nat.cast_smul_eq_nsmul K (Fintype.card N) (Coinvariants.mk ρ x), smul_smul]
          simp

/-- Helper for Exercise 7-7.2-3: quotienting an invariant vector and re-averaging recovers the
same invariant vector. -/
private theorem invariants_to_coinvariants_right_inv
    {K : Type uK} [Field K]
    {N : Type u} [Group N] [Fintype N]
    {X : Type w} [AddCommGroup X] [Module K X]
    [Invertible (Fintype.card N : K)]
    (ρ : Representation K N X) :
    coinvariants_to_invariants_of_averageMap ρ ∘ₗ invariants_to_coinvariants ρ = LinearMap.id := by
  -- On invariant vectors, the averaging projector is the identity.
  ext x
  exact Representation.averageMap_id ρ x x.property

/-- Helper for Exercise 7-7.2-3: for a finite group with invertible order, coinvariants and
invariants are canonically identified by averaging. -/
private noncomputable def coinvariants_equiv_invariants_of_averageMap
    {K : Type uK} [Field K]
    {N : Type u} [Group N] [Fintype N]
    {X : Type w} [AddCommGroup X] [Module K X]
    [Invertible (Fintype.card N : K)]
    (ρ : Representation K N X) :
    Coinvariants ρ ≃ₗ[K] Representation.invariants ρ :=
  LinearEquiv.ofLinear
    (coinvariants_to_invariants_of_averageMap ρ)
    (invariants_to_coinvariants ρ)
    (by
      simpa [LinearMap.comp_apply] using invariants_to_coinvariants_right_inv ρ)
    (by
      simpa [LinearMap.comp_apply] using invariants_to_coinvariants_left_inv ρ)

/-- Helper for Exercise 7-7.2-3: if `N` is normal in `H`, then averaging over the restricted
`N`-representation commutes with the ambient `H`-action. -/
private theorem averageMap_commutes_with_normal_action
    {K : Type uK} [Field K]
    {N : Subgroup H} [N.Normal]
    [Fintype N]
    {X : Type w} [AddCommGroup X] [Module K X]
    [Invertible (Fintype.card N : K)]
    (ρ : Representation K H X) (u : H) (x : X) :
    Representation.averageMap (ρ.comp N.subtype) (ρ u x) =
      ρ u (Representation.averageMap (ρ.comp N.subtype) x) := by
  -- Expand the average and reindex the kernel sum by conjugation with `u`.
  simp [Representation.averageMap, GroupAlgebra.average, map_sum]
  congr 1
  let e : N ≃ N :=
    { toFun := fun n ↦
        ⟨u⁻¹ * n * u, by
          simpa [mul_assoc] using
            Subgroup.Normal.conj_mem' (show N.Normal from inferInstance) n n.2 u⟩
      invFun := fun n ↦
        ⟨u * n * u⁻¹, by
          simpa [mul_assoc] using
            Subgroup.Normal.conj_mem (show N.Normal from inferInstance) n n.2 u⟩
      left_inv := fun n ↦ by
        ext
        simp [mul_assoc]
      right_inv := fun n ↦ by
        ext
        simp [mul_assoc] }
  exact Fintype.sum_equiv e
    (fun n : N ↦ ρ n (ρ u x))
    (fun n : N ↦ ρ u (ρ n x))
    fun n ↦ by
      simp [e, mul_assoc]

section FiniteSource

variable [Finite H]
local instance : DecidableEq G := Classical.decEq G

/-- Helper for Exercise 7-7.2-3: the hypothesis that `|ker α|` is invertible can be read using
the canonical `Fintype` structure on `ker α`, which is the form required by the averaging API. -/
private noncomputable instance invertible_fintypeCard_ker
    {K : Type uK} [Field K] (α : H →* G) [Invertible (Nat.card α.ker : K)] :
    Invertible (Fintype.card α.ker : K) := by
  rwa [Fintype.card_eq_nat_card]

/-- Helper for Exercise 7-7.2-3: averaging over `ker α` intertwines the quotient action on
coinvariants with the corresponding quotient action on invariants. -/
private theorem coinvariants_averageMap_conj_quotient_action
    {K : Type uK} [Field K]
    {W : Type w'} [AddCommGroup W] [Module K W]
    (α : H →* G) (hα : Function.Surjective α)
    [Invertible (Nat.card α.ker : K)]
    (θ : Representation K H W) (g : G) :
    ↑(coinvariants_equiv_invariants_of_averageMap (θ.comp α.ker.subtype)) ∘ₗ
        ((θ.quotientToCoinvariantsAlongSurjective α hα) g) =
      (θ.quotientToInvariantsAlongSurjective α hα) g ∘ₗ
        ↑(coinvariants_equiv_invariants_of_averageMap (θ.comp α.ker.subtype)) := by
  let ρKer : Representation K α.ker W := θ.comp α.ker.subtype
  obtain ⟨u, rfl⟩ := hα g
  -- It suffices to evaluate on coinvariant classes of actual vectors, where both sides reduce
  -- to the average of `θ u x`.
  apply Coinvariants.hom_ext
  ext x
  simp [coinvariants_equiv_invariants_of_averageMap,
    coinvariants_to_invariants_of_averageMap, Representation.quotientToCoinvariantsAlongSurjective,
    Representation.quotientToInvariantsAlongSurjective,
    quotientKerEquivOfSurjective_symm_apply_mk]
  simpa [Representation.averageMap] using
    (averageMap_commutes_with_normal_action (ρ := θ) (N := α.ker) (u := u) (x := x))

/-- Helper for Exercise 7-7.2-3: the averaging equivalence upgrades to a `G`-equivariant
identification between the quotient coinvariant and quotient invariant models. -/
private noncomputable abbrev
    quotientToCoinvariantsAlongSurjective_equiv_quotientToInvariantsAlongSurjective
    {K : Type uK} [Field K]
    {W : Type w'} [AddCommGroup W] [Module K W]
    (α : H →* G) (hα : Function.Surjective α)
    [Invertible (Nat.card α.ker : K)]
    (θ : Representation K H W) :
    (θ.quotientToCoinvariantsAlongSurjective α hα).Equiv
      (θ.quotientToInvariantsAlongSurjective α hα) :=
  Representation.Equiv.mk
    (coinvariants_equiv_invariants_of_averageMap (θ.comp α.ker.subtype))
    (coinvariants_averageMap_conj_quotient_action α hα θ)

/-- Helper for Exercise 7-7.2-3: the trace of the transported quotient action on `ker α`-invariants
is the trace of `averageMap ∘ θ u` on the original space, for any lift `u` of `s`. -/
private theorem trace_quotientToInvariantsAlongSurjective_eq_averageMap_comp
    {K : Type uK} [Field K]
    {W : Type w'} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (α : H →* G) (hα : Function.Surjective α)
    [Invertible (Nat.card α.ker : K)]
    (θ : Representation K H W) (s : G) (u : H) (hu : α u = s) :
    LinearMap.trace K (Representation.invariants (θ.comp α.ker.subtype))
      ((θ.quotientToInvariantsAlongSurjective α hα) s) =
    LinearMap.trace K W (Representation.averageMap (θ.comp α.ker.subtype) ∘ₗ θ u) := by
  let ρKer : Representation K α.ker W := θ.comp α.ker.subtype
  let p : W →ₗ[K] W := Representation.averageMap ρKer
  let hproj : LinearMap.IsProj (Representation.invariants ρKer) p :=
    Representation.isProj_averageMap ρKer
  let huInv :
      Representation.invariants ρKer ≤ (Representation.invariants ρKer).comap (θ u) :=
    Representation.le_comap_invariants θ α.ker u
  let Tu : Representation.invariants ρKer →ₗ[K] Representation.invariants ρKer :=
    (θ u).restrict fun x hx ↦ huInv hx
  let e : (Representation.invariants ρKer × LinearMap.ker p) ≃ₗ[K] W :=
    (Representation.invariants ρKer).prodEquivOfIsCompl (LinearMap.ker p) hproj.isCompl
  have hs :
      ((θ.quotientToInvariantsAlongSurjective α hα) s) = Tu := by
    -- After choosing a lift `u` of `s`, the quotient action is just the restriction of `θ u`.
    subst s
    ext x
    simp [Tu, Representation.quotientToInvariantsAlongSurjective,
      quotientKerEquivOfSurjective_symm_apply_mk]
  have hconj :
      e.symm.conj ((θ u) ∘ₗ p) = LinearMap.prodMap Tu 0 := by
    -- In the `invariants × ker(averageMap)` decomposition, `θ u ∘ averageMap` keeps only the
    -- invariant block and kills the complementary summand.
    apply LinearMap.ext
    rintro ⟨xInv, xKer⟩
    have hpInv : p xInv = xInv := by
      simpa [p, Representation.averageMap] using
        (Representation.averageMap_id ρKer xInv xInv.property)
    have hpKer : p xKer = 0 := xKer.property
    have hp :
        p (e (xInv, xKer)) = xInv := by
      change Representation.averageMap ρKer ((xInv : W) + (xKer : W)) = xInv
      rw [map_add, hpInv, hpKer, add_zero]
    have hleft :
        e.symm (((θ u) ∘ₗ p) (e (xInv, xKer))) = (Tu xInv, 0) := by
      change e.symm (θ u (p (e (xInv, xKer)))) = (Tu xInv, 0)
      rw [hp]
      simpa [e, Tu] using
        (Submodule.prodEquivOfIsCompl_symm_apply_left
          (p := Representation.invariants ρKer)
          (q := LinearMap.ker p)
          (h := hproj.isCompl)
          (x := Tu xInv))
    simpa [LinearEquiv.conj_apply, LinearMap.prodMap_apply] using hleft
  calc
    LinearMap.trace K (Representation.invariants ρKer)
        ((θ.quotientToInvariantsAlongSurjective α hα) s) =
        LinearMap.trace K (Representation.invariants ρKer) Tu := by
          rw [hs]
    _ = LinearMap.trace K (Representation.invariants ρKer × LinearMap.ker p)
          (LinearMap.prodMap Tu 0) := by
            simpa using
              (LinearMap.trace_prodMap' Tu (0 : LinearMap.ker p →ₗ[K] LinearMap.ker p)).symm
    _ = LinearMap.trace K (Representation.invariants ρKer × LinearMap.ker p)
          (e.symm.conj ((θ u) ∘ₗ p)) := by
            rw [hconj]
    _ = LinearMap.trace K W ((θ u) ∘ₗ p) := by
          simpa [e] using (LinearMap.trace_conj' ((θ u) ∘ₗ p) e.symm)
    _ = LinearMap.trace K W (p ∘ₗ θ u) := by
          simpa using (LinearMap.trace_mul_comm (R := K) (M := W) p (θ u)).symm
    _ = LinearMap.trace K W (Representation.averageMap (θ.comp α.ker.subtype) ∘ₗ θ u) := by
          rfl

/-- Helper for Exercise 7-7.2-3: the character of the transported quotient action on
`ker α`-invariants is the normalized average of `θ.character` over the fiber of `α` above `s`. -/
private theorem character_quotientToInvariantsAlongSurjective_eq_fiber_average
    {K : Type uK} [Field K]
    {W : Type w'} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (α : H →* G) (hα : Function.Surjective α)
    [Invertible (Nat.card α.ker : K)]
    (θ : Representation K H W) (s : G) :
    (θ.quotientToInvariantsAlongSurjective α hα).character s =
      (Nat.card α.ker : K)⁻¹ *
        ∑ t with α t = s, θ.character t := by
  let ρKer : Representation K α.ker W := θ.comp α.ker.subtype
  obtain ⟨u, hu⟩ := hα s
  have htrace :=
    trace_quotientToInvariantsAlongSurjective_eq_averageMap_comp α hα θ s u hu
  have hsum :
      ∑ n : α.ker, θ.character ((n : H) * u) =
        ∑ t with α t = s, θ.character t := by
    classical
    let e : α.ker ≃ { t : H // α t = s } :=
      { toFun := fun n ↦ ⟨(n : H) * u, by
          show α ((n : H) * u) = s
          simpa [map_mul, hu] using congrArg (fun z : G ↦ z * α u) n.property⟩
        invFun := fun t ↦ ⟨t * u⁻¹, by
          show α ((t : H) * u⁻¹) = 1
          calc
            α ((t : H) * u⁻¹) = α t * α u⁻¹ := by simp [map_mul]
            _ = s * s⁻¹ := by simp [t.property, hu]
            _ = 1 := by simp⟩
        left_inv := fun n ↦ by
          ext
          simp
        right_inv := fun t ↦ by
          ext
          simp [t.property, hu] }
    -- Reindex the kernel average by the fiber of `α` over `s`.
    calc
      ∑ n : α.ker, θ.character ((n : H) * u) =
          ∑ t : { t : H // α t = s }, θ.character (t : H) := by
            exact Fintype.sum_equiv e
              (fun n ↦ θ.character ((n : H) * u))
              (fun t ↦ θ.character (t : H))
              (fun n ↦ by rfl)
      _ = ∑ t with α t = s, θ.character t := by
            simpa using
              (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
                (p := fun t : H ↦ α t = s)
                (f := fun t : H ↦ θ.character t))
  rw [Representation.character]
  calc
    LinearMap.trace K (Representation.invariants ρKer)
        ((θ.quotientToInvariantsAlongSurjective α hα) s) =
        LinearMap.trace K W (Representation.averageMap ρKer ∘ₗ θ u) := htrace
    _ = LinearMap.trace K W (((Nat.card α.ker : K)⁻¹ • ∑ n : α.ker, ρKer n) ∘ₗ θ u) := by
          -- Expanding `averageMap` exhibits the averaging operator as the normalized kernel sum.
          simp [Representation.averageMap, GroupAlgebra.average, map_sum]
    _ = LinearMap.trace K W
          ((Nat.card α.ker : K)⁻¹ • ((∑ n : α.ker, ρKer n) ∘ₗ θ u)) := by
            rw [LinearMap.smul_comp]
    _ = (Nat.card α.ker : K)⁻¹ *
          LinearMap.trace K W ((∑ n : α.ker, ρKer n) ∘ₗ θ u) := by
            simpa [smul_eq_mul] using
              (map_smul (LinearMap.trace K W) (↑(Nat.card α.ker : K)⁻¹)
                ((∑ n : α.ker, ρKer n) ∘ₗ θ u))
    _ = (Nat.card α.ker : K)⁻¹ *
          ∑ n : α.ker, LinearMap.trace K W ((ρKer n) ∘ₗ θ u) := by
            have hcomp :
                (∑ n : α.ker, ρKer n) ∘ₗ θ u =
                  ∑ n : α.ker, (ρKer n) ∘ₗ θ u := by
              ext x
              simp
            rw [hcomp, map_sum]
    _ = (Nat.card α.ker : K)⁻¹ *
          ∑ n : α.ker, θ.character ((n : H) * u) := by
            congr 2 with n
            change LinearMap.trace K W (θ ↑n * θ u) = θ.character ((n : H) * u)
            simp [Representation.character, map_mul]
    _ = (Nat.card α.ker : K)⁻¹ * ∑ t with α t = s, θ.character t := by
          rw [hsum]

-- Proof sketch: rewrite `(ind α θ).character` using
-- `Representation.char_iso (ind_along_surjective_equiv_comp_quotientToCoinvariants α hα θ)`,
-- then identify the quotient character as the average of `θ.character` over the fiber of `α`
-- above `s`, whose size is `|ker α|`.
/-- Exercise 7-7.2-3 (3): if `α : H →* G` is surjective, then for each `s : G` the induced
character is the average of `θ.character` over the fiber `α ⁻¹' {s}`, with normalizing factor
`1 / |ker α|`. The source complex statement is the specialization `K = ℂ`. -/
theorem character_ind_along_surjective_eq_card_ker_inv_sum
    {K : Type uK} [Field K]
    {W : Type w'} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (α : H →* G) (hα : Function.Surjective α)
    [Invertible (Nat.card α.ker : K)]
    (θ : Representation K H W) (s : G) :
    (ind α θ).character s =
      (Nat.card α.ker : K)⁻¹ *
        ∑ t with α t = s, θ.character t := by
  -- Route correction: instead of staying on the coinvariant model, move first to the invariant
  -- model via averaging, then compute the invariant-side character by the trace of
  -- `averageMap ∘ θ u` and reindex the kernel sum by the fiber over `s`.
  calc
    (ind α θ).character s =
        (θ.quotientToCoinvariantsAlongSurjective α hα).character s := by
          -- Part (2) already identifies the induced representation with the quotient coinvariant
          -- model.
          simpa using congrFun
            (Representation.char_iso
              (ind_along_surjective_equiv_comp_quotientToCoinvariants α hα θ)) s
    _ = (θ.quotientToInvariantsAlongSurjective α hα).character s := by
          -- Averaging upgrades the quotient coinvariant model to the quotient invariant model.
          simpa using congrFun
            (Representation.char_iso
              (quotientToCoinvariantsAlongSurjective_equiv_quotientToInvariantsAlongSurjective
                α hα θ)) s
    _ = (Nat.card α.ker : K)⁻¹ *
          ∑ t with α t = s, θ.character t := by
            -- The invariant-side character is the normalized average over the fiber `α⁻¹(s)`.
            exact character_quotientToInvariantsAlongSurjective_eq_fiber_average α hα θ s

end FiniteSource

end Surjective

end
