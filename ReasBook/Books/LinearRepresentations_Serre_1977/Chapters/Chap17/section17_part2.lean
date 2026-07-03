import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_17_17_2_4 (from Chap17) -/
open scoped MonoidAlgebra Representation SubgroupInduction TensorProduct
open CategoryTheory

noncomputable section

universe u

namespace Representation

section OrdinaryRow

variable (k : Type u) [Field k]
variable (G : Type u) [Group G] [Finite G]

local instance ordinary_finiteRepGrothendieckAddCommMonoid
    (H : Type u) [Group H] [Finite H] : AddCommMonoid (R₀[k](H)) :=
  (QuotientAddGroup.Quotient.addCommGroup
    (finiteRepGrothendieckRelations k H)).toAddCommMonoid

local instance ordinary_finiteRepGrothendieckAddCommGroup
    (H : Type u) [Group H] [Finite H] : AddCommGroup (R₀[k](H)) :=
  QuotientAddGroup.Quotient.addCommGroup
    (finiteRepGrothendieckRelations k H)

local instance ordinary_finiteRepGrothendieckIntModule
    (H : Type u) [Group H] [Finite H] : Module ℤ (R₀[k](H)) :=
  AddCommGroup.toIntModule (R₀[k](H))

/-- Helper for Theorem 17-17.2-4: the normalized rationalized owner for `R₀[k](H)`. -/
private abbrev RationalizedFiniteRepGrothendieck
    (H : Type u) [Group H] [Finite H] :=
  @TensorProduct ℤ Int.instCommSemiring ℚ R₀[k](H) Rat.addCommMonoid
    (ordinary_finiteRepGrothendieckAddCommMonoid (k := k) H)
    (AddCommGroup.toIntModule ℚ)
    (ordinary_finiteRepGrothendieckIntModule (k := k) H)

/-- Helper for Theorem 17-17.2-4: the normalized cyclic direct-sum source for the ordinary row. -/
private abbrev CyclicRationalizedFiniteRepGrothendieckSource :=
  Π₀ H : _root_.Subgroup.cyclicSubgroups G, RationalizedFiniteRepGrothendieck (k := k) H.1

local instance : DecidableEq ↥(_root_.Subgroup.cyclicSubgroups G) :=
  Classical.decEq _

/-- Helper for Theorem 17-17.2-4: the cyclic-induction `DFinsupp` sum commutes with scalar
multiplication on the source. -/
private lemma cyclic_rationalized_induction_lsum_smul
    (q : ℚ) (ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G)) :
    (cyclic_rationalized_induction_lsum k G) (q • ξ) =
      q • (cyclic_rationalized_induction_lsum k G) ξ := by
  -- The source-side scalar acts through the `DFinsupp.lsum` because it is `ℚ`-linear.
  rw [map_smul]

/-- Helper for Theorem 17-17.2-4: the cyclic-induction `DFinsupp` sum commutes with addition on
the source. -/
private lemma cyclic_rationalized_induction_lsum_add
    (ξ η : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G)) :
    (cyclic_rationalized_induction_lsum k G) (ξ + η) =
      (cyclic_rationalized_induction_lsum k G) ξ +
        (cyclic_rationalized_induction_lsum k G) η := by
  -- The same linearity lets us separate a sum of componentwise witnesses.
  rw [map_add]

/-- Helper for Theorem 17-17.2-4: the zero tensor is hit trivially by the cyclic-induction owner.
-/
private theorem cyclic_rationalized_zero_pureTensor_preimage :
    ∃ N : ℕ, N ≠ 0 ∧
      ∃ ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
        (cyclic_rationalized_induction_lsum k G) ξ =
          (N : ℚ) •
            ((1 : ℚ) ⊗ₜ[ℤ] (0 : R₀[k](G)) :
              RationalizedFiniteRepGrothendieck (k := k) G) := by
  -- The zero tensor is obtained from the zero direct-sum vector with the harmless choice `N = 1`.
  refine ⟨1, one_ne_zero, 0, ?_⟩
  simp

/-- Helper for Theorem 17-17.2-4: the canonical `DFinsupp` sum of the rationalized cyclic
subgroup-induction maps. -/
private abbrev cyclic_rationalized_induction_lsum :
    (Π₀ H : _root_.Subgroup.cyclicSubgroups G,
      RationalizedFiniteRepGrothendieck (k := k) H.1) →ₗ[ℚ]
      RationalizedFiniteRepGrothendieck (k := k) G :=
  DFinsupp.lsum ℚ fun H : _root_.Subgroup.cyclicSubgroups G ↦
    (Subgroup.finiteRepGrothendieckGroupRationalizedInduction
      (k := k) (G := G) H.1 :
      RationalizedFiniteRepGrothendieck (k := k) H.1 →ₗ[ℚ]
        RationalizedFiniteRepGrothendieck (k := k) G)

/-- Helper for Theorem 17-17.2-4: restricting a finite-dimensional representation to a subgroup
simply rebundles the `Rep.res` owner. -/
private abbrev fdRep_subgroupRestriction_local
    {L : Type u} [Field L] (H : Subgroup G) (V : FDRep L G) : FDRep L H :=
  FDRep.of (Rep.res H.subtype (Rep.of V.ρ)).ρ

/-- Helper for Theorem 17-17.2-4: the morphism induced on bundled finite-dimensional
representations by subgroup restriction is just the `Rep.resFunctor` image transported back
through `FDRep`. -/
private abbrev fdRep_subgroupRestriction_map_local
    {L : Type u} [Field L] {H : Subgroup G} {V W : FDRep L G} (f : V ⟶ W) :
    fdRep_subgroupRestriction_local (G := G) H V ⟶
      fdRep_subgroupRestriction_local (G := G) H W :=
  (FDRep.forget₂HomLinearEquiv _ _)
    ((Rep.resFunctor H.subtype).map ((forget₂ (FDRep L G) (Rep L G)).map f))

/-- Helper for Theorem 17-17.2-4: forgetting a restricted `FDRep` morphism recovers the
underlying `Rep.resFunctor` image. -/
private theorem fdRep_subgroupRestriction_map_forget_local
    {L : Type u} [Field L] {H : Subgroup G} {V W : FDRep L G} (f : V ⟶ W) :
    (forget₂ (FDRep L H) (Rep L H)).map
        (fdRep_subgroupRestriction_map_local (G := G) (H := H) f) =
      (Rep.resFunctor H.subtype).map ((forget₂ (FDRep L G) (Rep L G)).map f) := by
  -- Expose the transport through `FDRep.forget₂HomLinearEquiv`.
  change
    (FDRep.forget₂HomLinearEquiv
      (fdRep_subgroupRestriction_local (G := G) H V)
      (fdRep_subgroupRestriction_local (G := G) H W)).symm
      ((FDRep.forget₂HomLinearEquiv
        (fdRep_subgroupRestriction_local (G := G) H V)
        (fdRep_subgroupRestriction_local (G := G) H W))
        ((Rep.resFunctor H.subtype).map
          ((forget₂ (FDRep L G) (Rep L G)).map f))) =
    (Rep.resFunctor H.subtype).map ((forget₂ (FDRep L G) (Rep L G)).map f)
  exact LinearEquiv.symm_apply_apply _ _

/-- Helper for Theorem 17-17.2-4: subgroup restriction preserves exact short complexes of
finite-dimensional representations. -/
private abbrev fdRep_subgroupRestriction_shortComplex_local
    {L : Type u} [Field L] (H : Subgroup G) (S : ShortComplex (FDRep L G)) :
    ShortComplex (FDRep L H) :=
  ShortComplex.mk
    (fdRep_subgroupRestriction_map_local (G := G) (H := H) S.f)
    (fdRep_subgroupRestriction_map_local (G := G) (H := H) S.g)
    (by
      -- After forgetting to `Rep`, this is exactly functoriality of `Rep.resFunctor`.
      apply (forget₂ (FDRep L H) (Rep L H)).map_injective
      rw [fdRep_subgroupRestriction_map_forget_local (G := G) (H := H) S.f]
      rw [fdRep_subgroupRestriction_map_forget_local (G := G) (H := H) S.g]
      simpa using Functor.map_zero (Rep.resFunctor H.subtype) S.zero)

/-- Helper for Theorem 17-17.2-4: subgroup restriction sends short exact sequences of
finite-dimensional representations to short exact sequences. -/
private theorem fdRep_subgroupRestriction_shortExact_local
    {L : Type u} [Field L] (H : Subgroup G) (S : ShortComplex (FDRep L G))
    (hS : S.ShortExact) :
    (fdRep_subgroupRestriction_shortComplex_local (G := G) (L := L) H S).ShortExact := by
  -- First forget to `Rep`, where the restriction functor preserves exactness automatically.
  have hRep :
      (((fdRep_subgroupRestriction_shortComplex_local
          (G := G) (L := L) H S).map (forget₂ (FDRep L H) (Rep L H)))).ShortExact := by
    simpa [fdRep_subgroupRestriction_shortComplex_local,
      fdRep_subgroupRestriction_map_forget_local] using
      (ShortComplex.ShortExact.map_of_exact (Rep.resFunctor H.subtype) S hS)
  refine ⟨?_, ?_, ?_⟩
  · exact
      ((fdRep_subgroupRestriction_shortComplex_local
          (G := G) (L := L) H S).exact_map_iff_of_faithful
        (forget₂ (FDRep L H) (Rep L H))).1 hRep.exact
  · exact (forget₂ (FDRep L H) (Rep L H)).mono_of_mono_map hRep.mono_f
  · exact (forget₂ (FDRep L H) (Rep L H)).epi_of_epi_map hRep.epi_g

/-- Helper for Theorem 17-17.2-4: the free-group lift sending `[V]` to the Grothendieck class of
its restricted representation on the subgroup. -/
private abbrev finiteRepGrothendieckGroupRestrictionLift_local
    {L : Type u} [Field L] (H : Subgroup G) :
    FreeAbelianGroup (FDRep L G) →+ R₀[L](H) :=
  FreeAbelianGroup.lift fun V ↦ [fdRep_subgroupRestriction_local (G := G) H V]₀

/-- Helper for Theorem 17-17.2-4: the defining relations of `R₀[L](G)` vanish after subgroup
restriction to `H`. -/
private theorem finiteRepGrothendieckRelations_le_subgroupRestrictionLift_ker_local
    {L : Type u} [Field L] (H : Subgroup G) :
    finiteRepGrothendieckRelations L G ≤
      (finiteRepGrothendieckGroupRestrictionLift_local (G := G) (L := L) H).ker := by
  -- Evaluate subgroup restriction on each defining short-exact-sequence generator.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  change
    [fdRep_subgroupRestriction_local (G := G) H S.X₂]₀ -
        [fdRep_subgroupRestriction_local (G := G) H S.X₁]₀ -
        [fdRep_subgroupRestriction_local (G := G) H S.X₃]₀ = 0
  rw [sub_eq_zero]
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right
      (L := L) (G := H)
      (fdRep_subgroupRestriction_shortComplex_local (G := G) (L := L) H S)
      (fdRep_subgroupRestriction_shortExact_local (G := G) (L := L) H S hS)
  calc
    [fdRep_subgroupRestriction_local (G := G) H S.X₂]₀ -
        [fdRep_subgroupRestriction_local (G := G) H S.X₁]₀ =
      ([fdRep_subgroupRestriction_local (G := G) H S.X₁]₀ +
          [fdRep_subgroupRestriction_local (G := G) H S.X₃]₀) -
        [fdRep_subgroupRestriction_local (G := G) H S.X₁]₀ := by
          rw [hrelation]
    _ = [fdRep_subgroupRestriction_local (G := G) H S.X₃]₀ := by
          abel

/-- Helper for Theorem 17-17.2-4: the Grothendieck-group restriction map
`Res_H^G : R₀[L](G) → R₀[L](H)` on finite-dimensional representations. -/
private def finiteRepGrothendieckGroupRestriction_local
    {L : Type u} [Field L] (H : Subgroup G) :
    R₀[L](G) →+ R₀[L](H) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations L G)
    (finiteRepGrothendieckGroupRestrictionLift_local (G := G) (L := L) H)
    (finiteRepGrothendieckRelations_le_subgroupRestrictionLift_ker_local
      (G := G) (L := L) H)

/-- Helper for Theorem 17-17.2-4: on a generator class, subgroup restriction gives the class of
the restricted representation. -/
@[simp] private theorem finiteRepGrothendieckGroupRestriction_apply_class_local
    {L : Type u} [Field L] (H : Subgroup G) (V : FDRep L G) :
    finiteRepGrothendieckGroupRestriction_local (G := G) (L := L) H [V]₀ =
      [fdRep_subgroupRestriction_local (G := G) H V]₀ := by
  -- Evaluate the quotient lift on the generator `FreeAbelianGroup.of V`.
  rfl

/-- Helper for Theorem 17-17.2-4: the trivial representation class is the multiplicative unit of
`R₀[k](G)`. -/
@[simp] private theorem finiteRepGrothendieckClass_trivial_eq_one :
    ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)) = 1 := by
  rfl

/-- Helper for Theorem 17-17.2-4: in the induced source, moving a subgroup action from the tensor
coefficient into the group coordinate shifts that coordinate by right multiplication with the
inverse subgroup element. -/
private theorem subgroupInduction_tensor_source_mk_shift_local
    (H : Subgroup G) (V : FDRep k H) (W : FDRep k G) (h : H) (g : G) (v : V) (w : W) :
    Representation.IndV.mk H.subtype
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) g
        (((Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ h)
          (v ⊗ₜ[k] w)) =
      Representation.IndV.mk H.subtype
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) (g * h⁻¹)
        (v ⊗ₜ[k] w) := by
  -- This is exactly the defining coinvariant relation in the tensor model of induction.
  change
    Representation.Coinvariants.mk
        (Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
          (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ)
        (Finsupp.single g (1 : k) ⊗ₜ[k]
          (((Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ h)
            (v ⊗ₜ[k] w))) =
      Representation.Coinvariants.mk
        (Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
          (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ)
        (Finsupp.single (g * h⁻¹) (1 : k) ⊗ₜ[k] (v ⊗ₜ[k] w))
  symm
  simpa using
    (Representation.Coinvariants.mk_inv_tmul
      (ρ := (Representation.leftRegular k G).comp H.subtype)
      (τ := (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ)
      (x := Finsupp.single g (1 : k))
      (y := (v ⊗ₜ[k] w))
      (g := h))

/-- Helper for Theorem 17-17.2-4: on the target tensor product, the ambient `G`-action acts by
the standard induced right translation on the first factor and by the ambient action on `W` on the
second factor. -/
private theorem subgroupInduction_tensor_target_action_mk_local
    (H : Subgroup G) (V : FDRep k H) (W : FDRep k G) (t g : G) (v : V) (w : W) :
    (((FDRep.subgroupInduction (k := k) (G := G) V).ρ ⊗ W.ρ) t)
        (Representation.IndV.mk H.subtype (Rep.of V.ρ) g v ⊗ₜ[k] w) =
      Representation.IndV.mk H.subtype (Rep.of V.ρ) (g * t⁻¹) v ⊗ₜ[k] (W.ρ t w) := by
  -- Unfold the tensor action once, then the induced factor is exactly `Representation.ind_mk`.
  simp [Representation.tprod_apply, Representation.ind_mk]

/-- Helper for Theorem 17-17.2-4: transporting the naive inverse seed
`[g ⊗ v] ⊗ w ↦ [g ⊗ (v ⊗ W(g) w)]` across the subgroup-induction relation produces the
conjugated ambient action `W(h g h⁻¹)`.

This records the exact obstruction in the current projection-formula route: the planned inverse
formula does not descend through the `IndV` quotient unless this conjugation term is accounted
for. -/
private theorem subgroupInduction_tensor_inverse_seed_conjugation_local
    (H : Subgroup G) (V : FDRep k H) (W : FDRep k G) (h : H) (g : G) (v : V) (w : W) :
    Representation.IndV.mk H.subtype
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) (g * h⁻¹)
        (v ⊗ₜ[k] W.ρ (g * h⁻¹) w) =
      Representation.IndV.mk H.subtype
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) g
        ((((Rep.of V.ρ).ρ h) v) ⊗ₜ[k] W.ρ ((h : G) * g * h⁻¹) w) := by
  -- Move the subgroup action from the group coordinate back into the coefficient, then simplify
  -- the tensor action on the restricted ambient factor.
  calc
    Representation.IndV.mk H.subtype
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) (g * h⁻¹)
        (v ⊗ₜ[k] W.ρ (g * h⁻¹) w) =
      Representation.IndV.mk H.subtype
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) g
        (((Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ h)
          (v ⊗ₜ[k] W.ρ (g * h⁻¹) w)) := by
            symm
            simpa using
              subgroupInduction_tensor_source_mk_shift_local
                (k := k) (G := G) H V W h g v (W.ρ (g * h⁻¹) w)
    _ =
      Representation.IndV.mk H.subtype
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) g
        ((((Rep.of V.ρ).ρ h) v) ⊗ₜ[k] W.ρ ((h : G) * g * h⁻¹) w) := by
          simp [Representation.tprod_apply, map_mul, mul_assoc]

/-- Helper for Theorem 17-17.2-4: the inverse Frobenius-reciprocity map evaluates on an induced
generator by moving back to the unit-coset seed and then using equivariance. -/
private theorem indResHomEquiv_symm_apply_mk_local
    {H' : Type*} [Group H']
    {G' : Type*} [Group G']
    (φ : H' →* G')
    (M : Rep k H')
    (N : Rep k G')
    (f : M ⟶ Rep.res φ N)
    (g : G') (x : M.V) :
    (((Rep.indResHomEquiv φ M N).symm f).hom) (Representation.IndV.mk φ M.ρ g x) =
      N.ρ g⁻¹ (f.hom x) := by
  let inv : Rep.ind φ M ⟶ N := (Rep.indResHomEquiv φ M N).symm f
  have hseed :
      inv.hom (Representation.IndV.mk φ M.ρ 1 x) = f.hom x := by
    have hEq : (Rep.indResHomEquiv φ M N) inv = f :=
      LinearEquiv.apply_symm_apply (Rep.indResHomEquiv φ M N) f
    have htmp :
        (((Rep.indResHomEquiv φ M N) inv).hom) x =
          inv.hom (Representation.IndV.mk φ M.ρ 1 x) := by
      rw [Rep.indResHomEquiv_apply]
      rfl
    simpa [hEq] using htmp.symm
  -- Move the general generator to the unit-coset generator, then use the intertwining relation.
  calc
    inv.hom (Representation.IndV.mk φ M.ρ g x) =
        inv.hom ((Representation.ind φ M.ρ) g⁻¹ (Representation.IndV.mk φ M.ρ 1 x)) := by
          rw [Representation.ind_mk]
          simp
    _ = N.ρ g⁻¹ (inv.hom (Representation.IndV.mk φ M.ρ 1 x)) := by
        simpa using
          (hom_comm_apply inv g⁻¹ (Representation.IndV.mk φ M.ρ 1 x))
    _ = N.ρ g⁻¹ (f.hom x) := by
        rw [hseed]

/-- Helper for Theorem 17-17.2-4: in the plain induced source, moving a subgroup action from the
coefficient into the group coordinate shifts that coordinate by right multiplication with the
inverse subgroup element. -/
private theorem subgroupInduction_source_mk_shift_local
    (H : Subgroup G) (V : FDRep k H) (h : H) (g : G) (v : V) :
    Representation.IndV.mk H.subtype (Rep.of V.ρ) g (((Rep.of V.ρ).ρ h) v) =
      Representation.IndV.mk H.subtype (Rep.of V.ρ) (g * h⁻¹) v := by
  -- This is the defining coinvariant relation in the ordinary induced model.
  change
    Representation.Coinvariants.mk
        (Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
          (Rep.of V.ρ).ρ)
        (Finsupp.single g (1 : k) ⊗ₜ[k] (((Rep.of V.ρ).ρ h) v)) =
      Representation.Coinvariants.mk
        (Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
          (Rep.of V.ρ).ρ)
        (Finsupp.single (g * h⁻¹) (1 : k) ⊗ₜ[k] v)
  symm
  simpa using
    (Representation.Coinvariants.mk_inv_tmul
      (ρ := (Representation.leftRegular k G).comp H.subtype)
      (τ := (Rep.of V.ρ).ρ)
      (x := Finsupp.single g (1 : k))
      (y := v)
      (g := h))

/-- Helper for Theorem 17-17.2-4: the unit-coset tensor map is `H`-equivariant before invoking
Frobenius reciprocity. -/
private theorem subgroupInduction_tensor_seed_isIntertwining_local
    (H : Subgroup G) (V : FDRep k H) (W : FDRep k G) :
    (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ.IsIntertwiningMap
      (Rep.res H.subtype (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)).ρ
      (TensorProduct.map
        (Representation.IndV.mk H.subtype (Rep.of V.ρ) 1)
        (LinearMap.id : W →ₗ[k] W)) := by
  refine Representation.IsIntertwiningMap.mk ?_
  intro h z
  -- Check equivariance on pure tensors; the two local `IndV.mk` transport lemmas are the only
  -- nontrivial input.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro v w
    calc
      (TensorProduct.map
          (Representation.IndV.mk H.subtype (Rep.of V.ρ) 1)
          (LinearMap.id : W →ₗ[k] W))
          (((Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ h)
            (v ⊗ₜ[k] w)) =
        Representation.IndV.mk H.subtype (Rep.of V.ρ) 1 (((Rep.of V.ρ).ρ h) v) ⊗ₜ[k]
          (W.ρ (h : G) w) := by
            simp [Representation.tprod_apply]
      _ =
        Representation.IndV.mk H.subtype (Rep.of V.ρ) ((1 : G) * h⁻¹) v ⊗ₜ[k]
          (W.ρ (h : G) w) := by
            rw [subgroupInduction_source_mk_shift_local (k := k) (G := G) H V h 1 v]
      _ =
        (((FDRep.subgroupInduction (k := k) (G := G) V).ρ ⊗ W.ρ) (h : G))
          (Representation.IndV.mk H.subtype (Rep.of V.ρ) 1 v ⊗ₜ[k] w) := by
            symm
            simpa using
              subgroupInduction_tensor_target_action_mk_local
                (k := k) (G := G) H V W (h : G) 1 v w
  · intro z₁ z₂ hz₁ hz₂
    simpa [map_add, hz₁, hz₂]

/-- Helper for Theorem 17-17.2-4: the canonical forward map for the projection formula is chosen
by Frobenius reciprocity from the unit-coset `H`-map. -/
private noncomputable abbrev subgroupInduction_tensor_restriction_hom_local
    (H : Subgroup G) (V : FDRep k H) (W : FDRep k G) :
    FDRep.subgroupInduction (k := k) (G := G)
        (V ⊗ fdRep_subgroupRestriction_local (G := G) H W) ⟶
      (FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W :=
  (FDRep.forget₂HomLinearEquiv _ _)
    (((Rep.indResHomEquiv
        H.subtype
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ)
        (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)).symm
      ((TensorProduct.map
          (Representation.IndV.mk H.subtype (Rep.of V.ρ) 1)
          (LinearMap.id : W →ₗ[k] W)).intertwiningMap_of_isIntertwiningMap
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ
        (Rep.res H.subtype
          (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)).ρ
        (subgroupInduction_tensor_seed_isIntertwining_local
          (k := k) (G := G) H V W)))

/-- Helper for Theorem 17-17.2-4: the canonical forward projection-formula map sends each induced
generator to the expected tensor generator formula. -/
private theorem subgroupInduction_tensor_restriction_hom_apply_mk_local
    (H : Subgroup G) (V : FDRep k H) (W : FDRep k G) (g : G) (v : V) (w : W) :
    (subgroupInduction_tensor_restriction_hom_local (k := k) (G := G) H V W).hom
        (Representation.IndV.mk H.subtype
          (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) g
          (v ⊗ₜ[k] w)) =
      Representation.IndV.mk H.subtype (Rep.of V.ρ) g v ⊗ₜ[k] (W.ρ g⁻¹ w) := by
  -- Evaluate the Frobenius-chosen forward map using the general `indResHomEquiv` generator
  -- formula, then rewrite the residual ambient action on the target tensor product.
  change
    (((Rep.indResHomEquiv
        H.subtype
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ)
        (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)).symm
      ((TensorProduct.map
          (Representation.IndV.mk H.subtype (Rep.of V.ρ) 1)
          (LinearMap.id : W →ₗ[k] W)).intertwiningMap_of_isIntertwiningMap
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ
        (Rep.res H.subtype
          (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)).ρ
        (subgroupInduction_tensor_seed_isIntertwining_local
          (k := k) (G := G) H V W))).hom
      (Representation.IndV.mk H.subtype
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) g
        (v ⊗ₜ[k] w)) =
      Representation.IndV.mk H.subtype (Rep.of V.ρ) g v ⊗ₜ[k] (W.ρ g⁻¹ w)
  calc
    (((Rep.indResHomEquiv
        H.subtype
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ)
        (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)).symm
      ((TensorProduct.map
          (Representation.IndV.mk H.subtype (Rep.of V.ρ) 1)
          (LinearMap.id : W →ₗ[k] W)).intertwiningMap_of_isIntertwiningMap
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ
        (Rep.res H.subtype
          (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)).ρ
        (subgroupInduction_tensor_seed_isIntertwining_local
          (k := k) (G := G) H V W))).hom
      (Representation.IndV.mk H.subtype
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) g
        (v ⊗ₜ[k] w)) =
      (((FDRep.subgroupInduction (k := k) (G := G) V).ρ ⊗ W.ρ) g⁻¹)
        (Representation.IndV.mk H.subtype (Rep.of V.ρ) 1 v ⊗ₜ[k] w) := by
          simpa using
            indResHomEquiv_symm_apply_mk_local
              (k := k)
              (φ := H.subtype)
              (M := Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ)
              (N := Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)
              ((TensorProduct.map
                  (Representation.IndV.mk H.subtype (Rep.of V.ρ) 1)
                  (LinearMap.id : W →ₗ[k] W)).intertwiningMap_of_isIntertwiningMap
                (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ
                (Rep.res H.subtype
                  (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)).ρ
                (subgroupInduction_tensor_seed_isIntertwining_local
                  (k := k) (G := G) H V W))
              g (v ⊗ₜ[k] w)
    _ = Representation.IndV.mk H.subtype (Rep.of V.ρ) g v ⊗ₜ[k] (W.ρ g⁻¹ w) := by
        simpa using
          subgroupInduction_tensor_target_action_mk_local
            (k := k) (G := G) H V W g⁻¹ 1 v w

/-- Helper for Theorem 17-17.2-4: the identity-copy projection on `Res_H^G(Ind_H^G(V))` sends an
`H`-indexed generator to the expected inverse translate of its coefficient. -/
private theorem induced_identity_copy_projection_apply_mk_mem_local
    (H : Subgroup G) (V : FDRep k H) (h : H) (v : V) :
    inducedIdentityCopyProjection H (Rep.of V.ρ).ρ
        (Representation.IndV.mk H.subtype (Rep.of V.ρ).ρ (h : G) v) =
      ((Rep.of V.ρ).ρ h⁻¹) v := by
  -- Rewrite the `H`-indexed generator to the unit copy and then evaluate the explicit projection.
  calc
    inducedIdentityCopyProjection H (Rep.of V.ρ).ρ
        (Representation.IndV.mk H.subtype (Rep.of V.ρ).ρ (h : G) v) =
      inducedIdentityCopyProjection H (Rep.of V.ρ).ρ
        (Representation.IndV.mk H.subtype (Rep.of V.ρ).ρ 1 (((Rep.of V.ρ).ρ h⁻¹) v)) := by
          exact congrArg
            (inducedIdentityCopyProjection H (Rep.of V.ρ).ρ)
            (ind_mk_eq_mk_one_inv (k := k) (θ := (Rep.of V.ρ).ρ) h v)
    _ = ((Rep.of V.ρ).ρ h⁻¹) v := by
          exact induced_identity_copy_projection_apply_mk_one H (Rep.of V.ρ).ρ _

/-- Helper for Theorem 17-17.2-4: the unit-copy projection is `H`-equivariant on the restricted
induced representation. -/
private theorem subgroupInduction_identity_projection_isIntertwining_local
    (H : Subgroup G) (V : FDRep k H) :
    (Rep.res H.subtype (Rep.of (FDRep.subgroupInduction (k := k) (G := G) V).ρ)).ρ
      .IsIntertwiningMap
        (Rep.of V.ρ).ρ
        (inducedIdentityCopyProjection H (Rep.of V.ρ).ρ) := by
  refine Representation.IsIntertwiningMap.mk ?_
  intro h
  -- Compare the two linear maps on the standard generators `IndV.mk g v`.
  apply Representation.IndV.hom_ext
  intro g
  ext v
  by_cases hg : g ∈ H
  · let gh : H := ⟨g, hg⟩
    have hgh_mem : g * h⁻¹ ∈ H := by
      exact H.mul_mem hg (H.inv_mem h.2)
    let ghh : H := ⟨g * h⁻¹, hgh_mem⟩
    have hinv : ghh⁻¹ = h * gh⁻¹ := by
      ext
      simp [ghh, gh, mul_assoc]
    -- Inside the identity copy, both sides reduce to the same inverse-action formula.
    calc
      inducedIdentityCopyProjection H (Rep.of V.ρ).ρ
          (((Rep.res H.subtype
              (Rep.of (FDRep.subgroupInduction (k := k) (G := G) V).ρ)).ρ) h
            (Representation.IndV.mk H.subtype (Rep.of V.ρ).ρ g v)) =
        inducedIdentityCopyProjection H (Rep.of V.ρ).ρ
          (Representation.IndV.mk H.subtype (Rep.of V.ρ).ρ (g * h⁻¹) v) := by
            simp [FDRep.subgroupInduction, Representation.ind_mk]
      _ = ((Rep.of V.ρ).ρ ghh⁻¹) v := by
            simpa [ghh] using
              induced_identity_copy_projection_apply_mk_mem_local
                (k := k) (G := G) H V ghh v
      _ = ((Rep.of V.ρ).ρ h) (((Rep.of V.ρ).ρ gh⁻¹) v) := by
            rw [hinv, map_mul]
      _ = ((Rep.of V.ρ).ρ h)
            (inducedIdentityCopyProjection H (Rep.of V.ρ).ρ
              (Representation.IndV.mk H.subtype (Rep.of V.ρ).ρ g v)) := by
            rw [induced_identity_copy_projection_apply_mk_mem_local
              (k := k) (G := G) H V gh v]
  · have hgh_not_mem : g * h⁻¹ ∉ H := by
      intro hgh_mem
      apply hg
      have hg_eq : g = (g * h⁻¹) * h := by
        simp [mul_assoc]
      rw [hg_eq]
      exact H.mul_mem hgh_mem h.2
    -- Outside the identity copy, the projection kills both the translated generator and the
    -- original generator.
    calc
      inducedIdentityCopyProjection H (Rep.of V.ρ).ρ
          (((Rep.res H.subtype
              (Rep.of (FDRep.subgroupInduction (k := k) (G := G) V).ρ)).ρ) h
            (Representation.IndV.mk H.subtype (Rep.of V.ρ).ρ g v)) =
        inducedIdentityCopyProjection H (Rep.of V.ρ).ρ
          (Representation.IndV.mk H.subtype (Rep.of V.ρ).ρ (g * h⁻¹) v) := by
            simp [FDRep.subgroupInduction, Representation.ind_mk]
      _ = 0 := by
            exact induced_identity_copy_projection_apply_mk_of_not_mem
              H (Rep.of V.ρ).ρ hgh_not_mem v
      _ = ((Rep.of V.ρ).ρ h)
            (inducedIdentityCopyProjection H (Rep.of V.ρ).ρ
              (Representation.IndV.mk H.subtype (Rep.of V.ρ).ρ g v)) := by
            rw [induced_identity_copy_projection_apply_mk_of_not_mem
              H (Rep.of V.ρ).ρ hg v]
            simp

/-- Helper for Theorem 17-17.2-4: the restriction-side unit-copy projection tensor seed is
`H`-equivariant. -/
private theorem subgroupInduction_tensor_projection_seed_isIntertwining_local
    (H : Subgroup G) (V : FDRep k H) (W : FDRep k G) :
    (Rep.res H.subtype (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)).ρ
      .IsIntertwiningMap
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ
        (TensorProduct.map
          (inducedIdentityCopyProjection H (Rep.of V.ρ).ρ)
          (LinearMap.id : W →ₗ[k] W)) := by
  refine Representation.IsIntertwiningMap.mk ?_
  intro h z
  -- Check equivariance on pure tensors, using the tensor action and the unit-copy projection
  -- intertwining property on the induced factor.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp
  · intro x w
    have hproj :=
      (subgroupInduction_identity_projection_isIntertwining_local
        (k := k) (G := G) H V).isIntertwining h x
    calc
      (TensorProduct.map
          (inducedIdentityCopyProjection H (Rep.of V.ρ).ρ)
          (LinearMap.id : W →ₗ[k] W))
          (((Rep.res H.subtype
              (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)).ρ) h)
            (x ⊗ₜ[k] w)) =
        (inducedIdentityCopyProjection H (Rep.of V.ρ).ρ
          (((Rep.res H.subtype
              (Rep.of (FDRep.subgroupInduction (k := k) (G := G) V).ρ)).ρ) h) x)) ⊗ₜ[k]
          (W.ρ (h : G) w) := by
            simp [Representation.tprod_apply]
      _ = ((Rep.of V.ρ).ρ h
            (inducedIdentityCopyProjection H (Rep.of V.ρ).ρ x)) ⊗ₜ[k]
          (W.ρ (h : G) w) := by
            rw [hproj]
      _ =
        (((Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ) h)
          ((TensorProduct.map
              (inducedIdentityCopyProjection H (Rep.of V.ρ).ρ)
              (LinearMap.id : W →ₗ[k] W))
            (x ⊗ₜ[k] w)) := by
              simp [Representation.tprod_apply]
  · intro z₁ z₂ hz₁ hz₂
    simpa [map_add, hz₁, hz₂]

/-- Helper for Theorem 17-17.2-4: the finite-index adjunction turns the restriction-side
unit-copy projection into a `G`-equivariant map back to the induced tensor source. -/
private noncomputable abbrev subgroupInduction_tensor_projection_hom_local
    (H : Subgroup G) (V : FDRep k H) (W : FDRep k G) :
    ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W) ⟶
      FDRep.subgroupInduction (k := k) (G := G)
        (V ⊗ fdRep_subgroupRestriction_local (G := G) H W) :=
  let _ : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  (FDRep.forget₂HomLinearEquiv _ _)
    ((Rep.resIndAdjunction k H).homEquiv
      (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)
      (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ)
      ((TensorProduct.map
          (inducedIdentityCopyProjection H (Rep.of V.ρ).ρ)
          (LinearMap.id : W →ₗ[k] W)).intertwiningMap_of_isIntertwiningMap
        (Rep.res H.subtype
          (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)).ρ
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ
        (subgroupInduction_tensor_projection_seed_isIntertwining_local
          (k := k) (G := G) H V W)))

/-- Helper for Theorem 17-17.2-4: after applying the forward Frobenius map and then the
restriction-side projection transpose, one recovers the `Res ⊣ Ind` counit on the induced tensor
source. -/
private theorem subgroupInduction_tensor_projection_counit_local
    (H : Subgroup G) (V : FDRep k H) (W : FDRep k G) :
    (Rep.resFunctor H.subtype).map
        ((forget₂
            (FDRep k G)
            (Rep k G)).map
          ((subgroupInduction_tensor_restriction_hom_local
            (k := k) (G := G) H V W) ≫
            (subgroupInduction_tensor_projection_hom_local
              (k := k) (G := G) H V W))) =
      (Rep.resIndAdjunction k H).counit.app
        (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) := by
  let _ : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  -- By adjunction naturality, it suffices to compare the restricted map with the explicit
  -- restriction-side seed on the standard induced generators.
  apply (Rep.resIndAdjunction k H).homEquiv.injective
  rw [(Rep.resIndAdjunction k H).homEquiv_counit
    (X := Rep.of
      (FDRep.subgroupInduction (k := k) (G := G)
        (V ⊗ fdRep_subgroupRestriction_local (G := G) H W)).ρ)
    (Y := Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ)
    (g := 𝟙 _)]
  ext g
  ext x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro v w
    by_cases hg : g ∈ H
    · let gh : H := ⟨g, hg⟩
      -- On the identity copy, the forward map contributes `g⁻¹` on `W`, and the projection
      -- removes the induced factor, leaving the standard counit formula.
      calc
        (((TensorProduct.map
              (inducedIdentityCopyProjection H (Rep.of V.ρ).ρ)
              (LinearMap.id : W →ₗ[k] W)).intertwiningMap_of_isIntertwiningMap
            (Rep.res H.subtype
              (Rep.of ((FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W).ρ)).ρ
            (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ).ρ
            (subgroupInduction_tensor_projection_seed_isIntertwining_local
              (k := k) (G := G) H V W)).hom
          (((Rep.resFunctor H.subtype).map
              ((forget₂
                  (FDRep k G)
                  (Rep k G)).map
                (subgroupInduction_tensor_restriction_hom_local
                  (k := k) (G := G) H V W))).hom
            (Representation.IndV.mk H.subtype
              (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) g
              (v ⊗ₜ[k] w))) =
          (((Rep.resIndAdjunction k H).counit.app
              (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ)).hom
            (Representation.IndV.mk H.subtype
              (Rep.of (V ⊗ fdRep_subgroupRestriction_local (G := G) H W).ρ) g
              (v ⊗ₜ[k] w))) := by
              simp [subgroupInduction_tensor_restriction_hom_apply_mk_local,
                induced_identity_copy_projection_apply_mk_mem_local,
                Rep.resIndAdjunction, gh]
    · -- Outside the identity copy, both the restriction-side projection and the counit vanish.
      simp [subgroupInduction_tensor_restriction_hom_apply_mk_local,
        induced_identity_copy_projection_apply_mk_of_not_mem, hg, Rep.resIndAdjunction]
  · intro x₁ x₂ hx₁ hx₂
    simp [map_add, hx₁, hx₂]
  · intro a x hx
    simp [hx]

/-- Helper for Theorem 17-17.2-4: subgroup induction commutes with tensoring by an ambient
representation after restricting that ambient factor to the subgroup. -/
private theorem fdRep_subgroupInduction_tensor_restriction_equiv_local
    (H : Subgroup G) (V : FDRep k H) (W : FDRep k G) :
    Nonempty
      (FDRep.subgroupInduction (k := k) (G := G)
          (V ⊗ fdRep_subgroupRestriction_local (G := G) H W) ≅
        (FDRep.subgroupInduction (k := k) (G := G) V) ⊗ W) := by
  -- Route correction: the local generator identities are now isolated in
  -- `subgroupInduction_tensor_source_mk_shift_local`,
  -- `subgroupInduction_tensor_target_action_mk_local`, and the adjunction-chosen forward map
  -- `subgroupInduction_tensor_restriction_hom_local`.
  --
  -- Route correction: the false explicit inverse seed has now been replaced by the genuine
  -- `Res ⊣ Ind` transpose of the restriction-side unit-copy projection.
  --
  -- The remaining closure is to turn the established left inverse
  -- `subgroupInduction_tensor_restriction_hom_local ≫
  --  subgroupInduction_tensor_projection_hom_local = 𝟙`
  -- into an isomorphism in `FDRep`; the proof frontier is now reduced to packaging that split
  -- mono as a finite-dimensional equivalence.
  sorry

/-- Helper for Theorem 17-17.2-4: subgroup induction satisfies LinearRepresentations_Serre_1977's projection formula on
Grothendieck classes once subgroup restriction is packaged on `R₀`. -/
private theorem finiteRep_subgroupInduction_mul_restriction_local
    (H : Subgroup G) (x : R₀[k](H)) (y : R₀[k](G)) :
    Representation.Subgroup.finiteRepGrothendieckGroupInduction k H
        (x * finiteRepGrothendieckGroupRestriction_local (G := G) (L := k) H y) =
      Representation.Subgroup.finiteRepGrothendieckGroupInduction k H x * y := by
  -- Reduce LinearRepresentations_Serre_1977's projection formula to generator classes `[V]₀` and `[W]₀`.
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · -- The zero subgroup class gives the trivial projection-formula identity.
    simp
  · intro V
    refine QuotientAddGroup.induction_on y ?_
    intro b
    refine FreeAbelianGroup.induction_on b ?_ ?_ ?_ ?_
    · -- The zero ambient class also reduces both sides to zero.
      simp
    · intro W
      -- On generator classes, the statement is exactly the induced-tensor equivalence.
      rw [finiteRepGrothendieckGroupRestriction_apply_class_local,
        finiteRepGrothendieckClass_mul,
        Representation.Subgroup.finiteRepGrothendieckGroupInduction_apply_class,
        Representation.Subgroup.finiteRepGrothendieckGroupInduction_apply_class,
        finiteRepGrothendieckClass_mul]
      exact
        finiteRepGrothendieckClass_eq_of_nonempty_iso
          (L := k) (G := G)
          (fdRep_subgroupInduction_tensor_restriction_equiv_local
            (k := k) (G := G) H V W)
    · intro b hb
      -- Both sides are additive homomorphisms in the ambient factor.
      simp [finiteRepGrothendieck_mul_neg, map_neg, hb]
    · intro b₁ b₂ hb₁ hb₂
      -- Distribute over ambient addition and reuse the induction hypotheses.
      simp [finiteRepGrothendieck_mul_add, map_add, hb₁, hb₂]
  · intro a ha
    -- Negation is preserved because subgroup induction and multiplication are additive.
    simp [finiteRepGrothendieck_neg_mul, map_neg, ha]
  · intro a₁ a₂ ha₁ ha₂
    -- The same additive descent closes the full subgroup-class statement.
    simp [finiteRepGrothendieck_add_mul, map_add, ha₁, ha₂]

/-- Helper for Theorem 17-17.2-4: in characteristic zero, the rationalized cyclic induction map
is already surjective. -/
private theorem cyclic_rationalized_induction_lsum_surjective_of_charZero [CharZero k] :
    Function.Surjective
      (cyclic_rationalized_induction_lsum k G) := by
  -- Route correction: reuse the already-closed characteristic-zero transport package and then
  -- identify its public cyclic owner with the normalized owner used in this file.
  simpa [cyclic_rationalized_induction_lsum,
    _root_.Representation.cyclic_rationalized_induction_lsum] using
    (_root_.Representation.cyclic_rationalized_induction_lsum_surjective_of_charZero
      (k := k) (G := G))

/-- Helper for Theorem 17-17.2-4: on a single cyclic summand, multiplying by the restricted
ambient class before induction matches multiplying the induced class by the ambient pure tensor. -/
private theorem cyclic_rationalized_induction_single_mul_restriction
    (H : _root_.Subgroup.cyclicSubgroups G)
    (z : RationalizedFiniteRepGrothendieck (k := k) H.1)
    (y : R₀[k](G)) :
    (cyclic_rationalized_induction_lsum k G)
        (DFinsupp.single H
          ((LinearMap.mulRight ℚ
              ((1 : ℚ) ⊗ₜ[ℤ]
                finiteRepGrothendieckGroupRestriction_local
                  (G := G) (L := k) H.1 y)) z)) =
      ((cyclic_rationalized_induction_lsum k G) (DFinsupp.single H z)) *
        (((1 : ℚ) ⊗ₜ[ℤ] y) : RationalizedFiniteRepGrothendieck (k := k) G) := by
  -- The target equality is linear in `z`, so it suffices to check it on pure tensors.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · simp [cyclic_rationalized_induction_lsum]
  · intro q x
    -- On pure tensors, base change reduces the statement to the integral projection formula.
    simp [cyclic_rationalized_induction_lsum,
      Subgroup.finiteRepGrothendieckGroupRationalizedInduction,
      LinearMap.baseChange_tmul, LinearMap.mulRight_apply,
      TensorProduct.tmul_mul_tmul,
      finiteRep_subgroupInduction_mul_restriction_local, mul_assoc]
  · intro z₁ z₂ hz₁ hz₂
    -- Both sides are additive in the cyclic summand.
    simp [hz₁, hz₂, add_mul, map_add]

/-- Helper for Theorem 17-17.2-4: componentwise multiplication by subgroup restrictions commutes
with the cyclic `DFinsupp` induction sum, up to ambient multiplication by `1 ⊗ y`. -/
private theorem cyclic_rationalized_induction_mapRange_mul_restriction
    (y : R₀[k](G)) :
    (cyclic_rationalized_induction_lsum k G).comp
        (DFinsupp.mapRange.linearMap fun H ↦
          LinearMap.mulRight ℚ
            (((1 : ℚ) ⊗ₜ[ℤ]
              finiteRepGrothendieckGroupRestriction_local
                (G := G) (L := k) H.1 y) :
                RationalizedFiniteRepGrothendieck (k := k) H.1)) =
      (LinearMap.mulRight ℚ
          (((1 : ℚ) ⊗ₜ[ℤ] y) :
            RationalizedFiniteRepGrothendieck (k := k) G)).comp
        (cyclic_rationalized_induction_lsum k G) := by
  -- Check the two linear maps on `DFinsupp.single` summands and then use `DFinsupp.lhom_ext`.
  apply DFinsupp.lhom_ext
  intro H z
  simpa [LinearMap.comp_apply] using
    cyclic_rationalized_induction_single_mul_restriction
      (k := k) (G := G) H z y

/-- Helper for Theorem 17-17.2-4: in positive characteristic, a nonzero integer multiple of the
trivial modular class is already hit by the cyclic-induction owner.

This is the fixed-unit descent step in LinearRepresentations_Serre_1977's proof: realize the `p`-regular zero extension of
the trivial modular character in characteristic zero, apply the ordinary cyclic theorem there, and
descend the resulting cyclic source back to `R₀[k](G)` componentwise. -/
private theorem cyclic_rationalized_unit_preimage_of_charZero_descent
    {K : Type u} [Field K] [CharZero K]
    (dG :
      (ℚ ⊗[ℤ] R₀[K](G)) →ₗ[ℚ]
        RationalizedFiniteRepGrothendieck (k := k) G)
    (dSource :
      ∀ H : _root_.Subgroup.cyclicSubgroups G,
        (ℚ ⊗[ℤ] R₀[K](H.1)) →ₗ[ℚ]
          RationalizedFiniteRepGrothendieck (k := k) H.1)
    (hcomm :
      ∀ ξ : Π₀ H : _root_.Subgroup.cyclicSubgroups G, ℚ ⊗[ℤ] R₀[K](H.1),
        (cyclic_rationalized_induction_lsum k G)
            ((DFinsupp.mapRange.linearMap dSource) ξ) =
          dG ((cyclic_rationalized_induction_lsum K G) ξ))
    (htriv :
      dG (((1 : ℚ) ⊗ₜ[ℤ]
          ([FDRep.of (Representation.trivial K G K)]₀ : R₀[K](G))) :
            ℚ ⊗[ℤ] R₀[K](G)) =
        ((1 : ℚ) ⊗ₜ[ℤ]
          ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)) :
            RationalizedFiniteRepGrothendieck (k := k) G)) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∃ ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
        (cyclic_rationalized_induction_lsum k G) ξ =
          (N : ℚ) •
            ((1 : ℚ) ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)) :
              RationalizedFiniteRepGrothendieck (k := k) G) := by
  rcases
      cyclic_rationalized_induction_lsum_surjective_of_charZero K G
        (((1 : ℚ) ⊗ₜ[ℤ]
          ([FDRep.of (Representation.trivial K G K)]₀ : R₀[K](G))) :
            ℚ ⊗[ℤ] R₀[K](G)) with
    ⟨ξK, hξK⟩
  refine ⟨1, one_ne_zero, (DFinsupp.mapRange.linearMap dSource) ξK, ?_⟩
  -- Descend LinearRepresentations_Serre_1977's characteristic-zero cyclic witness componentwise through the chosen
  -- decomposition square.
  calc
    (cyclic_rationalized_induction_lsum k G)
        ((DFinsupp.mapRange.linearMap dSource) ξK) =
      dG ((cyclic_rationalized_induction_lsum K G) ξK) := hcomm ξK
    _ =
        dG (((1 : ℚ) ⊗ₜ[ℤ]
          ([FDRep.of (Representation.trivial K G K)]₀ : R₀[K](G))) :
            ℚ ⊗[ℤ] R₀[K](G)) := by
          rw [hξK]
    _ =
        ((1 : ℚ) ⊗ₜ[ℤ]
          ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)) :
            RationalizedFiniteRepGrothendieck (k := k) G) := htriv
    _ =
        (1 : ℚ) •
          ((1 : ℚ) ⊗ₜ[ℤ]
            ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)) :
              RationalizedFiniteRepGrothendieck (k := k) G) := by
          simp

/-- Helper for Theorem 17-17.2-4: in positive characteristic, a nonzero integer multiple of the
trivial modular class is already hit by the cyclic-induction owner.

This is the fixed-unit descent step in LinearRepresentations_Serre_1977's proof: realize the `p`-regular zero extension of
the trivial modular character in characteristic zero, apply the ordinary cyclic theorem there, and
descend the resulting cyclic source back to `R₀[k](G)` componentwise. -/
private theorem cyclic_rationalized_unit_preimage_of_positive_char
    (hzero : ringChar k ≠ 0) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∃ ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
        (cyclic_rationalized_induction_lsum k G) ξ =
          (N : ℚ) •
            ((1 : ℚ) ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)) :
              RationalizedFiniteRepGrothendieck (k := k) G) := by
  -- Route correction: keep LinearRepresentations_Serre_1977's original fixed-unit descent rather than reopening the solved
  -- characteristic-zero transport layer in the main theorem file.
  let _ := hzero
  -- TODO: instantiate `cyclic_rationalized_unit_preimage_of_charZero_descent` with an actual
  -- mixed-characteristic package `(A, K, lift)` for the present field `k`, plus the componentwise
  -- decomposition square `d ∘ (ℚ ⊗ Ind) = (ℚ ⊗ Ind) ∘ ⊕ d_H`. The additive descent step is now
  -- available from the shared Chapter `16` bridge
  -- `Representation.decomposition_subgroupInduction_eq_subgroupInduction_decomposition_of_bridge`;
  -- the remaining blocker is the mixed-characteristic induced-stable-lattice witness on each
  -- cyclic summand, together with the trivial-class rewrite `d(1_K) = 1_k`.
  sorry

/-- Helper for Theorem 17-17.2-4: once the fixed-unit witness is known, multiplying each cyclic
summand by the subgroup restriction of `y` yields the corresponding witness for `N • (1 ⊗ y)`.

This is LinearRepresentations_Serre_1977's projection-formula step: compare the two targets on `PRegularConjClass G p`,
push the global factor through induction by `Ind_H^G(ψ * Res_H χ) = Ind_H^G(ψ) * χ`, and finish
by injectivity of the descended virtual modular character. -/
private theorem cyclic_rationalized_induction_mul_restriction_pureTensor
    (y : R₀[k](G))
    {N : ℕ} (hN : N ≠ 0)
    {ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G)}
    (hξ :
      (cyclic_rationalized_induction_lsum k G) ξ =
        (N : ℚ) •
          ((1 : ℚ) ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)) :
            RationalizedFiniteRepGrothendieck (k := k) G)) :
    ∃ ξ' : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
      (cyclic_rationalized_induction_lsum k G) ξ' =
        (N : ℚ) •
          ((1 : ℚ) ⊗ₜ[ℤ] y : RationalizedFiniteRepGrothendieck (k := k) G) := by
  -- Multiply each cyclic summand of the fixed-unit witness by the subgroup restriction of `y`.
  let ξ' :
      CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G) :=
    (DFinsupp.mapRange.linearMap fun H ↦
      LinearMap.mulRight ℚ
        (((1 : ℚ) ⊗ₜ[ℤ]
          finiteRepGrothendieckGroupRestriction_local
            (G := G) (L := k) H.1 y) :
            RationalizedFiniteRepGrothendieck (k := k) H.1)) ξ
  refine ⟨ξ', ?_⟩
  -- The packaged projection formula turns the componentwise multiplication into ambient
  -- multiplication by the pure tensor `1 ⊗ y`.
  calc
    (cyclic_rationalized_induction_lsum k G) ξ' =
        ((cyclic_rationalized_induction_lsum k G) ξ) *
          (((1 : ℚ) ⊗ₜ[ℤ] y) : RationalizedFiniteRepGrothendieck (k := k) G) := by
            simpa [ξ', LinearMap.comp_apply] using
              congrFun
                (cyclic_rationalized_induction_mapRange_mul_restriction
                  (k := k) (G := G) y) ξ
    _ =
        ((N : ℚ) •
          ((1 : ℚ) ⊗ₜ[ℤ] ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)) :
            RationalizedFiniteRepGrothendieck (k := k) G)) *
          (((1 : ℚ) ⊗ₜ[ℤ] y) : RationalizedFiniteRepGrothendieck (k := k) G) := by
            rw [hξ]
    _ =
        (N : ℚ) •
          ((((1 : ℚ) ⊗ₜ[ℤ]
              ([FDRep.of (Representation.trivial k G k)]₀ : R₀[k](G)) :
                RationalizedFiniteRepGrothendieck (k := k) G)) *
            (((1 : ℚ) ⊗ₜ[ℤ] y) : RationalizedFiniteRepGrothendieck (k := k) G)) := by
              rw [smul_mul_assoc]
    _ =
        (N : ℚ) •
          ((1 : ℚ) ⊗ₜ[ℤ] y : RationalizedFiniteRepGrothendieck (k := k) G) := by
            rw [TensorProduct.tmul_mul_tmul]
            simp [finiteRepGrothendieckClass_trivial_eq_one]

/-- Helper for Theorem 17-17.2-4: the only remaining ordinary-row branch is the positive-
characteristic pure-tensor step obtained from a cyclic unit witness. -/
private theorem cyclic_rationalized_pureTensor_preimage_of_nonzero_multiple_of_positive_char
    (y : R₀[k](G)) (hy : y ≠ 0) (hzero : ringChar k ≠ 0) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∃ ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
        (cyclic_rationalized_induction_lsum k G) ξ =
          (N : ℚ) •
            ((1 : ℚ) ⊗ₜ[ℤ] y :
              RationalizedFiniteRepGrothendieck (k := k) G) := by
  -- Route correction: isolate the positive-characteristic branch as its own theorem-local owner.
  -- The projective-row Cartan transport is now closed in the support files, so the remaining
  -- ordinary-row characteristic-zero transport is now closed by
  -- `cyclic_rationalized_induction_lsum_surjective_of_charZero`; the only remaining source-faithful
  -- work is the fixed-unit descent in positive characteristic.
  let _ := hy
  -- First invoke the source-faithful fixed-unit descent packaged in the support file.
  rcases cyclic_rationalized_unit_preimage_of_positive_char (k := k) (G := G) hzero with
    ⟨N, hN, ξ, hξ⟩
  -- Then multiply that cyclic unit witness by the subgroup restrictions of `y`.
  rcases cyclic_rationalized_induction_mul_restriction_pureTensor
      (k := k) (G := G) y hN hξ with
    ⟨ξ', hξ'⟩
  exact ⟨N, hN, ξ', hξ'⟩

/-- Helper for Theorem 17-17.2-4: every pure tensor in the rationalized modular Grothendieck
group is hit by the cyclic induction map up to a nonzero integer multiple. -/
lemma cyclic_rationalized_pureTensor_preimage_of_nonzero_multiple
    (y : R₀[k](G)) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∃ ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
        (cyclic_rationalized_induction_lsum k G) ξ =
          (N : ℚ) •
            ((1 : ℚ) ⊗ₜ[ℤ] y :
              RationalizedFiniteRepGrothendieck (k := k) G) := by
  by_cases hy : y = 0
  · -- Peel off the zero tensor first so the remaining blocker is only the nonzero target class.
    simpa [hy] using cyclic_rationalized_zero_pureTensor_preimage (k := k) (G := G)
  · by_cases hzero : ringChar k = 0
    · letI : CharZero k := (CharP.ringChar_zero_iff_CharZero (R := k)).mp hzero
      -- In characteristic zero, transport the already-proved Chapter `12` cyclic Artin induction
      -- theorem across the rationalized Grothendieck-character equivalence and take `N = 1`.
      rcases
          cyclic_rationalized_induction_lsum_surjective_of_charZero k G
            ((1 : ℚ) ⊗ₜ[ℤ] y) with
        ⟨ξ, hξ⟩
      refine ⟨1, one_ne_zero, ξ, ?_⟩
      simpa using hξ
    · -- The zero target and characteristic-zero branches are closed, so delegate the remaining
      -- positive-characteristic pure-tensor step to the theorem-local cyclic-unit descent owner.
      exact
        cyclic_rationalized_pureTensor_preimage_of_nonzero_multiple_of_positive_char
          (k := k) (G := G) y hy hzero

/-- Helper for Theorem 17-17.2-4: once the pure-tensor witness is known, scaling it by `q`
produces the corresponding witness for `q ⊗ y`. -/
lemma cyclic_rationalized_scalarTensor_preimage_of_nonzero_multiple
    (q : ℚ) (y : R₀[k](G))
    (hy : ∃ N : ℕ, N ≠ 0 ∧
      ∃ ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
        (cyclic_rationalized_induction_lsum k G) ξ =
          (N : ℚ) •
            ((1 : ℚ) ⊗ₜ[ℤ] y :
              RationalizedFiniteRepGrothendieck (k := k) G)) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∃ ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
        (cyclic_rationalized_induction_lsum k G) ξ =
          (N : ℚ) •
            ((q ⊗ₜ[ℤ] y : RationalizedFiniteRepGrothendieck (k := k) G)) := by
  rcases hy with ⟨N, hN, ξ, hξ⟩
  refine ⟨N, hN, q • ξ, ?_⟩
  -- The scalar can be pushed through the `DFinsupp` sum and then rewritten on the tensor factor.
  calc
    (cyclic_rationalized_induction_lsum k G) (q • ξ) =
        q • (cyclic_rationalized_induction_lsum k G) ξ := by
            rw [cyclic_rationalized_induction_lsum_smul (k := k) (G := G) q ξ]
    _ = q • ((N : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] y)) := by
          rw [hξ]
    _ = (q * (N : ℚ)) • ((1 : ℚ) ⊗ₜ[ℤ] y) := by
          rw [smul_smul]
    _ = ((q * (N : ℚ)) ⊗ₜ[ℤ] y) := by
          simp [TensorProduct.smul_tmul']
    _ = (N : ℚ) • (q ⊗ₜ[ℤ] y) := by
          rw [TensorProduct.smul_tmul']
          simp [mul_comm]

/-- Helper for Theorem 17-17.2-4: witnesses for `x` and `y` combine into a witness for `x + y`
after clearing the two nonzero integer multiples simultaneously. -/
lemma cyclic_rationalized_add_preimage_of_nonzero_multiple
    {x y : RationalizedFiniteRepGrothendieck (k := k) G}
    (hx : ∃ N : ℕ, N ≠ 0 ∧
      ∃ ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
        (cyclic_rationalized_induction_lsum k G) ξ =
          (N : ℚ) • x)
    (hy : ∃ N : ℕ, N ≠ 0 ∧
      ∃ ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
        (cyclic_rationalized_induction_lsum k G) ξ =
          (N : ℚ) • y) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∃ ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
        (cyclic_rationalized_induction_lsum k G) ξ =
          (N : ℚ) • (x + y) := by
  rcases hx with ⟨Nx, hNx, ξx, hξx⟩
  rcases hy with ⟨Ny, hNy, ξy, hξy⟩
  let N := Nx * Ny
  refine ⟨N, Nat.mul_ne_zero hNx hNy, (Ny : ℚ) • ξx + (Nx : ℚ) • ξy, ?_⟩
  -- Multiply each witness by the other denominator, then add the resulting identities.
  calc
    (cyclic_rationalized_induction_lsum k G)
        ((Ny : ℚ) • ξx + (Nx : ℚ) • ξy)
        =
          (Ny : ℚ) •
              (cyclic_rationalized_induction_lsum k G) ξx +
            (Nx : ℚ) •
              (cyclic_rationalized_induction_lsum k G) ξy := by
            rw [cyclic_rationalized_induction_lsum_add (k := k) (G := G)
              ((Ny : ℚ) • ξx) ((Nx : ℚ) • ξy)]
            rw [cyclic_rationalized_induction_lsum_smul (k := k) (G := G) (Ny : ℚ) ξx]
            rw [cyclic_rationalized_induction_lsum_smul (k := k) (G := G) (Nx : ℚ) ξy]
    _ = (Ny : ℚ) • ((Nx : ℚ) • x) + (Nx : ℚ) • ((Ny : ℚ) • y) := by
          rw [hξx, hξy]
    _ = ((N : ℕ) : ℚ) • (x + y) := by
          simp [N, smul_add, smul_smul, mul_comm]

/-- Helper for Theorem 17-17.2-4: every rationalized modular Grothendieck class is hit by the
cyclic induction map up to a nonzero integer multiple. -/
lemma cyclic_rationalized_finite_rep_induction_hits_nonzero_multiple
    (x : RationalizedFiniteRepGrothendieck (k := k) G) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∃ ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
        (cyclic_rationalized_induction_lsum k G) ξ =
          (N : ℚ) • x := by
  -- Once the pure-tensor case is isolated, the full rationalized statement is formal tensor
  -- induction.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · refine ⟨1, one_ne_zero, 0, ?_⟩
    simp
  · intro q y
    exact
      cyclic_rationalized_scalarTensor_preimage_of_nonzero_multiple (k := k) (G := G) q y
        (cyclic_rationalized_pureTensor_preimage_of_nonzero_multiple (k := k) (G := G) y)
  · intro x y hx hy
    exact cyclic_rationalized_add_preimage_of_nonzero_multiple (k := k) (G := G) hx hy

/-- Helper for Theorem 17-17.2-4: the pure-tensor fixed-multiple descent already gives
surjectivity of the whole rationalized cyclic-induction map, because every tensor is built from
`0`, pure tensors, and addition. -/
private theorem cyclic_rationalized_finite_rep_induction_surjective_of_pureTensor
    (hpure :
      ∀ y : R₀[k](G),
        ∃ N : ℕ, N ≠ 0 ∧
          ∃ ξ : CyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G),
            (cyclic_rationalized_induction_lsum k G) ξ =
              (N : ℚ) •
                ((1 : ℚ) ⊗ₜ[ℤ] y :
                  RationalizedFiniteRepGrothendieck (k := k) G)) :
    Function.Surjective
      (cyclic_rationalized_induction_lsum k G) := by
  -- First lift the pure-tensor hypothesis to arbitrary tensors by the same tensor induction used
  -- in the main source route.
  refine surjective_of_exists_nat_smul_preimage
    (cyclic_rationalized_induction_lsum k G) ?_
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · refine ⟨1, one_ne_zero, 0, ?_⟩
    simp
  · intro q y
    exact
      cyclic_rationalized_scalarTensor_preimage_of_nonzero_multiple (k := k) (G := G) q y
        (hpure y)
  · intro x y hx hy
    exact cyclic_rationalized_add_preimage_of_nonzero_multiple (k := k) (G := G) hx hy

/-- Theorem 17-17.2-4 (1): if `T` is the set of cyclic subgroups of `G`, then the induction map
`ℚ ⊗ Ind : ⨁_{H ∈ T} (ℚ ⊗ R_k(H)) → ℚ ⊗ R_k(G)` is surjective; in Lean the direct sum is
realized as a `DFinsupp` over the canonical finite family `Subgroup.cyclicSubgroups G`. -/
theorem cyclicSubgroupRationalizedFiniteRepGrothendieckInduction_surjective :
    Function.Surjective
      (cyclic_rationalized_induction_lsum k G) := by
  -- Route correction: the source proof reduces surjectivity to the pure-tensor descent step, so
  -- package that tensor-induction reduction explicitly and keep the remaining blocker isolated in
  -- `cyclic_rationalized_pureTensor_preimage_of_nonzero_multiple`.
  exact
    cyclic_rationalized_finite_rep_induction_surjective_of_pureTensor (k := k) (G := G)
      (cyclic_rationalized_pureTensor_preimage_of_nonzero_multiple (k := k) (G := G))

end OrdinaryRow

section ProjectiveRow

variable (k : Type u) [Field k]
variable (G : Type u) [Group G] [Finite G]

local instance projective_finiteProjectiveGrothendieckAddCommMonoid
    (H : Type u) [Group H] [Finite H] : AddCommMonoid (P₀[k](H)) :=
  (QuotientAddGroup.Quotient.addCommGroup
    (finiteProjectiveGroupAlgebraGrothendieckRelations k H)).toAddCommMonoid

local instance projective_finiteProjectiveGrothendieckAddCommGroup
    (H : Type u) [Group H] [Finite H] : AddCommGroup (P₀[k](H)) :=
  QuotientAddGroup.Quotient.addCommGroup
    (finiteProjectiveGroupAlgebraGrothendieckRelations k H)

local instance projective_finiteProjectiveGrothendieckIntModule
    (H : Type u) [Group H] [Finite H] : Module ℤ (P₀[k](H)) :=
  AddCommGroup.toIntModule (P₀[k](H))

local instance projective_finiteRepGrothendieckAddCommMonoid
    (H : Type u) [Group H] [Finite H] : AddCommMonoid (R₀[k](H)) :=
  (QuotientAddGroup.Quotient.addCommGroup
    (finiteRepGrothendieckRelations k H)).toAddCommMonoid

local instance projective_finiteRepGrothendieckAddCommGroup
    (H : Type u) [Group H] [Finite H] : AddCommGroup (R₀[k](H)) :=
  QuotientAddGroup.Quotient.addCommGroup
    (finiteRepGrothendieckRelations k H)

local instance projective_finiteRepGrothendieckIntModule
    (H : Type u) [Group H] [Finite H] : Module ℤ (R₀[k](H)) :=
  AddCommGroup.toIntModule (R₀[k](H))

/-- Helper for Theorem 17-17.2-4: the canonical `p`-part/prime-to-`p` factorization of
`Nat.card G` coming from `ordProj` and `ordCompl`. -/
private theorem card_eq_ordProj_mul_ordCompl_and_coprime
    {p : ℕ} [CharP k p] [Fact p.Prime] :
    let n := Nat.factorization (Nat.card G) p
    let m := ordCompl[p] (Nat.card G)
    Nat.card G = p ^ n * m ∧ Nat.Coprime p m := by
  -- Expand the standard `ordProj`/`ordCompl` decomposition of `Nat.card G`.
  dsimp
  constructor
  · simpa using (Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) p).symm
  · simpa using Nat.coprime_ordCompl (Fact.out : Nat.Prime p) Nat.card_pos.ne'

/-- Helper for Theorem 17-17.2-4: in characteristic zero, every finite-dimensional class comes
from an actual finite projective class under the Cartan map. -/
private theorem exists_projective_preimage_of_fdrep_charZero [CharZero k] (V : FDRep k G) :
    ∃ P : FiniteProjectiveGroupAlgebraModule k G, cartanHom k G [P]ₚ₀ = [V]₀ := by
  -- Route correction: reuse Maschke semisimplicity on the honest finite-dimensional owner before
  -- descending to the Grothendieck quotient.
  let ρ : Rep k G := (forget₂ (FDRep k G) (Rep k G)).obj V
  let W0 : ModuleCat k[G] := Rep.toModuleMonoidAlgebra.obj ρ
  let _ : Module k W0 := Module.compHom W0 (algebraMap k k[G])
  let _ : IsScalarTower k k[G] W0 := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hρfinite : Module.Finite k ρ := by
    simpa [ρ] using (show Module.Finite k V from inferInstance)
  let f : ρ →ₗ[k] W0 :=
    { toFun := ρ.ρ.asModuleEquiv.symm
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        change ρ.ρ.asModuleEquiv.symm (r • x) = ((algebraMap k k[G]) r) • ρ.ρ.asModuleEquiv.symm x
        exact ρ.ρ.asModuleEquiv_symm_map_smul r x }
  let _ : Module.Finite k W0 :=
    Module.Finite.of_surjective f fun y : W0 ↦ ⟨ρ.ρ.asModuleEquiv y, by rfl⟩
  let _ : Module.Finite k[G] W0 := Module.Finite.of_restrictScalars_finite k k[G] W0
  let W : FGModuleCat k[G] := by
    refine ⟨W0, ?_⟩
    change Module.Finite k[G] W0
    infer_instance
  letI : NeZero (Nat.card G : k) := by
    refine ⟨Nat.cast_ne_zero.mpr ?_⟩
    exact (Nat.card_ne_zero).2 ⟨inferInstance, inferInstance⟩
  have hproj : Module.Projective k[G] W := by
    -- Maschke makes the underlying finite `k[G]`-module projective.
    change Module.Projective k[G] W0
    exact Module.projective_of_isSemisimpleRing _ _
  let P : FiniteProjectiveGroupAlgebraModule k G := ⟨W, hproj⟩
  refine ⟨P, ?_⟩
  rw [cartanHom_projectiveClass_eq]
  let σ := P.toFiniteRep
  let eRep :
      ((forget₂ (FDRep k G) (Rep k G)).obj σ) ≅
        ((forget₂ (FDRep k G) (Rep k G)).obj V) := by
    simpa [σ, P, W, W0, ρ, FiniteProjectiveGroupAlgebraModule.toFiniteRep] using
      (Rep.unitIso ρ).symm
  let e : σ ≅ V := by
    refine ⟨(FDRep.forget₂HomLinearEquiv σ V) eRep.hom,
      (FDRep.forget₂HomLinearEquiv V σ) eRep.inv, ?_, ?_⟩
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.hom ≫ eRep.inv = 𝟙 _
      exact eRep.hom_inv_id
    · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
      change eRep.inv ≫ eRep.hom = 𝟙 _
      exact eRep.inv_hom_id
  -- The projective model is isomorphic to `V`, so it defines the same Grothendieck class.
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) ⟨e⟩

/-- Helper for Theorem 17-17.2-4: in characteristic zero the Cartan range is all of the ordinary
Grothendieck group. -/
private theorem cartan_range_eq_top_of_charZero [CharZero k] :
    (cartanHom k G).range = ⊤ := by
  -- Reduce the quotient owner to honest finite-dimensional generators and replace each one by its
  -- projective Maschke model.
  rw [AddMonoidHom.range_eq_top]
  intro x
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro V
    rcases exists_projective_preimage_of_fdrep_charZero (k := k) (G := G) V with ⟨P, hP⟩
    exact ⟨[P]ₚ₀, hP⟩
  · intro a ha
    rcases ha with ⟨y, hy⟩
    exact ⟨-y, by simpa [hy]⟩
  · intro a b ha hb
    rcases ha with ⟨ya, hya⟩
    rcases hb with ⟨yb, hyb⟩
    exact ⟨ya + yb, by simpa [map_add, hya, hyb]⟩

/-- Helper for Theorem 17-17.2-4: the integral Cartan map viewed as a `ℤ`-linear map. -/
private abbrev integral_cartan_linearMap :=
  (cartanHom k G).toIntLinearMap

/-- Helper for Theorem 17-17.2-4: the rationalized Cartan map as the literal base change of the
integral Cartan homomorphism. -/
private abbrev rationalized_cartan_linearMap :=
  (integral_cartan_linearMap (k := k) (G := G)).baseChange ℚ

/-- Helper for Theorem 17-17.2-4: a pure tensor of an integral multiple rewrites as the same
integral multiple of the corresponding rationalized pure tensor. -/
private theorem tmul_nsmul_eq_nsmul_tmul
    (q : ℚ) (y : R₀[k](G)) (N : ℕ) :
    q ⊗ₜ[ℤ] (N • y) = (N : ℚ) • (q ⊗ₜ[ℤ] y) := by
  induction N with
  | zero =>
      -- The zero multiple gives the zero tensor on both sides.
      simp
  | succ N ih =>
      -- Peel off one copy of `y` and rewrite the remaining multiple by the induction hypothesis.
      rw [succ_nsmul, TensorProduct.tmul_add, ih, Nat.cast_add, Nat.cast_one, add_smul, one_smul]

/-- Helper for Theorem 17-17.2-4: the tensorized Cartan map hits a nonzero integer multiple of
every rationalized ordinary Grothendieck class. -/
private theorem rationalized_cartan_hits_nonzero_multiple
    (x : ℚ ⊗[ℤ] R₀[k](G)) :
    ∃ N : ℕ, N ≠ 0 ∧
      ∃ y : ℚ ⊗[ℤ] P₀[k](G),
        rationalized_cartan_linearMap (k := k) (G := G) y = (N : ℚ) • x := by
  by_cases hchar0 : ringChar k = 0
  · letI : CharZero k := (CharP.ringChar_zero_iff_CharZero (R := k)).mp hchar0
    have hrange : (cartanHom k G).range = ⊤ :=
      cartan_range_eq_top_of_charZero (k := k) (G := G)
    have hsurj : Function.Surjective (integral_cartan_linearMap (k := k) (G := G)) := by
      -- In characteristic zero the integral Cartan map is already onto, so its rationalization
      -- hits the target exactly with multiplier `1`.
      rw [AddMonoidHom.range_eq_top] at hrange
      intro y
      rcases hrange y with ⟨z, hz⟩
      exact ⟨z, by simpa [integral_cartan_linearMap] using hz⟩
    have hsurjQ :
        Function.Surjective (rationalized_cartan_linearMap (k := k) (G := G)) := by
      -- Tensoring a surjective integral map with `ℚ` keeps it surjective.
      simpa [rationalized_cartan_linearMap, LinearMap.baseChange_eq_ltensor] using
        (LinearMap.lTensor_surjective (Q := ℚ) hsurj)
    rcases hsurjQ x with ⟨y, hy⟩
    exact ⟨1, one_ne_zero, y, by simpa using hy⟩
  · let p := ringChar k
    letI : CharP k p := ringChar.charP (R := k)
    have hp_ne_zero : p ≠ 0 := hchar0
    have hp_two_le : 2 ≤ p := by
      have hp_ne_one : p ≠ 1 := CharP.char_ne_one k p
      omega
    letI : Fact p.Prime := ⟨CharP.char_is_prime_of_two_le k p hp_two_le⟩
    let n := Nat.factorization (Nat.card G) p
    let m := ordCompl[p] (Nat.card G)
    have hcard_hm := card_eq_ordProj_mul_ordCompl_and_coprime (k := k) (G := G) (p := p)
    -- In positive characteristic, LinearRepresentations_Serre_1977's source route provides one fixed `p`-power multiple of
    -- every integral target class inside the Cartan image; tensor induction lifts that to `ℚ`.
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · refine ⟨1, one_ne_zero, 0, ?_⟩
      simp [rationalized_cartan_linearMap]
    · intro q y
      have hrange :
          (p ^ n) • y ∈ (cartanHom k G).range := by
        simpa [n, m] using
          (cartanHom_surjective_on_p_part_multiples
            (p := p) (k := k) (G := G) n m hcard_hm.1 hcard_hm.2 y)
      rcases hrange with ⟨z, hz⟩
      refine ⟨p ^ n, pow_ne_zero _ (Nat.Prime.ne_zero Fact.out), q ⊗ₜ[ℤ] z, ?_⟩
      calc
        rationalized_cartan_linearMap (k := k) (G := G) (q ⊗ₜ[ℤ] z) =
            q ⊗ₜ[ℤ] integral_cartan_linearMap (k := k) (G := G) z := by
              rw [rationalized_cartan_linearMap, LinearMap.baseChange_tmul]
        _ = q ⊗ₜ[ℤ] cartanHom k G z := by
              simp [integral_cartan_linearMap]
        _ = q ⊗ₜ[ℤ] ((p ^ n) • y) := by
              rw [hz]
        _ = (((p ^ n : ℕ) : ℚ)) • (q ⊗ₜ[ℤ] y) := by
              exact tmul_nsmul_eq_nsmul_tmul (k := k) (G := G) q y (p ^ n)
    · intro x y hx hy
      rcases hx with ⟨Nx, hNx, ξx, hξx⟩
      rcases hy with ⟨Ny, hNy, ξy, hξy⟩
      let N := Nx * Ny
      refine ⟨N, Nat.mul_ne_zero hNx hNy, (Ny : ℚ) • ξx + (Nx : ℚ) • ξy, ?_⟩
      -- Clear the two fixed multiples simultaneously and then add the resulting identities.
      calc
        rationalized_cartan_linearMap (k := k) (G := G)
            ((Ny : ℚ) • ξx + (Nx : ℚ) • ξy) =
              (Ny : ℚ) • rationalized_cartan_linearMap (k := k) (G := G) ξx +
                (Nx : ℚ) • rationalized_cartan_linearMap (k := k) (G := G) ξy := by
                  rw [map_add, map_smul, map_smul]
        _ = (Ny : ℚ) • ((Nx : ℚ) • x) + (Nx : ℚ) • ((Ny : ℚ) • y) := by
              rw [hξx, hξy]
        _ = ((N : ℕ) : ℚ) • (x + y) := by
              simp [N, smul_add, smul_smul, mul_comm]

/-- Helper for Theorem 17-17.2-4: the tensorized Cartan map is bijective over `ℚ`. -/
private theorem rationalized_cartan_linearMap_bijective :
    Function.Bijective (rationalized_cartan_linearMap (k := k) (G := G)) := by
  refine ⟨?_, ?_⟩
  · -- Injectivity survives base change because `ℚ` is flat over `ℤ`.
    simpa [rationalized_cartan_linearMap, LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap
        (M := ℚ) (integral_cartan_linearMap (k := k) (G := G))
        (by simpa [integral_cartan_linearMap] using (cartanHom_injective (k := k) (G := G))))
  · -- Surjectivity follows from the fixed-multiple witness and division by that nonzero integer.
    exact
      surjective_of_exists_nat_smul_preimage
        (rationalized_cartan_linearMap (k := k) (G := G))
        (rationalized_cartan_hits_nonzero_multiple (k := k) (G := G))

/-- Helper for Theorem 17-17.2-4: the rationalized Cartan map viewed only as the tensorized
integral Cartan homomorphism. -/
private noncomputable abbrev rationalizedCartanLinearEquiv :
    (ℚ ⊗[ℤ] P₀[k](G)) ≃ₗ[ℚ] ℚ ⊗[ℤ] R₀[k](G) :=
  -- Package the rationalized Cartan map as the actual base-changed linear map together with its
  -- explicit bijectivity proof.
  LinearEquiv.ofBijective
    (rationalized_cartan_linearMap (k := k) (G := G))
    (rationalized_cartan_linearMap_bijective (k := k) (G := G))

/-- Helper for Theorem 17-17.2-4: the rationalized Cartan equivalence acts on pure tensors by the
tensorized integral Cartan map. -/
private theorem rationalizedCartanLinearEquiv_apply_tmul
    (q : ℚ) (x : P₀[k](G)) :
    rationalizedCartanLinearEquiv (k := k) (G := G) (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] cartanHom k G x := by
  -- The equivalence was defined from the base-changed Cartan map, so the pure-tensor formula is
  -- exactly the standard `baseChange_tmul` computation.
  calc
    rationalizedCartanLinearEquiv (k := k) (G := G) (q ⊗ₜ[ℤ] x) =
        q ⊗ₜ[ℤ] integral_cartan_linearMap (k := k) (G := G) x := by
          simpa [rationalizedCartanLinearEquiv] using
            (LinearMap.baseChange_tmul
              (f := integral_cartan_linearMap (k := k) (G := G)) (A := ℚ) q x)
    _ = q ⊗ₜ[ℤ] cartanHom k G x := by
          simp [integral_cartan_linearMap]

/-- Helper for Theorem 17-17.2-4: the normalized rationalized owner for `P₀[k](H)`. -/
private abbrev RationalizedFiniteProjectiveGrothendieck
    (H : Type u) [Group H] [Finite H] :=
  @TensorProduct ℤ Int.instCommSemiring ℚ P₀[k](H) Rat.addCommMonoid
    (projective_finiteProjectiveGrothendieckAddCommMonoid (k := k) H)
    (AddCommGroup.toIntModule ℚ)
    (projective_finiteProjectiveGrothendieckIntModule (k := k) H)

/-- Helper for Theorem 17-17.2-4: the normalized rationalized owner for `R₀[k](H)` in the
projective-row transport square. -/
private abbrev ProjectiveRowRationalizedFiniteRepGrothendieck
    (H : Type u) [Group H] [Finite H] :=
  @TensorProduct ℤ Int.instCommSemiring ℚ R₀[k](H) Rat.addCommMonoid
    (projective_finiteRepGrothendieckAddCommMonoid (k := k) H)
    (AddCommGroup.toIntModule ℚ)
    (projective_finiteRepGrothendieckIntModule (k := k) H)

/-- Helper for Theorem 17-17.2-4: the normalized cyclic direct-sum source for the projective
row. -/
private abbrev CyclicRationalizedFiniteProjectiveGrothendieckSource :=
  Π₀ H : _root_.Subgroup.cyclicSubgroups G,
    RationalizedFiniteProjectiveGrothendieck (k := k) H.1

/-- Helper for Theorem 17-17.2-4: the normalized ordinary-row target owner appearing in the
projective Cartan transport square. -/
private abbrev ProjectiveRowCyclicRationalizedFiniteRepGrothendieckSource :=
  Π₀ H : _root_.Subgroup.cyclicSubgroups G,
    ProjectiveRowRationalizedFiniteRepGrothendieck (k := k) H.1

local instance : DecidableEq ↥(_root_.Subgroup.cyclicSubgroups G) :=
  Classical.decEq _

/-- Helper for Theorem 17-17.2-4: the projective-row cyclic-induction `DFinsupp` sum. -/
private abbrev cyclic_rationalized_projective_induction_lsum :
    CyclicRationalizedFiniteProjectiveGrothendieckSource (k := k) (G := G) →ₗ[ℚ]
      RationalizedFiniteProjectiveGrothendieck (k := k) G :=
  DFinsupp.lsum ℚ fun H : _root_.Subgroup.cyclicSubgroups G ↦
    (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction
      (k := k) (G := G) H.1 :
      (ℚ ⊗[ℤ] P₀[k](H.1)) →ₗ[ℚ] ℚ ⊗[ℤ] P₀[k](G))

/-- Helper for Theorem 17-17.2-4: surjectivity transports across a conjugating pair of linear
equivalences. -/
private theorem surjective_of_linear_equiv_conjugate
    {V W V' W' : Type u}
    [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    [AddCommGroup V'] [Module ℚ V']
    [AddCommGroup W'] [Module ℚ W']
    (eV : V ≃ₗ[ℚ] V')
    (eW : W ≃ₗ[ℚ] W')
    (f : V →ₗ[ℚ] W)
    (g : V' →ₗ[ℚ] W')
    (hconj : eW.toLinearMap.comp f = g.comp eV.toLinearMap)
    (hg : Function.Surjective g) :
    Function.Surjective f := by
  intro w
  rcases hg (eW w) with ⟨v', hv'⟩
  refine ⟨eV.symm v', ?_⟩
  -- Apply the conjugation identity to the chosen ordinary-row preimage and then cancel `eW`.
  apply eW.injective
  calc
    eW (f (eV.symm v')) = g (eV (eV.symm v')) := by
      simpa using LinearMap.congr_fun hconj (eV.symm v')
    _ = g v' := by
      simp
    _ = eW w := hv'

/-- Helper for Theorem 17-17.2-4: the subgroupwise rationalized Cartan equivalences assemble to a
single `DFinsupp` source equivalence. -/
private abbrev cyclic_rationalized_projective_source_cartan_equiv :
    CyclicRationalizedFiniteProjectiveGrothendieckSource (k := k) (G := G) ≃ₗ[ℚ]
      ProjectiveRowCyclicRationalizedFiniteRepGrothendieckSource (k := k) (G := G) :=
  DFinsupp.mapRange.linearEquiv fun H ↦
    rationalizedCartanLinearEquiv (k := k) (G := H.1)

/-- Helper for Theorem 17-17.2-4: the Chapter `16` projective subgroup-induction owner agrees
with the public induction map on `P₀`. -/
private theorem projective_subgroupInduction_eq_public
    (H : Subgroup G) :
    projective_subgroupInduction (k := k) (G := G) H =
      Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction k H := by
  -- Both projective induction owners are quotient lifts with the same values on generator classes.
  apply AddMonoidHom.ext
  intro x
  refine QuotientAddGroup.induction_on x ?_
  intro a
  refine FreeAbelianGroup.induction_on a ?_ ?_ ?_ ?_
  · simp [projective_subgroupInduction,
      Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction]
  · intro P
    change
      projective_subgroupInduction (k := k) (G := G) H [P]ₚ₀ =
        Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction k H [P]ₚ₀
    rw [projective_subgroupInduction_apply_class,
      Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction_apply_class]
  · intro a ha
    simpa [map_neg] using congrArg Neg.neg ha
  · intro a b ha hb
    simpa [map_add] using congrArg₂ HAdd.hAdd ha hb

/-- Helper for Theorem 17-17.2-4: on a single cyclic summand, the projective induction square
commutes after transporting by the rationalized Cartan maps. -/
private theorem rationalized_cartan_cyclic_induction_commutes_on_single
    (H : _root_.Subgroup.cyclicSubgroups G)
    (x : RationalizedFiniteProjectiveGrothendieck (k := k) H.1) :
    (rationalizedCartanLinearEquiv (k := k) (G := G))
        ((cyclic_rationalized_projective_induction_lsum k G) (DFinsupp.single H x)) =
      (cyclic_rationalized_induction_lsum k G)
        ((cyclic_rationalized_projective_source_cartan_equiv (k := k) (G := G))
          (DFinsupp.single H x)) := by
  -- Normalize the rationalized projective summand by tensor induction, so the Cartan square is
  -- proved first on pure tensors and then extended additively.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [cyclic_rationalized_projective_induction_lsum,
      cyclic_rationalized_projective_source_cartan_equiv]
  · intro q y
    -- On a pure tensor, both sides are the base change of the integral Cartan/induction square.
    calc
      (rationalizedCartanLinearEquiv (k := k) (G := G))
          ((cyclic_rationalized_projective_induction_lsum k G)
            (DFinsupp.single H (q ⊗ₜ[ℤ] y))) =
        q ⊗ₜ[ℤ]
          (cartanHom k G
            (Representation.Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupInduction
              k H.1 y)) := by
              simp [cyclic_rationalized_projective_induction_lsum,
                Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction,
                LinearMap.baseChange_tmul]
      _ =
        q ⊗ₜ[ℤ]
          (finiteRep_subgroupInduction (k := k) (G := G) H.1
            (cartanHom k H.1 y)) := by
              -- Rewrite the public projective induction owner to the Chapter `16` Cartan owner.
              rw [← projective_subgroupInduction_eq_public (k := k) (G := G) H.1]
              rw [cartanHom_subgroupInduction_eq_subgroupInduction_cartanHom
                (k := k) (G := G) (H := H.1) y]
      _ =
        (cyclic_rationalized_induction_lsum k G)
          ((cyclic_rationalized_projective_source_cartan_equiv (k := k) (G := G))
            (DFinsupp.single H (q ⊗ₜ[ℤ] y))) := by
              simp [cyclic_rationalized_projective_source_cartan_equiv,
                cyclic_rationalized_induction_lsum,
                Subgroup.finiteRepGrothendieckGroupRationalizedInduction,
                LinearMap.baseChange_tmul,
                finiteRep_subgroupInduction_eq_public (k := k) (G := G) (H := H.1)]
  · intro x y hx hy
    -- Additivity of the transport square lets the pure-tensor proof extend to all tensors.
    simpa [map_add] using congrArg₂ HAdd.hAdd hx hy

/-- Helper for Theorem 17-17.2-4: once the Cartan square is written on the explicit `DFinsupp`
owners, the projective row is a formal transport of the ordinary row. -/
private theorem cyclic_rationalized_projective_induction_surjective_of_cartan_square
    (hsquare :
      (rationalizedCartanLinearEquiv (k := k) (G := G)).toLinearMap.comp
          (cyclic_rationalized_projective_induction_lsum k G) =
        (cyclic_rationalized_induction_lsum k G).comp
          (cyclic_rationalized_projective_source_cartan_equiv (k := k) (G := G)).toLinearMap) :
    Function.Surjective
      (cyclic_rationalized_projective_induction_lsum k G) := by
  -- This is exactly LinearRepresentations_Serre_1977's source route: conjugate projective induction by Cartan to ordinary
  -- induction, then reuse the already-proved ordinary-row surjectivity.
  exact
    surjective_of_linear_equiv_conjugate
      (eV := cyclic_rationalized_projective_source_cartan_equiv (k := k) (G := G))
      (eW := rationalizedCartanLinearEquiv (k := k) (G := G))
      (f := cyclic_rationalized_projective_induction_lsum k G)
      (g := cyclic_rationalized_induction_lsum k G)
      hsquare
      (cyclicSubgroupRationalizedFiniteRepGrothendieckInduction_surjective (k := k) (G := G))

/-- Helper for Theorem 17-17.2-4: once the rationalized Cartan square for cyclic induction is
available, the projective row is just the ordinary row conjugated by the Cartan equivalence. -/
private theorem cyclic_rationalized_projective_induction_surjective_via_cartan_transport :
    Function.Surjective
      (cyclic_rationalized_projective_induction_lsum k G) := by
  -- Route correction: the source proof does not reprove the projective row independently.
  -- The formal conjugation step is now isolated; verify the Cartan square on each
  -- `DFinsupp.single` generator and then use `DFinsupp.lhom_ext`.
  have hsquare :
      (rationalizedCartanLinearEquiv (k := k) (G := G)).toLinearMap.comp
          (cyclic_rationalized_projective_induction_lsum k G) =
        (cyclic_rationalized_induction_lsum k G).comp
          (cyclic_rationalized_projective_source_cartan_equiv (k := k) (G := G)).toLinearMap
    := by
      apply DFinsupp.lhom_ext
      intro H x
      -- Reduce the global square to the already verified single-summand Cartan/induction square.
      simpa [LinearMap.comp_apply] using
        rationalized_cartan_cyclic_induction_commutes_on_single (k := k) (G := G) H x
  exact
    cyclic_rationalized_projective_induction_surjective_of_cartan_square
      (k := k) (G := G) hsquare

/-- Theorem 17-17.2-4 (2): if `T` is the set of cyclic subgroups of `G`, then the induction map
`ℚ ⊗ Ind : ⨁_{H ∈ T} (ℚ ⊗ P_k(H)) → ℚ ⊗ P_k(G)` is surjective; in Lean the direct sum is
realized as a `DFinsupp` over the canonical finite family `Subgroup.cyclicSubgroups G`. -/
  theorem cyclicSubgroupRationalizedFiniteProjectiveRepGrothendieckInduction_surjective :
    Function.Surjective
      (DFinsupp.lsum ℚ fun H : _root_.Subgroup.cyclicSubgroups G ↦
        (Subgroup.finiteProjectiveGroupAlgebraGrothendieckGroupRationalizedInduction
          (k := k) (G := G) H.1 :
          RationalizedFiniteProjectiveGrothendieck (k := k) H.1 →ₗ[ℚ]
            RationalizedFiniteProjectiveGrothendieck (k := k) G)) := by
  -- Reduce the textbook theorem to the theorem-local Cartan transport frontier.
  simpa [cyclic_rationalized_projective_induction_lsum] using
    cyclic_rationalized_projective_induction_surjective_via_cartan_transport
      (k := k) (G := G)

end ProjectiveRow

end Representation
