import Mathlib.GroupTheory.Index
import LinearRepresentations_Serre_1977.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.FixedIsotypicCoverAction

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
variable [IsAlgClosed (IsLocalRing.ResidueField A)]

local notation "k" => IsLocalRing.ResidueField A
private noncomputable instance theorem171761TargetModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance theorem171761TargetScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: the data carried by Serre's finite central-extension
quotient package before applying the lower-height induction to the multiplicity representation. -/
structure ConstituentProjectiveExtensionQuotientData
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (P_S : Type (max u v x)) [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule) where
  G2 : Type (max u v x)
  instGroupG2 : Group G2
  instFiniteG2 : Finite G2
  pi : G2 →* G
  I2 : Subgroup G2
  instNormalI2 : I2.Normal
  Nbar : Subgroup (G2 ⧸ I2)
  instNormalNbar : Nbar.Normal
  hNbar_central : Nbar ≤ Subgroup.center (G2 ⧸ I2)
  hNbar_cyclic : IsCyclic Nbar
  hNbar_coprime : Nat.Coprime p (Nat.card Nbar)
  tau : Representation k (G2 ⧸ I2) (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
  tau_irred : Representation.IsIrreducible tau
  quotientEquiv : ((G2 ⧸ I2) ⧸ Nbar) ≃* (G ⧸ I)
  descendLift :
    ∀ {P_tau : Type (max u v x)} (_ : AddCommGroup P_tau) (_ : Module A P_tau)
      (_ : Module.Free A P_tau) (_ : Module.Finite A P_tau)
      (ρA_tau : Representation A (G2 ⧸ I2) P_tau)
      (red_tau :
        P_tau →ₗ[A] fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar),
        IsResidueFieldLift tau ρA_tau red_tau →
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G P)
            (red : P →ₗ[A] V),
              IsResidueFieldLift ρ ρA red

attribute [instance]
  ConstituentProjectiveExtensionQuotientData.instGroupG2
  ConstituentProjectiveExtensionQuotientData.instFiniteG2
  ConstituentProjectiveExtensionQuotientData.instNormalI2
  ConstituentProjectiveExtensionQuotientData.instNormalNbar

omit [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: the generated cover `G₂` is finite as soon as the quotient
kernel `N̄ = ker(G₂ / I₂ → G / I)` is finite. -/
theorem fixed_constituent_generated_cover_finite_of_finite_quotient_kernel
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    Finite pi2.ker → Finite G2 := by
  dsimp
  intro hNbarFinite
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  have hkerFinite : Finite pi.ker := by
    let e : pi.ker ≃* pi2.ker := by
      simpa [G2, I2, pi2, pi] using
        generated_cover_kernel_equiv_nbar
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    exact Finite.of_equiv pi2.ker e.symm.toEquiv
  have hrangeFinite : Finite pi.range := by
    exact Finite.of_injective (fun y : pi.range => (y : G)) Subtype.val_injective
  exact (MonoidHom.finite_iff_finite_ker_range pi).2 ⟨hkerFinite, hrangeFinite⟩

omit [CharP k p] [Finite G] [FiniteDimensional k V] [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: an injective homomorphism into a finite cyclic group of
prime-to-`p` order transfers finiteness, cyclicity, and prime-to-`p` order to the source. -/
theorem finite_cyclic_coprime_of_injective_hom_to_cyclic_coprime_subgroup
    {Γ : Type*} [Group Γ]
    {Δ : Type*} [Group Δ]
    (C : Subgroup Δ) [Finite C]
    (hCcyclic : IsCyclic C)
    (hCcop : Nat.Coprime p (Nat.card C))
    (φ : Γ →* C) (hφ : Function.Injective φ) :
    Finite Γ ∧ IsCyclic Γ ∧ Nat.Coprime p (Nat.card Γ) := by
  have hΓfinite : Finite Γ := Finite.of_injective φ hφ
  have hΓcyclic : IsCyclic Γ := by
    letI : IsCyclic C := hCcyclic
    exact isCyclic_of_injective φ hφ
  have hcard_dvd : Nat.card Γ ∣ Nat.card C := by
    exact Subgroup.card_dvd_of_injective φ hφ
  constructor
  · exact hΓfinite
  constructor
  · exact hΓcyclic
  · exact hCcop.of_dvd_right hcard_dvd

omit [CharP k p] [Finite G] [FiniteDimensional k V] [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: an element of a finite subgroup has order dividing the
cardinality of that subgroup. -/
theorem pow_natCard_eq_one_of_mem_subgroup
    {Γ : Type*} [Group Γ]
    (C : Subgroup Γ) [Finite C]
    {x : Γ} (hx : x ∈ C) :
    x ^ Nat.card C = 1 := by
  let c : C := ⟨x, hx⟩
  exact congrArg (fun y : C => (y : Γ)) (pow_card_eq_one' (x := c))

omit [Finite G] [FiniteDimensional k V] [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: coercing the residue map on units agrees with applying the
residue homomorphism to the underlying unit. -/
theorem residue_units_map_coe
    (u : Aˣ) :
    ((Units.map (IsLocalRing.residue A).toMonoidHom u : kˣ) : k) =
      IsLocalRing.residue A (u : A) :=
  rfl

omit [Finite G] [FiniteDimensional k V] [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: a residue-field lift intertwines the lifted and residual
group actions after applying the chosen reduction map. -/
theorem isResidueFieldLift_apply
    {G' : Type v} [Group G']
    {V' : Type x} [AddCommGroup V'] [Module k V']
    {P : Type w} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (ρl : Representation k G' V')
    (ρA : Representation A G' P)
    (red : P →ₗ[A] V')
    (hLift : IsResidueFieldLift ρl ρA red)
    (g : G') (x : P) :
    red (ρA g x) = ρl g (red x) := by
  letI : Module (MonoidAlgebra A G') P := ρA.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower A (MonoidAlgebra A G') P := by
    refine IsScalarTower.of_algebraMap_smul ?_
    intro a x
    change ρA.asAlgebraHom (algebraMap A (MonoidAlgebra A G') a) x = a • x
    simp [Algebra.smul_def]
  letI : Module (MonoidAlgebra k G') V' := ρl.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower k (MonoidAlgebra k G') V' := by
    refine IsScalarTower.of_algebraMap_smul ?_
    intro a x
    change ρl.asAlgebraHom (algebraMap k (MonoidAlgebra k G') a) x = a • x
    simp [Algebra.smul_def]
  have hG :
      red ((MonoidAlgebra.single g (1 : A)) • x) =
        (MonoidAlgebra.single g (1 : k)) • red x := by
    simpa [MonoidAlgebra.of_apply] using
      LinearMap.IsResidueFieldReduction.map_monoidAlgebra_of
        (Λ := A) (G := G') (P := P) (Pbar := V') (f := red) hLift g x
  have hsrc : (MonoidAlgebra.single g (1 : A)) • x = ρA g x := by
    change (ρA.asAlgebraHom (MonoidAlgebra.single g 1)) x = _
    simp [Representation.asAlgebraHom_single]
  have htgt : (MonoidAlgebra.single g (1 : k)) • red x = ρl g (red x) := by
    change (ρl.asAlgebraHom (MonoidAlgebra.single g 1)) (red x) = _
    simp [Representation.asAlgebraHom_single]
  rw [hsrc] at hG
  rwa [htgt] at hG

omit [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: a base-change reduction map that intertwines the group
actions pointwise is a residue-field lift. -/
theorem isResidueFieldLift_of_isBaseChange_apply
    {G' : Type*} [Group G']
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (ρl : Representation k G' V')
    (ρA : Representation A G' P)
    (red : P →ₗ[A] V')
    (hbase : IsBaseChange k red)
    (hinter : ∀ (g : G') (x : P), red (ρA g x) = ρl g (red x)) :
    IsResidueFieldLift ρl ρA red := by
  letI : Module (MonoidAlgebra A G') P := Module.compHom P ρA.asAlgebraHom.toRingHom
  letI : IsScalarTower A (MonoidAlgebra A G') P :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρA.asAlgebraHom (algebraMap A (MonoidAlgebra A G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρA.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra k G') V' := Module.compHom V' ρl.asAlgebraHom.toRingHom
  letI : IsScalarTower k (MonoidAlgebra k G') V' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρl.asAlgebraHom (algebraMap k (MonoidAlgebra k G') a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρl.asAlgebraHom.commutes a) x
  letI : Module (MonoidAlgebra A G') V' :=
    Module.compHom V' (MonoidAlgebra.mapRingHom G' (algebraMap A k))
  letI : IsScalarTower A (MonoidAlgebra A G') V' :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change
        (MonoidAlgebra.mapRingHom G' (algebraMap A k))
            (MonoidAlgebra.single (1 : G') a) • x =
          a • x
      rw [MonoidAlgebra.mapRingHom_single]
      have hsingle :
          MonoidAlgebra.single (1 : G') (IsLocalRing.residue A a) =
            algebraMap k (MonoidAlgebra k G') (IsLocalRing.residue A a) := by
        rw [MonoidAlgebra.single_eq_algebraMap_mul_of]
        simp
      calc
        MonoidAlgebra.single (1 : G') (IsLocalRing.residue A a) • x =
            (IsLocalRing.residue A a) • x := by
              simpa only [hsingle] using
                (IsScalarTower.algebraMap_smul (MonoidAlgebra k G')
                  (IsLocalRing.residue A a) x)
        _ = a • x := by
              simpa [IsLocalRing.ResidueField.algebraMap_eq] using
                (IsScalarTower.algebraMap_smul k a x)
  change red.IsResidueFieldReduction G'
  refine ⟨hbase, ?_⟩
  refine Representation.IsIntertwiningMap.mk ?_
  intro g x
  calc
    red (MonoidAlgebra.of A G' g • x) = red (ρA g x) := by
      change
        red ((ρA.asAlgebraHom (MonoidAlgebra.single g (1 : A))) x) = red (ρA g x)
      simp [Representation.asAlgebraHom_single]
    _ = ρl g (red x) := hinter g x
    _ = MonoidAlgebra.of k G' g • red x := by
          change ρl g (red x) =
            (ρl.asAlgebraHom (MonoidAlgebra.single g (1 : k))) (red x)
          simp [Representation.asAlgebraHom_single]
    _ =
        (MonoidAlgebra.mapRingHom G' (algebraMap A k) (MonoidAlgebra.of A G' g)) •
          red x := by
            simp [MonoidAlgebra.of_apply]
    _ = MonoidAlgebra.of A G' g • red x := by
          rfl

omit [CommRing A] [HenselianLocalRing A] [CharP k p] [Finite G] [FiniteDimensional k V]
  [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: under the first isomorphism theorem for a surjective group
homomorphism, the inverse image of `φ h` is the quotient class represented by `h`. -/
theorem quotientKerEquivOfSurjective_symm_apply_mk
    {H Q : Type*} [Group H] [Group Q]
    (φ : H →* Q) (hφ : Function.Surjective φ) (h : H) :
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ h) = QuotientGroup.mk h := by
  apply (QuotientGroup.quotientKerEquivOfSurjective φ hφ).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

omit [CharP k p] [Finite G] [FiniteDimensional k V] [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: a residue-field lift on a surjective cover descends to the
quotient target when the lifted kernel action is trivial. -/
theorem isResidueFieldLift_descend_of_surjective
    {H Q : Type*} [Group H] [Group Q]
    {W : Type*} [AddCommGroup W] [Module k W]
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    (φ : H →* Q) (hφ : Function.Surjective φ)
    (ρ : Representation k Q W)
    (ρA_H : Representation A H P)
    (red : P →ₗ[A] W)
    [Representation.IsTrivial (ρA_H.comp φ.ker.subtype)]
    (hLift : IsResidueFieldLift (ρ.comp φ) ρA_H red) :
    let ρA_Q : Representation A Q P :=
      (ρA_H.ofQuotient φ.ker).comp
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toMonoidHom
    IsResidueFieldLift ρ ρA_Q red := by
  dsimp
  let ρA_Q : Representation A Q P :=
    (ρA_H.ofQuotient φ.ker).comp
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toMonoidHom
  have hinter :
      ∀ (q : Q) (x : P), red (ρA_Q q x) = ρ q (red x) := by
    intro q x
    obtain ⟨h, rfl⟩ := hφ q
    have hq :
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ h) =
          QuotientGroup.mk h := by
      simpa using quotientKerEquivOfSurjective_symm_apply_mk φ hφ h
    calc
      red (ρA_Q (φ h) x) = red (ρA_H h x) := by
            dsimp [ρA_Q]
            rw [hq]
            exact
              congrArg red
                (Representation.ofQuotient_coe_apply (ρ := ρA_H) (S := φ.ker) h x)
      _ = (ρ.comp φ) h (red x) := by
            exact isResidueFieldLift_apply (A := A) (ρ.comp φ) ρA_H red hLift h x
      _ = ρ (φ h) (red x) := rfl
  exact isResidueFieldLift_of_isBaseChange_apply ρ ρA_Q red hLift.1 hinter

omit [Finite G] [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: the prime-to-`p` triviality criterion for a lifted trivial
residual action is insensitive to the universe of the acting finite group. -/
theorem isTrivial_of_residueFieldLift_trivial_of_coprime_card_any
    (hp : Nat.Prime p)
    {N : Type*} [Group N] [Finite N]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {ρA : Representation A N P}
    {red : P →ₗ[A] W}
    (hLift : IsResidueFieldLift (Representation.trivial k N W) ρA red)
    (hNcop : Nat.Coprime p (Nat.card N)) :
    Representation.IsTrivial ρA := by
  obtain ⟨N₀, hN₀group, hN₀fintype, ⟨e⟩⟩ :=
    Finite.exists_type_univ_nonempty_mulEquiv.{_, u} N
  letI : Group N₀ := hN₀group
  letI : Fintype N₀ := hN₀fintype
  let ρA₀ : Representation A N₀ P := ρA.comp e.symm.toMonoidHom
  have hLift₀ :
      IsResidueFieldLift (Representation.trivial k N₀ W) ρA₀ red := by
    have hcomp :
        IsResidueFieldLift
          ((Representation.trivial k N W).comp e.symm.toMonoidHom)
          ρA₀
          red :=
      Representation.isResidueFieldLift_comp hLift e.symm.toMonoidHom
    simpa [ρA₀, Representation.trivial] using hcomp
  have hN₀cop : Nat.Coprime p (Nat.card N₀) := by
    have hcard : Nat.card N₀ = Nat.card N := Nat.card_congr e.symm.toEquiv
    rw [hcard]
    exact hNcop
  have hTrivial₀ : Representation.IsTrivial ρA₀ := by
    exact
      isTrivial_of_residueFieldLift_trivial_of_coprime_card
        (A := A) (p := p) hp hLift₀ hN₀cop
  refine Representation.IsTrivial.mk ?_
  intro n
  ext x
  have h := Representation.isTrivial_apply ρA₀ (e n) x
  simpa [ρA₀] using h

omit [CharP k p] [Finite G] [FiniteDimensional k V] [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: two residue maps into `k`-modules induce an `A`-linear
reduction map out of their tensor product whose pure tensors are evaluated over the residue
field. -/
theorem exists_tensorProduct_reduction_of_residue_maps
    {F : Type*} [AddCommGroup F] [Module k F]
    {S : Type*} [AddCommGroup S] [Module k S]
    {W : Type*} [AddCommGroup W] [Module k W]
    {P : Type*} [AddCommGroup P] [Module A P]
    {Q : Type*} [AddCommGroup Q] [Module A Q]
    (eval : F ⊗[k] S →ₗ[k] W)
    (redP : P →ₗ[A] F)
    (redQ : Q →ₗ[A] S) :
    ∃ red : P ⊗[A] Q →ₗ[A] W,
      ∀ (y : P) (z : Q), red (y ⊗ₜ[A] z) = eval (redP y ⊗ₜ[k] redQ z) := by
  let bilinear : P →ₗ[A] Q →ₗ[A] W :=
    { toFun := fun y =>
        { toFun := fun z => eval (redP y ⊗ₜ[k] redQ z)
          map_add' := by
            intro z₁ z₂
            rw [map_add, TensorProduct.tmul_add, map_add]
          map_smul' := by
            intro a z
            rw [map_smul]
            change eval (redP y ⊗ₜ[k] ((algebraMap A k a) • redQ z)) =
              (algebraMap A k a) • eval (redP y ⊗ₜ[k] redQ z)
            rw [TensorProduct.tmul_smul]
            change eval ((algebraMap A k a) • (redP y ⊗ₜ[k] redQ z)) =
              (algebraMap A k a) • eval (redP y ⊗ₜ[k] redQ z)
            exact eval.map_smul (algebraMap A k a) (redP y ⊗ₜ[k] redQ z) }
      map_add' := by
        intro y₁ y₂
        ext z
        change eval (redP (y₁ + y₂) ⊗ₜ[k] redQ z) =
          eval (redP y₁ ⊗ₜ[k] redQ z) + eval (redP y₂ ⊗ₜ[k] redQ z)
        rw [map_add, TensorProduct.add_tmul, map_add]
      map_smul' := by
        intro a y
        ext z
        change eval (redP (a • y) ⊗ₜ[k] redQ z) = a • eval (redP y ⊗ₜ[k] redQ z)
        rw [map_smul]
        change eval (((algebraMap A k a) • redP y) ⊗ₜ[k] redQ z) =
          (algebraMap A k a) • eval (redP y ⊗ₜ[k] redQ z)
        change eval ((algebraMap A k a) • (redP y ⊗ₜ[k] redQ z)) =
          (algebraMap A k a) • eval (redP y ⊗ₜ[k] redQ z)
        exact eval.map_smul (algebraMap A k a) (redP y ⊗ₜ[k] redQ z) }
  refine ⟨TensorProduct.lift bilinear, ?_⟩
  intro y z
  rfl

/-- Helper for Theorem 17-17.6-1: if both tensor factors are residue-field base changes, then
the pure-tensor reduction induced by a residue-field tensor equivalence is itself a base change. -/
theorem tensorProduct_reduction_isBaseChange_of_residue_maps
    {F : Type*} [AddCommGroup F] [Module A F] [Module k F] [IsScalarTower A k F]
    {S : Type*} [AddCommGroup S] [Module A S] [Module k S] [IsScalarTower A k S]
    {W : Type*} [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower A k W]
    {P : Type*} [AddCommGroup P] [Module A P]
    {Q : Type*} [AddCommGroup Q] [Module A Q]
    (eval : F ⊗[k] S ≃ₗ[k] W)
    (redP : P →ₗ[A] F)
    (redQ : Q →ₗ[A] S)
    (hredP : IsBaseChange k redP)
    (hredQ : IsBaseChange k redQ)
    (red : P ⊗[A] Q →ₗ[A] W)
    (hred_tmul :
      ∀ (y : P) (z : Q), red (y ⊗ₜ[A] z) = eval (redP y ⊗ₜ[k] redQ z)) :
    IsBaseChange k red := by
  letI : Module k k := Semiring.toModule
  letI : IsScalarTower A k k :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      simp [Algebra.smul_def]
  letI : Module k (k ⊗[A] P) := TensorProduct.leftModule
  letI : IsScalarTower A k (k ⊗[A] P) := TensorProduct.isScalarTower_left
  letI : IsScalarTower k k (k ⊗[A] P) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ by
      simp
  letI : SMulCommClass k k (k ⊗[A] P) := inferInstance
  letI : Module k (k ⊗[A] Q) := TensorProduct.leftModule
  letI : IsScalarTower A k (k ⊗[A] Q) := TensorProduct.isScalarTower_left
  letI : Module k (k ⊗[A] (P ⊗[A] Q)) := TensorProduct.leftModule
  letI : IsScalarTower A k (k ⊗[A] (P ⊗[A] Q)) := TensorProduct.isScalarTower_left
  let eAssoc : k ⊗[A] (P ⊗[A] Q) ≃ₗ[k] (k ⊗[A] P) ⊗[A] Q :=
    (TensorProduct.AlgebraTensorModule.assoc A A k k P Q).symm
  let eCancel : (k ⊗[A] P) ⊗[A] Q ≃ₗ[k] (k ⊗[A] P) ⊗[k] (k ⊗[A] Q) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A k k (k ⊗[A] P) Q).symm
  let eBase : k ⊗[A] (P ⊗[A] Q) ≃ₗ[k] (k ⊗[A] P) ⊗[k] (k ⊗[A] Q) :=
    eAssoc.trans eCancel
  let eTarget : (k ⊗[A] P) ⊗[k] (k ⊗[A] Q) ≃ₗ[k] F ⊗[k] S :=
    TensorProduct.congr hredP.equiv hredQ.equiv
  let e : k ⊗[A] (P ⊗[A] Q) ≃ₗ[k] W :=
    (eBase.trans eTarget).trans eval
  refine IsBaseChange.of_equiv e ?_
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp [e]
  · intro y z
    calc
      e (1 ⊗ₜ[A] (y ⊗ₜ[A] z)) =
          eval (eTarget (eCancel (eAssoc (1 ⊗ₜ[A] (y ⊗ₜ[A] z))))) := rfl
      _ = eval (eTarget (eCancel ((1 ⊗ₜ[A] y) ⊗ₜ[A] z))) := by
            rw [TensorProduct.AlgebraTensorModule.assoc_symm_tmul]
      _ = eval (eTarget ((1 ⊗ₜ[A] y) ⊗ₜ[k] (1 ⊗ₜ[A] z))) := by
            exact
              congrArg (fun x ↦ eval (eTarget x))
                (TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul
                  A k k (1 ⊗ₜ[A] y) z)
      _ = eval (hredP.equiv (1 ⊗ₜ[A] y) ⊗ₜ[k] hredQ.equiv (1 ⊗ₜ[A] z)) := by
            exact
              congrArg eval
                (TensorProduct.congr_tmul hredP.equiv hredQ.equiv
                  (1 ⊗ₜ[A] y) (1 ⊗ₜ[A] z))
      _ = eval (redP y ⊗ₜ[k] redQ z) := by
            rw [hredP.equiv_tmul (1 : k) y, hredQ.equiv_tmul (1 : k) z]
            simp
      _ = red (y ⊗ₜ[A] z) := by
            rw [hred_tmul]
  · intro t₁ t₂ ht₁ ht₂
    rw [TensorProduct.tmul_add, map_add, ht₁, ht₂, map_add]

/-- Helper for Theorem 17-17.6-1: the bounded determinant containment gives the explicit
candidate subgroup all three properties needed for a later injective comparison from the quotient
kernel. -/
theorem candidate_subgroup_finite_cyclic_coprime_of_bounded_containment
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hcandidate_le :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map
        (QuotientGroup.mk' Qd)
      fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar) :
    let Candidate :=
      fixed_constituent_projective_extension_candidate_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    Finite Candidate ∧ IsCyclic Candidate ∧ Nat.Coprime p (Nat.card Candidate) := by
  dsimp
  let Candidate :=
    fixed_constituent_projective_extension_candidate_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hCandidateFinite : Finite Candidate := by
    simpa [Candidate] using
      fixed_constituent_projective_extension_candidate_finite
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  have hCandidateShape :
      IsCyclic Candidate ∧ Nat.Coprime p (Nat.card Candidate) := by
    simpa [Candidate] using
      candidate_subgroup_cyclic_and_coprime_of_bounded_containment
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        hcandidate_le
  exact ⟨hCandidateFinite, hCandidateShape.1, hCandidateShape.2⟩

/-- Helper for Theorem 17-17.6-1: prime-to-`p` degree of the fixed residue constituent
transports across a residue-field lift to prime-to-`p` rank of the lifted constituent. -/
theorem fixed_constituent_lift_finrank_coprime_of_residue_finrank_coprime
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hSbar_rank_coprime : Nat.Coprime p (Module.finrank k Sbar.toSubmodule)) :
    Nat.Coprime p (Module.finrank A P_S) := by
  rw [fixed_constituent_lift_finrank_eq
      (A := A) (G := G) (I := I) (ρ := ρ) (Sbar := Sbar)
      hSbar_irred ρA_I red_S hLiftSbar]
  exact hSbar_rank_coprime

omit [CommRing A] [HenselianLocalRing A] [CharP k p] [Finite G] [FiniteDimensional k V]
  [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: the trace of a group-algebra element acting through a
representation is the coefficient-weighted character sum. -/
theorem trace_asAlgebraHom_eq_sum_coeff_mul_character
    {K : Type*} [Field K]
    {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (σ : Representation K H W) (u : MonoidAlgebra K H) :
    LinearMap.trace K W (σ.asAlgebraHom u) =
      ∑ s : H, u s * σ.character s := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  have hu : Finsupp.equivFunOnFinite.symm (fun s : H ↦ u s) = u := by
    ext s
    simp
  have hsum_finsupp :
      Finsupp.equivFunOnFinite.symm (fun s : H ↦ u s) =
        ∑ s : H, Finsupp.single s (u s) :=
    Finsupp.equivFunOnFinite_symm_eq_sum (fun s : H ↦ u s)
  have hsum_single : u = ∑ s : H, Finsupp.single s (u s) :=
    hu.symm.trans hsum_finsupp
  calc
    LinearMap.trace K W (σ.asAlgebraHom u) =
        LinearMap.trace K W
          (σ.asAlgebraHom (∑ s : H, Finsupp.single s (u s))) := by
          exact congrArg (fun z : MonoidAlgebra K H ↦
            LinearMap.trace K W (σ.asAlgebraHom z)) hsum_single
    _ = LinearMap.trace K W (∑ s : H, u s • σ s) := by
          congr 1
          simp
    _ = ∑ s : H, u s * σ.character s := by
          simp [Representation.character, smul_eq_mul]

omit [CommRing A] [HenselianLocalRing A] [Finite G] [FiniteDimensional k V]
  [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: over an algebraically closed field whose characteristic is
coprime to the finite group order, every irreducible representation has degree prime to that
characteristic. -/
theorem IsIrreducible.finrank_coprime_of_coprime_card
    {K : Type*} [Field K] [CharP K p] [IsAlgClosed K]
    {H : Type*} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (hHcop : Nat.Coprime p (Nat.card H))
    (σ : Representation K H W)
    (hσ : σ.IsIrreducible) :
    Nat.Coprime p (Module.finrank K W) := by
  rcases CharP.char_is_prime_or_zero K p with hp | hp0
  · classical
    letI : Fintype H := Fintype.ofFinite H
    letI : σ.IsIrreducible := hσ
    have hH_not_dvd : ¬ p ∣ Nat.card H := hp.coprime_iff_not_dvd.mp hHcop
    letI : NeZero (Nat.card H : K) := NeZero.of_not_dvd K hH_not_dvd
    letI : Invertible (Nat.card H : K) :=
      invertibleOfNonzero (NeZero.ne (Nat.card H : K))
    have hcard_ne_zero : (Nat.card H : K) ≠ 0 := NeZero.ne (Nat.card H : K)
    let f : classFunctionSubmodule K H :=
      ⟨fun s : H ↦ σ.character s⁻¹, inverse_character_mem_classFunctionSubmodule σ⟩
    let u : Subalgebra.center K (MonoidAlgebra K H) := (centerClassFunctionEquiv K).symm f
    have hu_coeff : ∀ s : H, (u : MonoidAlgebra K H) s = σ.character s⁻¹ := by
      intro s
      rfl
    have hself_pair :
        (Nat.card H : K)⁻¹ *
            ∑ s : H, σ.character s * σ.character s⁻¹ = 1 := by
      have hσσ : Nonempty (σ.Equiv σ) := ⟨Representation.Equiv.refl σ⟩
      simpa [hσσ] using (Representation.char_orthonormal (ρ := σ) (σ := σ))
    have hsum_char :
        ∑ s : H, σ.character s⁻¹ * σ.character s = (Nat.card H : K) := by
      have hsum_left :
          ∑ s : H, σ.character s * σ.character s⁻¹ = (Nat.card H : K) := by
        calc
          ∑ s : H, σ.character s * σ.character s⁻¹ =
              (Nat.card H : K) *
                ((Nat.card H : K)⁻¹ *
                  ∑ s : H, σ.character s * σ.character s⁻¹) := by
                rw [← mul_assoc, mul_inv_cancel₀ hcard_ne_zero, one_mul]
          _ = (Nat.card H : K) * 1 := by rw [hself_pair]
          _ = (Nat.card H : K) := by rw [mul_one]
      calc
        ∑ s : H, σ.character s⁻¹ * σ.character s =
            ∑ s : H, σ.character s * σ.character s⁻¹ := by
              apply Finset.sum_congr rfl
              intro s hs
              rw [mul_comm]
        _ = (Nat.card H : K) := hsum_left
    have htrace_coeff :
        LinearMap.trace K W (σ.asAlgebraHom (u : MonoidAlgebra K H)) =
          (Nat.card H : K) := by
      calc
        LinearMap.trace K W (σ.asAlgebraHom (u : MonoidAlgebra K H)) =
            ∑ s : H, (u : MonoidAlgebra K H) s * σ.character s := by
              exact trace_asAlgebraHom_eq_sum_coeff_mul_character σ
                (u : MonoidAlgebra K H)
        _ = ∑ s : H, σ.character s⁻¹ * σ.character s := by
              apply Finset.sum_congr rfl
              intro s hs
              rw [hu_coeff s]
        _ = (Nat.card H : K) := hsum_char
    have htrace_scalar :
        LinearMap.trace K W (σ.asAlgebraHom (u : MonoidAlgebra K H)) =
          ω[σ] u * (Module.finrank K W : K) := by
      rw [asAlgebraHom_center_eq_centralCharacter_smul_id σ u]
      simp [LinearMap.trace_id, smul_eq_mul]
    have hfinrank_ne_zero : (Module.finrank K W : K) ≠ 0 := by
      intro hfinrank_zero
      have hcard_zero : (Nat.card H : K) = 0 := by
        rw [← htrace_coeff, htrace_scalar, hfinrank_zero, mul_zero]
      exact hcard_ne_zero hcard_zero
    refine hp.coprime_iff_not_dvd.mpr ?_
    intro hdiv
    exact hfinrank_ne_zero ((CharP.cast_eq_zero_iff K p (Module.finrank K W)).2 hdiv)
  · letI : CharP K 0 := by
      rwa [hp0] at ‹CharP K p›
    letI : CharZero K := CharP.charP_to_charZero K
    letI : σ.IsIrreducible := hσ
    exact hHcop.of_dvd_right (Representation.finrank_dvd_card σ)

/-- Helper for Theorem 17-17.6-1: if the degree of the fixed residue constituent divides the
Hall-kernel order, then that degree is prime to the residue characteristic. -/
theorem fixed_constituent_residue_finrank_coprime_of_finrank_dvd_card
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_rank_dvd : Module.finrank k Sbar.toSubmodule ∣ Nat.card I) :
    Nat.Coprime p (Module.finrank k Sbar.toSubmodule) := by
  exact hIcop.of_dvd_right hSbar_rank_dvd

/-- Helper for Theorem 17-17.6-1: the fixed lifted constituent has degree prime to `p`. -/
theorem fixed_constituent_lift_finrank_coprime
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    Nat.Coprime p (Module.finrank A P_S) := by
  have hSbar_rank_coprime :
      Nat.Coprime p (Module.finrank k Sbar.toSubmodule) :=
    IsIrreducible.finrank_coprime_of_coprime_card
      (p := p) (K := k) (H := I) (W := Sbar.toSubmodule)
      hIcop Sbar.toRepresentation hSbar_irred
  exact
    fixed_constituent_lift_finrank_coprime_of_residue_finrank_coprime
      (A := A) (G := G) (I := I) ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
      hSbar_rank_coprime

omit [Finite G] [FiniteDimensional k V] in
/-- Helper for Theorem 17-17.6-1: the subgroup of units whose `d`-th power lies in a finite
prime-to-`p` determinant subgroup is itself finite, cyclic, and prime-to-`p`. -/
theorem determinant_root_subgroup_finite_cyclic_coprime
    (hp : Nat.Prime p)
    (C : Subgroup Aˣ)
    [Finite C]
    (hCcop : Nat.Coprime p (Nat.card C))
    {d : ℕ}
    (hdcop : Nat.Coprime p d) :
    let S : Subgroup Aˣ := C.comap (powMonoidHom d : Aˣ →* Aˣ)
    Finite S ∧ IsCyclic S ∧ Nat.Coprime p (Nat.card S) := by
  dsimp
  let n := d * Nat.card C
  let S : Subgroup Aˣ := C.comap (powMonoidHom d : Aˣ →* Aˣ)
  have hn : n ≠ 0 := by
    have hd_ne : d ≠ 0 := by
      intro hd0
      have hcop0 : Nat.Coprime p 0 := by
        simpa [hd0] using hdcop
      exact (hp.coprime_iff_not_dvd.mp hcop0) (Nat.dvd_zero p)
    have hC_ne : Nat.card C ≠ 0 := by
      exact Nat.ne_of_gt (Nat.card_pos (α := C))
    exact Nat.mul_ne_zero hd_ne hC_ne
  letI : NeZero n := ⟨hn⟩
  have hncop : Nat.Coprime p n := Nat.Coprime.mul_right hdcop hCcop
  have hpow_card : ∀ a : S, ((a : Aˣ) ^ n) = 1 := by
    intro a
    have haC : ((a : Aˣ) ^ d) ∈ C := by
      change ((powMonoidHom d : Aˣ →* Aˣ) (a : Aˣ)) ∈ C
      exact a.2
    calc
      (a : Aˣ) ^ n = ((a : Aˣ) ^ d) ^ Nat.card C := by
        simpa [n, pow_mul]
      _ = 1 := pow_natCard_eq_one_of_mem_subgroup C haC
  let res : Aˣ →* kˣ := Units.map (IsLocalRing.residue A).toMonoidHom
  let resS : S →* rootsOfUnity n k :=
    MonoidHom.codRestrict
      (res.comp (Subgroup.subtype S))
      (rootsOfUnity n k)
      fun a ↦ by
        exact (mem_rootsOfUnity n ((res.comp (Subgroup.subtype S)) a)).2 <| by
          simpa [res, map_pow] using congrArg res (hpow_card a)
  have hresS_injective : Function.Injective resS := by
    intro a b hab
    apply Subtype.ext
    have hres_div : res ((a : Aˣ) / (b : Aˣ)) = 1 := by
      have hresS_apply :
          ∀ a : S, ((resS a : rootsOfUnity n k) : kˣ) = res (a : Aˣ) := by
        intro a
        rfl
      have hab_val : res (a : Aˣ) = res (b : Aˣ) := by
        rw [← hresS_apply a, ← hresS_apply b]
        exact congrArg (fun z : rootsOfUnity n k => (z : kˣ)) hab
      rw [show res ((a : Aˣ) / (b : Aˣ)) = res (a : Aˣ) / res (b : Aˣ) by simp [res]]
      exact div_eq_one.2 hab_val
    have hpow_div : (((a : Aˣ) / (b : Aˣ)) ^ n) = 1 := by
      simpa using hpow_card (a / b)
    have hdiv_one : ((a : Aˣ) / (b : Aˣ)) = 1 := by
      apply unit_eq_one_of_pow_eq_one_of_residue_eq_one (A := A) (p := p) hp hncop
      · simpa using congrArg (fun z : Aˣ ↦ (z : A)) hpow_div
      · rw [← residue_units_map_coe (A := A) ((a : Aˣ) / (b : Aˣ))]
        simpa [res] using congrArg (fun z : kˣ ↦ (z : k)) hres_div
    exact div_eq_one.mp hdiv_one
  have hSfinite : Finite S := Finite.of_injective resS hresS_injective
  letI : Finite S := hSfinite
  have hroots_coprime : Nat.Coprime p (Nat.card (rootsOfUnity n k)) :=
    roots_of_unity_card_coprime_charP (A := A) hp hn
  have hrange_coprime : Nat.Coprime p (Nat.card resS.range) :=
    hroots_coprime.of_dvd_right resS.range.card_subgroup_dvd_card
  have hcard_eq : Nat.card S = Nat.card resS.range :=
    Nat.card_congr (MonoidHom.ofInjective hresS_injective).toEquiv
  exact ⟨hSfinite, isCyclic_of_injective resS hresS_injective, by
    rw [hcard_eq]
    exact hrange_coprime⟩

/-- Helper for Theorem 17-17.6-1: Serre's actual literal determinant-cover projection kernel is
finite, cyclic, and of order prime to the residue characteristic. -/
theorem literal_determinant_cover_kernel_finite_cyclic_coprime
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    let K :=
      (fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).ker
    Finite K ∧ IsCyclic K ∧ Nat.Coprime p (Nat.card K) := by
  dsimp
  let C : Subgroup Aˣ :=
    fixed_constituent_determinant_subgroup
      (A := A) (G := G) (I := I) (P_S := P_S) ρA_I
  let d := Module.finrank A P_S
  let RootSubgroup : Subgroup Aˣ := C.comap (powMonoidHom d : Aˣ →* Aˣ)
  have hCcop : Nat.Coprime p (Nat.card C) := by
    exact
      fixed_constituent_determinant_subgroup_coprime
        (A := A) (G := G) (I := I) (P_S := P_S) hIcop ρA_I
  have hdcop : Nat.Coprime p d := by
    simpa [d] using
      fixed_constituent_lift_finrank_coprime
        (A := A) (G := G) (I := I) hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  have hRoot :
      Finite RootSubgroup ∧ IsCyclic RootSubgroup ∧ Nat.Coprime p (Nat.card RootSubgroup) := by
    letI : Finite C := inferInstance
    simpa [RootSubgroup, C, d] using
      determinant_root_subgroup_finite_cyclic_coprime
        (A := A) (p := p) hp C hCcop hdcop
  let scalarRoot :=
    literal_determinant_cover_kernel_scalar_hom
      (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  have hscalarRoot_injective : Function.Injective scalarRoot := by
    simpa [scalarRoot] using
      literal_determinant_cover_kernel_scalar_hom_injective
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  letI : Finite RootSubgroup := hRoot.1
  exact
    finite_cyclic_coprime_of_injective_hom_to_cyclic_coprime_subgroup
      (p := p) RootSubgroup hRoot.2.1 hRoot.2.2 scalarRoot hscalarRoot_injective

/-- Helper for Theorem 17-17.6-1: the normalized quotient-kernel representative has trivial
residue determinant class modulo `d`-th powers. -/
theorem normalized_kernel_representative_det_class_eq_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (q :
      (generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift).ker) :
    QuotientGroup.mk'
        ((powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range)
        (Units.map (IsLocalRing.residue A)
          (fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2)) =
      1 := by
  exact
    normalized_kernel_determinant_class_eq_one
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q

/-- Helper for Theorem 17-17.6-1: over the algebraically closed residue field, every chosen
section determinant class modulo `d`-th powers is represented by the identity element of Serre's
determinant subgroup. -/
theorem fixed_constituent_section_determinant_class_lands_in_determinant_subgroup_of_algClosed
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    ∀ s : G,
      ∃ c : fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I,
        fixed_constituent_section_determinant_class
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s =
          fixed_constituent_determinant_subgroup_residue_class
            (A := A) (G := G) (I := I) ρA_I c := by
  intro s
  let d := Module.finrank A P_S
  let Qd : Subgroup kˣ := (powMonoidHom d : kˣ →* kˣ).range
  let sec :=
    fixed_constituent_transport_total_space_section
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let detSec : Aˣ :=
    fixed_constituent_transport_fiber_det
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) (sec s).2
  let y : kˣ := Units.map (IsLocalRing.residue A).toMonoidHom detSec
  have hd_ne : d ≠ 0 := by
    simpa [d] using
      fixed_constituent_lift_finrank_ne_zero
        (A := A) (G := G) (I := I) hIcop ρ Sbar hSbar_irred ρA_I red_S
        hLiftSbar
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_ne
  have hy_mem : y ∈ Qd := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y : k) hd_pos
    have hz_ne : z ≠ 0 := by
      intro hz0
      have hy_zero : (y : k) = 0 := by
        calc
          (y : k) = z ^ d := hz.symm
          _ = 0 := by rw [hz0, zero_pow hd_ne]
      exact y.ne_zero hy_zero
    let zUnit : kˣ := Units.mk0 z hz_ne
    have hzUnit : zUnit ^ d = y := by
      apply Units.ext
      simpa [zUnit] using hz
    exact ⟨zUnit, by simpa using hzUnit⟩
  have hclass_one :
      fixed_constituent_section_determinant_class
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift s = 1 := by
    change QuotientGroup.mk' Qd y = 1
    exact (QuotientGroup.eq_one_iff (N := Qd) y).2 hy_mem
  refine ⟨1, ?_⟩
  rw [hclass_one]
  simp [fixed_constituent_determinant_subgroup_residue_class]

/-- Helper for Theorem 17-17.6-1: literal determinant membership of the normalized kernel
representatives is exactly the condition needed to place their attached scalars in Serre's
determinant-root subgroup. -/
theorem kernel_scalar_mem_determinant_root_subgroup_of_normalized_det_mem
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hdet_mem :
      let G2 :=
        fixed_constituent_generated_cover_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      let I2 :=
        fixed_constituent_generated_cover_hall_kernel_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      let pi2 : G2 ⧸ I2 →* G ⧸ I :=
        generated_cover_proj_to_quotient_descends
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      ∀ q : Nbar,
        fixed_constituent_transport_fiber_det
            (A := A) (G := G) (I := I) (ρA_I := ρA_I)
            (normalized_kernel_representative
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift q).1.2 ∈
          C) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
    let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
    let d := Module.finrank A P_S
    let RootSubgroup : Subgroup Aˣ := C.comap (powMonoidHom d : Aˣ →* Aˣ)
    let kernelScalar : Nbar →* Aˣ :=
      kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ q : Nbar, kernelScalar q ∈ RootSubgroup := by
  dsimp
  intro q
  change
    (kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q) ^
      Module.finrank A P_S ∈
        fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
  rw [← normalized_kernel_representative_det_eq_kernel_scalar_pow
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q]
  exact hdet_mem q

/-- Helper for Theorem 17-17.6-1: normalized quotient-kernel scalars have trivial residue class
modulo `d`-th powers. -/
theorem kernel_scalar_pow_residue_class_eq_one_for_generated_cover_kernel
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      generated_cover_proj_to_quotient_descends
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
    let d := Module.finrank A P_S
    let kernelScalar : Nbar →* Aˣ :=
      kernel_scalar_unit
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ q : Nbar,
      QuotientGroup.mk'
          ((powMonoidHom d : kˣ →* kˣ).range)
          (Units.map (IsLocalRing.residue A).toMonoidHom (kernelScalar q ^ d)) =
        1 := by
  dsimp
  intro q
  exact
    kernel_scalar_pow_residue_class_eq_one
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift q

/-- Helper for Theorem 17-17.6-1: the fixed-isotypic tensor-evaluation equivalence sends a pure
tensor `f ⊗ x` to the value of the intertwining map `f` at `x`. -/
theorem fixed_isotypic_tensor_evaluation_linearEquiv_tmul
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
    (x : Sbar.toSubmodule) :
    fixed_isotypic_tensor_evaluation_linearEquiv
        (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
        (f ⊗ₜ[k] x) = f x := by
  simp [fixed_isotypic_tensor_evaluation_linearEquiv, Representation.isotypicTensorEvaluation]

/-- Helper for Theorem 17-17.6-1: evaluating a pure tensor after applying Serre's upstairs cover
operator on the multiplicity factor gives the ambient action on `V` applied to the transported
source argument. -/
theorem fixed_isotypic_tensor_evaluation_cover_action_tmul
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ (g : G2)
      (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
      (x : Sbar.toSubmodule),
      fixed_isotypic_tensor_evaluation_linearEquiv
          (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
          (((fixed_isotypic_cover_representation
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
              hTransportLift g) f) ⊗ₜ[k] x) =
        ρ g.1.1
          (f ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1.1).symm.toLinearMap
            ((fixed_constituent_transport_fiber_reduction_equiv
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
              hTransportLift g.1.1 g.1.2).toLinearMap x))) := by
  dsimp
  intro g f x
  rw [fixed_isotypic_tensor_evaluation_linearEquiv_tmul]
  simpa [fixed_isotypic_cover_representation] using
    fixed_isotypic_cover_action_linearEquiv_apply
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      g f x

/-- Helper for Theorem 17-17.6-1: the evaluation image of a subrepresentation of Serre's
upstairs multiplicity-space cover is stable under the pulled-back ambient representation on `V`. -/
theorem fixed_isotypic_cover_eval_image_stable
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let coverRep :=
      fixed_isotypic_cover_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ (U : Subrepresentation coverRep),
      let evalBilin :
          fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
            Sbar.toSubmodule →ₗ[k] V :=
        Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype)
      let evalImage : Submodule k V := Submodule.map₂ evalBilin U.toSubmodule ⊤
      ∀ (g : G2) (y : V), y ∈ evalImage → ρ g.1.1 y ∈ evalImage := by
  dsimp
  intro U
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let evalBilin :
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
        Sbar.toSubmodule →ₗ[k] V :=
    Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype)
  let evalImage : Submodule k V := Submodule.map₂ evalBilin U.toSubmodule ⊤
  intro g y hy
  let sourceTransport : Sbar.toSubmodule ≃ₗ[k] Sbar.toSubmodule :=
    (fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
      hTransportLift g.1.1 g.1.2).toLinearEquiv.trans
      (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1.1).symm.toLinearEquiv
  have hmap : evalImage.map (ρ g.1.1) ≤ evalImage := by
    rw [Submodule.map_le_iff_le_comap]
    rw [Submodule.map₂_le]
    intro f hf x hx
    have hcover_apply :
        evalBilin
            ((fixed_isotypic_cover_representation
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
              hTransportLift) g f)
            (sourceTransport.symm x) =
          ρ g.1.1 (evalBilin f x) := by
      have hraw :=
        fixed_isotypic_cover_action_linearEquiv_apply
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
          hTransportLift g f (sourceTransport.symm x)
      have hraw' :
          evalBilin
              ((fixed_isotypic_cover_representation
                (p := p) (A := A) (G := G) (V := V)
                hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
                hTransportLift) g f)
              (sourceTransport.symm x) =
            ρ g.1.1 (evalBilin f (sourceTransport (sourceTransport.symm x))) := by
        simpa [evalBilin, fixed_isotypic_cover_representation, sourceTransport] using hraw
      simpa using hraw'
    change ρ g.1.1 (evalBilin f x) ∈ evalImage
    rw [← hcover_apply]
    exact
      Submodule.apply_mem_map₂ evalBilin (U.apply_mem_toSubmodule g hf) Submodule.mem_top
  exact hmap ⟨y, hy, rfl⟩

/-- Helper for Theorem 17-17.6-1: the evaluation image of a cover-subrepresentation is stable
for the pulled-back ambient representation `ρ.comp π`. -/
theorem fixed_isotypic_cover_eval_image_apply_mem
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    let coverRep :=
      fixed_isotypic_cover_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ (U : Subrepresentation coverRep),
      let evalBilin :
          fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
            Sbar.toSubmodule →ₗ[k] V :=
        Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype)
      let evalImage : Submodule k V := Submodule.map₂ evalBilin U.toSubmodule ⊤
      ∀ (g : G2) {y : V}, y ∈ evalImage → (ρ.comp pi) g y ∈ evalImage := by
  dsimp
  intro U
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let evalBilin :
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
        Sbar.toSubmodule →ₗ[k] V :=
    Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype)
  let evalImage : Submodule k V := Submodule.map₂ evalBilin U.toSubmodule ⊤
  intro g y hy
  simpa [pi] using
    fixed_isotypic_cover_eval_image_stable
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      U g y hy

/-- Helper for Theorem 17-17.6-1: a nonzero subrepresentation of Serre's upstairs
multiplicity-space cover has nonzero evaluation image in the ambient fixed-isotypic module. -/
theorem fixed_isotypic_cover_eval_image_ne_bot_of_ne_bot
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let coverRep :=
      fixed_isotypic_cover_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ (U : Subrepresentation coverRep),
      U ≠ ⊥ →
        let evalBilin :
            fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
              Sbar.toSubmodule →ₗ[k] V :=
          Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype)
        let evalImage : Submodule k V := Submodule.map₂ evalBilin U.toSubmodule ⊤
        evalImage ≠ ⊥ := by
  dsimp
  intro U hU
  let evalBilin :
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
        Sbar.toSubmodule →ₗ[k] V :=
    Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype)
  let evalImage : Submodule k V := Submodule.map₂ evalBilin U.toSubmodule ⊤
  intro hEval
  have hUbot : U.toSubmodule = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro f hf
    by_contra hf_ne
    have hf_map_ne : ∃ x : Sbar.toSubmodule, evalBilin f x ≠ 0 := by
      by_contra hzero
      apply hf_ne
      apply Representation.IntertwiningMap.ext
      ext x
      exact not_not.mp fun hx ↦ hzero ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hf_map_ne
    have hx_mem : evalBilin f x ∈ evalImage :=
      Submodule.apply_mem_map₂ evalBilin hf Submodule.mem_top
    have hEval' : evalImage = ⊥ := by
      simpa [evalImage, evalBilin] using hEval
    have hx_bot : evalBilin f x ∈ (⊥ : Submodule k V) := by
      simpa [hEval'] using hx_mem
    exact hx hx_bot
  apply hU
  apply Subrepresentation.toSubmodule_injective
  simpa using hUbot

/-- Helper for Theorem 17-17.6-1: a nonzero subrepresentation of Serre's upstairs
multiplicity-space cover has full evaluation image in the irreducible pulled-back ambient module. -/
theorem fixed_isotypic_cover_eval_image_eq_top_of_ne_bot
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let pi : G2 →* G :=
      (fixed_constituent_transport_total_space_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
        (Subgroup.subtype G2)
    let coverRep :=
      fixed_isotypic_cover_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ (U : Subrepresentation coverRep),
      U ≠ ⊥ →
        let evalBilin :
            fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
              Sbar.toSubmodule →ₗ[k] V :=
          Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype)
        let evalImage : Submodule k V := Submodule.map₂ evalBilin U.toSubmodule ⊤
        evalImage = ⊤ := by
  dsimp
  intro U hU
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let coverRep :=
    fixed_isotypic_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  let evalBilin :
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
        Sbar.toSubmodule →ₗ[k] V :=
    Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype)
  let evalImage : Submodule k V := Submodule.map₂ evalBilin U.toSubmodule ⊤
  have hCompIrred : Representation.IsIrreducible (ρ.comp pi) := by
    simpa [G2, pi] using
      fixed_constituent_generated_cover_comp_irreducible
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hEval_ne_bot : evalImage ≠ ⊥ := by
    simpa [evalImage, evalBilin] using
      fixed_isotypic_cover_eval_image_ne_bot_of_ne_bot
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        U hU
  let W : Subrepresentation (ρ.comp pi) :=
    { toSubmodule := evalImage
      apply_mem_toSubmodule :=
        fixed_isotypic_cover_eval_image_apply_mem
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          U }
  have hW_ne_bot : W ≠ ⊥ := by
    intro hW
    apply hEval_ne_bot
    have hW_sub : W.toSubmodule = (⊥ : Submodule k V) :=
      congrArg Subrepresentation.toSubmodule hW
    simpa [W] using hW_sub
  letI : Representation.IsIrreducible (ρ.comp pi) := hCompIrred
  have hW_top : W = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hW_ne_bot
  have hW_sub_top : W.toSubmodule = (⊤ : Submodule k V) :=
    congrArg Subrepresentation.toSubmodule hW_top
  simpa [W] using hW_sub_top

/-- Helper for Theorem 17-17.6-1: a representation on a nontrivial module has a nontrivial
lattice of subrepresentations. -/
theorem subrepresentationNontrivialOfNontrivial
    {K Γ W : Type*} [Semiring K] [Monoid Γ] [AddCommMonoid W] [Module K W]
    (τ : Representation K Γ W) [Nontrivial W] :
    Nontrivial (Subrepresentation τ) := by
  have hbot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤ := by
    intro h
    have hsub : (⊥ : Submodule K W) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top hsub
  exact ⟨⊥, ⊤, hbot_ne_top⟩

/-- Helper for Theorem 17-17.6-1: if a bilinear map realizes a linear equivalence from
`M ⊗ S` onto `V`, then a subspace whose tensor with a nonzero `S` surjects onto `V` is all of
`M`. -/
theorem submodule_eq_top_of_map₂_eq_top_of_tensor_linearEquiv
    {K : Type*} [Field K]
    {M S V' : Type*}
    [AddCommGroup M] [Module K M]
    [AddCommGroup S] [Module K S]
    [AddCommGroup V'] [Module K V']
    [FiniteDimensional K M] [FiniteDimensional K S] [FiniteDimensional K V']
    (evalBilin : M →ₗ[K] S →ₗ[K] V')
    (evalEquiv : M ⊗[K] S ≃ₗ[K] V')
    (hS_nontrivial : Nontrivial S)
    (U : Submodule K M)
    (hEval_top : Submodule.map₂ evalBilin U ⊤ = ⊤) :
    U = ⊤ := by
  let tensorMap :
      U ⊗[K] (⊤ : Submodule K S) →ₗ[K] V' :=
    TensorProduct.lift evalBilin ∘ₗ TensorProduct.mapIncl U (⊤ : Submodule K S)
  have hRange : LinearMap.range tensorMap = ⊤ := by
    simpa [tensorMap, TensorProduct.map₂_eq_range_lift_comp_mapIncl] using hEval_top
  have hTensor_surj : Function.Surjective tensorMap :=
    LinearMap.range_eq_top.mp hRange
  have hfin_le :
      Module.finrank K V' ≤ Module.finrank K (U ⊗[K] (⊤ : Submodule K S)) :=
    LinearMap.finrank_le_finrank_of_surjective hTensor_surj
  have hfin_tensor_le :
      Module.finrank K V' ≤ Module.finrank K U * Module.finrank K S := by
    simpa [Module.finrank_tensorProduct] using hfin_le
  have hfin_eval :
      Module.finrank K V' = Module.finrank K M * Module.finrank K S := by
    rw [← evalEquiv.finrank_eq, Module.finrank_tensorProduct]
  have hS_pos : 0 < Module.finrank K S :=
    Module.finrank_pos_iff.mpr hS_nontrivial
  have hmul_le :
      Module.finrank K M * Module.finrank K S ≤ Module.finrank K U * Module.finrank K S := by
    simpa [hfin_eval] using hfin_tensor_le
  have hM_le_U : Module.finrank K M ≤ Module.finrank K U :=
    le_of_mul_le_mul_right hmul_le hS_pos
  have hU_finrank : Module.finrank K U = Module.finrank K M :=
    (Submodule.finrank_le U).antisymm hM_le_U
  exact Submodule.eq_top_of_finrank_eq hU_finrank

/-- Helper for Theorem 17-17.6-1: Serre's upstairs multiplicity-space cover representation is
irreducible in the fixed-isotypic branch. -/
theorem fixed_isotypic_cover_irreducible
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let coverRep :=
      fixed_isotypic_cover_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    Representation.IsIrreducible coverRep := by
  dsimp
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let coverRep :=
    fixed_isotypic_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  letI :
      FiniteDimensional k (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
    fixed_isotypic_multiplicity_space_finiteDimensional I ρ Sbar
  have hS_nontrivial : Nontrivial Sbar.toSubmodule := by
    letI : Sbar.toRepresentation.IsIrreducible := hSbar_irred
    exact nontrivial_of_isIrreducible_local_c17 Sbar.toRepresentation
  have hM_nontrivial :
      Nontrivial (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) := by
    have hV_nontrivial : Nontrivial V :=
      nontrivial_of_isIrreducible_local_c17 ρ
    have hV_pos : 0 < Module.finrank k V :=
      Module.finrank_pos_iff.mpr hV_nontrivial
    let evalEquiv :=
      fixed_isotypic_tensor_evaluation_linearEquiv
        (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
    have hTensor_pos :
        0 <
          Module.finrank k
            (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ⊗[k]
              Sbar.toSubmodule) := by
      rwa [evalEquiv.finrank_eq]
    have hProd_pos :
        0 <
          Module.finrank k (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) *
            Module.finrank k Sbar.toSubmodule := by
      simpa [Module.finrank_tensorProduct] using hTensor_pos
    have hM_pos :
        0 <
          Module.finrank k (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
      pos_of_mul_pos_left hProd_pos (Nat.zero_le _)
    exact Module.finrank_pos_iff.mp hM_pos
  letI :
      Nontrivial (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
    hM_nontrivial
  letI : Nontrivial (Subrepresentation coverRep) :=
    subrepresentationNontrivialOfNontrivial coverRep
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro U hU
  apply Subrepresentation.toSubmodule_injective
  let evalBilin :
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
        Sbar.toSubmodule →ₗ[k] V :=
    Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype)
  let evalEquiv :=
    fixed_isotypic_tensor_evaluation_linearEquiv
      (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
  have hEval_top :
      Submodule.map₂ evalBilin U.toSubmodule ⊤ = (⊤ : Submodule k V) := by
    simpa [G2, pi, coverRep, evalBilin] using
      fixed_isotypic_cover_eval_image_eq_top_of_ne_bot
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        U hU
  have hU_top : U.toSubmodule =
      (⊤ : Submodule k (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)) :=
    submodule_eq_top_of_map₂_eq_top_of_tensor_linearEquiv
      evalBilin evalEquiv hS_nontrivial U.toSubmodule hEval_top
  simpa using hU_top

/-- Helper for Theorem 17-17.6-1: the quotient multiplicity representation remains irreducible
after descending the upstairs cover action through the Hall-kernel subgroup. -/
theorem fixed_isotypic_multiplicity_space_quotient_irreducible
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let tau :=
      fixed_isotypic_multiplicity_space_quotient_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift
    Representation.IsIrreducible tau := by
  exact
    fixed_isotypic_multiplicity_space_quotient_irreducible_of_cover_irreducible
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
      hTransportLift
      (fixed_isotypic_cover_irreducible
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift)

/-- Helper for Theorem 17-17.6-1: Serre's transport total space acts on the fixed multiplicity
space by the same source-correction formula used for the generated cover. -/
noncomputable def fixed_isotypic_transport_total_space_action_linearEquiv
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I →
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ≃ₗ[k]
        fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar :=
  fun g ↦
    (fixed_isotypic_cover_section_action_linearEquiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      g.1).trans
      (fixed_isotypic_cover_source_correction_multiplicity_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g.1 g.2)

/-- Helper for Theorem 17-17.6-1: the total-space multiplicity action has the expected
evaluation formula. -/
theorem fixed_isotypic_transport_total_space_action_linearEquiv_apply
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (g : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I)
    (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
    (x : Sbar.toSubmodule) :
    ((fixed_isotypic_transport_total_space_action_linearEquiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      g) f).toLinearMap x =
      ρ g.1
        (f ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1).symm.toLinearMap
          ((fixed_constituent_transport_fiber_reduction_equiv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
            hTransportLift g.1 g.2).toLinearMap x))) := by
  let h := (hTransport g.1).some
  let r :=
    fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
      hTransportLift g.1 g.2
  rw [fixed_isotypic_transport_total_space_action_linearEquiv,
    fixed_isotypic_cover_section_action_linearEquiv,
    fixed_isotypic_cover_source_correction_multiplicity_linearEquiv,
    fixed_isotypic_cover_source_correction_equiv]
  simp [transported_fixed_isotypic_multiplicity_space_linearEquiv,
    fixed_isotypic_multiplicity_space_precompose_linearEquiv,
    fixed_isotypic_cover_section_action_to_transport_linearEquiv,
    fixed_isotypic_cover_section_action_to_transport_linearMap]
  change
    fixed_isotypic_cover_section_action_to_transport_map
        (I := I) (ρ := ρ) Sbar g.1 f
        (h.toLinearMap (h.symm.toLinearMap (r.toLinearMap x))) =
      ρ g.1
        (f ((transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1).symm.toLinearMap
          (r.toLinearMap x)))
  have hcancel : h.toLinearMap (h.symm.toLinearMap (r.toLinearMap x)) = r.toLinearMap x := by
    simpa using h.apply_symm_apply (r.toLinearMap x)
  rw [hcancel]
  rw [fixed_isotypic_cover_section_action_to_transport_map_apply]

/-- Helper for Theorem 17-17.6-1: the identity of the transport total space acts trivially on
the fixed multiplicity space. -/
theorem fixed_isotypic_transport_total_space_action_toLinearMap_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    (fixed_isotypic_transport_total_space_action_linearEquiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (1 : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I)).toLinearMap =
      LinearMap.id := by
  rw [fixed_isotypic_transport_total_space_action_linearEquiv]
  have hG1one :
      (1 : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) =
        ⟨1,
          fixed_constituent_transport_fiber_one
            (A := A) (G := G) (I := I) ρA_I⟩ := by
    rw [← fixed_constituent_transport_total_space_one
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)]
  rw [hG1one]
  rw [fixed_isotypic_cover_section_action_linearEquiv_one
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift]
  let C :=
    fixed_isotypic_cover_source_correction_multiplicity_linearEquiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (1 : G)
      (fixed_constituent_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I)
  ext f x
  change ((C.symm.trans C) f).toLinearMap x = (LinearMap.id f).toLinearMap x
  exact congrArg (fun y => y.toLinearMap x) (C.apply_symm_apply f)

/-- Helper for Theorem 17-17.6-1: the total-space multiplicity action respects multiplication. -/
theorem fixed_isotypic_transport_total_space_action_toLinearMap_mul
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (g h : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) :
    (fixed_isotypic_transport_total_space_action_linearEquiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      (g * h)).toLinearMap =
      (fixed_isotypic_transport_total_space_action_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g).toLinearMap *
        (fixed_isotypic_transport_total_space_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          h).toLinearMap := by
  apply LinearMap.ext
  intro f
  apply Representation.IntertwiningMap.ext
  ext x
  rw [Module.End.mul_apply]
  let cgx :=
    (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1).symm.toLinearMap
      ((fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
        hTransportLift g.1 g.2).toLinearMap x)
  let chcgx :=
    (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar h.1).symm.toLinearMap
      ((fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
        hTransportLift h.1 h.2).toLinearMap cgx)
  let cghx :=
    (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (g.1 * h.1)).symm.toLinearMap
      ((fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
        hTransportLift (g.1 * h.1)
        (fixed_constituent_transport_fiber_comp
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) g.2 h.2)).toLinearMap x)
  have hsource : cghx = chcgx := by
    simpa [cghx, chcgx, cgx] using
      fixed_constituent_transport_fiber_source_correction_comp_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
        hTransportLift g.2 h.2 x
  have hgh :
      ((fixed_isotypic_transport_total_space_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          (g * h)) f).toLinearMap x =
        ρ (g.1 * h.1) (f cghx) := by
    simpa [cghx, fixed_constituent_transport_total_space_mul_eq,
      fixed_constituent_transport_total_space_mul] using
      fixed_isotypic_transport_total_space_action_linearEquiv_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (g * h) f x
  have hg :
      ((fixed_isotypic_transport_total_space_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          g)
          ((fixed_isotypic_transport_total_space_action_linearEquiv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
            h) f)).toLinearMap x =
        ρ g.1
          (((fixed_isotypic_transport_total_space_action_linearEquiv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
            h) f).toLinearMap cgx) := by
    simpa [cgx] using
      fixed_isotypic_transport_total_space_action_linearEquiv_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g
        ((fixed_isotypic_transport_total_space_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          h) f) x
  have hh :
      ((fixed_isotypic_transport_total_space_action_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        h) f).toLinearMap cgx =
        ρ h.1 (f chcgx) := by
    simpa [chcgx, cgx] using
      fixed_isotypic_transport_total_space_action_linearEquiv_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        h f cgx
  calc
    ((fixed_isotypic_transport_total_space_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          (g * h)) f).toLinearMap x =
        ρ (g.1 * h.1) (f cghx) := hgh
    _ = ρ (g.1 * h.1) (f chcgx) := by
          rw [hsource]
    _ = ρ g.1 (ρ h.1 (f chcgx)) := by
          exact LinearMap.congr_fun (ρ.map_mul g.1 h.1) (f chcgx)
    _ =
        ρ g.1
          (((fixed_isotypic_transport_total_space_action_linearEquiv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
            h) f).toLinearMap cgx) := by
          rw [hh]
    _ =
        ((fixed_isotypic_transport_total_space_action_linearEquiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          g)
          ((fixed_isotypic_transport_total_space_action_linearEquiv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
            h) f)).toLinearMap x := hg.symm

/-- Helper for Theorem 17-17.6-1: the transport total space representation on the fixed
multiplicity space. -/
noncomputable def fixed_isotypic_transport_total_space_representation
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    Representation k
      (fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I)
      (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
  { toFun := fun g ↦
      (fixed_isotypic_transport_total_space_action_linearEquiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g).toLinearMap
    map_one' :=
      fixed_isotypic_transport_total_space_action_toLinearMap_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    map_mul' :=
      fixed_isotypic_transport_total_space_action_toLinearMap_mul
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift }

/-- Helper for Theorem 17-17.6-1: the literal determinant cover acts on the fixed multiplicity
space by restricting the transport-total-space action. -/
noncomputable def fixed_isotypic_literal_determinant_cover_representation
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I
    Representation k G2 (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  (fixed_isotypic_transport_total_space_representation
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
    hTransportLift).comp (Subgroup.subtype G2)

/-- Helper for Theorem 17-17.6-1: the embedded Hall kernel acts trivially on the literal-cover
multiplicity-space representation. -/
theorem fixed_isotypic_literal_determinant_cover_action_isTrivial_on_hall_kernel
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I
    let I2 :=
      fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I
    let coverRep :=
      fixed_isotypic_literal_determinant_cover_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    Representation.IsTrivial (coverRep.comp I2.subtype) := by
  dsimp only
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let I2 :=
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I
  let coverRep :=
    fixed_isotypic_literal_determinant_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  refine Representation.IsTrivial.mk ?_
  intro y
  rcases y with ⟨g, hg⟩
  rcases hg with ⟨x, rfl⟩
  let gx :=
    fixed_constituent_literal_determinant_cover_embed_hall_kernel
      (A := A) (G := G) (I := I) (ρA_I := ρA_I) x
  apply LinearMap.ext
  intro f
  apply Representation.IntertwiningMap.ext
  ext z
  let source :=
    (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar (x : G)).symm.toLinearMap
      ((fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        (x : G)
        (fixed_constituent_transport_fiber_of_hall_kernel_element
          (A := A) (G := G) (I := I) (ρA_I := ρA_I) x)).toLinearMap z)
  have hsource : source = Sbar.toRepresentation x⁻¹ z := by
    exact
      fixed_constituent_transport_fiber_source_correction_hall_kernel_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift x z
  have happly_raw :
      ((coverRep gx f).toLinearMap z) =
        ρ (x : G) (f source) := by
    simpa [coverRep, fixed_isotypic_literal_determinant_cover_representation,
      fixed_isotypic_transport_total_space_representation, gx,
      fixed_constituent_literal_determinant_cover_embed_hall_kernel,
      fixed_constituent_transport_total_space_embed_hall_kernel, source] using
      fixed_isotypic_transport_total_space_action_linearEquiv_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        gx.1 f z
  have happly :
      ((coverRep gx f).toLinearMap z) =
        ρ (x : G) (f (Sbar.toRepresentation x⁻¹ z)) := by
    calc
      ((coverRep gx f).toLinearMap z) = ρ (x : G) (f source) := happly_raw
      _ = ρ (x : G) (f (Sbar.toRepresentation x⁻¹ z)) := by
            rw [hsource]
  have hf :
      f (Sbar.toRepresentation x⁻¹ z) =
        ρ (((x⁻¹ : I) : G)) (f z) := by
    exact
      Representation.IntertwiningMap.isIntertwining
        Sbar.toRepresentation (ρ.comp I.subtype) f x⁻¹ z
  change ((coverRep gx f).toLinearMap z) = f.toLinearMap z
  calc
    ((coverRep gx f).toLinearMap z) =
        ρ (x : G) (f (Sbar.toRepresentation x⁻¹ z)) := happly
    _ = ρ (x : G) (ρ (((x⁻¹ : I) : G)) (f z)) := by
          rw [hf]
    _ = ρ ((x : G) * (((x⁻¹ : I) : G))) (f z) := by
          exact (LinearMap.congr_fun (ρ.map_mul (x : G) (((x⁻¹ : I) : G))) (f z)).symm
    _ = f z := by
          simp

/-- Helper for Theorem 17-17.6-1: the literal determinant-cover quotient acts on the fixed
multiplicity space after quotienting by the embedded Hall kernel. -/
noncomputable def fixed_isotypic_literal_determinant_multiplicity_space_quotient_representation
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I
    let I2 :=
      fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I
    Representation k (G2 ⧸ I2)
      (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let I2 :=
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I
  let coverRep :=
    fixed_isotypic_literal_determinant_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  letI : Representation.IsTrivial (coverRep.comp I2.subtype) :=
    fixed_isotypic_literal_determinant_cover_action_isTrivial_on_hall_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  coverRep.ofQuotient I2

/-- Helper for Theorem 17-17.6-1: a nonzero subrepresentation of the fixed multiplicity space
has nonzero evaluation image, independently of which cover acts on it. -/
theorem fixed_isotypic_eval_image_ne_bot_of_ne_bot
    {Γ : Type*} [Group Γ]
    (I : Subgroup G) [I.Normal]
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (τ : Representation k Γ (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar))
    (U : Subrepresentation τ)
    (hU : U ≠ ⊥) :
    let evalBilin :
        fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
          Sbar.toSubmodule →ₗ[k] V :=
      Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype)
    let evalImage : Submodule k V := Submodule.map₂ evalBilin U.toSubmodule ⊤
    evalImage ≠ ⊥ := by
  dsimp
  let evalBilin :
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
        Sbar.toSubmodule →ₗ[k] V :=
    Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype)
  let evalImage : Submodule k V := Submodule.map₂ evalBilin U.toSubmodule ⊤
  intro hEval
  have hUbot : U.toSubmodule = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro f hf
    by_contra hf_ne
    have hf_map_ne : ∃ x : Sbar.toSubmodule, evalBilin f x ≠ 0 := by
      by_contra hzero
      apply hf_ne
      apply Representation.IntertwiningMap.ext
      ext x
      exact not_not.mp fun hx ↦ hzero ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hf_map_ne
    have hx_mem : evalBilin f x ∈ evalImage :=
      Submodule.apply_mem_map₂ evalBilin hf Submodule.mem_top
    have hEval' : evalImage = ⊥ := by
      simpa [evalImage, evalBilin] using hEval
    have hx_bot : evalBilin f x ∈ (⊥ : Submodule k V) := by
      simpa [hEval'] using hx_mem
    exact hx hx_bot
  apply hU
  apply Subrepresentation.toSubmodule_injective
  simpa using hUbot

/-- Helper for Theorem 17-17.6-1: an upstairs action satisfying Serre's tensor-evaluation formula
is irreducible whenever its projection to `G` is surjective. -/
theorem fixed_isotypic_cover_irreducible_of_surjective_action_formula
    {Γ : Type*} [Group Γ]
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    (π : Γ →* G)
    (hπ_surj : Function.Surjective π)
    (coverRep :
      Representation k Γ (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar))
    (sourceTransport : Γ → Sbar.toSubmodule ≃ₗ[k] Sbar.toSubmodule)
    (hcover_eval :
      ∀ (g : Γ) (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
        (x : Sbar.toSubmodule),
        (Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype))
          (coverRep g f) ((sourceTransport g).symm x) =
        ρ (π g)
          ((Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype))
            f x)) :
    Representation.IsIrreducible coverRep := by
  letI :
      FiniteDimensional k (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
    fixed_isotypic_multiplicity_space_finiteDimensional I ρ Sbar
  have hS_nontrivial : Nontrivial Sbar.toSubmodule := by
    letI : Sbar.toRepresentation.IsIrreducible := hSbar_irred
    exact nontrivial_of_isIrreducible_local_c17 Sbar.toRepresentation
  have hM_nontrivial :
      Nontrivial (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) := by
    have hV_nontrivial : Nontrivial V :=
      nontrivial_of_isIrreducible_local_c17 ρ
    let evalEquiv :=
      fixed_isotypic_tensor_evaluation_linearEquiv
        (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
    have hTensor_pos :
        0 <
          Module.finrank k
            (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ⊗[k]
              Sbar.toSubmodule) := by
      have hV_pos : 0 < Module.finrank k V :=
        Module.finrank_pos_iff.mpr hV_nontrivial
      rwa [evalEquiv.finrank_eq]
    have hProd_pos :
        0 <
          Module.finrank k (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) *
            Module.finrank k Sbar.toSubmodule := by
      simpa [Module.finrank_tensorProduct] using hTensor_pos
    have hM_pos :
        0 <
          Module.finrank k (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
      pos_of_mul_pos_left hProd_pos (Nat.zero_le _)
    exact Module.finrank_pos_iff.mp hM_pos
  letI :
      Nontrivial (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar) :=
    hM_nontrivial
  letI : Nontrivial (Subrepresentation coverRep) :=
    subrepresentationNontrivialOfNontrivial coverRep
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro U hU
  apply Subrepresentation.toSubmodule_injective
  let evalBilin :
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar →ₗ[k]
        Sbar.toSubmodule →ₗ[k] V :=
    Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype)
  let evalImage : Submodule k V := Submodule.map₂ evalBilin U.toSubmodule ⊤
  have hstable :
      ∀ (g : Γ) {y : V}, y ∈ evalImage → (ρ.comp π) g y ∈ evalImage := by
    intro g y hy
    have hmap : evalImage.map (ρ (π g)) ≤ evalImage := by
      rw [Submodule.map_le_iff_le_comap]
      rw [Submodule.map₂_le]
      intro f hf x hx
      change ρ (π g) (evalBilin f x) ∈ evalImage
      rw [← hcover_eval g f x]
      exact
        Submodule.apply_mem_map₂ evalBilin (U.apply_mem_toSubmodule g hf) Submodule.mem_top
    exact hmap ⟨y, hy, rfl⟩
  have hEval_ne_bot : evalImage ≠ ⊥ := by
    simpa [evalImage, evalBilin] using
      fixed_isotypic_eval_image_ne_bot_of_ne_bot
        (I := I) (ρ := ρ) (Sbar := Sbar) coverRep U hU
  have hApply :
      ∀ (g : Γ) {y : V}, y ∈ evalImage → (ρ.comp π) g y ∈ evalImage :=
    hstable
  let W : Subrepresentation (ρ.comp π) :=
    { toSubmodule := evalImage
      apply_mem_toSubmodule := hApply }
  have hCompIrred : Representation.IsIrreducible (ρ.comp π) :=
    isIrreducible_comp_of_surjective π hπ_surj ρ
  have hW_ne_bot : W ≠ ⊥ := by
    intro hW
    apply hEval_ne_bot
    have hW_sub : W.toSubmodule = (⊥ : Submodule k V) :=
      congrArg Subrepresentation.toSubmodule hW
    simpa [W] using hW_sub
  letI : Representation.IsIrreducible (ρ.comp π) := hCompIrred
  have hW_top : W = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hW_ne_bot
  have hEval_top : evalImage = (⊤ : Submodule k V) := by
    have hW_sub_top : W.toSubmodule = (⊤ : Submodule k V) :=
      congrArg Subrepresentation.toSubmodule hW_top
    simpa [W] using hW_sub_top
  let evalEquiv :=
    fixed_isotypic_tensor_evaluation_linearEquiv
      (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
  have hU_top : U.toSubmodule =
      (⊤ : Submodule k (fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)) :=
    submodule_eq_top_of_map₂_eq_top_of_tensor_linearEquiv
      evalBilin evalEquiv hS_nontrivial U.toSubmodule hEval_top
  simpa using hU_top

/-- Helper for Theorem 17-17.6-1: the literal determinant-cover multiplicity-space action is
irreducible when the literal cover surjects onto `G`. -/
theorem fixed_isotypic_literal_determinant_cover_irreducible
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hproj_surj :
      Function.Surjective
        (fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I))) :
    let coverRep :=
      fixed_isotypic_literal_determinant_cover_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
    Representation.IsIrreducible coverRep := by
  dsimp
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let π : G2 →* G :=
    fixed_constituent_literal_determinant_cover_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  let coverRep :=
    fixed_isotypic_literal_determinant_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  let sourceTransport : G2 → Sbar.toSubmodule ≃ₗ[k] Sbar.toSubmodule := fun g ↦
    (fixed_constituent_transport_fiber_reduction_equiv
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      g.1.1 g.1.2).toLinearEquiv.trans
      (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1.1).symm.toLinearEquiv
  have hcover_eval :
      ∀ (g : G2) (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
        (x : Sbar.toSubmodule),
        (Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype))
          (coverRep g f) ((sourceTransport g).symm x) =
        ρ (π g)
          ((Representation.IntertwiningMap.toLinearMapl Sbar.toRepresentation (ρ.comp I.subtype))
            f x) := by
    intro g f x
    have hraw :=
      fixed_isotypic_transport_total_space_action_linearEquiv_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g.1 f ((sourceTransport g).symm x)
    have hsource :
        (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1.1).symm.toLinearMap
          ((fixed_constituent_transport_fiber_reduction_equiv
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
            hTransportLift g.1.1 g.1.2).toLinearMap ((sourceTransport g).symm x)) =
          x := by
      change (sourceTransport g) ((sourceTransport g).symm x) = x
      exact LinearEquiv.apply_symm_apply (sourceTransport g) x
    rw [hsource] at hraw
    simpa [coverRep, fixed_isotypic_literal_determinant_cover_representation,
      fixed_isotypic_transport_total_space_representation, π, sourceTransport] using hraw
  exact
    fixed_isotypic_cover_irreducible_of_surjective_action_formula
      (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred hSbar_top π
      (by simpa [π] using hproj_surj) coverRep sourceTransport hcover_eval

/-- Helper for Theorem 17-17.6-1: the literal determinant-cover quotient multiplicity
representation is irreducible. -/
theorem fixed_isotypic_literal_determinant_multiplicity_space_quotient_irreducible
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hproj_surj :
      Function.Surjective
        (fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I))) :
    let tau :=
      fixed_isotypic_literal_determinant_multiplicity_space_quotient_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift
    Representation.IsIrreducible tau := by
  dsimp
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let I2 :=
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I
  let coverRep :=
    fixed_isotypic_literal_determinant_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  letI : Representation.IsTrivial (coverRep.comp I2.subtype) :=
    fixed_isotypic_literal_determinant_cover_action_isTrivial_on_hall_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  letI : coverRep.IsIrreducible :=
    fixed_isotypic_literal_determinant_cover_irreducible
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
      hTransportLift hproj_surj
  simpa [fixed_isotypic_literal_determinant_multiplicity_space_quotient_representation,
    G2, I2, coverRep] using
    isIrreducible_of_ofQuotient_of_isTrivial_c17 coverRep I2

/-- Helper for Theorem 17-17.6-1: a residue-field lift of Serre's quotient multiplicity
representation inflates to a lift of the upstairs cover action on the multiplicity space. -/
theorem fixed_isotypic_cover_lift_of_quotient_lift
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    {P_tau : Type (max u v x)} [AddCommGroup P_tau] [Module A P_tau]
    [Module.Free A P_tau] [Module.Finite A P_tau]
    (ρA_tau :
      Representation A
        ((fixed_constituent_generated_cover_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift) ⧸
          fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)
        P_tau)
    (red_tau :
      P_tau →ₗ[A] fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
    (hLiftTau :
      IsResidueFieldLift
        (fixed_isotypic_multiplicity_space_quotient_representation
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
          hTransportLift)
        ρA_tau red_tau) :
    IsResidueFieldLift
      (fixed_isotypic_cover_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift)
      (ρA_tau.comp
        (QuotientGroup.mk'
          (fixed_constituent_generated_cover_hall_kernel_subgroup
            (p := p) (A := A) (G := G) (V := V)
            hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift)))
      red_tau := by
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let coverRep :=
    fixed_isotypic_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  let tau :=
    fixed_isotypic_multiplicity_space_quotient_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
      hTransportLift
  letI : Representation.IsTrivial (coverRep.comp I2.subtype) :=
    fixed_isotypic_cover_action_isTrivial_on_hall_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  have hInflated :
      IsResidueFieldLift
        (tau.comp (QuotientGroup.mk' I2))
        (ρA_tau.comp (QuotientGroup.mk' I2))
        red_tau :=
    Representation.isResidueFieldLift_comp hLiftTau (QuotientGroup.mk' I2)
  have hInflatedCover :
      IsResidueFieldLift
        ((coverRep.ofQuotient I2).comp (QuotientGroup.mk' I2))
        (ρA_tau.comp (QuotientGroup.mk' I2))
        red_tau := by
    simpa [tau, fixed_isotypic_multiplicity_space_quotient_representation, G2, I2, coverRep]
      using hInflated
  have hCoverEq : coverRep = (coverRep.ofQuotient I2).comp (QuotientGroup.mk' I2) := by
    ext g x
    simp [Representation.ofQuotient_coe_apply]
  change
    IsResidueFieldLift coverRep (ρA_tau.comp (QuotientGroup.mk' I2)) red_tau
  rw [hCoverEq]
  exact hInflatedCover

omit [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: the identity element of Serre's generated cover acts as the
identity on the fixed lifted constituent. -/
theorem fixed_constituent_generated_cover_fiber_action_toLinearMap_one
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    ((1 : G2).1.2).toLinearMap = LinearMap.id := by
  dsimp
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  change
    (((1 : G2) :
        fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I).2).toLinearMap =
      LinearMap.id
  have hG2one :
      ((1 : G2) :
          fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) =
        ⟨1, fixed_constituent_transport_fiber_one (A := A) (G := G) (I := I) ρA_I⟩ := by
    rw [← fixed_constituent_transport_total_space_one
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)]
    rfl
  rw [hG2one]
  ext x
  simp [fixed_constituent_transport_fiber_one, Representation.Equiv.mk]

omit [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: the transport-fiber action of Serre's generated cover
respects multiplication on the fixed lifted constituent. -/
theorem fixed_constituent_generated_cover_fiber_action_toLinearMap_mul
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ g h : G2, ((g * h).1.2).toLinearMap = g.1.2.toLinearMap * h.1.2.toLinearMap := by
  dsimp
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  intro g h
  change
    (((g * h : G2) :
        fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I).2).toLinearMap =
      g.1.2.toLinearMap * h.1.2.toLinearMap
  ext x
  rfl

omit [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: Serre's generated cover acts on the fixed lifted constituent
through the transport-fiber linear maps. -/
noncomputable def fixed_constituent_generated_cover_fiber_representation
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    Representation A G2 P_S :=
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  { toFun := fun g ↦ g.1.2.toLinearMap
    map_one' :=
      fixed_constituent_generated_cover_fiber_action_toLinearMap_one
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    map_mul' :=
      fixed_constituent_generated_cover_fiber_action_toLinearMap_mul
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift }

omit [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: reducing the generated-cover action on the lifted fixed
constituent gives the source correction used in Serre's cover action. -/
theorem fixed_constituent_generated_cover_fiber_source_correction_apply_red
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ (g : G2) (z : P_S),
      let e := transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1.1
      let r :=
        fixed_constituent_transport_fiber_reduction_equiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          g.1.1 g.1.2
      e.symm.toLinearMap (r.toLinearMap (red_S (g.1.2.toLinearMap z))) = red_S z := by
  dsimp
  intro g z
  have hsource :=
    fixed_constituent_transport_fiber_source_correction_apply_red
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      g.1.1 g.1.2 (g.1.2.toLinearMap z)
  simpa using hsource

/-- Helper for Theorem 17-17.6-1: reducing both lifted tensor factors makes the generated-cover
pure tensor action agree with the pulled-back ambient action under tensor evaluation. -/
theorem fixed_constituent_generated_cover_tensor_evaluation_apply_red_tmul
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    ∀ (g : G2)
      (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
      (z : P_S),
      fixed_isotypic_tensor_evaluation_linearEquiv
          (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
          (((fixed_isotypic_cover_representation
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
              hTransportLift g) f) ⊗ₜ[k] red_S (g.1.2.toLinearMap z)) =
        ρ g.1.1
          (fixed_isotypic_tensor_evaluation_linearEquiv
            (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
            (f ⊗ₜ[k] red_S z)) := by
  dsimp
  intro g f z
  rw [fixed_isotypic_tensor_evaluation_cover_action_tmul
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
    hTransportLift]
  have hsource :=
    fixed_constituent_generated_cover_fiber_source_correction_apply_red
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
      g z
  have hsource' :
      (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1.1).symm.toLinearMap
        ((fixed_constituent_transport_fiber_reduction_equiv
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          g.1.1 g.1.2).toLinearMap (red_S (g.1.2 z))) = red_S z := by
    simpa using hsource
  exact
    (congrArg (fun x ↦ ρ g.1.1 (f x)) hsource').trans
      (congrArg (ρ g.1.1)
        (fixed_isotypic_tensor_evaluation_linearEquiv_tmul
          (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
          f (red_S z)).symm)

/-- Helper for Theorem 17-17.6-1: a lift of the quotient multiplicity module tensors with the
fixed constituent lift and descends to a lift of the original representation. -/
theorem descend_lift_of_fixed_constituent_tensor
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hNbarData :
      let G2 :=
        fixed_constituent_generated_cover_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      let I2 :=
        fixed_constituent_generated_cover_hall_kernel_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      let pi2 : G2 ⧸ I2 →* G ⧸ I :=
        generated_cover_proj_to_quotient_descends
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
      let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
      Finite Nbar ∧ Nat.Coprime p (Nat.card Nbar)) :
    let G2 :=
      fixed_constituent_generated_cover_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let I2 :=
      fixed_constituent_generated_cover_hall_kernel_subgroup
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
    let tau :=
      fixed_isotypic_multiplicity_space_quotient_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift
    ∀ {P_tau : Type (max u v x)} (_ : AddCommGroup P_tau) (_ : Module A P_tau)
      (_ : Module.Free A P_tau) (_ : Module.Finite A P_tau)
      (ρA_tau : Representation A (G2 ⧸ I2) P_tau)
      (red_tau :
        P_tau →ₗ[A] fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar),
        IsResidueFieldLift tau ρA_tau red_tau →
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G P)
            (red : P →ₗ[A] V),
              IsResidueFieldLift ρ ρA red := by
  dsimp at hNbarData ⊢
  intro P_tau hP_tau_add hP_tau_module hP_tau_free hP_tau_finite ρA_tau red_tau hLiftTau
  letI : AddCommGroup P_tau := hP_tau_add
  letI : Module A P_tau := hP_tau_module
  letI : Module.Free A P_tau := hP_tau_free
  letI : Module.Finite A P_tau := hP_tau_finite
  let G2 :=
    fixed_constituent_generated_cover_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let I2 :=
    fixed_constituent_generated_cover_hall_kernel_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    generated_cover_proj_to_quotient_descends
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
  let coverRep :=
    fixed_isotypic_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  have hCoverLift :
      IsResidueFieldLift coverRep (ρA_tau.comp (QuotientGroup.mk' I2)) red_tau := by
    simpa [G2, I2, coverRep] using
      fixed_isotypic_cover_lift_of_quotient_lift
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift ρA_tau red_tau hLiftTau
  have hCoverLift_apply :
      ∀ (g : G2) (y : P_tau),
        red_tau ((ρA_tau.comp (QuotientGroup.mk' I2)) g y) =
          coverRep g (red_tau y) := by
    intro g y
    exact
      isResidueFieldLift_apply
        (A := A) coverRep (ρA_tau.comp (QuotientGroup.mk' I2)) red_tau hCoverLift g y
  let ρA_S_cover :=
    fixed_constituent_generated_cover_fiber_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hTensorPure_apply :
      ∀ (g : G2) (y : P_tau) (z : P_S),
        fixed_isotypic_tensor_evaluation_linearEquiv
            (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
            (red_tau ((ρA_tau.comp (QuotientGroup.mk' I2)) g y) ⊗ₜ[k]
              red_S (ρA_S_cover g z)) =
          ρ g.1.1
            (fixed_isotypic_tensor_evaluation_linearEquiv
              (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
              (red_tau y ⊗ₜ[k] red_S z)) := by
    intro g y z
    rw [hCoverLift_apply g y]
    simpa [ρA_S_cover] using
      fixed_constituent_generated_cover_tensor_evaluation_apply_red_tmul
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift g (red_tau y) z
  let evalTensor :
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ⊗[k] Sbar.toSubmodule
        →ₗ[k] V :=
    (fixed_isotypic_tensor_evaluation_linearEquiv
      (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top).toLinearMap
  obtain ⟨redTensor, hredTensor_tmul⟩ :
      ∃ redTensor : P_tau ⊗[A] P_S →ₗ[A] V,
        ∀ (y : P_tau) (z : P_S),
          redTensor (y ⊗ₜ[A] z) =
            evalTensor (red_tau y ⊗ₜ[k] red_S z) :=
    exists_tensorProduct_reduction_of_residue_maps
      (A := A) evalTensor red_tau red_S
  let ρA_tensor : Representation A G2 (P_tau ⊗[A] P_S) :=
    Representation.tprod (ρA_tau.comp (QuotientGroup.mk' I2)) ρA_S_cover
  have hρA_tensor_tmul :
      ∀ (g : G2) (y : P_tau) (z : P_S),
        ρA_tensor g (y ⊗ₜ[A] z) =
          ((ρA_tau.comp (QuotientGroup.mk' I2)) g y) ⊗ₜ[A] ρA_S_cover g z := by
    intro g y z
    simp [ρA_tensor, Representation.tprod_apply]
  have hTensorReduction_tmul :
      ∀ (g : G2) (y : P_tau) (z : P_S),
        redTensor (ρA_tensor g (y ⊗ₜ[A] z)) =
          ρ g.1.1 (redTensor (y ⊗ₜ[A] z)) := by
    intro g y z
    rw [hρA_tensor_tmul]
    rw [hredTensor_tmul, hredTensor_tmul]
    exact hTensorPure_apply g y z
  have hTensorReduction_intertwines :
      ∀ (g : G2) (t : P_tau ⊗[A] P_S),
        redTensor (ρA_tensor g t) = ρ g.1.1 (redTensor t) := by
    intro g t
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp
    · intro y z
      exact hTensorReduction_tmul g y z
    · intro t₁ t₂ ht₁ ht₂
      simp [map_add, ht₁, ht₂]
  have hTensorBaseChange : IsBaseChange k redTensor := by
    exact
      tensorProduct_reduction_isBaseChange_of_residue_maps
        (fixed_isotypic_tensor_evaluation_linearEquiv
          (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top)
        red_tau red_S hLiftTau.1 hLiftSbar.1 redTensor hredTensor_tmul
  let pi : G2 →* G :=
    (fixed_constituent_transport_total_space_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)).comp
      (Subgroup.subtype G2)
  let rhoPull : Representation k G2 V := ρ.comp pi
  have hTensorIntertwining :
      ∀ (g : G2) (t : P_tau ⊗[A] P_S),
        redTensor (ρA_tensor g t) = rhoPull g (redTensor t) := by
    intro g t
    simpa [rhoPull, pi] using
      hTensorReduction_intertwines g t
  have hTensorLift :
      IsResidueFieldLift rhoPull ρA_tensor redTensor := by
    exact
      isResidueFieldLift_of_isBaseChange_apply
        rhoPull ρA_tensor redTensor hTensorBaseChange hTensorIntertwining
  let K : Subgroup G2 := pi.ker
  have hTensorKernelLift :
      IsResidueFieldLift
        (rhoPull.comp K.subtype)
        (ρA_tensor.comp K.subtype)
        redTensor :=
    Representation.isResidueFieldLift_comp hTensorLift K.subtype
  have hTensorKernelSourceTrivial :
      Representation.IsTrivial (rhoPull.comp K.subtype) := by
    refine Representation.IsTrivial.mk ?_
    intro z
    ext x
    have hz : pi z.1 = 1 := z.2
    change ρ (pi z.1) x = x
    rw [hz]
    simp
  have hTensorKernelSourceEq :
      rhoPull.comp K.subtype = Representation.trivial k K V := by
    ext z x
    have hz : pi z.1 = 1 := z.2
    change ρ (pi z.1) x = x
    rw [hz]
    simp
  have hTensorKernelLift_trivialSource :
      IsResidueFieldLift
        (Representation.trivial k K V)
        (ρA_tensor.comp K.subtype)
        redTensor := by
    rw [← hTensorKernelSourceEq]
    exact hTensorKernelLift
  let kernelEquiv : K ≃* Nbar := by
    simpa [G2, I2, pi2, Nbar, pi, K] using
      generated_cover_kernel_equiv_nbar
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  have hKfinite : Finite K := by
    letI : Finite Nbar := hNbarData.1
    exact Finite.of_equiv Nbar kernelEquiv.symm.toEquiv
  have hKcop : Nat.Coprime p (Nat.card K) := by
    have hcard : Nat.card K = Nat.card Nbar := Nat.card_congr kernelEquiv.toEquiv
    rw [hcard]
    exact hNbarData.2
  letI : Finite K := hKfinite
  have hTensorKernelTrivial :
      Representation.IsTrivial (ρA_tensor.comp K.subtype) := by
    exact
      isTrivial_of_residueFieldLift_trivial_of_coprime_card_any
        (A := A) (p := p) hp hTensorKernelLift_trivialSource hKcop
  letI : Representation.IsTrivial (ρA_tensor.comp K.subtype) := hTensorKernelTrivial
  have hpi_surj : Function.Surjective pi := by
    simpa [G2, pi] using
      fixed_constituent_generated_cover_proj_surjective
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift
  let ρA : Representation A G (P_tau ⊗[A] P_S) :=
    (ρA_tensor.ofQuotient K).comp
      (QuotientGroup.quotientKerEquivOfSurjective pi hpi_surj).symm.toMonoidHom
  have hFinalLift : IsResidueFieldLift ρ ρA redTensor := by
    simpa [ρA, rhoPull] using
      isResidueFieldLift_descend_of_surjective
        (A := A) pi hpi_surj ρ ρA_tensor redTensor hTensorLift
  exact
    ⟨P_tau ⊗[A] P_S, inferInstance, inferInstance, inferInstance, inferInstance,
      ρA, redTensor, hFinalLift⟩

omit [CharP k p] [FiniteDimensional k V] [IsAlgClosed k] in
/-- Helper for Theorem 17-17.6-1: Serre's literal determinant cover is finite once its
projection kernel is finite. -/
theorem fixed_constituent_literal_determinant_cover_finite_of_finite_kernel
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    let G2 :=
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I
    let pi : G2 →* G :=
      fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
    Finite pi.ker → Finite G2 := by
  dsimp
  intro hKernelFinite
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let pi : G2 →* G :=
    fixed_constituent_literal_determinant_cover_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  have hRangeFinite : Finite pi.range := by
    exact Finite.of_injective (fun y : pi.range => (y : G)) Subtype.val_injective
  exact (MonoidHom.finite_iff_finite_ker_range pi).2 ⟨hKernelFinite, hRangeFinite⟩

/-- Helper for Theorem 17-17.6-1: Serre's literal quotient kernel is finite cyclic and has order
prime to the residue characteristic. -/
theorem literal_determinant_cover_quotient_kernel_finite_cyclic_coprime
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    let G2 :=
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I
    let I2 :=
      fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      fixed_constituent_literal_determinant_cover_proj_to_quotient
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
    let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
    Finite Nbar ∧ IsCyclic Nbar ∧ Nat.Coprime p (Nat.card Nbar) := by
  dsimp
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let I2 :=
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    fixed_constituent_literal_determinant_cover_proj_to_quotient
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
  let pi : G2 →* G :=
    fixed_constituent_literal_determinant_cover_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  let K : Subgroup G2 := pi.ker
  have hK : Finite K ∧ IsCyclic K ∧ Nat.Coprime p (Nat.card K) := by
    simpa [K, pi] using
      literal_determinant_cover_kernel_finite_cyclic_coprime
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  let e : K ≃* Nbar := by
    simpa [G2, I2, pi2, Nbar, pi, K] using
      literal_determinant_cover_kernel_equiv_quotient_kernel
        (A := A) (G := G) (I := I) ρA_I
  have hNbarFinite : Finite Nbar := by
    letI : Finite K := hK.1
    exact Finite.of_equiv K e.toEquiv
  have hNbarCyclic : IsCyclic Nbar := by
    letI : IsCyclic K := hK.2.1
    exact isCyclic_of_surjective e e.surjective
  have hNbarCoprime : Nat.Coprime p (Nat.card Nbar) := by
    letI : Finite K := hK.1
    letI : Finite Nbar := hNbarFinite
    have hcard : Nat.card Nbar = Nat.card K := (Nat.card_congr e.toEquiv).symm
    rw [hcard]
    exact hK.2.2
  exact ⟨hNbarFinite, hNbarCyclic, hNbarCoprime⟩

/-- Helper for Theorem 17-17.6-1: Serre's literal quotient kernel is central in the literal
quotient cover. -/
theorem literal_determinant_cover_quotient_kernel_central
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S) :
    let G2 :=
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I
    let I2 :=
      fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I
    let pi2 : G2 ⧸ I2 →* G ⧸ I :=
      fixed_constituent_literal_determinant_cover_proj_to_quotient
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
    pi2.ker ≤ Subgroup.center (G2 ⧸ I2) := by
  dsimp
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let I2 :=
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    fixed_constituent_literal_determinant_cover_proj_to_quotient
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  let pi : G2 →* G :=
    fixed_constituent_literal_determinant_cover_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro y
  rcases QuotientGroup.mk'_surjective I2 y with ⟨g, rfl⟩
  let K : Subgroup G2 := pi.ker
  let qN : pi2.ker := ⟨q, hq⟩
  let e : K ≃* pi2.ker := by
    simpa [G2, I2, pi2, pi, K] using
      literal_determinant_cover_kernel_equiv_quotient_kernel
        (A := A) (G := G) (I := I) ρA_I
  obtain ⟨z, hz⟩ := e.surjective qN
  have hmk : QuotientGroup.mk' I2 z.1 = q := by
    have hzval := congrArg Subtype.val hz
    simpa [e, literal_determinant_cover_kernel_equiv_quotient_kernel,
      literal_determinant_cover_kernel_to_quotient_kernel_hom, G2, I2, pi2, pi, K, qN]
      using hzval
  let a : Aˣ :=
    ((literal_determinant_cover_kernel_scalar
      (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z : _) : Aˣ)
  have hproj : z.1.1.1 = 1 := by
    have hzproj : pi z.1 = 1 := z.2
    simpa [pi, fixed_constituent_literal_determinant_cover_proj_hom,
      fixed_constituent_transport_total_space_proj_hom,
      fixed_constituent_transport_total_space_proj] using hzproj
  have hlin : z.1.1.2.toLinearEquiv = a • LinearEquiv.refl A P_S := by
    simpa [a] using
      literal_determinant_cover_kernel_scalar_spec
        (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar z
  have hscalar :
      (scalar_transport_fiber_one
        (A := A) (G := G) (I := I) ρA_I a).toLinearEquiv =
        a • LinearEquiv.refl A P_S := by
    simp [scalar_transport_fiber_one, Equiv.toLinearEquiv_mk']
  have hz_scalar :
      z.1.1 =
        ⟨1, scalar_transport_fiber_one (A := A) (G := G) (I := I) ρA_I a⟩ := by
    apply Sigma.ext
    · exact hproj
    · exact
        literal_determinant_cover_transport_fiber_heq_of_toLinearEquiv_eq
          (A := A) (G := G) I ρA_I hproj (hlin.trans hscalar.symm)
  have hcomm_total : g.1 * z.1.1 = z.1.1 * g.1 := by
    rw [hz_scalar]
    rw [fixed_constituent_transport_total_space_mul_eq]
    rw [fixed_constituent_transport_total_space_mul_eq]
    exact
      (scalar_transport_total_space_commutes
        (A := A) (G := G) (I := I) ρA_I a g.1).symm
  have hcomm : g * z.1 = z.1 * g := by
    apply Subtype.ext
    exact hcomm_total
  calc
    QuotientGroup.mk' I2 g * q =
        QuotientGroup.mk' I2 g * QuotientGroup.mk' I2 z.1 := by
          rw [hmk]
    _ = QuotientGroup.mk' I2 (g * z.1) := by
          rw [map_mul]
    _ = QuotientGroup.mk' I2 (z.1 * g) := by
          rw [hcomm]
    _ = QuotientGroup.mk' I2 z.1 * QuotientGroup.mk' I2 g := by
          rw [map_mul]
    _ = q * QuotientGroup.mk' I2 g := by
          rw [hmk]

/-- Helper for Theorem 17-17.6-1: the identity of Serre's transport total space acts as the
identity on the fixed lifted constituent. -/
theorem fixed_constituent_transport_total_space_fiber_action_toLinearMap_one
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    ((1 :
      fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I).2).toLinearMap =
      LinearMap.id := by
  have hG2one :
      (1 : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) =
        ⟨1, fixed_constituent_transport_fiber_one (A := A) (G := G) (I := I) ρA_I⟩ := by
    rw [← fixed_constituent_transport_total_space_one
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)]
  rw [hG2one]
  ext x
  simp [fixed_constituent_transport_fiber_one, Representation.Equiv.mk]

/-- Helper for Theorem 17-17.6-1: the transport-fiber action of Serre's total space respects
multiplication on the fixed lifted constituent. -/
theorem fixed_constituent_transport_total_space_fiber_action_toLinearMap_mul
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (g h : fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) :
    ((g * h).2).toLinearMap = g.2.toLinearMap * h.2.toLinearMap := by
  change
    ((fixed_constituent_transport_total_space_mul
        (A := A) (G := G) (I := I) (ρA_I := ρA_I) g h).2).toLinearMap =
      g.2.toLinearMap * h.2.toLinearMap
  ext x
  rfl

/-- Helper for Theorem 17-17.6-1: Serre's transport total space acts on the fixed lifted
constituent through its transport-fiber linear maps. -/
noncomputable def fixed_constituent_transport_total_space_fiber_representation
    (I : Subgroup G) [I.Normal]
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S) :
    Representation A
      (fixed_constituent_transport_total_space (A := A) (G := G) I ρA_I) P_S :=
  { toFun := fun g ↦ g.2.toLinearMap
    map_one' :=
      fixed_constituent_transport_total_space_fiber_action_toLinearMap_one
        I ρA_I
    map_mul' :=
      fixed_constituent_transport_total_space_fiber_action_toLinearMap_mul
        I ρA_I }

/-- Helper for Theorem 17-17.6-1: a residue-field lift of Serre's literal quotient multiplicity
representation inflates to a lift of the upstairs literal-cover action. -/
theorem fixed_isotypic_literal_determinant_cover_lift_of_quotient_lift
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    {P_tau : Type (max u v x)} [AddCommGroup P_tau] [Module A P_tau]
    [Module.Free A P_tau] [Module.Finite A P_tau]
    (ρA_tau :
      Representation A
        ((fixed_constituent_literal_determinant_cover_local
          (A := A) (G := G) (I := I) ρA_I) ⧸
          fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
            (A := A) (G := G) (I := I) ρA_I)
        P_tau)
    (red_tau :
      P_tau →ₗ[A] fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
    (hLiftTau :
      IsResidueFieldLift
        (fixed_isotypic_literal_determinant_multiplicity_space_quotient_representation
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
          hTransportLift)
        ρA_tau red_tau) :
    IsResidueFieldLift
      (fixed_isotypic_literal_determinant_cover_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift)
      (ρA_tau.comp
        (QuotientGroup.mk'
          (fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
            (A := A) (G := G) (I := I) ρA_I)))
      red_tau := by
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let I2 :=
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I
  let coverRep :=
    fixed_isotypic_literal_determinant_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  let tau :=
    fixed_isotypic_literal_determinant_multiplicity_space_quotient_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
      hTransportLift
  letI : Representation.IsTrivial (coverRep.comp I2.subtype) :=
    fixed_isotypic_literal_determinant_cover_action_isTrivial_on_hall_kernel
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  have hInflated :
      IsResidueFieldLift
        (tau.comp (QuotientGroup.mk' I2))
        (ρA_tau.comp (QuotientGroup.mk' I2))
        red_tau :=
    Representation.isResidueFieldLift_comp hLiftTau (QuotientGroup.mk' I2)
  have hInflatedCover :
      IsResidueFieldLift
        ((coverRep.ofQuotient I2).comp (QuotientGroup.mk' I2))
        (ρA_tau.comp (QuotientGroup.mk' I2))
        red_tau := by
    simpa [tau, fixed_isotypic_literal_determinant_multiplicity_space_quotient_representation,
      G2, I2, coverRep] using hInflated
  have hCoverEq : coverRep = (coverRep.ofQuotient I2).comp (QuotientGroup.mk' I2) := by
    ext g x
    simp [Representation.ofQuotient_coe_apply]
  change
    IsResidueFieldLift coverRep (ρA_tau.comp (QuotientGroup.mk' I2)) red_tau
  rw [hCoverEq]
  exact hInflatedCover

/-- Helper for Theorem 17-17.6-1: reducing both lifted tensor factors makes the literal-cover
pure tensor action agree with the pulled-back ambient action under tensor evaluation. -/
theorem fixed_constituent_literal_determinant_cover_tensor_evaluation_apply_red_tmul
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    let G2 :=
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I
    ∀ (g : G2)
      (f : fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar)
      (z : P_S),
      fixed_isotypic_tensor_evaluation_linearEquiv
          (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
          (((fixed_isotypic_literal_determinant_cover_representation
              (p := p) (A := A) (G := G) (V := V)
              hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport
              hTransportLift g) f) ⊗ₜ[k] red_S (g.1.2.toLinearMap z)) =
        ρ g.1.1
          (fixed_isotypic_tensor_evaluation_linearEquiv
            (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
            (f ⊗ₜ[k] red_S z)) := by
  dsimp
  intro g f z
  rw [fixed_isotypic_tensor_evaluation_linearEquiv_tmul]
  let source :=
    (transportedSubrepresentation_rep_equiv_local_c17 ρ Sbar g.1.1).symm.toLinearMap
      ((fixed_constituent_transport_fiber_reduction_equiv
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g.1.1 g.1.2).toLinearMap (red_S (g.1.2.toLinearMap z)))
  have hcover :
      ((fixed_isotypic_literal_determinant_cover_representation
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          g f).toLinearMap (red_S (g.1.2.toLinearMap z))) =
        ρ g.1.1 (f source) := by
    simpa [fixed_isotypic_literal_determinant_cover_representation,
      fixed_isotypic_transport_total_space_representation, source] using
      fixed_isotypic_transport_total_space_action_linearEquiv_apply
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g.1 f (red_S (g.1.2.toLinearMap z))
  have hsource :
      source = red_S z := by
    have hraw :=
      fixed_constituent_transport_fiber_source_correction_apply_red
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
        g.1.1 g.1.2 (g.1.2.toLinearMap z)
    simpa [source] using hraw
  calc
    ((fixed_isotypic_literal_determinant_cover_representation
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
          g f).toLinearMap (red_S (g.1.2.toLinearMap z))) =
        ρ g.1.1 (f source) := hcover
    _ = ρ g.1.1 (f (red_S z)) := by
          rw [hsource]
    _ =
        ρ g.1.1
          (fixed_isotypic_tensor_evaluation_linearEquiv
            (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
            (f ⊗ₜ[k] red_S z)) := by
          rw [fixed_isotypic_tensor_evaluation_linearEquiv_tmul]

/-- Helper for Theorem 17-17.6-1: a lift of the literal quotient multiplicity module tensors
with the fixed constituent lift and descends to a lift of the original representation. -/
theorem descend_lift_of_fixed_constituent_literal_determinant_tensor
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hproj_surj :
      Function.Surjective
        (fixed_constituent_literal_determinant_cover_proj_hom
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)))
    (hNbarData :
      let G2 :=
        fixed_constituent_literal_determinant_cover_local
          (A := A) (G := G) (I := I) ρA_I
      let I2 :=
        fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
          (A := A) (G := G) (I := I) ρA_I
      let pi2 : G2 ⧸ I2 →* G ⧸ I :=
        fixed_constituent_literal_determinant_cover_proj_to_quotient
          (A := A) (G := G) (I := I) (ρA_I := ρA_I)
      let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
      Finite Nbar ∧ Nat.Coprime p (Nat.card Nbar)) :
    let G2 :=
      fixed_constituent_literal_determinant_cover_local
        (A := A) (G := G) (I := I) ρA_I
    let I2 :=
      fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
        (A := A) (G := G) (I := I) ρA_I
    let tau :=
      fixed_isotypic_literal_determinant_multiplicity_space_quotient_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift
    ∀ {P_tau : Type (max u v x)} (_ : AddCommGroup P_tau) (_ : Module A P_tau)
      (_ : Module.Free A P_tau) (_ : Module.Finite A P_tau)
      (ρA_tau : Representation A (G2 ⧸ I2) P_tau)
      (red_tau :
        P_tau →ₗ[A] fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar),
        IsResidueFieldLift tau ρA_tau red_tau →
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A G P)
            (red : P →ₗ[A] V),
              IsResidueFieldLift ρ ρA red := by
  dsimp at hNbarData ⊢
  intro P_tau hP_tau_add hP_tau_module hP_tau_free hP_tau_finite ρA_tau red_tau hLiftTau
  letI : AddCommGroup P_tau := hP_tau_add
  letI : Module A P_tau := hP_tau_module
  letI : Module.Free A P_tau := hP_tau_free
  letI : Module.Finite A P_tau := hP_tau_finite
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let I2 :=
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    fixed_constituent_literal_determinant_cover_proj_to_quotient
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
  let coverRep :=
    fixed_isotypic_literal_determinant_cover_representation
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  have hCoverLift :
      IsResidueFieldLift coverRep (ρA_tau.comp (QuotientGroup.mk' I2)) red_tau := by
    simpa [G2, I2, coverRep] using
      fixed_isotypic_literal_determinant_cover_lift_of_quotient_lift
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift ρA_tau red_tau hLiftTau
  have hCoverLift_apply :
      ∀ (g : G2) (y : P_tau),
        red_tau ((ρA_tau.comp (QuotientGroup.mk' I2)) g y) =
          coverRep g (red_tau y) := by
    intro g y
    exact
      isResidueFieldLift_apply
        (A := A) coverRep (ρA_tau.comp (QuotientGroup.mk' I2)) red_tau hCoverLift g y
  let ρA_S_cover : Representation A G2 P_S :=
    (fixed_constituent_transport_total_space_fiber_representation
      (A := A) (G := G) (I := I) ρA_I).comp (Subgroup.subtype G2)
  have hTensorPure_apply :
      ∀ (g : G2) (y : P_tau) (z : P_S),
        fixed_isotypic_tensor_evaluation_linearEquiv
            (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
            (red_tau ((ρA_tau.comp (QuotientGroup.mk' I2)) g y) ⊗ₜ[k]
              red_S (ρA_S_cover g z)) =
          ρ g.1.1
            (fixed_isotypic_tensor_evaluation_linearEquiv
              (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top
              (red_tau y ⊗ₜ[k] red_S z)) := by
    intro g y z
    rw [hCoverLift_apply g y]
    simpa [ρA_S_cover, fixed_constituent_transport_total_space_fiber_representation] using
      fixed_constituent_literal_determinant_cover_tensor_evaluation_apply_red_tmul
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift g (red_tau y) z
  let evalTensor :
      fixed_isotypic_multiplicity_space (I := I) (ρ := ρ) Sbar ⊗[k] Sbar.toSubmodule
        →ₗ[k] V :=
    (fixed_isotypic_tensor_evaluation_linearEquiv
      (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top).toLinearMap
  obtain ⟨redTensor, hredTensor_tmul⟩ :
      ∃ redTensor : P_tau ⊗[A] P_S →ₗ[A] V,
        ∀ (y : P_tau) (z : P_S),
          redTensor (y ⊗ₜ[A] z) =
            evalTensor (red_tau y ⊗ₜ[k] red_S z) :=
    exists_tensorProduct_reduction_of_residue_maps
      (A := A) evalTensor red_tau red_S
  let ρA_tensor : Representation A G2 (P_tau ⊗[A] P_S) :=
    Representation.tprod (ρA_tau.comp (QuotientGroup.mk' I2)) ρA_S_cover
  have hρA_tensor_tmul :
      ∀ (g : G2) (y : P_tau) (z : P_S),
        ρA_tensor g (y ⊗ₜ[A] z) =
          ((ρA_tau.comp (QuotientGroup.mk' I2)) g y) ⊗ₜ[A] ρA_S_cover g z := by
    intro g y z
    simp [ρA_tensor, Representation.tprod_apply]
  have hTensorReduction_tmul :
      ∀ (g : G2) (y : P_tau) (z : P_S),
        redTensor (ρA_tensor g (y ⊗ₜ[A] z)) =
          ρ g.1.1 (redTensor (y ⊗ₜ[A] z)) := by
    intro g y z
    rw [hρA_tensor_tmul]
    rw [hredTensor_tmul, hredTensor_tmul]
    exact hTensorPure_apply g y z
  have hTensorReduction_intertwines :
      ∀ (g : G2) (t : P_tau ⊗[A] P_S),
        redTensor (ρA_tensor g t) = ρ g.1.1 (redTensor t) := by
    intro g t
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp
    · intro y z
      exact hTensorReduction_tmul g y z
    · intro t₁ t₂ ht₁ ht₂
      simp [map_add, ht₁, ht₂]
  have hTensorBaseChange : IsBaseChange k redTensor := by
    exact
      tensorProduct_reduction_isBaseChange_of_residue_maps
        (fixed_isotypic_tensor_evaluation_linearEquiv
          (A := A) (p := p) hp I hIcop ρ Sbar hSbar_irred hSbar_top)
        red_tau red_S hLiftTau.1 hLiftSbar.1 redTensor hredTensor_tmul
  let pi : G2 →* G :=
    fixed_constituent_literal_determinant_cover_proj_hom
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  let rhoPull : Representation k G2 V := ρ.comp pi
  have hTensorIntertwining :
      ∀ (g : G2) (t : P_tau ⊗[A] P_S),
        redTensor (ρA_tensor g t) = rhoPull g (redTensor t) := by
    intro g t
    simpa [rhoPull, pi] using
      hTensorReduction_intertwines g t
  have hTensorLift :
      IsResidueFieldLift rhoPull ρA_tensor redTensor := by
    exact
      isResidueFieldLift_of_isBaseChange_apply
        rhoPull ρA_tensor redTensor hTensorBaseChange hTensorIntertwining
  let K : Subgroup G2 := pi.ker
  have hTensorKernelLift :
      IsResidueFieldLift
        (rhoPull.comp K.subtype)
        (ρA_tensor.comp K.subtype)
        redTensor :=
    Representation.isResidueFieldLift_comp hTensorLift K.subtype
  have hTensorKernelSourceTrivial :
      Representation.IsTrivial (rhoPull.comp K.subtype) := by
    refine Representation.IsTrivial.mk ?_
    intro z
    ext x
    have hz : pi z.1 = 1 := z.2
    change ρ (pi z.1) x = x
    rw [hz]
    simp
  have hTensorKernelSourceEq :
      rhoPull.comp K.subtype = Representation.trivial k K V := by
    ext z x
    have hz : pi z.1 = 1 := z.2
    change ρ (pi z.1) x = x
    rw [hz]
    simp
  have hTensorKernelLift_trivialSource :
      IsResidueFieldLift
        (Representation.trivial k K V)
        (ρA_tensor.comp K.subtype)
        redTensor := by
    rw [← hTensorKernelSourceEq]
    exact hTensorKernelLift
  let kernelEquiv : K ≃* Nbar := by
    simpa [G2, I2, pi2, Nbar, pi, K] using
      literal_determinant_cover_kernel_equiv_quotient_kernel
        (A := A) (G := G) (I := I) ρA_I
  have hKfinite : Finite K := by
    letI : Finite Nbar := hNbarData.1
    exact Finite.of_equiv Nbar kernelEquiv.symm.toEquiv
  have hKcop : Nat.Coprime p (Nat.card K) := by
    have hcard : Nat.card K = Nat.card Nbar := Nat.card_congr kernelEquiv.toEquiv
    rw [hcard]
    exact hNbarData.2
  letI : Finite K := hKfinite
  have hTensorKernelTrivial :
      Representation.IsTrivial (ρA_tensor.comp K.subtype) := by
    exact
      isTrivial_of_residueFieldLift_trivial_of_coprime_card_any
        (A := A) (p := p) hp hTensorKernelLift_trivialSource hKcop
  letI : Representation.IsTrivial (ρA_tensor.comp K.subtype) := hTensorKernelTrivial
  have hpi_surj : Function.Surjective pi := by
    simpa [pi] using hproj_surj
  let ρA : Representation A G (P_tau ⊗[A] P_S) :=
    (ρA_tensor.ofQuotient K).comp
      (QuotientGroup.quotientKerEquivOfSurjective pi hpi_surj).symm.toMonoidHom
  have hFinalLift : IsResidueFieldLift ρ ρA redTensor := by
    simpa [ρA, rhoPull] using
      isResidueFieldLift_descend_of_surjective
        (A := A) pi hpi_surj ρ ρA_tensor redTensor hTensorLift
  exact
    ⟨P_tau ⊗[A] P_S, inferInstance, inferInstance, inferInstance, inferInstance,
      ρA, redTensor, hFinalLift⟩

/-- Helper for Theorem 17-17.6-1: bounded determinant control packages the fixed constituent into
Serre's quotient central-extension data. -/
noncomputable def projective_extension_kernel_quotient_data_from_bounded_generator_containment
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S))
    (hcandidate_le :
      let C := fixed_constituent_determinant_subgroup (A := A) (G := G) (I := I) ρA_I
      let Qd : Subgroup kˣ := (powMonoidHom (Module.finrank A P_S) : kˣ →* kˣ).range
      let Dbar := (rootsOfUnity (Nat.lcm (Nat.card G) (Nat.card C)) k).map (QuotientGroup.mk' Qd)
      fixed_constituent_projective_extension_candidate_subgroup
          (p := p) (A := A) (G := G) (V := V)
          hp I hIcop ρ Sbar ρA_I red_S hLiftSbar hTransport hTransportLift ≤
        Dbar) :
    ConstituentProjectiveExtensionQuotientData
      (p := p) (A := A) (G := G) (V := V) I ρ Sbar P_S ρA_I red_S :=
  let G2 :=
    fixed_constituent_literal_determinant_cover_local
      (A := A) (G := G) (I := I) ρA_I
  let I2 :=
    fixed_constituent_literal_determinant_cover_hall_kernel_subgroup
      (A := A) (G := G) (I := I) ρA_I
  let pi2 : G2 ⧸ I2 →* G ⧸ I :=
    fixed_constituent_literal_determinant_cover_proj_to_quotient
      (A := A) (G := G) (I := I) (ρA_I := ρA_I)
  let Nbar : Subgroup (G2 ⧸ I2) := pi2.ker
  let hsection :=
    fixed_constituent_section_determinant_class_lands_in_determinant_subgroup_of_algClosed
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift
  let hdcop :=
    fixed_constituent_lift_finrank_coprime
      (A := A) (G := G) (I := I) hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  let hproj_surj :=
    fixed_constituent_literal_determinant_cover_proj_surjective_of_section_class_lands_in_determinant_subgroup
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred hdcop ρA_I red_S hLiftSbar hTransport
      hTransportLift hsection
  let hActualKernel :=
    literal_determinant_cover_kernel_finite_cyclic_coprime
      (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  let hKernel :=
    literal_determinant_cover_quotient_kernel_finite_cyclic_coprime
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
  { G2 := G2
    instGroupG2 := inferInstance
    instFiniteG2 :=
      fixed_constituent_literal_determinant_cover_finite_of_finite_kernel
        (A := A) (G := G) (I := I) ρA_I hActualKernel.1
    pi :=
      fixed_constituent_literal_determinant_cover_proj_hom
        (A := A) (G := G) (I := I) (ρA_I := ρA_I)
    I2 := I2
    instNormalI2 := inferInstance
    Nbar := Nbar
    instNormalNbar := MonoidHom.normal_ker pi2
    hNbar_central :=
      literal_determinant_cover_quotient_kernel_central
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar
    hNbar_cyclic := hKernel.2.1
    hNbar_coprime := hKernel.2.2
    tau :=
      fixed_isotypic_literal_determinant_multiplicity_space_quotient_representation
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift
    tau_irred :=
      fixed_isotypic_literal_determinant_multiplicity_space_quotient_irreducible
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift hproj_surj
    quotientEquiv :=
      fixed_constituent_literal_determinant_cover_kernel_quotient_equiv_of_proj_surjective
        (A := A) (G := G) (I := I) ρA_I hproj_surj
    descendLift :=
      descend_lift_of_fixed_constituent_literal_determinant_tensor
        (p := p) (A := A) (G := G) (V := V)
        hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport
        hTransportLift hproj_surj ⟨hKernel.1, hKernel.2.2⟩ }

/-- Helper for Theorem 17-17.6-1: construct the fixed-constituent projective-extension quotient
package from the chosen lift of the Hall-kernel constituent. -/
noncomputable def exists_constituent_projective_extension_quotient_data
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V)
    [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤)
    {P_S : Type (max u v x)} [AddCommGroup P_S] [Module A P_S]
    [Module.Free A P_S] [Module.Finite A P_S]
    (ρA_I : Representation A I P_S)
    (red_S : P_S →ₗ[A] Sbar.toSubmodule)
    (hLiftSbar : IsResidueFieldLift Sbar.toRepresentation ρA_I red_S)
    (hTransport :
      ∀ s : G,
        Nonempty
          (Sbar.toRepresentation.Equiv
            (transportedSubrepresentation ρ Sbar s).toRepresentation))
    (hTransportLift :
      ∀ s : G,
        IsResidueFieldLift
          (transportedSubrepresentation ρ Sbar s).toRepresentation
          ρA_I
          (((hTransport s).some.toLinearMap.restrictScalars A).comp red_S)) :
    ConstituentProjectiveExtensionQuotientData
      (p := p) (A := A) (G := G) (V := V) I ρ Sbar P_S ρA_I red_S :=
  projective_extension_kernel_quotient_data_from_bounded_generator_containment
    (p := p) (A := A) (G := G) (V := V)
    hp I hIcop ρ Sbar hSbar_irred hSbar_top ρA_I red_S hLiftSbar hTransport hTransportLift
    (candidate_subgroup_le_rootsOfUnity_lcm_image
      (p := p) (A := A) (G := G) (V := V)
      hp I hIcop ρ Sbar hSbar_irred ρA_I red_S hLiftSbar hTransport hTransportLift)

end

end Representation
