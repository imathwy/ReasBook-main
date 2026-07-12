import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.GaloisDescentSummit
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.TwistIso
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.CoefficientTwistL
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.CyclicStraightening
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.Modular.SeparableSemisimple

/-!
# The characteristic-`p` modular Galois-descent capstone (assembly)

This module closes the characteristic-`p` modular Galois descent of Remark 14-14.5-1.  Given a
simple `k̄[G]`-module `T` over a **finite** field `k` whose modular Brauer character is
`Gal(k̄/k)`-invariant (and whose lift is Galois-equivariant on the prime-to-`p` roots), `T` is
the scalar extension of a simple `k[G]`-module `S`.

The proof integrates all of the sibling bricks:

* **G2** (`DefinedOverSubfield`) — define `T` over a finite Galois intermediate field `L/k`;
* **B** (`GaloisDescentSummit`) — absolute simplicity `End_{L[G]}(T_L) = L`;
* **G1** (`TwistIso`) + **C2** (`CoefficientTwistL`) + **C3** (`GaloisDescentSummit`) — the twist
  isomorphism `Tˢ ≅ T` descends to `LTwist φ T_L ≅ T_L` over `L`;
* **D** (`CyclicStraightening`) — straighten the φ-semilinear generator into a genuine
  `Gal(L/k)`-semilinear action;
* **G-core / wrapper** (`SemilinearGalois{Descent,Representation}`) — additive Speiser descent of
  that action, recovering the `k[G]`-model `S`.
-/

noncomputable section

universe u

open scoped TensorProduct Representation MonoidAlgebra
open CategoryTheory

namespace Representation

/-- Reconstruction isomorphism `τ ≅ FDRep.of τ.ρ` (a local copy of the standard bridge). -/
private def fdRepIsoOfRhoEndgame {K : Type u} [Field K] {G : Type u} [Group G] [Finite G]
    (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun _ => by ext x; rfl

variable {k : Type u} [Field k]
variable {p : ℕ} [hp : Fact p.Prime] [hk : CharP k p]
variable {G : Type u} [Group G] [Finite G]

local notation3 "k̄" => AlgebraicClosure k

/-! ### Two power lemmas for a semilinear additive automorphism -/

/-- The `j`-th power of a `φ`-semilinear additive automorphism is `φ^j`-semilinear. -/
private theorem addEquiv_pow_smul {L : Type u} [Field L] [Algebra k L]
    {M : Type u} [AddCommGroup M] [Module L M]
    (φ : L ≃ₐ[k] L) (f : M ≃+ M) (hsl : ∀ (c : L) (v : M), f (c • v) = φ c • f v) :
    ∀ (j : ℕ) (c : L) (v : M), (f ^ j) (c • v) = (φ ^ j) c • (f ^ j) v := by
  intro j
  induction j with
  | zero => intro c v; simp
  | succ j ih =>
      intro c v
      have hfs : ∀ x : M, (f ^ (j + 1)) x = f ((f ^ j) x) := fun x => by
        rw [pow_succ', AddAut.mul_apply]
      rw [hfs, ih c v, hsl, hfs]
      congr 1
      rw [pow_succ', AlgEquiv.mul_apply]

omit [Group G] [Finite G] in
/-- The powers of a `G`-equivariant additive automorphism are `G`-equivariant. -/
private theorem addEquiv_pow_comm {M : Type u} [AddCommGroup M]
    (act : G → M → M) (f : M ≃+ M) (hfG : ∀ (g : G) (v : M), f (act g v) = act g (f v)) :
    ∀ (j : ℕ) (g : G) (v : M), (f ^ j) (act g v) = act g ((f ^ j) v) := by
  intro j
  induction j with
  | zero => intro g v; simp
  | succ j ih =>
      intro g v
      have hfs : ∀ x : M, (f ^ (j + 1)) x = f ((f ^ j) x) := fun x => by
        rw [pow_succ', AddAut.mul_apply]
      rw [hfs, ih g v, hfG, hfs]

/-! ### The descent over a finite Galois intermediate field -/

/-- **The descent over a finite Galois extension `L/k` of a finite field.**  This is the body of the
capstone, stated over an abstract finite Galois `L/k` inside `k̄` (so the giant `adjoin` term never
enters instance synthesis). -/
private theorem descend_over_finiteGalois
    [Finite k]
    {L : Type u} [Field L] [Finite L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    [Algebra L k̄] [IsScalarTower k L k̄]
    (lift : PrimeToPRoot p k̄ →* k̄ˣ) (hlift : Function.Injective lift)
    (T : FDRep k̄ G) [Simple T]
    (hcompat : ∀ τ : k̄ ≃ₐ[k] k̄, PrimeToPRoot.toFieldLift lift ∘ twistPrimeToPRoot τ
        = fun x => (τ : k̄ →+* k̄) (PrimeToPRoot.toFieldLift lift x))
    (hInv : ∀ τ : k̄ ≃ₐ[k] k̄,
        FDRep.modularCharacterOnPRegularConjClass (p := p) T
            (fun x => (τ : k̄ →+* k̄) (PrimeToPRoot.toFieldLift lift x))
          = FDRep.modularCharacterOnPRegularConjClass (p := p) T (PrimeToPRoot.toFieldLift lift))
    (T_L : FDRep L G) (e0 : T ≅ FDRep.scalarExtension (k := k̄) T_L) :
    ∃ (S : FDRep k G), Simple S ∧ Nonempty (T ≅ FDRep.scalarExtension S) := by
  classical
  -- restrict scalars on the underlying space of `T_L`
  letI : Module k T_L.V := Module.compHom T_L.V (algebraMap k L)
  haveI : IsScalarTower k L T_L.V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : FiniteDimensional k T_L.V := Module.Finite.trans L T_L.V
  -- Step 2: simplicities and absolute simplicity
  haveI : Simple (FDRep.scalarExtension (k := k̄) T_L) := Simple.of_iso e0.symm
  haveI hsimpTL : Simple T_L := simple_of_scalarExtension_simple (k := k) T_L
  have hdim1 : Module.finrank L (Representation.IntertwiningMap T_L.ρ T_L.ρ) = 1 :=
    finrank_intertwiningMap_eq_one_of_scalarExtension_simple T_L T e0
  -- nontriviality of the carrier
  haveI hntV : Nontrivial T_L.V := by
    rcases subsingleton_or_nontrivial T_L.V with hsub | hnt
    · exfalso
      haveI := hsub
      haveI : Subsingleton (Representation.IntertwiningMap T_L.ρ T_L.ρ) :=
        ⟨fun a b => DFunLike.ext _ _ fun x => Subsingleton.elim _ _⟩
      rw [Module.finrank_zero_of_subsingleton] at hdim1
      exact absurd hdim1 (by norm_num)
    · exact hnt
  -- Step 3: the cyclic generator and a lift to `Gal(k̄/k)`
  haveI : Normal k L := inferInstance
  obtain ⟨φ, hφ⟩ := IsCyclic.exists_generator (α := L ≃ₐ[k] L)
  obtain ⟨τ, hτ⟩ :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := L) (E := k̄) φ
  haveI : Fintype (L ≃ₐ[k] L) := Fintype.ofFinite _
  have horder : orderOf φ = Module.finrank k L :=
    (orderOf_eq_card_of_forall_mem_zpowers hφ).trans (IsGalois.card_aut_eq_finrank k L)
  have hφn : φ ^ (Module.finrank k L) = 1 := by rw [← horder]; exact pow_orderOf_eq_one φ
  -- the σ-twist isomorphism `Twist τ (scalarExtension T_L) ≅ scalarExtension T_L`
  have hInvSE : ∀ ρ : k̄ ≃ₐ[k] k̄,
      FDRep.modularCharacterOnPRegularConjClass (p := p) (FDRep.scalarExtension (k := k̄) T_L)
          (fun x => (ρ : k̄ →+* k̄) (PrimeToPRoot.toFieldLift lift x))
        = FDRep.modularCharacterOnPRegularConjClass (p := p) (FDRep.scalarExtension (k := k̄) T_L)
            (PrimeToPRoot.toFieldLift lift) := by
    intro ρ
    have h1 := modularCharacterOnPRegularConjClass_eq_of_nonempty_iso (p := p) (k := k)
      (fun x => (ρ : k̄ →+* k̄) (PrimeToPRoot.toFieldLift lift x))
      (F := T) (F' := FDRep.scalarExtension (k := k̄) T_L) ⟨e0⟩
    have h2 := modularCharacterOnPRegularConjClass_eq_of_nonempty_iso (p := p) (k := k)
      (PrimeToPRoot.toFieldLift lift)
      (F := T) (F' := FDRep.scalarExtension (k := k̄) T_L) ⟨e0⟩
    rw [← h1, ← h2]; exact hInv ρ
  obtain ⟨i2⟩ := exists_twist_iso_of_modularCharacter_galoisInvariant (σ := τ)
    (T := FDRep.scalarExtension (k := k̄) T_L) lift hlift (hcompat τ) (hInvSE τ)
  have i1 := scalarExtension_LTwist_iso (σ := φ) (τ := τ) T_L hτ
  -- descend the `k̄`-isomorphism to `L`
  haveI : Simple (FDRep.scalarExtension (k := k̄) (LTwist φ T_L)) := Simple.of_iso (i1 ≪≫ i2)
  haveI : Simple (LTwist φ T_L) := simple_of_scalarExtension_simple (k := k) (LTwist φ T_L)
  obtain ⟨eφ⟩ := iso_of_scalarExtension_iso (LTwist φ T_L) T_L (i1 ≪≫ i2)
  -- Step 4: extract the φ-semilinear generator `f`
  let eφRep : Representation.Equiv (LTwist φ T_L).ρ T_L.ρ :=
    Representation.equivOfIso ((forget₂ (FDRep L G) (Rep L G)).mapIso eφ)
  let fLE : LTwistSpace φ T_L ≃ₗ[L] T_L.V := eφRep.toLinearEquiv
  have hfLE : ∀ (g : G) (x : LTwistSpace φ T_L),
      fLE ((LTwist φ T_L).ρ g x) = T_L.ρ g (fLE x) := by
    intro g x
    simpa [fLE] using LinearMap.congr_fun (eφRep.isIntertwining' g) x
  let f : T_L.V ≃+ T_L.V :=
    (LTwistSpace.LofBaseₛₗ (σ := φ) (W := T_L)).toAddEquiv.trans fLE.toAddEquiv
  have hf_apply : ∀ v : T_L.V, f v = fLE (LTwistSpace.LofBaseₛₗ (σ := φ) v) := fun _ => rfl
  have hsl : ∀ (c : L) (v : T_L.V), f (c • v) = φ c • f v := by
    intro c v
    have h1 : LTwistSpace.LofBaseₛₗ (σ := φ) (c • v)
        = φ c • LTwistSpace.LofBaseₛₗ (σ := φ) v := by rw [map_smulₛₗ]; rfl
    rw [hf_apply, hf_apply, h1, _root_.map_smul]
  have hfG : ∀ (g : G) (v : T_L.V), f (T_L.ρ g v) = T_L.ρ g (f v) := by
    intro g v
    have hclaim : LTwistSpace.LofBaseₛₗ (σ := φ) (T_L.ρ g v)
        = (LTwist φ T_L).ρ g (LTwistSpace.LofBaseₛₗ (σ := φ) v) := rfl
    rw [hf_apply, hf_apply, hclaim]
    exact hfLE g (LTwistSpace.LofBaseₛₗ (σ := φ) v)
  -- Step 5: `f ^ [L:k]` is a scalar lying in `k`
  let Fint : Representation.IntertwiningMap T_L.ρ T_L.ρ :=
    ({ toFun := fun v => (f ^ (Module.finrank k L)) v
       map_add' := fun x y => map_add (f ^ (Module.finrank k L)) x y
       map_smul' := fun c v => by
         simp only [RingHom.id_apply]
         rw [addEquiv_pow_smul φ f hsl (Module.finrank k L) c v, hφn, AlgEquiv.one_apply] } :
      T_L.V →ₗ[L] T_L.V).intertwiningMap_of_isIntertwiningMap T_L.ρ T_L.ρ
      (fun g v => addEquiv_pow_comm (fun g v => T_L.ρ g v) f hfG (Module.finrank k L) g v)
  have hFint : ∀ v, Fint v = (f ^ (Module.finrank k L)) v := fun _ => rfl
  have hone_ne : (1 : Representation.IntertwiningMap T_L.ρ T_L.ρ) ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : T_L.V)
    intro hcontra
    exact hw (by simpa [IntertwiningMap.coe_one] using DFunLike.congr_fun hcontra w)
  obtain ⟨lam_L, hlamL⟩ :=
    (finrank_eq_one_iff_of_nonzero' (1 : Representation.IntertwiningMap T_L.ρ T_L.ρ) hone_ne).mp
      hdim1 Fint
  have hpowL : ∀ v, (f ^ (Module.finrank k L)) v = lam_L • v := by
    intro v
    have h := DFunLike.congr_fun hlamL v
    simp only [IntertwiningMap.coe_smul, Pi.smul_apply, IntertwiningMap.coe_one, id_eq] at h
    rw [hFint] at h
    exact h.symm
  -- `lam_L` is fixed by `φ`, hence by the whole Galois group, hence lies in `k`
  have hfix : φ lam_L = lam_L := by
    obtain ⟨w, hw⟩ := exists_ne (0 : T_L.V)
    have hkey : lam_L • w = φ lam_L • w := by
      have hL : (f ^ (Module.finrank k L + 1)) (f.symm w) = lam_L • w := by
        rw [pow_succ, AddAut.mul_apply, f.apply_symm_apply, hpowL]
      have hR : (f ^ (Module.finrank k L + 1)) (f.symm w) = φ lam_L • w := by
        rw [pow_succ', AddAut.mul_apply, hpowL, hsl, f.apply_symm_apply]
      rw [← hL]; exact hR
    exact (smul_left_injective L hw hkey).symm
  have hpowfix : ∀ i : ℕ, (φ ^ i) lam_L = lam_L := by
    intro i
    induction i with
    | zero => simp
    | succ j ih => rw [pow_succ, AlgEquiv.mul_apply, hfix, ih]
  have hfixAll : ∀ σ : L ≃ₐ[k] L, σ lam_L = lam_L := by
    intro σ
    obtain ⟨i, hi⟩ : ∃ i : ℕ, φ ^ i = σ :=
      (Submonoid.mem_powers_iff σ φ).mp
        ((isOfFinOrder_of_finite φ).mem_powers_iff_mem_zpowers.mpr (hφ σ))
    rw [← hi]; exact hpowfix i
  obtain ⟨lam, hlam_eq⟩ : lam_L ∈ Set.range (algebraMap k L) :=
    (IsGalois.mem_range_algebraMap_iff_fixed lam_L).mpr hfixAll
  have hlamL_ne : lam_L ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : T_L.V)
    intro hzero
    have hfw : (f ^ (Module.finrank k L)) w = 0 := by rw [hpowL w, hzero, zero_smul]
    exact hw ((f ^ (Module.finrank k L)).injective
      (hfw.trans (map_zero (f ^ (Module.finrank k L))).symm))
  have hlam_ne : lam ≠ 0 := by
    intro h; exact hlamL_ne (by rw [← hlam_eq, h, map_zero])
  have hpow : ∀ v, (f ^ (Module.finrank k L)) v = algebraMap k L lam • v := by
    intro v; rw [hlam_eq]; exact hpowL v
  -- Step 6: straighten into a genuine semilinear Galois action
  obtain ⟨A, c, hAφ⟩ :=
    exists_semilinearGaloisAction_of_generator φ hφ f hsl lam hlam_ne hpow
  -- Step 7: `A` commutes with the `G`-action `T_L.ρ`
  have hcommφ : ∀ (g : G) (v : T_L.V), A.act φ (T_L.ρ g v) = T_L.ρ g (A.act φ v) := by
    intro g v
    simp only [hAφ]
    rw [hfG, _root_.map_smul]
  have hcommPow : ∀ (j : ℕ) (g : G) (v : T_L.V),
      A.act (φ ^ j) (T_L.ρ g v) = T_L.ρ g (A.act (φ ^ j) v) := by
    intro j
    induction j with
    | zero => intro g v; rw [pow_zero, A.act_one_apply, A.act_one_apply]
    | succ j ih =>
        intro g v
        rw [pow_succ, A.act_mul', A.act_mul', hcommφ, ih]
  have hcomm : ∀ (σ : L ≃ₐ[k] L) (g : G) (v : T_L.V),
      A.act σ (T_L.ρ g v) = T_L.ρ g (A.act σ v) := by
    intro σ g v
    obtain ⟨j, hj⟩ : ∃ j : ℕ, φ ^ j = σ :=
      (Submonoid.mem_powers_iff σ φ).mp
        ((isOfFinOrder_of_finite φ).mem_powers_iff_mem_zpowers.mpr (hφ σ))
    rw [← hj]; exact hcommPow j g v
  -- Step 8: descend to a `k`-representation `S` and recover `T_L` after scalar extension
  set S : FDRep k G := FDRep.of (A.descendedRep T_L.ρ hcomm) with hS
  let eSRep : Representation.Equiv
      (Representation.scalarExtension (k := L) (A.descendedRep T_L.ρ hcomm)) T_L.ρ :=
    Representation.Equiv.mk A.descentEquiv (by
      intro g
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      exact A.descentEquiv_baseChange_descendedRep T_L.ρ hcomm g x)
  have eS : FDRep.scalarExtension (k := L) S ≅ T_L :=
    eSRep.toFDRepIso.trans (fdRepIsoOfRhoEndgame T_L).symm
  -- Step 9: the scalar-extension tower recovers `T`
  let eCancelRep : Representation.Equiv
      (Representation.scalarExtension (k := k̄) (Representation.scalarExtension (k := L) S.ρ))
      (Representation.scalarExtension (k := k̄) S.ρ) :=
    Representation.Equiv.mk (TensorProduct.AlgebraTensorModule.cancelBaseChange k L k̄ k̄ S.V)
      (by intro g
          apply LinearMap.ext
          intro w
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
          exact cancelBaseChange_scalarExtension_equiv S.ρ g w)
  have e1 : FDRep.scalarExtension (k := k̄) (FDRep.scalarExtension (k := L) S)
      ≅ FDRep.scalarExtension (k := k̄) S := eCancelRep.toFDRepIso
  have e2 := scalarExtensionIsoOfIso (K := L) (K' := k̄) eS
  have eT : FDRep.scalarExtension (k := k̄) S ≅ T := e1.symm ≪≫ e2 ≪≫ e0.symm
  -- Step 10: `S` is simple
  haveI : Simple (FDRep.scalarExtension (k := k̄) S) := Simple.of_iso eT
  haveI : Simple S := simple_of_scalarExtension_simple (k := k) S
  exact ⟨S, this, ⟨eT.symm⟩⟩

variable [Finite k]

/-- **Characteristic-`p` modular Galois descent (capstone).**

A simple `k̄[G]`-module `T` over a finite field `k`, whose modular Brauer character is
`Gal(k̄/k)`-invariant (`hInv`) and whose lift is Galois-equivariant on the prime-to-`p` roots of
unity (`hcompat`), is the scalar extension of a simple `k[G]`-module `S`. -/
theorem descend_summit
    (lift : PrimeToPRoot p k̄ →* k̄ˣ) (hlift : Function.Injective lift)
    (T : FDRep k̄ G) [Simple T]
    (hcompat : ∀ τ : k̄ ≃ₐ[k] k̄, PrimeToPRoot.toFieldLift lift ∘ twistPrimeToPRoot τ
        = fun x => (τ : k̄ →+* k̄) (PrimeToPRoot.toFieldLift lift x))
    (hInv : ∀ τ : k̄ ≃ₐ[k] k̄,
        FDRep.modularCharacterOnPRegularConjClass (p := p) T
            (fun x => (τ : k̄ →+* k̄) (PrimeToPRoot.toFieldLift lift x))
          = FDRep.modularCharacterOnPRegularConjClass (p := p) T (PrimeToPRoot.toFieldLift lift)) :
    ∃ (S : FDRep k G), Simple S ∧ Nonempty (T ≅ FDRep.scalarExtension S) := by
  haveI : IsGalois k (AlgebraicClosure k) := inferInstance
  obtain ⟨L, T_L, ⟨e0⟩⟩ := exists_finiteGaloisIntermediateField_model (k := k) T
  haveI hT : IsScalarTower k (L.toIntermediateField : IntermediateField k k̄) k̄ :=
    IntermediateField.isScalarTower_mid' _
  haveI : IsScalarTower k (L : Type u) k̄ := hT
  haveI : Finite (L : Type u) := Module.finite_of_finite k
  exact descend_over_finiteGalois lift hlift T hcompat hInv T_L e0

/-- **k-valued ⟹ descends** (relocated from `GaloisDescent`, refined with the faithful `hcompat`
hypothesis that the lift is Galois-equivariant on prime-to-`p` roots — automatic for the canonical
inclusion lift).  The character argument (`k`-valued ⟹ Galois-invariant) is
`modularCharacter_galoisInvariant_of_kValued`; the module-level descent is `descend_summit`. -/
theorem descend_simple_of_modularCharacter_kValued [Finite k]
    (lift : PrimeToPRoot p (AlgebraicClosure k) →* (AlgebraicClosure k)ˣ)
    (hlift : Function.Injective lift)
    (T : FDRep (AlgebraicClosure k) G) [Simple T]
    (hcompat : ∀ τ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
        PrimeToPRoot.toFieldLift lift ∘ twistPrimeToPRoot τ
          = fun x => (τ : AlgebraicClosure k →+* AlgebraicClosure k)
            (PrimeToPRoot.toFieldLift lift x))
    (hT : ∀ c : PRegularConjClass G p,
        FDRep.modularCharacterOnPRegularConjClass (p := p) T
            (PrimeToPRoot.toFieldLift lift) c
          ∈ Set.range (algebraMap k (AlgebraicClosure k))) :
    ∃ (S : FDRep k G), Simple S ∧ Nonempty (T ≅ FDRep.scalarExtension S) :=
  descend_summit lift hlift T hcompat
    (fun σ => modularCharacter_galoisInvariant_of_kValued lift T hT σ)

/-- **Char-`p` modular Galois descent (headline export, relocated + `hcompat`-refined).** -/
theorem exists_simple_isScalarExtension_of_modularCharacter_kValued [Finite k]
    (lift : PrimeToPRoot p (AlgebraicClosure k) →* (AlgebraicClosure k)ˣ)
    (hlift : Function.Injective lift)
    (T : FDRep (AlgebraicClosure k) G) [Simple T]
    (hcompat : ∀ τ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
        PrimeToPRoot.toFieldLift lift ∘ twistPrimeToPRoot τ
          = fun x => (τ : AlgebraicClosure k →+* AlgebraicClosure k)
            (PrimeToPRoot.toFieldLift lift x))
    (hT : ∀ c : PRegularConjClass G p,
        FDRep.modularCharacterOnPRegularConjClass (p := p) T
            (PrimeToPRoot.toFieldLift lift) c
          ∈ Set.range (algebraMap k (AlgebraicClosure k))) :
    ∃ (S : FDRep k G), Simple S ∧ Nonempty (T ≅ FDRep.scalarExtension S) :=
  descend_simple_of_modularCharacter_kValued lift hlift T hcompat hT

end Representation
