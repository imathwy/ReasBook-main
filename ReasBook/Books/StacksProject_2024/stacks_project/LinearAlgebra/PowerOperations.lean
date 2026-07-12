import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorPower.Symmetric

open Module
open scoped TensorProduct

universe u u1 u2 u3

section

variable {R : Type u} [CommRing R]
variable {M₂ : Type u1} [AddCommGroup M₂] [Module R M₂]
variable {M₁ : Type u2} [AddCommGroup M₁] [Module R M₁]
variable {M : Type u3} [AddCommGroup M] [Module R M]

namespace SymmetricPower

/-- The finite index type `Fin n` lifted to the universe of the coefficient ring. This is the
canonical index used in the universe-polymorphic `n`th symmetric tensor power owners below. -/
abbrev UFin (n : ℕ) : Type u := ULift.{u} (Fin n)

private def cons (x : M₁) (m : UFin n → M₁) : UFin (n + 1) → M₁
  | ⟨i⟩ => Fin.cases x (fun j ↦ m ⟨j⟩) i

private lemma cons_update (x : M₁) (m : UFin n → M₁) (i : UFin n) (y : M₁) :
    cons x (Function.update m i y) = Function.update (cons x m) ⟨i.down.succ⟩ y := by
  classical
  ext j
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  cases j using Fin.cases with
  | zero => rfl
  | succ j =>
      simp [cons, Function.update]

private def succPerm (n : ℕ) (e : Equiv.Perm (UFin n)) : Equiv.Perm (UFin (n + 1)) where
  toFun
    | ⟨i⟩ => ⟨Fin.cases 0 (fun j ↦ (e ⟨j⟩).down.succ) i⟩
  invFun
    | ⟨i⟩ => ⟨Fin.cases 0 (fun j ↦ (e.symm ⟨j⟩).down.succ) i⟩
  left_inv i := by
    rcases i with ⟨i⟩
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
        ext
        have h : ((e.symm ⟨(e ⟨i⟩).down⟩).down : Fin n) = i :=
          congrArg ULift.down (e.left_inv ⟨i⟩)
        have hs : ((e.symm ⟨(e ⟨i⟩).down⟩).down.succ : Fin (n + 1)) = i.succ :=
          congrArg Fin.succ h
        exact congrArg Fin.val hs
  right_inv i := by
    rcases i with ⟨i⟩
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
        ext
        have h : ((e ⟨(e.symm ⟨i⟩).down⟩).down : Fin n) = i :=
          congrArg ULift.down (e.right_inv ⟨i⟩)
        have hs : ((e ⟨(e.symm ⟨i⟩).down⟩).down.succ : Fin (n + 1)) = i.succ :=
          congrArg Fin.succ h
        exact congrArg Fin.val hs

private lemma map_rel (n : ℕ) (g : M₁ →ₗ[R] M)
    {x y : ⨂[R] (_ : UFin n), M₁}
    (h : addConGen (Rel R (UFin n) M₁) x y) :
    addConGen (Rel R (UFin n) M)
      (PiTensorProduct.map (fun _ ↦ g) x)
      (PiTensorProduct.map (fun _ ↦ g) y) := by
  induction h with
  | of _ _ h =>
      cases h with
      | perm e f =>
          simpa [PiTensorProduct.map_tprod, Function.comp_def] using
            (AddConGen.Rel.of _ _ (Rel.perm e (g ∘ f)))
  | refl => exact AddCon.refl _ _
  | symm hxy ih => exact AddCon.symm _ ih
  | trans hxy hyz ihxy ihyz => exact AddCon.trans _ ihxy ihyz
  | add hxy hyz ihxy ihyz =>
      simpa [LinearMap.map_add] using AddCon.add _ ihxy ihyz

/-- The linear map between symmetric powers induced by a linear map of modules. -/
noncomputable def map (n : ℕ) (g : M₁ →ₗ[R] M) :
    Sym[R] (UFin n) M₁ →ₗ[R] Sym[R] (UFin n) M where
  __ :=
    AddCon.lift _
      (AddMonoidHom.comp (AddCon.mk' _) (PiTensorProduct.map (fun _ ↦ g)).toAddMonoidHom)
      (fun x y h ↦ Quotient.sound (map_rel n g h))
  map_smul' r q := by
    refine AddCon.induction_on q ?_
    intro x
    change ((addConGen (Rel R (UFin n) M₁)).lift
        ((addConGen (Rel R (UFin n) M)).mk'.comp (PiTensorProduct.map (fun _ ↦ g)).toAddMonoidHom)
        (fun a b h ↦ Quotient.sound (map_rel n g h)))
      ((SymmetricPower.smul' (UFin n) M₁ r) ((addConGen (Rel R (UFin n) M₁)).mk' x)) = _
    have hs₁ :
        SymmetricPower.smul' (UFin n) M₁ r ((addConGen (Rel R (UFin n) M₁)).mk' x) =
          ((addConGen (Rel R (UFin n) M₁)).mk' (r • x) : Sym[R] (UFin n) M₁) := rfl
    rw [hs₁, AddCon.lift_mk']
    change ((addConGen (Rel R (UFin n) M)).mk' (PiTensorProduct.map (fun _ ↦ g) (r • x)) :
        Sym[R] (UFin n) M) =
      SymmetricPower.smul' (UFin n) M r
        ((addConGen (Rel R (UFin n) M)).mk' (PiTensorProduct.map (fun _ ↦ g) x) :
          Sym[R] (UFin n) M)
    have hs₂ :
        SymmetricPower.smul' (UFin n) M r
            (((addConGen (Rel R (UFin n) M)).mk' (PiTensorProduct.map (fun _ ↦ g) x) :
              Sym[R] (UFin n) M)) =
          ((addConGen (Rel R (UFin n) M)).mk' (r • PiTensorProduct.map (fun _ ↦ g) x) :
            Sym[R] (UFin n) M) := rfl
    rw [hs₂]
    simp

@[simp] theorem map_mk (n : ℕ) (g : M₁ →ₗ[R] M) (x : ⨂[R] (_ : UFin n), M₁) :
    map n g (SymmetricPower.mk R (UFin n) M₁ x) =
      SymmetricPower.mk R (UFin n) M (PiTensorProduct.map (fun _ ↦ g) x) :=
  rfl

@[simp] theorem map_tprod (n : ℕ) (g : M₁ →ₗ[R] M) (m : UFin n → M₁) :
    map n g (SymmetricPower.tprod R m) = SymmetricPower.tprod R (g ∘ m) := by
  change map n g (SymmetricPower.mk R (UFin n) M₁ (PiTensorProduct.tprod R m)) =
    SymmetricPower.mk R (UFin n) M (PiTensorProduct.tprod R (g ∘ m))
  rw [map_mk, PiTensorProduct.map_tprod]
  rfl

@[simp] theorem map_id (n : ℕ) :
    map n (LinearMap.id : M₁ →ₗ[R] M₁) = LinearMap.id := by
  ext q
  refine AddCon.induction_on q ?_
  intro x
  change SymmetricPower.mk R (UFin n) M₁
      (PiTensorProduct.map (fun _ ↦ (LinearMap.id : M₁ →ₗ[R] M₁)) x) =
    SymmetricPower.mk R (UFin n) M₁ x
  simp

@[simp] theorem map_comp (n : ℕ) (f : M₁ →ₗ[R] M) (g : M →ₗ[R] M₂) :
    map n (g ∘ₗ f) = map n g ∘ₗ map n f := by
  ext q
  refine AddCon.induction_on q ?_
  intro x
  change SymmetricPower.mk R (UFin n) M₂ (PiTensorProduct.map (fun _ ↦ g ∘ₗ f) x) =
    SymmetricPower.mk R (UFin n) M₂
      (PiTensorProduct.map (fun _ ↦ g) (PiTensorProduct.map (fun _ ↦ f) x))
  simp [PiTensorProduct.map_comp]

private noncomputable def prependMultilinear (n : ℕ) (x : M₁) :
    MultilinearMap R (fun _ : UFin n ↦ M₁) (Sym[R] (UFin (n + 1)) M₁) :=
  MultilinearMap.mk'
    (fun m ↦ SymmetricPower.tprod R (cons x m))
    (fun m i y z ↦ by
      let F : MultilinearMap R (fun _ : UFin (n + 1) ↦ M₁) (Sym[R] (UFin (n + 1)) M₁) :=
        SymmetricPower.tprod R
      simpa [F, cons_update] using F.map_update_add (cons x m) ⟨i.down.succ⟩ y z)
    (fun m i c y ↦ by
      let F : MultilinearMap R (fun _ : UFin (n + 1) ↦ M₁) (Sym[R] (UFin (n + 1)) M₁) :=
        SymmetricPower.tprod R
      simpa [F, cons_update] using F.map_update_smul (cons x m) ⟨i.down.succ⟩ c y)

private noncomputable def prependTensorMap (n : ℕ) :
    M₁ →ₗ[R] (⨂[R] (_ : UFin n), M₁) →ₗ[R] Sym[R] (UFin (n + 1)) M₁ where
  toFun x :=
    PiTensorProduct.lift (prependMultilinear n x)
  map_add' x y := by
    ext m
    let F : MultilinearMap R (fun _ : UFin (n + 1) ↦ M₁) (Sym[R] (UFin (n + 1)) M₁) :=
      SymmetricPower.tprod R
    letI : DecidableEq (UFin (n + 1)) := Classical.decEq _
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, LinearMap.add_apply]
    change F (cons (x + y) m) = F (cons x m) + F (cons y m)
    have hxy :
        Function.update (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) (x + y) = cons (x + y) m := by
      ext j
      rcases j with ⟨j⟩
      cases j using Fin.cases <;> simp [cons, Function.update]
    have hx :
        Function.update (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) x = cons x m := by
      ext j
      rcases j with ⟨j⟩
      cases j using Fin.cases <;> simp [cons, Function.update]
    have hy :
        Function.update (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) y = cons y m := by
      ext j
      rcases j with ⟨j⟩
      cases j using Fin.cases <;> simp [cons, Function.update]
    simpa [hxy, hx, hy] using
      F.map_update_add (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) x y
  map_smul' r x := by
    ext m
    let F : MultilinearMap R (fun _ : UFin (n + 1) ↦ M₁) (Sym[R] (UFin (n + 1)) M₁) :=
      SymmetricPower.tprod R
    letI : DecidableEq (UFin (n + 1)) := Classical.decEq _
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, LinearMap.smul_apply]
    change F (cons (r • x) m) = r • F (cons x m)
    have hrx :
        Function.update (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) (r • x) = cons (r • x) m := by
      ext j
      rcases j with ⟨j⟩
      cases j using Fin.cases <;> simp [cons, Function.update]
    have hx :
        Function.update (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) x = cons x m := by
      ext j
      rcases j with ⟨j⟩
      cases j using Fin.cases <;> simp [cons, Function.update]
    simpa [hrx, hx] using
      F.map_update_smul (cons (0 : M₁) m) (⟨0⟩ : UFin (n + 1)) r x

private lemma prepend_eq (n : ℕ) (x : M₁)
    {y z : ⨂[R] (_ : UFin n), M₁}
    (h : addConGen (Rel R (UFin n) M₁) y z) :
    prependTensorMap n x y = prependTensorMap n x z := by
  induction h with
  | of _ _ h =>
      cases h with
      | perm e m =>
          have hcons :
              ((fun j : UFin (n + 1) ↦ cons x (fun i ↦ m (e i)) j) : UFin (n + 1) → M₁) =
                (fun j : UFin (n + 1) ↦ cons x m (succPerm n e j)) := by
            ext i
            rcases i with ⟨i⟩
            cases i using Fin.cases with
            | zero => rfl
            | succ i =>
                simp [cons, succPerm]
          have htprod :
              SymmetricPower.tprod R (cons x m ∘ succPerm n e) =
                SymmetricPower.tprod R (cons x m) :=
            SymmetricPower.tprod_equiv (succPerm n e) (cons x m)
          have hperm :
              SymmetricPower.tprod R (cons x (fun i ↦ m (e i))) =
                SymmetricPower.tprod R (cons x m ∘ succPerm n e) :=
            MultilinearMap.congr_arg (SymmetricPower.tprod R) hcons
          change PiTensorProduct.lift (prependMultilinear n x) (PiTensorProduct.tprod R m) =
            PiTensorProduct.lift (prependMultilinear n x) (PiTensorProduct.tprod R (fun i ↦ m (e i)))
          rw [PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
          exact htprod.symm.trans hperm.symm
  | refl => rfl
  | symm hyz ih => exact ih.symm
  | trans hxy hyz ihxy ihyz => exact ihxy.trans ihyz
  | add hxy hyz ihxy ihyz =>
      simpa [LinearMap.map_add] using congrArg₂ (· + ·) ihxy ihyz

private noncomputable def prependMap (n : ℕ) :
    M₁ →ₗ[R] Sym[R] (UFin n) M₁ →ₗ[R] Sym[R] (UFin (n + 1)) M₁ where
  toFun x :=
    { __ := AddCon.lift _ (prependTensorMap n x).toAddMonoidHom (fun _ _ h ↦ prepend_eq n x h)
      map_smul' r q := by
        refine AddCon.induction_on q ?_
        intro y
        change ((addConGen (Rel R (UFin n) M₁)).lift ((prependTensorMap n x).toAddMonoidHom)
            (fun a b h ↦ prepend_eq n x h))
          ((SymmetricPower.smul' (UFin n) M₁ r) ((addConGen (Rel R (UFin n) M₁)).mk' y)) = _
        rw [show
          SymmetricPower.smul' (UFin n) M₁ r ((addConGen (Rel R (UFin n) M₁)).mk' y) =
            ((addConGen (Rel R (UFin n) M₁)).mk' (r • y) : Sym[R] (UFin n) M₁) by
            rfl]
        simp
    }
  map_add' x y := by
    ext q
    refine AddCon.induction_on q ?_
    intro z
    simpa [LinearMap.add_apply] using congrArg (fun f ↦ f z) ((prependTensorMap n).map_add x y)
  map_smul' r x := by
    ext q
    refine AddCon.induction_on q ?_
    intro y
    simpa [LinearMap.smul_apply] using
      congrArg (fun f ↦ f y) ((prependTensorMap n).map_smulₛₗ r x)

/-- The canonical comparison map `M₂ ⊗[R] Sym[R]^n M₁ → Sym[R]^(n + 1) M₁`
induced by a linear map `M₂ →ₗ[R] M₁`. -/
noncomputable def leftTensorMap (n : ℕ) (f : M₂ →ₗ[R] M₁) :
    M₂ ⊗[R] Sym[R] (UFin n) M₁ →ₗ[R] Sym[R] (UFin (n + 1)) M₁ :=
  TensorProduct.lift (prependMap n ∘ₗ f)

@[simp] theorem leftTensorMap_tmul_tprod (n : ℕ) (f : M₂ →ₗ[R] M₁)
    (x : M₂) (m : UFin n → M₁) :
    leftTensorMap n f (x ⊗ₜ SymmetricPower.tprod R m) =
      SymmetricPower.tprod R (cons (f x) m) := by
  rw [leftTensorMap, TensorProduct.lift.tmul]
  change ((addConGen (Rel R (UFin n) M₁)).lift
      (prependTensorMap n (f x)).toAddMonoidHom
      (fun a b h ↦ prepend_eq n (f x) h))
    ((addConGen (Rel R (UFin n) M₁)).mk' (PiTensorProduct.tprod R m)) =
      SymmetricPower.tprod R (cons (f x) m)
  rw [AddCon.lift_mk']
  simp [prependTensorMap, prependMultilinear]

private def permSetoid (n : ℕ) (κ : Type*) : Setoid (UFin n → κ) where
  r a b := ∃ e : Equiv.Perm (UFin n), b = a ∘ e
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨Equiv.refl _, by ext i <;> rfl⟩
    · intro a b h
      rcases h with ⟨e, rfl⟩
      exact ⟨e.symm, by ext i <;> simp⟩
    · intro a b c hab hbc
      rcases hab with ⟨e, rfl⟩
      rcases hbc with ⟨e', rfl⟩
      exact ⟨e'.trans e, by ext i <;> rfl⟩

private abbrev OrbitIndex (n : ℕ) (κ : Type*) :=
  Quotient (permSetoid n κ)

private def permTupleEquiv (n : ℕ) {κ : Type*} (e : Equiv.Perm (UFin n)) :
    (UFin n → κ) ≃ (UFin n → κ) where
  toFun m := m ∘ e
  invFun m := m ∘ e.symm
  left_inv m := by
    ext i
    simp
  right_inv m := by
    ext i
    simp

private noncomputable def orbitBasisVec {κ : Type*} (n : ℕ) (b : Basis κ R M₁) :
    OrbitIndex n κ → Sym[R] (UFin n) M₁ :=
  Quotient.lift
    (fun m ↦ SymmetricPower.tprod R (fun i ↦ b (m i)))
    (by
      intro a b h
      rcases h with ⟨e, rfl⟩
      simpa [Function.comp_def] using
        (SymmetricPower.tprod_equiv (R := R) e (fun i ↦ b (a i))).symm)

private noncomputable def orbitReprTensor {κ : Type*} (n : ℕ) (b : Basis κ R M₁) :
    (⨂[R] (_ : UFin n), M₁) →ₗ[R] OrbitIndex n κ →₀ R :=
  (Finsupp.lmapDomain R R (Quotient.mk (permSetoid n κ))).comp
    (Basis.piTensorProduct (fun _ : UFin n ↦ b)).repr.toLinearMap

private theorem piTensorProduct_repr_tprod_perm {κ : Type*} (n : ℕ) (b : Basis κ R M₁)
    (e : Equiv.Perm (UFin n)) (f : UFin n → M₁) :
    (Basis.piTensorProduct (fun _ : UFin n ↦ b)).repr
        (PiTensorProduct.tprod R (fun i ↦ f (e i))) =
      Finsupp.mapDomain (permTupleEquiv n e)
        ((Basis.piTensorProduct (fun _ : UFin n ↦ b)).repr (PiTensorProduct.tprod R f)) := by
  ext m
  rw [Finsupp.mapDomain_equiv_apply]
  simp only [Basis.piTensorProduct_repr_tprod_apply]
  apply Fintype.prod_equiv e
  intro i
  simp [permTupleEquiv]

private theorem orbitReprTensor_rel {κ : Type*} (n : ℕ) (b : Basis κ R M₁)
    (e : Equiv.Perm (UFin n)) (f : UFin n → M₁) :
    orbitReprTensor n b (PiTensorProduct.tprod R f) =
      orbitReprTensor n b (PiTensorProduct.tprod R (fun i ↦ f (e i))) := by
  let q : (UFin n → κ) → OrbitIndex n κ := Quotient.mk (permSetoid n κ)
  simp only [orbitReprTensor, LinearMap.comp_apply, Finsupp.lmapDomain_apply]
  have hrepr :=
    congrArg (Finsupp.mapDomain q) (piTensorProduct_repr_tprod_perm n b e f)
  have hq :
      Finsupp.mapDomain q
          (Finsupp.mapDomain (permTupleEquiv n e)
            ((Basis.piTensorProduct (fun _ : UFin n ↦ b)).repr (PiTensorProduct.tprod R f))) =
        Finsupp.mapDomain q
          ((Basis.piTensorProduct (fun _ : UFin n ↦ b)).repr (PiTensorProduct.tprod R f)) := by
    rw [← Finsupp.mapDomain_comp]
    apply Finsupp.mapDomain_congr
    intro m hm
    exact Quot.sound ⟨e.symm, by
      ext i
      simp [permTupleEquiv]
    ⟩
  exact hq.symm.trans hrepr.symm

private noncomputable def orbitRepr {κ : Type*} (n : ℕ) (b : Basis κ R M₁) :
    Sym[R] (UFin n) M₁ →ₗ[R] OrbitIndex n κ →₀ R where
  __ :=
    AddCon.lift _
      (orbitReprTensor n b).toAddMonoidHom
      (by
        intro x y h
        induction h with
        | of _ _ h =>
            cases h with
            | perm e f =>
                simpa using orbitReprTensor_rel n b e f
        | refl => rfl
        | symm hxy ih => exact ih.symm
        | trans hxy hyz ihxy ihyz => exact ihxy.trans ihyz
        | add hxy hyz ihxy ihyz =>
            simpa [LinearMap.map_add] using congrArg₂ (· + ·) ihxy ihyz)
  map_smul' r q := by
    refine AddCon.induction_on q ?_
    intro x
    change Finsupp.mapDomain (Quotient.mk (permSetoid n κ))
        ((Basis.piTensorProduct (fun _ : UFin n ↦ b)).repr (r • x)) =
      r • Finsupp.mapDomain (Quotient.mk (permSetoid n κ))
        ((Basis.piTensorProduct (fun _ : UFin n ↦ b)).repr x)
    simpa using Finsupp.mapDomain_smul (f := Quotient.mk (permSetoid n κ)) r
      ((Basis.piTensorProduct (fun _ : UFin n ↦ b)).repr x)

@[simp] private theorem orbitRepr_tprod {κ : Type*} (n : ℕ) (b : Basis κ R M₁)
    (f : UFin n → M₁) :
    orbitRepr n b (SymmetricPower.tprod R f) =
      orbitReprTensor n b (PiTensorProduct.tprod R f) := by
  rfl

@[simp] private theorem orbitReprTensor_tprod_basis {κ : Type*} (n : ℕ) (b : Basis κ R M₁)
    (m : UFin n → κ) :
    orbitReprTensor n b (PiTensorProduct.tprod R (fun i ↦ b (m i))) =
      Finsupp.single (Quotient.mk (permSetoid n κ) m) 1 := by
  have hrepr :
      (Basis.piTensorProduct (fun _ : UFin n ↦ b)).repr
          (PiTensorProduct.tprod R (fun i ↦ b (m i))) =
        Finsupp.single m 1 := by
    simpa using
      (Basis.repr_self (Basis.piTensorProduct (fun _ : UFin n ↦ b)) m)
  simpa [orbitReprTensor, hrepr]

private noncomputable def orbitTotal {κ : Type*} (n : ℕ) (b : Basis κ R M₁) :
    (OrbitIndex n κ →₀ R) →ₗ[R] Sym[R] (UFin n) M₁ :=
  Finsupp.linearCombination R (orbitBasisVec n b)

@[simp] private theorem orbitRepr_orbitBasisVec {κ : Type*} (n : ℕ) (b : Basis κ R M₁)
    (q : OrbitIndex n κ) :
    orbitRepr n b (orbitBasisVec n b q) = Finsupp.single q 1 := by
  refine Quotient.inductionOn q ?_
  intro m
  simp [orbitBasisVec, orbitReprTensor_tprod_basis]

private noncomputable def orbitLinearEquiv {κ : Type*} (n : ℕ) (b : Basis κ R M₁) :
    Sym[R] (UFin n) M₁ ≃ₗ[R] OrbitIndex n κ →₀ R :=
  LinearEquiv.ofLinear
    (orbitRepr n b)
    (orbitTotal n b)
    (by
      apply LinearMap.ext
      intro l
      ext q
      induction l using Finsupp.induction_linear with
      | zero =>
          simp [orbitTotal]
      | add l₁ l₂ ih₁ ih₂ =>
          simpa [orbitTotal, LinearMap.comp_apply] using congrArg₂ (· + ·) ih₁ ih₂
      | single q' a =>
          simp [orbitTotal, orbitRepr_orbitBasisVec])
    (by
      let B : Basis (UFin n → κ) R (⨂[R] (_ : UFin n), M₁) :=
        Basis.piTensorProduct (fun _ : UFin n ↦ b)
      have hTensor :
          ((orbitTotal n b).comp (orbitRepr n b)).comp (SymmetricPower.mk R (UFin n) M₁) =
            SymmetricPower.mk R (UFin n) M₁ := by
        apply B.ext
        intro m
        rw [Basis.piTensorProduct_apply]
        change orbitTotal n b (orbitRepr n b (SymmetricPower.tprod R (fun i ↦ b (m i)))) =
          SymmetricPower.tprod R (fun i ↦ b (m i))
        rw [orbitRepr_tprod, orbitReprTensor_tprod_basis]
        simp [orbitTotal, orbitBasisVec]
      ext z
      obtain ⟨x, rfl⟩ := AddCon.mk'_surjective z
      simpa [LinearMap.comp_apply] using DFunLike.congr_fun hTensor x
    )

/-- If `M` is a free `R`-module, then so is its `n`th symmetric power. -/
theorem instFree [Module.Free R M₁] (n : ℕ) :
    Module.Free R (Sym[R] (UFin n) M₁) := by
  classical
  let b := Module.Free.chooseBasis R M₁
  exact Module.Free.of_equiv (orbitLinearEquiv n b).symm

end SymmetricPower

attribute [instance] SymmetricPower.instFree

namespace exteriorPower

/-- The canonical comparison map `M₂ ⊗[R] ⋀[R]^n M₁ → ⋀[R]^(n + 1) M₁`
induced by a linear map `M₂ →ₗ[R] M₁`. -/
noncomputable def leftTensorMap (n : ℕ) (f : M₂ →ₗ[R] M₁) :
    M₂ ⊗[R] ⋀[R]^n M₁ →ₗ[R] ⋀[R]^(n + 1) M₁ :=
  TensorProduct.lift {
    toFun := fun x ↦
      alternatingMapLinearEquiv ((ιMulti R (n + 1)).curryLeft (f x))
    map_add' x y := by
      ext m
      simp
    map_smul' r x := by
      ext m
      simp
  }

@[simp] theorem leftTensorMap_tmul_ιMulti (n : ℕ) (f : M₂ →ₗ[R] M₁)
    (x : M₂) (m : Fin n → M₁) :
    leftTensorMap n f (x ⊗ₜ exteriorPower.ιMulti R n m) =
      exteriorPower.ιMulti R (n + 1) (Fin.cons (f x) m) := by
  simpa [Matrix.vecCons] using
    (show leftTensorMap n f (x ⊗ₜ exteriorPower.ιMulti R n m) =
      exteriorPower.ιMulti R (n + 1) (Matrix.vecCons (f x) m) by
        rw [leftTensorMap, TensorProduct.lift.tmul]
        simp)

end exteriorPower

end
