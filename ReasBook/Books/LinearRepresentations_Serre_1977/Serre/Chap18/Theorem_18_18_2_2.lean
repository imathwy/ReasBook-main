import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_1_2.Index
import LinearRepresentations_Serre_1977.Serre.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Serre.Chap18.Theorem_18_18_2_1

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u v

namespace Representation

section PRegularConjClassFunctions

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {A : Type v} [CommRing A]
variable {G : Type u} [Group G] [Finite G]

section Multiplicative

-- Route correction: the descended owner `virtualModularCharacterOnPRegularConjClass` already lives
-- in `Theorem_18_18_2_1.RegularConjClassCore`, so this file only adds the multiplicative and
-- scalar-extension layer needed for Theorem `18-18.2-2`.

omit [Field k] [IsAlgClosed k] in
/-- Helper for Theorem 18-18.2-2: equal multisets give equal sums over their attached copies once
the summands are matched along the multiset equality. -/
private theorem attached_sum_eq_of_eq_local
    {B : Type*} [AddCommMonoid B]
    {m₁ m₂ : Multiset k} (hm : m₁ = m₂)
    (f₁ : {x // x ∈ m₁} → B) (f₂ : {x // x ∈ m₂} → B)
    (hfun : ∀ μ : {x // x ∈ m₁}, f₁ μ = f₂ ⟨μ.1, hm ▸ μ.2⟩) :
    (Multiset.map f₁ m₁.attach).sum = (Multiset.map f₂ m₂.attach).sum := by
  -- Transport the attached roots across `hm` and compare the resulting mapped multisets.
  subst hm
  refine congrArg Multiset.sum ?_
  apply Multiset.map_congr rfl
  intro μ _
  exact hfun μ

/-- Helper for Theorem 18-18.2-2: the descended Brauer character of the trivial representation is
the constant unit function on `PRegularConjClass G p`. -/
private theorem modularCharacterOnPRegularConjClass_one
    (lift : PrimeToPRoot p k →* A) :
    FDRep.modularCharacterOnPRegularConjClass
        (p := p) (G := G) (A := A) (FDRep.of (Representation.trivial k G k)) lift = 1 := by
  ext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simp [s]
  -- Evaluate the descended character on one regular representative.
  rw [← hs, FDRep.modularCharacterOnPRegularConjClass_ofSubtype]
  have hroots :
      (Representation.trivial k G k s).charpoly.roots =
        (Representation.trivial k G k (1 : G)).charpoly.roots := by
    simp [Representation.trivial]
  have hsame :
      φ[lift](Representation.trivial k G k) s =
        φ[lift](Representation.trivial k G k) ⟨(1 : G), isPRegular_one p⟩ := by
    -- The trivial representation has the same single eigenvalue on every group element.
    unfold Representation.modularCharacter
    exact attached_sum_eq_of_eq_local hroots _ _ (by
      intro μ
      exact congrArg lift (by ext; simp [Representation.trivial]))
  have hone :
      φ[lift](Representation.trivial k G k) ⟨(1 : G), isPRegular_one p⟩ = (1 : A) := by
    -- At the identity, Proposition `18-18.1-2 (1)` reduces the value to the one-dimensional rank.
    convert
      (modularCharacter_one_eq_finrank (p := p) (lift := lift)
        (ρ := Representation.trivial k G k)) using 1
    simp
  exact hsame.trans hone

/-- Helper for Theorem 18-18.2-2: the modular character is multiplicative on tensor products
without introducing a separate `[Fact p.Prime]` parameter, because the needed nonvanishing of
`orderOf s` in `k` follows from the field's ring characteristic dividing `p`. -/
private theorem modularCharacter_tensor_local
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (lift : PrimeToPRoot p k →* A) (ρ : Representation k G V) (σ : Representation k G W)
    (s : { t : G // IsPRegular p t }) :
    φ[lift](Representation.tprod ρ σ) s =
      φ[lift](ρ) s *
        φ[lift](σ) s := by
  classical
  -- Finite groups only contain elements of finite order, so the order of `s` is nonzero.
  have hm : orderOf s.1 ≠ 0 := by
    exact orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite s.1)
  -- The characteristic of the field divides `p`, hence cannot divide the order of a `p`-regular
  -- element; therefore `orderOf s` stays nonzero after casting to `k`.
  have hmk : ((orderOf s.1 : ℕ) : k) ≠ 0 := by
    intro hzero
    have hdiv_order : ringChar k ∣ orderOf s.1 := ringChar.dvd hzero
    have hp_zero : ((p : ℕ) : k) = 0 := CharP.cast_eq_zero k p
    have hdiv_p : ringChar k ∣ p := ringChar.dvd hp_zero
    have hdiv_one : ringChar k ∣ 1 := by
      rw [← s.2.gcd_eq_one]
      exact Nat.dvd_gcd hdiv_p hdiv_order
    exact CharP.ringChar_ne_one (R := k) (Nat.dvd_one.mp hdiv_one)
  -- Extend the lift to all field elements by sending non-roots to zero.
  let fA : k → A := fun μ ↦
    if h : ∃ x : PrimeToPRoot p k, ((x : kˣ) : k) = μ then lift (Classical.choose h) else 0
  have hfA : ∀ x : PrimeToPRoot p k, lift x = fA ((x : kˣ) : k) := by
    intro x
    have hex : ∃ y : PrimeToPRoot p k, ((y : kˣ) : k) = ((x : kˣ) : k) := ⟨x, rfl⟩
    have hsel : fA ((x : kˣ) : k) = lift (Classical.choose hex) := dif_pos hex
    rw [hsel]
    congr 1
    apply Subtype.ext
    apply Units.ext
    exact (Classical.choose_spec hex).symm
  have hfA_mul : ∀ x y : PrimeToPRoot p k,
      fA (((x : kˣ) : k) * ((y : kˣ) : k)) = fA ((x : kˣ) : k) * fA ((y : kˣ) : k) := by
    intro x y
    have hxy : (((x * y : PrimeToPRoot p k) : kˣ) : k) = ((x : kˣ) : k) * ((y : kˣ) : k) := by
      push_cast
      rfl
    rw [← hxy, ← hfA (x * y), map_mul, hfA x, hfA y]
  -- Choose eigenbases for the two actions of the regular element `s`.
  have hu₁ : (ρ s.1) ^ orderOf s.1 = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hu₂ : (σ s.1) ^ orderOf s.1 = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨κ₁, _, b₁, d₁, hb₁⟩ := exists_eigenbasis_of_pow_eq_one (ρ s.1) hm hmk hu₁
  obtain ⟨κ₂, _, b₂, d₂, hb₂⟩ := exists_eigenbasis_of_pow_eq_one (σ s.1) hm hmk hu₂
  -- Tensoring eigenvectors multiplies their eigenvalues.
  have hbT : ∀ ij : κ₁ × κ₂,
      (Representation.tprod ρ σ) s.1 ((Module.Basis.tensorProduct b₁ b₂) ij) =
        (d₁ ij.1 * d₂ ij.2) • (Module.Basis.tensorProduct b₁ b₂) ij := by
    intro ij
    rw [Module.Basis.tensorProduct_apply']
    rw [Representation.tprod_apply]
    rw [TensorProduct.map_tmul]
    rw [hb₁ ij.1, hb₂ ij.2]
    rw [TensorProduct.smul_tmul_smul]
  -- Rewrite all three modular characters as sums over the characteristic roots.
  have h₁ := modularCharacter_eq_roots_sum (p := p) (k := k) (G := G)
    (lift := fun x : PrimeToPRoot p k ↦ lift x) (f := fA) hfA ρ s
  have h₂ := modularCharacter_eq_roots_sum (p := p) (k := k) (G := G)
    (lift := fun x : PrimeToPRoot p k ↦ lift x) (f := fA) hfA σ s
  have hT := modularCharacter_eq_roots_sum (p := p) (k := k) (G := G)
    (lift := fun x : PrimeToPRoot p k ↦ lift x) (f := fA) hfA
    (Representation.tprod ρ σ) s
  change modularCharacter (fun x : PrimeToPRoot p k ↦ lift x) (Representation.tprod ρ σ) s =
    modularCharacter (fun x : PrimeToPRoot p k ↦ lift x) ρ s *
      modularCharacter (fun x : PrimeToPRoot p k ↦ lift x) σ s
  rw [h₁, h₂, hT]
  -- Replace the root multisets by the eigenvalue multisets coming from the chosen bases.
  rw [charpoly_roots_of_eigenbasis (ρ s.1) b₁ d₁ hb₁]
  rw [charpoly_roots_of_eigenbasis (σ s.1) b₂ d₂ hb₂]
  rw [charpoly_roots_of_eigenbasis ((Representation.tprod ρ σ) s.1)
    (Module.Basis.tensorProduct b₁ b₂) (fun ij ↦ d₁ ij.1 * d₂ ij.2) hbT]
  -- Each eigenvalue is the field value of a prime-to-`p` root, so `fA` is multiplicative on
  -- the tensor-product eigenvalues.
  have hd₁ : ∀ i, ∃ x : PrimeToPRoot p k, ((x : kˣ) : k) = d₁ i := by
    intro i
    have hroot : d₁ i ∈ (ρ s.1).charpoly.roots := by
      rw [charpoly_roots_of_eigenbasis (ρ s.1) b₁ d₁ hb₁]
      exact Multiset.mem_map_of_mem d₁ (Finset.mem_univ i)
    exact ⟨charpolyRoot_primeToPRoot (p := p) (k := k) ρ s.2 hroot,
      charpolyRoot_primeToPRoot_coe (p := p) (k := k) ρ s.2 hroot⟩
  have hd₂ : ∀ j, ∃ y : PrimeToPRoot p k, ((y : kˣ) : k) = d₂ j := by
    intro j
    have hroot : d₂ j ∈ (σ s.1).charpoly.roots := by
      rw [charpoly_roots_of_eigenbasis (σ s.1) b₂ d₂ hb₂]
      exact Multiset.mem_map_of_mem d₂ (Finset.mem_univ j)
    exact ⟨charpolyRoot_primeToPRoot (p := p) (k := k) σ s.2 hroot,
      charpolyRoot_primeToPRoot_coe (p := p) (k := k) σ s.2 hroot⟩
  -- Expand both factors and identify the tensor-product summand termwise.
  have hsum₁ : (Finset.univ.val.map d₁).map fA = Finset.univ.val.map fun i ↦ fA (d₁ i) := by
    rw [Multiset.map_map]
    rfl
  have hsum₂ : (Finset.univ.val.map d₂).map fA = Finset.univ.val.map fun j ↦ fA (d₂ j) := by
    rw [Multiset.map_map]
    rfl
  have hsumT : (Finset.univ.val.map fun ij : κ₁ × κ₂ ↦ d₁ ij.1 * d₂ ij.2).map fA =
      Finset.univ.val.map fun ij : κ₁ × κ₂ ↦ fA (d₁ ij.1) * fA (d₂ ij.2) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl ?_
    intro ij _
    obtain ⟨x, hx⟩ := hd₁ ij.1
    obtain ⟨y, hy⟩ := hd₂ ij.2
    change fA (d₁ ij.1 * d₂ ij.2) = fA (d₁ ij.1) * fA (d₂ ij.2)
    rw [← hx, ← hy]
    exact hfA_mul x y
  rw [hsum₁, hsum₂, hsumT]
  -- The remaining equality is the usual factorization of a double sum.
  change (∑ ij : κ₁ × κ₂, fA (d₁ ij.1) * fA (d₂ ij.2)) =
    (∑ i : κ₁, fA (d₁ i)) * (∑ j : κ₂, fA (d₂ j))
  rw [Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  rfl

/-- Helper for Theorem 18-18.2-2: the descended Brauer character is multiplicative on tensor
products of honest finite-dimensional representations. -/
private theorem modularCharacterOnPRegularConjClass_tensor
    (lift : PrimeToPRoot p k →* A) (V W : FDRep k G) :
    FDRep.modularCharacterOnPRegularConjClass
        (p := p) (G := G) (A := A) (E := FDRep.of (Representation.tprod V.ρ W.ρ)) lift =
      FDRep.modularCharacterOnPRegularConjClass (p := p) (G := G) (A := A) V lift *
        FDRep.modularCharacterOnPRegularConjClass (p := p) (G := G) (A := A) W lift := by
  ext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simp [s]
  -- Evaluate both descended characters on the same regular representative.
  rw [← hs]
  simpa [FDRep.modularCharacterOnPRegularConjClass_ofSubtype] using
    modularCharacter_tensor_local (p := p) (k := k) (G := G) lift V.ρ W.ρ s

-- Proof sketch: evaluate the descended Brauer character of the tensor unit at a chosen regular
-- representative, then unfold the trivial representation there.
/-- On Serre's representation ring, the descended virtual modular character sends `1` to the
constant function `1`. -/
@[simp] theorem virtualModularCharacterOnPRegularConjClass_one
    (lift : PrimeToPRoot p k →* A) :
    virtualModularCharacterOnPRegularConjClass (p := p) lift (1 : R₀[k](G)) = 1 := by
  -- Rewrite the Grothendieck-unit class as the trivial representation and use the previous
  -- representative-level computation.
  change
    virtualModularCharacterOnPRegularConjClass (p := p) lift
        [FDRep.of (Representation.trivial k G k)]₀ = 1
  rw [virtualModularCharacterOnPRegularConjClass_class]
  exact modularCharacterOnPRegularConjClass_one (p := p) (k := k) (G := G) lift

-- Proof sketch: descend to generator classes in each variable, where multiplication is tensor
-- product and Proposition `18-18.1-2 (4)` gives the Brauer-character identity.
/-- On Serre's representation ring, the descended virtual modular character is multiplicative. -/
@[simp] theorem virtualModularCharacterOnPRegularConjClass_mul
    (lift : PrimeToPRoot p k →* A) (x y : R₀[k](G)) :
    virtualModularCharacterOnPRegularConjClass (p := p) lift (x * y) =
      virtualModularCharacterOnPRegularConjClass (p := p) lift x *
        virtualModularCharacterOnPRegularConjClass (p := p) lift y := by
  -- Descend multiplicativity from honest representation classes by the same additive induction
  -- that defines Serre's Grothendieck ring.
  refine QuotientAddGroup.induction_on x fun a ↦ ?_
  refine QuotientAddGroup.induction_on y fun b ↦ ?_
  refine
    FreeAbelianGroup.induction_on a
      (by simp)
      (fun V ↦ ?_)
      (fun a ha ↦ by
        simp [map_neg, ha])
      (fun a₁ a₂ ha₁ ha₂ ↦ by
        simp [map_add, ha₁, ha₂, add_mul])
  refine
    FreeAbelianGroup.induction_on b
      (by simp)
      (fun W ↦ by
        -- On generator classes, multiplication is tensor product and the Brauer character
        -- multiplies under tensor products.
        change
          virtualModularCharacterOnPRegularConjClass (p := p) lift ([V]₀ * [W]₀) =
            virtualModularCharacterOnPRegularConjClass (p := p) lift [V]₀ *
              virtualModularCharacterOnPRegularConjClass (p := p) lift [W]₀
        rw [finiteRepGrothendieckClass_mul,
          virtualModularCharacterOnPRegularConjClass_class,
          virtualModularCharacterOnPRegularConjClass_class,
          virtualModularCharacterOnPRegularConjClass_class]
        exact modularCharacterOnPRegularConjClass_tensor (p := p) (k := k) (G := G) lift V W)
      (fun b hb ↦ by
        simp [map_neg, hb])
      (fun b₁ b₂ hb₁ hb₂ ↦ by
        simp [map_add, hb₁, hb₂, mul_add])

end Multiplicative

end PRegularConjClassFunctions

section ScalarExtension

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Theorem 18-18.2-2: the unscaled descended Brauer-character map viewed as a
`ℤ`-linear map into the `K`-valued regular class functions. -/
private def virtualModularCharacterOnPRegularConjClassLinear
    (lift : PrimeToPRoot p k →* Kˣ) :
    R₀[k](G) →ₗ[ℤ] (PRegularConjClass G p → K) :=
  -- Package the descended additive owner through the standard additive-hom-to-`ℤ`-linear API.
  -- The `ℤ`-module structure on `R₀[k](G)` is the canonical one of its quotient `AddCommGroup`,
  -- which the representation-ring instance now reuses definitionally.
  (virtualModularCharacterOnPRegularConjClass
    (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift)).toIntLinearMap

omit [CharP k p] [Finite G] in
/-- Helper for Theorem 18-18.2-2: the canonical `ℤ`-linear packaging evaluates pointwise as the
original descended additive Brauer-character map. -/
@[simp] private theorem virtualModularCharacterOnPRegularConjClassLinear_apply_local
    (lift : PrimeToPRoot p k →* Kˣ) (x : R₀[k](G)) :
      virtualModularCharacterOnPRegularConjClassLinear
        (p := p) (k := k) (G := G) lift x =
      virtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift) x := by
  -- The chosen linear packaging keeps the same underlying function.
  rfl

/-- Helper for Theorem 18-18.2-2: the scalar-extension map at a fixed tensor coefficient. -/
private def scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent
    (lift : PrimeToPRoot p k →* Kˣ) (a : K) :
    R₀[k](G) →ₗ[ℤ] (PRegularConjClass G p → K) :=
  -- Fix the tensor coefficient first; the remaining map is just a scalar multiple of the
  -- underlying `ℤ`-linear Brauer-character owner.
  a •
    virtualModularCharacterOnPRegularConjClassLinear
      (p := p) (k := k) (G := G) lift

omit [CharP k p] [Finite G] in
/-- Helper for Theorem 18-18.2-2: the fixed-coefficient component evaluates to the corresponding
scalar multiple of the descended Brauer-character map. -/
@[simp] private theorem scalarExtensionComponent_apply_local
    (lift : PrimeToPRoot p k →* Kˣ) (a : K) (x : R₀[k](G)) :
    scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent
        (p := p) (k := k) (G := G) lift a x =
      a •
        virtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift) x := by
  -- The component map is defined by scalar-multiplying the unscaled descended owner.
  simp [scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent,
    virtualModularCharacterOnPRegularConjClassLinear_apply_local]

omit [CharP k p] [Finite G] in
/-- Helper for Theorem 18-18.2-2: the tensor coefficient variable is additive in the lifted
scalar-extension map. -/
private theorem scalarExtensionVirtualModularCharacterOnPRegularConjClassLift_map_add
    (lift : PrimeToPRoot p k →* Kˣ) (a b : K) :
    scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent
        (p := p) (k := k) (G := G) lift (a + b) =
      scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent
          (p := p) (k := k) (G := G) lift a +
        scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent
          (p := p) (k := k) (G := G) lift b := by
  -- This is just distributivity of scalar multiplication on the linear-map codomain.
  simp [scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent, add_smul]

omit [CharP k p] [Finite G] in
/-- Helper for Theorem 18-18.2-2: the tensor coefficient variable is `K`-linear in the lifted
scalar-extension map. -/
private theorem scalarExtensionVirtualModularCharacterOnPRegularConjClassLift_map_smul
    (lift : PrimeToPRoot p k →* Kˣ) (a b : K) :
    scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent
        (p := p) (k := k) (G := G) lift (a * b) =
      a •
        scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent
          (p := p) (k := k) (G := G) lift b := by
  -- The coefficient action on linear maps is the ambient `K`-module structure.
  simp [scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent, smul_smul]

-- source-facing: Serre's theorem identifies the scalar extension of `R₀[k](G)` with the full
-- function space on `PRegularConjClass G p`.
-- core/canonical: `virtualModularCharacter` from Remark `18-18.1-3`.
-- bridge/view: `virtualModularCharacterOnPRegularConjClass` descends that owner to regular
-- conjugacy classes, and `scalarExtensionVirtualModularCharacterOnPRegularConjClass` is its
-- canonical scalar extension to a `K`-linear map.
/-- Helper for Theorem 18-18.2-2: the universal-property linear map used to tensor-extend the
descended Brauer-character map. -/
private def scalarExtensionVirtualModularCharacterOnPRegularConjClassLift
    (lift : PrimeToPRoot p k →* Kˣ) :
    K →ₗ[K] R₀[k](G) →ₗ[ℤ] (PRegularConjClass G p → K) :=
  { toFun :=
      scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent
        (p := p) (k := k) (G := G) lift
    map_add' :=
      scalarExtensionVirtualModularCharacterOnPRegularConjClassLift_map_add
        (p := p) (k := k) (G := G) lift
    map_smul' :=
      scalarExtensionVirtualModularCharacterOnPRegularConjClassLift_map_smul
        (p := p) (k := k) (G := G) lift }

/-- Bridge/view: the canonical `K`-linear scalar extension of the virtual modular character map on
`PRegularConjClass G p`. -/
def scalarExtensionVirtualModularCharacterOnPRegularConjClass
    (lift : PrimeToPRoot p k →* Kˣ) :
    K ⊗[ℤ] R₀[k](G) →ₗ[K] (PRegularConjClass G p → K) :=
  -- Route correction: use the canonical base-change owner `liftBaseChange`, so pure tensors are
  -- controlled by the standard `*_tmul` theorem instead of a bespoke tensor recursion.
  (scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent
      (p := p) (k := k) (G := G) lift (1 : K)).liftBaseChange K

omit [CharP k p] [Finite G] in
@[simp] theorem scalarExtensionVirtualModularCharacterOnPRegularConjClass_tmul
    (lift : PrimeToPRoot p k →* Kˣ) (a : K) (x : R₀[k](G)) :
    scalarExtensionVirtualModularCharacterOnPRegularConjClass (p := p) (k := k) (G := G) lift
        (a ⊗ₜ[ℤ] x) =
      a •
        (virtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift)) x := by
  -- Unfold the scalar extension once and apply the standard pure-tensor formula for
  -- `LinearMap.liftBaseChange`.
  rw [scalarExtensionVirtualModularCharacterOnPRegularConjClass, LinearMap.liftBaseChange_tmul]
  -- The coefficient-`1` component is the original descended Brauer-character map.
  simp [scalarExtensionVirtualModularCharacterOnPRegularConjClassComponent,
    virtualModularCharacterOnPRegularConjClassLinear_apply_local]

/-- Helper for Theorem 18-18.2-2: the tensor-extended descended Brauer-character map preserves
multiplication on pure tensors. -/
private theorem scalarExtensionVirtualModularCharacterOnPRegularConjClass_preserves_tmul_mul
    (lift : PrimeToPRoot p k →* Kˣ) :
    ∀ (a₁ a₂ : K) (b₁ b₂ : R₀[k](G)),
      scalarExtensionVirtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (G := G) lift ((a₁ * a₂) ⊗ₜ[ℤ] (b₁ * b₂)) =
        scalarExtensionVirtualModularCharacterOnPRegularConjClass
            (p := p) (k := k) (G := G) lift (a₁ ⊗ₜ[ℤ] b₁) *
      scalarExtensionVirtualModularCharacterOnPRegularConjClass
            (p := p) (k := k) (G := G) lift (a₂ ⊗ₜ[ℤ] b₂) := by
  intro a₁ a₂ b₁ b₂
  -- Rewrite all three pure tensors by the scalar-extension formula.
  ext c
  rw [scalarExtensionVirtualModularCharacterOnPRegularConjClass_tmul,
    scalarExtensionVirtualModularCharacterOnPRegularConjClass_tmul,
    scalarExtensionVirtualModularCharacterOnPRegularConjClass_tmul]
  -- On each regular class, multiplicativity reduces to the ring-level Brauer-character identity.
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  have hmul :
      (virtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift))
          (b₁ * b₂) c =
        ((virtualModularCharacterOnPRegularConjClass
            (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift)) b₁ *
          (virtualModularCharacterOnPRegularConjClass
            (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift)) b₂) c := by
    simpa [PrimeToPRoot.toFieldLift] using
      congrFun
        (virtualModularCharacterOnPRegularConjClass_mul
          (p := p) (k := k) (A := K) (G := G) ((Units.coeHom K).comp lift) b₁ b₂)
        c
  rw [hmul, Pi.mul_apply]
  ring

/-- Helper for Theorem 18-18.2-2: the tensor-extended descended Brauer-character map preserves
the tensor-product unit. -/
private theorem scalarExtensionVirtualModularCharacterOnPRegularConjClass_preserves_tmul_one
    (lift : PrimeToPRoot p k →* Kˣ) :
    scalarExtensionVirtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (G := G) lift (((1 : K) ⊗ₜ[ℤ] (1 : R₀[k](G)))) = 1 := by
  -- Specialize the pure-tensor formula to the tensor unit, then use the unit computation on the
  -- underlying Grothendieck ring.
  rw [scalarExtensionVirtualModularCharacterOnPRegularConjClass_tmul]
  have hunit :=
    virtualModularCharacterOnPRegularConjClass_one
      (p := p) (k := k) (A := K) (G := G) ((Units.coeHom K).comp lift)
  simpa [PrimeToPRoot.toFieldLift] using hunit

/-- Core/canonical multiplicative refinement of Theorem `18-18.2-2`: the scalar-extension
Brauer-character map is a `K`-algebra homomorphism to the function ring on
`PRegularConjClass G p`. -/
def scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgHom
    (lift : PrimeToPRoot p k →* Kˣ) :
    K ⊗[ℤ] R₀[k](G) →ₐ[K] (PRegularConjClass G p → K) :=
  { toFun :=
      scalarExtensionVirtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (G := G) lift
    map_zero' := by
      simp [scalarExtensionVirtualModularCharacterOnPRegularConjClass]
    map_add' := by
      intro ξ η
      simp [scalarExtensionVirtualModularCharacterOnPRegularConjClass]
    map_one' := by
      -- The tensor-product unit is the pure tensor `1 ⊗ 1`, so the earlier pure-tensor unit
      -- computation closes the algebra-unit goal directly.
      change
        scalarExtensionVirtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (G := G) lift (((1 : K) ⊗ₜ[ℤ] (1 : R₀[k](G)))) = 1
      simpa using
        scalarExtensionVirtualModularCharacterOnPRegularConjClass_preserves_tmul_one
          (p := p) (k := k) (G := G) lift
    map_mul' := by
      intro ξ η
      -- Reduce both tensor inputs to pure tensors; multiplicativity was already proved on those.
      refine TensorProduct.induction_on ξ ?_ ?_ ?_
      · simp
      · intro a x
        refine TensorProduct.induction_on η ?_ ?_ ?_
        · simp [map_zero]
        · intro b y
          -- Normalize the tensor-product multiplication of pure tensors before invoking the
          -- already-proved pure-tensor multiplicativity lemma.
          have htmul_mul :
              (a ⊗ₜ[ℤ] x) * (b ⊗ₜ[ℤ] y) = ((a * b) : K) ⊗ₜ[ℤ] (x * y) := by
            simp
          rw [htmul_mul]
          exact
            scalarExtensionVirtualModularCharacterOnPRegularConjClass_preserves_tmul_mul
              (p := p) (k := k) (G := G) lift a b x y
        · intro η₁ η₂ hη₁ hη₂
          -- Distribute the pure tensor over the sum and use both inductive hypotheses.
          simp [mul_add, hη₁, hη₂]
      · intro ξ₁ ξ₂ hξ₁ hξ₂
        -- Distribute the sum over `η` and use both inductive hypotheses.
        simp [add_mul, hξ₁, hξ₂]
    commutes' := by
      intro a
      -- The scalar `a` acts on the tensor product by the pure tensor `a ⊗ 1`, and the target
      -- algebra map is the constant function with value `a`.
      ext c
      change
        scalarExtensionVirtualModularCharacterOnPRegularConjClass
            (p := p) (k := k) (G := G) lift (a ⊗ₜ[ℤ] (1 : R₀[k](G))) c =
          a
      rw [scalarExtensionVirtualModularCharacterOnPRegularConjClass_tmul]
      change
        a * (virtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift)
          (1 : R₀[k](G)) c) = a
      have hunit :=
        congrFun
          (virtualModularCharacterOnPRegularConjClass_one
            (p := p) (k := k) (A := K) (G := G) ((Units.coeHom K).comp lift))
          c
      have hunit' :
          virtualModularCharacterOnPRegularConjClass
              (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift lift)
              (1 : R₀[k](G)) c = 1 := by
        simpa [PrimeToPRoot.toFieldLift] using hunit
      simp [hunit'] }

section Equivalence

omit [IsAlgClosed k] [Finite G] in
/-- Helper for Theorem 18-18.2-2: choose one representative of each isomorphism class of simple
finite-dimensional `k[G]`-representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family_theorem18_2_2_local :
    ∃ (ι : Type (u + 1)) (E : ι → FDRep k G),
      PairwiseNonisomorphic E ∧ IsCompleteIrreducibleFamily E := by
  classical
  let SimpleRep : Type (u + 1) := { τ : FDRep k G // Simple τ }
  let r : Setoid SimpleRep :=
    { r := fun a b ↦ Nonempty (a.1 ≅ b.1)
      iseqv :=
        ⟨fun a ↦ ⟨Iso.refl _⟩,
          fun {a b} hab ↦ by
            rcases hab with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {a b c} hab hbc ↦ by
            rcases hab with ⟨eab⟩
            rcases hbc with ⟨ebc⟩
            exact ⟨eab.trans ebc⟩⟩ }
  let ι : Type (u + 1) := Quotient r
  let E : ι → FDRep k G := fun q ↦ (Quotient.out q).1
  have hE_pairwise : PairwiseNonisomorphic E := by
    -- Distinct quotient classes cannot admit an isomorphism.
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨e⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hE_complete : IsCompleteIrreducibleFamily E := by
    refine ⟨?_, ?_⟩
    · intro q
      exact (Quotient.out q).2
    · intro τ hτ
      let q : ι := ⟦⟨τ, hτ⟩⟧
      refine ⟨q, ?_⟩
      have hq : Nonempty (((Quotient.out q).1) ≅ τ) := by
        exact Quotient.exact (Quotient.out_eq q)
      rcases hq with ⟨e⟩
      exact ⟨e.symm⟩
  exact ⟨ι, E, hE_pairwise, hE_complete⟩

variable [Fact p.Prime]

/-- Helper for Theorem 18-18.2-2: on the simple-class basis attached to a complete irreducible
family, the scalar-extension map matches the Brauer-character basis term by term. -/
private theorem scalarExtension_finsupp_sum_of_complete_family_local
    {ι : Type (u + 1)}
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (c : ι →₀ K) :
    let bR₀ :=
      simple_finiteRep_classes_basis_of_complete_family E hE_pairwise hE_complete
    let bφ :=
      irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
        (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete
    scalarExtensionVirtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (G := G) lift (c.sum fun i a ↦ a ⊗ₜ[ℤ] bR₀ i) =
      c.sum fun i a ↦ a • bφ i := by
  -- Compare the two bases term by term and let linearity handle the finite sum.
  simp [Finsupp.sum, map_sum,
    simple_finiteRep_classes_basis_of_complete_family_apply,
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply,
    virtualModularCharacterOnPRegularConjClass_class]

/-- Helper for Theorem 18-18.2-2: the scalar-extension Brauer-character map is surjective once a
complete irreducible family is fixed. -/
private theorem scalarExtension_surjective_of_complete_family_local
    {ι : Type (u + 1)}
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Function.Surjective
      (scalarExtensionVirtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (G := G) lift :
        K ⊗[ℤ] R₀[k](G) →ₗ[K] (PRegularConjClass G p → K)) := by
  classical
  let bR₀ :=
    simple_finiteRep_classes_basis_of_complete_family E hE_pairwise hE_complete
  let bφ :=
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete
  intro f
  obtain ⟨c, hc⟩ :=
    exists_finite_brauer_character_expansion_of_complete_family
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete f
  refine ⟨c.sum fun i a ↦ a ⊗ₜ[ℤ] bR₀ i, ?_⟩
  -- Use the Brauer-character basis expansion of `f` as the preimage recipe.
  calc
    scalarExtensionVirtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (G := G) lift (c.sum fun i a ↦ a ⊗ₜ[ℤ] bR₀ i) =
      c.sum fun i a ↦ a • bφ i := by
          simpa [bR₀, bφ] using
            scalarExtension_finsupp_sum_of_complete_family_local
              (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete c
    _ = f := by
          simpa [Finsupp.sum, bφ,
            irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions_apply] using hc

/-- Helper for Theorem 18-18.2-2: the scalar-extension Brauer-character map is injective once a
complete irreducible family is fixed. -/
private theorem scalarExtension_injective_of_complete_family_local
    {ι : Type (u + 1)}
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift)
    (E : ι → FDRep k G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E) :
    Function.Injective
      (scalarExtensionVirtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (G := G) lift :
        K ⊗[ℤ] R₀[k](G) →ₗ[K] (PRegularConjClass G p → K)) := by
  classical
  let bR₀ :=
    simple_finiteRep_classes_basis_of_complete_family E hE_pairwise hE_complete
  let bφ :=
    irreducible_modular_characters_form_basis_of_pRegularConjClassFunctions
      (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete
  -- Base-change the simple-class `ℤ`-basis of `R₀[k](G)` to a `K`-basis of the tensor product.
  let bT : Module.Basis ι K (K ⊗[ℤ] R₀[k](G)) := bR₀.baseChange K
  -- The scalar-extension map sends the base-changed basis to the Brauer-character basis, so it
  -- agrees with the corresponding basis equivalence.
  have hmap :
      (scalarExtensionVirtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (G := G) lift :
          K ⊗[ℤ] R₀[k](G) →ₗ[K] (PRegularConjClass G p → K)) =
        (bT.equiv bφ (_root_.Equiv.refl ι)).toLinearMap := by
    refine bT.ext fun i ↦ ?_
    -- The basis equivalence matches the `i`-th basis vectors by construction.
    have hRHS : (bT.equiv bφ (_root_.Equiv.refl ι)).toLinearMap (bT i) = bφ i := by
      simp
    -- The scalar-extension map evaluates on the pure tensor `1 ⊗ [E i]₀` by the tensor formula.
    have hbT : bT i = (1 : K) ⊗ₜ[ℤ] bR₀ i := by
      simp [bT]
    rw [hRHS, hbT, scalarExtensionVirtualModularCharacterOnPRegularConjClass_tmul, one_smul]
    -- Both sides are the Brauer character of the simple representation `E i`.
    simp [bR₀, bφ, virtualModularCharacterOnPRegularConjClass_class]
  rw [hmap]
  exact (bT.equiv bφ (_root_.Equiv.refl ι)).injective

/-- Helper for Theorem 18-18.2-2: the scalar-extension Brauer-character map is bijective. -/
private theorem scalarExtensionVirtualModularCharacterOnPRegularConjClass_bijective
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift) :
    Function.Bijective
      (scalarExtensionVirtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (G := G) lift :
        K ⊗[ℤ] R₀[k](G) →ₗ[K] (PRegularConjClass G p → K)) := by
  classical
  obtain ⟨ι, E, hE_pairwise, hE_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_theorem18_2_2_local (k := k) (G := G)
  constructor
  · exact
      scalarExtension_injective_of_complete_family_local
        (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete
  · exact
      scalarExtension_surjective_of_complete_family_local
        (p := p) (k := k) (K := K) (G := G) lift hlift E hE_pairwise hE_complete

/-- Theorem 18-18.2-2: the canonical `K`-linear scalar extension of the virtual modular character
map is a linear isomorphism from `K ⊗[ℤ] R_k(G)` onto the `K`-algebra of `K`-valued functions on
the `p`-regular conjugacy classes of `G`.

Serre's modular-character theorem is a positive-characteristic statement: here `p` is the prime
characteristic of `k`. The earlier `p = 0` branch was not source-faithful, since
`IsPRegular 0 g` forces `g = 1` in this formalization. -/
noncomputable def scalarExtensionVirtualModularCharacterOnPRegularConjClassLinearEquiv
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift) :
    K ⊗[ℤ] R₀[k](G) ≃ₗ[K] (PRegularConjClass G p → K) :=
  LinearEquiv.ofBijective
    (scalarExtensionVirtualModularCharacterOnPRegularConjClass
      (p := p) (k := k) (G := G) lift)
    (scalarExtensionVirtualModularCharacterOnPRegularConjClass_bijective
      (p := p) (k := k) (K := K) (G := G) lift hlift)

/-- Companion: the underlying linear map of
`scalarExtensionVirtualModularCharacterOnPRegularConjClassLinearEquiv` is bijective. -/
theorem bijective_scalarExtensionVirtualModularCharacterOnPRegularConjClass
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift) :
    Function.Bijective
      (scalarExtensionVirtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (G := G) lift :
        K ⊗[ℤ] R₀[k](G) →ₗ[K] (PRegularConjClass G p → K)) :=
  scalarExtensionVirtualModularCharacterOnPRegularConjClass_bijective
    (p := p) (k := k) (K := K) (G := G) lift hlift

/-- Helper for Theorem 18-18.2-2: the algebra-hom form of the scalar-extension Brauer-character
map has the same bijectivity as the underlying linear map. -/
private theorem scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgHom_bijective
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift) :
    Function.Bijective
      (scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgHom
        (p := p) (k := k) lift :
        K ⊗[ℤ] R₀[k](G) →ₐ[K] (PRegularConjClass G p → K)) := by
  -- The algebra hom has the same underlying function as the already-bijective linear map.
  simpa [scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgHom] using
    bijective_scalarExtensionVirtualModularCharacterOnPRegularConjClass
      (p := p) (k := k) (K := K) (G := G) lift hlift

/-- Theorem 18-18.2-2, canonical multiplicative form: the scalar-extension Brauer-character map is
a `K`-algebra isomorphism from `K ⊗[ℤ] R_k(G)` onto the function ring on the `p`-regular
conjugacy classes of `G`. -/
noncomputable def scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgEquiv
    (lift : PrimeToPRoot p k →* Kˣ)
    (hlift : Function.Injective lift) :
    K ⊗[ℤ] R₀[k](G) ≃ₐ[K] (PRegularConjClass G p → K) :=
  -- Package the multiplicative scalar-extension map with its bijectivity.
  AlgEquiv.ofBijective
    (scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgHom
      (p := p) (k := k) lift)
    (scalarExtensionVirtualModularCharacterOnPRegularConjClassAlgHom_bijective
      (p := p) (k := k) (K := K) (G := G) lift hlift)

end Equivalence

end ScalarExtension

end Representation
