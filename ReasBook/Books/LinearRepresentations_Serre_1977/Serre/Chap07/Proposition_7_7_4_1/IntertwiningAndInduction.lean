import Mathlib.LinearAlgebra.Projection
import LinearRepresentations_Serre_1977.Serre.Chap07.Proposition_7_7_3_1
import LinearRepresentations_Serre_1977.Serre.Chap07.Remark_7_7_3_2
import LinearRepresentations_Serre_1977.Serre.Chap02.Theorem_2_2_3_5

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientIntertwining (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

/-- Helper for Proposition 7-7.4-1: postcomposing with a representation equivalence identifies
intertwining spaces with the same source. -/
noncomputable def intertwiningMapCongrRight
    {Γ : Type*} [Group Γ]
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {W' : Type*} [AddCommGroup W'] [Module k W']
    {U' : Type*} [AddCommGroup U'] [Module k U']
    {ρ : Representation k Γ V'} {σ : Representation k Γ W'} {τ : Representation k Γ U'}
    (e : σ.Equiv τ) :
    ρ.IntertwiningMap σ ≃ₗ[k] ρ.IntertwiningMap τ :=
  { toFun := fun f ↦ e.toIntertwiningMap.comp f
    invFun := fun f ↦ e.symm.toIntertwiningMap.comp f
    left_inv := by
      -- The two compositions simplify pointwise to the identity intertwiner.
      intro f
      ext x
      simp
    right_inv := by
      -- The same pointwise simplification gives the inverse identity.
      intro f
      ext x
      simp
    map_add' := by
      intro f g
      ext x
      simp
    map_smul' := by
      intro a f
      ext x
      simp
  }
/-- Helper for Proposition 7-7.4-1: postcomposing an intertwiner with a target equivalence
evaluates by applying the forward target equivalence afterwards. -/
theorem intertwiningMapCongrRight_apply
    {Γ : Type*} [Group Γ]
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {W' : Type*} [AddCommGroup W'] [Module k W']
    {U' : Type*} [AddCommGroup U'] [Module k U']
    {ρ : Representation k Γ V'} {σ : Representation k Γ W'} {τ : Representation k Γ U'}
    (e : σ.Equiv τ)
    (f : ρ.IntertwiningMap σ) (x : V') :
    ((intertwiningMapCongrRight (k := k) (ρ := ρ) (σ := σ) (τ := τ) e) f) x =
      e (f x) := by
  rfl
/-- Helper for Proposition 7-7.4-1: precomposing with a representation equivalence identifies
intertwining spaces with the same codomain. -/
noncomputable def intertwiningMapCongrLeft
    {Γ : Type*} [Group Γ]
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {W' : Type*} [AddCommGroup W'] [Module k W']
    {U' : Type*} [AddCommGroup U'] [Module k U']
    {ρ : Representation k Γ V'} {σ : Representation k Γ W'} {τ : Representation k Γ U'}
    (e : ρ.Equiv σ) :
    ρ.IntertwiningMap τ ≃ₗ[k] σ.IntertwiningMap τ :=
  { toFun := fun f ↦ f.comp e.symm.toIntertwiningMap
    invFun := fun f ↦ f.comp e.toIntertwiningMap
    left_inv := by
      -- The inverse compositions simplify pointwise to the original intertwiner.
      intro f
      ext x
      simp
    right_inv := by
      -- The same pointwise simplification recovers the target intertwiner.
      intro f
      ext x
      simp
    map_add' := by
      intro f g
      ext x
      simp
    map_smul' := by
      intro a f
      ext x
      simp
  }
/-- Helper for Proposition 7-7.4-1: precomposing an intertwiner with a source equivalence
evaluates by first applying the inverse source equivalence. -/
theorem intertwiningMapCongrLeft_apply
    {Γ : Type*} [Group Γ]
    {V' : Type*} [AddCommGroup V'] [Module k V']
    {W' : Type*} [AddCommGroup W'] [Module k W']
    {U' : Type*} [AddCommGroup U'] [Module k U']
    {ρ : Representation k Γ V'} {σ : Representation k Γ W'} {τ : Representation k Γ U'}
    (e : ρ.Equiv σ)
    (f : Representation.IntertwiningMap ρ τ) (x : W') :
    ((intertwiningMapCongrLeft (k := k) (ρ := ρ) (σ := σ) (τ := τ) e) f) x =
      f (e.symm x) := by
  rfl
/-- Helper for Proposition 7-7.4-1: transporting the source of morphisms along an isomorphism in
`Rep` identifies the corresponding hom spaces. -/
noncomputable def homCongrLeft
    {Γ : Type*} [Group Γ]
    {A B C : Rep k Γ} (i : A ≅ B) :
    (A ⟶ C) ≃ₗ[k] (B ⟶ C) :=
  (Rep.homLinearEquiv A C) ≪≫ₗ
    intertwiningMapCongrLeft (Representation.equivOfIso i) ≪≫ₗ
      (Rep.homLinearEquiv B C).symm
/-- Helper for Proposition 7-7.4-1: transporting the source of a morphism along an isomorphism
evaluates by first applying the inverse source isomorphism. -/
theorem homCongrLeft_apply
    {Γ : Type*} [Group Γ]
    {A B C : Rep k Γ} (i : A ≅ B)
    (f : A ⟶ C) (x : B.V) :
    (((homCongrLeft (k := k) (A := A) (B := B) (C := C) i) f).hom) x =
      f.hom (i.inv.hom x) := by
  rfl
/-- Helper for Proposition 7-7.4-1: transporting the target of morphisms along an isomorphism in
`Rep` identifies the corresponding hom spaces. -/
noncomputable def homCongrRight
    {Γ : Type*} [Group Γ]
    {A B C : Rep k Γ} (i : B ≅ C) :
    (A ⟶ B) ≃ₗ[k] (A ⟶ C) :=
  (Rep.homLinearEquiv A B) ≪≫ₗ
    intertwiningMapCongrRight (Representation.equivOfIso i) ≪≫ₗ
      (Rep.homLinearEquiv A C).symm
/-- Helper for Proposition 7-7.4-1: transporting the target of a morphism along an isomorphism
evaluates by applying the forward target isomorphism afterwards. -/
theorem homCongrRight_apply
    {Γ : Type*} [Group Γ]
    {A B C : Rep k Γ} (i : B ≅ C)
    (f : A ⟶ B) (x : A.V) :
    (((homCongrRight (k := k) (A := A) (B := B) (C := C) i) f).hom) x =
      i.hom.hom (f.hom x) := by
  rfl
/-- Helper for Proposition 7-7.4-1: choose double-coset representatives with the identity class
represented by `1`. -/
noncomputable def doubleCosetRepresentative
    (H : Subgroup G) : DoubleCoset.Quotient (H : Set G) H → G :=
  fun q ↦ if q = DoubleCoset.mk H H 1 then 1 else q.out
/-- Helper for Proposition 7-7.4-1: the chosen representative still lies in the prescribed double
coset. -/
theorem doubleCosetRepresentative_spec
    (H : Subgroup G) (q : DoubleCoset.Quotient (H : Set G) H) :
    DoubleCoset.mk H H (doubleCosetRepresentative H q) = q := by
  classical
  by_cases hq : q = DoubleCoset.mk H H 1
  · -- The distinguished identity class is represented by `1`.
    simp [doubleCosetRepresentative, hq]
  · -- Every other class uses its quotient representative.
    simp [doubleCosetRepresentative, hq, DoubleCoset.out_eq' H H q]
/-- Helper for Proposition 7-7.4-1: the representative choice is a genuine system of
double-coset representatives. -/
theorem doubleCosetRepresentative_bijective
    (H : Subgroup G) :
    Function.Bijective
      (fun q : DoubleCoset.Quotient (H : Set G) H ↦
        DoubleCoset.mk H H (doubleCosetRepresentative H q)) := by
  constructor
  · intro a b hab
    simpa [doubleCosetRepresentative_spec] using hab
  · intro q
    exact ⟨q, doubleCosetRepresentative_spec H q⟩
/-- Helper for Proposition 7-7.4-1: the distinguished identity double coset is represented by
`1`. -/
theorem doubleCosetRepresentative_identity
    (H : Subgroup G) :
    doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)) = 1 := by
  -- The representative function is defined to choose `1` on the identity class.
  simp [doubleCosetRepresentative]
/-- Helper for Proposition 7-7.4-1: every nonidentity double coset is represented by an element
outside `H`, since the identity class is represented by `1`. -/
theorem doubleCoset_eq_identity_of_mem
    (H : Subgroup G) {s : G} (hs : s ∈ H) :
    DoubleCoset.mk H H s = DoubleCoset.mk H H 1 := by
  -- An element of `H` belongs to the identity double coset.
  rw [DoubleCoset.eq]
  exact ⟨s⁻¹, H.inv_mem hs, 1, H.one_mem, by simp⟩
/-- Helper for Proposition 7-7.4-1: every nonidentity double coset is represented by an element
outside `H`, since the identity class is represented by `1`. -/
theorem doubleCosetRepresentative_not_mem_of_ne_identity
    (H : Subgroup G) {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H 1) :
    doubleCosetRepresentative H q ∉ H := by
  intro hs
  have hrep :
      DoubleCoset.mk H H (doubleCosetRepresentative H q) = DoubleCoset.mk H H (1 : G) := by
    -- Membership in `H` forces the representative into the identity double coset.
    exact doubleCoset_eq_identity_of_mem H hs
  have : q = DoubleCoset.mk H H 1 := by
    calc
      q = DoubleCoset.mk H H (doubleCosetRepresentative H q) := by
        symm
        exact doubleCosetRepresentative_spec H q
      _ = DoubleCoset.mk H H 1 := hrep
  exact hq this
/-- Helper for Proposition 7-7.4-1: for the pair `(H, H)`, belonging to the identity double coset
is equivalent to belonging to `H`. -/
theorem mem_of_doubleCoset_eq_identity
    (H : Subgroup G) {s : G}
    (hs : DoubleCoset.mk H H s = DoubleCoset.mk H H 1) :
    s ∈ H := by
  rw [DoubleCoset.eq] at hs
  rcases hs with ⟨a, ha, b, hb, hab⟩
  have hs_eq : s = a⁻¹ * b⁻¹ := by
    calc
      s = a⁻¹ * (a * s * b) * b⁻¹ := by simp [mul_assoc]
      _ = a⁻¹ * 1 * b⁻¹ := by rw [← hab]
      _ = a⁻¹ * b⁻¹ := by simp
  rw [hs_eq]
  exact H.mul_mem (H.inv_mem ha) (H.inv_mem hb)
/-- Helper for Proposition 7-7.4-1: an element outside `H` represents a nonidentity double coset. -/
theorem doubleCoset_ne_identity_of_not_mem
    (H : Subgroup G) {s : G} (hs : s ∉ H) :
    DoubleCoset.mk H H s ≠ DoubleCoset.mk H H 1 := by
  -- Route correction: the forward implication only needs the basic double-coset fact that an
  -- off-subgroup element cannot lie in the distinguished identity class.
  intro h
  exact hs (mem_of_doubleCoset_eq_identity H h)
/-- Helper for Proposition 7-7.4-1: maps into a finite representation direct sum are equivalent to
families of maps into the individual summands. -/
noncomputable def intertwiningMapIntoDirectSumEquivPi_local
    {Γ : Type*} [Group Γ]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Type*} [AddCommGroup A] [Module k A]
    {M : ι → Type*}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module k (M i)]
    (ρ : Representation k Γ A) (π : ∀ i, Representation k Γ (M i)) :
    ρ.IntertwiningMap (Representation.directSum π) ≃ₗ[k] ∀ i, ρ.IntertwiningMap (π i) :=
  { toFun := fun F i ↦
      -- Project the direct-sum target to its `i`-th coordinate.
      ((DirectSum.component k ι M i).comp F.toLinearMap).intertwiningMap_of_isIntertwiningMap
        ρ (π i) fun g x ↦ by
          simpa [Representation.directSum] using
            congrArg (fun T ↦ DirectSum.component k ι M i (T x))
              (F.isIntertwining' g)
    invFun := fun f ↦
      -- Reassemble a family of target coordinates into one map to the direct sum.
      { toLinearMap :=
          (DirectSum.linearEquivFunOnFintype k ι M).symm.toLinearMap.comp
            (LinearMap.pi fun i ↦ (f i).toLinearMap)
        isIntertwining' := by
          intro g
          ext x i
          change ((LinearMap.pi fun i ↦ (f i).toLinearMap) ((ρ g) x)) i =
            ((π i) g) (((LinearMap.pi fun i ↦ (f i).toLinearMap) x) i)
          simp [Representation.IntertwiningMap.isIntertwining] }
    left_inv := by
      intro F
      -- Equality of direct-sum-valued maps is checked on each coordinate.
      apply Representation.IntertwiningMap.ext
      ext x i
      change DirectSum.component k ι M i (F x) = (F x) i
      rfl
    right_inv := by
      intro f
      -- Each recovered coordinate is definitionally the original one.
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      change DirectSum.component k ι M i
          ((DirectSum.linearEquivFunOnFintype k ι M).symm
            ((LinearMap.pi fun i ↦ (f i).toLinearMap) x)) =
        (f i) x
      rfl
    map_add' := by
      intro F G
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a F
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl }
/-- Helper for Proposition 7-7.4-1: intertwining maps out of a representation direct sum are
equivalent to families of intertwining maps out of each summand. -/
noncomputable def directSum_intertwiningMapEquivPi_local
    {Γ : Type*} [Group Γ]
    {ι : Type*}
    {M : ι → Type*}
    [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module k (M i)]
    {W' : Type*} [AddCommGroup W'] [Module k W']
    (π : ∀ i, Representation k Γ (M i)) (τ : Representation k Γ W') :
    (Representation.directSum π).IntertwiningMap τ ≃ₗ[k] ∀ i, (π i).IntertwiningMap τ :=
  let _ : DecidableEq ι := Classical.decEq ι
  { toFun := fun F i ↦
      -- Restrict the source intertwiner to the `i`-th direct-sum summand.
      ((F.toLinearMap.comp
          (DirectSum.lof k ι M i)).intertwiningMap_of_isIntertwiningMap
        (π i) τ fun g x ↦ by
          simpa [Representation.directSum] using
            congr($(F.isIntertwining' g) (DirectSum.lof k ι M i x)))
    invFun := fun f ↦
      -- Reassemble a coordinate family into a map out of the direct sum.
      { toLinearMap := DirectSum.toModule k _ _ fun i ↦ (f i).toLinearMap
        isIntertwining' := by
          intro g
          apply DirectSum.linearMap_ext
          intro i
          ext x
          simp [Representation.directSum, Representation.IntertwiningMap.isIntertwining] }
    left_inv := by
      intro F
      -- Equality of intertwiners out of a direct sum is checked on each summand inclusion.
      apply Representation.IntertwiningMap.ext
      apply DirectSum.linearMap_ext
      intro i
      ext x
      change
        (DirectSum.toModule k ι W'
          (fun j ↦ F.toLinearMap.comp (DirectSum.lof k ι M j)))
          (DirectSum.lof k ι M i x) =
        F (DirectSum.lof k ι M i x)
      simp
    right_inv := by
      intro f
      -- Each recovered coordinate agrees with the original family by construction.
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      change
        (DirectSum.toModule k ι W' fun j ↦ (f j).toLinearMap)
          (DirectSum.lof k ι M i x) =
        (f i) x
      simp
    map_add' := by
      intro F H
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a F
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl }
/-- Helper for Proposition 7-7.4-1: the explicit projection to the unit-coset copy inside the
induced representation. -/
noncomputable def inducedIdentityCopyProjectionAux
    (H : Subgroup G) (ρ : Representation k H V) :
    (G →₀ k) →ₗ[k] V →ₗ[k] V :=
  Finsupp.lift _ _ _ fun g ↦
    @dite _ (g ∈ H) ((Classical.decPred fun x : G ↦ x ∈ H) g) (fun hg ↦ ρ ⟨g, hg⟩⁻¹)
      (fun _ ↦ 0)
/-- Helper for Proposition 7-7.4-1: the unit-coset projection respects the induction
coinvariant relations. -/
theorem induced_identity_copy_projectionAux_respects
    (H : Subgroup G) (ρ : Representation k H V) :
    ∀ h : H,
      TensorProduct.lift (inducedIdentityCopyProjectionAux H ρ) ∘ₗ
          (Representation.tprod ((leftRegular k G).comp H.subtype) ρ) h =
        TensorProduct.lift (inducedIdentityCopyProjectionAux H ρ) := by
  classical
  intro h
  -- Check the coinvariant relation on a basis tensor `δ_g ⊗ v`.
  ext g v
  by_cases hg : g ∈ H
  · have hhg : ((h : G) * g) ∈ H := H.mul_mem h.property hg
    have hmul : ρ ⟨(h : G) * g, hhg⟩⁻¹ (ρ h v) = ρ ⟨g, hg⟩⁻¹ v := by
      have hsub : ((⟨(h : G) * g, hhg⟩⁻¹ : H) * h) = ⟨g, hg⟩⁻¹ := by
        ext
        simp [mul_assoc]
      calc
        ρ ⟨(h : G) * g, hhg⟩⁻¹ (ρ h v)
            = ρ (((⟨(h : G) * g, hhg⟩⁻¹ : H) * h)) v := by
                simp [Module.End.mul_apply, map_mul]
        _ = ρ ⟨g, hg⟩⁻¹ v := by
              rw [hsub]
    -- On the unit-coset copy, the projection cancels the extra translate.
    simpa [inducedIdentityCopyProjectionAux, TensorProduct.lift.tmul, hg, hhg] using hmul
  · have hnhg : ((h : G) * g) ∉ H := by
      intro hmem
      have htmp : ((h : G)⁻¹ * ((h : G) * g)) ∈ H :=
        H.mul_mem (H.inv_mem h.property) hmem
      have hg' : g ∈ H := by
        simpa [mul_assoc] using htmp
      exact hg hg'
    -- Off the unit-coset copy, both sides project to zero.
    rw [inducedIdentityCopyProjectionAux]
    simp [TensorProduct.lift.tmul, hg, hnhg]
/-- Helper for Proposition 7-7.4-1: projection from `Ind_H^G(ρ)` onto the unit-coset copy of
`ρ`. -/
noncomputable def inducedIdentityCopyProjection
    (H : Subgroup G) (ρ : Representation k H V) :
    Representation.IndV H.subtype ρ →ₗ[k] V :=
  Representation.Coinvariants.lift _
    (TensorProduct.lift (inducedIdentityCopyProjectionAux H ρ))
    (induced_identity_copy_projectionAux_respects H ρ)
/-- Helper for Proposition 7-7.4-1: the unit-coset projection recovers the original vector on
`IndV.mk ... 1`. -/
theorem induced_identity_copy_projection_apply_mk_one
    (H : Subgroup G) (ρ : Representation k H V) (v : V) :
    inducedIdentityCopyProjection H ρ (Representation.IndV.mk H.subtype ρ 1 v) = v := by
  classical
  have hone : (1 : G) ∈ H := H.one_mem
  have hbase : ρ ⟨1, hone⟩⁻¹ v = v := by
    have hsub : ((⟨1, hone⟩ : H)⁻¹) = 1 := by
      ext
      simp
    rw [hsub]
    exact LinearMap.congr_fun ρ.map_one v
  -- Evaluating the quotient lift at the unit generator reduces to the identity on `V`.
  simpa [inducedIdentityCopyProjection, inducedIdentityCopyProjectionAux, TensorProduct.lift.tmul,
    hone] using hbase
/-- Helper for Proposition 7-7.4-1: the unit-copy projection kills every standard generator whose
group label lies outside `H`. -/
theorem induced_identity_copy_projection_apply_mk_of_not_mem
    (H : Subgroup G) (ρ : Representation k H V)
    {g : G} (hg : g ∉ H) (v : V) :
    inducedIdentityCopyProjection H ρ (Representation.IndV.mk H.subtype ρ g v) = 0 := by
  classical
  -- Outside the unit copy, the explicit projection formula is definitionally zero.
  simp [inducedIdentityCopyProjection, inducedIdentityCopyProjectionAux, TensorProduct.lift.tmul, hg]
/-- Helper for Proposition 7-7.4-1: a nonidentity double-coset representative contributes no
vector to the unit-copy projection, even after the inverse translate used by the Mackey seed
generator. -/
theorem induced_identity_copy_projection_apply_mk_inv_representative_of_ne_identity
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G)) (v : V) :
    inducedIdentityCopyProjection H ρ
      (Representation.IndV.mk H.subtype ρ (doubleCosetRepresentative H q)⁻¹ v) = 0 := by
  -- A nonidentity representative lies outside `H`, and so does its inverse.
  apply induced_identity_copy_projection_apply_mk_of_not_mem (k := k) (H := H) (ρ := ρ)
  intro hs
  have hrep : doubleCosetRepresentative H q ∉ H :=
    doubleCosetRepresentative_not_mem_of_ne_identity H hq
  exact hrep <| by simpa using H.inv_mem hs
/-- Helper for Proposition 7-7.4-1: the standard generator `IndV.mk H.subtype ρ 1` is
injective. -/
theorem induced_unit_generator_injective
    (H : Subgroup G) (ρ : Representation k H V) :
    Function.Injective (Representation.IndV.mk H.subtype ρ 1) := by
  intro x y hxy
  -- Apply the explicit projection back to `ρ`; it is a left inverse on the unit copy.
  have hproj := congrArg (inducedIdentityCopyProjection H ρ) hxy
  calc
    x = inducedIdentityCopyProjection H ρ (Representation.IndV.mk H.subtype ρ 1 x) := by
          symm
          exact induced_identity_copy_projection_apply_mk_one H ρ x
    _ = inducedIdentityCopyProjection H ρ (Representation.IndV.mk H.subtype ρ 1 y) := hproj
    _ = y := induced_identity_copy_projection_apply_mk_one H ρ y
/-- Helper for Proposition 7-7.4-1: the unit-copy projection is surjective because it is a left
inverse to the unit generator `IndV.mk ... 1`. -/
theorem induced_identity_copy_projection_surjective
    (H : Subgroup G) (ρ : Representation k H V) :
    Function.Surjective (inducedIdentityCopyProjection H ρ) := by
  intro v
  refine ⟨Representation.IndV.mk H.subtype ρ 1 v, ?_⟩
  exact induced_identity_copy_projection_apply_mk_one H ρ v
/-- Helper for Proposition 7-7.4-1: replace an unbundled representation by the same action on a
`ULift` carrier so that the bundled owner lives in the common universe `max u v`. -/
def uliftRepresentation
    {Γ : Type*} [Monoid Γ]
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ : Representation k Γ V') :
    Representation k Γ (ULift.{u} V') where
  toFun g :=
    { toFun := fun x ↦ ⟨ρ g x.down⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul]
/-- Helper for Proposition 7-7.4-1: the `ULift` model is equivariantly identical to the original
representation. -/
def uliftRepresentationEquiv
    {Γ : Type*} [Monoid Γ]
    {V' : Type*} [AddCommGroup V'] [Module k V']
    (ρ : Representation k Γ V') :
    ρ.Equiv (uliftRepresentation (k := k) ρ) :=
  Representation.Equiv.mk ULift.moduleEquiv.symm fun g ↦ by
    -- Both actions are definitionally the same after inserting the `ULift` wrapper.
    ext x
    rfl
/-- Helper for Proposition 7-7.4-1: in an induced representation, a generator indexed by
`φ h` is the unit generator with coefficient translated by `h⁻¹`. -/
theorem ind_mk_eq_mk_one_inv
    {Γ Δ : Type*} [Group Γ] [Group Δ]
    {φ : Γ →* Δ}
    {A : Type*} [AddCommGroup A] [Module k A]
    (θ : Representation k Γ A) (h : Γ) (x : A) :
    Representation.IndV.mk φ θ (φ h) x =
      Representation.IndV.mk φ θ 1 (θ h⁻¹ x) := by
  -- This is the standard coinvariant relation specialized to the unit `Δ`-coordinate.
  symm
  simpa [Representation.IndV.mk] using
      (Representation.Coinvariants.mk_inv_tmul
        (ρ := (Representation.leftRegular k Δ).comp φ)
        (τ := θ)
        (x := Finsupp.single (1 : Δ) (1 : k))
        (y := x)
      (g := h))
/-- Helper for Proposition 7-7.4-1: intertwining spaces are unchanged by simultaneously replacing
both source and target representations with their `ULift` models. -/
noncomputable def intertwiningMap_ulift_equiv
    {Γ : Type*} [Group Γ]
    {V' W' : Type*} [AddCommGroup V'] [Module k V']
    [AddCommGroup W'] [Module k W']
    (ρ : Representation k Γ V') (σ : Representation k Γ W') :
    ρ.IntertwiningMap σ ≃ₗ[k]
      (uliftRepresentation (k := k) ρ).IntertwiningMap
        (uliftRepresentation (k := k) σ) := by
  let ρu : Representation k Γ (ULift.{u} V') := uliftRepresentation (k := k) ρ
  let σu : Representation k Γ (ULift.{u} W') := uliftRepresentation (k := k) σ
  let eρ : ρ.Equiv ρu := uliftRepresentationEquiv (k := k) ρ
  let eσ : σ.Equiv σu := uliftRepresentationEquiv (k := k) σ
  let hleft : ρ.IntertwiningMap σ ≃ₗ[k] ρu.IntertwiningMap σ :=
    intertwiningMapCongrLeft (k := k) (ρ := ρ) (σ := ρu) (τ := σ) eρ
  let hright : ρu.IntertwiningMap σ ≃ₗ[k] ρu.IntertwiningMap σu :=
    intertwiningMapCongrRight (k := k) (ρ := ρu) (σ := σ) (τ := σu) eσ
  -- First transport the source representation, then transport the target representation.
  exact hleft ≪≫ₗ hright
/-- Helper for Proposition 7-7.4-1: induction carries an equivariant equivalence of
`H`-representations to an equivariant equivalence of the induced `G`-representations. -/
noncomputable def inducedRepresentationEquiv
    (H : Subgroup G)
    {W : Type*} [AddCommGroup W] [Module k W]
    {ρ : Representation k H V} {σ : Representation k H W}
    (e : ρ.Equiv σ) :
    (Rep.ind H.subtype (of ρ)).ρ.Equiv (Rep.ind H.subtype (of σ)).ρ := by
  let inducedHom :
      (Rep.ind H.subtype (of ρ)).ρ.IntertwiningMap (Rep.ind H.subtype (of σ)).ρ :=
    { toLinearMap := Representation.Coinvariants.map _ _
        (e.toLinearMap.lTensor _)
        (by
          simp [LinearMap.lTensor_comp_map, e.toIntertwiningMap.2,
            LinearMap.map_comp_lTensor])
      isIntertwining' := by
        -- The induced action commutes with the transported source map on standard generators.
        intro g
        ext h a
        simp }
  let inducedInv :
      (Rep.ind H.subtype (of σ)).ρ.IntertwiningMap (Rep.ind H.subtype (of ρ)).ρ :=
    { toLinearMap := Representation.Coinvariants.map _ _
        (e.symm.toLinearMap.lTensor _)
        (by
          intro g
          ext x y
          simpa using
            congrArg (fun z ↦ (Finsupp.single (↑g * x) (1 : k)) ⊗ₜ[k] z)
              (LinearMap.congr_fun (e.symm.toIntertwiningMap.2 g) y))
      isIntertwining' := by
        -- The same generator computation gives the inverse intertwining map.
        intro g
        ext h a
        simp }
  have hinduced_inv_hom :
      inducedInv.toLinearMap ∘ₗ inducedHom.toLinearMap = LinearMap.id := by
    -- The two induced maps are inverse because they agree with `e` and `e.symm` on `IndV.mk`.
    apply Representation.IndV.hom_ext
    intro h
    ext a
    simp [inducedHom, inducedInv]
  have hinduced_hom_inv :
      inducedHom.toLinearMap ∘ₗ inducedInv.toLinearMap = LinearMap.id := by
    -- The same generator test proves the inverse identity in the opposite order.
    apply Representation.IndV.hom_ext
    intro h
    ext a
    simp [inducedHom, inducedInv]
  exact Representation.Equiv.mk
    (LinearEquiv.ofLinear inducedHom.toLinearMap inducedInv.toLinearMap
      hinduced_hom_inv hinduced_inv_hom)
    inducedHom.isIntertwining'
/-- Helper for Proposition 7-7.4-1: after replacing `ρ` by its `ULift` model to align category
universes, Frobenius reciprocity identifies endomorphisms of `Ind_H^G(ρ)` with maps from the
restricted induced representation back to `ρ`. -/
noncomputable def induced_endomorphism_to_restricted_hom_equiv
    (H : Subgroup G) (ρ : Representation k H V) :
    let τ : Rep.{max u v} k G := Rep.ind H.subtype (of ρ)
    (τ ⟶ τ) ≃ₗ[k] (Rep.res H.subtype τ ⟶ Rep.of (uliftRepresentation (k := k) ρ)) := by
  classical
  let τ : Rep.{max u v} k G := Rep.ind H.subtype (of ρ)
  let ρu : Representation k H (ULift.{u} V) := uliftRepresentation (k := k) ρ
  let eInd : τ ≅ Rep.ind H.subtype (Rep.of ρu) :=
    Rep.mkIso (inducedRepresentationEquiv (k := k) H (uliftRepresentationEquiv (k := k) ρ))
  let _ : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  let _ : DecidableRel ((QuotientGroup.rightRel H : Setoid G).r) := Classical.decRel _
  let eCoind : Rep.ind H.subtype (Rep.of ρu) ≅ Rep.coind H.subtype (Rep.of ρu) :=
    Rep.indCoindIso (Rep.of ρu)
  let eRight : (τ ⟶ τ) ≃ₗ[k] (τ ⟶ Rep.coind H.subtype (Rep.of ρu)) :=
    homCongrRight (k := k) (A := τ) (B := τ)
      (C := Rep.coind H.subtype (Rep.of ρu)) (eInd ≪≫ eCoind)
  let eLeft0 :
      (Rep.res H.subtype τ ⟶ Rep.of ρu) ≃ₗ[k]
        (τ ⟶ Rep.coind H.subtype (Rep.of ρu)) :=
    Rep.resCoindHomEquiv H.subtype τ (Rep.of ρu)
  let eLeft :
      (τ ⟶ Rep.coind H.subtype (Rep.of ρu)) ≃ₗ[k]
        (Rep.res H.subtype τ ⟶ Rep.of ρu) :=
    eLeft0.symm
  -- This is exactly the Frobenius/coinduction step from the source proof, with `ULift`
  -- inserted only to keep all bundled objects in the same universe.
  exact eRight.trans eLeft
/-- Helper for Proposition 7-7.4-1: a semisimple representation is irreducible once every
nonzero self-intertwiner is bijective. -/
theorem isIrreducible_of_semisimple_and_nonzero_endomorphisms_bijective
    {U : Type*} [AddCommGroup U] [Module k U] [Nontrivial U]
    (τ : Representation k G U)
    [Representation.IsSemisimpleRepresentation τ]
    (hbij :
      ∀ f : τ.IntertwiningMap τ, f ≠ 0 → Function.Bijective f) :
    τ.IsIrreducible := by
  rw [Representation.IsIrreducible]
  letI : Nontrivial (Subrepresentation τ) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  refine IsSimpleOrder.of_forall_eq_top ?_
  intro σ hσ
  obtain ⟨σ', hcompl⟩ := exists_isCompl σ
  have hcompl_sub : IsCompl σ.toSubmodule σ'.toSubmodule := by
    rw [isCompl_iff]
    constructor
    · rw [disjoint_iff]
      calc
        σ.toSubmodule ⊓ σ'.toSubmodule = (σ ⊓ σ').toSubmodule := by simp
        _ = ⊥ := by simpa using congrArg Subrepresentation.toSubmodule hcompl.inf_eq_bot
    · rw [codisjoint_iff]
      calc
        σ.toSubmodule ⊔ σ'.toSubmodule = (σ ⊔ σ').toSubmodule := by simp
        _ = ⊤ := by simpa using congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top
  by_cases htop : σ = ⊤
  · exact htop
  have hσ'_ne_bot : σ' ≠ ⊥ := by
    intro hbot
    have : σ = ⊤ := by
      simpa [hbot] using hcompl.sup_eq_top
    exact htop this
  let p : τ.IntertwiningMap τ :=
    { toLinearMap := Submodule.IsCompl.projection hcompl_sub
      isIntertwining' := by
        intro g
        ext x
        rcases Submodule.existsUnique_add_of_isCompl hcompl_sub (τ g x) with
          ⟨u, v, huv, huniq⟩
        have hu_mem :
            τ g (Submodule.IsCompl.projection hcompl_sub x) ∈ σ.toSubmodule := by
          exact σ.apply_mem_toSubmodule g (Submodule.IsCompl.projection_apply_mem hcompl_sub x)
        have hv_mem :
            τ g (Submodule.IsCompl.projection hcompl_sub.symm x) ∈ σ'.toSubmodule := by
          exact σ'.apply_mem_toSubmodule g
            (Submodule.IsCompl.projection_apply_mem hcompl_sub.symm x)
        have hsplit :
            ((⟨τ g (Submodule.IsCompl.projection hcompl_sub x), hu_mem⟩ : σ.toSubmodule) : U) +
                (⟨τ g (Submodule.IsCompl.projection hcompl_sub.symm x), hv_mem⟩ :
                  σ'.toSubmodule) =
              τ g x := by
          -- Transport the canonical decomposition of `x` through the `G`-action.
          change
            τ g (Submodule.IsCompl.projection hcompl_sub x) +
                τ g (Submodule.IsCompl.projection hcompl_sub.symm x) =
              τ g x
          rw [← map_add, Submodule.IsCompl.projection_add_projection_eq_self hcompl_sub]
        have hfirst :=
          (huniq
            ⟨τ g (Submodule.IsCompl.projection hcompl_sub x), hu_mem⟩
            ⟨τ g (Submodule.IsCompl.projection hcompl_sub.symm x), hv_mem⟩
            hsplit).1
        have hu :
            (u : U) = Submodule.IsCompl.projection hcompl_sub (τ g x) := by
          -- Projecting the unique decomposition of `τ g x` isolates its `σ`-component.
          have hproj := congrArg (Submodule.IsCompl.projection hcompl_sub) huv
          simpa [LinearMap.map_add,
            (Submodule.IsCompl.projection_eq_self_iff hcompl_sub (u : U)).2 u.property,
            (Submodule.IsCompl.projection_apply_eq_zero_iff hcompl_sub).2 v.property] using
            hproj
        calc
          Submodule.IsCompl.projection hcompl_sub (τ g x) = (u : U) := hu.symm
          _ = τ g (Submodule.IsCompl.projection hcompl_sub x) := by
            exact congrArg Subtype.val hfirst.symm }
  have hp_ne_zero : p ≠ 0 := by
    intro hp
    have hσ_bot : σ = ⊥ := by
      apply Subrepresentation.toSubmodule_injective
      apply bot_unique
      intro x hx
      have hx' : (p : U →ₗ[k] U) x = 0 := by
        simpa [p, hp]
      have hxself : Submodule.IsCompl.projection hcompl_sub x = x := by
        exact (Submodule.IsCompl.projection_eq_self_iff hcompl_sub x).2 hx
      have hxzero : x = 0 := by
        simpa [p, hxself] using hx'
      simpa using hxzero
    exact hσ hσ_bot
  have hp_not_bijective : ¬ Function.Bijective p := by
    intro hpbij
    have hrange : LinearMap.range (p : U →ₗ[k] U) = σ.toSubmodule := by
      simpa [p] using Submodule.IsCompl.projection_range hcompl_sub
    have hσ_top : σ.toSubmodule = ⊤ := by
      rw [← hrange]
      exact LinearMap.range_eq_top.2 hpbij.2
    exact htop (Subrepresentation.toSubmodule_injective hσ_top)
  exact (hp_not_bijective (hbij p hp_ne_zero)).elim
end MackeyIrreducibilityCriterion

end Representation
