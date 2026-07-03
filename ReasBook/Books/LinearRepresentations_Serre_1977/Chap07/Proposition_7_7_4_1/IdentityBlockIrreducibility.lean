import Serre.Chap07.Proposition_7_7_4_1.FrobeniusCoordinates

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientIdentityBlock (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

/-- Helper for Proposition 7-7.4-1: a bundled representation morphism is zero once all of its
values are zero. -/
theorem rep_hom_eq_zero_of_apply_eq_zero
    {Γ : Type*} [Group Γ]
    {A B : Rep k Γ} (f : A ⟶ B)
    (hzero : ∀ x, f.hom x = 0) :
    f = 0 := by
  -- Equality of bundled morphisms is checked on the underlying linear maps.
  apply Rep.Hom.ext
  ext x
  exact hzero x
/-- Helper for Proposition 7-7.4-1: if a nonzero linear projection vanishes on the image of a
surjective map, then that map cannot be surjective. -/
theorem not_surjective_of_comp_eq_zero
    {A B C : Type*}
    [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C]
    (π : B →ₗ[k] C) (F : A →ₗ[k] B)
    (hπ : π ≠ 0) (hcomp : π.comp F = 0) :
    ¬ Function.Surjective F := by
  intro hsurj
  apply hπ
  ext b
  obtain ⟨a, rfl⟩ := hsurj b
  simpa [LinearMap.comp_apply] using LinearMap.congr_fun hcomp a
/-- Helper for Proposition 7-7.4-1: if a Mackey coordinate family is a singleton supported at `q`,
then every distinct intermediate block already vanishes before the final Frobenius transport. -/
theorem singleton_off_identity_intermediate_block_of_ne
    (H : Subgroup G) (ρ : Representation k H V)
    (q q' : DoubleCoset.Quotient (H : Set G) H)
    (hq' : q' ≠ q)
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f) :
    ((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) ⟨q'⟩ = 0 := by
  -- Apply the blockwise Frobenius equivalence and use that the singleton family vanishes away
  -- from its supporting double coset.
  have hcoord :
      ((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F) q' = 0 := by
    rw [hF]
    exact singleton_mackey_coordinate_family_of_ne (k := k) H ρ q q' hq' f
  apply (mackey_coordinate_hom_equiv
    (k := k) H ρ (doubleCosetRepresentative H q')).injective
  apply Rep.Hom.ext
  ext x
  have hEval := congrArg (fun z ↦ z.hom x) hcoord
  calc
    (Rep.Hom.hom
        ((mackey_coordinate_hom_equiv (k := k) H ρ (doubleCosetRepresentative H q'))
          (((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) ⟨q'⟩))) x =
      (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F) q').hom x := by
        symm
        exact coordinate_eq_intermediate_block_apply (k := k) H ρ F q' x
    _ = 0 := by
        simpa using hEval
    _ =
      (Rep.Hom.hom
        ((mackey_coordinate_hom_equiv (k := k) H ρ (doubleCosetRepresentative H q')) 0)) x := by
        simp
/-- Helper for Proposition 7-7.4-1: a singleton Mackey family supported away from the identity
double coset already has zero identity intermediate block before the last Frobenius transport. -/
theorem singleton_off_identity_identity_intermediate_block_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f) :
    ((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F)
      ⟨DoubleCoset.mk H H (1 : G)⟩ = 0 := by
  have hq1 : DoubleCoset.mk H H (1 : G) ≠ q := by
    intro hEq
    exact hq hEq.symm
  -- Specialize the already-proved off-support vanishing to the distinguished identity block.
  exact singleton_off_identity_intermediate_block_of_ne (k := k) H ρ q
    (DoubleCoset.mk H H (1 : G)) hq1 f F hF
/-- Helper for Proposition 7-7.4-1: project the restricted induced representation onto the
identity Mackey summand by transporting through the Mackey direct-sum decomposition and then
taking the identity direct-sum component. -/
noncomputable def identity_mackey_block_projection
    (H : Subgroup G) (ρ : Representation k H V) :
    Representation.IndV H.subtype ρ →ₗ[k]
      Representation.IndV
        (mackeySubgroup H H
          (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).subtype
        ((mackeyTwist H H (of ρ)
          (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).ρ) :=
  let q1 : ULift (DoubleCoset.Quotient (H : Set G) H) := ⟨DoubleCoset.mk H H (1 : G)⟩
  let M : ULift (DoubleCoset.Quotient (H : Set G) H) → Type _ :=
    fun q ↦ Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)
  let e :
      Representation.IndV H.subtype ρ →ₗ[k]
        DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H)) M :=
    ((induced_restriction_mackey_iso (k := k) H ρ).hom.hom :
      Representation.IndV H.subtype ρ →ₗ[k]
        DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H)) M)
  (DirectSum.component k _ M q1).comp e
/-- Helper for Proposition 7-7.4-1: the identity Mackey-block projector recovers the identity
summand basis vector after transporting it back through the inverse Mackey isomorphism. -/
theorem identity_mackey_block_projection_apply_mackey_lof_identity
    (H : Subgroup G) (ρ : Representation k H V)
    (y : Representation.IndV
      (mackeySubgroup H H
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).subtype
      ((mackeyTwist H H (of ρ)
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).ρ)) :
    identity_mackey_block_projection (k := k) H ρ
      (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom :
          DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
            (fun q ↦
              Representation.IndV
                (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
                ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)) →ₗ[k]
          Representation.IndV H.subtype ρ)
        (DirectSum.lof k _
          (fun q : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
              ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ))
          ⟨DoubleCoset.mk H H (1 : G)⟩ y)) =
      y := by
  -- The source-side Mackey isomorphism sends the chosen identity summand back to a vector whose
  -- identity component is exactly the original basis vector.
  simp [identity_mackey_block_projection]
/-- Helper for Proposition 7-7.4-1: the identity Mackey-block projector kills every off-identity
summand basis vector after transporting it back through the inverse Mackey isomorphism. -/
theorem identity_mackey_block_projection_apply_mackey_lof_of_ne
    (H : Subgroup G) (ρ : Representation k H V)
    (q : ULift (DoubleCoset.Quotient (H : Set G) H))
    (hq : q ≠ ⟨DoubleCoset.mk H H (1 : G)⟩)
    (y : Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)) :
    identity_mackey_block_projection (k := k) H ρ
      (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom :
          DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
            (fun q ↦
              Representation.IndV
                (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
                ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)) →ₗ[k]
          Representation.IndV H.subtype ρ)
        (DirectSum.lof k _
          (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ))
          q y)) =
      0 := by
  -- After re-entering the induced representation from an off-identity summand, the identity
  -- direct-sum component is definitionally zero.
  simp [identity_mackey_block_projection, DirectSum.component.of, hq]
/-- Helper for Proposition 7-7.4-1: the identity Mackey-block projector is surjective, because
the inverse Mackey isomorphism followed by the distinguished `DirectSum.lof` gives an explicit
right inverse. -/
theorem identity_mackey_block_projection_surjective
    (H : Subgroup G) (ρ : Representation k H V) :
    Function.Surjective (identity_mackey_block_projection (k := k) H ρ) := by
  intro y
  let q1 : ULift (DoubleCoset.Quotient (H : Set G) H) := ⟨DoubleCoset.mk H H (1 : G)⟩
  refine ⟨((induced_restriction_mackey_iso (k := k) H ρ).inv.hom :
      DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
        (fun q ↦
          Representation.IndV
            (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
            ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)) →ₗ[k]
      Representation.IndV H.subtype ρ)
      (DirectSum.lof k _
        (fun q : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
          Representation.IndV
            (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
            ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ))
        q1 y), ?_⟩
  -- Evaluate the projector on the explicit right-inverse element coming from the identity summand.
  simpa [q1] using identity_mackey_block_projection_apply_mackey_lof_identity (k := k) H ρ y
/-- Helper for Proposition 7-7.4-1: on the identity Mackey summand, the unit-copy projection is
injective because the unit generator is also a right inverse. -/
theorem identity_mackey_block_unit_projection_injective
    (H : Subgroup G) (ρ : Representation k H V) [NeZero (Nat.card H : k)] :
    Function.Injective
      (inducedIdentityCopyProjection
        (mackeySubgroup H H
          (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G))))
        ((mackeyTwist H H (of ρ)
          (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).ρ)) := by
  let K : Subgroup H :=
    mackeySubgroup H H (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))
  let σ : Representation k K V :=
    (mackeyTwist H H (of ρ)
      (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).ρ
  have hleft :
      (Representation.IndV.mk K.subtype σ 1).comp
          (inducedIdentityCopyProjection K σ) = LinearMap.id := by
    -- The induced representation over the identity Mackey block is generated by `IndV.mk ... 1`,
    -- and the unit-copy projection sends each generator back to its coefficient.
    apply Representation.IndV.hom_ext (φ := K.subtype) (ρ := σ)
    intro h
    ext v
    let hK : K := ⟨h, by
      -- At the identity double coset, every element of `H` lies in the Mackey subgroup.
      simpa [K, doubleCosetRepresentative_identity, mackeySubgroup] using h.2⟩
    calc
      Representation.IndV.mk K.subtype σ 1
          (inducedIdentityCopyProjection K σ
            (Representation.IndV.mk K.subtype σ (h : H) v)) =
        Representation.IndV.mk K.subtype σ 1
          (inducedIdentityCopyProjection K σ
            (Representation.IndV.mk K.subtype σ 1 (σ hK⁻¹ v))) := by
          simpa [hK] using
            congrArg
              (fun z : Representation.IndV K.subtype σ ↦
                Representation.IndV.mk K.subtype σ 1
                  (inducedIdentityCopyProjection K σ z))
              (ind_mk_eq_mk_one_inv (k := k) (θ := σ) hK v)
      _ = Representation.IndV.mk K.subtype σ 1 (σ hK⁻¹ v) := by
          rw [induced_identity_copy_projection_apply_mk_one]
      _ = Representation.IndV.mk K.subtype σ (h : H) v := by
          simpa [hK] using
            (ind_mk_eq_mk_one_inv (k := k) (θ := σ) hK v).symm
  intro x y hxy
  have hx :
      ((Representation.IndV.mk K.subtype σ 1).comp
          (inducedIdentityCopyProjection K σ)) x = x := by
    -- Evaluate the right-inverse identity on `x`.
    simpa [LinearMap.comp_apply] using congrArg (fun f : _ →ₗ[k] _ ↦ f x) hleft
  have hy :
      ((Representation.IndV.mk K.subtype σ 1).comp
          (inducedIdentityCopyProjection K σ)) y = y := by
    -- The same right-inverse identity also evaluates on `y`.
    simpa [LinearMap.comp_apply] using congrArg (fun f : _ →ₗ[k] _ ↦ f y) hleft
  have hmk :
      (Representation.IndV.mk K.subtype σ 1)
        ((inducedIdentityCopyProjection K σ) x) =
      (Representation.IndV.mk K.subtype σ 1)
        ((inducedIdentityCopyProjection K σ) y) := by
    -- Apply the common right inverse map to the equality of projections.
    exact congrArg (Representation.IndV.mk K.subtype σ 1) hxy
  -- Apply the common right inverse to the assumed equality of projections.
  calc
    x = ((Representation.IndV.mk K.subtype σ 1).comp
        (inducedIdentityCopyProjection K σ)) x := hx.symm
    _ = (Representation.IndV.mk K.subtype σ 1)
        ((inducedIdentityCopyProjection K σ) y) := by
          simpa [LinearMap.comp_apply] using hmk
    _ = ((Representation.IndV.mk K.subtype σ 1).comp
        (inducedIdentityCopyProjection K σ)) y := by
          rfl
    _ = y := by
          change ((Representation.IndV.mk K.subtype σ 1).comp
              (inducedIdentityCopyProjection K σ)) y = y
          exact hy
/-- Helper for Proposition 7-7.4-1: a singleton Mackey family with nonzero supporting coordinate
produces a nonzero induced endomorphism under the global coordinate equivalence. -/
theorem induced_endomorphism_ne_zero_of_singleton_coordinate_nonzero
    (H : Subgroup G) (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f)
    (hf : f ≠ 0) :
    F ≠ 0 := by
  intro hzero
  have hcoord_zero :
      ((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F) q = 0 := by
    simpa [hzero]
  have hcoord_self :
      ((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F) q = f := by
    simpa [singleton_mackey_coordinate_family_self] using congrFun hF q
  exact hf (hcoord_self.symm.trans hcoord_zero)
/-- Helper for Proposition 7-7.4-1: if the induced representation is irreducible, then any
endomorphism whose Mackey coordinates are a singleton family with nonzero support is bijective. -/
theorem bijective_of_singleton_coordinate_nonzero_of_ind_isIrreducible
    (H : Subgroup G) (ρ : Representation k H V)
    (hInd : (Rep.ind H.subtype (of ρ)).ρ.IsIrreducible)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f)
    (hf : f ≠ 0) :
    Function.Bijective F.hom := by
  letI : (Rep.ind H.subtype (of ρ)).ρ.IsIrreducible := hInd
  have hF_ne : F ≠ 0 :=
    induced_endomorphism_ne_zero_of_singleton_coordinate_nonzero (k := k) H ρ q f F hF hf
  have hF_hom_ne : F.hom ≠ 0 := by
    intro hzero
    exact hF_ne (Rep.hom_ext hzero)
  exact
    (Representation.IsIrreducible.bijective_or_eq_zero
      (ρ := (Rep.ind H.subtype (of ρ)).ρ)
      (σ := (Rep.ind H.subtype (of ρ)).ρ)
      (f := F.hom)).resolve_right hF_hom_ne
/-- Helper for Proposition 7-7.4-1: a nonzero self-intertwiner of `ρ` induces a nonzero
endomorphism of `Ind_H^G(ρ)`. -/
theorem indMap_ne_zero_of_ne_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {g : Rep.of ρ ⟶ Rep.of ρ} (hg : g ≠ 0) :
    Rep.indMap H.subtype g ≠ 0 := by
  intro hind_zero
  apply hg
  ext v
  have hzero :
      inducedIdentityCopyProjection H ρ
          ((Rep.indMap H.subtype g).hom (Representation.IndV.mk H.subtype ρ 1 v)) = 0 := by
    simpa using
      congrArg
        (fun f : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ) ↦
          inducedIdentityCopyProjection H ρ
            (f.hom (Representation.IndV.mk H.subtype ρ 1 v)))
        hind_zero
  have happly :
      (Rep.indMap H.subtype g).hom (Representation.IndV.mk H.subtype ρ 1 v) =
        Representation.IndV.mk H.subtype ρ 1 (g.hom v) := by
    simp [Rep.indMap]
  calc
    g.hom v = inducedIdentityCopyProjection H ρ
          (Representation.IndV.mk H.subtype ρ 1 (g.hom v)) := by
          symm
          exact induced_identity_copy_projection_apply_mk_one H ρ (g.hom v)
    _ = inducedIdentityCopyProjection H ρ
          ((Rep.indMap H.subtype g).hom (Representation.IndV.mk H.subtype ρ 1 v)) := by
          rw [happly]
    _ = 0 := hzero
/-- Helper for Proposition 7-7.4-1: induction on morphisms is faithful because the unit-copy
projection recovers the original map on `IndV.mk ... 1`. -/
theorem indMap_injective
    (H : Subgroup G) (ρ : Representation k H V) :
    Function.Injective (fun g : Rep.of ρ ⟶ Rep.of ρ ↦ Rep.indMap H.subtype g) := by
  intro g₁ g₂ hEq
  apply Rep.Hom.ext
  ext v
  have hEval := congrArg
      (fun F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ) ↦
        inducedIdentityCopyProjection H ρ
          (F.hom (Representation.IndV.mk H.subtype ρ 1 v)))
      hEq
  calc
    g₁.hom v = inducedIdentityCopyProjection H ρ
        (Representation.IndV.mk H.subtype ρ 1 (g₁.hom v)) := by
          symm
          exact induced_identity_copy_projection_apply_mk_one H ρ (g₁.hom v)
    _ = inducedIdentityCopyProjection H ρ
        ((Rep.indMap H.subtype g₁).hom (Representation.IndV.mk H.subtype ρ 1 v)) := by
          simp [Rep.indMap]
    _ = inducedIdentityCopyProjection H ρ
        ((Rep.indMap H.subtype g₂).hom (Representation.IndV.mk H.subtype ρ 1 v)) := hEval
    _ = inducedIdentityCopyProjection H ρ
        (Representation.IndV.mk H.subtype ρ 1 (g₂.hom v)) := by
          simp [Rep.indMap]
    _ = g₂.hom v := induced_identity_copy_projection_apply_mk_one H ρ (g₂.hom v)
/-- Helper for Proposition 7-7.4-1: induction preserves and reflects bijectivity for
self-intertwiners of `ρ`. -/
theorem induced_map_bijective_iff_self_hom_bijective
    (H : Subgroup G) (ρ : Representation k H V) (g : Rep.of ρ ⟶ Rep.of ρ) :
    Function.Bijective (Rep.indMap H.subtype g).hom ↔ Function.Bijective g.hom := by
  constructor
  · intro hInd
    constructor
    · intro x y hxy
      -- Injectivity descends along the unit generator `IndV.mk ... 1`.
      apply induced_unit_generator_injective H ρ
      apply hInd.1
      simpa [Rep.indMap] using congrArg (Representation.IndV.mk H.subtype ρ 1) hxy
    · intro y
      -- Surjectivity descends by projecting a preimage of the unit generator back to `ρ`.
      obtain ⟨z, hz⟩ := hInd.2 (Representation.IndV.mk H.subtype ρ 1 y)
      refine ⟨inducedIdentityCopyProjection H ρ z, ?_⟩
      calc
        g.hom (inducedIdentityCopyProjection H ρ z) =
            inducedIdentityCopyProjection H ρ ((Rep.indMap H.subtype g).hom z) := by
              symm
              simpa [LinearMap.comp_apply] using
                LinearMap.congr_fun (induced_identity_copy_projection_indMap H ρ g) z
        _ = inducedIdentityCopyProjection H ρ (Representation.IndV.mk H.subtype ρ 1 y) := by
              simpa [hz]
        _ = y := induced_identity_copy_projection_apply_mk_one H ρ y
  · intro hg
    -- A bijective intertwiner of `ρ` upgrades to an equivariant linear equivalence, and induction
    -- preserves that equivalence.
    let eg : ρ.Equiv ρ :=
      Representation.Equiv.mk
        (LinearEquiv.ofBijective g.hom hg)
        (by
          intro h
          ext v
          exact LinearMap.congr_fun (g.hom.2 h) v)
    let eind :
        (Rep.ind H.subtype (Rep.of ρ)).ρ.Equiv (Rep.ind H.subtype (Rep.of ρ)).ρ :=
      inducedRepresentationEquiv (k := k) H eg
    have hind :
        (eind.toLinearEquiv : Representation.IndV H.subtype ρ ≃ₗ[k]
          Representation.IndV H.subtype ρ).toLinearMap =
          (Rep.indMap H.subtype g).hom := by
      refine Representation.IndV.hom_ext (φ := H.subtype) (ρ := ρ) ?_
      intro h
      ext v
      rfl
    simpa [hind] using eind.toLinearEquiv.bijective
/-- Helper for Proposition 7-7.4-1: an irreducible representation has a nontrivial carrier. -/
theorem irreducible_nontrivial
    {Γ : Type*} [Group Γ]
    {U : Type*} [AddCommGroup U] [Module k U]
    (τ : Representation k Γ U) [τ.IsIrreducible] : Nontrivial U := by
  classical
  -- If the carrier were trivial, the zero and whole subrepresentations would coincide.
  by_contra hU
  letI : Subsingleton U := not_nontrivial_iff_subsingleton.mp hU
  have hbot_top : (⊥ : Subrepresentation τ) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  exact bot_ne_top hbot_top
/-- Helper for Proposition 7-7.4-1: the cardinal of any subgroup remains nonzero in the base
field whenever the ambient finite group cardinal does. -/
theorem subgroup_card_ne_zero
    {Γ : Type*} [Group Γ] [Finite Γ] [NeZero (Nat.card Γ : k)]
    (K : Subgroup Γ) : NeZero (Nat.card K : k) := by
  refine ⟨?_⟩
  intro hcardK
  obtain ⟨n, hn⟩ := Subgroup.card_subgroup_dvd_card K
  have hcardΓ' : (Nat.card Γ : k) = ((Nat.card K * n : ℕ) : k) := by
    exact congrArg (fun m : ℕ ↦ (m : k)) hn
  have hcardΓ : (Nat.card Γ : k) = (Nat.card K : k) * (n : k) := by
    simpa using hcardΓ'
  have hzeroΓ : (Nat.card Γ : k) = 0 := by
    rw [hcardΓ, hcardK, zero_mul]
  exact NeZero.ne (Nat.card Γ : k) hzeroΓ
/-- Helper for Proposition 7-7.4-1: if `ρ` is irreducible, then the identity Mackey block is
nontrivial, so the canonical projection onto that block is a nonzero linear map. -/
theorem identity_mackey_block_projection_ne_zero
    (H : Subgroup G) (ρ : Representation k H V) [ρ.IsIrreducible] :
    identity_mackey_block_projection (k := k) H ρ ≠ 0 := by
  letI : Nontrivial V := irreducible_nontrivial (k := k) ρ
  letI : NeZero (Nat.card H : k) := subgroup_card_ne_zero (k := k) H
  letI :
      NeZero
        (Nat.card
          (mackeySubgroup H H
            (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))) : k) :=
    subgroup_card_ne_zero (k := k)
      (mackeySubgroup H H
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G))))
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let q1 : ULift (DoubleCoset.Quotient (H : Set G) H) := ⟨DoubleCoset.mk H H (1 : G)⟩
  let y : Representation.IndV
      (mackeySubgroup H H
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).subtype
      ((mackeyTwist H H (of ρ)
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).ρ) :=
    Representation.IndV.mk
      (mackeySubgroup H H
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).subtype
      ((mackeyTwist H H (of ρ)
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).ρ)
      1 v
  have hy : y ≠ 0 := by
    -- The unit generator in the identity Mackey summand detects the chosen nonzero vector `v`.
    intro hy0
    apply hv
    have hy0' :
        Representation.IndV.mk
            (mackeySubgroup H H
              (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).subtype
            ((mackeyTwist H H (of ρ)
              (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).ρ)
            1 v =
          Representation.IndV.mk
            (mackeySubgroup H H
              (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).subtype
            ((mackeyTwist H H (of ρ)
              (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).ρ)
            1 (0 : V) := by
      simpa [y] using hy0
    exact induced_unit_generator_injective
      (H := mackeySubgroup H H
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G))))
      (ρ := (mackeyTwist H H (of ρ)
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).ρ)
      hy0'
  intro hπ
  have hEval := congrArg
      (fun f ↦
        f (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom :
          DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
            (fun q ↦
              Representation.IndV
                (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
                ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ)) →ₗ[k]
          Representation.IndV H.subtype ρ)
          (DirectSum.lof k _
            (fun q : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
              Representation.IndV
                (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype
                ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down)).ρ))
            q1 y)))
      hπ
  -- Transport the identity summand witness back through the Mackey isomorphism and evaluate the
  -- projection there; the direct-sum component recovers exactly the chosen vector `y`.
  apply hy
  simpa [identity_mackey_block_projection, q1, y] using hEval
/-- Helper for Proposition 7-7.4-1: once the composition with the identity Mackey-block
projection is zero, surjectivity of the underlying induced endomorphism is impossible. -/
theorem not_surjective_of_identity_mackey_block_projection_comp_eq_zero
    (H : Subgroup G) (ρ : Representation k H V) [ρ.IsIrreducible]
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hcomp :
      identity_mackey_block_projection (k := k) H ρ ∘ₗ
        (F.hom : Representation.IndV H.subtype ρ →ₗ[k] Representation.IndV H.subtype ρ) = 0) :
    ¬ Function.Surjective F.hom := by
  -- The identity Mackey-block projector is a nonzero map on an irreducible source block, so a
  -- zero composite with `F` contradicts surjectivity.
  exact not_surjective_of_comp_eq_zero
    (identity_mackey_block_projection (k := k) H ρ)
    (F.hom : Representation.IndV H.subtype ρ →ₗ[k] Representation.IndV H.subtype ρ)
    (identity_mackey_block_projection_ne_zero (k := k) H ρ)
    hcomp
/-- Helper for Proposition 7-7.4-1: once the identity Mackey-block projection annihilates an
induced endomorphism, that endomorphism cannot be bijective. -/
theorem not_bijective_of_identity_mackey_block_projection_comp_eq_zero
    (H : Subgroup G) (ρ : Representation k H V) [ρ.IsIrreducible]
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hcomp :
      identity_mackey_block_projection (k := k) H ρ ∘ₗ
        (F.hom : Representation.IndV H.subtype ρ →ₗ[k] Representation.IndV H.subtype ρ) = 0) :
    ¬ Function.Bijective F.hom := by
  -- The previous projector criterion already rules out surjectivity, hence bijectivity as well.
  intro hbij
  exact
    not_surjective_of_identity_mackey_block_projection_comp_eq_zero (k := k) H ρ F hcomp hbij.2
/-- Helper for Proposition 7-7.4-1: the unit-copy projection from `Ind_H^G(ρ)` is nonzero as soon
as `ρ` is irreducible. -/
theorem induced_identity_copy_projection_ne_zero
    (H : Subgroup G) (ρ : Representation k H V) [ρ.IsIrreducible] :
    inducedIdentityCopyProjection H ρ ≠ 0 := by
  letI : Nontrivial V := irreducible_nontrivial (k := k) ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  intro hzero
  have hEval :
      inducedIdentityCopyProjection H ρ
        (Representation.IndV.mk H.subtype ρ 1 v) = 0 := by
    simpa using congrArg
      (fun f : Representation.IndV H.subtype ρ →ₗ[k] V ↦
        f (Representation.IndV.mk H.subtype ρ 1 v))
      hzero
  apply hv
  calc
    v = inducedIdentityCopyProjection H ρ (Representation.IndV.mk H.subtype ρ 1 v) := by
          symm
          exact induced_identity_copy_projection_apply_mk_one H ρ v
    _ = 0 := hEval
/-- Helper for Proposition 7-7.4-1: an off-identity singleton Mackey family makes the extracted
identity self-intertwiner vanish pointwise on every vector of `ρ`. -/
theorem singleton_off_identity_identity_self_hom_apply_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f) :
    ∀ v : V,
      (((mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
          (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F)
            (DoubleCoset.mk H H (1 : G)))).hom) v = 0 := by
  -- First collapse the identity coordinate to the zero self-hom, then evaluate at `v`.
  intro v
  have hzero :
      (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
        (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F)
          (DoubleCoset.mk H H (1 : G))) = 0 := by
    exact singleton_off_identity_identity_self_hom_eq_zero H ρ hq f F hF
  simpa using congrArg (fun z : Rep.of ρ ⟶ Rep.of ρ ↦ z.hom v) hzero
/-- Helper for Proposition 7-7.4-1: a Mackey singleton supported away from the identity double
coset cannot come from a bijective induced endomorphism. -/
theorem linearMap_eq_zero_of_comp_induced_restriction_mackey_iso_inv_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {W : Type*} [AddCommGroup W] [Module k W]
    (L : Representation.IndV H.subtype ρ →ₗ[k] W)
    (hL :
      L.comp
          (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom.toLinearMap :
              _ →ₗ[k] Representation.IndV H.subtype ρ)) = 0) :
    L = 0 := by
  have hIso :
      ((induced_restriction_mackey_iso (k := k) H ρ).inv.hom.toLinearMap).comp
          ((induced_restriction_mackey_iso (k := k) H ρ).hom.hom.toLinearMap) =
        LinearMap.id := by
    ext x
    -- The forward and inverse Mackey isomorphisms cancel before forgetting to linear maps.
    simpa [LinearMap.comp_apply] using
      congrArg
        (fun f : Rep.res H.subtype (Rep.ind H.subtype (of ρ)) ⟶
            Rep.res H.subtype (Rep.ind H.subtype (of ρ)) ↦
          f.hom x)
        ((induced_restriction_mackey_iso (k := k) H ρ).hom_inv_id)
  have hComp := congrArg
      (fun T ↦ T.comp ((induced_restriction_mackey_iso (k := k) H ρ).hom.hom.toLinearMap :
        Representation.IndV H.subtype ρ →ₗ[k] _))
      hL
  -- Precomposing with the inverse Mackey isomorphism already tests `L` on a spanning family,
  -- because composing back with the forward isomorphism recovers the identity.
  simpa [LinearMap.comp_assoc, hIso] using hComp
/-- Helper for Proposition 7-7.4-1: if the Mackey coordinate family of `F` is supported away from
the identity double coset, then the restricted Frobenius morphism already vanishes on every
identity-summand generator transported back through the inverse Mackey isomorphism. -/
theorem singleton_off_identity_restricted_hom_apply_lof_identity_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f)
    (y : Representation.IndV
      (mackeySubgroup H H
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).subtype
      ((mackeyTwist H H (of ρ)
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).ρ)) :
    ((((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom)
      (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom :
          DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
            (fun q' ↦
              Representation.IndV
                (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
                ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ)) →ₗ[k]
          Representation.IndV H.subtype ρ)
        (DirectSum.lof k _
          (fun q' : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
              ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ))
          ⟨DoubleCoset.mk H H (1 : G)⟩ y))).down = 0 := by
  let q1 : ULift (DoubleCoset.Quotient (H : Set G) H) := ⟨DoubleCoset.mk H H (1 : G)⟩
  let M : ULift (DoubleCoset.Quotient (H : Set G) H) → Type _ :=
    fun q' ↦ Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ)
  have hblock :
      ((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) q1 = 0 := by
    -- The identity intermediate block is off the singleton support, so it already vanishes.
    simpa [q1] using
      singleton_off_identity_identity_intermediate_block_eq_zero (k := k) H ρ hq f F hF
  have hEval :
      ((((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) q1).hom y).down = 0 := by
    -- Evaluate the zero block morphism on the chosen identity-summand vector.
    simpa using congrArg (fun T ↦ (T.hom y).down) hblock
  calc
    ((((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom)
        (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom :
            DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H)) M →ₗ[k]
              Representation.IndV H.subtype ρ)
          (DirectSum.lof k _ M q1 y))).down =
      ((((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) q1).hom y).down := by
        -- Read the restricted Frobenius image through the identity Mackey block of the direct sum.
        symm
        simpa [q1, M] using
          intermediate_block_apply_eq_restricted_hom_apply (k := k) H ρ F q1 y
    _ = 0 := hEval
/-- Helper for Proposition 7-7.4-1: if the Mackey coordinate family of `F` is supported at `q`,
then every other transported `DirectSum.lof` generator already lands in the kernel of the
restricted Frobenius morphism. -/
theorem singleton_off_identity_restricted_hom_apply_lof_of_ne_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f)
    (q' : ULift (DoubleCoset.Quotient (H : Set G) H))
    (hq' : q'.down ≠ q)
    (y : Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ)) :
    ((((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom)
      (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom :
          DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
            (fun r ↦
              Representation.IndV
                (mackeySubgroup H H (doubleCosetRepresentative H r.down)).subtype
                ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H r.down)).ρ)) →ₗ[k]
          Representation.IndV H.subtype ρ)
        (DirectSum.lof k _
          (fun r : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H r.down)).subtype
              ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H r.down)).ρ))
          q' y))).down = 0 := by
  let M : ULift (DoubleCoset.Quotient (H : Set G) H) → Type _ :=
    fun r ↦ Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H r.down)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H r.down)).ρ)
  have hblock :
      ((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) q' = 0 := by
    -- Every intermediate block away from the singleton support is already zero.
    exact singleton_off_identity_intermediate_block_of_ne (k := k) H ρ q q'.down hq' f F hF
  have hEval :
      ((((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) q').hom y).down = 0 := by
    -- Evaluate the zero block morphism on the chosen off-support Mackey vector.
    simpa using congrArg (fun T ↦ (T.hom y).down) hblock
  calc
    ((((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom)
        (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom :
            DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H)) M →ₗ[k]
              Representation.IndV H.subtype ρ)
          (DirectSum.lof k _ M q' y))).down =
      ((((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F) q').hom y).down := by
        -- The off-support Mackey block is read by the same transport formula as the identity block.
        symm
        simpa [M] using
          intermediate_block_apply_eq_restricted_hom_apply (k := k) H ρ F q' y
    _ = 0 := hEval
/-- Helper for Proposition 7-7.4-1: an off-identity singleton Mackey family makes the restricted
Frobenius morphism vanish on any transported `DirectSum.lof` generator that either lies in the
identity summand or away from the singleton support. -/
theorem singleton_off_identity_restricted_hom_apply_lof_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f)
    (q' : ULift (DoubleCoset.Quotient (H : Set G) H))
    (hq' : q'.down = DoubleCoset.mk H H (1 : G) ∨ q'.down ≠ q)
    (y : Representation.IndV
      (mackeySubgroup H H (doubleCosetRepresentative H q'.down)).subtype
      ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H q'.down)).ρ)) :
    ((((induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ) F).hom)
      (((induced_restriction_mackey_iso (k := k) H ρ).inv.hom :
          DirectSum (ULift (DoubleCoset.Quotient (H : Set G) H))
            (fun r ↦
              Representation.IndV
                (mackeySubgroup H H (doubleCosetRepresentative H r.down)).subtype
                ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H r.down)).ρ)) →ₗ[k]
          Representation.IndV H.subtype ρ)
        (DirectSum.lof k _
          (fun r : ULift (DoubleCoset.Quotient (H : Set G) H) ↦
            Representation.IndV
              (mackeySubgroup H H (doubleCosetRepresentative H r.down)).subtype
              ((mackeyTwist H H (of ρ) (doubleCosetRepresentative H r.down)).ρ))
          q' y))).down = 0 := by
  rcases hq' with hq' | hq'
  · have hq'_lift : q' = ⟨DoubleCoset.mk H H (1 : G)⟩ := by
      cases q'
      simp_all
    -- The identity branch is exactly the previously isolated identity-summand vanishing.
    subst hq'_lift
    simpa using
      singleton_off_identity_restricted_hom_apply_lof_identity_eq_zero
        (k := k) H ρ hq f F hF y
  · -- Every nonidentity branch is handled by the off-support vanishing lemma with support `q`.
    exact singleton_off_identity_restricted_hom_apply_lof_of_ne_eq_zero
      (k := k) H ρ hq f F hF q' hq' y
/-- Helper for Proposition 7-7.4-1: if `Ind_H^G(ρ)` is irreducible, then `ρ` is irreducible. -/
theorem isIrreducible_of_ind_isIrreducible
    (H : Subgroup G) (ρ : Representation k H V)
    (hInd : (Rep.ind H.subtype (of ρ)).ρ.IsIrreducible) :
    ρ.IsIrreducible := by
  letI : (Rep.ind H.subtype (of ρ)).ρ.IsIrreducible := hInd
  -- The unit-coset copy embeds `ρ` faithfully into the induced representation.
  letI : Nontrivial (Representation.IndV H.subtype ρ) :=
    irreducible_nontrivial ((Rep.ind H.subtype (of ρ)).ρ)
  letI : Nontrivial V := by
    have hIdInd_ne : (𝟙 (Rep.ind H.subtype (of ρ))) ≠ 0 := by
      intro hzero
      obtain ⟨x, hx⟩ := exists_ne (0 : Representation.IndV H.subtype ρ)
      exact hx <| by
        simpa using congrArg
          (fun f : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ) ↦ f.hom x)
          hzero
    have hIdρ_ne : (𝟙 (Rep.of ρ)) ≠ 0 := by
      intro hzero
      have hmap_id :
          Rep.indMap H.subtype (𝟙 (Rep.of ρ)) = 𝟙 (Rep.ind H.subtype (of ρ)) := by
        simpa using (Rep.indFunctor (k := k) H.subtype).map_id (Rep.of ρ)
      have hmap_zero :
          Rep.indMap H.subtype (0 : Rep.of ρ ⟶ Rep.of ρ) = 0 := by
        ext h v
        simp [Rep.indMap]
      apply hIdInd_ne
      calc
        𝟙 (Rep.ind H.subtype (of ρ)) = Rep.indMap H.subtype (𝟙 (Rep.of ρ)) := hmap_id.symm
        _ = Rep.indMap H.subtype 0 := by rw [hzero]
        _ = 0 := hmap_zero
    by_contra hV
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    exact hIdρ_ne <| by
      ext v
      exact Subsingleton.elim _ _
  letI : NeZero (Nat.card H : k) := by
    refine ⟨?_⟩
    intro hcardH
    obtain ⟨n, hn⟩ := Subgroup.card_subgroup_dvd_card H
    have hcardG' : (Nat.card G : k) = ((Nat.card H * n : ℕ) : k) := by
      exact congrArg (fun m : ℕ ↦ (m : k)) hn
    have hcardG : (Nat.card G : k) = (Nat.card H : k) * (n : k) := by
      simpa using hcardG'
    have hzeroG : (Nat.card G : k) = 0 := by
      rw [hcardG, hcardH, zero_mul]
    exact NeZero.ne (Nat.card G : k) hzeroG
  -- Every nonzero endomorphism of `ρ` induces a nonzero global endomorphism, so Schur on
  -- `Ind_H^G(ρ)` forces bijectivity back on `ρ`.
  refine isIrreducible_of_semisimple_and_nonzero_endomorphisms_bijective (τ := ρ) ?_
  intro g hg
  have hIndg_ne : Rep.indMap H.subtype (Rep.ofHom g) ≠ 0 :=
    indMap_ne_zero_of_ne_zero (H := H) (ρ := ρ) (g := Rep.ofHom g) <| by
      intro hzero
      exact hg <| Rep.Hom.ext_iff.mp hzero
  have hIndg_hom_ne : (Rep.indMap H.subtype (Rep.ofHom g)).hom ≠ 0 := by
    intro hzero
    exact hIndg_ne <| Rep.hom_ext hzero
  have hbijInd : Function.Bijective (Rep.indMap H.subtype (Rep.ofHom g)).hom := by
    exact
      (Representation.IsIrreducible.bijective_or_eq_zero
        (ρ := (Rep.ind H.subtype (of ρ)).ρ)
        (σ := (Rep.ind H.subtype (of ρ)).ρ)
        (f := (Rep.indMap H.subtype (Rep.ofHom g)).hom)).resolve_right hIndg_hom_ne
  simpa using
    (induced_map_bijective_iff_self_hom_bijective H ρ (Rep.ofHom g)).1 hbijInd

-- Source/core/bridge triage:
-- * source-facing: Mackey's irreducibility criterion for the induced representation `Ind_H^G(ρ)`.
-- * core/canonical: the bundled owner operations are `Rep.ind`, `Rep.res`, and the Chapter 2
--   irreducibility owner `Representation.IsIrreducible` on the underlying representation.
-- * bridge/view: `mackeyTwist` from Proposition `7-7.3-1` supplies the subgroup-conjugation view
--   needed to phrase the Mackey summands without introducing a parallel wrapper API here.
-- * primitive data: a subgroup `H ≤ G` and an `H`-representation `ρ`.
-- * derived API: irreducibility of the induced owner `Rep.ind H.subtype (Rep.of ρ)` and the
--   Mackey disjointness condition expressed by the vanishing of every canonical intertwining map
--   from the twist to the restricted owner.

-- Proof sketch: combine the finite-index Frobenius adjunction with Mackey's decomposition of the
-- restriction of `Ind_H^G(ρ)` to `H`, so that global endomorphisms of `Rep.ind H.subtype (of ρ)`
-- are identified with the family of Mackey coordinates indexed by `H \ G / H`. The identity
-- double-coset coordinate is the self-intertwining space of `ρ`, while the off-identity
-- coordinates are exactly the morphism spaces
-- `mackeyTwist H H (Rep.of ρ) s ⟶ Rep.res (mackeySubgroup H H s).subtype (Rep.of ρ)`.
-- The remaining general-field step is to show that bijectivity of a global endomorphism is
-- controlled precisely by its identity Mackey coordinate, using the Chapter 7.1 identity-copy
-- inducedness machinery.
end MackeyIrreducibilityCriterion

end Representation
