import Serre.Chap07.Proposition_7_7_4_1.MackeyDecomposition

noncomputable section

universe u v

namespace Representation

section MackeyIrreducibilityCriterion

open Rep (of)
open CategoryTheory

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G] [NeZero (Nat.card G : k)]
variable {V : Type v} [AddCommGroup V] [Module k V]

local instance instDecidableEqDoubleCosetQuotientMackeyCoordinates (H : Subgroup G) :
    DecidableEq (DoubleCoset.Quotient (H : Set G) H) :=
  Classical.decEq _

/-- Helper for Proposition 7-7.4-1: morphisms out of a representation direct sum are equivalent to
families of morphisms out of the individual summands. -/
noncomputable def directSum_hom_equivPi_local
    {Γ : Type*} [Group Γ]
    {ι : Type*}
    (π : ι → Rep k Γ) (τ : Rep k Γ) :
    (Rep.of (Representation.directSum fun i ↦ (π i).ρ) ⟶ τ) ≃ₗ[k] ∀ i, (π i ⟶ τ) :=
  (Rep.homLinearEquiv _ _) ≪≫ₗ
    (directSum_intertwiningMapEquivPi_local (k := k) (fun i ↦ (π i).ρ) τ.ρ) ≪≫ₗ
      LinearEquiv.piCongrRight fun i ↦ (Rep.homLinearEquiv (π i) τ).symm
/-- Helper for Proposition 7-7.4-1: evaluating the direct-sum decomposition equivalence at one
coordinate simply restricts the original morphism along the corresponding `DirectSum.lof`. -/
theorem directSum_hom_equivPi_local_apply
    {Γ : Type*} [Group Γ]
    {ι : Type*} [DecidableEq ι]
    {π : ι → Rep k Γ} (τ : Rep k Γ)
    (F : Rep.of (Representation.directSum fun i ↦ (π i).ρ) ⟶ τ)
    (i : ι) (x : (π i).V) :
    (((directSum_hom_equivPi_local (k := k) π τ) F i).hom) x =
      F.hom (DirectSum.lof k ι (fun j ↦ (π j).V) i x) := by
  have hDecEq : (Classical.decEq ι) = (inferInstance : DecidableEq ι) := by
    funext a b
    apply Subsingleton.elim
  -- Unfolding the equivalence shows that the `i`-th coordinate map is exactly restriction along
  -- the `i`-th summand inclusion.
  simp [directSum_hom_equivPi_local, directSum_intertwiningMapEquivPi_local, LinearMap.comp_apply]
  rw [show Rep.homEquiv F = F.hom from rfl]
  have harg :
      ((@DirectSum.lof k _ ι (fun j ↦ (π j).V) _ _ (Classical.decEq ι) i) x :
          DirectSum ι (fun j ↦ (π j).V)) =
        ((@DirectSum.lof k _ ι (fun j ↦ (π j).V) _ _ (inferInstance : DecidableEq ι) i) x :
          DirectSum ι (fun j ↦ (π j).V)) := by
    cases hDecEq
    rfl
  rw [harg]
/-- Helper for Proposition 7-7.4-1: at a fixed `ULift`-indexed Mackey summand, Frobenius
reciprocity and the target-side `ULift` equivalence identify the corresponding coordinate space
with the final Mackey intertwining space appearing in the criterion. -/
noncomputable def mackey_coordinate_hom_equiv
    (H : Subgroup G) (ρ : Representation k H V) (s : G) :
    (mackeySummand H H (of ρ) s ⟶ Rep.of (uliftRepresentation (k := k) ρ)) ≃ₗ[k]
      (mackeyTwist H H (of ρ) s ⟶
        Rep.res (mackeySubgroup H H s).subtype (of ρ)) :=
  let ρu : Representation k H (ULift.{u} V) := uliftRepresentation (k := k) ρ
  let φ : mackeySubgroup H H s →* H := (mackeySubgroup H H s).subtype
  let eSummand :
      (mackeySummand H H (of ρ) s ⟶ Rep.of ρu) ≃ₗ[k]
        (mackeySummand H H (of ρu) s ⟶ Rep.of ρu) :=
    homCongrLeft (k := k)
      (A := mackeySummand H H (of ρ) s)
      (B := mackeySummand H H (of ρu) s)
      (C := Rep.of ρu)
      (Rep.mkIso (mackeySummand_ulift_equiv (k := k) H ρ s)).symm
  let eSourceRep :
      (mackeyTwist H H (of ρu) s).ρ.Equiv (mackeyTwist H H (of ρ) s).ρ :=
    by
      -- Conjugation and restriction commute definitionally with the `ULift` carrier replacement.
      simpa [mackeyTwist] using
        (uliftRepresentationEquiv (k := k) ((mackeyTwist H H (of ρ) s).ρ)).symm
  let eTargetRep :
      (Rep.res φ (Rep.of ρu)).ρ.Equiv (Rep.res φ (Rep.of ρ)).ρ :=
    by
      -- Restriction commutes definitionally with the `ULift` carrier replacement.
      simpa using
        (uliftRepresentationEquiv (k := k) ((Rep.res φ (Rep.of ρ)).ρ)).symm
  let eTwistHom :
      (mackeyTwist H H (of ρu) s ⟶ Rep.res φ (Rep.of ρu)) ≃ₗ[k]
        (mackeyTwist H H (of ρ) s ⟶ Rep.res φ (Rep.of ρ)) :=
    (Rep.homLinearEquiv
      (mackeyTwist H H (of ρu) s)
      (Rep.res φ (Rep.of ρu))) ≪≫ₗ
      intertwiningMapCongrLeft (k := k)
        (ρ := (mackeyTwist H H (of ρu) s).ρ)
        (σ := (mackeyTwist H H (of ρ) s).ρ)
        (τ := (Rep.res φ (Rep.of ρu)).ρ)
        eSourceRep ≪≫ₗ
      intertwiningMapCongrRight (k := k)
        (ρ := (mackeyTwist H H (of ρ) s).ρ)
        (σ := (Rep.res φ (Rep.of ρu)).ρ)
        (τ := (Rep.res φ (Rep.of ρ)).ρ)
        eTargetRep ≪≫ₗ
      (Rep.homLinearEquiv
        (mackeyTwist H H (of ρ) s)
        (Rep.res φ (Rep.of ρ))).symm
  let eFrobenius :
      (mackeySummand H H (of ρu) s ⟶ Rep.of ρu) ≃ₗ[k]
        (mackeyTwist H H (of ρu) s ⟶ Rep.res φ (Rep.of ρu)) :=
    Rep.indResHomEquiv φ (mackeyTwist H H (of ρu) s) (Rep.of ρu)
  -- First lift the Mackey summand to the common owner universe, then apply Frobenius, and
  -- finally remove the `ULift` from both the Mackey twist and the restricted target.
  eSummand ≪≫ₗ eFrobenius ≪≫ₗ eTwistHom
/-- Helper for Proposition 7-7.4-1: at a fixed `ULift`-indexed Mackey summand, Frobenius
reciprocity and the target-side `ULift` equivalence identify the corresponding coordinate space
with the final Mackey intertwining space appearing in the criterion. -/
noncomputable def mackey_coordinate_hom_equiv_ulift
    (H : Subgroup G) (ρ : Representation k H V)
    (q : ULift (DoubleCoset.Quotient (H : Set G) H)) :
    (mackeySummand H H (of ρ) (doubleCosetRepresentative H q.down) ⟶
        Rep.of (uliftRepresentation (k := k) ρ)) ≃ₗ[k]
      (mackeyTwist H H (of ρ) (doubleCosetRepresentative H q.down) ⟶
        Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q.down)).subtype (of ρ)) :=
  -- This is the fixed-`s` equivalence specialized to the chosen representative of `q`.
  mackey_coordinate_hom_equiv (k := k) H ρ (doubleCosetRepresentative H q.down)
/-- Helper for Proposition 7-7.4-1: the final Frobenius equivalence evaluates a Mackey block map
on the standard seed generator `IndV.mk ... 1`. -/
theorem mackey_coordinate_hom_equiv_apply
    (H : Subgroup G) (ρ : Representation k H V) (s : G)
    (f : mackeySummand H H (of ρ) s ⟶ Rep.of (uliftRepresentation (k := k) ρ))
    (x : mackeyTwist H H (of ρ) s) :
    (((mackey_coordinate_hom_equiv (k := k) H ρ s) f).hom) x =
      (f.hom
        (Representation.IndV.mk
          (mackeySubgroup H H s).subtype
          ((mackeyTwist H H (of ρ) s).ρ)
          1 x)).down := by
  let φ : mackeySubgroup H H s →* H := (mackeySubgroup H H s).subtype
  let g :
      mackeySummand H H (of (uliftRepresentation (k := k) ρ)) s ⟶
        Rep.of (uliftRepresentation (k := k) ρ) :=
    homCongrLeft (k := k)
      (A := mackeySummand H H (of ρ) s)
      (B := mackeySummand H H (of (uliftRepresentation (k := k) ρ)) s)
      (C := Rep.of (uliftRepresentation (k := k) ρ))
      (Rep.mkIso (mackeySummand_ulift_equiv (k := k) H ρ s)).symm f
  -- Evaluate the Frobenius step on the lifted seed, then remove the `ULift` on both source and
  -- target with the explicit seed formulas.
  calc
    (((mackey_coordinate_hom_equiv (k := k) H ρ s) f).hom) x =
      (((Rep.indResHomEquiv φ
          (mackeyTwist H H (of (uliftRepresentation (k := k) ρ)) s)
          (Rep.of (uliftRepresentation (k := k) ρ))) g).hom (ULift.up x)).down := by
        rfl
    _ = (g.hom
        (Representation.IndV.mk
          (mackeySubgroup H H s).subtype
          ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ)) s).ρ)
          1 (ULift.up x))).down := by
        rw [Rep.indResHomEquiv_apply]
        rfl
    _ = (f.hom
        ((mackeySummand_ulift_equiv (k := k) H ρ s).toLinearEquiv
          (Representation.IndV.mk
            (mackeySubgroup H H s).subtype
            ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ)) s).ρ)
            1 (ULift.up x)))).down := by
        simpa [g] using
          congrArg ULift.down
            (homCongrLeft_apply (k := k)
              (A := mackeySummand H H (of ρ) s)
              (B := mackeySummand H H (of (uliftRepresentation (k := k) ρ)) s)
              (C := Rep.of (uliftRepresentation (k := k) ρ))
              (Rep.mkIso (mackeySummand_ulift_equiv (k := k) H ρ s)).symm
              f
              (Representation.IndV.mk
                (mackeySubgroup H H s).subtype
                ((mackeyTwist H H (of (uliftRepresentation (k := k) ρ)) s).ρ)
                1 (ULift.up x)))
    _ = (f.hom
        (Representation.IndV.mk
          (mackeySubgroup H H s).subtype
          ((mackeyTwist H H (of ρ) s).ρ)
          1 x)).down := by
        rw [mackeySummand_ulift_equiv_apply_mk_one]
/-- Helper for Proposition 7-7.4-1: equal double-coset representatives define canonically
equivalent Mackey coordinate spaces. -/
noncomputable def mackey_coordinate_equiv_of_same_doubleCoset
    (H : Subgroup G) (ρ : Representation k H V)
    {s t : G}
    (hst : DoubleCoset.mk H H s = DoubleCoset.mk H H t) :
    (mackeyTwist H H (of ρ) s ⟶
      Rep.res (mackeySubgroup H H s).subtype (of ρ)) ≃ₗ[k]
      (mackeyTwist H H (of ρ) t ⟶
        Rep.res (mackeySubgroup H H t).subtype (of ρ)) := by
  let i : mackeySummand H H (of ρ) s ≅ mackeySummand H H (of ρ) t :=
    Classical.choice
      (mackeySummand_isomorphic_of_same_doubleCoset
        (k := k) (K := H) (H := H) (W := of ρ) hst)
  -- Transport the Mackey summand first, then use the fixed-`s` Frobenius equivalence on both
  -- sides to identify the two coordinate spaces.
  exact
    (mackey_coordinate_hom_equiv (k := k) H ρ s).symm ≪≫ₗ
      homCongrLeft (k := k)
        (A := mackeySummand H H (of ρ) s)
        (B := mackeySummand H H (of ρ) t)
        (C := Rep.of (uliftRepresentation (k := k) ρ))
        i ≪≫ₗ
      mackey_coordinate_hom_equiv (k := k) H ρ t
/-- Helper for Proposition 7-7.4-1: reindex a dependent family from the `ULift` of the
double-coset quotient back to the plain quotient. -/
noncomputable def ulift_doubleCoset_family_equiv
    (H : Subgroup G)
    (C : DoubleCoset.Quotient (H : Set G) H → Type*)
    [∀ q, AddCommGroup (C q)] [∀ q, Module k (C q)] :
    (∀ q : ULift (DoubleCoset.Quotient (H : Set G) H), C q.down) ≃ₗ[k]
      ∀ q : DoubleCoset.Quotient (H : Set G) H, C q :=
  -- `LinearEquiv.piCongrLeft` is exactly the dependent reindexing equivalence along `ULift.down`.
  LinearEquiv.piCongrLeft k C (Equiv.ofBijective ULift.down ULift.down_bijective)
/-- Helper for Proposition 7-7.4-1: Mackey decomposition and the finite-index Frobenius
equivalences identify `End_G(Ind_H^G ρ)` with the family of Mackey coordinate spaces appearing in
the statement. -/
noncomputable def induced_endomorphism_mackey_coordinate_equiv
    (H : Subgroup G) (ρ : Representation k H V) :
    let τ : Rep k G := Rep.ind H.subtype (of ρ)
    (τ ⟶ τ) ≃ₗ[k]
      ∀ q : DoubleCoset.Quotient (H : Set G) H,
        (mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
          Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ)) :=
  let τ : Rep k G := Rep.ind H.subtype (of ρ)
  let π : ULift (DoubleCoset.Quotient (H : Set G) H) → Rep k H := fun q ↦
    mackeySummand H H (of ρ) (doubleCosetRepresentative H q.down)
  let C : DoubleCoset.Quotient (H : Set G) H → Type _ := fun q ↦
    mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ)
  let eRestricted :
      (τ ⟶ τ) ≃ₗ[k] (Rep.res H.subtype τ ⟶ Rep.of (uliftRepresentation (k := k) ρ)) :=
    induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ
  let eMackey :
      (Rep.res H.subtype τ ⟶ Rep.of (uliftRepresentation (k := k) ρ)) ≃ₗ[k]
        (Rep.of (Representation.directSum fun q ↦ (π q).ρ) ⟶
          Rep.of (uliftRepresentation (k := k) ρ)) :=
    homCongrLeft (k := k)
      (A := Rep.res H.subtype τ)
      (B := Rep.of (Representation.directSum fun q ↦ (π q).ρ))
      (C := Rep.of (uliftRepresentation (k := k) ρ))
      (induced_restriction_mackey_iso (k := k) H ρ)
  let ePi :
      (Rep.of (Representation.directSum fun q ↦ (π q).ρ) ⟶
          Rep.of (uliftRepresentation (k := k) ρ)) ≃ₗ[k]
        ∀ q : ULift (DoubleCoset.Quotient (H : Set G) H),
          (π q ⟶ Rep.of (uliftRepresentation (k := k) ρ)) :=
    directSum_hom_equivPi_local (k := k) π (Rep.of (uliftRepresentation (k := k) ρ))
  let eCoordinate :
      (∀ q : ULift (DoubleCoset.Quotient (H : Set G) H),
          (π q ⟶ Rep.of (uliftRepresentation (k := k) ρ))) ≃ₗ[k]
        ∀ q : ULift (DoubleCoset.Quotient (H : Set G) H), C q.down :=
    LinearEquiv.piCongrRight fun q ↦ mackey_coordinate_hom_equiv_ulift (k := k) H ρ q
  let eReindex :
      (∀ q : ULift (DoubleCoset.Quotient (H : Set G) H), C q.down) ≃ₗ[k]
        ∀ q : DoubleCoset.Quotient (H : Set G) H, C q :=
    ulift_doubleCoset_family_equiv (k := k) H C
  -- Route correction: first pass through the `ULift`-indexed Mackey decomposition, then reindex
  -- the resulting coordinate family back to the plain double-coset quotient.
  eRestricted ≪≫ₗ eMackey ≪≫ₗ ePi ≪≫ₗ eCoordinate ≪≫ₗ eReindex
/-- Helper for Proposition 7-7.4-1: stop the Mackey-coordinate equivalence before the final
Frobenius and `ULift`-reindexing transports, so the direct-sum block components can be computed
at the level of the Mackey summands themselves. -/
noncomputable def induced_endomorphism_mackey_intermediate_equiv
    (H : Subgroup G) (ρ : Representation k H V) :
    let τ : Rep k G := Rep.ind H.subtype (of ρ)
    (τ ⟶ τ) ≃ₗ[k]
      ∀ q : ULift (DoubleCoset.Quotient (H : Set G) H),
        (mackeySummand H H (of ρ) (doubleCosetRepresentative H q.down) ⟶
          Rep.of (uliftRepresentation (k := k) ρ)) := by
  let τ : Rep k G := Rep.ind H.subtype (of ρ)
  let π : ULift (DoubleCoset.Quotient (H : Set G) H) → Rep k H := fun q ↦
    mackeySummand H H (of ρ) (doubleCosetRepresentative H q.down)
  let eRestricted :
      (τ ⟶ τ) ≃ₗ[k] (Rep.res H.subtype τ ⟶ Rep.of (uliftRepresentation (k := k) ρ)) :=
    induced_endomorphism_to_restricted_hom_equiv (k := k) H ρ
  let eMackey :
      (Rep.res H.subtype τ ⟶ Rep.of (uliftRepresentation (k := k) ρ)) ≃ₗ[k]
        (Rep.of (Representation.directSum fun q ↦ (π q).ρ) ⟶
          Rep.of (uliftRepresentation (k := k) ρ)) :=
    homCongrLeft (k := k)
      (A := Rep.res H.subtype τ)
      (B := Rep.of (Representation.directSum fun q ↦ (π q).ρ))
      (C := Rep.of (uliftRepresentation (k := k) ρ))
      (induced_restriction_mackey_iso (k := k) H ρ)
  let ePi :
      (Rep.of (Representation.directSum fun q ↦ (π q).ρ) ⟶
          Rep.of (uliftRepresentation (k := k) ρ)) ≃ₗ[k]
        ∀ q : ULift (DoubleCoset.Quotient (H : Set G) H),
          (π q ⟶ Rep.of (uliftRepresentation (k := k) ρ)) :=
    directSum_hom_equivPi_local (k := k) π (Rep.of (uliftRepresentation (k := k) ρ))
  -- This is the decomposition stage before passing each block through Frobenius reciprocity.
  exact eRestricted ≪≫ₗ eMackey ≪≫ₗ ePi
/-- Helper for Proposition 7-7.4-1: reindexing a `ULift`-indexed coordinate family back to the
plain double-coset quotient evaluates the family at the lifted coordinate. -/
theorem ulift_doubleCoset_family_equiv_apply
    (H : Subgroup G)
    (C : DoubleCoset.Quotient (H : Set G) H → Type*)
    [∀ q, AddCommGroup (C q)] [∀ q, Module k (C q)]
    (f : ∀ q : ULift (DoubleCoset.Quotient (H : Set G) H), C q.down)
    (q : DoubleCoset.Quotient (H : Set G) H) :
    (ulift_doubleCoset_family_equiv (k := k) H C f) q = f ⟨q⟩ := by
  -- The `LinearEquiv.piCongrLeft` reindexing is evaluation at the corresponding lifted index.
  change
    (Equiv.piCongrLeft C (Equiv.ofBijective ULift.down ULift.down_bijective) f) q = f ⟨q⟩
  simpa using
    (Equiv.piCongrLeft_apply_apply
      (P := C)
      (e := Equiv.ofBijective ULift.down ULift.down_bijective)
      f ⟨q⟩)
/-- Helper for Proposition 7-7.4-1: equal double-coset indices determine definitionally equal
Mackey coordinate spaces. -/
theorem singleton_mackey_coordinate_type_eq
    (H : Subgroup G) (ρ : Representation k H V)
    {q q' : DoubleCoset.Quotient (H : Set G) H}
    (h : q' = q) :
    (mackeyTwist H H (of ρ) (doubleCosetRepresentative H q') ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q')).subtype (of ρ)) =
    (mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ)) := by
  subst h
  rfl
/-- Helper for Proposition 7-7.4-1: the Mackey coordinate family concentrated at one double coset
uses that coordinate and is zero elsewhere. -/
noncomputable def singleton_mackey_coordinate_family
    (H : Subgroup G) (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ)) :
    ∀ q' : DoubleCoset.Quotient (H : Set G) H,
      (mackeyTwist H H (of ρ) (doubleCosetRepresentative H q') ⟶
        Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q')).subtype (of ρ)) :=
  fun q' ↦
    if h : q' = q then
      cast (singleton_mackey_coordinate_type_eq (k := k) H ρ h).symm f
    else
      0
/-- Helper for Proposition 7-7.4-1: the singleton Mackey family takes the prescribed value at its
supporting double coset. -/
theorem singleton_mackey_coordinate_family_self
    (H : Subgroup G) (ρ : Representation k H V)
    (q : DoubleCoset.Quotient (H : Set G) H)
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ)) :
    singleton_mackey_coordinate_family (k := k) H ρ q f q = f := by
  -- At the supporting double coset, the `dite` chooses the original coordinate.
  simp [singleton_mackey_coordinate_family]
/-- Helper for Proposition 7-7.4-1: the singleton Mackey family vanishes away from its supporting
double coset. -/
theorem singleton_mackey_coordinate_family_of_ne
    (H : Subgroup G) (ρ : Representation k H V)
    (q q' : DoubleCoset.Quotient (H : Set G) H)
    (hq' : q' ≠ q)
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ)) :
    singleton_mackey_coordinate_family (k := k) H ρ q f q' = 0 := by
  -- Off the supporting double coset, the `dite` selects the zero coordinate.
  simp [singleton_mackey_coordinate_family, hq']
/-- Helper for Proposition 7-7.4-1: a singleton Mackey family supported away from the identity
double coset has zero identity coordinate. -/
theorem singleton_mackey_coordinate_family_identity_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ)) :
    singleton_mackey_coordinate_family (k := k) H ρ q f (DoubleCoset.mk H H (1 : G)) = 0 := by
  -- The identity coordinate is off the singleton support, so the family is zero there.
  exact singleton_mackey_coordinate_family_of_ne (k := k) H ρ q
    (DoubleCoset.mk H H (1 : G)) (by simpa using hq.symm) f
/-- Helper for Proposition 7-7.4-1: if the Mackey coordinate family of `F` is a singleton
supported away from the identity double coset, then the identity coordinate of `F` is zero. -/
theorem singleton_off_identity_identity_coordinate_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f) :
    ((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F)
      (DoubleCoset.mk H H (1 : G)) = 0 := by
  -- Rewriting by the singleton-support hypothesis reduces the claim to the distinguished
  -- identity-coordinate vanishing for singleton families.
  rw [hF]
  exact singleton_mackey_coordinate_family_identity_eq_zero (k := k) H ρ hq f
/-- Helper for Proposition 7-7.4-1: at the identity representative, the Mackey subgroup inside
`H` is all of `H`. -/
theorem mackeySubgroup_self_identity_eq_top
    (H : Subgroup G) :
    mackeySubgroup H H (1 : G) = ⊤ := by
  -- At `s = 1`, the defining condition `x ∈ H ∩ sHs⁻¹` reduces to `x ∈ H`.
  ext x
  simp [mackeySubgroup]
/-- Helper for Proposition 7-7.4-1: restricting `ρ` to the top subgroup of `H` does not change
its self-intertwining space. -/
noncomputable def restrict_top_self_hom_equiv
    (H : Subgroup G) (ρ : Representation k H V) :
    (Rep.res (show (⊤ : Subgroup H) →* H from (⊤ : Subgroup H).subtype) (Rep.of ρ) ⟶
      Rep.res (show (⊤ : Subgroup H) →* H from (⊤ : Subgroup H).subtype) (Rep.of ρ)) ≃ₗ[k]
      (Rep.of ρ ⟶ Rep.of ρ) := by
  let toFun :
      (Rep.res (show (⊤ : Subgroup H) →* H from (⊤ : Subgroup H).subtype) (Rep.of ρ) ⟶
        Rep.res (show (⊤ : Subgroup H) →* H from (⊤ : Subgroup H).subtype) (Rep.of ρ)) →
      (Rep.of ρ ⟶ Rep.of ρ) := fun f ↦
      Rep.ofHom
        { toLinearMap := f.hom
          isIntertwining' := by
            -- The `⊤`-action is the original `H`-action evaluated on the same underlying element.
            intro h
            ext v
            simpa using LinearMap.congr_fun (f.hom.2 ⟨h, by simp⟩) v }
  let invFun :
      (Rep.of ρ ⟶ Rep.of ρ) →
      (Rep.res (show (⊤ : Subgroup H) →* H from (⊤ : Subgroup H).subtype) (Rep.of ρ) ⟶
        Rep.res (show (⊤ : Subgroup H) →* H from (⊤ : Subgroup H).subtype) (Rep.of ρ)) :=
      fun f ↦
      Rep.ofHom
        { toLinearMap := f.hom
          isIntertwining' := by
            -- Conversely, an `H`-equivariant map is already equivariant for the restricted action.
            intro h
            ext v
            simpa using LinearMap.congr_fun (f.hom.2 h.1) v }
  refine
    { toFun := toFun
      invFun := invFun
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro f g
    -- Linearity is inherited from the unchanged underlying linear maps.
    apply Rep.Hom.ext
    ext v
    rfl
  · intro a f
    -- Scalar multiplication is likewise unchanged by the transport.
    apply Rep.Hom.ext
    ext v
    rfl
  · intro f
    -- Both transports keep the same underlying linear map.
    apply Rep.Hom.ext
    ext v
    rfl
  · intro f
    -- The inverse transport is equally definitionally the identity on linear maps.
    apply Rep.Hom.ext
    ext v
    rfl
/-- Helper for Proposition 7-7.4-1: the identity Mackey coordinate is canonically the
self-intertwining space of `ρ`. -/
noncomputable def mackey_identity_coordinate_equiv_self_hom_raw
    (H : Subgroup G) (ρ : Representation k H V) :
    (mackeyTwist H H (of ρ) (1 : G) ⟶
      Rep.res (mackeySubgroup H H (1 : G)).subtype (of ρ)) ≃ₗ[k]
    (Rep.of ρ ⟶ Rep.of ρ) := by
  let S : Subgroup H := mackeySubgroup H H (1 : G)
  let toFun :
      (mackeyTwist H H (of ρ) (1 : G) ⟶ Rep.res S.subtype (of ρ)) →
        (Rep.of ρ ⟶ Rep.of ρ) := fun f ↦
      Rep.ofHom
        { toLinearMap := f.hom
          isIntertwining' := by
            -- At `s = 1`, the Mackey-twist action is the original `H`-action.
            intro h
            ext v
            let hs : S := ⟨h, by simpa [S, mackeySubgroup] using h.2⟩
            simpa [S, mackeyTwist, mackeySubgroup] using
              LinearMap.congr_fun (f.hom.2 hs) v }
  let invFun :
      (Rep.of ρ ⟶ Rep.of ρ) →
        (mackeyTwist H H (of ρ) (1 : G) ⟶ Rep.res S.subtype (of ρ)) := fun f ↦
      Rep.ofHom
        { toLinearMap := f.hom
          isIntertwining' := by
            -- Conversely, an `H`-equivariant map already intertwines the identity Mackey twist.
            intro h
            ext v
            simpa [S, mackeyTwist, mackeySubgroup] using
              LinearMap.congr_fun (f.hom.2 h.1) v }
  refine
    { toFun := toFun
      invFun := invFun
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro f g
    -- Linearity is inherited from the unchanged underlying linear maps.
    apply Rep.Hom.ext
    ext v
    rfl
  · intro a f
    -- Scalar multiplication is likewise inherited from the same linear maps.
    apply Rep.Hom.ext
    ext v
    rfl
  · intro f
    -- Both transports are definitionally the identity on the underlying linear map.
    apply Rep.Hom.ext
    ext v
    rfl
  · intro f
    -- The inverse transport is definitionally the same unchanged linear map.
    apply Rep.Hom.ext
    ext v
    rfl
/-- Helper for Proposition 7-7.4-1: the identity Mackey coordinate is canonically the
self-intertwining space of `ρ`. -/
noncomputable def mackey_identity_coordinate_equiv_self_hom
    (H : Subgroup G) (ρ : Representation k H V) :
    (mackeyTwist H H (of ρ)
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G))) ⟶
      Rep.res
        (mackeySubgroup H H (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).subtype
        (of ρ)) ≃ₗ[k]
    (Rep.of ρ ⟶ Rep.of ρ) := by
  let s : G := doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G))
  let S : Subgroup H := mackeySubgroup H H s
  let toFun :
      (mackeyTwist H H (of ρ) s ⟶ Rep.res S.subtype (of ρ)) →
        (Rep.of ρ ⟶ Rep.of ρ) := fun f ↦
      Rep.ofHom
        { toLinearMap := f.hom
          isIntertwining' := by
            -- The distinguished representative is `1`, so this source action is the original
            -- `H`-action.
            intro h
            ext v
            let hs : S := ⟨h, by
              simpa [S, s, doubleCosetRepresentative_identity, mackeySubgroup] using h.2⟩
            simpa [S, s, doubleCosetRepresentative_identity, mackeyTwist, mackeySubgroup] using
              LinearMap.congr_fun (f.hom.2 hs) v }
  let invFun :
      (Rep.of ρ ⟶ Rep.of ρ) →
        (mackeyTwist H H (of ρ) s ⟶ Rep.res S.subtype (of ρ)) := fun f ↦
      Rep.ofHom
        { toLinearMap := f.hom
          isIntertwining' := by
            -- Conversely, an `H`-equivariant endomorphism already intertwines the identity block.
            intro h
            ext v
            simpa [S, s, doubleCosetRepresentative_identity, mackeyTwist, mackeySubgroup] using
              LinearMap.congr_fun (f.hom.2 h.1) v }
  refine
    { toFun := toFun
      invFun := invFun
      map_add' := ?_
      map_smul' := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro f g
    -- Linearity is inherited from the unchanged underlying linear map.
    apply Rep.Hom.ext
    ext v
    rfl
  · intro a f
    -- Scalar multiplication is likewise inherited from the same underlying map.
    apply Rep.Hom.ext
    ext v
    rfl
  · intro f
    -- Both transports keep the same underlying linear map.
    apply Rep.Hom.ext
    ext v
    rfl
  · intro f
    -- The inverse transport is definitionally the same unchanged linear map.
    apply Rep.Hom.ext
    ext v
    rfl
/-- Helper for Proposition 7-7.4-1: at the identity double coset, the final transport to
`End_H(ρ)` keeps the same underlying linear map. -/
theorem mackey_identity_coordinate_equiv_self_hom_apply
    (H : Subgroup G) (ρ : Representation k H V)
    (f : mackeyTwist H H (of ρ)
        (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G))) ⟶
      Rep.res
        (mackeySubgroup H H
          (doubleCosetRepresentative H (DoubleCoset.mk H H (1 : G)))).subtype
        (of ρ))
    (v : V) :
    (((mackey_identity_coordinate_equiv_self_hom (k := k) H ρ) f).hom) v = f.hom v := by
  -- The direct equivalence keeps the same underlying linear map on the identity Mackey block.
  rfl
/-- Helper for Proposition 7-7.4-1: the identity self-intertwiner extracted from an off-identity
singleton Mackey family is the zero endomorphism of `ρ`. -/
theorem singleton_off_identity_identity_self_hom_eq_zero
    (H : Subgroup G) (ρ : Representation k H V)
    {q : DoubleCoset.Quotient (H : Set G) H}
    (hq : q ≠ DoubleCoset.mk H H (1 : G))
    (f : mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
      Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (hF :
      (induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F =
        singleton_mackey_coordinate_family (k := k) H ρ q f) :
    (mackey_identity_coordinate_equiv_self_hom (k := k) H ρ)
      (((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F)
        (DoubleCoset.mk H H (1 : G))) = 0 := by
  -- The previous lemma shows that the identity coordinate itself is zero, and the identity
  -- coordinate equivalence preserves zero.
  rw [singleton_off_identity_identity_coordinate_eq_zero H ρ hq f F hF]
  simp
/-- Helper for Proposition 7-7.4-1: before evaluating the plain double-coset index `q`, the final
coordinate equivalence is exactly the `ULift` reindexing of the blockwise Frobenius image of the
intermediate Mackey family. -/
theorem induced_endomorphism_coordinate_eq_reindexed
    (H : Subgroup G) (ρ : Representation k H V)
    (F : Rep.ind H.subtype (of ρ) ⟶ Rep.ind H.subtype (of ρ))
    (q : DoubleCoset.Quotient (H : Set G) H) :
    ((induced_endomorphism_mackey_coordinate_equiv (k := k) H ρ) F) q =
      (ulift_doubleCoset_family_equiv (k := k) H
        (fun q ↦
          mackeyTwist H H (of ρ) (doubleCosetRepresentative H q) ⟶
            Rep.res (mackeySubgroup H H (doubleCosetRepresentative H q)).subtype (of ρ))
        ((LinearEquiv.piCongrRight fun q ↦ mackey_coordinate_hom_equiv_ulift (k := k) H ρ q)
          (((induced_endomorphism_mackey_intermediate_equiv (k := k) H ρ) F)))) q := by
  -- This only unfolds the last reindexing stage of the global coordinate equivalence.
  rfl
end MackeyIrreducibilityCriterion

end Representation
