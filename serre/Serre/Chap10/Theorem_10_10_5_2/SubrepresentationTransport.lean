import Mathlib
import Serre.Chap01.Theorem_1_1_4_2
import Serre.Chap03.Definition_3_3_3_1
import Serre.Chap03.Exercise_3_3_3_6
import Serre.Chap07.Proposition_7_7_1_3
import Serre.Chap07.Remark_7_7_1_4
import Serre.Chap08.Definition_8_8_3_2
import Serre.Chap08.Exercise_8_8_3_9
import Serre.Chap10.Definition_10_10_1_3
import Serre.Chap10.MonomialCharacter

noncomputable section

namespace Representation

open CategoryTheory Rep
open scoped Representation SubgroupInduction
open scoped BigOperators Pointwise

section

variable {G : Type} [Group G] [Finite G]

/-- A subgroup of a finite group is finite. -/
local instance theorem_10_10_5_2_subrep_transport_fintype_of_finite : Fintype G := Fintype.ofFinite G

/-- A subgroup of a finite group is finite. -/
local instance theorem_10_10_5_2_subrep_transport_subgroup_fintype_of_finite (H : Subgroup G) :
    Fintype H := Fintype.ofFinite H
/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the underlying
`ℂ`-subspace obtained by transporting an `A`-stable subspace through the operator `ρ g`. -/
def transportedSubrepresentationCarrier_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (A : Subgroup Q)
    (W : Subrepresentation (ρ.comp A.subtype)) (g : Q) :
    Submodule ℂ V :=
  W.toSubmodule.map (ρ g)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: normality of `A`
makes the `ρ g`-image of an `A`-stable subspace stable under the restricted `A`-action again. -/
theorem transportedSubrepresentationCarrier_apply_mem_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (A : Subgroup Q) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : Q) (a : A)
    {v : V} (hv : v ∈ transportedSubrepresentationCarrier_local ρ A W g) :
    ρ a v ∈ transportedSubrepresentationCarrier_local ρ A W g := by
  -- Write `v` as `ρ g w` with `w ∈ W`, then move the `A`-action across `ρ g` by conjugation.
  rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
  let a' : A := ⟨g⁻¹ * a * g, Subgroup.Normal.conj_mem' (H := A) inferInstance a a.property g⟩
  refine Submodule.mem_map.mpr ?_
  refine ⟨ρ a' w, W.apply_mem_toSubmodule a' hw, ?_⟩
  calc
    ρ g (ρ a' w) = ρ (g * (a' : A)) w := by
      exact (LinearMap.congr_fun (ρ.map_mul g (a' : A)) w).symm
    _ = ρ (g * (a' : A)) w := by
      rfl
    _ = ρ ((a : Q) * g) w := by
      simp [a', mul_assoc]
    _ = ρ a (ρ g w) := by
      exact LinearMap.congr_fun (ρ.map_mul (a : Q) g) w

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: transporting an
`A`-stable subrepresentation through `ρ g` produces another `A`-stable subrepresentation. -/
def transportedSubrepresentation_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (A : Subgroup Q) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : Q) :
    Subrepresentation (ρ.comp A.subtype) where
  toSubmodule := transportedSubrepresentationCarrier_local ρ A W g
  apply_mem_toSubmodule := transportedSubrepresentationCarrier_apply_mem_local ρ A W g

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: the transported
subrepresentation has the expected carrier. -/
@[simp] theorem transportedSubrepresentation_toSubmodule_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (A : Subgroup Q) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : Q) :
    (transportedSubrepresentation_local ρ A W g).toSubmodule =
      transportedSubrepresentationCarrier_local ρ A W g :=
  rfl

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: every `ρ g` is
injective, so transporting a nonzero subrepresentation keeps it nonzero. -/
theorem transportedSubrepresentation_ne_bot_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (A : Subgroup Q) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : Q)
    (hW : W.toSubmodule ≠ ⊥) :
    (transportedSubrepresentation_local ρ A W g).toSubmodule ≠ ⊥ := by
  -- Apply `ρ g⁻¹` to an equality `map (ρ g) = ⊥` to recover `W = ⊥`.
  intro hbot
  apply hW
  refine le_antisymm ?_ bot_le
  intro w hw
  have hmem : ρ g w ∈ (transportedSubrepresentation_local ρ A W g).toSubmodule := by
    rw [transportedSubrepresentation_toSubmodule_local]
    exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  have hzero_mem : ρ g w ∈ (⊥ : Submodule ℂ V) := by
    rw [hbot] at hmem
    simpa using hmem
  have hzero : ρ g w = 0 := by
    simpa using hzero_mem
  have happly := congrArg (ρ g⁻¹) hzero
  simpa using happly

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: if a restricted
subrepresentation is nonzero as an `ℂ[A]`-owner submodule, then its transported copy is still
nonzero as an owner submodule. -/
theorem transportedSubrepresentation_asSubmodule_ne_bot_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (A : Subgroup Q) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : Q)
    (hW : W.asSubmodule ≠ ⊥) :
    (transportedSubrepresentation_local ρ A W g).asSubmodule ≠ ⊥ := by
  let ρA : Representation ℂ A V := ρ.comp A.subtype
  have hW_toSubmodule : W.toSubmodule ≠ ⊥ := by
    intro hbot
    apply hW
    ext v
    change ((v : V) ∈ W.toSubmodule) ↔
        v ∈ (⊥ : Submodule (MonoidAlgebra ℂ A) ρA.asModule)
    rw [hbot]
    constructor <;> intro hv <;> simpa using hv
  have htransport_toSubmodule :
      (transportedSubrepresentation_local ρ A W g).toSubmodule ≠ ⊥ :=
    transportedSubrepresentation_ne_bot_local ρ A W g hW_toSubmodule
  intro hbot
  have hbot_toSubmodule :
      (transportedSubrepresentation_local ρ A W g).toSubmodule = ⊥ := by
    ext v
    change v ∈ (transportedSubrepresentation_local ρ A W g).asSubmodule ↔
        v ∈ (⊥ : Submodule (MonoidAlgebra ℂ A) ρA.asModule)
    rw [hbot]
  exact htransport_toSubmodule hbot_toSubmodule

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: transporting a fully
invariant `A`-stable summand through `ρ g` preserves full invariance for the restricted
`A`-module. -/
theorem transportedSubrepresentation_asSubmodule_isFullyInvariant_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (A : Subgroup Q) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : Q)
    (hW : W.asSubmodule.IsFullyInvariant) :
    ((transportedSubrepresentation_local ρ A W g).asSubmodule).IsFullyInvariant := by
  let ρA : Representation ℂ A V := ρ.comp A.subtype
  letI : Module (MonoidAlgebra ℂ A) V := ρA.instModuleMonoidAlgebraAsModule
  intro f v hv
  change v ∈ (transportedSubrepresentation_local ρ A W g).toSubmodule at hv
  change f v ∈ (transportedSubrepresentation_local ρ A W g).toSubmodule
  rw [transportedSubrepresentation_toSubmodule_local] at hv ⊢
  rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
  let fInter : ρA.IntertwiningMap ρA :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρA) (σ := ρA)).symm f
  let fConjLin : V →ₗ[ℂ] V := (ρ g⁻¹).comp (fInter.toLinearMap.comp (ρ g))
  have hfConj : ρA.IsIntertwiningMap ρA fConjLin := by
    rw [Representation.isIntertwiningMap_iff]
    intro a x
    let a' : A := ⟨g * a * g⁻¹, Subgroup.Normal.conj_mem inferInstance (a : Q) a.property g⟩
    -- Move the `A`-action across `ρ g⁻¹`, use equivariance of `f`, then move it back across
    -- `ρ g`.
    calc
      fConjLin (ρA a x)
          = ρ g⁻¹ (fInter (ρ g (ρA a x))) := by
              rfl
      _ = ρ g⁻¹ (fInter (ρA a' (ρ g x))) := by
            congr 1
            simp [ρA, a', mul_assoc]
      _ = ρ g⁻¹ (ρA a' (fInter (ρ g x))) := by
            congr 1
            show fInter (ρA a' (ρ g x)) = ρA a' (fInter (ρ g x))
            exact LinearMap.congr_fun (fInter.isIntertwining' a') (ρ g x)
      _ = ρA a (ρ g⁻¹ (fInter (ρ g x))) := by
            simp [ρA, a', mul_assoc]
      _ = ρA a (fConjLin x) := by
            rfl
  let fConj : Module.End (MonoidAlgebra ℂ A) V :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρA) (σ := ρA))
      (fConjLin.intertwiningMap_of_isIntertwiningMap ρA ρA hfConj.isIntertwining)
  have hwConj : fConj w ∈ W.asSubmodule := by
    exact hW fConj hw
  -- Apply full invariance to the conjugated endomorphism on the original component and then
  -- transport the resulting vector forward by `ρ g`.
  refine Submodule.mem_map.mpr ⟨fConj w, hwConj, ?_⟩
  change ρ g (ρ g⁻¹ (f (ρ g w))) = f (ρ g w)
  calc
    ρ g (ρ g⁻¹ (f (ρ g w))) = ρ (g * g⁻¹) (f (ρ g w)) := by
      exact (LinearMap.congr_fun (ρ.map_mul g g⁻¹) (f (ρ g w))).symm
    _ = f (ρ g w) := by
      simp

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: transporting an
`A`-stable subrepresentation through `ρ g` identifies it with the conjugate representation
`W.toRepresentation ^ g`. -/
noncomputable def transportedSubrepresentation_rep_equiv_local
    {Q : Type} [Group Q]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Q V) (A : Subgroup Q) [A.Normal]
    (W : Subrepresentation (ρ.comp A.subtype)) (g : Q) :
    Representation.Equiv
      ((W.toRepresentation).comp (MulAut.conjNormal g⁻¹).toMonoidHom)
      (transportedSubrepresentation_local ρ A W g).toRepresentation := by
  -- The transported carrier is literally `W.toSubmodule.map (ρ g)`, so `ρ g` gives the
  -- underlying linear equivalence and the conjugation formula supplies equivariance.
  let e : W.toSubmodule ≃ₗ[ℂ] (transportedSubrepresentation_local ρ A W g).toSubmodule :=
    Submodule.equivMapOfInjective (ρ g) (ρ.apply_bijective g).injective W.toSubmodule
  refine Representation.Equiv.mk e ?_
  intro a
  ext w
  change ρ g (ρ ((MulAut.conjNormal g).symm a) (w : V)) = ρ a (ρ g w)
  calc
    ρ g (ρ ((MulAut.conjNormal g).symm a) (w : V))
        = ρ (g * (((MulAut.conjNormal g).symm a : A))) (w : V) := by
            exact
              (LinearMap.congr_fun (ρ.map_mul g (((MulAut.conjNormal g).symm a : A))) (w : V)).symm
    _ = ρ ((a : Q) * g) (w : V) := by
          simp [MulAut.conjNormal_symm_apply, mul_assoc]
    _ = ρ a (ρ g w) := by
          exact LinearMap.congr_fun (ρ.map_mul (a : Q) g) (w : V)

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: conjugating the
`A`-action by `g` does not change the subrepresentation lattice. -/
noncomputable def conjugatedSubrepresentationOrderIso_local
    {Q : Type} [Group Q]
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (A : Subgroup Q) [A.Normal]
    (σ : Representation ℂ A W') (g : Q) :
    Subrepresentation (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom) ≃o Subrepresentation σ := {
  toFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro a x hx
        rcases (MulAut.conjNormal g⁻¹).surjective a with ⟨b, rfl⟩
        exact U.apply_mem_toSubmodule b hx }
  invFun U :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule := by
        intro a x hx
        exact U.apply_mem_toSubmodule ((MulAut.conjNormal g⁻¹) a) hx }
  left_inv U := by
    -- Conjugating the action and then untwisting it leaves the carrier unchanged.
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv U := by
    -- The same carrier-level argument proves the reverse identity.
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro U V
    rfl
  }

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: a representation
equivalence induces an order isomorphism on subrepresentations. -/
noncomputable def subrepresentationOrderIso_local
    {A' : Type*} [Group A']
    {V' W' : Type*} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W'] [Module ℂ W']
    {ρ : Representation ℂ A' V'} {σ : Representation ℂ A' W'} (e : ρ.Equiv σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun U :=
    { toSubmodule := U.toSubmodule.map e.toLinearMap
      apply_mem_toSubmodule := by
        intro a x hx
        rcases hx with ⟨y, hy, rfl⟩
        -- Mapping a stable subspace through an intertwining equivalence preserves stability.
        refine ⟨ρ a y, U.apply_mem_toSubmodule a hy, ?_⟩
        simp [e.isIntertwining] }
  invFun U :=
    { toSubmodule := U.toSubmodule.map e.symm.toLinearMap
      apply_mem_toSubmodule := by
        intro a x hx
        rcases hx with ⟨y, hy, rfl⟩
        -- The inverse intertwining equivalence transports stable subspaces back.
        refine ⟨σ a y, U.apply_mem_toSubmodule a hy, ?_⟩
        simp [e.symm.isIntertwining] }
  left_inv U := by
    -- Mapping to `σ` and back to `ρ` recovers the original subrepresentation.
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e x := by
        simpa using congrArg e hxy
      subst this
      simpa using hy
    · intro hx
      change x ∈ Submodule.map e.symm.toLinearMap (Submodule.map e.toLinearMap U.toSubmodule)
      exact ⟨e x, ⟨x, hx, rfl⟩, by simp⟩
  right_inv U := by
    -- The same argument shows that mapping forward and back on `σ` is inverse.
    apply Subrepresentation.toSubmodule_injective
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have : y = e.symm x := by
        simpa using congrArg e.symm hxy
      subst this
      simpa using hy
    · intro hx
      change x ∈ Submodule.map e.toLinearMap (Submodule.map e.symm.toLinearMap U.toSubmodule)
      exact ⟨e.symm x, ⟨x, hx, by simp⟩, by simp⟩
  map_rel_iff' := by
    intro U V
    constructor
    · intro h x hx
      have hxmap : e x ∈ U.toSubmodule.map e.toLinearMap :=
        Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      have hVmap : e x ∈ V.toSubmodule.map e.toLinearMap := h hxmap
      rcases Submodule.mem_map.mp hVmap with ⟨y, hy, hyx⟩
      have : y = x := by
        apply e.injective
        simpa using hyx
      simpa [this] using hy
    · intro h x hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, rfl⟩
      exact ⟨y, h hy, rfl⟩

/-- Helper for fdRepCharacterRing_mem_monomialCharacterSpan_of_irreducible: conjugation leaves
the underlying `ℂ`-submodule unchanged. -/
@[simp] theorem conjugatedSubrepresentationOrderIso_toSubmodule_local
    {Q : Type} [Group Q]
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    (A : Subgroup Q) [A.Normal]
    (σ : Representation ℂ A W') (g : Q)
    (U : Subrepresentation (σ.comp (MulAut.conjNormal g⁻¹).toMonoidHom)) :
    (conjugatedSubrepresentationOrderIso_local A σ g U).toSubmodule = U.toSubmodule :=
  rfl

end

end Representation
