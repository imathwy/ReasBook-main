import Mathlib
import LinearRepresentations_Serre_1977.Chap01.Theorem_1_1_4_2
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_1
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3
import LinearRepresentations_Serre_1977.Chap07.Remark_7_7_1_4
import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_4_1.IdentityProjectionRepresentativeSeeds
import LinearRepresentations_Serre_1977.Chap08.Corollary_8_8_3_8
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.ResidueFieldLift
import LinearRepresentations_Serre_1977.GroupTheory.PSolvable
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicNormalByPGroupBasics
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CliffordIsotypicTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CyclicOrbitSpan
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ProperOvergroupRecursion
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ResidueFieldLiftInductionTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.ULiftScalarExtensionPreparation
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedScalarExtensionTransport
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.InducedCoinvariantsMaps
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.CharacterFieldTransportCore

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

open CategoryTheory Rep
open scoped Representation

section

variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable {G : Type v} [Group G] [Finite G]
variable {p : ℕ}

variable [CharP (IsLocalRing.ResidueField A) p]
variable {V : Type w} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable {C P : Subgroup G}

local notation "k" => IsLocalRing.ResidueField A
noncomputable local instance characterFieldTransportLiftResidueFieldModule
    {W : Type*} [AddCommGroup W] [Module k W] : Module A W :=
  Module.compHom W (algebraMap A k)
local instance characterFieldTransportLiftResidueFieldIsScalarTower
    {W : Type*} [AddCommGroup W] [Module k W] : IsScalarTower A k W :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.3-1: on the lifted cyclic `C`-module, a `C`-equivariant
endomorphism is the identity as soon as it fixes the chosen generator `w0`. -/
theorem character_field_transport_endomorphism_eq_id_of_generator_local
    {W : Type u} [AddCommGroup W] [Module A W]
    (ρA_C : Representation A C W)
    (w0 : W)
    (hspanLifted : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤)
    {f : W →ₗ[A] W}
    (hf : ρA_C.IsIntertwiningMap ρA_C f)
    (hw0 : f w0 = w0) :
    f = LinearMap.id := by
  have hid : ρA_C.IsIntertwiningMap ρA_C (LinearMap.id : W →ₗ[A] W) := by
    -- The identity endomorphism commutes with the `C`-action tautologically.
    rw [Representation.isIntertwiningMap_iff]
    intro c x
    rfl
  -- Generator extensionality turns equality at `w0` into equality on all of `W`.
  simpa using
    c_equivariant_endomorphism_ext_of_generator
      (A := A) (C := C) ρA_C w0 hspanLifted hf hid hw0

/-- Helper for Theorem 17-17.3-1: the identity comparison already belongs to the transport fiber
over `1 ∈ P`. This is Serre's neutral normalized transport once the correction step is done. -/
noncomputable def character_field_transport_fiber_one_local
    {W : Type u} [AddCommGroup W] [Module A W] [C.Normal]
    (ρA_C : Representation A C W) :
    Representation.Equiv
      (ρA_C.comp (MulAut.conjNormal (((1 : P) : G))⁻¹).toMonoidHom)
      ρA_C := by
  refine Representation.Equiv.mk (LinearEquiv.refl A W) ?_
  intro a
  ext x
  simp [MulAut.conjNormal_apply]

/-- Helper for Theorem 17-17.3-1: transport fibers compose by reusing the same carrier map for
the second factor after conjugating its source action by the first factor. This is the literal
source-faithful multiplication law before normalization is imposed. -/
noncomputable def character_field_transport_fiber_comp_local
    {W : Type u} [AddCommGroup W] [Module A W] [C.Normal]
    (ρA_C : Representation A C W)
    {s t : P}
    (u :
      Representation.Equiv
        (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
        ρA_C)
    (v :
      Representation.Equiv
        (ρA_C.comp (MulAut.conjNormal ((t : G))⁻¹).toMonoidHom)
        ρA_C) :
    Representation.Equiv
      (ρA_C.comp (MulAut.conjNormal (((s * t : P) : G))⁻¹).toMonoidHom)
      ρA_C := by
  let v_over_s :
      Representation.Equiv
        (ρA_C.comp (MulAut.conjNormal (((s * t : P) : G))⁻¹).toMonoidHom)
        (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom) := by
    -- The same carrier transport `v` still intertwines after conjugating both source actions by
    -- `s`; this is the source-level cocycle composition step.
    refine Representation.Equiv.mk v.toLinearEquiv ?_
    intro a
    ext x
    simpa [MulAut.conjNormal_apply, mul_assoc] using
      LinearMap.congr_fun (v.isIntertwining' ((MulAut.conjNormal ((s : G))⁻¹) a)) x
  -- Compose the two transport operators in Serre's order: first `t`, then `s`.
  exact v_over_s.trans u

/-- Helper for Theorem 17-17.3-1: once two comparison maps have the same reduction formula and
both fix the chosen lifted generator, generator extensionality forces them to coincide. -/
theorem character_field_transport_equiv_eq_of_reduction_and_generator_local
    (ρ : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module A W] [C.Normal]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (w0 : W)
    (hspanLifted : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤)
    {s : P}
    {u v :
      Representation.Equiv
        (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
        ρA_C}
    (huRed :
      red_C.comp u.toLinearMap =
        (((restricted_conjugation_equiv_of_p_local
            (ρ := ρ) (C := C) (inferInstance : C.Normal) s).toLinearMap.restrictScalars A).comp
          red_C))
    (hvRed :
      red_C.comp v.toLinearMap =
        (((restricted_conjugation_equiv_of_p_local
            (ρ := ρ) (C := C) (inferInstance : C.Normal) s).toLinearMap.restrictScalars A).comp
          red_C))
    (hu0 : u w0 = w0)
    (hv0 : v w0 = w0) :
    u = v := by
  let σs :
      V →ₗ[A] V :=
    (restricted_conjugation_equiv_of_p_local
      (ρ := ρ) (C := C) (inferInstance : C.Normal) s).toLinearMap.restrictScalars A
  have hu_eval : ∀ y : W, red_C (u y) = σs (red_C y) := by
    intro y
    simpa [σs, LinearMap.comp_apply] using
      congrArg (fun f : W →ₗ[A] V ↦ f y) huRed
  have hv_eval : ∀ y : W, red_C (v y) = σs (red_C y) := by
    intro y
    simpa [σs, LinearMap.comp_apply] using
      congrArg (fun f : W →ₗ[A] V ↦ f y) hvRed
  let e : Representation.Equiv ρA_C ρA_C := u.symm.trans v
  have hred_e : red_C.comp e.toLinearMap = red_C := by
    -- The defect map reduces to the identity because both comparisons have the same reduced
    -- action.
    apply LinearMap.ext
    intro x
    calc
      red_C (e x) = red_C (v (u.symm x)) := rfl
      _ = σs (red_C (u.symm x)) := hv_eval (u.symm x)
      _ = red_C (u (u.symm x)) := by
            symm
            exact hu_eval (u.symm x)
      _ = red_C x := by
            simpa using congrArg red_C (u.apply_symm_apply x)
  have huSymm0 : u.symm w0 = w0 := by
    calc
      u.symm w0 = u.symm (u w0) := by rw [hu0]
      _ = w0 := by simpa using (u.symm_apply_apply w0)
  have hw0_e : e w0 = w0 := by
    -- Both comparisons fix `w0`, so their defect endomorphism also fixes `w0`.
    change v (u.symm w0) = w0
    rw [huSymm0, hv0]
  have heInter : ρA_C.IsIntertwiningMap ρA_C e.toLinearMap := by
    -- Forgetting the equivalence keeps the underlying `C`-equivariant endomorphism.
    rw [Representation.isIntertwiningMap_iff]
    intro c x
    exact LinearMap.congr_fun (e.isIntertwining' c) x
  have he_id : e.toLinearMap = LinearMap.id := by
    -- The cyclic-generator lemma turns the fixed-generator condition into triviality.
    exact
      character_field_transport_endomorphism_eq_id_of_generator_local
        (A := A) (C := C) ρA_C w0 hspanLifted heInter hw0_e
  ext x
  -- Evaluate the defect identity at `u x` to recover equality of the original comparisons.
  have hx :
      e.toLinearMap (u x) = (LinearMap.id : W →ₗ[A] W) (u x) := by
    simpa using congrArg (fun f : W →ₗ[A] W ↦ f (u x)) he_id
  calc
    u x = (LinearMap.id : W →ₗ[A] W) (u x) := rfl
    _ = e.toLinearMap (u x) := hx.symm
    _ = v (u.symm (u x)) := rfl
    _ = v x := by rw [u.symm_apply_apply]

/-- Helper for Theorem 17-17.3-1: if two normalized comparisons satisfy the expected reduction
formulas for `s` and `t`, then their Serre-style composition has the expected reduction formula
for `s * t`. -/
theorem character_field_transport_fiber_comp_reduction_local
    (ρ : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module A W] [C.Normal]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    {s t : P}
    {u :
      Representation.Equiv
        (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
        ρA_C}
    {v :
      Representation.Equiv
        (ρA_C.comp (MulAut.conjNormal ((t : G))⁻¹).toMonoidHom)
        ρA_C}
    (huRed :
      red_C.comp u.toLinearMap =
        (((restricted_conjugation_equiv_of_p_local
            (ρ := ρ) (C := C) (inferInstance : C.Normal) s).toLinearMap.restrictScalars A).comp
          red_C))
    (hvRed :
      red_C.comp v.toLinearMap =
        (((restricted_conjugation_equiv_of_p_local
            (ρ := ρ) (C := C) (inferInstance : C.Normal) t).toLinearMap.restrictScalars A).comp
          red_C)) :
    red_C.comp
        (character_field_transport_fiber_comp_local (A := A) (G := G) (P := P)
          (C := C) ρA_C u v).toLinearMap =
      (((restricted_conjugation_equiv_of_p_local
          (ρ := ρ) (C := C) (inferInstance : C.Normal) (s * t)).toLinearMap.restrictScalars A).comp
        red_C) := by
  let σs :
      V →ₗ[A] V :=
    (restricted_conjugation_equiv_of_p_local
      (ρ := ρ) (C := C) (inferInstance : C.Normal) s).toLinearMap.restrictScalars A
  let σt :
      V →ₗ[A] V :=
    (restricted_conjugation_equiv_of_p_local
      (ρ := ρ) (C := C) (inferInstance : C.Normal) t).toLinearMap.restrictScalars A
  let σst :
      V →ₗ[A] V :=
    (restricted_conjugation_equiv_of_p_local
      (ρ := ρ) (C := C) (inferInstance : C.Normal) (s * t)).toLinearMap.restrictScalars A
  have hu_eval : ∀ y : W, red_C (u y) = σs (red_C y) := by
    intro y
    simpa [σs, LinearMap.comp_apply] using
      congrArg (fun f : W →ₗ[A] V ↦ f y) huRed
  have hv_eval : ∀ y : W, red_C (v y) = σt (red_C y) := by
    intro y
    simpa [σt, LinearMap.comp_apply] using
      congrArg (fun f : W →ₗ[A] V ↦ f y) hvRed
  apply LinearMap.ext
  intro x
  -- The raw composed transport reduces to `ρ s ∘ ρ t`, hence to `ρ (s * t)`.
  calc
    red_C ((character_field_transport_fiber_comp_local
        (A := A) (G := G) (P := P) (C := C) ρA_C u v) x)
        = red_C (u (v x)) := rfl
    _ = σs (red_C (v x)) := hu_eval (v x)
    _ = σs (σt (red_C x)) := by rw [hv_eval x]
    _ = ρ (s : G) (ρ (t : G) (red_C x)) := rfl
    _ = ρ (((s * t : P) : G)) (red_C x) := by
          simpa [Module.End.mul_apply] using
            (LinearMap.congr_fun (ρ.map_mul (s : G) (t : G)) (red_C x)).symm
    _ = σst (red_C x) := rfl

/-- Helper for Theorem 17-17.3-1: once the normalized comparisons are available, the fixed
generator `w0` forces the normalized family to satisfy Serre's multiplicativity law. -/
theorem character_field_transport_normalized_multiplicative_local
    (ρ : Representation k G V)
    {W : Type u} [AddCommGroup W] [Module A W] [C.Normal]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (w0 : W)
    (hspanLifted : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤)
    (uNorm :
      ∀ s : P,
        Representation.Equiv
          (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
          ρA_C)
    (huRed :
      ∀ s : P,
        red_C.comp (uNorm s).toLinearMap =
          (((restricted_conjugation_equiv_of_p_local
              (ρ := ρ) (C := C) (inferInstance : C.Normal) s).toLinearMap.restrictScalars A).comp
            red_C))
    (hu0 : ∀ s : P, uNorm s w0 = w0) :
    uNorm 1 =
        character_field_transport_fiber_one_local
          (A := A) (G := G) (P := P) (C := C) ρA_C ∧
      ∀ s t : P,
        character_field_transport_fiber_comp_local
            (A := A) (G := G) (P := P) (C := C) ρA_C (uNorm s) (uNorm t) =
          uNorm (s * t) := by
  have honeRed :
      red_C.comp
          (character_field_transport_fiber_one_local
            (A := A) (G := G) (P := P) (C := C) ρA_C).toLinearMap =
        (((restricted_conjugation_equiv_of_p_local
            (ρ := ρ) (C := C) (inferInstance : C.Normal) (1 : P)).toLinearMap.restrictScalars A).comp
          red_C) := by
    -- At `1`, the transport fiber is the identity map, and the reduced action is `ρ 1 = id`.
    apply LinearMap.ext
    intro x
    calc
      red_C ((character_field_transport_fiber_one_local
          (A := A) (G := G) (P := P) (C := C) ρA_C) x)
          = red_C x := by
              change red_C x = red_C x
              rfl
      _ = ρ (1 : G) (red_C x) := by
            simpa using (LinearMap.congr_fun ρ.map_one (red_C x)).symm
      _ =
          ((restricted_conjugation_equiv_of_p_local
              (ρ := ρ) (C := C) (inferInstance : C.Normal) (1 : P)).toLinearMap.restrictScalars A)
            (red_C x) := rfl
  have hone0 :
      (character_field_transport_fiber_one_local
        (A := A) (G := G) (P := P) (C := C) ρA_C) w0 = w0 := by
    change w0 = w0
    rfl
  constructor
  · -- The normalized comparison at `1` is uniquely forced by the reduction formula and the fact
    -- that it fixes `w0`.
    exact
      character_field_transport_equiv_eq_of_reduction_and_generator_local
        (A := A) (G := G) (V := V) (C := C) (P := P)
        (ρ := ρ) (ρA_C := ρA_C) (red_C := red_C) (w0 := w0) (hspanLifted := hspanLifted)
        (u := uNorm 1)
        (v := character_field_transport_fiber_one_local
          (A := A) (G := G) (P := P) (C := C) ρA_C)
        (huRed := huRed 1)
        (hvRed := honeRed)
        (hu0 := hu0 1)
        (hv0 := hone0)
  · intro s t
    -- The Serre-style product comparison has the correct reduced action and still fixes `w0`, so
    -- uniqueness on the cyclic generator identifies it with `uNorm (s * t)`.
    apply
      character_field_transport_equiv_eq_of_reduction_and_generator_local
        (A := A) (G := G) (V := V) (C := C) (P := P)
        ρ ρA_C red_C w0 hspanLifted
    · exact
        character_field_transport_fiber_comp_reduction_local
          (A := A) (G := G) (V := V) (C := C) (P := P)
          ρ ρA_C red_C (huRed s) (huRed t)
    · exact huRed (s * t)
    · change uNorm s (uNorm t w0) = w0
      rw [hu0 t, hu0 s]
    · exact hu0 (s * t)

/-- Helper for Theorem 17-17.3-1: once the `P`-fixed vector and orbit-span checkpoints are
established and a lift of the restricted `C`-representation is chosen, the only remaining work in
the isotypic branch is the character-field transport of the `P`-action to that chosen lift. -/
theorem character_field_transport_extends_lift
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hC : C.Normal) (hCP : C.IsComplement' P)
    (hCndvd : ¬ p ∣ Nat.card C)
    (hCyclic : IsCyclic C)
    {W : Type u} [AddCommGroup W] [Module A W]
    [Module.Free A W] [Module.Finite A W]
    (ρA_C : Representation A C W)
    (red_C : W →ₗ[A] V)
    (hLiftC : IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C)
    (w0 : W) (ν : V)
    (hν0 : ν ≠ 0)
    (hw0 : red_C w0 = ν)
    (hνfixed : ∀ s : P, (ρ.comp P.subtype) s ν = ν)
    (hOrbitSpan : Submodule.span k (Set.range fun c : C ↦ ρ c ν) = ⊤)
    (hspanLifted : Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤) :
    ∃ ρA : Representation A G W,
      IsResidueFieldLift ρ ρA red_C := by
  -- Route correction: the cyclic generator `w0` and its lifted orbit span are already fixed, so
  -- the only remaining source-faithful step is to normalize each conjugate comparison so it fixes
  -- `w0` and then assemble those normalized maps into the ambient `P`-action.
  let _ := hC
  let _ := hCP
  let _ := hCndvd
  let _ := hCyclic
  let _ := hLiftC
  let _ := hν0
  let _ := hw0
  let _ := hνfixed
  let _ := hOrbitSpan
  let _ := hspanLifted
  letI : CommGroup C := IsCyclic.commGroup
  have hConjCompare :
      ∀ s : P,
        ∃ u :
            Representation.Equiv
              (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
              ρA_C,
          red_C.comp u.toLinearMap =
              (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
                A).comp red_C) ∧
            red_C (u w0) = ν := by
    intro s
    -- The conjugated lift is now packaged exactly as in Serre's source route, and the comparison
    -- already sends `w0` to another lift of the same residue generator `ν`.
    exact
      character_field_transport_conjugate_lift_compare_fixed_vector_local
        (A := A) (G := G) (p := p) (V := V) (C := C) (P := P)
        ρ hC hCndvd ρA_C red_C hLiftC w0 ν hw0 hνfixed s
  have hCompareSpan :
      ∀ s : P,
        ∃ u :
            Representation.Equiv
              (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
              ρA_C,
          red_C.comp u.toLinearMap =
              (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
                A).comp red_C) ∧
            red_C (u w0) = ν ∧
            Submodule.span A (Set.range fun c : C ↦ ρA_C c (u w0)) = ⊤ := by
    intro s
    rcases hConjCompare s with ⟨u, huRed, huw0⟩
    refine ⟨u, huRed, huw0, ?_⟩
    -- The comparison vector `u w0` is another lift of `ν`, so it generates the same lifted
    -- cyclic `C`-module by the previously established Nakayama step.
    exact
      character_field_transport_compare_generator_span_local
        (A := A) (G := G) (ρ := ρ) (C := C) ρA_C red_C hLiftC (u w0) ν huw0 hOrbitSpan
  classical
  have hNormExists :
      ∀ s : P,
        ∃ uNorm :
            Representation.Equiv
              (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
              ρA_C,
          red_C.comp uNorm.toLinearMap =
              (((restricted_conjugation_equiv_of_p_local (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars
                A).comp red_C) ∧
            uNorm w0 = w0 := by
    intro s
    rcases hCompareSpan s with ⟨u, huRed, huw1, hspan1⟩
    rcases
        character_field_transport_correction_equiv_local
          (A := A) (G := G) (C := C) (ρ := ρ)
          ρA_C red_C hLiftC w0 (u w0) ν hw0 huw1 hspanLifted hspan1 with
      ⟨corr, hcorrRed, hcorrw⟩
    let uNorm :
        Representation.Equiv
          (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
          ρA_C := u.trans corr
    refine ⟨uNorm, ?_, hcorrw⟩
    -- The correction map preserves reduction, so the normalized transport keeps Serre's reduced
    -- comparison formula while now fixing `w0`.
    apply LinearMap.ext
    intro x
    calc
      red_C (uNorm x) = red_C (corr (u x)) := rfl
      _ = red_C (u x) := by
            simpa [LinearMap.comp_apply] using
              congrArg (fun f : W →ₗ[A] V ↦ f (u x)) hcorrRed
      _ =
          (((restricted_conjugation_equiv_of_p_local
              (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars A).comp red_C) x := by
            simpa [LinearMap.comp_apply] using
              congrArg (fun f : W →ₗ[A] V ↦ f x) huRed
  let uNorm :
      ∀ s : P,
        Representation.Equiv
          (ρA_C.comp (MulAut.conjNormal ((s : G))⁻¹).toMonoidHom)
          ρA_C :=
    fun s ↦ Classical.choose (hNormExists s)
  have huNormRed :
      ∀ s : P,
        red_C.comp (uNorm s).toLinearMap =
          (((restricted_conjugation_equiv_of_p_local
              (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars A).comp red_C) := by
    intro s
    exact (Classical.choose_spec (hNormExists s)).1
  have huNorm0 : ∀ s : P, uNorm s w0 = w0 := by
    intro s
    exact (Classical.choose_spec (hNormExists s)).2
  have hNormOneMul :
      uNorm 1 =
          character_field_transport_fiber_one_local
            (A := A) (G := G) (P := P) (C := C) ρA_C ∧
        ∀ s t : P,
          character_field_transport_fiber_comp_local
              (A := A) (G := G) (P := P) (C := C) ρA_C (uNorm s) (uNorm t) =
            uNorm (s * t) :=
    character_field_transport_normalized_multiplicative_local
      (A := A) (G := G) (V := V) (C := C) (P := P)
      ρ ρA_C red_C w0 hspanLifted uNorm huNormRed huNorm0
  rcases hNormOneMul with ⟨hNormOne, hNormMul⟩
  have huNorm_one_apply : ∀ x : W, uNorm 1 x = x := by
    intro x
    rw [hNormOne]
    rfl
  have huNorm_mul_apply : ∀ s t : P, ∀ x : W, uNorm (s * t) x = uNorm s (uNorm t x) := by
    intro s t x
    simpa [character_field_transport_fiber_comp_local] using
      congrArg (fun e :
        Representation.Equiv
          (ρA_C.comp (MulAut.conjNormal (((s * t : P) : G))⁻¹).toMonoidHom)
          ρA_C ↦ e x) (hNormMul s t).symm
  have huNorm_comm :
      ∀ s : P, ∀ c : C, ∀ x : W,
        uNorm s (ρA_C c x) =
          ρA_C ((MulAut.conjNormal ((s : G)) c)) (uNorm s x) := by
    intro s c x
    -- Evaluate the normalized transport on the conjugate of `c`; the source action simplifies
    -- back to the original `c`-action.
    simpa [MulAut.conjNormal_apply, mul_assoc] using
      LinearMap.congr_fun ((uNorm s).isIntertwining' ((MulAut.conjNormal ((s : G)) c))) x
  let split : G → C × P := fun g ↦ Classical.choose (hCP.2 g)
  have hsplit_spec : ∀ g : G, ((split g).1 : G) * ((split g).2 : G) = g := by
    intro g
    exact Classical.choose_spec (hCP.2 g)
  have hsplit_one : split (1 : G) = ((1 : C), (1 : P)) := by
    apply hCP.1
    simpa using hsplit_spec (1 : G)
  have hsplit_mul :
      ∀ g h : G,
        split (g * h) =
          ((split g).1 * (MulAut.conjNormal ((split g).2 : G) ((split h).1)),
            (split g).2 * (split h).2) := by
    intro g h
    apply hCP.1
    calc
      (((split (g * h)).1 : C) : G) * (((split (g * h)).2 : P) : G) = g * h := hsplit_spec (g * h)
      _ = ((((split g).1 : C) : G) * (((split g).2 : P) : G)) *
            ((((split h).1 : C) : G) * (((split h).2 : P) : G)) := by
              rw [hsplit_spec g, hsplit_spec h]
      _ =
          ((((split g).1 * (MulAut.conjNormal ((split g).2 : G) ((split h).1)) : C) : G) *
            ((((split g).2 * (split h).2 : P) : G))) := by
              simp [MulAut.conjNormal_apply, mul_assoc]
  let ρA : Representation A G W :=
    { toFun := fun g =>
        let c : C := (split g).1
        let s : P := (split g).2
        { toFun := fun x ↦ ρA_C c (uNorm s x)
          map_add' := by
            intro x y
            simp
          map_smul' := by
            intro a x
            simp }
      map_one' := by
        ext x
        -- The normalized family is trivial at `1`, so the factorized action recovers `ρA_C 1 = id`.
        change ρA_C ((split 1).1) (uNorm ((split 1).2) x) = x
        rw [hsplit_one]
        simpa using huNorm_one_apply x
      map_mul' := by
        intro g h
        ext x
        let cg : C := (split g).1
        let sg : P := (split g).2
        let ch : C := (split h).1
        let sh : P := (split h).2
        -- Rewrite the `C`-component of `g * h` using the complement factorization, then move the
        -- `C`-action across the normalized `P`-transport.
        rw [hsplit_mul]
        change
          ρA_C (cg * MulAut.conjNormal (sg : G) ch) (uNorm (sg * sh) x) =
            ρA_C cg (uNorm sg (ρA_C ch (uNorm sh x)))
        rw [huNorm_mul_apply]
        calc
          ρA_C (cg * MulAut.conjNormal (sg : G) ch) (uNorm sg (uNorm sh x))
              = ρA_C cg (ρA_C (MulAut.conjNormal (sg : G) ch) (uNorm sg (uNorm sh x))) := by
                  simpa [Module.End.mul_apply] using
                    LinearMap.congr_fun (ρA_C.map_mul cg (MulAut.conjNormal (sg : G) ch))
                      (uNorm sg (uNorm sh x))
          _ = ρA_C cg (uNorm sg (ρA_C ch (uNorm sh x))) := by
                rw [huNorm_comm sg ch (uNorm sh x)] }
  have hinter : ρA.IsIntertwiningMap (ρ.restrictScalars A) red_C := by
    rw [Representation.isIntertwiningMap_iff]
    intro g x
    let c : C := (split g).1
    let s : P := (split g).2
    have hRedC :
        red_C (ρA_C c (uNorm s x)) =
          (Representation.restrictScalars A (ρ.comp C.subtype)) c (red_C (uNorm s x)) := by
      simpa [Representation.restrictScalars_apply] using
        (residueFieldLift_isIntertwining_restrictScalars
          (A := A) (σ := ρ.comp C.subtype) hLiftC).isIntertwining c (uNorm s x)
    have hRedP :
        red_C (uNorm s x) =
          ((restricted_conjugation_equiv_of_p_local
              (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars A) (red_C x) := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun f : W →ₗ[A] V ↦ f x) (huNormRed s)
    -- The normalized `P`-transport has the prescribed reduced action, so the factorized `G`
    -- action intertwines with `red_C`.
    calc
      red_C (ρA g x) = red_C (ρA_C c (uNorm s x)) := rfl
      _ = (Representation.restrictScalars A (ρ.comp C.subtype)) c (red_C (uNorm s x)) := hRedC
      _ =
          (Representation.restrictScalars A (ρ.comp C.subtype)) c
            (((restricted_conjugation_equiv_of_p_local
                (ρ := ρ) (C := C) hC s).toLinearMap.restrictScalars A) (red_C x)) := by
              rw [hRedP]
      _ = ρ (c : G) (ρ (s : G) (red_C x)) := rfl
      _ = ρ (((c : C) : G) * ((s : P) : G)) (red_C x) := by
            simpa [Module.End.mul_apply] using
              (LinearMap.congr_fun (ρ.map_mul ((c : C) : G) ((s : P) : G)) (red_C x)).symm
      _ = ρ g (red_C x) := by rw [hsplit_spec g]
      _ = (ρ.restrictScalars A) g (red_C x) := by rfl
  have hraw :
      RawIsResidueFieldReduction_local (A := A) ρ ρA red_C :=
    residueFieldReduction_of_isBaseChange_isIntertwining
      (A := A) (G' := G) (ρ := ρ) (ρA := ρA) hLiftC.1 hinter
  refine ⟨ρA, ?_⟩
  simpa [IsResidueFieldLift, RawIsResidueFieldReduction_local] using hraw

/-- Helper for Theorem 17-17.3-1: once the fixed vector and orbit-span checkpoints are in place,
the chosen `C`-lift can be extended to `G` after supplying the coprimality witness on `C`. -/
theorem exists_residueFieldLift_of_character_field_transport
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hC : C.Normal) (hCP : C.IsComplement' P)
    (hCndvd : ¬ p ∣ Nat.card C)
    (hCyclic : IsCyclic C)
    (hIso :
      let ρC : Representation k C V := ρ.comp C.subtype
      letI : Module (MonoidAlgebra k C) V := ρC.instModuleMonoidAlgebraAsModule
      IsIsotypic (MonoidAlgebra k C) V)
    (ν : V) (hν0 : ν ≠ 0)
    (hνfixed : ∀ s : P, (ρ.comp P.subtype) s ν = ν)
    (hOrbitSpan : Submodule.span k (Set.range fun c : C ↦ ρ c ν) = ⊤)
    (hLiftC :
      ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
        (_ : Module.Free A W) (_ : Module.Finite A W)
        (ρA_C : Representation A C W)
        (red_C : W →ₗ[A] V),
          IsResidueFieldLift (ρ.comp C.subtype) ρA_C red_C) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module A W)
      (_ : Module.Free A W) (_ : Module.Finite A W)
      (ρA : Representation A G W)
      (red : W →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  rcases hLiftC with ⟨W, hWadd, hWmod, hWfree, hWfinite, ρA_C, red_C, hLiftC⟩
  letI : AddCommGroup W := hWadd
  letI : Module A W := hWmod
  letI : Module.Free A W := hWfree
  letI : Module.Finite A W := hWfinite
  letI : Module A (IsLocalRing.ResidueField A) := Algebra.toModule
  let _ := hν0
  have hred_surj : Function.Surjective red_C :=
    residueFieldLift_surjective (A := A) hLiftC
  obtain ⟨w0, hw0⟩ := hred_surj ν
  have hspanLifted :
      Submodule.span A (Set.range fun c : C ↦ ρA_C c w0) = ⊤ := by
    -- Route correction: the lifted orbit span is now upgraded to `⊤` before we normalize the
    -- comparison isomorphisms. This follows Serre's source proof more faithfully than trying to
    -- build the `P`-action first and only then recover generation.
    exact
      cyclic_lift_span_top_of_fixed_lift
        (A := A) (G := G) (ρ := ρ) (C := C) ρA_C red_C hLiftC w0 ν hw0 hOrbitSpan
  rcases
      character_field_transport_extends_lift
        (A := A) (G := G) (V := V) (C := C) (P := P) (ρ := ρ) hC hCP hCndvd hCyclic
        ρA_C red_C hLiftC w0 ν hν0 hw0 hνfixed hOrbitSpan hspanLifted with
    ⟨ρA, hLift⟩
  -- The lifted `C`-module is fixed above; after extending its action from `C` to `G`, the
  -- residue-field reduction map is unchanged.
  let _ := hIso
  let _ := hOrbitSpan
  exact ⟨W, hWadd, hWmod, hWfree, hWfinite, ρA, red_C, hLift⟩



end

end Representation
