import LinearRepresentations_Serre_1977.Serre.Chap04.Proposition_4_27
import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_5
import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_15
import LinearRepresentations_Serre_1977.Serre.Chap04.Theorem_4_32

noncomputable section

open MeasureTheory
open scoped ComplexConjugate MonoidAlgebra

-- Semantic recall: `lean_leansearch` surfaced `isotypicComponents`/`isotypicComponent` as the
-- canonical owner. The explicit operator in Theorem 4-33 is the character-average endomorphism;
-- the claim that it projects onto the relevant isotypic component is therefore recorded at the
-- proposition level via `LinearMap.IsProj`, rather than by manufacturing decomposition data from
-- Theorem 4-32.

universe u v w

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]
variable (ρ : Representation ℂ G V)

/-- The explicit operator in Theorem 4-33, namely
`n_i ∫ t, conj (χ_i t) • ρ t ∂μG` with `n_i = Module.finrank ℂ W`. -/
def isotypicCharacterAverage
    [Representation.IsContinuous ρ]
    (π : Representation ℂ G W) [Representation.IsContinuous π] :
    Module.End ℂ V :=
  (Module.finrank ℂ W : ℂ) •
    (classFunctionAveragedEndomorphism ρ (fun t ↦ conj (π.character t))).toLinearMap

/-- Evaluating `isotypicCharacterAverage ρ π` on `x : V` gives the source-facing integral formula
`n_i ∫ t, conj (χ_i t) • ρ t x ∂μG`, with `n_i = Module.finrank ℂ W`. -/
theorem isotypicCharacterAverage_apply
    [Representation.IsContinuous ρ]
    (π : Representation ℂ G W) [Representation.IsContinuous π]
    (x : V) :
    isotypicCharacterAverage ρ π x =
      (Module.finrank ℂ W : ℂ) • ∫ t, conj (π.character t) • ρ t x ∂μG := by
  -- Expand the averaged operator once, then evaluate the integral operator on the vector `x`.
  simpa [Representation.isotypicCharacterAverage, LinearMap.smul_apply] using
    congrArg (fun y : V ↦ (Module.finrank ℂ W : ℂ) • y)
      (Representation.classFunctionAveragedEndomorphism_apply ρ
        (fun t ↦ conj (π.character t))
        (by
          simpa using
            Complex.continuous_conj.comp
              (Representation.continuous_character_of_isContinuousCompact (ρ := π)))
        x)

/-- Helper for Theorem 4-33: the conjugated character `t ↦ conj (π.character t)` is continuous on
the compact group `G`. -/
private theorem continuous_conjCharacter
    (π : Representation ℂ G W) [Representation.IsContinuous π] :
    Continuous fun t ↦ conj (π.character t) := by
  -- Compose continuity of the character with continuity of complex conjugation.
  simpa using
    Complex.continuous_conj.comp
      (Representation.continuous_character_of_isContinuousCompact (ρ := π))

omit [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℂ W]
  [T2Space W] [FiniteDimensional ℂ W] in
/-- Helper for Theorem 4-33: the conjugated character `t ↦ conj (π.character t)` is a class
function. -/
private theorem isClassFunction_conjCharacter
    (π : Representation ℂ G W) :
    _root_.IsClassFunction fun t ↦ conj (π.character t) := by
  -- The ordinary character is constant on conjugacy classes, hence so is its conjugate.
  refine isClassFunction_of_forall_conj_eq ?_
  intro s t
  simp [π.char_conj t s]

omit [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [CompleteSpace V] [FiniteDimensional ℂ V] in
/-- Helper for Theorem 4-33: the owner action on `Subrepresentation.ofSubmodule' S` is the
original `ℂ[G]`-action on the owner submodule `S`. -/
private theorem subrepresentation_ofSubmodule'_asAlgebraHom_apply_local
    (S : Submodule ℂ[G] ρ.asModule) (r : ℂ[G]) (x : S) :
    (((Subrepresentation.ofSubmodule' S).toRepresentation).asAlgebraHom r) x = r • x := by
  -- Compare the intrinsic owner action with the ambient owner action on the subtype carrier.
  apply Subtype.ext
  induction r using MonoidAlgebra.induction_linear with
  | zero =>
      -- Both actions send `0` to the zero vector.
      rfl
  | add a b ha hb =>
      -- Additivity reduces the ambient equality to the induction hypotheses.
      rw [map_add, LinearMap.add_apply, Submodule.coe_add, add_smul, Submodule.coe_add, ha, hb]
      rfl
  | single g a =>
      -- On monomials, both actions are the restricted `ρ g` scaled by `a`.
      simp [Representation.asAlgebraHom_single, Representation.single_smul]
      rfl

/-- Helper for Theorem 4-33: the owner module of
`(Subrepresentation.ofSubmodule' S).toRepresentation` is canonically the original `ℂ[G]`-module
`S`. -/
private noncomputable def subrepresentation_ofSubmodule'_asModule_linearEquiv_local
    (S : Submodule ℂ[G] ρ.asModule) :
    ((Subrepresentation.ofSubmodule' S).toRepresentation).asModule ≃ₗ[ℂ[G]] S := by
  let ρS : Representation ℂ G S := (Subrepresentation.ofSubmodule' S).toRepresentation
  letI : Module ℂ[G] ρS.asModule := ρS.instModuleMonoidAlgebraAsModule
  refine
    { toFun := fun x => ρS.asModuleEquiv x
      invFun := fun x => ρS.asModuleEquiv.symm x
      left_inv := by
        intro x
        simp
      right_inv := by
        intro x
        simp
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        -- Rewrite the transported action through `asModuleEquiv`, then identify it with the
        -- original owner action on `S`.
        intro r x
        calc
          ρS.asModuleEquiv (r • x) = (ρS.asAlgebraHom r) (ρS.asModuleEquiv x) := by
            exact Representation.asModuleEquiv_map_smul (ρ := ρS) r x
          _ = r • ρS.asModuleEquiv x := by
            exact subrepresentation_ofSubmodule'_asAlgebraHom_apply_local (ρ := ρ) S r
              (ρS.asModuleEquiv x) }

omit [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W] in
/-- Helper for Theorem 4-33: a `ℂ[G]`-linear equivalence from a simple owner summand `S` to the
owner module of `π` upgrades to an equivalence of the corresponding representations. -/
private theorem nonempty_equiv_of_subrepresentation_moduleLinearEquiv
    [Representation.IsContinuous ρ]
    (π : Representation ℂ G W) [Representation.IsContinuous π]
    (S : Submodule ℂ[G] ρ.asModule) (e : S ≃ₗ[ℂ[G]] π.asModule) :
    Nonempty (((Subrepresentation.ofSubmodule' S).toRepresentation).Equiv π) := by
  let ρS : Representation ℂ G S := (Subrepresentation.ofSubmodule' S).toRepresentation
  let eRep : ρS.asModule ≃ₗ[ℂ[G]] π.asModule :=
    (subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) S).trans e
  -- Convert the owner-linear equivalence into an intertwiner, then package bijectivity.
  let f : ρS.IntertwiningMap π :=
    (Representation.IntertwiningMap.equivLinearMapAsModule ρS π).symm eRep.toLinearMap
  exact ⟨f.ofBijective eRep.bijective⟩

/-- Helper for Theorem 4-33: a representation equivalence induces the corresponding owner-module
linear equivalence. -/
private noncomputable def representationEquiv_asModuleLinearEquiv_local
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    {W' : Type*} [AddCommGroup W'] [Module ℂ W']
    {ρ' : Representation ℂ G V'} {σ' : Representation ℂ G W'}
    (e : ρ'.Equiv σ') :
    ρ'.asModule ≃ₗ[ℂ[G]] σ'.asModule := by
  refine
    { toFun := (Representation.IntertwiningMap.equivLinearMapAsModule ρ' σ') e.toIntertwiningMap
      invFun :=
        (Representation.IntertwiningMap.equivLinearMapAsModule σ' ρ') e.symm.toIntertwiningMap
      left_inv := by
        intro x
        change e.symm (e x) = x
        simp
      right_inv := by
        intro x
        change e (e.symm x) = x
        simp
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro r x
        simp }

omit [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W] in
/-- Helper for Theorem 4-33: an equivalence
`((Subrepresentation.ofSubmodule' S).toRepresentation) ≃ π` yields the underlying owner-level
`ℂ[G]`-linear equivalence `S ≃ₗ[ℂ[G]] W`. -/
private theorem nonempty_moduleLinearEquiv_of_nonempty_equiv_of_subrepresentation
    [Representation.IsContinuous ρ]
    (π : Representation ℂ G W) [Representation.IsContinuous π]
    (S : Submodule ℂ[G] ρ.asModule)
    (hSπ : Nonempty (((Subrepresentation.ofSubmodule' S).toRepresentation).Equiv π)) :
    Nonempty (S ≃ₗ[ℂ[G]] π.asModule) := by
  rcases hSπ with ⟨e⟩
  -- Forget the representation equivalence to the owner `ℂ[G]`-module level, then untwist the
  -- canonical owner-module identification for `Subrepresentation.ofSubmodule' S`.
  exact ⟨(subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) S).symm.trans
    (representationEquiv_asModuleLinearEquiv_local e)⟩

/-- Helper for Theorem 4-33: the owner module underlying `π` is canonically the ambient vector
space `W` equipped with its `ℂ[G]`-action. -/
private noncomputable def representationAsModuleLinearEquivCarrier
    (π : Representation ℂ G W) :
    let _ : Module ℂ[G] W := π.instModuleMonoidAlgebraAsModule
    π.asModule ≃ₗ[ℂ[G]] W := by
  letI : Module ℂ[G] W := π.instModuleMonoidAlgebraAsModule
  refine
    { toFun := fun x => π.asModuleEquiv x
      invFun := fun x => π.asModuleEquiv.symm x
      left_inv := by
        intro x
        simp
      right_inv := by
        intro x
        simp
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        -- Rewrite the owner action through `asModuleEquiv`, then use the defining owner action of
        -- `π`.
        intro r x
        calc
          π.asModuleEquiv (r • x) = π.asAlgebraHom r (π.asModuleEquiv x) := by
            exact Representation.asModuleEquiv_map_smul (ρ := π) r x
          _ = r • π.asModuleEquiv x := by
            rfl }

/-- Helper for Theorem 4-33: a simple owner summand lies in `ρ.moduleIsotypicComponent π`
exactly when its associated irreducible subrepresentation is equivalent to `π`. -/
private theorem simpleSubmodule_le_moduleIsotypicComponent_iff_equiv
    [Representation.IsContinuous ρ]
    (π : Representation ℂ G W) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S] :
    S ≤ ρ.moduleIsotypicComponent π ↔
      Nonempty (((Subrepresentation.ofSubmodule' S).toRepresentation).Equiv π) := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : Module ℂ[G] W := π.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] W := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule π).mp inferInstance
  let S' : Submodule ℂ[G] V := S
  constructor
  · intro hS
    have hS' : S' ≤ ρ.moduleIsotypicComponent π := by
      simpa [S'] using hS
    -- Route correction: keep the isotypic argument purely on the owner-module surface, then
    -- package the resulting `ℂ[G]`-linear equivalence as a representation equivalence.
    have hTargetIsotypic : IsIsotypicOfType ℂ[G] (ρ.moduleIsotypicComponent π) W := by
      simpa [Representation.moduleIsotypicComponent] using
        (IsIsotypicOfType.isotypicComponent (R := ℂ[G]) (M := V) (S := W))
    have hIsotypic : IsIsotypicOfType ℂ[G] S' W := by
      let i : S' →ₗ[ℂ[G]] ρ.moduleIsotypicComponent π := Submodule.inclusion hS'
      have hi : Function.Injective i := Submodule.inclusion_injective hS'
      exact hTargetIsotypic.of_injective i hi
    letI : IsSimpleModule ℂ[G] S' := by
      simpa [S'] using (inferInstance : IsSimpleModule ℂ[G] S)
    letI : IsSimpleModule ℂ[G] (⊤ : Submodule ℂ[G] S') :=
      IsSimpleModule.congr (Submodule.topEquiv : (⊤ : Submodule ℂ[G] S') ≃ₗ[ℂ[G]] S')
    have hEquivTop : Nonempty ((⊤ : Submodule ℂ[G] S') ≃ₗ[ℂ[G]] W) := hIsotypic ⊤
    have hEquivCarrier : Nonempty (S ≃ₗ[ℂ[G]] W) := by
      rcases hEquivTop with ⟨eTop⟩
      exact ⟨(Submodule.topEquiv : (⊤ : Submodule ℂ[G] S') ≃ₗ[ℂ[G]] S').symm.trans eTop⟩
    rcases hEquivCarrier with ⟨eSW⟩
    let eπ : π.asModule ≃ₗ[ℂ[G]] W := representationAsModuleLinearEquivCarrier π
    exact nonempty_equiv_of_subrepresentation_moduleLinearEquiv (ρ := ρ) π S
      (eSW.trans eπ.symm)
  · intro hSπ
    rcases nonempty_moduleLinearEquiv_of_nonempty_equiv_of_subrepresentation
        (ρ := ρ) π S hSπ with ⟨eSπ⟩
    let eπ : π.asModule ≃ₗ[ℂ[G]] W := representationAsModuleLinearEquivCarrier π
    have hEq : isotypicComponent ℂ[G] V S' = isotypicComponent ℂ[G] V W := by
      simpa [S'] using (eSπ.trans eπ).isotypicComponent_eq
    intro x hx
    have hxS' : x ∈ S' := by
      simpa [S'] using hx
    have hx' : x ∈ isotypicComponent ℂ[G] V S' := S'.le_isotypicComponent hxS'
    simpa [Representation.moduleIsotypicComponent, S', hEq] using hx'

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [CompleteSpace V] [FiniteDimensional ℂ V] in
/-- Helper for Theorem 4-33: a subrepresentation of a continuous representation inherits the
continuity needed for the compact-group averaging operators. -/
private theorem subrepresentation_toRepresentation_isContinuous
    [Representation.IsContinuous ρ]
    (σ : Subrepresentation ρ) :
    Representation.IsContinuous σ.toRepresentation := by
  -- Restrict the ambient continuous action to the invariant subtype carrier.
  refine Representation.isContinuous_of_continuousAction σ.toRepresentation ?_
  exact
    ((Representation.continuousAction ρ).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
      (fun gx ↦ σ.apply_mem_toSubmodule gx.1 gx.2.2)

/-- Helper for Theorem 4-33: if the owner summand `S` is simple, then the corresponding
subrepresentation `(Subrepresentation.ofSubmodule' S).toRepresentation` is irreducible. -/
private theorem subrepresentation_toRepresentation_isIrreducible_of_isSimpleModule
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S] :
    ((Subrepresentation.ofSubmodule' S).toRepresentation).IsIrreducible := by
  let ρS : Representation ℂ G S := (Subrepresentation.ofSubmodule' S).toRepresentation
  letI : Module ℂ[G] ρS.asModule := ρS.instModuleMonoidAlgebraAsModule
  -- Transfer simplicity across the canonical owner-module equivalence and then invoke the
  -- irreducibility/simple-module bridge for the bundled subrepresentation.
  exact
    (Representation.irreducible_iff_isSimpleModule_asModule ρS).mpr
      (@IsSimpleModule.congr (ℂ[G]) inferInstance ρS.asModule
        ρS.instAddCommGroupAsModule ρS.instModuleMonoidAlgebraAsModule
        S S.addCommGroup S.module
        (subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) S) inferInstance)

/-- Helper for Theorem 4-33: forgetting the averaged operator on
`(Subrepresentation.ofSubmodule' S).toRepresentation` recovers the ambient averaged operator on
`V`. -/
private theorem subtypeVal_isotypicCharacterAverage_ofSubmodule'
    [Representation.IsContinuous ρ]
    (π : Representation ℂ G W) [Representation.IsContinuous π]
    (S : Submodule ℂ[G] ρ.asModule)
    [Representation.IsContinuous ((Subrepresentation.ofSubmodule' S).toRepresentation)]
    {x : V} (hx : x ∈ S) :
    Subtype.val (Representation.isotypicCharacterAverage
        ((Subrepresentation.ofSubmodule' S).toRepresentation) π ⟨x, hx⟩) =
      Representation.isotypicCharacterAverage ρ π x := by
  let T : Submodule ℂ V := (Subrepresentation.ofSubmodule' S).toSubmodule
  let ρS : Representation ℂ G T := (Subrepresentation.ofSubmodule' S).toRepresentation
  let φ : G → T := fun t ↦ conj (π.character t) • ρS t ⟨x, hx⟩
  have hφ_cont : Continuous φ := by
    -- The integrand is continuous because both the character factor and the restricted orbit map
    -- are continuous on the compact group.
    exact (continuous_conjCharacter (G := G) (π := π)).smul
      (Representation.continuous_apply ρS ⟨x, hx⟩)
  have hφ_int : Integrable φ μG := by
    -- Compactness upgrades the vector-valued integrand to Bochner integrability.
    have hIntOn : IntegrableOn φ Set.univ μG :=
      ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ hφ_cont.continuousOn
    simpa [MeasureTheory.integrableOn_univ] using hIntOn
  -- Commute the forgetful map `Subtype.val` through the integral, then identify the pointwise
  -- integrands with the ambient action of `ρ`.
  rw [Representation.isotypicCharacterAverage_apply (ρ := ρS) (π := π) ⟨x, hx⟩,
    Representation.isotypicCharacterAverage_apply (ρ := ρ) (π := π) x]
  change
    (Module.finrank ℂ W : ℂ) • Subtype.val (∫ t, φ t ∂μG) =
      (Module.finrank ℂ W : ℂ) • ∫ t, conj (π.character t) • ρ t x ∂μG
  congr 1
  calc
    Subtype.val (∫ t, φ t ∂μG)
      = (LinearMap.toContinuousLinearMap (Submodule.subtype T)) (∫ t, φ t ∂μG) := by
          rfl
    _ = ∫ t, (LinearMap.toContinuousLinearMap (Submodule.subtype T)) (φ t) ∂μG := by
          simpa using
            (ContinuousLinearMap.integral_comp_comm
              (LinearMap.toContinuousLinearMap (Submodule.subtype T)) hφ_int).symm
    _ = ∫ t, conj (π.character t) • ρ t x ∂μG := by
          refine integral_congr_ae ?_
          filter_upwards with t
          change Subtype.val (conj (π.character t) • ρS t ⟨x, hx⟩) =
            conj (π.character t) • ρ t x
          rfl

/-- Helper for Theorem 4-33: on a simple owner summand, the averaged character operator acts by
the scalar predicted by Proposition 4-27 and Theorem 4-15. -/
private theorem isotypicCharacterAverage_eq_pairing_smul_of_mem_simpleSubmodule
    [Representation.IsContinuous ρ]
    (π : Representation ℂ G W) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S]
    [Representation.IsContinuous ((Subrepresentation.ofSubmodule' S).toRepresentation)]
    {x : V} (hx : x ∈ S) :
    Representation.isotypicCharacterAverage ρ π x =
      ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) *
          (Representation.characterL2 ((Subrepresentation.ofSubmodule' S).toRepresentation) |
            Representation.characterL2 π)_G) : ℂ) • x := by
  let T : Submodule ℂ V := (Subrepresentation.ofSubmodule' S).toSubmodule
  let ρS : Representation ℂ G T := (Subrepresentation.ofSubmodule' S).toRepresentation
  letI : ρS.IsIrreducible := subrepresentation_toRepresentation_isIrreducible_of_isSimpleModule
    (ρ := ρ) S
  letI : Module ℂ[G] T := ρS.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] T := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule ρS).mp inferInstance
  letI : Nontrivial T := IsSimpleModule.nontrivial ℂ[G] T
  have hfinrankT : Module.finrank ℂ T = Module.finrank ℂ S := by
    calc
      Module.finrank ℂ T = Module.finrank ℂ ρS.asModule := by
        symm
        exact LinearEquiv.finrank_eq ρS.asModuleEquiv
      _ = Module.finrank ℂ S := by
        exact LinearEquiv.finrank_eq
          ((subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) S).restrictScalars ℂ)
  have hscalar :
      Representation.classFunctionAveragedEndomorphism ρS (fun t ↦ conj (π.character t)) =
        (((Module.finrank ℂ T : ℂ)⁻¹ *
            ∫ t, conj (π.character t) * ρS.character t ∂μG) : ℂ) •
          ContinuousLinearMap.id ℂ T := by
    -- Proposition 4-27 computes the source-facing class-function average on the simple summand.
    exact
      Representation.classFunctionAveragedEndomorphism_eq_characterIntegral_smul_id_of_isIrreducible
        ρS (fun t ↦ conj (π.character t))
        (continuous_conjCharacter (G := G) (π := π))
        (isClassFunction_conjCharacter (G := G) (π := π))
  have happly :
      Representation.isotypicCharacterAverage ρS π ⟨x, hx⟩ =
        ((((Module.finrank ℂ W : ℂ) *
            ((Module.finrank ℂ T : ℂ)⁻¹ *
              ∫ t, conj (π.character t) * ρS.character t ∂μG)) : ℂ)) •
          ⟨x, hx⟩ := by
    have happly_scalar :
        Representation.classFunctionAveragedEndomorphism ρS (fun t ↦ conj (π.character t))
            ⟨x, hx⟩ =
          (((Module.finrank ℂ T : ℂ)⁻¹ *
              ∫ t, conj (π.character t) * ρS.character t ∂μG) : ℂ) •
            ⟨x, hx⟩ := by
      -- Apply the scalar-operator identity to the chosen vector of the simple summand.
      simpa using congrArg (fun f : T →L[ℂ] T => f ⟨x, hx⟩) hscalar
    -- Expand the averaged operator once, then substitute the scalar action from Proposition 4-27.
    calc
      Representation.isotypicCharacterAverage ρS π ⟨x, hx⟩
          = (Module.finrank ℂ W : ℂ) •
              (Representation.classFunctionAveragedEndomorphism ρS
                (fun t ↦ conj (π.character t)) ⟨x, hx⟩) := by
                  simp [Representation.isotypicCharacterAverage]
      _ = (Module.finrank ℂ W : ℂ) •
            ((((Module.finrank ℂ T : ℂ)⁻¹ *
                ∫ t, conj (π.character t) * ρS.character t ∂μG) : ℂ) •
              ⟨x, hx⟩) := by
                rw [happly_scalar]
      _ = ((((Module.finrank ℂ W : ℂ) *
              ((Module.finrank ℂ T : ℂ)⁻¹ *
                ∫ t, conj (π.character t) * ρS.character t ∂μG)) : ℂ)) •
            ⟨x, hx⟩ := by
              simp [smul_smul]
  have hpair :
      ∫ t, conj (π.character t) * ρS.character t ∂μG =
        (Representation.characterL2 ρS | Representation.characterL2 π)_G := by
    -- Rewrite the character integral on `S` as the canonical `L²` pairing from Theorem 4-15.
    calc
      ∫ t, conj (π.character t) * ρS.character t ∂μG
        = ∫ t, ρS.character t * conj (π.character t) ∂μG := by
            refine integral_congr_ae ?_
            filter_upwards with t
            rw [mul_comm]
      _ = (Representation.characterL2 ρS | Representation.characterL2 π)_G := by
            symm
            exact Representation.characterL2_pairing_eq_characterIntegral ρS π
  -- Transport the scalar formula from the restricted representation back to the ambient space.
  calc
    Representation.isotypicCharacterAverage ρ π x
      = Subtype.val (Representation.isotypicCharacterAverage ρS π ⟨x, hx⟩) := by
          symm
          exact subtypeVal_isotypicCharacterAverage_ofSubmodule' (ρ := ρ) (π := π) S hx
    _ = ((((Module.finrank ℂ W : ℂ) *
            ((Module.finrank ℂ T : ℂ)⁻¹ *
              ∫ t, conj (π.character t) * ρS.character t ∂μG)) : ℂ)) • x := by
            simpa using congrArg Subtype.val happly
    _ = ((((Module.finrank ℂ W : ℂ) *
            ((Module.finrank ℂ T : ℂ)⁻¹ *
              (Representation.characterL2 ρS | Representation.characterL2 π)_G)) : ℂ)) • x := by
            rw [hpair]
    _ = ((((Module.finrank ℂ W : ℂ) *
            ((Module.finrank ℂ S : ℂ)⁻¹ *
              (Representation.characterL2 ρS | Representation.characterL2 π)_G)) : ℂ)) • x := by
            rw [hfinrankT]
    _ = ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) *
            (Representation.characterL2 ρS | Representation.characterL2 π)_G) : ℂ) • x := by
            congr 1
            rw [div_eq_mul_inv]
            ring

/-- Helper for Theorem 4-33: on a simple owner summand equivalent to `π`, the operator
`isotypicCharacterAverage ρ π` acts as the identity. -/
private theorem isotypicCharacterAverage_eq_self_of_mem_simpleSubmodule_of_equiv
    [Representation.IsContinuous ρ]
    (π : Representation ℂ G W) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S]
    [Representation.IsContinuous ((Subrepresentation.ofSubmodule' S).toRepresentation)]
    {x : V} (hx : x ∈ S)
    (hSπ : Nonempty (((Subrepresentation.ofSubmodule' S).toRepresentation).Equiv π)) :
    Representation.isotypicCharacterAverage ρ π x = x := by
  let T : Submodule ℂ V := (Subrepresentation.ofSubmodule' S).toSubmodule
  let ρS : Representation ℂ G T := (Subrepresentation.ofSubmodule' S).toRepresentation
  letI : ρS.IsIrreducible := subrepresentation_toRepresentation_isIrreducible_of_isSimpleModule
    (ρ := ρ) S
  letI : Module ℂ[G] W := π.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] W := by
    simpa using (Representation.irreducible_iff_isSimpleModule_asModule π).mp inferInstance
  letI : Nontrivial W := IsSimpleModule.nontrivial ℂ[G] W
  have hW_ne_zero : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  have hfinrankT : Module.finrank ℂ T = Module.finrank ℂ S := by
    calc
      Module.finrank ℂ T = Module.finrank ℂ ρS.asModule := by
        symm
        exact LinearEquiv.finrank_eq ρS.asModuleEquiv
      _ = Module.finrank ℂ S := by
        exact LinearEquiv.finrank_eq
          ((subrepresentation_ofSubmodule'_asModule_linearEquiv_local (ρ := ρ) S).restrictScalars ℂ)
  rcases hSπ with ⟨eSπ⟩
  have hpair_one :
      (Representation.characterL2 ρS | Representation.characterL2 π)_G = 1 := by
    -- Theorem 4-15 gives the orthonormality relation for equivalent irreducibles.
    exact
      Representation.characterPairing_eq_one_of_equiv_of_isIrreducible_of_isContinuousCompact
        ρS π eSπ
  have hfinrank : Module.finrank ℂ S = Module.finrank ℂ W := by
    calc
      Module.finrank ℂ S = Module.finrank ℂ T := by rw [hfinrankT]
      _ = Module.finrank ℂ W := LinearEquiv.finrank_eq eSπ.toLinearEquiv
  -- Substitute the character pairing and the matching dimensions into the scalar-action formula.
  calc
    Representation.isotypicCharacterAverage ρ π x
      = ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) *
          (Representation.characterL2 ρS | Representation.characterL2 π)_G) : ℂ) • x := by
            exact isotypicCharacterAverage_eq_pairing_smul_of_mem_simpleSubmodule
              (ρ := ρ) π S hx
    _ = ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) * 1) : ℂ) • x := by
          rw [hpair_one]
    _ = x := by
          rw [mul_one, hfinrank, div_self hW_ne_zero, one_smul]

/-- Helper for Theorem 4-33: on a simple owner summand not equivalent to `π`, the operator
`isotypicCharacterAverage ρ π` vanishes. -/
private theorem isotypicCharacterAverage_eq_zero_of_mem_simpleSubmodule_of_not_equiv
    [Representation.IsContinuous ρ]
    (π : Representation ℂ G W) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S]
    [Representation.IsContinuous ((Subrepresentation.ofSubmodule' S).toRepresentation)]
    {x : V} (hx : x ∈ S)
    (hSπ : ¬ Nonempty (((Subrepresentation.ofSubmodule' S).toRepresentation).Equiv π)) :
    Representation.isotypicCharacterAverage ρ π x = 0 := by
  let T : Submodule ℂ V := (Subrepresentation.ofSubmodule' S).toSubmodule
  let ρS : Representation ℂ G T := (Subrepresentation.ofSubmodule' S).toRepresentation
  letI : ρS.IsIrreducible := subrepresentation_toRepresentation_isIrreducible_of_isSimpleModule
    (ρ := ρ) S
  have hpair_zero :
      (Representation.characterL2 ρS | Representation.characterL2 π)_G = 0 := by
    -- Theorem 4-15 gives the orthogonality relation for nonisomorphic irreducibles.
    exact
      characterPairing_eq_zero_of_not_isomorphic_of_isIrreducible_of_isContinuousCompact
        ρS π hSπ
  -- The scalar in the simple-summand formula is zero by irreducible character orthogonality.
  calc
    Representation.isotypicCharacterAverage ρ π x
      = ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) *
          (Representation.characterL2 ρS | Representation.characterL2 π)_G) : ℂ) • x := by
            exact isotypicCharacterAverage_eq_pairing_smul_of_mem_simpleSubmodule
              (ρ := ρ) π S hx
    _ = ((((Module.finrank ℂ W : ℂ) / (Module.finrank ℂ S : ℂ)) * 0) : ℂ) • x := by
          rw [hpair_zero]
    _ = 0 := by
          simp

/-- Helper for Theorem 4-33: the operator `isotypicCharacterAverage ρ π` lands in the canonical
owner-level `π`-isotypic component on every simple summand. -/
private theorem isotypicCharacterAverage_mem_moduleIsotypicComponent_of_mem_simpleSubmodule
    [Representation.IsContinuous ρ]
    (π : Representation ℂ G W) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (S : Submodule ℂ[G] ρ.asModule) [IsSimpleModule ℂ[G] S]
    {x : V} (hx : x ∈ S) :
    Representation.isotypicCharacterAverage ρ π x ∈ ρ.moduleIsotypicComponent π := by
  letI : Representation.IsContinuous ((Subrepresentation.ofSubmodule' S).toRepresentation) :=
    subrepresentation_toRepresentation_isContinuous (ρ := ρ) (Subrepresentation.ofSubmodule' S)
  by_cases hSπ : Nonempty (((Subrepresentation.ofSubmodule' S).toRepresentation).Equiv π)
  · -- On `π`-type summands, the operator is the identity and the summand is contained in the
    -- canonical isotypic component.
    rw [isotypicCharacterAverage_eq_self_of_mem_simpleSubmodule_of_equiv
      (ρ := ρ) π S hx hSπ]
    exact (simpleSubmodule_le_moduleIsotypicComponent_iff_equiv (ρ := ρ) π S).2 hSπ hx
  · -- On the other simple summands, the operator vanishes.
    rw [isotypicCharacterAverage_eq_zero_of_mem_simpleSubmodule_of_not_equiv
      (ρ := ρ) π S hx hSπ]
    exact ((ρ.moduleIsotypicComponent π).zero_mem :
      (0 : V) ∈ ρ.moduleIsotypicComponent π)

/-- Helper for Theorem 4-33: the operator `isotypicCharacterAverage ρ π` is the identity on the
whole owner-level `π`-isotypic component. -/
private theorem isotypicCharacterAverage_eq_self_of_mem_piIsotypicComponent
    [Representation.IsContinuous ρ]
    (π : Representation ℂ G W) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    {v : V} (hv : v ∈ ρ.moduleIsotypicComponent π) :
    Representation.isotypicCharacterAverage ρ π v = v := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower ℂ ℂ[G] V := by
    simpa [Representation.asModule] using (inferInstance : IsScalarTower ℂ ℂ[G] ρ.asModule)
  letI : IsSemisimpleModule ℂ[G] V := ρ.ownerIsSemisimpleModule
  let N : Submodule ℂ[G] V := ρ.moduleIsotypicComponent π
  have hsup :
      (⨆ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S ∧ S ≤ N), S) = N := by
    -- Semisimplicity spans the isotypic component by its simple constituents.
    simpa [sSup_eq_iSup] using
      (IsSemisimpleModule.sSup_simples_le (R := ℂ[G]) (M := V) N)
  have hspan :
      Submodule.span ℂ
        (⋃ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S ∧ S ≤ N),
          (((S.restrictScalars ℂ : Submodule ℂ V) : Set V))) =
      N.restrictScalars ℂ := by
    rw [← Submodule.iSup_eq_span'
      (p := fun S : Submodule ℂ[G] V ↦ S.restrictScalars ℂ)
      (h := fun S ↦ IsSimpleModule ℂ[G] S ∧ S ≤ N)]
    simpa using congrArg (Submodule.restrictScalars ℂ) hsup
  have hv_span :
      v ∈ Submodule.span ℂ
        (⋃ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S ∧ S ≤ N),
          (((S.restrictScalars ℂ : Submodule ℂ V) : Set V))) := by
    rw [hspan]
    simpa [N] using hv
  -- Reduce to the simple constituents inside the `π`-isotypic component.
  refine Submodule.span_induction
    (p := fun x _ ↦ Representation.isotypicCharacterAverage ρ π x = x)
    ?_ ?_ ?_ ?_ hv_span
  · intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨S, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hSN, hx⟩
    let Sρ : Submodule ℂ[G] ρ.asModule := S
    letI : IsSimpleModule ℂ[G] Sρ := hSN.1
    letI : Representation.IsContinuous ((Subrepresentation.ofSubmodule' Sρ).toRepresentation) :=
      subrepresentation_toRepresentation_isContinuous (ρ := ρ) (Subrepresentation.ofSubmodule' Sρ)
    have hSπ :
        Nonempty (((Subrepresentation.ofSubmodule' Sρ).toRepresentation).Equiv π) :=
      (simpleSubmodule_le_moduleIsotypicComponent_iff_equiv (ρ := ρ) π Sρ).1 hSN.2
    exact isotypicCharacterAverage_eq_self_of_mem_simpleSubmodule_of_equiv
      (ρ := ρ) π Sρ (by simpa [Sρ] using hx) hSπ
  · simp [Representation.isotypicCharacterAverage]
  · intro x y hx hy hfx hfy
    calc
      Representation.isotypicCharacterAverage ρ π (x + y)
        = Representation.isotypicCharacterAverage ρ π x +
            Representation.isotypicCharacterAverage ρ π y := by
              exact LinearMap.map_add (Representation.isotypicCharacterAverage ρ π) x y
      _ = x + y := by rw [hfx, hfy]
  · intro a x hx hfx
    calc
      Representation.isotypicCharacterAverage ρ π (a • x)
        = a • Representation.isotypicCharacterAverage ρ π x := by
              exact LinearMap.map_smul (Representation.isotypicCharacterAverage ρ π) a x
      _ = a • x := by rw [hfx]

/-- Theorem 4-33 (2): the explicit operator `isotypicCharacterAverage ρ π` is the projection onto
the canonical `π`-isotypic component of `ρ`. -/
theorem piIsotypicCharacterAverage_isProj
    [Representation.IsContinuous ρ]
    (π : Representation ℂ G W) [Representation.IsContinuous π] [Representation.IsIrreducible π] :
    LinearMap.IsProj ((ρ.moduleIsotypicComponent π).restrictScalars ℂ)
      (isotypicCharacterAverage ρ π) := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower ℂ ℂ[G] V := by
    simpa [Representation.asModule] using (inferInstance : IsScalarTower ℂ ℂ[G] ρ.asModule)
  letI : IsSemisimpleModule ℂ[G] V := ρ.ownerIsSemisimpleModule
  have hsup :
      (⨆ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S), S) =
        (⊤ : Submodule ℂ[G] V) := by
    -- Semisimplicity spans the ambient owner module by its simple submodules.
    simpa [sSup_eq_iSup] using
      (IsSemisimpleModule.sSup_simples_eq_top (R := ℂ[G]) (M := V))
  have hspan :
      Submodule.span ℂ
        (⋃ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S),
          (((S.restrictScalars ℂ : Submodule ℂ V) : Set V))) =
      (⊤ : Submodule ℂ V) := by
    rw [← Submodule.iSup_eq_span'
      (p := fun S : Submodule ℂ[G] V ↦ S.restrictScalars ℂ)
      (h := fun S ↦ IsSimpleModule ℂ[G] S)]
    simpa using congrArg (Submodule.restrictScalars ℂ) hsup
  have hmap_mem :
      ∀ x : V, Representation.isotypicCharacterAverage ρ π x ∈
        (ρ.moduleIsotypicComponent π).restrictScalars ℂ := by
    intro x
    have hx_span :
        x ∈ Submodule.span ℂ
          (⋃ (S : Submodule ℂ[G] V) (_ : IsSimpleModule ℂ[G] S),
            (((S.restrictScalars ℂ : Submodule ℂ V) : Set V))) := by
      rw [hspan]
      simp
    -- Check the image on each simple constituent, then extend by linearity.
    refine Submodule.span_induction
      (p := fun y _ ↦ Representation.isotypicCharacterAverage ρ π y ∈
        (ρ.moduleIsotypicComponent π).restrictScalars ℂ) ?_ ?_ ?_ ?_ hx_span
    · intro y hy
      rcases Set.mem_iUnion.1 hy with ⟨S, hy⟩
      rcases Set.mem_iUnion.1 hy with ⟨hS, hy⟩
      let Sρ : Submodule ℂ[G] ρ.asModule := S
      letI : IsSimpleModule ℂ[G] Sρ := hS
      simpa using isotypicCharacterAverage_mem_moduleIsotypicComponent_of_mem_simpleSubmodule
        (ρ := ρ) π Sρ (by simpa [Sρ] using hy)
    · have hzero : (0 : V) ∈ (ρ.moduleIsotypicComponent π).restrictScalars ℂ :=
        ((ρ.moduleIsotypicComponent π).restrictScalars ℂ).zero_mem
      simpa using hzero
    · intro x y hx hy hxmem hymem
      simpa using ((ρ.moduleIsotypicComponent π).restrictScalars ℂ).add_mem hxmem hymem
    · intro a y hy hymem
      simpa using ((ρ.moduleIsotypicComponent π).restrictScalars ℂ).smul_mem a hymem
  have hid :
      ∀ x ∈ (ρ.moduleIsotypicComponent π).restrictScalars ℂ,
        Representation.isotypicCharacterAverage ρ π x = x := by
    intro x hx
    simpa using isotypicCharacterAverage_eq_self_of_mem_piIsotypicComponent
      (ρ := ρ) π hx
  -- The averaged operator has the right image and restricts to the identity on that image.
  exact LinearMap.IsProj.mk hmap_mem hid

/-- Companion form of Theorem 4-33 (2): if the canonical summand `c` is the `π`-isotypic
component of `ρ`, then the explicit operator `isotypicCharacterAverage ρ π` is the projection
onto that summand. -/
theorem isotypicCharacterAverage_isProj
    [Representation.IsContinuous ρ]
    (c : ρ.isotypicComponentsSet)
    (π : Representation ℂ G W) [Representation.IsContinuous π] [Representation.IsIrreducible π]
    (hcπ : c.1 = ρ.moduleIsotypicComponent π) :
    LinearMap.IsProj (ρ.isotypicSubmoduleFamily c) (isotypicCharacterAverage ρ π) := by
  simpa [isotypicSubmoduleFamily_apply, hcπ] using ρ.piIsotypicCharacterAverage_isProj π

end

end Representation
