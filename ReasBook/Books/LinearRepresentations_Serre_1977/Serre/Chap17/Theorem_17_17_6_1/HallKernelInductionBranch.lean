import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.FixedConstituentBasicSetup
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.QuotientHeightRecursion
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.HallKernelCliffordSplit
import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_3_1.StandardInducedModelLift

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

local notation "k" => IsLocalRing.ResidueField A
private noncomputable instance theorem171761TargetModule : Module A V :=
  Module.compHom V (algebraMap A k)
private instance theorem171761TargetScalarTower : IsScalarTower A k V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- Helper for Theorem 17-17.6-1: a lifted `A[G']`-representation may be moved into the common
witness universe by `ULift` without changing its action. -/
def uliftRepresentation_witness
    {G' : Type v} [Group G']
    {P : Type u} [AddCommGroup P] [Module A P]
    (ρA : Representation A G' P) :
    Representation A G' (ULift.{max v x, u} P) where
  toFun g :=
    { toFun := fun p ↦ ⟨ρA g p.down⟩
      map_add' := by
        intro p q
        ext
        simp
      map_smul' := by
        intro a p
        ext
        simp }
  map_one' := by
    ext p
    simp
  map_mul' g h := by
    ext p
    simp [map_mul]

/-- Helper for Theorem 17-17.6-1: raising the lifted source carrier to the common witness universe
preserves the residue-field lift. -/
theorem residueFieldLift_ulift_witness
    {G' : Type v} [Group G'] [Finite G']
    {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    {P : Type u} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {ρ : Representation k G' V'}
    {ρA : Representation A G' P}
    {red : P →ₗ[A] V'}
    (hLift : IsResidueFieldLift ρ ρA red) :
    IsResidueFieldLift ρ (uliftRepresentation_witness (A := A) ρA)
      (red.comp (ULift.moduleEquiv : ULift.{max v x, u} P ≃ₗ[A] P).toLinearMap) := by
  -- Specialize the general source-side transport bridge to the `ULift` carrier equivalence.
  let eU :
      (uliftRepresentation_witness (A := A) ρA).Equiv ρA :=
    Representation.Equiv.mk ULift.moduleEquiv fun g ↦ by
      -- Both actions are definitionally the same after inserting the `ULift` wrapper.
      ext x
      rfl
  simpa using
    residueFieldLift_of_equiv_source_local (A := A) (ρ := ρ) (ρA := ρA) hLift eU

/-- Helper for Theorem 17-17.6-1: any free finite `A[G']`-model can be transported to the
same-universe coordinate module `Fin (finrank_A P) → A`, and the residue-field lift transports
along that source equivalence. -/
theorem residueFieldLift_same_universe_witness
    {G' : Type v} [Group G'] [Finite G']
    {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    {P : Type*} [AddCommGroup P] [Module A P]
    [Module.Free A P] [Module.Finite A P]
    {ρ : Representation k G' V'}
    {ρA : Representation A G' P}
    {red : P →ₗ[A] V'}
    (hLift : IsResidueFieldLift ρ ρA red) :
    ∃ (P' : Type u) (_ : AddCommGroup P') (_ : Module A P')
      (_ : Module.Free A P') (_ : Module.Finite A P')
      (ρA' : Representation A G' P')
      (red' : P' →ₗ[A] V'),
        IsResidueFieldLift ρ ρA' red' := by
  letI : Module A A := Semiring.toModule
  let n := Module.finrank A P
  let P' : Type u := Fin n → A
  letI : AddCommGroup P' := Pi.addCommGroup
  letI : Module A P' := Pi.Function.module (Fin n) A A
  letI : Module.Free A P' := Module.Free.of_basis (Pi.basisFun A (Fin n))
  letI : Module.Finite A P' := Module.Finite.of_basis (Pi.basisFun A (Fin n))
  let e : P ≃ₗ[A] P' := (Module.finBasis A P).equivFun
  let ρA' : Representation A G' P' :=
    { toFun := fun g ↦ e.conj (ρA g)
      map_one' := by
        calc
          e.conj (ρA 1) = e.conj 1 := by rw [map_one]
          _ = 1 := LinearEquiv.conj_id _
      map_mul' := by
        intro g h
        rw [map_mul]
        ext x
        simp [LinearEquiv.conj_apply_apply] }
  let eRep : ρA'.Equiv ρA :=
    Representation.Equiv.mk e.symm fun g ↦ by
      apply LinearMap.ext
      intro x
      change e.symm (e (ρA g (e.symm x))) = ρA g (e.symm x)
      simp
  refine
    ⟨P', inferInstance, inferInstance, inferInstance, inferInstance, ρA',
      red.comp e.symm.toLinearMap, ?_⟩
  simpa using
    residueFieldLift_of_equiv_source_local (A := A) (ρ := ρ) (ρA := ρA)
      hLift eRep

/-- Helper for Theorem 17-17.6-1: the Chapter `17.3` prime-to-`p` lifting theorem can be
repackaged into the common witness universe used by this file. -/
theorem exists_residueFieldLift_of_non_dvd_card_witness
    {G' : Type v} [Group G'] [Finite G']
    {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    (hGcop : ¬ p ∣ Nat.card G')
    (ρ : Representation k G' V') :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G' P)
      (red : P →ₗ[A] V'),
        IsResidueFieldLift ρ ρA red := by
  -- Choose the Chapter `17.3` lift in universe `u`, then move it into the common witness
  -- universe by `ULift`.
  rcases
      Representation.exists_residueFieldLift_of_non_dvd_card
        (A := A) (p := p) (H := G') hGcop ρ with
    ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
  letI : AddCommGroup P := hPadd
  letI : Module A P := hPmod
  letI : Module.Free A P := hPfree
  letI : Module.Finite A P := hPfinite
  refine
    ⟨ULift.{max v x, u} P, inferInstance, inferInstance, inferInstance, inferInstance,
      uliftRepresentation_witness (A := A) ρA,
      red.comp (ULift.moduleEquiv : ULift.{max v x, u} P ≃ₗ[A] P).toLinearMap, ?_⟩
  exact residueFieldLift_ulift_witness (A := A) (ρ := ρ) hLift

/-- Helper for Theorem 17-17.6-1: if a normal subgroup acts trivially and the quotient lift is
already known in the common witness universe, inflating it back yields a lift of the ambient
representation in the same witness universe. -/
theorem exists_residueFieldLift_of_ofQuotient_of_isTrivial_witness
    {G' : Type v} [Group G'] [Finite G']
    {V' : Type x} [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
    (ρ : Representation k G' V')
    (I : Subgroup G') [I.Normal]
    [Representation.IsTrivial (ρ.comp I.subtype)]
    (hquotLift :
      ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
        (_ : Module.Free A P) (_ : Module.Finite A P)
        (ρA : Representation A (G' ⧸ I) P)
        (red : P →ₗ[A] V'),
          IsResidueFieldLift (ρ.ofQuotient I) ρA red) :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G' P)
      (red : P →ₗ[A] V'),
        IsResidueFieldLift ρ ρA red := by
  rcases hquotLift with ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA, red, hLift⟩
  letI : AddCommGroup P := hPadd
  letI : Module A P := hPmod
  letI : Module.Free A P := hPfree
  letI : Module.Finite A P := hPfinite
  -- Inflate the quotient lift and then rewrite the source representation by the trivial-kernel
  -- comparison from the quotient recursion helper file.
  refine ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA.comp (QuotientGroup.mk' I), red, ?_⟩
  have hLift' :
      IsResidueFieldLift
        ((ρ.ofQuotient I).comp (QuotientGroup.mk' I))
        (ρA.comp (QuotientGroup.mk' I))
        red :=
    Representation.isResidueFieldLift_comp hLift (QuotientGroup.mk' I)
  rw [quotient_inflation_eq_original_of_isTrivial (ρ := ρ) (I := I)]
  exact hLift'

/-- Helper for Theorem 17-17.6-1: in the proper-overgroup branch, the same-height recursion on the
stabilizer overgroup already produces a residue-field lift of the inducing subrepresentation. -/
theorem exists_residueFieldLift_of_proper_overgroup_subrepresentation
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (hquot : IsPSolvableOfHeight p h (G ⧸ I))
    (hrecSame :
      ∀ {H : Subgroup G} {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
        (hH : H < ⊤)
        (hHG : IsPSolvableOfHeight p (Nat.succ h) H)
        (σ : Representation k H W) [σ.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A H P)
            (red : P →ₗ[A] W),
              IsResidueFieldLift σ ρA red)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hproper :
      ∃ H : Subgroup G,
        I ≤ H ∧ H < ⊤ ∧
          ∃ W : Subrepresentation (ρ.comp H.subtype),
            W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) :
    ∃ H : Subgroup G, ∃ hIH : I ≤ H, ∃ hHlt : H < ⊤,
      ∃ W : Subrepresentation (ρ.comp H.subtype),
        ∃ hInd : ρ.IsInducedFromSubrepresentation H W,
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A H P)
            (red : P →ₗ[A] W.toSubmodule),
              IsResidueFieldLift W.toRepresentation ρA red := by
  rcases hproper with ⟨H, hIH, hHlt, W, hWirred, hInd⟩
  have hHquot :
      IsPSolvableOfHeight p h (H.map (QuotientGroup.mk' I)) := by
    -- The quotient image of the stabilizer overgroup inherits the lower-height hypothesis.
    exact (proper_overgroup_quotient_data (p := p) (h := h) I H hIH hHlt hquot).2.1
  have hHsolv : IsPSolvableOfHeight p (Nat.succ h) H := by
    -- Reinsert the same coprime Hall kernel inside `H` to recover the same-height recursion.
    exact
      isPSolvableOfHeight_succ_of_normal_coprime_subgroup_and_quotient_map
        (p := p) (h := h) I H hIH hIcop hHquot
  letI : W.toRepresentation.IsIrreducible := hWirred
  rcases hrecSame hHlt hHsolv W.toRepresentation with
    ⟨P, hPadd, hPmod, hPfree, hPfinite, ρA_H, red_H, hLiftH⟩
  -- This packages the entire recursive subgroup step so the ambient branch only has to induce
  -- the resulting lift back to `G`.
  exact
    ⟨H, hIH, hHlt, W, hInd, P, hPadd, hPmod, hPfree, hPfinite, ρA_H, red_H, hLiftH⟩

/-- Helper for Theorem 17-17.6-1: once the Clifford split lands in the proper-overgroup branch,
the remaining work is to recurse on that subgroup and transport the lift back across induction. -/
theorem exists_residueFieldLift_of_proper_overgroup_induced_hall
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (hquot : IsPSolvableOfHeight p h (G ⧸ I))
    (hrecSame :
      ∀ {H : Subgroup G} {W : Type x} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
        (hH : H < ⊤)
        (hHG : IsPSolvableOfHeight p (Nat.succ h) H)
        (σ : Representation k H W) [σ.IsIrreducible],
          ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
            (_ : Module.Free A P) (_ : Module.Finite A P)
            (ρA : Representation A H P)
            (red : P →ₗ[A] W),
              IsResidueFieldLift σ ρA red)
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hproper :
      ∃ H : Subgroup G,
        I ≤ H ∧ H < ⊤ ∧
          ∃ W : Subrepresentation (ρ.comp H.subtype),
            W.toRepresentation.IsIrreducible ∧ ρ.IsInducedFromSubrepresentation H W) :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  rcases
      exists_residueFieldLift_of_proper_overgroup_subrepresentation
        (A := A) (p := p) (h := h) I hIcop hquot hrecSame ρ hproper with
    ⟨H, hIH, hHlt, W, hInd, P, hPadd, hPmod, hPfree, hPfinite, ρA_H, red_H, hLiftH⟩
  letI : AddCommGroup P := hPadd
  letI : Module A P := hPmod
  letI : Module.Free A P := hPfree
  letI : Module.Finite A P := hPfinite
  -- Route correction: reuse the Chapter `17.3` induced-transport helper directly. In this file,
  -- the proper-overgroup branch should only supply the recursive subgroup lift and the inducedness
  -- witness, not reprove the standard induced-model transport a second time.
  let _ := hp
  rcases
      residueFieldLift_same_universe_witness
        (A := A) (ρ := W.toRepresentation) hLiftH with
    ⟨P', hP'add, hP'mod, hP'free, hP'finite, ρA_H', red_H', hLiftH'⟩
  letI : AddCommGroup P' := hP'add
  letI : Module A P' := hP'mod
  letI : Module.Free A P' := hP'free
  letI : Module.Finite A P' := hP'finite
  rcases
    exists_residueFieldLift_of_isInducedFromSubrepresentation_local
      (A := A) (G := G) (V := V) ρ W ρA_H' red_H' hLiftH' hInd with
    ⟨P'', hP''add, hP''mod, hP''free, hP''finite, ρA, red, hLift⟩
  letI : AddCommGroup P'' := hP''add
  letI : Module A P'' := hP''mod
  letI : Module.Free A P'' := hP''free
  letI : Module.Finite A P'' := hP''finite
  refine
    ⟨ULift.{max v x, u} P'', inferInstance, inferInstance, inferInstance, inferInstance,
      uliftRepresentation_witness (A := A) ρA,
      red.comp (ULift.moduleEquiv : ULift.{max v x, u} P'' ≃ₗ[A] P'').toLinearMap, ?_⟩
  exact residueFieldLift_ulift_witness (A := A) (ρ := ρ) hLift

/-- Helper for Theorem 17-17.6-1: in the isotypic Hall-kernel branch, one can already choose
Serre's irreducible constituent `S̄` and show that its owner isotypic component is all of the
restricted module. -/
theorem exists_irreducible_constituent_with_isotypic_component_top_of_isotypic_restriction
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (hIsotypic :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      IsIsotypic (MonoidAlgebra k I) V) :
    let ρI : Representation k I V := ρ.comp I.subtype
    letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
    ∃ Sbar : Subrepresentation ρI,
      Sbar.toRepresentation.IsIrreducible ∧
        @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
          inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤ := by
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  have hsemisimple : IsSemisimpleModule (MonoidAlgebra k I) V :=
    isSemisimpleModule_restrict_of_coprime_card hp I hIcop ρ
  letI : IsSemisimpleModule (MonoidAlgebra k I) V := hsemisimple
  have hV_nontrivial : Nontrivial V := nontrivial_of_isIrreducible_local_c17 (ρ := ρ)
  letI : Nontrivial V := hV_nontrivial
  -- Route correction: choose Serre's constituent first as a simple owner `k[I]`-submodule of the
  -- restricted module, and only then repackage it as a bundled irreducible subrepresentation.
  obtain ⟨N, -, hNsimple⟩ :=
    (IsSemisimpleModule.eq_bot_or_exists_simple_le
      (R := MonoidAlgebra k I) (M := V) (⊤ : Submodule (MonoidAlgebra k I) V)).resolve_left
        top_ne_bot
  let Sbar : Subrepresentation ρI := Subrepresentation.ofSubmodule' N
  have hSbar_irred : Sbar.toRepresentation.IsIrreducible := by
    -- Chapter `1` upgrades the chosen simple owner submodule to an irreducible constituent.
    exact
      isIrreducible_toRepresentation_of_isSimpleModule_asSubmodule_without_neZero
        ρI N hNsimple
  have hN_top : isotypicComponent (MonoidAlgebra k I) V N = ⊤ := by
    letI : IsSimpleModule (MonoidAlgebra k I) N := hNsimple
    -- The ambient restricted module is already isotypic, so the component of this constituent is
    -- the whole module.
    exact (isotypicComponent_eq_top_iff (R := MonoidAlgebra k I) (M := V) (S := N)).2
      (hIsotypic N)
  refine ⟨Sbar, hSbar_irred, ?_⟩
  simpa [Sbar] using hN_top

/-- Helper for Theorem 17-17.6-1: the chosen irreducible constituent `S̄` should be simple as an
owner `k[I]`-submodule of the restricted module. This is the precise intrinsic-to-owner transport
needed before invoking the owner-module isotypic decomposition API. -/
theorem chosen_constituent_owner_simple
    (I : Subgroup G)
    (ρ : Representation k G V)
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible) :
    @IsSimpleModule (MonoidAlgebra k I) inferInstance Sbar.asSubmodule inferInstance
      Sbar.asSubmodule.module := by
  let ρS : Representation k I Sbar.toSubmodule := Sbar.toRepresentation
  letI : Module (MonoidAlgebra k I) ρS.asModule := ρS.instModuleMonoidAlgebraAsModule
  -- Move Serre's chosen constituent from the intrinsic carrier `S̄.toSubmodule` to the owner
  -- submodule `S̄.asSubmodule` using the canonical owner/intrinsic linear equivalence.
  exact
    @IsSimpleModule.congr (MonoidAlgebra k I) inferInstance Sbar.asSubmodule
      Sbar.asSubmodule.addCommGroup Sbar.asSubmodule.module
      ρS.asModule ρS.instAddCommGroupAsModule ρS.instModuleMonoidAlgebraAsModule
      (subrepresentation_owner_intrinsic_linearEquiv_local_c17 (ρ := ρ.comp I.subtype) Sbar).symm
      ((Representation.irreducible_iff_isSimpleModule_asModule ρS).mp hSbar_irred)

/-- Helper for Theorem 17-17.6-1: once the chosen constituent `S̄` fills the whole isotypic
component of the restricted module, the owner `k[I]`-module `V` can already be rigidified onto a
finite coordinate model `Fin n → S̄`. This is Serre's first fixed-object checkpoint before the
projective-extension cover is introduced. -/
theorem exists_linearEquiv_pi_of_isotypic_component_top
    (hp : Nat.Prime p)
    (I : Subgroup G) [I.Normal]
    (hIcop : Nat.Coprime p (Nat.card I))
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (Sbar : Subrepresentation (ρ.comp I.subtype))
    (hSbar_irred : Sbar.toRepresentation.IsIrreducible)
    (hSbar_top :
      let ρI : Representation k I V := ρ.comp I.subtype
      letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
      @isotypicComponent (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module = ⊤) :
    let ρI : Representation k I V := ρ.comp I.subtype
    letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
    ∃ n : ℕ, Nonempty (V ≃ₗ[MonoidAlgebra k I] Fin n → Sbar.asSubmodule) := by
  let ρI : Representation k I V := ρ.comp I.subtype
  letI : Module (MonoidAlgebra k I) V := ρI.instModuleMonoidAlgebraAsModule
  letI : IsScalarTower k (MonoidAlgebra k I) V :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      change ρI.asAlgebraHom (algebraMap k (MonoidAlgebra k I) a) x = a • x
      simpa [Algebra.smul_def] using LinearMap.congr_fun (ρI.asAlgebraHom.commutes a) x
  letI : IsSemisimpleModule (MonoidAlgebra k I) V :=
    isSemisimpleModule_restrict_of_coprime_card hp I hIcop ρ
  letI : Module.Finite (MonoidAlgebra k I) V :=
    Module.Finite.of_restrictScalars_finite k (MonoidAlgebra k I) V
  letI : Nontrivial V := nontrivial_of_isIrreducible_local_c17 (ρ := ρ)
  letI hSimple :
      @IsSimpleModule (MonoidAlgebra k I) inferInstance Sbar.asSubmodule inferInstance
        Sbar.asSubmodule.module :=
    chosen_constituent_owner_simple (I := I) (ρ := ρ) (Sbar := Sbar) hSbar_irred
  have hType :
      @IsIsotypicOfType (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module := by
    -- The chosen constituent already controls the whole restricted module.
    exact
      (@isotypicComponent_eq_top_iff (MonoidAlgebra k I) V Sbar.asSubmodule
        inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module
        hSimple inferInstance).mp hSbar_top
  rcases
    @IsIsotypicOfType.linearEquiv_fun (MonoidAlgebra k I) V Sbar.asSubmodule
      inferInstance inferInstance inferInstance inferInstance Sbar.asSubmodule.module
      inferInstance inferInstance hType with ⟨n, e⟩
  exact ⟨n, e⟩

end

end Representation
