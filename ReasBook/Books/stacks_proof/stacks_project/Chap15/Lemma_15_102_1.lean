import Mathlib
import StacksProject_2024.Chap04.Example_4_22_6
import StacksProject_2024.Chap10.Lemma_10_51_3
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap15.Lemma_15_102_Basic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Limits
open Opposite
open SequentialProObjectMorphismRep
open scoped IdealPowerSubmodule

noncomputable section

universe u v

namespace CategoryTheory.ShortComplex

variable {A : Type u} [CommRing A]

local notation "Mod" => ModuleCat A
local notation "SeqMod" => SequentialInverseSystem Mod

/- Domain-style sampling for `15.102.1`:
- primary domain: homology of short complexes of finite modules and the induced `I`-adic inverse
  systems;
- sampled core/canonical owners:
  `ShortComplex.leftHomology`,
  `ShortComplex.leftHomologyMap`,
  `ShortComplex.map`,
  `ShortComplex.mapNatTrans`,
  `Functor.ofOpSequence`,
  `SequentialProObjectMorphismRep.IsProIsomorphism`,
  `Submodule.pow_smul_top_le`;
- best owner abstraction: the ambient short complex `S : ShortComplex (ModuleCat A)` should own
  the ideal-power stage complexes, the ambient homology `S.leftHomology`, and the induced towers;
  the ideal-power stage maps should be induced from the owner-level short-complex APIs
  `ShortComplex.map` and `ShortComplex.mapNatTrans`, the inverse systems should use the canonical
  owner `Functor.ofOpSequence`, and the resulting pro-comparison should live in
  `SequentialProObjectMorphismRep` with owner property `r.IsProIsomorphism`;
- primitive data: the short complex `S` together with the ideal-power submodules
  `I^n S.X₁`, `I^n S.X₂`, and `I^n S.X₃`;
- derived API: the stage homology objects, their transition maps, the map to the ambient
  homology, and the eventual comparison data;
-- source/core/bridge triage:
  `source-facing`: the eventual comparison between filtered homology and the `I`-adic filtration on
    ambient homology;
  `core/canonical`: `ShortComplex.leftHomology`, `ShortComplex.leftHomologyMap`,
    `ShortComplex.map`, `ShortComplex.mapNatTrans`, `Functor.ofOpSequence`,
    `idealPowerSubmodule`, and
    `SequentialProObjectMorphismRep.IsProIsomorphism`;
  `bridge/view`: the ideal-power stage complexes and the induced maps from those stages to `S`. -/

section Comparison

variable (S : ShortComplex Mod) (I : Ideal A)

/-- The `n`th ideal-power subcomplex of `S`. -/
abbrev idealPowerSubmoduleStageComplex
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) : ShortComplex Mod :=
  S.map (idealPowerSubmoduleFunctor I n)

instance idealPowerSubmoduleStageComplex_hasLeftHomology
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    (S.idealPowerSubmoduleStageComplex I n).HasLeftHomology := by
  let T : ShortComplex Mod := S.idealPowerSubmoduleStageComplex I n
  let _ : HasKernel T.g := inferInstance
  let _ : HasCokernel (kernel.lift T.g T.f T.zero) := inferInstance
  exact HasLeftHomology.mk' (LeftHomologyData.ofHasKernelOfHasCokernel T)

/-- The homology object `H[n]` of the `n`th ideal-power subcomplex of `S`. -/
abbrev idealPowerSubmoduleHomologyStage
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) : Mod :=
  (S.idealPowerSubmoduleStageComplex I n).leftHomology

/-- The canonical map from the homology of the `n`th ideal-power subcomplex to the ambient left
homology of `S`, induced by the inclusion `I^[n] S ⟶ S`. -/
abbrev idealPowerSubmoduleHomologyToLeftHomology
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.idealPowerSubmoduleHomologyStage I n ⟶ S.leftHomology :=
  leftHomologyMap <| S.mapNatTrans (idealPowerSubtypeNatTrans I n)

/-- The transition map `(H[n+1]) ⟶ H[n]` on the homology tower of the ideal-power subcomplexes of
`S`. -/
abbrev idealPowerSubmoduleHomologyStep
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.idealPowerSubmoduleHomologyStage I (n + 1) ⟶
      S.idealPowerSubmoduleHomologyStage I n :=
  leftHomologyMap <| S.mapNatTrans (idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ n))

/-- The inverse system `(H[n])_n` obtained by taking left homology of the ideal-power
subcomplexes of `S`. -/
abbrev idealPowerSubmoduleHomologyTower
    (S : ShortComplex Mod) (I : Ideal A) : SeqMod :=
  Functor.ofOpSequence (fun n ↦ S.idealPowerSubmoduleHomologyStep I n)

/-- The `n`th ideal-power stage `I^[n] H` of the ambient left homology `H = S.leftHomology`. -/
abbrev leftHomologyIdealPowerStage
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) : Mod :=
  idealPowerStage I n S.leftHomology

/-- The transition map `I^[n+1] H ⟶ I^[n] H` on the ideal-power tower of the ambient left homology
`H = S.leftHomology`. -/
abbrev leftHomologyIdealPowerStep
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.leftHomologyIdealPowerStage I (n + 1) ⟶ S.leftHomologyIdealPowerStage I n :=
  ModuleCat.ofHom <|
    Submodule.inclusion
      (show I^[n + 1] S.leftHomology ≤ I^[n] S.leftHomology from
        idealPowerSubmodule_mono I (Nat.le_succ n))

/-- The inverse system `(I^[n] H)_n` on the ambient left homology `H = S.leftHomology`. -/
abbrev leftHomologyIdealPowerTower
    (S : ShortComplex Mod) (I : Ideal A) : SeqMod :=
  Functor.ofOpSequence (fun n ↦ S.leftHomologyIdealPowerStep I n)

variable [IsNoetherianRing A]
variable [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃]

/-- Arithmetic helper for the shifted transition maps in Lemma 15.102.1. -/
theorem shiftComparison_le (n c : ℕ) :
    n ≤ c + (c + n) := by
  exact (Nat.le_add_left n c).trans (Nat.le_add_left (c + n) c)

/-- Helper for Lemma 15.102.1: a cycle in the `n`th ideal-power stage complex is still an ambient
cycle in `S`. -/
private theorem idealPowerSubmoduleStageCyclesToCycles_mem
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    ∀ x : LinearMap.ker (S.idealPowerSubmoduleStageComplex I n).g.hom,
      ((idealPowerSubtype I n S.X₂).comp
          (LinearMap.ker (S.idealPowerSubmoduleStageComplex I n).g.hom).subtype) x ∈
        LinearMap.ker S.g.hom := by
  intro x
  -- A cycle in the stage complex is, by definition, an element of `I^[n] S.X₂` annihilated by
  -- the restricted differential; forgetting the stage places it in the ambient kernel.
  change idealPowerSubtype I n S.X₃ ((S.idealPowerSubmoduleStageComplex I n).g.hom x.1) = 0
  have hx : (S.idealPowerSubmoduleStageComplex I n).g.hom x.1 = 0 := by
    simpa [LinearMap.mem_ker] using x.2
  simpa using congrArg (idealPowerSubtype I n S.X₃) hx

/-- Helper for Lemma 15.102.1: the cycles of the `n`th ideal-power stage map canonically to the
ambient cycles of `S`. -/
private abbrev idealPowerSubmoduleStageCyclesToCycles
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    LinearMap.ker (S.idealPowerSubmoduleStageComplex I n).g.hom →ₗ[A]
      LinearMap.ker S.g.hom :=
  (((idealPowerSubtype I n S.X₂).comp
      (LinearMap.ker (S.idealPowerSubmoduleStageComplex I n).g.hom).subtype).codRestrict
        (LinearMap.ker S.g.hom)
        (idealPowerSubmoduleStageCyclesToCycles_mem S I n))

/-- Helper for Lemma 15.102.1: after forgetting the stage, a stage cycle is represented by the
same element of `S.X₂`. -/
private theorem idealPowerSubmoduleStageCyclesToCycles_subtype
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ)
    (x : LinearMap.ker (S.idealPowerSubmoduleStageComplex I n).g.hom) :
    ((idealPowerSubmoduleStageCyclesToCycles S I n x : LinearMap.ker S.g.hom) : S.X₂) = x.1.1 := by
  -- The codomain restriction only records the ambient cycle proof; it does not change the
  -- underlying element of `S.X₂`.
  rfl

/-- Helper for Lemma 15.102.1: the stage boundary map becomes the ambient boundary map after
including stage cycles into ambient cycles. -/
private theorem idealPowerSubmoduleStageCyclesToCycles_comp_moduleCatToCycles
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    (idealPowerSubmoduleStageCyclesToCycles S I n).comp
        (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles =
      S.moduleCatToCycles.comp (idealPowerSubtype I n S.X₁) := by
  -- Both sides send an element of `I^[n] S.X₁` to the same ambient boundary in `ker S.g`.
  ext x
  rfl

/-- Helper for Lemma 15.102.1: the stage cycles are exactly the ambient cycles lying in the
`n`th ideal-power submodule of `S.X₂`. -/
private theorem idealPowerSubmoduleStageCyclesToCycles_range_eq
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I n) =
      Submodule.comap (LinearMap.ker S.g.hom).subtype (I^[n] S.X₂) := by
  -- We prove the bridge by unpacking the range witness in both directions.
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    -- A stage cycle is represented by an element of `I^[n] S.X₂`.
    change y.1.1 ∈ I^[n] S.X₂
    exact y.1.2
  · intro hx
    -- An ambient cycle whose underlying element lies in `I^[n] S.X₂` defines a stage cycle.
    refine ⟨⟨⟨x.1, hx⟩, ?_⟩, ?_⟩
    · -- The stage differential vanishes because the ambient element is already a cycle.
      change (idealPowerSubmoduleMap I S.g.hom n) ⟨x.1, hx⟩ = 0
      apply Subtype.ext
      simpa [LinearMap.mem_ker] using x.2
    · -- Forgetting the stage recovers the original ambient cycle.
      ext
      rfl

/-- Helper for Lemma 15.102.1: forgetting the stage data on cycles is injective. -/
private theorem idealPowerSubmoduleStageCyclesToCycles_injective
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    Function.Injective (idealPowerSubmoduleStageCyclesToCycles S I n) := by
  intro x y hxy
  -- The stage-cycle inclusion only forgets proofs, so equality of the ambient cycles forces
  -- equality of the stage cycles themselves.
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : LinearMap.ker S.g.hom ↦ (z : S.X₂)) hxy

/-- Helper for Lemma 15.102.1: the stage cycles identify with the ambient cycles whose
underlying element lies in `I^[n] S.X₂`. -/
private abbrev idealPowerSubmoduleStageCyclesEquivComap
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    LinearMap.ker (S.idealPowerSubmoduleStageComplex I n).g.hom ≃ₗ[A]
      Submodule.comap (LinearMap.ker S.g.hom).subtype (I^[n] S.X₂) :=
  let toComap :
      LinearMap.ker (S.idealPowerSubmoduleStageComplex I n).g.hom →ₗ[A]
        Submodule.comap (LinearMap.ker S.g.hom).subtype (I^[n] S.X₂) :=
    (idealPowerSubmoduleStageCyclesToCycles S I n).codRestrict _ fun x ↦ by
      -- The codomain restriction uses the previously identified range of the forgetful map.
      rw [← idealPowerSubmoduleStageCyclesToCycles_range_eq (S := S) (I := I) (n := n)]
      exact LinearMap.mem_range_self _ x
  LinearEquiv.ofBijective toComap <| by
    constructor
    · intro x y hxy
      -- Equality after codomain restriction is already equality of the forgotten ambient cycles.
      apply idealPowerSubmoduleStageCyclesToCycles_injective (S := S) (I := I) (n := n)
      exact
        congrArg
          (fun z :
            Submodule.comap (LinearMap.ker S.g.hom).subtype (I^[n] S.X₂) ↦
              (z : LinearMap.ker S.g.hom))
          hxy
    · intro x
      -- Every ambient cycle in the comap submodule comes from a unique stage cycle.
      have hx :
          (x : LinearMap.ker S.g.hom) ∈
            LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I n) := by
        rw [idealPowerSubmoduleStageCyclesToCycles_range_eq (S := S) (I := I) (n := n)]
        exact x.2
      rcases hx with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      exact hy

/-- Helper for Lemma 15.102.1: the stage boundaries are exactly the ambient boundaries coming from
the `n`th ideal-power submodule of `S.X₁`. -/
private theorem idealPowerSubmoduleStageBoundary_range_eq
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    LinearMap.range
        ((idealPowerSubmoduleStageCyclesToCycles S I n).comp
          (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles) =
      Submodule.map S.moduleCatToCycles (I^[n] S.X₁) := by
  -- We compare the two sides by chasing witnesses for the same ambient boundary.
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [Submodule.mem_map]
    refine ⟨y.1, y.2, ?_⟩
    simpa using
      congrArg
        (fun f ↦ f y)
        (idealPowerSubmoduleStageCyclesToCycles_comp_moduleCatToCycles S I n)
  · rw [Submodule.mem_map]
    rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    simpa using
      congrArg
        (fun f ↦ f ⟨y, hy⟩)
        (idealPowerSubmoduleStageCyclesToCycles_comp_moduleCatToCycles S I n)

/-- Helper for Lemma 15.102.1: one positive Artin-Rees constant simultaneously controls the
ambient cycle inclusion `ker(S.g) ↪ S.X₂` and the boundary map `S.X₁ → ker(S.g)`. -/
private theorem exists_cycle_subtype_artin_rees_shift
    (S : ShortComplex Mod) (I : Ideal A) [Module.Finite A S.X₂] :
    ∃ c : ℕ, ∀ n : ℕ,
      Submodule.comap (LinearMap.ker S.g.hom).subtype (I^[c + n] S.X₂) ≤
        I^[n] (LinearMap.ker S.g.hom) := by
  -- Route correction: we first freeze the owner-level Artin-Rees statement for the cycle
  -- inclusion `ker(S.g) ↪ S.X₂`, before translating anything into stage-complex language.
  let _ : Module.Finite A ↥S.X₂ := by
    simpa using (inferInstance : Module.Finite A S.X₂)
  obtain ⟨c, hpow, _⟩ :=
    Ideal.exists_artin_rees_constant_of_exact I
      (LinearMap.exact_subtype_ker_map (LinearMap.ker S.g.hom).subtype)
  refine ⟨c, ?_⟩
  intro n
  have hker : LinearMap.ker (LinearMap.ker S.g.hom).subtype = ⊥ := by
    ext x
    simp
  -- The exact-sequence Artin-Rees equality at stage `c + n` collapses to a shifted ideal-power
  -- containment because the subtype map has zero kernel.
  calc
    Submodule.comap (LinearMap.ker S.g.hom).subtype (I^[c + n] S.X₂) =
        I ^ n •
          Submodule.comap (LinearMap.ker S.g.hom).subtype (I ^ c • (⊤ : Submodule A S.X₂)) := by
      simpa [idealPowerSubmodule, hker, show c + n - c = n by omega] using
        hpow (c + n) (Nat.le_add_right c n)
    _ ≤ I ^ n • (⊤ : Submodule A (LinearMap.ker S.g.hom)) :=
      smul_mono_right _ le_top
    _ = I^[n] (LinearMap.ker S.g.hom) := rfl

/-- Helper for Lemma 15.102.1: Artin-Rees controls the boundary map `S.X₁ → ker(S.g)` after a
uniform shift. -/
private theorem exists_boundary_artin_rees_shift
    (S : ShortComplex Mod) (I : Ideal A) [Module.Finite A S.X₂] :
    ∃ c : ℕ, ∀ n : ℕ,
      LinearMap.range S.moduleCatToCycles ⊓ I^[c + n] (LinearMap.ker S.g.hom) ≤
        Submodule.map S.moduleCatToCycles (I^[n] S.X₁) := by
  -- We first obtain the exact preimage equality for the owner boundary map, then convert it to
  -- the Artin-Rees range containment and evaluate it at the shifted stage `c + n`.
  let _ : Module.Finite A ↥S.X₂ := by
    simpa using (inferInstance : Module.Finite A S.X₂)
  let _ : IsNoetherian A ↥S.X₂ := by
    simpa using (inferInstance : IsNoetherian A S.X₂)
  let _ : Module.Finite A (LinearMap.ker S.g.hom) := by
    infer_instance
  obtain ⟨c, hpreimage⟩ := Ideal.exists_exact_preimage_pow_smul_eq I S.moduleCatToCycles
  have hbound : S.moduleCatToCycles.IsArtinReesBound I c :=
    LinearMap.isArtinReesBound_of_preimage_pow_smul_eq (I := I) hpreimage
  refine ⟨c, ?_⟩
  intro n
  simpa [idealPowerSubmodule, show c + n - c = n by omega] using
    hbound (c + n) (Nat.le_add_right c n)

/-- Helper for Lemma 15.102.1: one positive Artin-Rees constant simultaneously controls the
ambient cycle inclusion `ker(S.g) ↪ S.X₂` and the boundary map `S.X₁ → ker(S.g)`. -/
private theorem exists_artin_rees_constant_for_cycles_and_boundaries
    (S : ShortComplex Mod) (I : Ideal A) [Module.Finite A S.X₂] :
    ∃ c : ℕ, 0 < c ∧
      (∀ n : ℕ,
        LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I (c + n)) ≤
          I^[n] (LinearMap.ker S.g.hom)) ∧
      ∀ n : ℕ,
        LinearMap.range S.moduleCatToCycles ⊓ I^[c + n] (LinearMap.ker S.g.hom) ≤
          LinearMap.range
            ((idealPowerSubmoduleStageCyclesToCycles S I n).comp
              (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles) := by
  -- Route correction: the owner-level Artin-Rees containments are now proved separately, so this
  -- wrapper only synchronizes the two constants and rewrites the conclusions into stage language.
  rcases exists_cycle_subtype_artin_rees_shift S I with ⟨cZ, hcyclesZ⟩
  rcases exists_boundary_artin_rees_shift S I with ⟨cB, hboundariesB⟩
  refine ⟨cZ + cB + 1, Nat.succ_pos _, ?_, ?_⟩
  · intro n
    -- The stage-cycle range is the ambient cycle intersection at level `c + n`; the owner-level
    -- Artin-Rees shift then lands in a higher ideal power of `ker(S.g)`, which forgets to `I^[n]`.
    rw [idealPowerSubmoduleStageCyclesToCycles_range_eq]
    have hshift :
        Submodule.comap (LinearMap.ker S.g.hom).subtype
            (I^[cZ + cB + 1 + n] S.X₂) ≤
          I^[cB + 1 + n] (LinearMap.ker S.g.hom) := by
      simpa [Nat.add_assoc] using hcyclesZ (cB + 1 + n)
    exact hshift.trans <|
      idealPowerSubmodule_mono I (Nat.le_add_left n (cB + 1))
  · intro n
    -- The owner-level boundary containment at level `c + n` lands in a deeper ideal-power stage
    -- of `S.X₁`; monotonicity then compares that deeper stage with the `n`th stage boundary range.
    rw [idealPowerSubmoduleStageBoundary_range_eq]
    have hshift :
        LinearMap.range S.moduleCatToCycles ⊓
            I^[cZ + cB + 1 + n] (LinearMap.ker S.g.hom) ≤
          Submodule.map S.moduleCatToCycles (I^[cZ + 1 + n] S.X₁) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        hboundariesB (cZ + 1 + n)
    exact hshift.trans <|
      Submodule.map_mono (idealPowerSubmodule_mono I (Nat.le_add_left n (cZ + 1)))

/-- Helper for Lemma 15.102.1: the `n`th ideal-power stage inside the cycle object `S.cycles`. -/
private abbrev cycleIdealPower
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    Submodule A (LinearMap.ker S.g.hom) :=
  I ^ n • (⊤ : Submodule A (LinearMap.ker S.g.hom))

/-- Helper for Lemma 15.102.1: a deep cycle lies in every shallower ideal-power stage of the
ambient middle term. -/
private theorem cycleIdealPower_mem_stageCycleComap
    (S : ShortComplex Mod) (I : Ideal A) (n m : ℕ) (hnm : n ≤ m) :
    ∀ x : cycleIdealPower S I m,
      ((cycleIdealPower S I m).subtype x :
          LinearMap.ker S.g.hom) ∈
        Submodule.comap (LinearMap.ker S.g.hom).subtype (I^[n] S.X₂) := by
  intro x
  -- We first forget from `I^[m] Z` to `I^[n] Z`, and then map that ideal-power containment
  -- along the cycle inclusion `Z ↪ S.X₂`.
  change ((LinearMap.ker S.g.hom).subtype ((cycleIdealPower S I m).subtype x)) ∈ I^[n] S.X₂
  have hxZ :
      ((cycleIdealPower S I m).subtype x : LinearMap.ker S.g.hom) ∈
        I^[n] (LinearMap.ker S.g.hom) := by
    exact idealPowerSubmodule_mono I hnm x.2
  have hxMap :
      ((LinearMap.ker S.g.hom).subtype ((cycleIdealPower S I m).subtype x)) ∈
        Submodule.map (LinearMap.ker S.g.hom).subtype
          (I^[n] (LinearMap.ker S.g.hom)) := by
    exact Submodule.mem_map_of_mem hxZ
  have hmap :
      Submodule.map (LinearMap.ker S.g.hom).subtype
          (I^[n] (LinearMap.ker S.g.hom)) ≤
        I^[n] S.X₂ := by
    rw [idealPowerSubmodule, idealPowerSubmodule, Submodule.map_smul'', Submodule.map_top]
    exact smul_mono_right _ le_top
  exact hmap hxMap

/-- Helper for Lemma 15.102.1: a deep ambient cycle canonically determines a cycle in every
shallower stage complex. -/
private abbrev cycleIdealPowerToStageCycles
    (S : ShortComplex Mod) (I : Ideal A) (n m : ℕ) (hnm : n ≤ m) :
    cycleIdealPower S I m →ₗ[A]
      LinearMap.ker (S.idealPowerSubmoduleStageComplex I n).g.hom :=
  { toFun := fun x ↦ by
      -- A deep cycle already lies in the shallower ideal-power stage, and its ambient cycle
      -- equation is unchanged by that forgetful transport.
      refine ⟨⟨x.1.1, ?_⟩, ?_⟩
      · change ((cycleIdealPower S I m).subtype x : LinearMap.ker S.g.hom) ∈
            Submodule.comap (LinearMap.ker S.g.hom).subtype (I^[n] S.X₂)
        exact cycleIdealPower_mem_stageCycleComap S I n m hnm x
      · apply Subtype.ext
        exact x.1.2
    map_add' := by
      intro x y
      ext
      rfl
    map_smul' := by
      intro a x
      ext
      rfl }

/-- Helper for Lemma 15.102.1: forgetting the shallower stage produced from a deep cycle recovers
the original ambient cycle. -/
private theorem cycleIdealPowerToStageCycles_forget
    (S : ShortComplex Mod) (I : Ideal A) (n m : ℕ) (hnm : n ≤ m)
    (x : cycleIdealPower S I m) :
    idealPowerSubmoduleStageCyclesToCycles S I n
        (cycleIdealPowerToStageCycles S I n m hnm x) =
      ((cycleIdealPower S I m).subtype x : LinearMap.ker S.g.hom) := by
  -- The direct constructor changes only the ideal-power membership proof, so forgetting the stage
  -- recovers the original ambient cycle verbatim.
  ext
  rfl

/-- Helper for Lemma 15.102.1: the direct deep-cycle-to-stage-cycle constructor leaves the
underlying representative in `S.X₂` unchanged. -/
private theorem cycleIdealPowerToStageCycles_subtype
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ)
    (m : ℕ) (hnm : n ≤ m) (x : cycleIdealPower S I m) :
    (cycleIdealPowerToStageCycles S I n m hnm x).1.1 = x.1.1 := by
  -- The constructor changes only the ideal-power membership proof on the same ambient element.
  rfl

/-- Helper for Lemma 15.102.1: if a deep cycle already comes from an ambient boundary, then its
transport to a shallower stage complex comes from a stage boundary. -/
private theorem cycleIdealPowerToStageCycles_mem_boundary
    (S : ShortComplex Mod) (I : Ideal A) {c n : ℕ}
    (hboundaries : ∀ n : ℕ,
      LinearMap.range S.moduleCatToCycles ⊓ I^[c + n] (LinearMap.ker S.g.hom) ≤
        LinearMap.range
          ((idealPowerSubmoduleStageCyclesToCycles S I n).comp
            (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles))
    (x : cycleIdealPower S I (c + n))
    (hx :
      ((cycleIdealPower S I (c + n)).subtype x : LinearMap.ker S.g.hom) ∈
        LinearMap.range S.moduleCatToCycles) :
    cycleIdealPowerToStageCycles S I n (c + n) (Nat.le_add_left n c) x ∈
      LinearMap.range (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles := by
  let T := S.idealPowerSubmoduleStageComplex I n
  have hmem :
      ((cycleIdealPower S I (c + n)).subtype x : LinearMap.ker S.g.hom) ∈
        LinearMap.range S.moduleCatToCycles ⊓ I^[c + n] (LinearMap.ker S.g.hom) := by
    -- The source representative is both a boundary by hypothesis and a deep cycle by
    -- construction of `cycleIdealPower`.
    exact ⟨hx, x.2⟩
  have hstage :
      ((cycleIdealPower S I (c + n)).subtype x : LinearMap.ker S.g.hom) ∈
        LinearMap.range
          ((idealPowerSubmoduleStageCyclesToCycles S I n).comp T.moduleCatToCycles) :=
    hboundaries n hmem
  rcases LinearMap.mem_range.mp hstage with ⟨y, hy⟩
  refine LinearMap.mem_range.mpr ⟨y, ?_⟩
  -- Forgetting stage data identifies the explicit transported cycle with the boundary witness
  -- produced by the Artin-Rees containment, so injectivity upgrades equality of ambient cycles to
  -- equality of stage cycles.
  apply idealPowerSubmoduleStageCyclesToCycles_injective (S := S) (I := I) (n := n)
  calc
    idealPowerSubmoduleStageCyclesToCycles S I n (T.moduleCatToCycles y) =
        ((cycleIdealPower S I (c + n)).subtype x : LinearMap.ker S.g.hom) := by
      simpa [T, LinearMap.comp_apply] using hy
    _ =
        idealPowerSubmoduleStageCyclesToCycles S I n
          (cycleIdealPowerToStageCycles S I n (c + n) (Nat.le_add_left n c) x) := by
      symm
      exact cycleIdealPowerToStageCycles_forget
        (S := S) (I := I) (n := n) (m := c + n) (hnm := Nat.le_add_left n c) x

/-- Helper for Lemma 15.102.1: transporting a cycle through `moduleCatCyclesIso.hom` records the
same ambient element of `S.X₂` as the canonical inclusion `S.cycles ↪ S.X₂`. -/
private theorem moduleCatCyclesIso_hom_iCycles
    (S : ShortComplex Mod) (z : S.cycles) :
    (S.moduleCatCyclesIso.hom z).1 = S.iCycles.hom z := by
  -- The short-complex cycles object is definitionally the kernel used by
  -- `moduleCatCyclesIso`, so both sides forget to the same ambient element.
  rfl

/-- Helper for Lemma 15.102.1: after transporting a stage-kernel representative into the
categorical cycle object, the categorical `cyclesMap` for the stage inclusion agrees with the
explicit kernel-level forgetful map. -/
private theorem cyclesMap_stageInclusion_moduleCatCyclesIso_inv
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    let T := S.idealPowerSubmoduleStageComplex I n
    let φ : T ⟶ S := S.mapNatTrans (idealPowerSubtypeNatTrans I n)
    ∀ x : T.moduleCatLeftHomologyData.K,
      T.cyclesMap φ (T.moduleCatCyclesIso.inv.hom x) =
        S.moduleCatCyclesIso.inv.hom (idealPowerSubmoduleStageCyclesToCycles S I n x) := by
  intro T φ x
  -- We prove equality in `S.cycles` after applying the mono `S.iCycles`.
  apply (ModuleCat.mono_iff_injective S.iCycles).1 inferInstance
  have hi :=
    congrArg
      (fun f : T.cycles ⟶ S.X₂ ↦ f.hom (T.moduleCatCyclesIso.inv.hom x))
      (ShortComplex.cyclesMap_i φ)
  -- The left side becomes the ambient middle-term representative carried by `x`.
  have hx :
      T.iCycles.hom (T.moduleCatCyclesIso.inv.hom x) = x.1 := by
    calc
      T.iCycles.hom (T.moduleCatCyclesIso.inv.hom x) =
          (T.moduleCatCyclesIso.hom (T.moduleCatCyclesIso.inv.hom x)).1 := by
        symm
        exact moduleCatCyclesIso_hom_iCycles (S := T) (z := T.moduleCatCyclesIso.inv.hom x)
      _ = x.1 := by
        change ((T.moduleCatCyclesIso.hom (T.moduleCatCyclesIso.inv.hom x)).1 = x.1)
        simpa using congrArg Subtype.val (T.moduleCatCyclesIso.inv_hom_id_apply x)
  -- The right side is the same representative, now viewed as an ambient cycle of `S`.
  have hforget :
      S.iCycles.hom
          (S.moduleCatCyclesIso.inv.hom (idealPowerSubmoduleStageCyclesToCycles S I n x)) =
        x.1.1 := by
    calc
      S.iCycles.hom
          (S.moduleCatCyclesIso.inv.hom (idealPowerSubmoduleStageCyclesToCycles S I n x)) =
          (S.moduleCatCyclesIso.hom
            (S.moduleCatCyclesIso.inv.hom (idealPowerSubmoduleStageCyclesToCycles S I n x))).1 := by
        symm
        exact moduleCatCyclesIso_hom_iCycles
          (S := S) (z := S.moduleCatCyclesIso.inv.hom (idealPowerSubmoduleStageCyclesToCycles S I n x))
      _ = ((idealPowerSubmoduleStageCyclesToCycles S I n x : LinearMap.ker S.g.hom)).1 := by
        change
          ((S.moduleCatCyclesIso.hom
              (S.moduleCatCyclesIso.inv.hom (idealPowerSubmoduleStageCyclesToCycles S I n x))).1 =
            ((idealPowerSubmoduleStageCyclesToCycles S I n x : LinearMap.ker S.g.hom)).1)
        simpa using
          congrArg Subtype.val
            (S.moduleCatCyclesIso.inv_hom_id_apply
              (idealPowerSubmoduleStageCyclesToCycles S I n x))
      _ = x.1.1 := by
        simpa using idealPowerSubmoduleStageCyclesToCycles_subtype (S := S) (I := I) (n := n) x
  -- Both transported cycles therefore have the same image in `S.X₂`.
  calc
    S.iCycles.hom (T.cyclesMap φ (T.moduleCatCyclesIso.inv.hom x)) =
        φ.τ₂.hom (T.iCycles.hom (T.moduleCatCyclesIso.inv.hom x)) := by
      exact hi
    _ = φ.τ₂.hom x.1 := by rw [hx]
    _ = x.1.1 := rfl
    _ = S.iCycles.hom
          (S.moduleCatCyclesIso.inv.hom (idealPowerSubmoduleStageCyclesToCycles S I n x)) := by
      rw [hforget]

/-- Helper for Lemma 15.102.1: the quotient map from categorical cycles to left homology sends the
`n`th ideal-power stage of `S.cycles` onto the `n`th ideal-power stage of `H`. -/
private theorem leftHomologyπ_map_cyclesIdealPower_eq_idealPowerStage
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    Submodule.map S.leftHomologyπ.hom (I^[n] S.cycles) =
      I^[n] S.leftHomology := by
  -- Route correction: `S.leftHomologyπ.hom` is defined on the categorical cycle object
  -- `S.cycles`, so we first normalize the source stage to `I^n • ⊤` there and only then use
  -- surjectivity of the quotient map.
  have hsurj : Function.Surjective S.leftHomologyπ.hom :=
    (ModuleCat.epi_iff_surjective S.leftHomologyπ).1 inferInstance
  rw [idealPowerSubmodule, idealPowerSubmodule, Submodule.map_smul'', Submodule.map_top]
  simpa [LinearMap.range_eq_top.2 hsurj]

/-- Helper for Lemma 15.102.1: the quotient map on cycles restricts to a map
`I^[n] S.cycles → I^[n] H`. -/
private abbrev cyclesIdealPowerToLeftHomologyIdealPower
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    I^[n] S.cycles →ₗ[A] S.leftHomologyIdealPowerStage I n :=
  (S.leftHomologyπ.hom.comp (idealPowerSubtype I n S.cycles)).codRestrict
      (I^[n] S.leftHomology) fun x ↦ by
    -- The image computation above gives the codomain membership for every deep cycle.
    rw [← leftHomologyπ_map_cyclesIdealPower_eq_idealPowerStage (S := S) (I := I) (n := n)]
    exact Submodule.mem_map_of_mem x.2

/-- Helper for Lemma 15.102.1: the restricted map `I^[n] S.cycles → I^[n] H` is surjective. -/
private theorem cyclesIdealPowerToLeftHomologyIdealPower_range_eq_top
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    LinearMap.range (cyclesIdealPowerToLeftHomologyIdealPower S I n) = ⊤ := by
  ext y
  constructor
  · intro _
    simp
  · intro _
    -- The image formula above provides a deep-cycle representative for every point of `I^[n] H`.
    have hy :
        (idealPowerSubtype I n S.leftHomology y : S.leftHomology) ∈
          Submodule.map S.leftHomologyπ.hom (I^[n] S.cycles) := by
      rw [leftHomologyπ_map_cyclesIdealPower_eq_idealPowerStage (S := S) (I := I) (n := n)]
      exact y.2
    rcases hy with ⟨x, hx, hxy⟩
    refine LinearMap.mem_range.mpr ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy

-- Route correction: the quotient kernel has to be computed on the genuine cycles object
-- `S.cycles`, not on the ambient kernel model, before descending the reverse comparison map.
/-- Helper for Lemma 15.102.1: a categorical cycle represents the zero class in left homology
exactly when it lies in the transported boundary submodule of `S.cycles`. -/
private theorem leftHomologyπ_eq_zero_iff_mem_cycles_boundary
    (S : ShortComplex Mod) (q : S.cycles) :
    S.leftHomologyπ.hom q = 0 ↔
      q ∈ Submodule.map S.moduleCatCyclesIso.inv.hom (LinearMap.range S.moduleCatToCycles) := by
  have hcomm :
      S.leftHomologyπ ≫ S.moduleCatLeftHomologyData.leftHomologyIso.hom =
        S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π := by
    -- Compare the abstract quotient on `S.cycles` with the concrete quotient by boundaries
    -- before converting vanishing into a membership statement.
    simpa using
      (ShortComplex.leftHomologyMapData (𝟙 S) S.leftHomologyData S.moduleCatLeftHomologyData).commπ
  constructor
  · intro hq
    -- Push the vanishing class through the concrete quotient comparison and then record the
    -- resulting boundary representative back on `S.cycles`.
    have hπ := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom (S.leftHomologyπ.hom q) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hπ
    rw [hq, LinearMap.map_zero] at hπ
    have hmem :
        S.moduleCatCyclesIso.hom q ∈ LinearMap.range S.moduleCatToCycles := by
      simpa using
        (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).1 hπ.symm
    exact
      Submodule.mem_map.2 ⟨S.moduleCatCyclesIso.hom q, hmem, by
        simpa using S.moduleCatCyclesIso.hom_inv_id_apply q⟩
  · intro hq
    rcases Submodule.mem_map.1 hq with ⟨y, hy, hyq⟩
    have hy' : S.moduleCatCyclesIso.hom q = y := by
      calc
        S.moduleCatCyclesIso.hom q = S.moduleCatCyclesIso.hom.hom (S.moduleCatCyclesIso.inv.hom y) := by
          rw [hyq]
        _ = y := by
          simpa using S.moduleCatCyclesIso.inv_hom_id_apply y
    have hπ : S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q) = 0 := by
      rw [hy']
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range S.moduleCatToCycles)).2 hy
    -- Transport zero back across the quotient comparison isomorphism to the abstract homology.
    have hzero := congrArg (fun f : S.cycles ⟶ S.moduleCatLeftHomologyData.H ↦ f.hom q) hcomm
    change
      S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom (S.leftHomologyπ.hom q) =
        S.moduleCatLeftHomologyData.π.hom (S.moduleCatCyclesIso.hom q)
      at hzero
    rw [hπ] at hzero
    have hinj :
        Function.Injective S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom :=
      (ModuleCat.mono_iff_injective S.moduleCatLeftHomologyData.leftHomologyIso.hom).1
        inferInstance
    have h0 : 0 = S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom 0 := by
      simpa using (S.moduleCatLeftHomologyData.leftHomologyIso.hom.hom.map_zero).symm
    exact hinj (hzero.trans h0)

/-- Helper for Lemma 15.102.1: transporting the `n`th ideal-power stage of `S.cycles` through
`moduleCatCyclesIso.hom` gives the corresponding ideal-power stage inside the ambient kernel
model. -/
private theorem moduleCatCyclesIso_map_cyclesIdealPower_eq_cycleIdealPower
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    Submodule.map S.moduleCatCyclesIso.hom.hom (I^[n] S.cycles) =
      cycleIdealPower S I n := by
  have hsurj : Function.Surjective S.moduleCatCyclesIso.hom.hom :=
    (ModuleCat.epi_iff_surjective S.moduleCatCyclesIso.hom).1 inferInstance
  -- An isomorphism carries `I^n • ⊤` on `S.cycles` to the same `I^n • ⊤` on the kernel model
  -- because it maps the whole module onto the whole module.
  rw [idealPowerSubmodule, cycleIdealPower, Submodule.map_smul'', Submodule.map_top]
  rw [LinearMap.range_eq_top.2 hsurj]
  rfl

/-- Helper for Lemma 15.102.1: the kernel of `I^[n] S.cycles → I^[n] H` is exactly the
intersection of the `n`th cycle stage with the transported boundary submodule. -/
private theorem cyclesIdealPowerToLeftHomologyIdealPower_ker_eq
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    LinearMap.ker (cyclesIdealPowerToLeftHomologyIdealPower S I n) =
      ((Submodule.map S.moduleCatCyclesIso.inv.hom (LinearMap.range S.moduleCatToCycles) ⊓
          I^[n] S.cycles).submoduleOf (I^[n] S.cycles)) := by
  ext x
  constructor
  · intro hx
    -- Vanishing in the restricted codomain means the underlying cycle class already vanishes in
    -- `H`, so the representative lies in the transported boundary submodule.
    rw [LinearMap.mem_ker] at hx
    change (x : S.cycles) ∈
      (Submodule.map S.moduleCatCyclesIso.inv.hom (LinearMap.range S.moduleCatToCycles) ⊓
        I^[n] S.cycles)
    refine ⟨?_, x.2⟩
    have hx0 : S.leftHomologyπ.hom (x : S.cycles) = 0 := by
      exact congrArg Subtype.val hx
    exact (leftHomologyπ_eq_zero_iff_mem_cycles_boundary S (x : S.cycles)).1 hx0
  · intro hx
    -- Membership in the transported boundary intersection is the exact zero criterion for the
    -- quotient map on cycles.
    change (x : S.cycles) ∈
      (Submodule.map S.moduleCatCyclesIso.inv.hom (LinearMap.range S.moduleCatToCycles) ⊓
        I^[n] S.cycles) at hx
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    exact (leftHomologyπ_eq_zero_iff_mem_cycles_boundary S (x : S.cycles)).2 hx.1

/-- Helper for Lemma 15.102.1: quotienting `I^[n] S.cycles` by the kernel of the restricted
surjection to `I^[n] H` recovers `I^[n] H`. -/
private abbrev cyclesIdealPowerQuotientEquivLeftHomologyIdealPower
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    (I^[n] S.cycles ⧸ LinearMap.ker (cyclesIdealPowerToLeftHomologyIdealPower S I n)) ≃ₗ[A]
      S.leftHomologyIdealPowerStage I n :=
  -- The restricted map is surjective, so its quotient by the kernel identifies with the full
  -- codomain.
  (cyclesIdealPowerToLeftHomologyIdealPower S I n).quotKerEquivRange.trans <|
    LinearEquiv.ofTop _ (cyclesIdealPowerToLeftHomologyIdealPower_range_eq_top
      (S := S) (I := I) (n := n))

/-- Helper for Lemma 15.102.1: transporting a categorical deep cycle through
`moduleCatCyclesIso.hom` lands in the corresponding concrete ideal-power stage of the ambient
kernel model. -/
private theorem moduleCatCyclesIso_hom_mem_cycleIdealPower
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    ∀ x : I^[n] S.cycles,
      S.moduleCatCyclesIso.hom.hom ((idealPowerSubtype I n S.cycles) x) ∈
        cycleIdealPower S I n := by
  intro x
  -- The stage identity for `moduleCatCyclesIso.hom` rewrites the target membership into the
  -- image description of `I^[n] S.cycles`.
  rw [← moduleCatCyclesIso_map_cyclesIdealPower_eq_cycleIdealPower (S := S) (I := I) (n := n)]
  exact Submodule.mem_map_of_mem x.2

/-- Helper for Lemma 15.102.1: a categorical cycle already lies in `I^[n] S.cycles` whenever its
image under `moduleCatCyclesIso.hom` lies in the concrete `n`th ideal-power stage of the ambient
kernel model. -/
private theorem mem_cyclesIdealPower_of_moduleCatCyclesIso_mem
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) (q : S.cycles)
    (hq : S.moduleCatCyclesIso.hom.hom q ∈ cycleIdealPower S I n) :
    q ∈ I^[n] S.cycles := by
  -- The map description of `I^[n] S.cycles` under `moduleCatCyclesIso.hom` supplies a witness,
  -- and injectivity of the isomorphism identifies that witness with `q`.
  rw [← moduleCatCyclesIso_map_cyclesIdealPower_eq_cycleIdealPower (S := S) (I := I) (n := n)] at hq
  rcases Submodule.mem_map.1 hq with ⟨y, hy, hyq⟩
  have hinj : Function.Injective S.moduleCatCyclesIso.hom.hom :=
    (ModuleCat.mono_iff_injective S.moduleCatCyclesIso.hom).1 inferInstance
  have hy' : y = q := hinj hyq
  simpa [hy'] using hy

/-- Helper for Lemma 15.102.1: forgetting a `(c + n)`th stage cycle to `S.cycles` lands in the
`n`th ideal-power stage of `S.cycles`. -/
private theorem stageCyclesToCycles_mem_cyclesIdealPower
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I (c + n)) ≤
        I^[n] (LinearMap.ker S.g.hom))
    (n : ℕ) :
    ∀ x : (S.idealPowerSubmoduleStageComplex I (c + n)).moduleCatLeftHomologyData.K,
      S.moduleCatCyclesIso.inv.hom
          (idealPowerSubmoduleStageCyclesToCycles S I (c + n) x) ∈
        I^[n] S.cycles := by
  intro x
  -- The Artin-Rees cycle bound is phrased on the concrete kernel model; transporting back along
  -- `moduleCatCyclesIso` recovers the categorical ideal-power stage by the image description of
  -- `I^[n] S.cycles`.
  let q : S.cycles :=
    S.moduleCatCyclesIso.inv.hom (idealPowerSubmoduleStageCyclesToCycles S I (c + n) x)
  have hmem :
      idealPowerSubmoduleStageCyclesToCycles S I (c + n) x ∈
        I^[n] (LinearMap.ker S.g.hom) := by
    exact hcycles n (LinearMap.mem_range_self _ x)
  have hq_eq :
      S.moduleCatCyclesIso.hom.hom q =
        idealPowerSubmoduleStageCyclesToCycles S I (c + n) x := by
    simpa [q] using
      S.moduleCatCyclesIso.inv_hom_id_apply
        (idealPowerSubmoduleStageCyclesToCycles S I (c + n) x)
  have hq :
      S.moduleCatCyclesIso.hom.hom q ∈ cycleIdealPower S I n := by
    exact hq_eq ▸ hmem
  simpa [q] using
    mem_cyclesIdealPower_of_moduleCatCyclesIso_mem (S := S) (I := I) (n := n) q hq

/-- Helper for Lemma 15.102.1: the reverse comparison on representatives sends a deep categorical
cycle to its class in the `n`th stage homology quotient. -/
private abbrev cyclesIdealPowerToStageHomologyRaw
    (S : ShortComplex Mod) (I : Ideal A) (c n : ℕ) :
    I^[c + n] S.cycles →ₗ[A]
      (S.idealPowerSubmoduleStageComplex I n).moduleCatLeftHomologyData.H :=
  let T := S.idealPowerSubmoduleStageComplex I n
  T.moduleCatLeftHomologyData.π.hom.comp <|
    (cycleIdealPowerToStageCycles S I n (c + n) (Nat.le_add_left n c)).comp <|
      ((S.moduleCatCyclesIso.hom.hom.comp (idealPowerSubtype I (c + n) S.cycles)).codRestrict
        (cycleIdealPower S I (c + n))
        (moduleCatCyclesIso_hom_mem_cycleIdealPower (S := S) (I := I) (n := c + n)))

/-- Helper for Lemma 15.102.1: the reverse raw map annihilates the kernel of
`I^[c+n] S.cycles → I^[c+n] H`, so it descends to `I^[c+n] H → H[n]`. -/
private theorem cyclesIdealPowerToStageHomologyRaw_ker_le
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hboundaries : ∀ n : ℕ,
      LinearMap.range S.moduleCatToCycles ⊓ I^[c + n] (LinearMap.ker S.g.hom) ≤
        LinearMap.range
          ((idealPowerSubmoduleStageCyclesToCycles S I n).comp
            (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles))
    (n : ℕ) :
    LinearMap.ker (cyclesIdealPowerToLeftHomologyIdealPower S I (c + n)) ≤
      LinearMap.ker (cyclesIdealPowerToStageHomologyRaw S I c n) := by
  intro x hx
  let T := S.idealPowerSubmoduleStageComplex I n
  let z : cycleIdealPower S I (c + n) :=
    ((S.moduleCatCyclesIso.hom.hom.comp (idealPowerSubtype I (c + n) S.cycles)).codRestrict
      (cycleIdealPower S I (c + n))
      (moduleCatCyclesIso_hom_mem_cycleIdealPower (S := S) (I := I) (n := c + n))) x
  have hx' :
      (x : S.cycles) ∈
        Submodule.map S.moduleCatCyclesIso.inv.hom (LinearMap.range S.moduleCatToCycles) ⊓
          I^[c + n] S.cycles := by
    rw [cyclesIdealPowerToLeftHomologyIdealPower_ker_eq (S := S) (I := I) (n := c + n)] at hx
    exact hx
  have hz_boundary :
      ((cycleIdealPower S I (c + n)).subtype z : LinearMap.ker S.g.hom) ∈
        LinearMap.range S.moduleCatToCycles := by
    rcases Submodule.mem_map.1 hx'.1 with ⟨y, hy, hyx⟩
    have hyz :
        y =
          ((cycleIdealPower S I (c + n)).subtype z : LinearMap.ker S.g.hom) := by
      dsimp [z]
      calc
        y = S.moduleCatCyclesIso.hom.hom (S.moduleCatCyclesIso.inv.hom y) := by
          symm
          simpa using S.moduleCatCyclesIso.inv_hom_id_apply y
        _ = S.moduleCatCyclesIso.hom.hom (x : S.cycles) := by
          exact congrArg S.moduleCatCyclesIso.hom.hom hyx
        _ = ((cycleIdealPower S I (c + n)).subtype z : LinearMap.ker S.g.hom) := by
          rfl
    simpa [hyz] using hy
  have hz_stage :
      cycleIdealPowerToStageCycles S I n (c + n) (Nat.le_add_left n c) z ∈
        LinearMap.range T.moduleCatToCycles := by
    exact
      cycleIdealPowerToStageCycles_mem_boundary
        (S := S) (I := I) (c := c) (n := n) hboundaries z hz_boundary
  rw [LinearMap.mem_ker]
  change
    T.moduleCatLeftHomologyData.π.hom
        (cycleIdealPowerToStageCycles S I n (c + n) (Nat.le_add_left n c) z) = 0
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range T.moduleCatToCycles)).2 hz_stage

/-- Helper for Lemma 15.102.1: the forward comparison on representatives forgets a stage cycle to
an ambient categorical cycle and then passes to `I^[n] H`. -/
private abbrev stageHomologyToLeftHomologyIdealPowerRaw
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I (c + n)) ≤
        I^[n] (LinearMap.ker S.g.hom))
    (n : ℕ) :
    (S.idealPowerSubmoduleStageComplex I (c + n)).moduleCatLeftHomologyData.K →ₗ[A]
      S.leftHomologyIdealPowerStage I n :=
  (cyclesIdealPowerToLeftHomologyIdealPower S I n).comp <|
    ((S.moduleCatCyclesIso.inv.hom.comp
        (idealPowerSubmoduleStageCyclesToCycles S I (c + n))).codRestrict
      (I^[n] S.cycles)
      (stageCyclesToCycles_mem_cyclesIdealPower (S := S) (I := I) (c := c) hcycles n))

/-- Helper for Lemma 15.102.1: the forward raw map kills stage boundaries, so it descends to
`H[c+n] → I^[n] H`. -/
private theorem stageHomologyToLeftHomologyIdealPower_boundary_ker
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I (c + n)) ≤
        I^[n] (LinearMap.ker S.g.hom))
    (n : ℕ) :
    LinearMap.range (S.idealPowerSubmoduleStageComplex I (c + n)).moduleCatToCycles ≤
      LinearMap.ker (stageHomologyToLeftHomologyIdealPowerRaw S I c hcycles n) := by
  intro x hx
  let T := S.idealPowerSubmoduleStageComplex I (c + n)
  rcases LinearMap.mem_range.1 hx with ⟨y, rfl⟩
  let q : S.cycles :=
    S.moduleCatCyclesIso.inv.hom
      (idealPowerSubmoduleStageCyclesToCycles S I (c + n) (T.moduleCatToCycles y))
  have hq_boundary :
      q ∈ Submodule.map S.moduleCatCyclesIso.inv.hom (LinearMap.range S.moduleCatToCycles) := by
    refine Submodule.mem_map.2 ?_
    refine ⟨S.moduleCatToCycles (idealPowerSubtype I (c + n) S.X₁ y), ?_, ?_⟩
    · exact LinearMap.mem_range_self _ _
    · -- The stage boundary forgets to the same ambient boundary in `ker(S.g)`.
      change
        S.moduleCatCyclesIso.inv.hom
            (idealPowerSubmoduleStageCyclesToCycles S I (c + n) (T.moduleCatToCycles y)) =
          S.moduleCatCyclesIso.inv.hom
            (S.moduleCatToCycles (idealPowerSubtype I (c + n) S.X₁ y))
      have hforget :
          idealPowerSubmoduleStageCyclesToCycles S I (c + n) (T.moduleCatToCycles y) =
            S.moduleCatToCycles (idealPowerSubtype I (c + n) S.X₁ y) := by
        simpa [T, LinearMap.comp_apply] using
          congrArg
            (fun f : I^[c + n] S.X₁ →ₗ[A] LinearMap.ker S.g.hom ↦ f y)
            (idealPowerSubmoduleStageCyclesToCycles_comp_moduleCatToCycles S I (c + n))
      exact congrArg S.moduleCatCyclesIso.inv.hom hforget
  have hq_zero : S.leftHomologyπ.hom q = 0 := by
    exact (leftHomologyπ_eq_zero_iff_mem_cycles_boundary S q).2 hq_boundary
  change (cyclesIdealPowerToLeftHomologyIdealPower S I n)
      (((S.moduleCatCyclesIso.inv.hom.comp
          (idealPowerSubmoduleStageCyclesToCycles S I (c + n))).codRestrict
        (I^[n] S.cycles)
        (stageCyclesToCycles_mem_cyclesIdealPower (S := S) (I := I) (c := c) hcycles n))
        (T.moduleCatToCycles y)) = 0
  apply Subtype.ext
  change S.leftHomologyπ.hom q = 0
  exact hq_zero

/-- Helper for Lemma 15.102.1: descending the reverse raw map through the quotient model of
`I^[c+n] H` gives the canonical comparison `I^[c+n] H → H[n]`. -/
private abbrev leftHomologyIdealPowerToStageHomology
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hboundaries : ∀ n : ℕ,
      LinearMap.range S.moduleCatToCycles ⊓ I^[c + n] (LinearMap.ker S.g.hom) ≤
        LinearMap.range
          ((idealPowerSubmoduleStageCyclesToCycles S I n).comp
            (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles))
    (n : ℕ) :
    S.leftHomologyIdealPowerStage I (c + n) ⟶
      S.idealPowerSubmoduleHomologyStage I n :=
  -- We keep the source proof on the quotient-of-cycles model until the very end, and only then
  -- transport back to abstract left homology of the `n`th stage complex.
  (cyclesIdealPowerQuotientEquivLeftHomologyIdealPower S I (c + n)).symm.toModuleIso.hom ≫
    ModuleCat.ofHom
      ((LinearMap.ker (cyclesIdealPowerToLeftHomologyIdealPower S I (c + n))).liftQ
        (cyclesIdealPowerToStageHomologyRaw S I c n)
        (cyclesIdealPowerToStageHomologyRaw_ker_le S I c hboundaries n)) ≫
      (S.idealPowerSubmoduleStageComplex I n).moduleCatLeftHomologyData.leftHomologyIso.inv

/-- Helper for Lemma 15.102.1: the reverse stage comparison is the quotient descent followed by
the abstract left-homology transport. -/
private theorem leftHomologyIdealPowerToStageHomology_eq_descended
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hboundaries : ∀ n : ℕ,
      LinearMap.range S.moduleCatToCycles ⊓ I^[c + n] (LinearMap.ker S.g.hom) ≤
        LinearMap.range
          ((idealPowerSubmoduleStageCyclesToCycles S I n).comp
            (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles))
    (n : ℕ) :
    leftHomologyIdealPowerToStageHomology S I c hboundaries n =
      (cyclesIdealPowerQuotientEquivLeftHomologyIdealPower S I (c + n)).symm.toModuleIso.hom ≫
      ModuleCat.ofHom
        ((LinearMap.ker (cyclesIdealPowerToLeftHomologyIdealPower S I (c + n))).liftQ
          (cyclesIdealPowerToStageHomologyRaw S I c n)
          (cyclesIdealPowerToStageHomologyRaw_ker_le S I c hboundaries n)) ≫
        (S.idealPowerSubmoduleStageComplex I n).moduleCatLeftHomologyData.leftHomologyIso.inv := by
  -- This is just the defining quotient descent written as a standalone rewrite.
  rfl

/-- Helper for Lemma 15.102.1: descending the forward raw map through stage homology gives the
canonical comparison `H[c+n] → I^[n] H`. -/
private abbrev stageHomologyToLeftHomologyIdealPower
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I (c + n)) ≤
        I^[n] (LinearMap.ker S.g.hom))
    (n : ℕ) :
    S.idealPowerSubmoduleHomologyStage I (c + n) ⟶
      S.leftHomologyIdealPowerStage I n :=
  let T := S.idealPowerSubmoduleStageComplex I (c + n)
  -- Route correction: the forward map is first defined on the concrete quotient by stage
  -- boundaries, then transported to abstract stage homology via `leftHomologyIso`.
  T.moduleCatLeftHomologyData.leftHomologyIso.hom ≫
    ModuleCat.ofHom
      ((LinearMap.range T.moduleCatToCycles).liftQ
        (stageHomologyToLeftHomologyIdealPowerRaw S I c hcycles n)
        (stageHomologyToLeftHomologyIdealPower_boundary_ker S I c hcycles n))

/-- Helper for Lemma 15.102.1: the forward stage comparison is the concrete quotient descent
preceded by the abstract left-homology transport. -/
private theorem stageHomologyToLeftHomologyIdealPower_eq_descended
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I (c + n)) ≤
        I^[n] (LinearMap.ker S.g.hom))
    (n : ℕ) :
    stageHomologyToLeftHomologyIdealPower S I c hcycles n =
      (S.idealPowerSubmoduleStageComplex I (c + n)).moduleCatLeftHomologyData.leftHomologyIso.hom ≫
      ModuleCat.ofHom
        ((LinearMap.range
            (S.idealPowerSubmoduleStageComplex I (c + n)).moduleCatToCycles).liftQ
          (stageHomologyToLeftHomologyIdealPowerRaw S I c hcycles n)
          (stageHomologyToLeftHomologyIdealPower_boundary_ker S I c hcycles n)) := by
  -- This is just the defining quotient descent written as a standalone rewrite.
  rfl

/-- Helper for Lemma 15.102.1: evaluating the forward stage comparison on a concrete stage cycle
representative produces the explicit ambient cycle class in `I^[n] H`. -/
private theorem stageHomologyToLeftHomologyIdealPower_on_representatives
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I (c + n)) ≤
        I^[n] (LinearMap.ker S.g.hom))
    (n : ℕ) :
    let T := S.idealPowerSubmoduleStageComplex I (c + n)
    ∀ z : T.cycles,
      ((stageHomologyToLeftHomologyIdealPower S I c hcycles n ≫
            ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology)).hom)
          (T.leftHomologyπ.hom z) =
        S.leftHomologyπ.hom
          (S.moduleCatCyclesIso.inv.hom
            (idealPowerSubmoduleStageCyclesToCycles S I (c + n)
              (T.moduleCatCyclesIso.hom z))) := by
  intro T z
  have hcomm :
      T.leftHomologyπ ≫ T.moduleCatLeftHomologyData.leftHomologyIso.hom =
        T.moduleCatCyclesIso.hom ≫ T.moduleCatLeftHomologyData.π := by
    -- We first rewrite abstract stage homology representatives into the concrete quotient model
    -- used to define `toStage`.
    simpa using
      (ShortComplex.leftHomologyMapData (𝟙 T) T.leftHomologyData T.moduleCatLeftHomologyData).commπ
  have hleft :
      ((stageHomologyToLeftHomologyIdealPower S I c hcycles n ≫
            ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology)).hom)
          (T.leftHomologyπ.hom z) =
        S.leftHomologyπ.hom
          (S.moduleCatCyclesIso.inv.hom
            (idealPowerSubmoduleStageCyclesToCycles S I (c + n)
              (T.moduleCatCyclesIso.hom z))) := by
    -- After rewriting `toStage` through its quotient descent, evaluating on a cycle
    -- representative reduces to the raw cycle-level map.
    rw [stageHomologyToLeftHomologyIdealPower_eq_descended
      (S := S) (I := I) (c := c) (hcycles := hcycles) (n := n)]
    have hπ :=
      congrArg
        (fun f : T.cycles ⟶ T.moduleCatLeftHomologyData.H ↦ f.hom z)
        hcomm
    change
      T.moduleCatLeftHomologyData.leftHomologyIso.hom.hom (T.leftHomologyπ.hom z) =
        T.moduleCatLeftHomologyData.π.hom (T.moduleCatCyclesIso.hom z) at hπ
    change
      ((ModuleCat.ofHom
            ((LinearMap.range T.moduleCatToCycles).liftQ
              (stageHomologyToLeftHomologyIdealPowerRaw S I c hcycles n)
              (stageHomologyToLeftHomologyIdealPower_boundary_ker S I c hcycles n)) ≫
          ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology)).hom)
        (T.moduleCatLeftHomologyData.leftHomologyIso.hom.hom (T.leftHomologyπ.hom z)) =
        S.leftHomologyπ.hom
          (S.moduleCatCyclesIso.inv.hom
            (idealPowerSubmoduleStageCyclesToCycles S I (c + n)
              (T.moduleCatCyclesIso.hom z)))
    rw [hπ]
    change
      idealPowerSubtype I n S.leftHomology
          (((LinearMap.range T.moduleCatToCycles).liftQ
              (stageHomologyToLeftHomologyIdealPowerRaw S I c hcycles n)
              (stageHomologyToLeftHomologyIdealPower_boundary_ker S I c hcycles n))
            (T.moduleCatLeftHomologyData.π.hom (T.moduleCatCyclesIso.hom z))) =
        S.leftHomologyπ.hom
          (S.moduleCatCyclesIso.inv.hom
            (idealPowerSubmoduleStageCyclesToCycles S I (c + n)
              (T.moduleCatCyclesIso.hom z)))
    have hmkQ :
        ((LinearMap.range T.moduleCatToCycles).liftQ
            (stageHomologyToLeftHomologyIdealPowerRaw S I c hcycles n)
            (stageHomologyToLeftHomologyIdealPower_boundary_ker S I c hcycles n))
          (T.moduleCatLeftHomologyData.π.hom (T.moduleCatCyclesIso.hom z)) =
        stageHomologyToLeftHomologyIdealPowerRaw S I c hcycles n (T.moduleCatCyclesIso.hom z) := by
      -- The concrete quotient map on stage cycles is the quotient constructor `mkQ`.
      rfl
    rw [hmkQ]
    change
      idealPowerSubtype I n S.leftHomology
          (stageHomologyToLeftHomologyIdealPowerRaw S I c hcycles n
            (T.moduleCatCyclesIso.hom z)) =
        S.leftHomologyπ.hom
          (S.moduleCatCyclesIso.inv.hom
            (idealPowerSubmoduleStageCyclesToCycles S I (c + n)
              (T.moduleCatCyclesIso.hom z)))
    rfl
  exact hleft

/-- Helper for Lemma 15.102.1: morphisms out of a stage left-homology object are determined after
precomposing with the canonical quotient map from stage cycles. -/
private theorem eq_of_comp_leftHomologyπ_eq
    (S : ShortComplex Mod) (I : Ideal A) (c n : ℕ)
    {Y : Mod}
    {f g : (S.idealPowerSubmoduleStageComplex I (c + n)).leftHomology ⟶ Y}
    (hfg :
      (S.idealPowerSubmoduleStageComplex I (c + n)).leftHomologyπ ≫ f =
        (S.idealPowerSubmoduleStageComplex I (c + n)).leftHomologyπ ≫ g) :
    f = g := by
  let T := S.idealPowerSubmoduleStageComplex I (c + n)
  -- The stage quotient map `T.cycles ⟶ H[c+n]` is epi, so equality after precomposition is
  -- already equality of the target morphisms.
  exact (cancel_epi T.leftHomologyπ).1 (by simpa [T] using hfg)

/-- Helper for Lemma 15.102.1: transporting a concrete stage-cycle quotient class back through
`leftHomologyIso.inv` gives the corresponding abstract left-homology class. -/
private theorem moduleCatLeftHomologyIso_inv_pi_eq_leftHomologyπ
    (T : ShortComplex Mod) [T.HasLeftHomology]
    (x : T.moduleCatLeftHomologyData.K) :
    T.moduleCatLeftHomologyData.leftHomologyIso.inv.hom
        (T.moduleCatLeftHomologyData.π.hom x) =
      T.leftHomologyπ.hom (T.moduleCatCyclesIso.inv.hom x) := by
  -- TODO: apply `leftHomologyMapData.commπ` to `T.moduleCatCyclesIso.inv.hom x`, then transport
  -- the resulting equality back across `leftHomologyIso.inv`.
  sorry

/-- Helper for Lemma 15.102.1: the reverse quotient descent evaluates on deep cycle
representatives by applying the raw representative map and then transporting back through
`leftHomologyIso.inv`. -/
private theorem leftHomologyIdealPowerToStageHomology_precompose_eq_raw
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hboundaries : ∀ n : ℕ,
      LinearMap.range S.moduleCatToCycles ⊓ I^[c + n] (LinearMap.ker S.g.hom) ≤
        LinearMap.range
          ((idealPowerSubmoduleStageCyclesToCycles S I n).comp
            (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles))
    (n : ℕ) :
    ModuleCat.ofHom (cyclesIdealPowerToLeftHomologyIdealPower S I (c + n)) ≫
        leftHomologyIdealPowerToStageHomology S I c hboundaries n =
      ModuleCat.ofHom (cyclesIdealPowerToStageHomologyRaw S I c n) ≫
        (S.idealPowerSubmoduleStageComplex I n).moduleCatLeftHomologyData.leftHomologyIso.inv := by
  -- TODO: rewrite the quotient-equivalence inverse on the image of `x` to `mkQ x`, then the
  -- descended `liftQ` evaluates definitionally to the raw representative map.
  sorry

/-- Helper for Lemma 15.102.1: evaluating the reverse stage comparison on a deep categorical
cycle gives the corresponding explicit stage-homology class. -/
private theorem leftHomologyIdealPowerToStageHomology_on_cycles
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hboundaries : ∀ n : ℕ,
      LinearMap.range S.moduleCatToCycles ⊓ I^[c + n] (LinearMap.ker S.g.hom) ≤
        LinearMap.range
          ((idealPowerSubmoduleStageCyclesToCycles S I n).comp
            (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles))
    (n : ℕ) :
    let T := S.idealPowerSubmoduleStageComplex I n
    ∀ x : I^[c + n] S.cycles,
      (leftHomologyIdealPowerToStageHomology S I c hboundaries n).hom
          ((cyclesIdealPowerToLeftHomologyIdealPower S I (c + n)) x) =
        T.leftHomologyπ.hom
          (T.moduleCatCyclesIso.inv.hom
            (cycleIdealPowerToStageCycles S I n (c + n) (Nat.le_add_left n c)
              (((S.moduleCatCyclesIso.hom.hom.comp
                  (idealPowerSubtype I (c + n) S.cycles)).codRestrict
                (cycleIdealPower S I (c + n))
                (moduleCatCyclesIso_hom_mem_cycleIdealPower (S := S) (I := I) (n := c + n))) x))) := by
  -- TODO: evaluate the precomposed reverse descent via
  -- `leftHomologyIdealPowerToStageHomology_precompose_eq_raw`, then rewrite the remaining
  -- transport with `moduleCatLeftHomologyIso_inv_pi_eq_leftHomologyπ`.
  sorry

/-- Helper for Lemma 15.102.1: a deep cycle representative in any stage complex has the same
underlying element of `S.X₂` after transporting back from the concrete kernel model. -/
private theorem stageCycles_iCycles_moduleCatCyclesIso_inv
    (S : ShortComplex Mod) (I : Ideal A) (n m : ℕ) (hnm : n ≤ m)
    (x : cycleIdealPower S I m) :
    ((((S.idealPowerSubmoduleStageComplex I n).iCycles.hom
        ((S.idealPowerSubmoduleStageComplex I n).moduleCatCyclesIso.inv.hom
          (cycleIdealPowerToStageCycles S I n m hnm x))) : I^[n] S.X₂).1) =
      x.1.1 := by
  -- TODO: transport the stage representative through `moduleCatCyclesIso.hom`, identify its
  -- underlying stage element, and then use `cycleIdealPowerToStageCycles_subtype`.
  sorry

/-- Helper for Lemma 15.102.1: the homology transition induced by a stage inclusion sends a deep
cycle representative to the corresponding shallower stage representative of the same ambient
cycle. -/
private theorem idealPowerSubmoduleHomology_transition_on_deep_cycle_representatives
    (S : ShortComplex Mod) (I : Ideal A) {n m l : ℕ}
    (hnm : n ≤ m) (hml : m ≤ l) :
    let Tm := S.idealPowerSubmoduleStageComplex I m
    let Tn := S.idealPowerSubmoduleStageComplex I n
    let φ : Tm ⟶ Tn := S.mapNatTrans (idealPowerSubmoduleInclusionNatTrans I hnm)
    ∀ x : cycleIdealPower S I l,
      (leftHomologyMap φ).hom
        (Tm.leftHomologyπ.hom
          (Tm.moduleCatCyclesIso.inv.hom
            (cycleIdealPowerToStageCycles S I m l hml x))) =
      Tn.leftHomologyπ.hom
        (Tn.moduleCatCyclesIso.inv.hom
          (cycleIdealPowerToStageCycles S I n l (hnm.trans hml) x)) := by
  -- TODO: evaluate `ShortComplex.homologyπ_naturality` on the transported deep stage
  -- representative, then prove the cycle-level map is the explicit shallower representative by
  -- comparing their images under `Tn.iCycles`.
  sorry

/-- Helper for Lemma 15.102.1: morphisms out of `I^[c+n] H` are determined on deep cycle
representatives. -/
private theorem eq_of_comp_cyclesIdealPower_eq
    (S : ShortComplex Mod) (I : Ideal A) (c n : ℕ)
    {Y : Mod}
    {f g : S.leftHomologyIdealPowerStage I (c + n) ⟶ Y}
    (hfg :
      ModuleCat.ofHom (cyclesIdealPowerToLeftHomologyIdealPower S I (c + n)) ≫ f =
        ModuleCat.ofHom (cyclesIdealPowerToLeftHomologyIdealPower S I (c + n)) ≫ g) :
    f = g := by
  let _ : Epi (ModuleCat.ofHom (cyclesIdealPowerToLeftHomologyIdealPower S I (c + n))) :=
    (ModuleCat.epi_iff_surjective _).2 <|
      LinearMap.range_eq_top.1
        (cyclesIdealPowerToLeftHomologyIdealPower_range_eq_top (S := S) (I := I) (n := c + n))
  -- The restricted cycle-to-homology map is surjective, so it suffices to compare both morphisms
  -- on deep cycle representatives.
  exact (cancel_epi (ModuleCat.ofHom (cyclesIdealPowerToLeftHomologyIdealPower S I (c + n)))).1 hfg

/-- Helper for Lemma 15.102.1: the successor map on the ideal-power tower followed by the ambient
inclusion is the next ambient inclusion. -/
private theorem leftHomologyIdealPowerStep_comp_subtype
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.leftHomologyIdealPowerStep I n ≫ ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology) =
      ModuleCat.ofHom (idealPowerSubtype I (n + 1) S.leftHomology) := by
  -- Both sides forget the `(n + 1)`st ideal-power membership proof and keep the same homology
  -- class in the ambient module.
  ext x
  rfl

/-- Helper for Lemma 15.102.1: the homology transition `H[c+n+1] → H[c+n]` followed by the
ambient map to `H` is already the direct ambient map from the deeper stage. -/
private theorem idealPowerSubmoduleHomologyStep_comp_toLeftHomology
    (S : ShortComplex Mod) (I : Ideal A) (n : ℕ) :
    S.idealPowerSubmoduleHomologyStep I n ≫
        S.idealPowerSubmoduleHomologyToLeftHomology I n =
      S.idealPowerSubmoduleHomologyToLeftHomology I (n + 1) := by
  -- The two short-complex morphisms from stage `n + 1` to `S` compose strictly, so their
  -- induced maps on left homology also compose strictly.
  change
    leftHomologyMap
        (S.mapNatTrans (idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ n))) ≫
      leftHomologyMap (S.mapNatTrans (idealPowerSubtypeNatTrans I n)) =
    leftHomologyMap (S.mapNatTrans (idealPowerSubtypeNatTrans I (n + 1)))
  rw [← ShortComplex.leftHomologyMap_comp]
  rfl

/-- Helper for Lemma 15.102.1: the descended forward stage comparison agrees with the canonical
map to ambient left homology after including `I^[n] H ↪ H`. -/
private theorem stageHomologyToLeftHomologyIdealPower_comp_subtype
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I (c + n)) ≤
        I^[n] (LinearMap.ker S.g.hom))
    (n : ℕ) :
    stageHomologyToLeftHomologyIdealPower S I c hcycles n ≫
        ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology) =
      S.idealPowerSubmoduleHomologyToLeftHomology I (c + n) := by
  let T := S.idealPowerSubmoduleStageComplex I (c + n)
  let φ : T ⟶ S := S.mapNatTrans (idealPowerSubtypeNatTrans I (c + n))
  -- We lift the representative-level formula to the abstract owner-level equality by cancelling
  -- the epi `T.leftHomologyπ`.
  apply eq_of_comp_leftHomologyπ_eq (S := S) (I := I) (c := c) (n := n)
  ext z
  change
    ((stageHomologyToLeftHomologyIdealPower S I c hcycles n ≫
          ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology)).hom)
        (T.leftHomologyπ.hom z) =
      (S.idealPowerSubmoduleHomologyToLeftHomology I (c + n)).hom
        (T.leftHomologyπ.hom z)
  rw [stageHomologyToLeftHomologyIdealPower_on_representatives
    (S := S) (I := I) (c := c) (hcycles := hcycles) (n := n) z]
  have hnat :
      T.leftHomologyπ ≫ S.idealPowerSubmoduleHomologyToLeftHomology I (c + n) =
        T.cyclesMap φ ≫ S.leftHomologyπ := by
    simpa [idealPowerSubmoduleHomologyToLeftHomology, φ] using
      (ShortComplex.homologyπ_naturality φ)
  have hnat_eval :=
    congrArg
      (fun f : T.cycles ⟶ S.leftHomology ↦ f.hom z)
      hnat
  change
    (S.idealPowerSubmoduleHomologyToLeftHomology I (c + n)).hom (T.leftHomologyπ.hom z) =
      S.leftHomologyπ.hom (T.cyclesMap φ z) at hnat_eval
  have hcyclesMap :
      T.cyclesMap φ z =
        S.moduleCatCyclesIso.inv.hom
          (idealPowerSubmoduleStageCyclesToCycles S I (c + n) (T.moduleCatCyclesIso.hom z)) := by
    calc
      T.cyclesMap φ z =
          T.cyclesMap φ (T.moduleCatCyclesIso.inv.hom (T.moduleCatCyclesIso.hom z)) := by
        rw [T.moduleCatCyclesIso.hom_inv_id_apply]
      _ =
          S.moduleCatCyclesIso.inv.hom
            (idealPowerSubmoduleStageCyclesToCycles S I (c + n) (T.moduleCatCyclesIso.hom z)) := by
        simpa [T, φ] using
          cyclesMap_stageInclusion_moduleCatCyclesIso_inv
            (S := S) (I := I) (n := c + n) (x := T.moduleCatCyclesIso.hom z)
  rw [hcyclesMap] at hnat_eval
  exact hnat_eval.symm

/-- Helper for Lemma 15.102.1: after precomposing with deep cycle representatives, the reverse
stage comparison commutes with the successor maps of the two towers. -/
private theorem leftHomologyIdealPowerToStageHomology_step_after_cycles_precompose
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hboundaries : ∀ n : ℕ,
      LinearMap.range S.moduleCatToCycles ⊓ I^[c + n] (LinearMap.ker S.g.hom) ≤
        LinearMap.range
          ((idealPowerSubmoduleStageCyclesToCycles S I n).comp
            (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles))
    (n : ℕ) :
    ModuleCat.ofHom (cyclesIdealPowerToLeftHomologyIdealPower S I (c + (n + 1))) ≫
        S.leftHomologyIdealPowerStep I (c + n) ≫
          leftHomologyIdealPowerToStageHomology S I c hboundaries n =
      ModuleCat.ofHom (cyclesIdealPowerToLeftHomologyIdealPower S I (c + (n + 1))) ≫
        leftHomologyIdealPowerToStageHomology S I c hboundaries (n + 1) ≫
          S.idealPowerSubmoduleHomologyStep I n := by
  -- TODO: restrict the deep categorical cycle to `I^[c+n] S.cycles`, evaluate both reverse maps
  -- on that representative, and compare the resulting stage classes via
  -- `idealPowerSubmoduleHomology_transition_on_deep_cycle_representatives`.
  sorry

/-- Helper for Lemma 15.102.1: after precomposing with the stage quotient map, the forward stage
comparison commutes with the successor maps of the two towers. -/
private theorem stageHomologyToLeftHomologyIdealPower_step_after_leftHomologyπ
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hcycles : ∀ n : ℕ,
      LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I (c + n)) ≤
        I^[n] (LinearMap.ker S.g.hom))
    (n : ℕ) :
    (S.idealPowerSubmoduleStageComplex I (c + (n + 1))).leftHomologyπ ≫
        S.idealPowerSubmoduleHomologyStep I (c + n) ≫
          stageHomologyToLeftHomologyIdealPower S I c hcycles n =
      (S.idealPowerSubmoduleStageComplex I (c + (n + 1))).leftHomologyπ ≫
        stageHomologyToLeftHomologyIdealPower S I c hcycles (n + 1) ≫
          S.leftHomologyIdealPowerStep I n := by
  let T := S.idealPowerSubmoduleStageComplex I (c + (n + 1))
  -- Route correction: we compare both maps after the mono `I^[n] H ↪ H`, where both sides become
  -- the same ambient homology morphism from the deep stage.
  apply (cancel_mono (ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology))).1
  calc
    (T.leftHomologyπ ≫ S.idealPowerSubmoduleHomologyStep I (c + n) ≫
          stageHomologyToLeftHomologyIdealPower S I c hcycles n) ≫
        ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology) =
      T.leftHomologyπ ≫
        (S.idealPowerSubmoduleHomologyStep I (c + n) ≫
          S.idealPowerSubmoduleHomologyToLeftHomology I (c + n)) := by
            rw [Category.assoc, Category.assoc,
              stageHomologyToLeftHomologyIdealPower_comp_subtype
                (S := S) (I := I) (c := c) (hcycles := hcycles) (n := n)]
    _ = T.leftHomologyπ ≫ S.idealPowerSubmoduleHomologyToLeftHomology I (c + (n + 1)) := by
          rw [idealPowerSubmoduleHomologyStep_comp_toLeftHomology (S := S) (I := I) (n := c + n)]
    _ = (T.leftHomologyπ ≫ stageHomologyToLeftHomologyIdealPower S I c hcycles (n + 1) ≫
          S.leftHomologyIdealPowerStep I n) ≫
        ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology) := by
          rw [Category.assoc, Category.assoc,
            leftHomologyIdealPowerStep_comp_subtype]
          simpa [Category.assoc, stageHomologyToLeftHomologyIdealPower] using
            congrArg
              (fun f :
                (S.idealPowerSubmoduleStageComplex I (c + (n + 1))).leftHomology ⟶
                  S.leftHomology ↦
                T.leftHomologyπ ≫ f)
              (stageHomologyToLeftHomologyIdealPower_comp_subtype
                (S := S) (I := I) (c := c) (hcycles := hcycles) (n := n + 1)).symm

/-- Helper for Lemma 15.102.1: after precomposing with deep cycle representatives, the reverse
then forward shifted composite is the canonical transition map on the ideal-power tower. -/
private theorem leftHomologyIdealPower_composite_after_cycles_precompose
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hboundaries : ∀ n : ℕ,
      LinearMap.range S.moduleCatToCycles ⊓ I^[c + n] (LinearMap.ker S.g.hom) ≤
        LinearMap.range
          ((idealPowerSubmoduleStageCyclesToCycles S I n).comp
            (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles))
    (hcycles : ∀ n : ℕ,
      LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I (c + n)) ≤
        I^[n] (LinearMap.ker S.g.hom))
    (n : ℕ) :
    ModuleCat.ofHom (cyclesIdealPowerToLeftHomologyIdealPower S I (c + (c + n))) ≫
        leftHomologyIdealPowerToStageHomology S I c hboundaries (c + n) ≫
          stageHomologyToLeftHomologyIdealPower S I c hcycles n =
      ModuleCat.ofHom (cyclesIdealPowerToLeftHomologyIdealPower S I (c + (c + n))) ≫
        SequentialInverseSystem.transitionMap (S.leftHomologyIdealPowerTower I)
          (shiftComparison_le n c) := by
  -- TODO: compare both composites after postcomposing with `I^[n] H ↪ H`, then use the verified
  -- reverse-on-cycles and forward-on-representatives formulas to identify both sides with the
  -- same ambient left-homology class of a deep cycle representative.
  sorry

/-- Helper for Lemma 15.102.1: after precomposing with the stage quotient map, the forward then
reverse shifted composite is the canonical transition map on the stage-homology tower. -/
private theorem idealPowerSubmoduleHomology_composite_after_leftHomologyπ
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (hboundaries : ∀ n : ℕ,
      LinearMap.range S.moduleCatToCycles ⊓ I^[c + n] (LinearMap.ker S.g.hom) ≤
        LinearMap.range
          ((idealPowerSubmoduleStageCyclesToCycles S I n).comp
            (S.idealPowerSubmoduleStageComplex I n).moduleCatToCycles))
    (hcycles : ∀ n : ℕ,
      LinearMap.range (idealPowerSubmoduleStageCyclesToCycles S I (c + n)) ≤
        I^[n] (LinearMap.ker S.g.hom))
    (n : ℕ) :
    (S.idealPowerSubmoduleStageComplex I (c + (c + n))).leftHomologyπ ≫
        stageHomologyToLeftHomologyIdealPower S I c hcycles (c + n) ≫
          leftHomologyIdealPowerToStageHomology S I c hboundaries n =
      (S.idealPowerSubmoduleStageComplex I (c + (c + n))).leftHomologyπ ≫
        SequentialInverseSystem.transitionMap (S.idealPowerSubmoduleHomologyTower I)
          (shiftComparison_le n c) := by
  -- TODO: evaluate the forward map on a deep stage representative `z`, identify its image in
  -- `I^[c+n] H` via the already proved representative formula, and then compare the reverse image
  -- with the direct stage transition using a representative-level bridge for the deep stage.
  sorry

/-- Lemma 15.102.1: for a complex `K ⟶ L ⟶ M` of finite `A`-modules over a Noetherian ring and an
ideal `I`, the filtered homology groups `H[n]` are eventually compared with the `I`-adic
filtration on `H = ker β / im α` by shifted natural transformations in both directions whose
stagewise composites are the canonical transition morphisms. -/
@[stacks 0G3K]
theorem exists_idealPowerSubmoduleHomologyComparison
    (S : ShortComplex Mod) (I : Ideal A)
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃] :
    ∃ c : ℕ, 0 < c ∧
      ∃ toPower :
        (S.idealPowerSubmoduleHomologyTower I).shift c ⟶ S.leftHomologyIdealPowerTower I,
        ∃ fromPower :
          (S.leftHomologyIdealPowerTower I).shift c ⟶ S.idealPowerSubmoduleHomologyTower I,
          (∀ n : ℕ,
            toPower.app (Opposite.op n) ≫ ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology) =
              S.idealPowerSubmoduleHomologyToLeftHomology I (c + n)) ∧
            (∀ n : ℕ,
              ((fromPower.app (Opposite.op (c + n))) :
                  S.leftHomologyIdealPowerStage I (c + (c + n)) ⟶
                    S.idealPowerSubmoduleHomologyStage I (c + n)) ≫
                toPower.app (Opposite.op n) =
                SequentialInverseSystem.transitionMap (S.leftHomologyIdealPowerTower I)
                  (shiftComparison_le n c)) ∧
            ∀ n : ℕ,
              ((toPower.app (Opposite.op (c + n))) :
                  S.idealPowerSubmoduleHomologyStage I (c + (c + n)) ⟶
                    S.leftHomologyIdealPowerStage I (c + n)) ≫
                fromPower.app (Opposite.op n) =
                SequentialInverseSystem.transitionMap (S.idealPowerSubmoduleHomologyTower I)
                  (shiftComparison_le n c) := by
  -- Route correction: the earlier route jumped directly to tower morphisms. We first freeze the
  -- concrete cycle and boundary Artin-Rees data that the quotient-model construction needs.
  rcases exists_artin_rees_constant_for_cycles_and_boundaries S I with
    ⟨c, hc, hcycles, hboundaries⟩
  let fromStage := leftHomologyIdealPowerToStageHomology S I c hboundaries
  let toStage := stageHomologyToLeftHomologyIdealPower S I c hcycles
  have hfromStage_transport :
      ∀ n : ℕ,
        fromStage n =
          (cyclesIdealPowerQuotientEquivLeftHomologyIdealPower S I (c + n)).symm.toModuleIso.hom ≫
          ModuleCat.ofHom
            ((LinearMap.ker (cyclesIdealPowerToLeftHomologyIdealPower S I (c + n))).liftQ
              (cyclesIdealPowerToStageHomologyRaw S I c n)
              (cyclesIdealPowerToStageHomologyRaw_ker_le S I c hboundaries n)) ≫
            (S.idealPowerSubmoduleStageComplex I n).moduleCatLeftHomologyData.leftHomologyIso.inv :=
    fun n ↦ leftHomologyIdealPowerToStageHomology_eq_descended S I c hboundaries n
  have htoStage_transport :
      ∀ n : ℕ,
        toStage n =
          (S.idealPowerSubmoduleStageComplex I (c + n)).moduleCatLeftHomologyData.leftHomologyIso.hom ≫
          ModuleCat.ofHom
            ((LinearMap.range
                (S.idealPowerSubmoduleStageComplex I (c + n)).moduleCatToCycles).liftQ
              (stageHomologyToLeftHomologyIdealPowerRaw S I c hcycles n)
              (stageHomologyToLeftHomologyIdealPower_boundary_ker S I c hcycles n)) :=
    fun n ↦ stageHomologyToLeftHomologyIdealPower_eq_descended S I c hcycles n
  have htoStage_subtype :
      ∀ n : ℕ,
        toStage n ≫ ModuleCat.ofHom (idealPowerSubtype I n S.leftHomology) =
          S.idealPowerSubmoduleHomologyToLeftHomology I (c + n) :=
    fun n ↦ stageHomologyToLeftHomologyIdealPower_comp_subtype S I c hcycles n
  have hfromStage_step :
      ∀ n : ℕ,
        S.leftHomologyIdealPowerStep I (c + n) ≫ fromStage n =
          fromStage (n + 1) ≫ S.idealPowerSubmoduleHomologyStep I n := by
    intro n
    -- Route correction: we first compare both morphisms on the deep cycle epi
    -- `I^[c + (n + 1)] S.cycles ⟶ I^[c + (n + 1)] H`, then cancel that epi.
    apply eq_of_comp_cyclesIdealPower_eq (S := S) (I := I) (c := c) (n := n + 1)
    simpa [fromStage] using
      leftHomologyIdealPowerToStageHomology_step_after_cycles_precompose
        (S := S) (I := I) (c := c) (hboundaries := hboundaries) n
  have htoStage_step :
      ∀ n : ℕ,
        S.idealPowerSubmoduleHomologyStep I (c + n) ≫ toStage n =
          toStage (n + 1) ≫ S.leftHomologyIdealPowerStep I n := by
    intro n
    -- We compare both forward maps after precomposing with the stage quotient map
    -- `H[c + (n + 1)]_cycles ⟶ H[c + (n + 1)]`.
    apply eq_of_comp_leftHomologyπ_eq (S := S) (I := I) (c := c) (n := n + 1)
    simpa [toStage] using
      stageHomologyToLeftHomologyIdealPower_step_after_leftHomologyπ
        (S := S) (I := I) (c := c) (hcycles := hcycles) n
  have hfrom_to :
      ∀ n : ℕ,
        fromStage (c + n) ≫ toStage n =
          SequentialInverseSystem.transitionMap (S.leftHomologyIdealPowerTower I)
            (shiftComparison_le n c) := by
    intro n
    -- The reverse-then-forward composite is proved on deep cycle representatives and then
    -- upgraded to the abstract tower morphism by cancelling the same epi as above.
    apply eq_of_comp_cyclesIdealPower_eq (S := S) (I := I) (c := c) (n := c + n)
    simpa [fromStage, toStage] using
      leftHomologyIdealPower_composite_after_cycles_precompose
        (S := S) (I := I) (c := c) (hboundaries := hboundaries) (hcycles := hcycles) n
  have hto_from :
      ∀ n : ℕ,
        toStage (c + n) ≫ fromStage n =
          SequentialInverseSystem.transitionMap (S.idealPowerSubmoduleHomologyTower I)
            (shiftComparison_le n c) := by
    intro n
    -- The forward-then-reverse composite is handled on the deep stage quotient model before
    -- cancelling the canonical quotient map.
    apply eq_of_comp_leftHomologyπ_eq (S := S) (I := I) (c := c) (n := c + n)
    simpa [fromStage, toStage] using
      idealPowerSubmoduleHomology_composite_after_leftHomologyπ
        (S := S) (I := I) (c := c) (hboundaries := hboundaries) (hcycles := hcycles) n
  let toPower :
      (S.idealPowerSubmoduleHomologyTower I).shift c ⟶ S.leftHomologyIdealPowerTower I :=
    NatTrans.ofOpSequence
      (fun n ↦ toStage n)
      (fun n ↦ by
        -- The shifted source successor is the owner transition `H[c + n + 1] → H[c + n]`.
        change
          ((S.idealPowerSubmoduleHomologyTower I).shift c).transitionMap (Nat.le_succ n) ≫
              toStage n =
            toStage (n + 1) ≫
              (S.leftHomologyIdealPowerTower I).transitionMap (Nat.le_succ n)
        rw [SequentialInverseSystem.shift_transitionMap]
        simpa [idealPowerSubmoduleHomologyTower, leftHomologyIdealPowerTower,
          SequentialInverseSystem.transitionMap, Nat.add_assoc,
          Functor.ofOpSequence_map_homOfLE_succ] using htoStage_step n)
  let fromPower :
      (S.leftHomologyIdealPowerTower I).shift c ⟶ S.idealPowerSubmoduleHomologyTower I :=
    NatTrans.ofOpSequence
      (fun n ↦ fromStage n)
      (fun n ↦ by
        -- The shifted source successor is the owner transition `I^[c + n + 1] H → I^[c + n] H`.
        change
          ((S.leftHomologyIdealPowerTower I).shift c).transitionMap (Nat.le_succ n) ≫
              fromStage n =
            fromStage (n + 1) ≫
              (S.idealPowerSubmoduleHomologyTower I).transitionMap (Nat.le_succ n)
        rw [SequentialInverseSystem.shift_transitionMap]
        simpa [idealPowerSubmoduleHomologyTower, leftHomologyIdealPowerTower,
          SequentialInverseSystem.transitionMap, Nat.add_assoc,
          Functor.ofOpSequence_map_homOfLE_succ] using hfromStage_step n)
  refine ⟨c, hc, toPower, fromPower, ?_, ?_, ?_⟩
  · intro n
    -- Stagewise, `toPower` is exactly the owner-level forward comparison `toStage n`.
    simpa [toPower] using htoStage_subtype n
  · intro n
    -- The reverse-then-forward composite was already proved on the owner stages.
    simpa [toPower, fromPower] using hfrom_to n
  · intro n
    -- The forward-then-reverse composite is the corresponding owner-level transition map.
    simpa [toPower, fromPower] using hto_from n

/-- Helper for Lemma 15.102.1: the stagewise composite identities from the source comparison
package the shifted natural transformation into a pro-isomorphism witness. -/
private theorem shifted_idealPowerSubmodule_comparison_isProIsomorphism
    (S : ShortComplex Mod) (I : Ideal A) (c : ℕ)
    (toPower :
      (S.idealPowerSubmoduleHomologyTower I).shift c ⟶ S.leftHomologyIdealPowerTower I)
    (fromPower :
      (S.leftHomologyIdealPowerTower I).shift c ⟶ S.idealPowerSubmoduleHomologyTower I)
    (hfrom : ∀ n : ℕ,
      ((fromPower.app (Opposite.op (c + n))) :
          S.leftHomologyIdealPowerStage I (c + (c + n)) ⟶
            S.idealPowerSubmoduleHomologyStage I (c + n)) ≫
        toPower.app (Opposite.op n) =
        SequentialInverseSystem.transitionMap (S.leftHomologyIdealPowerTower I)
          (shiftComparison_le n c))
    (hto : ∀ n : ℕ,
      ((toPower.app (Opposite.op (c + n))) :
          S.idealPowerSubmoduleHomologyStage I (c + (c + n)) ⟶
            S.leftHomologyIdealPowerStage I (c + n)) ≫
        fromPower.app (Opposite.op n) =
        SequentialInverseSystem.transitionMap (S.idealPowerSubmoduleHomologyTower I)
          (shiftComparison_le n c)) :
    (ofShiftNatTrans c toPower).IsProIsomorphism := by
  let homologyComp :=
    compRep (ofShiftNatTrans c toPower) (ofShiftNatTrans c fromPower)
  let powerComp :=
    compRep (ofShiftNatTrans c fromPower) (ofShiftNatTrans c toPower)
  refine ⟨ofShiftNatTrans c fromPower, ?_, ?_⟩
  · -- The composite on the homology tower is already the canonical transition map after
    -- refining both representatives to the common stage `n ↦ c + (c + n)`.
    refine ⟨homologyComp.reindex, fun n ↦ le_rfl, ?_, ?_⟩
    · intro n
      simpa [homologyComp, SequentialProObjectMorphismRep.compRep,
        SequentialProObjectMorphismRep.ofShiftNatTrans] using shiftComparison_le n c
    · intro n
      simpa [homologyComp, SequentialInverseSystem.transitionMap] using hto n
  · -- The same common refinement identifies the reverse composite with the transition map on
    -- the ideal-power tower of the ambient left homology.
    refine ⟨powerComp.reindex, fun n ↦ le_rfl, ?_, ?_⟩
    · intro n
      simpa [powerComp, SequentialProObjectMorphismRep.compRep,
        SequentialProObjectMorphismRep.ofShiftNatTrans] using shiftComparison_le n c
    · intro n
      simpa [powerComp, SequentialInverseSystem.transitionMap] using hfrom n

/-- Companion to Lemma 15.102.1: the filtered homology tower `(H[n])_n` and the `I`-adic tower
`(H^[n])_n`, with `H^[n] = I^n H`, are pro-isomorphic via the explicit shift representative coming
from the forward comparison natural transformation. -/
theorem idealPowerSubmoduleHomologyTower_isProIsomorphic_to_leftHomologyIdealPowerTower
    (S : ShortComplex Mod) (I : Ideal A)
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] [Module.Finite A S.X₃] :
    ∃ c : ℕ, 0 < c ∧
      ∃ comparison :
        (S.idealPowerSubmoduleHomologyTower I).shift c ⟶ S.leftHomologyIdealPowerTower I,
        (ofShiftNatTrans c comparison).IsProIsomorphism := by
  -- Use the main comparison theorem to obtain the two shifted natural transformations and
  -- then package their stagewise transition identities into a pro-isomorphism witness.
  rcases exists_idealPowerSubmoduleHomologyComparison S I with
    ⟨c, hc, toPower, fromPower, htoPower, hfromPower, htoHomology⟩
  refine ⟨c, hc, toPower, ?_⟩
  exact shifted_idealPowerSubmodule_comparison_isProIsomorphism
    S I c toPower fromPower hfromPower htoHomology

end Comparison

end CategoryTheory.ShortComplex
