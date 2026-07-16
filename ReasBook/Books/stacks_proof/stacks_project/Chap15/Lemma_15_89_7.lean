import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import stacks_proof.stacks_project.Chap13.Lemma_13_11_6
import stacks_proof.stacks_project.Chap13.Lemma_13_42_3
import stacks_proof.stacks_project.Chap13.Lemma_13_33_7
import stacks_proof.stacks_project.Chap13.Lemma_13_38_1
import stacks_proof.stacks_project.Chap13.Remark_13_12_4
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Definition_15_59_13
import stacks_proof.stacks_project.Chap15.Lemma_15_59_14
import stacks_proof.stacks_project.Chap15.Lemma_15_67_8
import stacks_proof.stacks_project.Chap15.Lemma_15_67_20
import stacks_proof.stacks_project.Chap15.Definition_15_89_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "DbMod" => boundedDerivedCategory (ModuleCat R)
local notation "Hb" => boundedDerivedHomologyFunctor (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "RmodI" =>
  ModuleCat.single0Functor.obj (ModuleCat.of R (R ⧸ I))

/- Domain-style sampling for derived tensor bounds with ideal-power torsion coefficients:
- primary domain: canonical t-structure bounds `DerivedCategory.IsLE 0` on derived tensor
  products in `D(R)`;
- same-domain declarations inspected:
  `DerivedCategory.IsLE`,
  `boundedDerivedHomologyFunctor`,
  `ModuleCat.single0Functor`,
  `DerivedCategory.isLE_iff`,
  `Module.IsIdealPowerTorsion`;
- best owner abstraction: the bound `(K ⊗[R]^L M).IsLE 0` in the canonical derived-category
  t-structure;
- primitive data: the bounded object `M`, the source-facing nonpositive bound `M.obj.IsLE 0`,
  and the torsion hypotheses on the genuinely possibly nonzero cohomology objects `H^i(M)` for
  `i ≤ 0`;
- derived API: vanishing of the positive cohomology objects of `M` is already supplied by
  `DerivedCategory.isLE_iff` / `DerivedCategory.isZero_of_isLE`, so torsion in positive degrees
  is redundant and should not remain primitive input.

Layer triage:
- `source-facing`: the tensor-vanishing statement for bounded complexes with ideal-power torsion
  cohomology;
- `core/canonical`: the owner predicate `DerivedCategory.IsLE 0` on the derived tensor product;
- `bridge/view`: `ModuleCat.single0Functor` for modules concentrated in degree `0` and
  `boundedDerivedHomologyFunctor` for the cohomology objects of `M`.

Within this file, the quotient clause `(1)` is derived API: after identifying `R ⧸ I^n` as an
`I`-power torsion module through `Module.isIdealPowerTorsion_quotient_pow`, it is a specialization
of the module clause `(2)` rather than a second primitive owner.
-/

/-- Helper for Lemma 15.89.7: the finite power-torsion stages exhaust any `I`-power torsion
module. -/
private theorem ideal_power_torsion_iSup_power_torsion_eq_top
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    (⨆ n : ℕ+, Ideal.powerTorsion I N (n : ℕ)) = ⊤ := by
  -- Proof comment: unpack the elementwise torsion witnesses and place each element into the
  -- corresponding finite power-torsion stage.
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  rw [Module.isIdealPowerTorsion_iff] at hN
  obtain ⟨n, hn⟩ := hN x
  refine Submodule.mem_iSup_of_mem n ?_
  rw [show Ideal.powerTorsion I N (n : ℕ) = N[I^(n : ℕ)] by rfl]
  rw [Submodule.mem_torsionBySet_iff]
  exact hn

/-- Helper for Lemma 15.89.7: the finite power-torsion stages form an increasing sequence. -/
private theorem power_torsion_mono
    (N : ModuleCat R) {n m : ℕ+} (hnm : n ≤ m) :
    Ideal.powerTorsion I N (n : ℕ) ≤ Ideal.powerTorsion I N (m : ℕ) := by
  -- Proof comment: an element killed by `I^n` is also killed by the smaller ideal `I^m ⊆ I^n`
  -- once `n ≤ m`.
  intro x hx
  rw [show Ideal.powerTorsion I N (n : ℕ) = N[I^(n : ℕ)] by rfl] at hx
  rw [show Ideal.powerTorsion I N (m : ℕ) = N[I^(m : ℕ)] by rfl]
  rw [Submodule.mem_torsionBySet_iff] at hx
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  exact hx ⟨a, Ideal.pow_le_pow_right (show (n : ℕ) ≤ (m : ℕ) from hnm) a.2⟩

/-- Helper for Lemma 15.89.7: each finite power-torsion stage is annihilated by the
corresponding power of `I`. -/
private theorem power_torsion_le_annihilator
    (N : ModuleCat R) (n : ℕ) :
    I ^ n ≤ Module.annihilator R (Ideal.powerTorsion I N n) := by
  -- Proof comment: by definition, every element of the stage `N[I^n]` is killed by every
  -- coefficient in `I^n`.
  intro a ha
  rw [Submodule.mem_annihilator]
  intro x hx
  rw [show Ideal.powerTorsion I N n = N[I^n] by rfl] at hx
  rw [Submodule.mem_torsionBySet_iff] at hx
  exact hx ⟨a, ha⟩

/-- Helper for Lemma 15.89.7: the positive stages `N[I^(n+1)]` still exhaust an
`I`-power torsion module. -/
private theorem ideal_power_torsion_iSup_succ_eq_top
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    (⨆ n : ℕ, Ideal.powerTorsion I N (n + 1)) = ⊤ := by
  -- Proof comment: reindex the elementwise torsion witness so the sequential diagram starts at
  -- the first nontrivial stage `I¹`.
  refine Submodule.eq_top_iff'.2 fun x ↦ ?_
  rw [Module.isIdealPowerTorsion_iff] at hN
  obtain ⟨n, hn⟩ := hN x
  cases n with
  | zero =>
      refine Submodule.mem_iSup_of_mem 0 ?_
      rw [show Ideal.powerTorsion I N (0 + 1) = N[I ^ (0 + 1)] by rfl]
      rw [Submodule.mem_torsionBySet_iff]
      intro a ha
      exact hn ⟨a, Ideal.pow_le_pow_right (show (0 : ℕ) ≤ 1 by omega) ha⟩
  | succ n =>
      refine Submodule.mem_iSup_of_mem n ?_
      simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using hn

/-- Helper for Lemma 15.89.7: the positive power-torsion stages form an increasing sequential
system. -/
private theorem power_torsion_succ_mono
    (N : ModuleCat R) (n : ℕ) :
    Ideal.powerTorsion I N (n + 1) ≤ Ideal.powerTorsion I N (n + 2) := by
  -- Proof comment: increasing the exponent shrinks the ideal, so anything killed by `I^(n+1)` is
  -- also killed by `I^(n+2)`.
  intro x hx
  rw [show Ideal.powerTorsion I N (n + 1) = N[I ^ (n + 1)] by rfl] at hx
  rw [show Ideal.powerTorsion I N (n + 2) = N[I ^ (n + 2)] by rfl]
  rw [Submodule.mem_torsionBySet_iff] at hx ⊢
  intro a ha
  exact hx ⟨a, Ideal.pow_le_pow_right (show n + 1 ≤ n + 2 by omega) ha⟩

/-- Helper for Lemma 15.89.7: the source proof uses the sequential diagram of positive
power-torsion stages `N[I^(n+1)]`. -/
private noncomputable def power_torsion_stage_diagram
    (N : ModuleCat R) : ℕ ⥤ ModuleCat R :=
  Functor.ofSequence (fun n ↦
    (Submodule.inclusion (power_torsion_succ_mono (I := I) N n)))

/-- Helper for Lemma 15.89.7: each object in the sequential stage diagram is annihilated by the
matching power of `I`. -/
private theorem power_torsion_stage_diagram_annihilator
    (N : ModuleCat R) (n : ℕ) :
    I ^ (n + 1) ≤ Module.annihilator R ((power_torsion_stage_diagram (I := I) N).obj n) := by
  -- Proof comment: the `n`th stage of the sequence is literally `N[I^(n+1)]`.
  simpa [power_torsion_stage_diagram] using
    power_torsion_le_annihilator (I := I) N (n + 1)

/-- Helper for Lemma 15.89.7: applying the degree-zero single-complex functor to the stage
diagram gives the concrete telescope used for the homotopy-colimit step. -/
private noncomputable def power_torsion_stage_complex_diagram
    (N : ModuleCat R) : ℕ ⥤ CochainComplex (ModuleCat R) ℤ :=
  (power_torsion_stage_diagram (I := I) N) ⋙
    (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ))

/-- Helper for Lemma 15.89.7: the termwise colimit of the stage complexes is already a homotopy
colimit after localizing to the derived category. -/
private theorem power_torsion_stage_complex_colimit_is_hocolim
    (N : ModuleCat R) :
    IsHomotopyColimitOf
      ((power_torsion_stage_complex_diagram (I := I) N) ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.obj (Limits.colimit (power_torsion_stage_complex_diagram (I := I) N))) := by
  -- Proof comment: this is exactly the Chapter 13 telescope theorem applied to the explicit stage
  -- diagram on the complexes `N[I^(n+1)][0]`.
  simpa [power_torsion_stage_complex_diagram] using
    (termwise_colimit_is_homotopy_colimit (𝒜 := ModuleCat R)
      (power_torsion_stage_complex_diagram (I := I) N))

/-- Helper for Lemma 15.89.7: every element of an `I`-power torsion module lies in some positive
stage `N[I^(n+1)]` of the source sequential system. -/
private theorem mem_power_torsion_stage_succ
    {N : ModuleCat R} (hN : Module.IsIdealPowerTorsion I N) (x : N) :
    ∃ n : ℕ, x ∈ Ideal.powerTorsion I N (n + 1) := by
  -- Proof comment: reindex the elementwise torsion witness so that the sequential system starts
  -- at the first nontrivial stage `I¹`.
  rw [Module.isIdealPowerTorsion_iff] at hN
  obtain ⟨n, hn⟩ := hN x
  cases n with
  | zero =>
      refine ⟨0, ?_⟩
      rw [show Ideal.powerTorsion I N (0 + 1) = N[I ^ (0 + 1)] by rfl]
      rw [Submodule.mem_torsionBySet_iff]
      intro a ha
      exact hn ⟨a, Ideal.pow_le_pow_right (show (0 : ℕ) ≤ 1 by omega) ha⟩
  | succ n =>
      refine ⟨n, ?_⟩
      simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using hn

/-- Helper for Lemma 15.89.7: the canonical cocone from the positive power-torsion stages to the
ambient module is given by the literal inclusion maps. -/
private noncomputable def power_torsion_stage_cocone
    (N : ModuleCat R) : Cocone (power_torsion_stage_diagram (I := I) N) :=
  Cocone.mk N <|
    NatTrans.ofSequence
      (fun n ↦ ModuleCat.ofHom ((Ideal.powerTorsion I N (n + 1)).subtype))
      (fun n ↦ by
        -- Proof comment: both composites are the same literal inclusion into `N`.
        ext x
        rfl)

/-- Helper for Lemma 15.89.7: descending the inclusion cocone yields the canonical map from the
colimit of the stage diagram to `N`. -/
private noncomputable def power_torsion_stage_colimit_to_module
    (N : ModuleCat R) :
    Limits.colimit (power_torsion_stage_diagram (I := I) N) ⟶ N :=
  Limits.colimit.desc _ (power_torsion_stage_cocone (I := I) N)

/-- Helper for Lemma 15.89.7: forgetting the module colimit cocone to additive groups produces a
canonical comparison from the sequential AddCommGrp colimit to the forgotten module colimit. -/
private noncomputable def power_torsion_stage_add_colimit_iso
    (N : ModuleCat R) :
    Limits.colimit
        ((power_torsion_stage_diagram (I := I) N) ⋙
          forget₂ (ModuleCat R) AddCommGrpCat) ≅
      (forget₂ (ModuleCat R) AddCommGrpCat).obj
        (Limits.colimit (power_torsion_stage_diagram (I := I) N)) := by
  let c := Limits.colimit.cocone (power_torsion_stage_diagram (I := I) N)
  let hc : IsColimit c := Limits.colimit.isColimit _
  let hcAdd :
      IsColimit ((forget₂ (ModuleCat R) AddCommGrpCat).mapCocone c) := by
    exact isColimitOfPreserves (forget₂ (ModuleCat R) AddCommGrpCat) hc
  -- Proof comment: the forgotten module colimit cocone is still colimiting in additive groups, so
  -- the canonical AddCommGrp colimit identifies with the forgotten module colimit.
  exact IsColimit.coconePointUniqueUpToIso
    (Limits.colimit.isColimit
      ((power_torsion_stage_diagram (I := I) N) ⋙ forget₂ (ModuleCat R) AddCommGrpCat))
    hcAdd

/-- Helper for Lemma 15.89.7: on each stage, the AddCommGrp comparison map carries the canonical
colimit leg to the forgotten module-colimit leg. -/
private theorem power_torsion_stage_add_colimit_iso_hom_comp
    (N : ModuleCat R) (n : ℕ) :
    Limits.colimit.ι
        ((power_torsion_stage_diagram (I := I) N) ⋙ forget₂ (ModuleCat R) AddCommGrpCat) n ≫
      (power_torsion_stage_add_colimit_iso (I := I) N).hom =
        ((forget₂ (ModuleCat R) AddCommGrpCat).mapCocone
          (Limits.colimit.cocone (power_torsion_stage_diagram (I := I) N))).ι.app n := by
  -- Proof comment: this is the defining property of the cocone-point comparison isomorphism.
  simpa [power_torsion_stage_add_colimit_iso] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (Limits.colimit.isColimit
        ((power_torsion_stage_diagram (I := I) N) ⋙ forget₂ (ModuleCat R) AddCommGrpCat))
      (isColimitOfPreserves
        (forget₂ (ModuleCat R) AddCommGrpCat)
        (Limits.colimit.isColimit (power_torsion_stage_diagram (I := I) N)))
      n)

/-- Helper for Lemma 15.89.7: after forgetting to additive groups, the canonical colimit map from
the stage system to `N` agrees with the descended sequential AddCommGrp map. -/
private theorem power_torsion_stage_add_desc_eq
    (N : ModuleCat R) :
    sequential_addCommGrp_colimit_desc
        (fun n ↦
          (((power_torsion_stage_diagram (I := I) N) ⋙
              forget₂ (ModuleCat R) AddCommGrpCat).map
            (homOfLE (Nat.le_succ n))))
        (fun n ↦
          AddCommGrpCat.ofHom
            ((ModuleCat.ofHom ((Ideal.powerTorsion I N (n + 1)).subtype)).hom.toAddMonoidHom))
        (fun n ↦ by
          -- Proof comment: the stage-to-ambient maps are compatible with the successor inclusions.
          ext x
          rfl) =
      (power_torsion_stage_add_colimit_iso (I := I) N).hom ≫
        AddCommGrpCat.ofHom
          ((power_torsion_stage_colimit_to_module (I := I) N).hom.toAddMonoidHom) := by
  -- Proof comment: both morphisms out of the AddCommGrp colimit are determined by their values on
  -- the stagewise colimit legs.
  apply Limits.colimit.hom_ext
  intro n
  rw [Limits.colimit.ι_desc, Limits.colimit.ι_desc]
  calc
    Limits.colimit.ι
        ((power_torsion_stage_diagram (I := I) N) ⋙ forget₂ (ModuleCat R) AddCommGrpCat) n ≫
          (power_torsion_stage_add_colimit_iso (I := I) N).hom ≫
            AddCommGrpCat.ofHom
              ((power_torsion_stage_colimit_to_module (I := I) N).hom.toAddMonoidHom) =
      ((forget₂ (ModuleCat R) AddCommGrpCat).mapCocone
          (Limits.colimit.cocone (power_torsion_stage_diagram (I := I) N))).ι.app n ≫
            AddCommGrpCat.ofHom
              ((power_torsion_stage_colimit_to_module (I := I) N).hom.toAddMonoidHom) := by
        rw [Category.assoc, power_torsion_stage_add_colimit_iso_hom_comp (I := I) N n]
    _ =
      AddCommGrpCat.ofHom
        ((ModuleCat.ofHom ((Ideal.powerTorsion I N (n + 1)).subtype)).hom.toAddMonoidHom) := by
        rw [power_torsion_stage_colimit_to_module, Limits.colimit.ι_desc]
        rfl

/-- Helper for Lemma 15.89.7: if a stage element maps to zero in `N`, then it is already zero in
the next stage of the sequential system. -/
private theorem power_torsion_stage_kernel_killed
    (N : ModuleCat R) (n : ℕ) (x : ((power_torsion_stage_diagram (I := I) N) ⋙
      forget₂ (ModuleCat R) AddCommGrpCat).obj n)
    (hx :
      (AddCommGrpCat.ofHom
        ((ModuleCat.ofHom ((Ideal.powerTorsion I N (n + 1)).subtype)).hom.toAddMonoidHom)).hom
        x = 0) :
    ((((power_torsion_stage_diagram (I := I) N) ⋙
        forget₂ (ModuleCat R) AddCommGrpCat).map
      (homOfLE (Nat.le_succ n))).hom x) = 0 := by
  -- Proof comment: the stage-to-ambient map is the subtype inclusion, so zero image forces the
  -- stage element itself to be zero.
  have hx0 : x = 0 := by
    apply Subtype.ext
    simpa using hx
  simpa [hx0]

/-- Helper for Lemma 15.89.7: the canonical colimit map from the stage diagram to `N` is
injective. -/
private theorem power_torsion_stage_colimit_to_module_injective
    (N : ModuleCat R) :
    Function.Injective (power_torsion_stage_colimit_to_module (I := I) N).hom := by
  intro z₁ z₂ hEq
  apply sub_eq_zero.mp
  let eAdd := power_torsion_stage_add_colimit_iso (I := I) N
  have hzAdd :
      (sequential_addCommGrp_colimit_desc
        (fun n ↦
          (((power_torsion_stage_diagram (I := I) N) ⋙
              forget₂ (ModuleCat R) AddCommGrpCat).map
            (homOfLE (Nat.le_succ n))))
        (fun n ↦
          AddCommGrpCat.ofHom
            ((ModuleCat.ofHom ((Ideal.powerTorsion I N (n + 1)).subtype)).hom.toAddMonoidHom))
        (fun n ↦ by
          ext x
          rfl)).hom
        (eAdd.hom.hom (z₁ - z₂)) = 0 := by
    -- Proof comment: rewrite the forgotten module-colimit map through the canonical AddCommGrp
    -- colimit comparison, then use the assumed equality in `N`.
    rw [power_torsion_stage_add_desc_eq (I := I) N]
    change
      ((AddCommGrpCat.ofHom
          ((power_torsion_stage_colimit_to_module (I := I) N).hom.toAddMonoidHom)).hom
        (eAdd.hom.hom (z₁ - z₂))) = 0
    simpa [map_sub, hEq]
  have hzZero :
      eAdd.hom.hom (z₁ - z₂) = 0 := by
    exact sequential_addCommGrp_colimit_desc_eq_zero_of_kernel_killed
      (fun n ↦
        (((power_torsion_stage_diagram (I := I) N) ⋙
            forget₂ (ModuleCat R) AddCommGrpCat).map
          (homOfLE (Nat.le_succ n))))
      (fun n ↦
        AddCommGrpCat.ofHom
          ((ModuleCat.ofHom ((Ideal.powerTorsion I N (n + 1)).subtype)).hom.toAddMonoidHom))
      (fun n ↦ by
        ext x
        rfl)
      (power_torsion_stage_kernel_killed (I := I) N)
      hzAdd
  have hzBack := congrArg eAdd.inv.hom hzZero
  simpa using hzBack

/-- Helper for Lemma 15.89.7: the canonical colimit map from the stage diagram to `N` is
surjective because every element appears in some finite torsion stage. -/
private theorem power_torsion_stage_colimit_to_module_surjective
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    Function.Surjective (power_torsion_stage_colimit_to_module (I := I) N).hom := by
  intro x
  obtain ⟨n, hx⟩ := mem_power_torsion_stage_succ (I := I) hN x
  refine ⟨(Limits.colimit.ι (power_torsion_stage_diagram (I := I) N) n).hom ⟨x, hx⟩, ?_⟩
  -- Proof comment: the descended colimit map restricts to the literal inclusion on each stage.
  change
    (((Limits.colimit.ι (power_torsion_stage_diagram (I := I) N) n) ≫
        power_torsion_stage_colimit_to_module (I := I) N).hom ⟨x, hx⟩) = x
  rw [power_torsion_stage_colimit_to_module, Limits.colimit.ι_desc]
  rfl

/-- Helper for Lemma 15.89.7: the colimit of the positive power-torsion stage diagram is the
ambient module itself. -/
private noncomputable def power_torsion_stage_colimit_module_iso
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    Limits.colimit (power_torsion_stage_diagram (I := I) N) ≅ N :=
  -- Proof comment: the canonical colimit map is bijective, so it upgrades to a module isomorphism.
  (LinearEquiv.ofBijective
    (power_torsion_stage_colimit_to_module (I := I) N).hom
    ⟨power_torsion_stage_colimit_to_module_injective (I := I) N,
      power_torsion_stage_colimit_to_module_surjective (I := I) N hN⟩).toModuleIso

/-- Helper for Lemma 15.89.7: because the degree-zero single-complex functor preserves colimits,
the colimit of the stage complexes is the degree-zero complex on the stage-module colimit. -/
private noncomputable def power_torsion_stage_complex_colimit_iso
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    Limits.colimit (power_torsion_stage_complex_diagram (I := I) N) ≅
      (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N :=
  -- Proof comment: first use preservation of colimits by `singleFunctor`, then insert the already
  -- proved colimit identification for the underlying stage modules.
  ((CategoryTheory.preservesColimitIso
      (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ))
      (power_torsion_stage_diagram (I := I) N)).symm) ≪≫
    (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).mapIso
      (power_torsion_stage_colimit_module_iso (I := I) N hN)

/-- Helper for Lemma 15.89.7: after applying `Q`, the colimit of the stage complexes is the
canonical degree-zero derived object on `N`. -/
private noncomputable def power_torsion_stage_colimit_single0_iso
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    DerivedCategory.Q.obj (Limits.colimit (power_torsion_stage_complex_diagram (I := I) N)) ≅
      ModuleCat.single0Functor.obj N :=
  -- Proof comment: the cochain-level colimit comparison becomes the desired derived comparison by
  -- functoriality of `Q` and the standard `singleFunctorIsoCompQ` identification.
  (DerivedCategory.Q.mapIso
      (power_torsion_stage_complex_colimit_iso (I := I) N hN)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app N).symm

/-- Helper for Lemma 15.89.7: derived tensor product is functorial in the right variable after
transporting across the tensor symmetry. -/
noncomputable def derivedTensorProduct_right_map_iso
    {X Y Z : DMod} (e : Y ≅ Z) :
    X ⊗[R]^L Y ≅ X ⊗[R]^L Z :=
  derivedTensorProduct_comm X Y ≪≫
    ((derivedTensorProduct X).mapIso e) ≪≫
      (derivedTensorProduct_comm Z X)

/-- Helper for Lemma 15.89.7: shifting the right tensor factor shifts the total derived tensor
product by the same amount. -/
noncomputable def derivedTensorProduct_right_shift_iso
    (X Y : DMod) (d : ℤ) :
    X ⊗[R]^L (Y⟦d⟧) ≅ (X ⊗[R]^L Y)⟦d⟧ :=
  derivedTensorProduct_comm X (Y⟦d⟧) ≪≫
    (((derivedTensorProduct_commShift X).commShiftIso d).app Y) ≪≫
      ((shiftFunctor DMod d).mapIso (derivedTensorProduct_comm Y X))

/-- Helper for Lemma 15.89.7: bounded-derived homology commutes with shifting in the expected
degree. -/
noncomputable def boundedDerived_homology_shift_iso
    (M : DbMod) (d i : ℤ) :
    ((Hb i).obj ((shiftFunctor DbMod d).obj M)) ≅ ((Hb (i + d)).obj M) := by
  -- Proof comment: commute the bounded-derived inclusion past the shift, then apply the ambient
  -- homology shift isomorphism.
  dsimp [boundedDerivedHomologyFunctor]
  exact
    ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
      (((ObjectProperty.ι DerivedCategory.TStructure.t.bounded).commShiftIso d).app M)) ≪≫
      (((DerivedCategory.homologyFunctor (ModuleCat R) 0).shiftIso d i (i + d)
        (add_comm d i)).app M.obj)

/-- Helper for Lemma 15.89.7: tensoring a nonpositive derived module with a degree-zero module
stays nonpositive. -/
private lemma tensor_single_isLE_zero_of_isLE_zero
    {S : Type u} [CommRing S]
    (L : DerivedCategory (ModuleCat S)) (hL : L.IsLE 0) (M : ModuleCat S) :
    (L ⊗[S]^L ModuleCat.single0Functor.obj M).IsLE 0 := by
  -- Proof comment: replace `L` by a strict `≤ 0` cochain representative, where positive
  -- homology of the tensor complex vanishes because the positive tensor term itself vanishes.
  rw [DerivedCategory.isLE_iff]
  intro i hi
  letI : L.IsLE 0 := hL
  obtain ⟨P, hPle, ⟨eP⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE L 0
  letI : P.IsStrictlyLE 0 := hPle
  let Tsingle : CochainComplex (ModuleCat S) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat S) (0 : ℤ)).obj M
  have hTensorTermZero :
      IsZero
        ((((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P).X i) := by
    -- Proof comment: right tensoring preserves the vanishing of the positive degree-`i` term.
    change IsZero (((CategoryTheory.MonoidalCategory.tensorRight M).obj (P.X i)))
    exact CategoryTheory.Functor.map_isZero
      (CategoryTheory.MonoidalCategory.tensorRight M)
      (P.isZero_of_isStrictlyLE 0 i hi)
  have hOrdinaryHomologyZero :
      IsZero ((HomologicalComplex.tensorObj P Tsingle).homology i) := by
    let eSc := tensor_single0_shortComplex_iso (R := S) P M i
    have hMappedHomologyZero :
        IsZero
          ((((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P).sc i).homology := by
      -- Proof comment: with zero middle term, the short complex computing degree-`i` homology is
      -- exact.
      exact
        ShortComplex.isZero_homology_of_isZero_X₂
          (S := (((CategoryTheory.MonoidalCategory.tensorRight M).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P).sc i)
          (by simpa [HomologicalComplex.sc] using hTensorTermZero)
    exact (ShortComplex.homologyMapIso eSc).isZero_iff.2 hMappedHomologyZero
  have hRepresentedHomologyZero :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((DerivedCategory.Q.obj P) ⊗[S]^L ModuleCat.single0Functor.obj M)) := by
    -- Proof comment: compare ordinary tensor-complex homology with derived tensor homology.
    exact
      hOrdinaryHomologyZero.of_iso
        (tensorObj_single0_homology_iso_derivedTensor (R := S) P i M)
  -- Proof comment: transport the vanishing statement back across the chosen strict model of `L`.
  exact
    ((DerivedCategory.homologyFunctor (ModuleCat S) i).mapIso
      ((derivedTensorProduct (ModuleCat.single0Functor.obj M)).mapIso eP)).isZero_iff.2
      hRepresentedHomologyZero

/-- Helper for Lemma 15.89.7: composing a surjective map out of the base ring of a trivial
square-zero extension with the first projection stays surjective. -/
private theorem trivSqZeroExt_fst_comp_surjective
    {A B : Type u} [CommRing A] [CommRing B]
    {M : Type u} [AddCommGroup M] [Module A M]
    (f : A →+* B)
    (hf : Function.Surjective f) :
    Function.Surjective (f.comp (TrivSqZeroExt.fstHom ℤ A M).toRingHom) := by
  -- Proof comment: lift a target element through `f` and then include that lift into the
  -- square-zero extension via the canonical first-summand embedding.
  intro x
  rcases hf x with ⟨a, rfl⟩
  refine ⟨TrivSqZeroExt.inl a, ?_⟩
  rfl

/-- Helper for Lemma 15.89.7: the intrinsic square-zero ideal lies in the kernel of any composite
`TrivSqZeroExt A M → A → B` through the first projection. -/
private theorem trivSqZeroExt_kerIdeal_le_ker_fst_comp
    {A B : Type u} [CommRing A] [CommRing B]
    {M : Type u} [AddCommGroup M] [Module A M]
    (f : A →+* B) :
    TrivSqZeroExt.kerIdeal A M ≤ RingHom.ker (f.comp (TrivSqZeroExt.fstHom ℤ A M).toRingHom) := by
  -- Proof comment: elements of the square-zero ideal have zero first component, so every such
  -- element maps to zero after applying the projection-based composite.
  intro x hx
  rw [TrivSqZeroExt.mem_kerIdeal_iff_inr] at hx
  rcases hx with ⟨m, rfl⟩
  rfl

/-- Helper for Lemma 15.89.7: the natural quotient map `R / I^(n + 1) → R / I` is surjective. -/
private theorem quotient_pow_to_modIdeal_surjective
    (n : ℕ) :
    Function.Surjective
      (Ideal.Quotient.factorₐ R
        (show I ^ (n + 1) ≤ I by
          simpa using Ideal.pow_le_self (show n + 1 ≠ 0 by omega))) := by
  intro x
  refine Quotient.inductionOn' x ?_
  intro r
  refine ⟨Ideal.Quotient.mk (I ^ (n + 1)) r, ?_⟩
  rfl

/-- Helper for Lemma 15.89.7: the kernel of `R / I^(n + 1) → R / I` is nilpotent. -/
private theorem quotient_pow_to_modIdeal_kernel_isNilpotent
    (n : ℕ) :
    IsNilpotent
      (RingHom.ker
        ((Ideal.Quotient.factorₐ R
          (show I ^ (n + 1) ≤ I by
            simpa using Ideal.pow_le_self (show n + 1 ≠ 0 by omega))).toRingHom)) := by
  rw [Ideal.isNilpotent_iff_le_nilradical]
  intro x hx
  rcases Quotient.exists_rep x with ⟨a, rfl⟩
  rw [mem_nilradical]
  change
    ((Ideal.Quotient.factorₐ R
      (show I ^ (n + 1) ≤ I by
        simpa using Ideal.pow_le_self (show n + 1 ≠ 0 by omega))).toRingHom
      (Ideal.Quotient.mk (I ^ (n + 1)) a)) = 0 at hx
  have ha : a ∈ I := by
    simpa [Ideal.Quotient.factorₐ, Ideal.Quotient.factor, RingHom.comp_apply] using hx
  refine IsNilpotent.mk _ (n + 1) ?_
  change Ideal.Quotient.mk (I ^ (n + 1)) (a ^ (n + 1)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow ha (n + 1)

/-- Helper for Lemma 15.89.7: if a module is annihilated by a power of `I`, then the source
square-zero extension argument upgrades the mod-`I` tensor bound to that module. -/
private theorem derivedTensorProduct_annihilatedModule_isLE_zero_of_modIdeal
    (K : DMod)
    (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (N0 : ModuleCat R) (n : ℕ)
    (hann : I ^ (n + 1) ≤ Module.annihilator R N0) :
    (K ⊗[R]^L ModuleCat.single0Functor.obj N0).IsLE 0 := by
  -- Route correction: the remaining finite-stage source proof passes to the square-zero extension
  -- `R / I^(n + 1) ⊕ N0`, compares its quotient-side test object with `K ⊗^L_R (R / I)[0]`, and
  -- then descends nonpositivity back across the nilpotent quotient.
  -- TODO(Lemma 15.89.7): build the explicit square-zero extension over `R / I^(n + 1)`, prove
  -- the quotient-side and square-zero-side derived tensor comparison isomorphisms, and apply the
  -- nilpotent-descent package from Lemma `15.76.3` to the shifted cohomology objects.
  let _ := hann
  let _ := hKI
  sorry

/-- Helper for Lemma 15.89.7: a positive stagewise `IsLE 0` bound already kills the corresponding
strict tensor-complex homology on a chosen representative of `K`. -/
private theorem strict_tensor_single0_homology_isZero_of_isLE_zero
    (K : DMod) (M : ModuleCat R) {i : ℤ} (hi : 0 < i)
    (hKM : (K ⊗[R]^L ModuleCat.single0Functor.obj M).IsLE 0) :
    IsZero
      ((HomologicalComplex.tensorObj
          (DerivedCategory.Q.objPreimage K)
          ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).homology i) := by
  let E : CochainComplex (ModuleCat R) ℤ := DerivedCategory.Q.objPreimage K
  have hModelZero :
      IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
          ((DerivedCategory.Q.obj E) ⊗[R]^L ModuleCat.single0Functor.obj M)) := by
    -- Proof comment: first transport the given `IsLE 0` bound from `K` to the canonical strict
    -- model `Q.objPreimage K`.
    exact
      ((DerivedCategory.isLE_iff.mp hKM) i hi).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso
          ((derivedTensorProduct (ModuleCat.single0Functor.obj M)).mapIso
            (DerivedCategory.Q.objObjPreimageIso K)))
  -- Proof comment: the strict tensor complex computes the same homology as the derived tensor
  -- object with the degree-zero module `M[0]`.
  exact
    hModelZero.of_iso
      (tensorObj_single0_homology_iso_derivedTensor (R := R) E i M).symm

/-- Helper for Lemma 15.89.7: once every positive power-torsion stage has the tensor bound, the
same bound holds for the whole `I`-power torsion module via the sequential homotopy colimit. -/
private theorem derivedTensorProduct_power_torsion_stages_isLE_zero_of_modIdeal
    (K : DMod)
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N)
    (hStage :
      ∀ n : ℕ,
        (K ⊗[R]^L ModuleCat.single0Functor.obj
          ((power_torsion_stage_diagram (I := I) N).obj n)).IsLE 0) :
    (K ⊗[R]^L ModuleCat.single0Functor.obj N).IsLE 0 := by
  -- Route correction: the explicit sequential system `N[I^(n+1)][0]` already presents `N[0]` as
  -- a derived homotopy colimit; the remaining work is to transport that presentation through the
  -- fixed-left derived tensor functor and then use the Chapter 13 homology-colimit comparison in
  -- positive degrees.
  -- TODO(Lemma 15.89.7): the remaining step is now purely the sequential homotopy-colimit
  -- transport. The strict helper `strict_tensor_single0_homology_isZero_of_isLE_zero` above
  -- already converts each stagewise `IsLE 0` bound into vanishing of the positive homology of the
  -- strict tensor complexes `Q.objPreimage K ⊗ N[I^(n+1)][0]`; what is still missing is a usable
  -- dependency-closed comparison between the homology of the sequential colimit of those strict
  -- tensor complexes and the homology of `K ⊗^L_R N[0]`.
  let _ := hN
  let _ := hStage
  sorry

-- Proof sketch: write an `I`-power torsion module `N` as the filtered colimit of its submodules
-- annihilated by powers of `I`, reduce to the case where some `I^n` kills `N`, and then apply
-- the quotient case `R ⧸ I^n` after passing to the square-zero extension `R ⧸ I^n ⊕ N` as in the
-- textbook proof.
/-- Lemma 15.89.7 (2): if `K ⊗_R^{\mathbf L} (R ⧸ I)[0]` has no positive cohomology, then
`K ⊗_R^{\mathbf L} N[0]` has no positive cohomology for every `I`-power torsion `R`-module
`N`. -/
@[stacks 0H82]
theorem derivedTensorProduct_idealPowerTorsionModule_isLE_zero_of_modIdeal
    (K : DMod)
    (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    (K ⊗[R]^L ModuleCat.single0Functor.obj N).IsLE 0 := by
  -- Route correction: the source proof first controls the annihilated stages `N[I^(n+1)]`, then
  -- passes to the whole module through the explicit sequential hocolim presentation.
  have hStage :
      ∀ n : ℕ,
        (K ⊗[R]^L ModuleCat.single0Functor.obj
          ((power_torsion_stage_diagram (I := I) N).obj n)).IsLE 0 := by
    intro n
    -- Proof comment: each stage is annihilated by `I^(n+1)`, so the finite-stage square-zero
    -- argument applies directly.
    exact
      derivedTensorProduct_annihilatedModule_isLE_zero_of_modIdeal
        (I := I) K hKI
        ((power_torsion_stage_diagram (I := I) N).obj n) n
        (power_torsion_stage_diagram_annihilator (I := I) N n)
  -- Proof comment: the explicit stage diagram exhausts `N`, so the stagewise bounds pass to the
  -- whole module through the sequential homotopy-colimit comparison.
  exact
    derivedTensorProduct_power_torsion_stages_isLE_zero_of_modIdeal
      (I := I) K N hN hStage

/-- Helper for Lemma 15.89.7: once the degree-zero tensor bound is known for a module, the same
bound holds for the corresponding single object placed in any nonpositive degree. -/
private theorem tensor_singleFunctor_isLE_zero_of_single0
    (K : DMod) {M : ModuleCat R} {c : ℤ}
    (hK : (K ⊗[R]^L ModuleCat.single0Functor.obj M).IsLE 0)
    (hc : c ≤ 0) :
    (K ⊗[R]^L (DerivedCategory.singleFunctor (ModuleCat R) c).obj M).IsLE 0 := by
  let eSingle :
      (DerivedCategory.singleFunctor (ModuleCat R) c).obj M ≅
        (ModuleCat.single0Functor.obj M)⟦-c⟧ :=
    -- Proof comment: rewrite the degree-`c` single object as the shifted degree-zero single
    -- object on the same module.
    (shiftShiftNeg ((DerivedCategory.singleFunctor (ModuleCat R) c).obj M) c).symm ≪≫
      (shiftFunctor DMod (-c)).mapIso
        (singleFunctor_shifted_single0_iso_canonical (R := R) M c)
  have hShifted : (K ⊗[R]^L ((ModuleCat.single0Functor.obj M)⟦-c⟧)).IsLE c := by
    have hBaseShift : ((K ⊗[R]^L ModuleCat.single0Functor.obj M)⟦-c⟧).IsLE c := by
      -- Proof comment: shifting a nonpositive object by `-c` moves the cohomological cutoff from
      -- `0` to `c`.
      letI : (K ⊗[R]^L ModuleCat.single0Functor.obj M).IsLE 0 := hK
      simpa using (t.isLE_shift (K ⊗[R]^L ModuleCat.single0Functor.obj M) 0 (-c) c)
    -- Proof comment: transport the shifted cutoff across the canonical tensor/shift comparison.
    exact
      t.isLE_of_iso
        (derivedTensorProduct_right_shift_iso (R := R) K
          (ModuleCat.single0Functor.obj M) (-c)).symm
        c hBaseShift
  have hShiftedZero : (K ⊗[R]^L ((ModuleCat.single0Functor.obj M)⟦-c⟧)).IsLE 0 := by
    -- Proof comment: the stronger bound `≤ c` implies the desired bound `≤ 0` because `c ≤ 0`.
    rw [DerivedCategory.isLE_iff] at hShifted ⊢
    intro i hi
    exact hShifted i (lt_of_le_of_lt hc hi)
  -- Proof comment: transport the shifted degree-zero bound back to the original degree-`c`
  -- single object.
  exact t.isLE_of_iso ((derivedTensorProduct K).mapIso eSingle) 0 hShiftedZero

/-- Helper for Lemma 15.89.7: a bounded nonpositive derived object whose cohomology is
`I`-power torsion in the finite range `[-n, 0]` inherits the same tensor bound as the degree-zero
module case. -/
private theorem derivedTensorProduct_isLE_zero_of_nonpositive_width
    (K : DMod) (hKI : (K ⊗[R]^L RmodI).IsLE 0) :
    ∀ n : ℕ, ∀ L : DMod,
      L.IsGE (-((n : ℤ))) →
      L.IsLE 0 →
      (∀ i ≤ 0, Module.IsIdealPowerTorsion I ((H i).obj L)) →
      (K ⊗[R]^L L).IsLE 0 := by
  intro n
  induction n with
  | zero =>
      intro L hLge hLle hLt
      letI : L.IsGE 0 := hLge
      letI : L.IsLE 0 := hLle
      rcases DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L 0 with ⟨M, ⟨eL⟩⟩
      let eH : (H 0).obj L ≅ M :=
        -- Proof comment: identify the surviving degree-zero cohomology module of `L` with the
        -- coefficient of its canonical single-object presentation.
        (H 0).mapIso eL ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (0 : ℤ)).app M
      have hMtors : Module.IsIdealPowerTorsion I M := by
        -- Proof comment: transport the degree-zero torsion hypothesis across the canonical
        -- homology identification above.
        exact
          (Module.isIdealPowerTorsion_iff_of_linearEquiv I eH.toLinearEquiv).1
            (hLt 0 (by simp))
      have hTensorSingle : (K ⊗[R]^L ModuleCat.single0Functor.obj M).IsLE 0 := by
        -- Proof comment: the width-zero case is exactly the module statement already proved as
        -- part `(2)`.
        exact
          derivedTensorProduct_idealPowerTorsionModule_isLE_zero_of_modIdeal
            I K hKI M hMtors
      -- Proof comment: replace the concentrated object `L` by its degree-zero single-module
      -- model and conclude from the module case.
      exact t.isLE_of_iso ((derivedTensorProduct K).mapIso eL) 0 hTensorSingle
  | succ n ih =>
      intro L hLge hLle hLt
      let a : ℤ := -((Nat.succ n : ℤ))
      have hLgea : L.IsGE a := by
        simpa [a] using hLge
      letI : L.IsGE a := hLgea
      letI : L.IsLE 0 := hLle
      let T : Triangle DMod := truncGE_step_homologyTriangle L a
      have hT : T ∈ distTriang DMod := truncGE_step_homology_triangle L a
      have hHeadSingle :
          (K ⊗[R]^L ModuleCat.single0Functor.obj ((H a).obj L)).IsLE 0 := by
        -- Proof comment: the first truncation piece is controlled by the module clause applied to
        -- the degree-`a` cohomology module.
        exact
          derivedTensorProduct_idealPowerTorsionModule_isLE_zero_of_modIdeal
            I K hKI ((H a).obj L) (hLt a (by omega))
      have hHead : (K ⊗[R]^L T.obj₁).IsLE 0 := by
        have hHeadA :
            (K ⊗[R]^L (DerivedCategory.singleFunctor (ModuleCat R) a).obj
              ((H a).obj L)).IsLE 0 := by
          -- Proof comment: the first truncation vertex is the degree-`a` single object on
          -- `H^a(L)`, so transport the degree-zero module bound to that degree.
          exact tensor_singleFunctor_isLE_zero_of_single0 (I := I) K hHeadSingle (by omega)
        simpa [T, truncGE_step_homologyTriangle, a] using hHeadA
      have hTailGE : T.obj₃.IsGE (-((n : ℤ))) := by
        -- Proof comment: the lower truncation `τ_{≥ a + 1}L` starts one degree higher, so its
        -- lower support bound is `-n`.
        dsimp [T, truncGE_step_homologyTriangle, a]
        infer_instance
      have hTailLE : T.obj₃.IsLE 0 := by
        -- Proof comment: lower truncation does not create any new positive cohomology.
        dsimp [T, truncGE_step_homologyTriangle, a]
        infer_instance
      have hTailTors :
          ∀ i ≤ 0, Module.IsIdealPowerTorsion I ((H i).obj T.obj₃) := by
        intro i hi
        by_cases hia : i < a + 1
        · have hZero : IsZero ((H i).obj T.obj₃) := by
            -- Proof comment: below the truncation cutoff, the lower tail has vanishing homology.
            exact DerivedCategory.isZero_of_isGE T.obj₃ (a + 1) i hia
          rw [Module.isIdealPowerTorsion_iff]
          intro x
          let _ : Subsingleton ((H i).obj T.obj₃) := ModuleCat.subsingleton_of_isZero hZero
          refine ⟨1, ?_⟩
          intro b
          simpa [Subsingleton.elim x (0 : ((H i).obj T.obj₃))] using
            (smul_zero (b : R) : (b : R) • (0 : ((H i).obj T.obj₃)) = 0)
        · have hle : a + 1 ≤ i := by
            omega
          let eHi : (H i).obj L ≅ (H i).obj T.obj₃ :=
            -- Proof comment: at and above the new cutoff, lower truncation preserves homology.
            @asIso _ _ _ _
              ((H i).map ((t.truncGEπ (a + 1)).app L))
              (isIso_homologyMap_truncGEπ_of_le (𝒜 := ModuleCat R) L (a + 1) i hle)
          exact
            (Module.isIdealPowerTorsion_iff_of_linearEquiv I eHi.toLinearEquiv).1
              (hLt i hi)
      have hTail : (K ⊗[R]^L T.obj₃).IsLE 0 := by
        -- Proof comment: the lower tail has one smaller cohomological width, so the induction
        -- hypothesis applies to it.
        exact ih T.obj₃ hTailGE hTailLE hTailTors
      let F : DMod ⥤ DMod := derivedTensorProduct K
      letI : F.CommShift ℤ := derivedTensorProduct_commShift K
      letI : F.IsTriangulated := derivedTensorProduct_isTriangulated K
      letI : F.Additive := inferInstance
      letI : F.PreservesZeroMorphisms := inferInstance
      have hFT : F.mapTriangle.obj T ∈ distTriang DMod := by
        -- Proof comment: tensoring by the fixed left factor `K` preserves distinguished triangles.
        simpa [F, T] using F.map_distinguished T hT
      have hMidTrunc : (K ⊗[R]^L T.obj₂).IsLE 0 := by
        rw [DerivedCategory.isLE_iff]
        intro i hi
        have h₁ : IsZero ((H i).obj ((F.mapTriangle.obj T).obj₁)) := by
          letI : (F.obj T.obj₁).IsLE 0 := hHead
          -- Proof comment: the first tensor vertex already has no positive cohomology.
          simpa [F] using (DerivedCategory.isZero_of_isLE (F.obj T.obj₁) 0 i hi)
        have h₃ : IsZero ((H i).obj ((F.mapTriangle.obj T).obj₃)) := by
          letI : (F.obj T.obj₃).IsLE 0 := hTail
          -- Proof comment: the same holds for the inductive lower tail.
          simpa [F] using (DerivedCategory.isZero_of_isLE (F.obj T.obj₃) 0 i hi)
        -- Proof comment: exactness of homology on the mapped truncation triangle forces the
        -- middle positive homology to vanish once both outer vertices vanish.
        simpa [F] using
          isZero_homology_obj₂_of_distinguished_triangle_of_outer_zeros
            (R' := R) (T := F.mapTriangle.obj T) hFT i h₁ h₃
      letI : IsIso ((t.truncGEπ a).app L) := (t.isGE_iff_isIso_truncGEπ_app a L).1 hLgea
      let eMid : T.obj₂ ≅ L := by
        -- Proof comment: because `L` is already concentrated in degrees `≥ a`, its lower
        -- truncation at `a` is canonically isomorphic to `L` itself.
        simpa [T, truncGE_step_homologyTriangle, a] using
          (asIso ((t.truncGEπ a).app L)).symm
      -- Proof comment: the middle vertex of the truncation triangle is `L` itself, so the bound
      -- on the tensor of the middle truncation object is the desired result.
      exact t.isLE_of_iso ((derivedTensorProduct K).mapIso eMid) 0 hMidTrunc

-- Proof sketch: this is the module case `(2)` specialized to the `I`-power torsion module
-- `R ⧸ I^n`, using `Module.isIdealPowerTorsion_quotient_pow`.
/-- Lemma 15.89.7 (1): if `K ⊗_R^{\mathbf L} (R ⧸ I)[0]` has no positive cohomology, then
`K ⊗_R^{\mathbf L} (R ⧸ I^n)[0]` has no positive cohomology for every positive `n`. -/
@[stacks 0H82]
theorem derivedTensorProduct_idealPowQuotient_isLE_zero_of_modIdeal
    (K : DMod)
    (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (n : ℕ+) :
    (K ⊗[R]^L ModuleCat.single0Functor.obj (ModuleCat.of R (R ⧸ I ^ (n : ℕ)))).IsLE 0 := by
  simpa using
    derivedTensorProduct_idealPowerTorsionModule_isLE_zero_of_modIdeal
      I K hKI (ModuleCat.of R (R ⧸ I ^ (n : ℕ)))
      (Module.isIdealPowerTorsion_quotient_pow I (n : ℕ))

-- Proof sketch: use part `(2)` for each possibly nonzero cohomology object `H^i(M)` with `i ≤ 0`,
-- since `hMle` already forces `H^i(M) = 0` for `i > 0`; then induct on the number of nonzero
-- cohomology objects of the bounded complex `M` via the truncation distinguished triangles from
-- Remark `13.12.4`.
/-- Lemma 15.89.7 (3): if `M` is a bounded derived `R`-complex whose nonpositive cohomology
modules are `I`-power torsion and which has no positive cohomology, then
`K ⊗_R^{\mathbf L} M` has no positive cohomology whenever
`K ⊗_R^{\mathbf L} (R ⧸ I)[0]` has none. -/
@[stacks 0H82]
theorem derivedTensorProduct_boundedIdealPowerTorsion_isLE_zero_of_modIdeal
    (K : DMod)
    (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (M : DbMod)
    (hMtors : ∀ i ≤ 0, Module.IsIdealPowerTorsion I ((Hb i).obj M))
    (hMle : M.obj.IsLE 0) :
    (K ⊗[R]^L M.obj).IsLE 0 := by
  -- Route correction: clause `(3)` depends only on the already stated module case `(2)`, so the
  -- remaining work here is the source truncation induction on the finite nonzero cohomology range
  -- of `M`.
  rcases (derivedCategory_t_bounded_iff M.obj).1 M.property with ⟨⟨c, hc⟩, _⟩
  have hMge : M.obj.IsGE c := by
    -- Proof comment: boundedness supplies a finite lower cohomological cutoff for `M`.
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact hc i hi
  let c₀ : ℤ := min c 0
  have hMge₀ : M.obj.IsGE c₀ := by
    -- Proof comment: replace the bounded-below cutoff by a nonpositive one so it can be written
    -- as `-n` for some natural number.
    exact t.isGE_of_ge M.obj c₀ c (by exact min_le_left _ _) hMge
  let n : ℕ := Int.toNat (-c₀)
  have hc₀ : c₀ = -((n : ℤ)) := by
    -- Proof comment: `c₀ ≤ 0`, so converting `-c₀` to a natural number and back recovers `c₀`.
    have hc₀_nonpos : c₀ ≤ 0 := by
      exact min_le_right _ _
    omega
  have hMgeN : M.obj.IsGE (-((n : ℤ))) := by
    simpa [hc₀] using hMge₀
  have hMtors' : ∀ i ≤ 0, Module.IsIdealPowerTorsion I ((H i).obj M.obj) := by
    intro i hi
    -- Proof comment: bounded-derived homology is the ambient derived homology of the underlying
    -- object.
    simpa [boundedDerivedHomologyFunctor] using hMtors i hi
  -- Proof comment: apply the finite-width truncation induction to the underlying bounded object.
  exact
    derivedTensorProduct_isLE_zero_of_nonpositive_width
      (I := I) K hKI n M.obj hMgeN hMle hMtors'

end

end CategoryTheory
