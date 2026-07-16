import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_87_10
import StacksProject_2024.stacks_project.Chap15.Lemma_15_92_17
import StacksProject_2024.stacks_project.Chap15.Lemma_15_94_6
import StacksProject_2024.stacks_project.Chap15.PrincipalIdeal
import StacksProject_2024.stacks_project.Chap15.Remark_15_94_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open scoped PrincipalIdeal PrincipalTateModule

universe u

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Example `15.94.5`.
- primary domain: principal derived completion of modules and derived objects, together with the
  degree-`-1`/`0` module case and the general cohomology short exact sequence;
- sampled owner declarations:
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `principalTateModule`,
  `DerivedCategory.derivedCompletionOf`;
- sampled bridge companion declarations:
  `principalDerivedCompletion_cohomology_has_comparison_diagram`;
- best owner abstraction: the source-facing owner is the canonical derived completion object
  `((single0).obj M)^∧[(f), principalIdeal_fg f]`, together with the chapter owners
  `principalTateModule` and `principalPowerQuotientTower`/`principalPowerTorsionTower`; the later
  comparison theorem from `Lemma_15_94_6` is bridge/view data, while the degree-zero short exact
  sequence itself is owned canonically by the Milnor theorem
  `CategoryTheory.derivedLimit_cohomology_shortExact` specialized to the principal completion
  tower;
- primitive vs. derived:
  primitive data are the ring element `f`, the module `M`, and the canonical principal towers
  `principalPowerQuotientTower f M` and `principalPowerTorsionTower f M`, together with the
  derived object `K` and degree `p` for the general cohomology sequence;
  derived API is the `H^{-1}` Tate-module comparison, the module-level `H^0` short exact sequence
  against the ordinary completion tower, the general short exact sequence
  `0 → H^0(H^p(K)^∧) → H^p(K^∧) → T_f(H^{p+1}(K)) → 0`, and the amplitude bound below.

Source/core/bridge triage:
- `source-facing`: the `H^{-1}`/`H^0` module statements for
  `((single0).obj M)^∧[(f), principalIdeal_fg f]`, the general short exact sequence for
  `H^p(K^∧[(f), principalIdeal_fg f])`, and the amplitude bound;
- `core/canonical`: `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `principalTateModule`, `principalPowerQuotientTower`, `principalPowerTorsionTower`, and
  `DerivedCategory.derivedCompletionOf`;
- `bridge/view`: the later comparison theorem from `Lemma_15_94_6`, specialized to `K = M[0]` and
  `p = -1, 0` in the module case and used below to recover the general cohomology sequence. -/

section

variable {A : Type u} [CommRing A]

local notation "ModA" => ModuleCat A
local notation "DMod" => DerivedCategory ModA
local notation "H" => DerivedCategory.homologyFunctor ModA
local notation "single0" => DerivedCategory.singleFunctor ModA (0 : ℤ)

/- Example 15.94.5: the source-facing Tate module in this chapter is the owner
`principalTateModule`, written `T[f] M`. -/
recall principalTateModule

/- Companion bridge: Lemma `15.94.6` records the comparison rows and columns used to recover the
source-facing module statements below. -/

section

variable (f : A)

local notation "I" => ((f) : Ideal A)
local notation "hI" => principalIdeal_fg f

/-- Helper for Example 15.94.5: the inverse limit and first derived inverse limit of a sequential
system of modules vanish when every stage is zero. -/
theorem sequentialModule_limit_and_firstDerivedLimit_isZero_of_stagewise_isZero
    (Msys : SequentialInverseSystem ModA)
    (hMsys : ∀ n : ℕ, IsZero (Msys.obj (op n))) :
    IsZero (limit Msys) ∧ IsZero (firstDerivedLimit Msys) := by
  constructor
  · -- Proof comment: each projection from the limit lands in a zero stage, so the identity on
    -- the limit is zero.
    refine (IsZero.iff_id_eq_zero _).2 ?_
    apply limit.hom_ext
    intro n
    have hzero : IsZero (Msys.obj n) := by
      simpa using hMsys n.unop
    exact hzero.eq_of_tgt _ _
  · -- Proof comment: the defining product object of `R^1 lim` is zero, so the difference map is
    -- epi and its cokernel vanishes.
    have hprod : IsZero (∏ᶜ inverseSystemFamily Msys) := by
      refine (IsZero.iff_id_eq_zero _).2 ?_
      apply Pi.hom_ext
      intro n
      exact (hMsys n).eq_of_tgt _ _
    have hEpi : Epi (derivedLimitDifferenceMap Msys) := by
      refine ⟨fun g h _ ↦ hprod.eq_of_src g h⟩
    let _ : Epi (derivedLimitDifferenceMap Msys) := hEpi
    simpa [firstDerivedLimit] using
      (isZero_cokernel_of_epi (derivedLimitDifferenceMap Msys))

/-- Helper for Example 15.94.5: the cohomology of a degree-zero single object vanishes away from
degree `0`. -/
theorem single_zero_complex_homology_isZero_of_ne
    (M : ModA) (p : ℤ) (hp : p ≠ 0) :
    IsZero ((H p).obj ((single0).obj M)) := by
  -- Proof comment: `M[0]` is both `IsGE 0` and `IsLE 0`, so any nonzero degree cohomology group
  -- vanishes by the standard `t`-structure bounds.
  by_cases hlt : p < 0
  · let _ : ((single0).obj M).IsGE 0 := inferInstance
    exact DerivedCategory.isZero_of_isGE _ 0 p hlt
  · have hgt : 0 < p := by
      omega
    let _ : ((single0).obj M).IsLE 0 := inferInstance
    exact DerivedCategory.isZero_of_isLE _ 0 p hgt

/-- Helper for Example 15.94.5: principal derived completion preserves zero objects on
degree-zero single complexes. -/
theorem principalDerivedCompletion_single0_isZero_of_isZero
    (M : ModA) (hM : IsZero M) :
    IsZero (((single0).obj M)^∧[I, hI]) := by
  -- Proof comment: both `single0` and derived completion are functors, so they transport the
  -- zero-object structure directly.
  exact Functor.map_isZero (DerivedCategory.derivedCompletion I hI)
    (Functor.map_isZero single0 hM)

/-- Helper for Example 15.94.5: the principal Tate module of a zero module is zero. -/
theorem principalTateModule_isZero_of_isZero
    (M : ModA) (hM : IsZero M) :
    IsZero (T[f] M) := by
  have hstage : ∀ n : ℕ, IsZero ((principalPowerTorsionTower f M).obj (op n)) := by
    intro n
    -- Proof comment: a finite torsion submodule of a zero module is again zero.
    let _ : Subsingleton M := ModuleCat.subsingleton_of_isZero hM
    let _ : Subsingleton ((principalPowerTorsionTower f M).obj (op n)) := by
      change Subsingleton (M[f ^ (n + 1)])
      infer_instance
    exact ModuleCat.isZero_of_subsingleton _
  exact
    (sequentialModule_limit_and_firstDerivedLimit_isZero_of_stagewise_isZero
      (Msys := principalPowerTorsionTower f M) hstage).1

/-- Helper for Example 15.94.5: an isomorphism of modules induces an isomorphism of their
principal-power torsion towers. -/
theorem principalPowerTorsionTower_iso_of_iso
    {M N : ModA} (e : M ≅ N) :
    Nonempty (principalPowerTorsionTower f M ≅ principalPowerTorsionTower f N) := by
  let stageHom :
      ∀ n : ℕ,
        (principalPowerTorsionTower f M).obj (op n) ⟶
          (principalPowerTorsionTower f N).obj (op n) :=
    fun n ↦
      ModuleCat.ofHom
        { toFun := fun x ↦
            ⟨e.hom.hom x.1, by
              have hx : (f ^ (n + 1)) • x.1 = 0 := by
                simpa [Submodule.mem_torsionBy_iff] using x.2
              change e.hom.hom ((f ^ (n + 1)) • x.1) = 0
              simpa using congrArg e.hom.hom hx⟩
          map_add' := by
            intro x y
            ext
            simp
          map_smul' := by
            intro a x
            ext
            simp }
  let stageInv :
      ∀ n : ℕ,
        (principalPowerTorsionTower f N).obj (op n) ⟶
          (principalPowerTorsionTower f M).obj (op n) :=
    fun n ↦
      ModuleCat.ofHom
        { toFun := fun x ↦
            ⟨e.inv.hom x.1, by
              have hx : (f ^ (n + 1)) • x.1 = 0 := by
                simpa [Submodule.mem_torsionBy_iff] using x.2
              change e.inv.hom ((f ^ (n + 1)) • x.1) = 0
              simpa using congrArg e.inv.hom hx⟩
          map_add' := by
            intro x y
            ext
            simp
          map_smul' := by
            intro a x
            ext
            simp }
  have hstageHom_naturality :
      ∀ n : ℕ,
        (principalPowerTorsionTower f M).map (homOfLE (Nat.le_succ n)).op ≫ stageHom (n + 1) =
          stageHom n ≫ (principalPowerTorsionTower f N).map (homOfLE (Nat.le_succ n)).op := by
    intro n
    ext x
    simp [stageHom, principalPowerTorsionStep]
  have hstageInv_naturality :
      ∀ n : ℕ,
        (principalPowerTorsionTower f N).map (homOfLE (Nat.le_succ n)).op ≫ stageInv (n + 1) =
          stageInv n ≫ (principalPowerTorsionTower f M).map (homOfLE (Nat.le_succ n)).op := by
    intro n
    ext x
    simp [stageInv, principalPowerTorsionStep]
  let α : principalPowerTorsionTower f M ⟶ principalPowerTorsionTower f N :=
    NatTrans.ofOpSequence stageHom hstageHom_naturality
  let β : principalPowerTorsionTower f N ⟶ principalPowerTorsionTower f M :=
    NatTrans.ofOpSequence stageInv hstageInv_naturality
  exact ⟨α, β, by
    ext n x
    simp [α, β, stageHom, stageInv], by
    ext n x
    simp [α, β, stageHom, stageInv]⟩

/-- Helper for Example 15.94.5: a natural isomorphism of sequential inverse systems induces the
corresponding isomorphism on inverse limits. -/
theorem sequentialModule_limit_iso_of_natIso
    {Msys Nsys : SequentialInverseSystem ModA} (e : Msys ≅ Nsys) :
    limit Msys ≅ limit Nsys := by
  -- Proof comment: this is the canonical limit comparison attached to a natural isomorphism of
  -- diagrams.
  exact HasLimit.isoOfNatIso e

/-- Helper for Example 15.94.5: a natural isomorphism of sequential inverse systems induces the
corresponding isomorphism on the degree-one Milnor term `R^1 \!\varprojlim`. -/
theorem sequentialModule_firstDerivedLimit_iso_of_natIso
    {Msys Nsys : SequentialInverseSystem ModA} (e : Msys ≅ Nsys) :
    firstDerivedLimit Msys ≅ firstDerivedLimit Nsys := by
  -- Proof comment: `R^1 lim` is the Milnor cokernel, so the inverse natural transformation gives
  -- the inverse map on cokernels; both triangle identities reduce to `simp` after canceling the
  -- cokernel projections.
  refine ⟨SequentialInverseSystem.firstDerivedLimitMap e.hom,
    SequentialInverseSystem.firstDerivedLimitMap e.inv, ?_, ?_⟩
  · apply (cancel_epi (cokernel.π (derivedLimitDifferenceMap Msys))).1
    simp [SequentialInverseSystem.firstDerivedLimitMap, Category.assoc]
  · apply (cancel_epi (cokernel.π (derivedLimitDifferenceMap Nsys))).1
    simp [SequentialInverseSystem.firstDerivedLimitMap, Category.assoc]

/-- Helper for Example 15.94.5: an isomorphism of modules induces an isomorphism of the
corresponding principal Tate modules. -/
theorem principalTateModule_iso_of_iso
    {M N : ModA} (e : M ≅ N) :
    Nonempty (T[f] M ≅ T[f] N) := by
  -- Proof comment: limits preserve isomorphic inverse systems, so it is enough to compare the
  -- torsion towers stagewise.
  exact ⟨sequentialModule_limit_iso_of_natIso
    (Classical.choice (principalPowerTorsionTower_iso_of_iso (f := f) e))⟩

/-- Helper for Example 15.94.5: in an exact short complex of modules, vanishing of the outer
terms forces vanishing of the middle term. -/
theorem isZero_middle_of_exact_of_isZero_ends
    {X₁ X₂ X₃ : ModA}
    {α : X₁ ⟶ X₂} {β : X₂ ⟶ X₃} {hαβ : α ≫ β = 0}
    (hexact : (ShortComplex.mk α β hαβ).Exact)
    (h₁ : IsZero X₁) (h₃ : IsZero X₃) :
    IsZero X₂ := by
  -- Proof comment: exactness and a zero source make the right map mono, and a mono into a zero
  -- object forces the middle object to vanish.
  have hmono : Mono β := by
    exact ((ShortComplex.mk α β hαβ).exact_iff_mono (h₁.eq_of_src _ _)).1 hexact
  exact IsZero.of_mono β h₃

/-- Helper for Example 15.94.5: extract the middle row of the comparison diagram from
Lemma `15.94.6`. -/
theorem principalDerivedCompletion_middle_row_shortExact
    (K : DMod) (p : ℤ) :
    ∃ (ι :
        (H 0).obj (((single0).obj ((H p).obj K))^∧[I, hI]) ⟶
          (H p).obj (K^∧[I, hI]))
      (π :
        (H p).obj (K^∧[I, hI]) ⟶
          T[f] ((H (p + 1)).obj K))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  -- Proof comment: the public theorem only needs the middle row, so unpack the comparison
  -- diagram once and discard the extra rows and columns.
  rcases principalDerivedCompletion_cohomology_has_comparison_diagram (f := f) K p with
    ⟨_, _, middleRowLeft, middleRowRight, _, _, _, _, _, middleRowZero, _, _, _, _, _,
      middleRowShortExact, _, _, _, _, _, _⟩
  exact ⟨middleRowLeft, middleRowRight, middleRowZero, middleRowShortExact⟩

/-- Helper for Example 15.94.5: extract the left column of the comparison diagram from
Lemma `15.94.6`. This is the exact sequence available from the comparison-diagram route before
any source-facing tower rewrites. -/
theorem principalDerivedCompletion_left_column_shortExact
    (K : DMod) (p : ℤ) :
    ∃ (ι :
        limit (principalPowerQuotientTower f ((H p).obj K)) ⟶
          (H 0).obj (((single0).obj ((H p).obj K))^∧[I, hI]))
      (π :
        (H 0).obj (((single0).obj ((H p).obj K))^∧[I, hI]) ⟶
          firstDerivedLimit (principalPowerTorsionTower f ((H p).obj K)))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  -- Proof comment: the public theorem only needs the left column as a short exact sequence, so
  -- unpack the comparison diagram once and discard the remaining rows, columns, and comparison map.
  rcases principalDerivedCompletion_cohomology_has_comparison_diagram (f := f) K p with
    ⟨_, _, _, _, leftColumnTop, leftColumnBottom, _, _, _, _, leftColumnZero, _, _, _, _, _,
      leftColumnShortExact, _, _, _, _, _⟩
  exact ⟨leftColumnTop, leftColumnBottom, leftColumnZero, leftColumnShortExact⟩

/-- Helper for Example 15.94.5: extract the middle column of the comparison diagram from
Lemma `15.94.6`. This is the exact sequence available from the comparison-diagram route before
rewriting the Koszul-tensor homology towers to the source-facing quotient and torsion towers. -/
theorem principalDerivedCompletion_middle_column_shortExact
    (K : DMod) (p : ℤ) :
    ∃ (ι :
        limit
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem
              K (fun _ : Fin 1 ↦ f) ⋙ H p) ⟶
          (H p).obj (K^∧[I, hI]))
      (π :
        (H p).obj (K^∧[I, hI]) ⟶
          firstDerivedLimit
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem
              K (fun _ : Fin 1 ↦ f) ⋙ H (p - 1)))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  -- Proof comment: this is the middle column packaged in `Lemma 15.94.6`; extracting it here
  -- keeps the remaining blocker focused on identifying the canonical Milnor comparison.
  rcases principalDerivedCompletion_cohomology_has_comparison_diagram (f := f) K p with
    ⟨_, _, _, _, _, _, middleColumnTop, middleColumnBottom, _, _, _, middleColumnZero, _, _, _,
      _, middleColumnShortExact, _, _, _, _, _⟩
  exact ⟨middleColumnTop, middleColumnBottom, middleColumnZero, middleColumnShortExact⟩

/-
Example 15.94.5: the degree-zero cohomology of principal derived completion of a module fits
into the short exact sequence
`0 → R^1 lim_n M[f^(n + 1)] → H^0(M^∧) → lim_n M / f^(n + 1) M → 0`.
-/
/-- Helper for Example 15.94.5: once `toDerivedCompletion` is packaged as the canonical
principal Koszul comparison on `M[0]`, the degree-zero Milnor short exact sequence follows
immediately from the owner theorem `derivedLimit_cohomology_shortExact`. -/
theorem principal_single0_milnor_shortExact_zero
    (M : ModA)
    (hc :
      CategoryTheory.IsDerivedCompletionKoszulPowerTensorComparison
        (fun _ : Fin 1 ↦ f)
        ((single0).obj M)
        (((single0).obj M)^∧[I, hI])
        (DerivedCategory.toDerivedCompletion I hI ((single0).obj M))) :
    ∃ (ι :
        firstDerivedLimit
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem
              ((single0).obj M) (fun _ : Fin 1 ↦ f) ⋙ H (-1)) ⟶
          (H 0).obj (((single0).obj M)^∧[I, hI]))
      (π :
        (H 0).obj (((single0).obj M)^∧[I, hI]) ⟶
          limit
            (derivedCompletionKoszulPowerTensorDerivedInverseSystem
              ((single0).obj M) (fun _ : Fin 1 ↦ f) ⋙ H 0))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  -- Proof comment: this is exactly the Milnor short exact sequence for the principal Koszul
  -- tensor tower on `M[0]`, specialized to degree `0`.
  simpa using
    CategoryTheory.derivedLimit_cohomology_shortExact
      (derivedCompletionKoszulPowerTensorDerivedInverseSystem
        ((single0).obj M) (fun _ : Fin 1 ↦ f))
      (((single0).obj M)^∧[I, hI])
      hc.isDerivedLimit
      0

theorem principalDerivedCompletionModule_hzero_shortExact
    (M : ModA) :
    ∃ (ι :
        firstDerivedLimit (principalPowerTorsionTower f M) ⟶
          (H 0).obj (((single0).obj M)^∧[I, hI]))
      (π :
        (H 0).obj (((single0).obj M)^∧[I, hI]) ⟶
          limit (principalPowerQuotientTower f M))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  -- Route correction: the comparison-diagram rows in `Lemma_15.94.6` do not expose the module
  -- Milnor sequence in the source-facing orientation `R^1 lim -> H^0 -> lim`. The extracted
  -- helpers `principalDerivedCompletion_left_column_shortExact` and
  -- `principalDerivedCompletion_middle_column_shortExact` only yield the reverse-direction exact
  -- sequences `0 → lim -> H^0 -> R^1 lim → 0`, so the proof must instead specialize
  -- `CategoryTheory.derivedLimit_cohomology_shortExact` directly to the principal Koszul tensor
  -- tower on `M[0]`.
  -- TODO: first prove that `toDerivedCompletion I hI ((single0).obj M)` is the canonical
  -- principal Koszul comparison; the proved helper `principal_single0_milnor_shortExact_zero`
  -- will then supply the raw Milnor exact sequence in the correct orientation. The remaining
  -- source-faithful step is to rewrite the stagewise `H^0` and `H^-1` towers as
  -- `principalPowerQuotientTower f M` and `principalPowerTorsionTower f M`.
  sorry

/-- Example 15.94.5: the degree-`-1` cohomology of principal derived completion of a module is
canonically isomorphic to the principal Tate module `T[f] M`. -/
theorem principalDerivedCompletionModule_hnegOne_isomorphic_tateModule
    (M : ModA) :
    IsIsomorphic ((H (-1)).obj (((single0).obj M)^∧[I, hI])) (T[f] M) := by
  -- Proof comment: apply the already-extracted middle row at `K = M[0]` and `p = -1`; the left
  -- term vanishes because `H^-1(M[0]) = 0`, so the right map is an isomorphism.
  rcases principalDerivedCompletion_middle_row_shortExact (f := f) ((single0).obj M) (-1) with
    ⟨ι, π, hπ, hshort⟩
  have hleftModule :
      IsZero ((H (-1)).obj ((single0).obj M)) := by
    exact single_zero_complex_homology_isZero_of_ne (p := -1) M (by norm_num)
  have hleftCompletion :
      IsZero (((single0).obj ((H (-1)).obj ((single0).obj M)))^∧[I, hI]) :=
    principalDerivedCompletion_single0_isZero_of_isZero (f := f)
      ((H (-1)).obj ((single0).obj M)) hleftModule
  have hleft :
      IsZero
        ((H 0).obj (((single0).obj ((H (-1)).obj ((single0).obj M)))^∧[I, hI])) := by
    exact Functor.map_isZero (H 0) hleftCompletion
  haveI : IsIso π := (ShortComplex.ShortExact.isIso_g_iff hshort).2 hleft
  let hnegOneIso :
      ((H (-1)).obj (((single0).obj M)^∧[I, hI])) ≅
        T[f] ((H 0).obj ((single0).obj M)) :=
    asIso π
  let singleHomologyIso :
      ((H 0).obj ((single0).obj M)) ≅ M :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat A) (0 : ℤ)).app M
  -- Proof comment: transport the Tate-module target along the canonical identification
  -- `H^0(M[0]) ≅ M`.
  exact ⟨hnegOneIso ≪≫ Classical.choice
    (principalTateModule_iso_of_iso (f := f) singleHomologyIso)⟩

/-- Example 15.94.5: for every `K ∈ D(A)` and `p : ℤ`, the cohomology of principal derived
completion fits into the short exact sequence
`0 → H^0(H^p(K)^∧) → H^p(K^∧) → T_f(H^{p+1}(K)) → 0`. -/
theorem principalDerivedCompletion_cohomology_shortExact
    (K : DMod) (p : ℤ) :
    ∃ (ι :
        (H 0).obj (((single0).obj ((H p).obj K))^∧[I, hI]) ⟶
          (H p).obj (K^∧[I, hI]))
      (π :
        (H p).obj (K^∧[I, hI]) ⟶
          T[f] ((H (p + 1)).obj K))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  -- Proof comment: this is exactly the middle row of the comparison diagram from
  -- Lemma `15.94.6`.
  simpa using principalDerivedCompletion_middle_row_shortExact (f := f) K p

-- Proof sketch: the derived inverse limit of a tower of modules has no cohomology above degree
-- `1`, and for the principal completion tower all degrees below `-1` are trivially zero because
-- each stage is a two-term complex.
/-- The derived `(f)`-adic completion of a module has cohomology only in degrees `-1` and `0`. -/
theorem principalDerivedCompletionModule_homology_isZero_of_ne_zero_or_negOne
    (M : ModA) (p : ℤ)
    (hp0 : p ≠ 0) (hpneg1 : p ≠ -1) :
    IsZero ((H p).obj (((single0).obj M)^∧[I, hI])) := by
  -- Proof comment: specialize the general short exact sequence to `K = M[0]`; both outer terms
  -- vanish because the cohomology of `M[0]` is zero away from degree `0`.
  rcases principalDerivedCompletion_cohomology_shortExact (f := f) ((single0).obj M) p with
    ⟨ι, π, hπ, hshort⟩
  have hleftModule :
      IsZero ((H p).obj ((single0).obj M)) :=
    single_zero_complex_homology_isZero_of_ne (p := p) M hp0
  have hleftCompletion :
      IsZero (((single0).obj ((H p).obj ((single0).obj M)))^∧[I, hI]) :=
    principalDerivedCompletion_single0_isZero_of_isZero (f := f)
      ((H p).obj ((single0).obj M)) hleftModule
  have hleft :
      IsZero
        ((H 0).obj (((single0).obj ((H p).obj ((single0).obj M)))^∧[I, hI])) := by
    exact Functor.map_isZero (H 0) hleftCompletion
  have hrightModule :
      IsZero ((H (p + 1)).obj ((single0).obj M)) := by
    apply single_zero_complex_homology_isZero_of_ne (p := p + 1) M
    omega
  have hright :
      IsZero (T[f] ((H (p + 1)).obj ((single0).obj M))) :=
    principalTateModule_isZero_of_isZero (f := f)
      ((H (p + 1)).obj ((single0).obj M)) hrightModule
  exact isZero_middle_of_exact_of_isZero_ends hshort.exact hleft hright

end

end
