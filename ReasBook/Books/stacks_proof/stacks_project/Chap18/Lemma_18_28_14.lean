import Mathlib
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap18.Definition_18_28_1
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

private abbrev finiteIndex (n : ℕ) : Type u :=
  ULift.{u} (Fin n)

private abbrev localizedModuleCategory
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) (U : C) :=
  ringedSiteModuleCategory (J.over U) (𝒪.over U)

private abbrev iteratedLocalizedModuleCategory
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) {U : C} (V : Over U) :=
  ringedSiteModuleCategory ((J.over U).over V) ((𝒪.over U).over V)

private abbrev localizedFiniteFreeModule
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) (U : C) (n : ℕ) :
    localizedModuleCategory J 𝒪 U :=
  SheafOfModules.free (finiteIndex n)

private abbrev iteratedLocalizedFiniteFreeModule
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) {U : C} (V : Over U) (n : ℕ) :
    iteratedLocalizedModuleCategory J 𝒪 V :=
  SheafOfModules.free (finiteIndex n)

private abbrev iteratedRestriction
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (𝒪 : Sheaf J CommRingCat) {U : C} (V : Over U) :
    localizedModuleCategory J 𝒪 U ⥤ iteratedLocalizedModuleCategory J 𝒪 V :=
  SheafOfModules.pushforward (𝟙 (((ringSheaf J 𝒪).over U).over V))

/-- Helper for Chap18 Lemma 18 28 14: restricting from `(C/U, 𝒪_U)` to a further slice
`((C/U)/V, 𝒪_V)` is canonically the pullback along the slice inclusion. -/
private noncomputable def iteratedRestrictionPullbackIso
    {U : C} (V : Over U) :
    SheafOfModules.pullback
        (SheafOfModules.pushforwardOver (R := ringSheaf (J.over U) (𝒪.over U)) V) ≅
      iteratedRestriction J 𝒪 V := by
  -- Proof comment: both functors are the left adjoint to extension by zero along the same slice
  -- inclusion, so the canonical uniqueness isomorphism identifies them.
  simpa [iteratedRestriction, ringedSiteLocalizedRestriction] using
    (Adjunction.leftAdjointUniq
      (SheafOfModules.pullbackPushforwardAdjunction
        (SheafOfModules.pushforwardOver (R := ringSheaf (J.over U) (𝒪.over U)) V))
      (SheafOfModules.overPushforwardOverAdj
        (R := ringSheaf (J.over U) (𝒪.over U)) V))

/-- Helper for Chap18 Lemma 18 28 14: restricting a localized finite free module to a further
slice keeps it finite free, via the canonical pullback/free comparison isomorphism. -/
private noncomputable def iteratedRestrictionFreeIso
    {U : C} (V : Over U) (n : ℕ) :
    (iteratedRestriction J 𝒪 V).obj (localizedFiniteFreeModule J 𝒪 U n) ≅
      iteratedLocalizedFiniteFreeModule J 𝒪 V n := by
  let restrictionApp :
      (iteratedRestriction J 𝒪 V).obj (localizedFiniteFreeModule J 𝒪 U n) ≅
        (SheafOfModules.pullback
            (SheafOfModules.pushforwardOver
              (R := ringSheaf (J.over U) (𝒪.over U)) V)).obj
          (localizedFiniteFreeModule J 𝒪 U n) :=
    ((iteratedRestrictionPullbackIso (J := J) (𝒪 := 𝒪) V).app
      (localizedFiniteFreeModule J 𝒪 U n)).symm
  -- Proof comment: after identifying restriction with pullback, `pullbackObjFreeIso` gives the
  -- canonical free-module comparison on the iterated slice.
  exact restrictionApp ≪≫
    (by
      simpa [localizedFiniteFreeModule, iteratedLocalizedFiniteFreeModule] using
        (SheafOfModules.pullbackObjFreeIso
          (SheafOfModules.pushforwardOver
            (R := ringSheaf (J.over U) (𝒪.over U)) V)
          (finiteIndex n)))

private def localFiniteFreeFactorization
    (ℱ : ringedSiteModuleCategory J 𝒪) {U : C} {m n : ℕ}
    (relation : localizedFiniteFreeModule J 𝒪 U m ⟶ localizedFiniteFreeModule J 𝒪 U n)
    (s : localizedFiniteFreeModule J 𝒪 U n ⟶ ℱ.over U) : Prop :=
  let Free := localizedFiniteFreeModule J 𝒪 U
  ∃ (I : Type u) (Ui : I → Over U), (J.over U).CoversTop Ui ∧
    ∀ i : I,
      let restriction := iteratedRestriction J 𝒪 (Ui i)
      let Free' := iteratedLocalizedFiniteFreeModule J 𝒪 (Ui i)
      ∃ (l : ℕ)
        (B : restriction.obj (Free n) ⟶ Free' l)
        (t : Free' l ⟶ (ℱ.over U).over (Ui i)),
        restriction.map s = B ≫ t ∧
          restriction.map relation ≫ B = 0

/-- Helper for Lemma 18.28.14: the sieve generated by a family of objects in the slice site
agrees with the sieve generated by their underlying arrows in the ambient site. -/
private theorem overSieveOfObjectsEqOfArrows
    {U : C} {ι : Type*} (X : ι → Over U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects X (Over.mk (𝟙 U))) =
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) := by
  -- Proof comment: a factorization in the slice category forgets to the same factorization in the
  -- ambient site, and every ambient factorization lifts back to the slice.
  ext W g
  constructor
  · intro hg
    rw [Sieve.overEquiv_iff] at hg
    rw [Sieve.mem_ofObjects_iff] at hg
    rcases hg with ⟨i, ⟨a⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, a.left, by simpa using a.w.symm⟩
  · intro hg
    rw [Sieve.overEquiv_iff]
    rw [Sieve.mem_ofArrows_iff] at hg
    rcases hg with ⟨i, a, ha⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk a (by simpa using ha.symm)⟩⟩

/-- Helper for Lemma 18.28.14: the identity arrow of `U` gives a singleton covering family in the
slice site `(C/U, J.over U)`. -/
private theorem identitySingletonCoversTopOver (U : C) :
    (J.over U).CoversTop (fun _ : PUnit ↦ Over.mk (𝟙 U)) := by
  -- Proof comment: the unique member of the family is already the terminal object of `C/U`.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal (J := J.over U) (X := Over.mk (𝟙 U))
    (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff]
  have htop :
      (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects (fun _ : PUnit ↦ Over.mk (𝟙 U)) (Over.mk (𝟙 U))) = ⊤ := by
    ext Z g
    constructor
    · intro _
      trivial
    · intro _
      rw [Sieve.overEquiv_iff]
      exact ⟨PUnit.unit, ⟨Over.homMk g⟩⟩
  rw [htop]
  exact J.top_mem U

/-- Helper for Lemma 18.28.14: composing a slice-site cover with covers of each member gives a
sigma-indexed refinement cover. -/
private theorem coversTopSigmaComp
    {U : C} {I : Type u} {X : I → Over U}
    (hX : (J.over U).CoversTop X)
    {K : I → Type u} {Y : ∀ i : I, K i → Over (X i).left}
    (hY : ∀ i : I, (J.over (X i).left).CoversTop (Y i)) :
    (J.over U).CoversTop
      (fun a : Sigma K ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom)) := by
  -- Proof comment: convert both slice covers to ambient covering sieves and compose them with
  -- the transitivity axiom `bindOfArrows`.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows]
  have hX' :
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈ J U := by
    have hXTerminal :
        Sieve.ofObjects X (Over.mk (𝟙 U)) ∈ (J.over U) (Over.mk (𝟙 U)) :=
      (GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal) X).1 hX
    rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows] at hXTerminal
    exact hXTerminal
  have hY' :
      ∀ i : I,
        Sieve.ofArrows (fun k ↦ (Y i k).left) (fun k ↦ (Y i k).hom) ∈ J (X i).left := by
    intro i
    have hYTerminal :
        Sieve.ofObjects (Y i) (Over.mk (𝟙 (X i).left)) ∈
          (J.over (X i).left) (Over.mk (𝟙 (X i).left)) :=
      (GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := J.over (X i).left) (X := Over.mk (𝟙 (X i).left))
        (hX := Over.mkIdTerminal) (Y i)).1 (hY i)
    rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows] at hYTerminal
    exact hYTerminal
  simpa [Presieve.bindOfArrows_ofArrows] using
    J.bindOfArrows
      (h := hX')
      (R := fun i ↦ Presieve.ofArrows (fun k ↦ (Y i k).left) (fun k ↦ (Y i k).hom))
      (fun i ↦ by simpa using hY' i)

/-- Helper for Lemma 18.28.14: a relation with zero source rank already has the trivial local
factorization on the identity cover. -/
private theorem localFiniteFreeFactorization_zeroSource
    (ℱ : ringedSiteModuleCategory J 𝒪) {U : C} {n : ℕ}
    (s : localizedFiniteFreeModule J 𝒪 U n ⟶ ℱ.over U) :
    localFiniteFreeFactorization ℱ
      (0 : localizedFiniteFreeModule J 𝒪 U 0 ⟶ localizedFiniteFreeModule J 𝒪 U n) s := by
  -- Proof comment: on the identity cover of `U`, the given map already factors through itself via
  -- the identity of the restricted rank-`n` free module, and the zero relation stays zero after
  -- restriction.
  dsimp [localFiniteFreeFactorization]
  refine ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), identitySingletonCoversTopOver (J := J) U, ?_⟩
  intro i
  let restriction := iteratedRestriction J 𝒪 (Over.mk (𝟙 U))
  let e := iteratedRestrictionFreeIso (J := J) (𝒪 := 𝒪) (Over.mk (𝟙 U)) n
  refine ⟨n, e.hom, e.inv ≫ restriction.map s, ?_, ?_⟩
  · -- Proof comment: insert the comparison isomorphism between the restricted free module and the
    -- canonical free module on the identity slice.
    simpa [restriction, Category.assoc] using (e.hom_inv_id_assoc (restriction.map s)).symm
  · simp
  · simp [restriction]

/-- Helper for Lemma 18.28.14: a morphism out of the rank-zero finite free module is zero. -/
private theorem localizedFiniteFree_zero_hom_eq_zero
    {U : C} {n : ℕ}
    (A : localizedFiniteFreeModule J 𝒪 U 0 ⟶ localizedFiniteFreeModule J 𝒪 U n) :
    A = 0 := by
  -- Proof comment: `freeHomEquiv` reduces a map out of the rank-zero free module to a family
  -- indexed by `Fin 0`, which is necessarily empty.
  apply (localizedFiniteFreeModule J 𝒪 U n).freeHomEquiv.injective
  funext i
  exact Fin.elim0 i.down

/-- Helper for Lemma 18.28.14: restricting a terminal value along the unique maps from the slice
terminal object is compatible with all restriction maps. -/
private theorem over_sections_from_terminal_naturality
    {U : C} {M : localizedModuleCategory J 𝒪 U}
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    ∀ V Y : (Over U)ᵒᵖ, ∀ f : V ⟶ Y,
      M.val.map f (M.val.map ((Over.mkIdTerminal.from V.unop).op) m) =
        M.val.map ((Over.mkIdTerminal.from Y.unop).op) m := by
  intro V Y f
  -- Proof comment: every object of the slice admits a unique morphism to the terminal object.
  have h :
      (Over.mkIdTerminal.from V.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
    apply Quiver.Hom.unop_inj
    simp only [Quiver.Hom.unop_op]
    exact Over.mkIdTerminal.hom_ext
      (f.unop ≫ Over.mkIdTerminal.from V.unop)
      (Over.mkIdTerminal.from Y.unop)
  rw [← PresheafOfModules.map_comp_apply, h]

/-- Helper for Lemma 18.28.14: a terminal value determines a section on the slice site by
restriction from the terminal object. -/
private noncomputable def over_sections_from_terminal
    {U : C} (M : localizedModuleCategory J 𝒪 U)
    (m : M.val.obj (op (Over.mk (𝟙 U)))) : M.sections :=
  M.val.sectionsMk
    (fun V ↦ M.val.map ((Over.mkIdTerminal.from V.unop).op) m)
    (over_sections_from_terminal_naturality (M := M) m)

/-- Helper for Lemma 18.28.14: a slice section is determined by its value at the terminal object. -/
private theorem over_sections_equiv_terminal_left_inv
    {U : C} {M : localizedModuleCategory J 𝒪 U}
    (s : M.sections) :
    over_sections_from_terminal (J := J) (𝒪 := 𝒪) M
        (s.1 (op (Over.mk (𝟙 U)))) = s := by
  -- Proof comment: every component is obtained by restricting the terminal component.
  ext V
  simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)

/-- Helper for Lemma 18.28.14: evaluating the reconstructed section at the terminal object recovers
the original terminal value. -/
private theorem over_sections_equiv_terminal_right_inv
    {U : C} {M : localizedModuleCategory J 𝒪 U}
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    (over_sections_from_terminal (J := J) (𝒪 := 𝒪) M m).1
        (op (Over.mk (𝟙 U))) = m := by
  -- Proof comment: the terminal object only maps to itself by the identity.
  change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
  have h :
      Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
    Over.mkIdTerminal.hom_ext _ _
  simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 18.28.14: evaluating at the terminal object gives an equivalence between
slice sections and terminal values. -/
private noncomputable def over_sections_equiv_terminal
    {U : C} (M : localizedModuleCategory J 𝒪 U) :
    M.sections ≃ M.val.obj (op (Over.mk (𝟙 U))) :=
  { toFun := fun s ↦ s.1 (op (Over.mk (𝟙 U)))
    invFun := over_sections_from_terminal (J := J) (𝒪 := 𝒪) M
    left_inv := over_sections_equiv_terminal_left_inv (J := J) (𝒪 := 𝒪) (M := M)
    right_inv := over_sections_equiv_terminal_right_inv (J := J) (𝒪 := 𝒪) (M := M) }

/-- Helper for Lemma 18.28.14: under terminal evaluation, a section map is exactly the terminal
component of the underlying sheaf morphism. -/
private theorem over_sections_equiv_terminal_sectionsMap
    {U : C} {M N : localizedModuleCategory J 𝒪 U}
    (ψ : M ⟶ N) (s : M.sections) :
    over_sections_equiv_terminal (J := J) (𝒪 := 𝒪) N
        (SheafOfModules.sectionsMap ψ s) =
      (ψ.val.app (op (Over.mk (𝟙 U))))
        (over_sections_equiv_terminal (J := J) (𝒪 := 𝒪) M s) := by
  -- Proof comment: both sides are definitionally the terminal evaluation of the mapped section.
  rfl

/-- Helper for Lemma 18.28.14: the inverse terminal-evaluation equivalence is natural in a module
sheaf morphism. -/
private theorem sectionsMap_over_sections_equiv_terminal_symm
    {U : C} {M N : localizedModuleCategory J 𝒪 U}
    (ψ : M ⟶ N) (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    SheafOfModules.sectionsMap ψ
        ((over_sections_equiv_terminal (J := J) (𝒪 := 𝒪) M).symm m) =
      (over_sections_equiv_terminal (J := J) (𝒪 := 𝒪) N).symm
        ((ψ.val.app (op (Over.mk (𝟙 U)))) m) := by
  -- Proof comment: compare both sections after applying terminal evaluation.
  apply (over_sections_equiv_terminal (J := J) (𝒪 := 𝒪) N).injective
  rw [over_sections_equiv_terminal_sectionsMap]
  simp

/-- Helper for Lemma 18.28.14: a family of terminal sections of a slice module sheaf packages into
the canonical morphism from a finite free sheaf. -/
private noncomputable def free_morphism_of_section_family
    {U : C} {n : ℕ} (M : localizedModuleCategory J 𝒪 U)
    (s : Fin n → M.val.obj (op (Over.mk (𝟙 U)))) :
    (localizedFiniteFreeModule J 𝒪 U n) ⟶ M :=
  (localizedFiniteFreeModule J 𝒪 U n).freeHomEquiv.symm
    (fun i : ULift (Fin n) ↦
      (over_sections_equiv_terminal (J := J) (𝒪 := 𝒪) M).symm (s i.down))

/-- Helper for Lemma 18.28.14: evaluating the morphism built from a family of terminal sections on
the terminal free basis section recovers the chosen terminal coefficient. -/
private theorem free_morphism_of_section_family_app_terminal_freeSection
    {U : C} {n : ℕ} (M : localizedModuleCategory J 𝒪 U)
    (s : Fin n → M.val.obj (op (Over.mk (𝟙 U)))) (i : ULift (Fin n)) :
    ((free_morphism_of_section_family (J := J) (𝒪 := 𝒪) M s).val.app
        (op (Over.mk (𝟙 U))))
      ((show (localizedFiniteFreeModule J 𝒪 U n).sections from
          SheafOfModules.freeSection (R := ringSheaf (J.over U) (𝒪.over U)) i).1
        (op (Over.mk (𝟙 U)))) = s i.down := by
  -- Proof comment: first use the defining basis formula for `freeHomEquiv.symm`, then evaluate the
  -- resulting section at the terminal object.
  have h :=
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (f := fun j : ULift (Fin n) ↦
        (over_sections_equiv_terminal (J := J) (𝒪 := 𝒪) M).symm (s j.down))
      (R := ringSheaf (J.over U) (𝒪.over U)) (i := i))
  have hterminal :=
    congrArg
      (fun t : M.sections ↦ over_sections_equiv_terminal (J := J) (𝒪 := 𝒪) M t)
      h
  simpa [free_morphism_of_section_family] using hterminal

/-- Helper for Chap18 Lemma 18 28 14: evaluating a sheaf module at `U` agrees definitionally with
evaluating its restriction to the slice site at the slice terminal object. -/
private theorem evaluation_over_terminal_obj_eq
    {U : C} (M : ringedSiteModuleCategory J 𝒪) :
    (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).obj M =
      (SheafOfModules.evaluation ((ringSheaf J 𝒪).over U)
          (op (Over.mk (𝟙 U)))).obj
        (M.over U) := by
  -- Proof comment: both sides are the same underlying module obtained by restricting `M` to the
  -- slice site over `U` and then reading off its value at the terminal object `U ⟶ U`.
  rfl

/-- Helper for Chap18 Lemma 18 28 14: objectwise evaluation of a sheaf morphism agrees
definitionally with terminal evaluation after restricting to the slice site. -/
private theorem evaluation_over_terminal_map_eq
    {U : C} {M N : ringedSiteModuleCategory J 𝒪} (f : M ⟶ N) :
    (SheafOfModules.evaluation (ringSheaf J 𝒪) (op U)).map f =
      (SheafOfModules.evaluation ((ringSheaf J 𝒪).over U)
          (op (Over.mk (𝟙 U)))).map
        ((SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))).map f) := by
  -- Proof comment: after the preceding definitional identification of objects, both maps are the
  -- same terminal component of the restricted sheaf morphism.
  rfl

/-- Helper for Chap18 Lemma 18 28 14: evaluation at the terminal object of a slice site is exact
on sheaves of modules. -/
private theorem slice_terminal_evaluation_exact
    {U : C} :
    exactFunctor _ _
      (SheafOfModules.evaluation ((ringSheaf J 𝒪).over U)
        (op (Over.mk (𝟙 U)))) := by
  -- Proof comment: evaluation at a fixed object preserves finite limits and finite colimits
  -- objectwise, so the terminal slice evaluation is exact just like any other module evaluation.
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

/- Domain-style sampling for Lemma 18.28.14:
- primary domain: flat sheaves of modules on a ringed site, tested by localized finite-free
  factorization criteria;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFlat`,
  `SheafOfModules.free`,
  `SheafOfModules.over`,
  `SheafOfModules.pushforward`,
  `SheafOfModules.pushforwardOver`;
- best owner abstraction: the ambient module object should live in the chapter-level owner
  `ringedSiteModuleCategory J 𝒪`, while localization is expressed through the canonical
  restriction objects `ℱ ↦ ℱ.over U`, `((ℱ.over U).over V)`, and the canonical localization
  functor to iterated slice sites;
- primitive data: a module `ℱ : ringedSiteModuleCategory J 𝒪`, finite free modules on localized
  sites, and the further-localization functor from `(C/U, \mathcal O_U)` to
  `((C/U)/V, \mathcal O_V)`;
- derived API: the uniform local finite-free factorization predicate and its source-facing
  one-relation / finite-presentation specializations.

Source/core/bridge triage:
- `source-facing`: the two local factorization predicates and their equivalence with flatness;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪`,
  `SheafOfModules.RingedSite.IsFlat`, `SheafOfModules.free`,
  `SheafOfModules.over`, `SheafOfModules.pushforward`, and
  `SheafOfModules.pushforwardOver`;
- `bridge/view`: the further-localization functor from `ℱ.over U` to `((ℱ.over U).over V)` and
  the uniform factorization predicate `localFiniteFreeFactorization`.

This file should therefore reuse the upstream owner `ringedSiteModuleCategory` from
`Lemma_18_19_2`, with localized finite free modules and iterated restrictions expressed through a
thin internal layer over the chapter's canonical `over` / `pushforward` surface rather than
repeating the raw sheaf expressions in every public statement.
-/

/-- The single-relation local factorization criterion for flatness on a ringed site. -/
def flatSingleRelationFactorization
    (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  ∀ (U : C) (n : ℕ),
    let Free := localizedFiniteFreeModule J 𝒪 U
    ∀ (f : Free 1 ⟶ Free n) (s : Free n ⟶ ℱ.over U) (_ : f ≫ s = 0),
      localFiniteFreeFactorization ℱ f s

/-- The finite-presentation local factorization criterion for flatness on a ringed site. -/
def flatMatrixFactorization
    (ℱ : ringedSiteModuleCategory J 𝒪) : Prop :=
  ∀ (U : C) (m n : ℕ),
    let Free := localizedFiniteFreeModule J 𝒪 U
    ∀ (A : Free m ⟶ Free n) (s : Free n ⟶ ℱ.over U) (_ : A ≫ s = 0),
      localFiniteFreeFactorization ℱ A s

/-- Helper for Lemma 18.28.14: flatness implies the single-relation local factorization
criterion. -/
private theorem singleRelationFactorization_of_isFlat
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    IsFlat 𝒪 ℱ → flatSingleRelationFactorization ℱ := by
  intro hFlat
  -- TODO: use `isFlat_over` to pass flatness to the slice, convert the relation `f ≫ s = 0` into
  -- a kernel section problem on the rank-one free module, and package the resulting local section
  -- family back into a free-module morphism via `over_sections_equiv_terminal`.
  sorry

/-- Helper for Lemma 18.28.14: the finite-presentation criterion specializes to the
single-relation criterion. -/
private theorem matrixFactorization_implies_singleRelationFactorization
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    flatMatrixFactorization ℱ → flatSingleRelationFactorization ℱ := by
  intro hmatrix
  -- Proof comment: specialize the matrix criterion to source rank `1`.
  intro U n
  simpa [flatMatrixFactorization, flatSingleRelationFactorization] using
    hmatrix U 1 n

/-- Helper for Lemma 18.28.14: the first `m` basis vectors of `Fin (m + 1)` give the canonical
source truncation map between finite free modules. -/
private abbrev finiteIndexCastSucc (m : ℕ) :
    finiteIndex m → finiteIndex (m + 1) :=
  fun i ↦ ULift.up i.down.castSucc

/-- Helper for Lemma 18.28.14: the final basis vector of `Fin (m + 1)` records the last column of
a finite free map. -/
private abbrev finiteIndexLast (m : ℕ) : finiteIndex (m + 1) :=
  ULift.up (Fin.last m)

/-- Helper for Lemma 18.28.14: the canonical inclusion of the first `m` basis vectors into the
rank-`m + 1` finite free module. -/
private noncomputable def localizedFiniteFreeCastSucc
    {U : C} (m : ℕ) :
    localizedFiniteFreeModule J 𝒪 U m ⟶ localizedFiniteFreeModule J 𝒪 U (m + 1) :=
  SheafOfModules.freeMap (finiteIndexCastSucc m)

/-- Helper for Lemma 18.28.14: the last column of a map out of a rank-`m + 1` finite free module,
viewed as a map out of rank `1`. -/
private noncomputable def localizedFiniteFreeLastColumn
    {U : C} {m : ℕ} {M : localizedModuleCategory J 𝒪 U}
    (A : localizedFiniteFreeModule J 𝒪 U (m + 1) ⟶ M) :
    localizedFiniteFreeModule J 𝒪 U 1 ⟶ M :=
  M.freeHomEquiv.symm
    (fun _ ↦
      M.freeHomEquiv A (finiteIndexLast m))

/-- Helper for Lemma 18.28.14: restriction to a further slice commutes with the canonical
truncation map on finite free modules. -/
private theorem iteratedRestriction_map_castSucc
    {U : C} (V : Over U) (m : ℕ) :
    (iteratedRestrictionFreeIso (J := J) (𝒪 := 𝒪) V m).inv ≫
        (iteratedRestriction J 𝒪 V).map
          (localizedFiniteFreeCastSucc (J := J) (𝒪 := 𝒪) (U := U) m) ≫
        (iteratedRestrictionFreeIso (J := J) (𝒪 := 𝒪) V (m + 1)).hom =
      localizedFiniteFreeCastSucc (J := J.over U) (𝒪 := 𝒪.over U) (U := V) m := by
  -- Proof comment: transport the restricted source and target to the canonical free modules on the
  -- iterated slice, then compare basis coordinates using the pullback/free naturality formula.
  apply (iteratedLocalizedFiniteFreeModule (J := J) (𝒪 := 𝒪) V (m + 1)).freeHomEquiv.injective
  funext i
  simp [iteratedRestrictionFreeIso, iteratedRestrictionPullbackIso, localizedFiniteFreeCastSucc,
    finiteIndexCastSucc, Category.assoc, SheafOfModules.freeHomEquiv_comp_apply,
    SheafOfModules.freeHomEquiv_freeMap]

/-- Helper for Lemma 18.28.14: restriction to a further slice commutes with extracting the last
column of a finite free map. -/
private theorem iteratedRestriction_map_lastColumn
    {U : C} {m : ℕ} {M : localizedModuleCategory J 𝒪 U}
    (V : Over U)
    (A : localizedFiniteFreeModule J 𝒪 U (m + 1) ⟶ M) :
    localizedFiniteFreeLastColumn (J := J.over U) (𝒪 := 𝒪.over U)
        ((iteratedRestrictionFreeIso (J := J) (𝒪 := 𝒪) V (m + 1)).inv ≫
          (iteratedRestriction J 𝒪 V).map A) =
      (iteratedRestrictionFreeIso (J := J) (𝒪 := 𝒪) V 1).inv ≫
        (iteratedRestriction J 𝒪 V).map
          (localizedFiniteFreeLastColumn (J := J) (𝒪 := 𝒪) A) := by
  -- Proof comment: after normalizing the restricted source by `iteratedRestrictionFreeIso`, both
  -- morphisms have the same unique basis-coordinate, namely the restricted last-column coordinate.
  apply ((iteratedRestriction J 𝒪 V).obj M).freeHomEquiv.injective
  funext i
  cases i with
  | up i =>
  fin_cases i
  simp [iteratedRestrictionFreeIso, iteratedRestrictionPullbackIso, localizedFiniteFreeLastColumn,
    Category.assoc, SheafOfModules.freeHomEquiv_comp_apply]

/-- Helper for Lemma 18.28.14: extracting the last column commutes with postcomposition. -/
private theorem localizedFiniteFreeLastColumn_comp
    {U : C} {m : ℕ} {M N : localizedModuleCategory J 𝒪 U}
    (A : localizedFiniteFreeModule J 𝒪 U (m + 1) ⟶ M) (g : M ⟶ N) :
    localizedFiniteFreeLastColumn (J := J) (𝒪 := 𝒪) (A ≫ g) =
      localizedFiniteFreeLastColumn (J := J) (𝒪 := 𝒪) A ≫ g := by
  -- Proof comment: both morphisms have the same unique basis-coordinate after applying
  -- `freeHomEquiv`, namely the last-column coordinate of `A` followed by `g`.
  apply N.freeHomEquiv.injective
  funext i
  cases' i with i
  fin_cases i
  simp [localizedFiniteFreeLastColumn, SheafOfModules.freeHomEquiv_comp_apply]

/-- Helper for Lemma 18.28.14: if a relation `A ≫ s = 0` holds, then the last column of `A`
already vanishes after composing with `s`. -/
private theorem localizedFiniteFreeLastColumn_comp_eq_zero_of_comp_eq_zero
    (ℱ : ringedSiteModuleCategory J 𝒪)
    {U : C} {m n : ℕ}
    (A : localizedFiniteFreeModule J 𝒪 U (m + 1) ⟶ localizedFiniteFreeModule J 𝒪 U n)
    (s : localizedFiniteFreeModule J 𝒪 U n ⟶ ℱ.over U)
    (hAs : A ≫ s = 0) :
    localizedFiniteFreeLastColumn (J := J) (𝒪 := 𝒪) A ≫ s = 0 := by
  -- Proof comment: rewrite the composite as the last column of `A ≫ s`, then use `A ≫ s = 0`
  -- and the fact that the last column of the zero map is again zero.
  rw [← localizedFiniteFreeLastColumn_comp (J := J) (𝒪 := 𝒪) A s, hAs]
  apply (ℱ.over U).freeHomEquiv.injective
  funext i
  cases i with
  | up i =>
    fin_cases i
    simp [localizedFiniteFreeLastColumn]

/-- Helper for Lemma 18.28.14: a map out of rank `m + 1` is zero once both its truncation to the
first `m` basis vectors and its last column vanish. -/
private theorem localizedFiniteFree_hom_eq_zero_of_castSucc_and_lastColumn
    {U : C} {m : ℕ} {M : localizedModuleCategory J 𝒪 U}
    (A : localizedFiniteFreeModule J 𝒪 U (m + 1) ⟶ M)
    (htrunc :
      localizedFiniteFreeCastSucc (J := J) (𝒪 := 𝒪) (U := U) m ≫ A = 0)
    (hlast : localizedFiniteFreeLastColumn (J := J) (𝒪 := 𝒪) A = 0) :
    A = 0 := by
  -- Proof comment: every basis vector of `Fin (m + 1)` is either in the first `m` positions or
  -- is the last one, so the corresponding `freeHomEquiv` coordinate is killed by `htrunc` or
  -- `hlast`.
  apply M.freeHomEquiv.injective
  funext i
  cases i with
  | up i =>
  refine Fin.lastCases ?_ ?_ i
  · -- The final basis vector is exactly the last-column coordinate.
    simpa [localizedFiniteFreeLastColumn] using
      congrFun (congrArg (M.freeHomEquiv) hlast) (finiteIndexLast m)
  · intro j
    have htruncj :
        M.freeHomEquiv (localizedFiniteFreeCastSucc (J := J) (𝒪 := 𝒪) (U := U) m ≫ A)
          (ULift.up j) =
        M.freeHomEquiv (0 : localizedFiniteFreeModule J 𝒪 U m ⟶ M) (ULift.up j) := by
      simpa using congrFun (congrArg (M.freeHomEquiv) htrunc) (ULift.up j)
    -- Route correction: compare the truncation basis vector through `freeMap`; this avoids
    -- unfolding the full source morphism `A` and isolates the only needed basis computation.
    simpa [localizedFiniteFreeCastSucc, finiteIndexCastSucc,
      SheafOfModules.freeHomEquiv_comp_apply] using htruncj

/-- Helper for Lemma 18.28.14: the single-relation local factorization criterion implies the
finite-presentation version. -/
private theorem matrixFactorization_of_singleRelation
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    flatSingleRelationFactorization ℱ → flatMatrixFactorization ℱ := by
  -- TODO: induct on the source rank, kill the last column by the single-relation criterion, then
  -- transport the induction hypothesis to the slice site and compose the resulting covers.
  sorry

/-- Helper for Lemma 18.28.14: the finite-presentation local factorization criterion forces
flatness. -/
private theorem isFlat_of_matrixFactorization
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    flatMatrixFactorization ℱ → IsFlat 𝒪 ℱ := sorry

-- Proof sketch: `(1) → (2)` is the standard local syzygy criterion obtained by applying
-- flatness to the ideal generated by one relation. `(2) → (3)` is an induction on the number of
-- columns of the presentation matrix. `(3) → (1)` is the finite-presentation criterion for
-- injectivity after tensoring, using that sections of `ℱ` are filtered colimits of finitely
-- presented modules and then applying the local factorization through finite free modules.
/-- Lemma 18.28.14: for a ringed site `(\mathcal C, \mathcal O)` and an `\mathcal O`-module
`\mathcal F`, flatness of `\mathcal F` is equivalent to the local finite-relation factorization
criterion for one relation and to its finite-presentation version for arbitrary maps
`\mathcal O_U^{\oplus m} \to \mathcal O_U^{\oplus n}`. -/
@[stacks 08FC]
theorem isFlat_tfae_factorizationCriteria
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    List.TFAE [
      IsFlat 𝒪 ℱ,
      flatSingleRelationFactorization ℱ,
      flatMatrixFactorization ℱ
    ] := by
  -- Proof comment: prove the cycle `(1) → (2) → (3) → (1)` and finish via `tfae`.
  tfae_have 1 → 2 := by
    -- TODO: use flatness on the slice site over `U`, kill the tensor relation locally,
    -- and rewrite the resulting trivial relation as the required local finite free factorization.
    exact singleRelationFactorization_of_isFlat (J := J) (𝒪 := 𝒪) ℱ
  tfae_have 2 → 3 := by
    -- TODO: induct on the source rank `m`, first killing the last column via the one-relation
    -- criterion and then composing with the induction hypothesis on the remaining columns.
    exact matrixFactorization_of_singleRelation (J := J) (𝒪 := 𝒪) ℱ
  tfae_have 3 → 1 := by
    -- TODO: use the finite-presentation factorization criterion to show tensoring by `ℱ`
    -- preserves monomorphisms locally on sections, then apply the exact-functor criterion.
    exact isFlat_of_matrixFactorization (J := J) (𝒪 := 𝒪) ℱ
  tfae_finish

end SheafOfModules.RingedSite
