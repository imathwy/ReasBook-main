import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.Chap07.Lemma_7_41_2
import StacksProject_2024.Chap17.Definition_17_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open CategoryTheory.ObjectProperty

noncomputable section

universe u v u'

/- Domain-style sampling for Lemma 17.9.3:
- primary domain: finite-type sheaves of modules over a sheaf of rings on a site;
- inspected owner declarations:
  `SheafOfModules.IsFiniteType`,
  `CategoryTheory.ObjectProperty.IsClosedUnderQuotients`,
  `CategoryTheory.ObjectProperty.IsClosedUnderExtensions`,
  `SheafOfModules.finiteTypeModuleProperty_isClosedUnderIsomorphisms`,
  `Abelian.factorThruImage`;
- owner abstraction: the canonical owner predicate `SheafOfModules.IsFiniteType`, used directly
  through its `ObjectProperty` view;
- primitive data: local finite generating families, as provided by
  `SheafOfModules.IsFiniteType.exists_localGeneratorsData`;
- derived API: closure under quotients, images, and short exact extensions.

Source/core/bridge triage:
- `source-facing`: the Stacks Project claims that finite-type modules are stable under images and
  extensions;
- `core/canonical`: the owner predicate `SheafOfModules.IsFiniteType` and its object-property
  packaging;
- `bridge/view`: the ringed-space specialization obtained by taking `R = (RingedSpace.ringCatSheaf X)`.

The file should therefore state the closure facts at the generic `SheafOfModules` owner layer,
with ringed spaces only as a specialization, rather than as parallel ringed-space-specific global
theorems. -/

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

variable {ℱ 𝒢 : SheafOfModules R}

/-- Helper for Lemma 17.9.3: restricting an `R`-module sheaf to the slice site `J.over X` is the
canonical pushforward functor along the identity comparison morphism of sheaves of rings. -/
abbrev overRestrictionFunctor (X : C) : SheafOfModules R ⥤ SheafOfModules (R.over X) :=
  SheafOfModules.pushforward
    (CategoryTheory.CategoryStruct.id
      (((CategoryTheory.Over.forget X).sheafPushforwardContinuous RingCat (J.over X) J).obj R))

namespace GeneratingSections

omit [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Helper for Lemma 17.9.3: pushing a finite generating family through an epimorphism preserves
finiteness of the indexing type. -/
lemma isFiniteType_ofEpi {M N : SheafOfModules R} (σ : M.GeneratingSections)
    [σ.IsFiniteType] (p : M ⟶ N) [Epi p] :
    (σ.ofEpi p).IsFiniteType := by
  -- `GeneratingSections.ofEpi` keeps the same index type, so only the original finiteness matters.
  refine ⟨?_⟩
  simpa [SheafOfModules.GeneratingSections.ofEpi] using (inferInstance : Finite σ.I)

end GeneratingSections

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Helper for Lemma 17.9.3: if the underlying additive-sheaf map is epi, then the original
module-sheaf map is epi. -/
lemma epi_of_toSheaf_map_epi {M N : SheafOfModules R} (p : M ⟶ N)
    [Epi ((SheafOfModules.toSheaf R).map p)] : Epi p := by
  -- Faithfulness of `toSheaf` reflects the right-cancellation property from additive sheaves.
  refine ⟨?_⟩
  intro Z g h hgh
  apply (SheafOfModules.toSheaf R).map_injective
  apply (cancel_epi ((SheafOfModules.toSheaf R).map p)).1
  simpa using congrArg ((SheafOfModules.toSheaf R).map) hgh

/-- Helper for Lemma 17.9.3: the inverse terminal-evaluation section is compatible with
restriction maps in the slice category. -/
private theorem over_sections_equiv_terminal_inv_naturality
    {U : C} {M : SheafOfModules (R.over U)}
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    ∀ V Y : (Over U)ᵒᵖ, ∀ f : V ⟶ Y,
      M.val.map f (M.val.map ((Over.mkIdTerminal.from V.unop).op) m) =
        M.val.map ((Over.mkIdTerminal.from Y.unop).op) m := by
  intro V Y f
  -- Proof comment: every object of `Over U` has a unique map to the terminal object.
  have h :
      (Over.mkIdTerminal.from V.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
    apply Quiver.Hom.unop_inj
    simp only [Quiver.Hom.unop_op]
    exact Over.mkIdTerminal.hom_ext
      (f.unop ≫ Over.mkIdTerminal.from V.unop)
      (Over.mkIdTerminal.from Y.unop)
  rw [← PresheafOfModules.map_comp_apply, h]

/-- Helper for Lemma 17.9.3: rebuild a section on the slice from its value at the terminal
object. -/
private noncomputable def over_sections_from_terminal
    {U : C} (M : SheafOfModules (R.over U))
    (m : M.val.obj (op (Over.mk (𝟙 U)))) : M.sections :=
  M.val.sectionsMk
    (fun V ↦ M.val.map ((Over.mkIdTerminal.from V.unop).op) m)
    (over_sections_equiv_terminal_inv_naturality (M := M) m)

/-- Helper for Lemma 17.9.3: a slice section is recovered from its value at the terminal object by
restricting along the unique terminal maps. -/
private theorem over_sections_equiv_terminal_left_inv
    {U : C} {M : SheafOfModules (R.over U)} (s : M.sections) :
    over_sections_from_terminal M (s.1 (op (Over.mk (𝟙 U)))) = s := by
  -- Proof comment: a section on the slice is determined by its restrictions from the terminal
  -- object.
  ext V
  simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)

/-- Helper for Lemma 17.9.3: evaluating the reconstructed slice section at the terminal object
returns the original value. -/
private theorem over_sections_equiv_terminal_right_inv
    {U : C} {M : SheafOfModules (R.over U)}
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    (over_sections_from_terminal M m).1 (op (Over.mk (𝟙 U))) = m := by
  -- Proof comment: the unique endomorphism of the terminal object is the identity.
  change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
  have h :
      Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
    Over.mkIdTerminal.hom_ext _ _
  simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 17.9.3: terminal evaluation identifies sections on a slice with the value at
the terminal object. -/
private noncomputable def over_sections_equiv_terminal
    {U : C} (M : SheafOfModules (R.over U)) :
    M.sections ≃ M.val.obj (op (Over.mk (𝟙 U))) :=
  { toFun := fun s ↦ s.1 (op (Over.mk (𝟙 U)))
    invFun := over_sections_from_terminal M
    left_inv := over_sections_equiv_terminal_left_inv (M := M)
    right_inv := over_sections_equiv_terminal_right_inv (M := M) }

/-- Helper for Lemma 17.9.3: under terminal evaluation, `sectionsMap` is exactly the terminal
component of the underlying sheaf morphism on the slice site. -/
private theorem over_sections_equiv_terminal_sectionsMap
    {U : C} {M N : SheafOfModules (R.over U)} (ψ : M ⟶ N) (s : M.sections) :
    over_sections_equiv_terminal N (SheafOfModules.sectionsMap ψ s) =
      (ψ.val.app (op (Over.mk (𝟙 U)))) (over_sections_equiv_terminal M s) := by
  -- Proof comment: both sides are definitionally the terminal evaluation of the mapped section.
  rfl

/-- Helper for Lemma 17.9.3: the inverse terminal-evaluation equivalence is natural in module-sheaf
morphisms on the slice site. -/
private theorem sectionsMap_over_sections_equiv_terminal_symm
    {U : C} {M N : SheafOfModules (R.over U)} (ψ : M ⟶ N)
    (m : M.val.obj (op (Over.mk (𝟙 U)))) :
    SheafOfModules.sectionsMap ψ ((over_sections_equiv_terminal M).symm m) =
      (over_sections_equiv_terminal N).symm ((ψ.val.app (op (Over.mk (𝟙 U)))) m) := by
  -- Proof comment: compare both sections after applying terminal evaluation.
  apply (over_sections_equiv_terminal N).injective
  rw [over_sections_equiv_terminal_sectionsMap]
  simp

/-- Helper for Lemma 17.9.3: an epimorphism of `R`-module sheaves remains epic after forgetting to
the underlying sheaf of abelian groups. -/
private theorem underlying_epi_of_module_epi
    {M N : SheafOfModules R} (p : M ⟶ N) [Epi p] :
    Epi ((SheafOfModules.toSheaf R).map p) := by
  -- TODO for Lemma 17.9.3: prove epi preservation for `SheafOfModules.toSheaf` via the correct
  -- exact/preserves-colimits API instead of the current universe-mismatched route.
  sorry

/-- Helper for Lemma 17.9.3: restricting an epic module-sheaf morphism to a slice site keeps it
epic. -/
private theorem overRestrictionFunctor_map_epi
    {U : C} {M N : SheafOfModules R} (p : M ⟶ N) [Epi p] :
    Epi ((overRestrictionFunctor (R := R) U).map p) := by
  -- TODO for Lemma 17.9.3: deduce slice epimorphicity from the adjunction/underlying-sheaf
  -- transport after the ambient epi-reflection lemmas are repaired.
  sorry

/-- Helper for Lemma 17.9.3: an epic module-sheaf morphism admits local lifts of ambient
sections. -/
private theorem exists_cover_lift_of_locallySurjective_section
    {M N : SheafOfModules R} (p : M ⟶ N)
    [Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map p)]
    (U : C) (s : N.val.obj (op U)) :
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      ∃ t : M.val.obj (op I.Y),
        (p.val.app (op I.Y)) t = N.val.map I.f.op s := by
  -- TODO for Lemma 17.9.3: once the ambient epi/local-surjectivity bridge is restored, package
  -- the image-sieve cover and canonical local preimages here.
  sorry

/-- Helper for Lemma 17.9.3: an epic module-sheaf morphism admits local lifts of ambient
sections. -/
private theorem exists_cover_lift_of_epi_section
    {M N : SheafOfModules R} (p : M ⟶ N) [Epi p] (U : C)
    (s : N.val.obj (op U)) :
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      ∃ t : M.val.obj (op I.Y),
        (p.val.app (op I.Y)) t = N.val.map I.f.op s := by
  -- TODO for Lemma 17.9.3: derive local lifts from the repaired underlying-sheaf epi theorem and
  -- the image-sieve cover construction.
  sorry

/-- Helper for Lemma 17.9.3: sections of the restriction of a module sheaf to `W : Over U` are
canonically identified with the value of the ambient sheaf on `W`. -/
private theorem over_sections_equiv_obj_inv_property
    {U : C} (M : SheafOfModules (R.over U)) (W : Over U)
    (m : M.val.obj (op W)) :
    ∀ ⦃V Y : (Over W)ᵒᵖ⦄ (f : V ⟶ Y),
      (M.over W).val.map f ((M.over W).val.map ((Over.mkIdTerminal.from V.unop).op) m) =
        (M.over W).val.map ((Over.mkIdTerminal.from Y.unop).op) m := by
  intro V Y f
  -- Proof comment: every object of `Over W` has a unique map to the terminal object.
  have h :
      (Over.mkIdTerminal.from V.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
    apply Quiver.Hom.unop_inj
    simp only [Quiver.Hom.unop_op]
    exact Over.mkIdTerminal.hom_ext
      (f.unop ≫ Over.mkIdTerminal.from V.unop)
      (Over.mkIdTerminal.from Y.unop)
  rw [← PresheafOfModules.map_comp_apply, h]

/-- Helper for Lemma 17.9.3: a section of `M.over W` is determined by its value on the terminal
object of `Over W`. -/
private theorem over_sections_equiv_obj_left_inv
    {U : C} (M : SheafOfModules (R.over U)) (W : Over U)
    (s : (M.over W).sections) :
    (M.over W).val.sectionsMk
        (fun V ↦ (M.over W).val.map ((Over.mkIdTerminal.from V.unop).op)
          (s.1 (op (Over.mk (𝟙 W)))))
        (over_sections_equiv_obj_inv_property (R := R) M W
          (s.1 (op (Over.mk (𝟙 W))))) = s := by
  -- Proof comment: a section of the localized sheaf is recovered from its terminal value.
  ext V
  simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from V.unop).op)

/-- Helper for Lemma 17.9.3: evaluating the section induced by `m` at the terminal object gives
back `m`. -/
private theorem over_sections_equiv_obj_right_inv
    {U : C} (M : SheafOfModules (R.over U)) (W : Over U)
    (m : M.val.obj (op W)) :
    ((M.over W).val.sectionsMk
        (fun V ↦ (M.over W).val.map ((Over.mkIdTerminal.from V.unop).op) m)
        (over_sections_equiv_obj_inv_property (R := R) M W m)).1
      (op (Over.mk (𝟙 W))) = m := by
  -- Proof comment: the terminal restriction of the reconstructed section is the original value.
  change (M.over W).val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 W))).op) m = m
  have h :
      Over.mkIdTerminal.from (Over.mk (𝟙 W)) = 𝟙 (Over.mk (𝟙 W)) :=
    Over.mkIdTerminal.hom_ext _ _
  simpa using (M.over W).val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 17.9.3: sections of the restriction to `W : Over U` are canonically
identified with the ambient value on `W`. -/
private noncomputable def over_sections_equiv_obj
    {U : C} (M : SheafOfModules (R.over U)) (W : Over U) :
    (M.over W).sections ≃ M.val.obj (op W) :=
  { toFun := fun s ↦ s.1 (op (Over.mk (𝟙 W)))
    invFun := fun m ↦
      (M.over W).val.sectionsMk
        (fun V ↦ (M.over W).val.map ((Over.mkIdTerminal.from V.unop).op) m)
        (over_sections_equiv_obj_inv_property (R := R) M W m)
    left_inv := over_sections_equiv_obj_left_inv (R := R) M W
    right_inv := over_sections_equiv_obj_right_inv (R := R) M W }

/-- Helper for Lemma 17.9.3: under the canonical section equivalence, restriction of a morphism
to `W` acts by the ambient component map on `W`. -/
private theorem overRestrictionFunctor_map_app_terminal
    {U : C} {M N : SheafOfModules (R.over U)}
    (ψ : M ⟶ N) (W : Over U) :
    ((overRestrictionFunctor (R := R.over U) W).map ψ).val.app (op (Over.mk (𝟙 W))) =
      ψ.val.app (op W) := by
  ext m
  rfl

/-- Helper for Lemma 17.9.3: under the canonical section equivalence, the restricted morphism
acts on sections by the ambient component map on `W`. -/
private theorem over_sections_equiv_obj_sectionsMap
    {U : C} {M N : SheafOfModules (R.over U)}
    (ψ : M ⟶ N) (W : Over U) (s : (M.over W).sections) :
    (over_sections_equiv_obj (R := R) N W)
      (SheafOfModules.sectionsMap ((overRestrictionFunctor (R := R.over U) W).map ψ) s) =
        (ψ.val.app (op W)) ((over_sections_equiv_obj (R := R) M W) s) := by
  -- Proof comment: evaluating both sides at the terminal object produces the same formula.
  change (((overRestrictionFunctor (R := R.over U) W).map ψ).val.app
      (op (Over.mk (𝟙 W)))) (s.1 (op (Over.mk (𝟙 W)))) =
    (ψ.val.app (op W)) (s.1 (op (Over.mk (𝟙 W))))
  exact congrArg
    (fun f : M.val.obj (op W) ⟶ N.val.obj (op W) ↦ f (s.1 (op (Over.mk (𝟙 W)))))
    (overRestrictionFunctor_map_app_terminal (R := R) ψ W)

/-- Helper for Lemma 17.9.3: the inverse of the section equivalence is natural in the sheaf
morphism. -/
private theorem sectionsMap_over_sections_equiv_obj_symm
    {U : C} {M N : SheafOfModules (R.over U)}
    (ψ : M ⟶ N) (W : Over U) (m : M.val.obj (op W)) :
    SheafOfModules.sectionsMap ((overRestrictionFunctor (R := R.over U) W).map ψ)
        ((over_sections_equiv_obj (R := R) M W).symm m) =
      (over_sections_equiv_obj (R := R) N W).symm ((ψ.val.app (op W)) m) := by
  -- Proof comment: compare the two sections after evaluating on the terminal object of `Over W`.
  apply (over_sections_equiv_obj (R := R) N W).injective
  rw [over_sections_equiv_obj_sectionsMap]
  simp

/-- Helper for Lemma 17.9.3: restricting the generating epimorphism of a generating family keeps
it epic on the slice. -/
private theorem restrictedGeneratingPiEpi
    {U : C} {M : SheafOfModules (R.over U)}
    (σ : M.GeneratingSections) (W : Over U) :
    Epi ((overRestrictionFunctor (R := R.over U) W).map σ.π) := by
  -- Route correction: use the slice adjunction directly, as in the working sibling files,
  -- instead of introducing extra iterated-slice hypotheses.
  let F : SheafOfModules (R.over U) ⥤
      SheafOfModules ((R.over U).over W) :=
    overRestrictionFunctor (R := R.over U) W
  letI : Functor.PreservesEpimorphisms F :=
    Functor.preservesEpimorphisms_of_adjunction
      (SheafOfModules.overPushforwardOverAdj (R := R.over U) W)
  -- Proof comment: restriction to `W` is a left adjoint on module sheaves, so it preserves the
  -- epimorphic generating map `σ.π`.
  change Epi (F.map σ.π)
  infer_instance

/-- Helper for Lemma 17.9.3: the terminal maps in `Over U` compose functorially. -/
private theorem mkIdTerminal_from_comp
    {U : C} {V W : Over U} (g : W ⟶ V) :
    g ≫ Over.mkIdTerminal.from V = Over.mkIdTerminal.from W := by
  -- Proof comment: `Over.mk (𝟙 U)` is terminal in the slice category.
  exact Over.mkIdTerminal.hom_ext _ _

/-- Helper for Lemma 17.9.3: after passing to opposites, the terminal maps in `Over U` still
compose functorially. -/
private theorem op_mkIdTerminal_from_comp
    {U : C} {V W : Over U} (g : W ⟶ V) :
    (Over.mkIdTerminal.from V).op ≫ g.op = (Over.mkIdTerminal.from W).op := by
  exact congrArg Quiver.Hom.op (mkIdTerminal_from_comp (g := g))

/-- Helper for Lemma 17.9.3: a local lift on a slice chart restricts along any further slice arrow
to the corresponding lift on the refinement. -/
private theorem local_lift_restricts_along_slice_arrow
    {U : C} {M N : SheafOfModules (R.over U)} (p : M ⟶ N)
    {V W : Over U} (g : W ⟶ V)
    {s : N.val.obj (op (Over.mk (𝟙 U)))} {t : M.val.obj (op V)}
    (ht : (p.val.app (op V)) t = N.val.map (Over.mkIdTerminal.from V).op s) :
    (p.val.app (op W)) (M.val.map g.op t) =
      N.val.map (Over.mkIdTerminal.from W).op s := by
  -- Route correction: first rewrite the lift along the naturality square for `p`, then collapse
  -- the terminal-map composite using functoriality in `Over U`.
  have hnat :=
    congrArg
      (fun f : M.val.obj (op V) ⟶ N.val.obj (op W) ↦ f t)
      (p.val.naturality g.op)
  rw [ht] at hnat
  calc
    (p.val.app (op W)) (M.val.map g.op t) =
      N.val.map g.op ((p.val.app (op V)) t) := by
        simpa using hnat.symm
    _ = N.val.map g.op (N.val.map (Over.mkIdTerminal.from V).op s) := by
        rw [ht]
    _ = N.val.map ((Over.mkIdTerminal.from W).op) s := by
        rw [← PresheafOfModules.map_comp_apply, op_mkIdTerminal_from_comp (g := g)]

/-- Helper for Lemma 17.9.3: the sieve generated by a family of slice objects is the sieve
generated by the corresponding underlying arrows in the ambient site. -/
private theorem over_sieve_of_objects_eq_of_arrows
    {U : C} {ι : Type*} (X : ι → Over U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects X (Over.mk (𝟙 U))) =
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) := by
  ext W g
  constructor
  · intro hg
    -- Proof comment: a factorization in the slice category forgets to the same factorization in
    -- the ambient site.
    rw [Sieve.overEquiv_iff] at hg
    rw [Sieve.mem_ofObjects_iff] at hg
    rcases hg with ⟨i, ⟨a⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, a.left, by simpa using a.w.symm⟩
  · intro hg
    -- Proof comment: conversely, any underlying factorization lifts uniquely to the slice.
    rw [Sieve.overEquiv_iff]
    rw [Sieve.mem_ofArrows_iff] at hg
    rcases hg with ⟨i, a, ha⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk a (by simpa using ha.symm)⟩⟩

/-- Helper for Lemma 17.9.3: the cover arrows of a slice cover of `V` form a top cover on the
slice over `V.left`. -/
private theorem cover_arrow_family_coversTop_left
    {U : C} {V : Over U} (T : (J.over U).Cover V) :
    (J.over V.left).CoversTop (fun A : T.Arrow ↦ Over.mk A.f.left) := by
  -- Proof comment: reduce the `CoversTop` statement to a covering sieve statement on the
  -- terminal object of `J.over V.left`.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := J.over V.left) (X := Over.mk (𝟙 V.left)) (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, over_sieve_of_objects_eq_of_arrows]
  have hT : (Sieve.overEquiv V) T.1 ∈ J V.left := by
    -- Proof comment: forgetting a covering sieve in the slice over `U` gives a covering sieve on
    -- `V.left` in the ambient site.
    have hT' : T.1 ∈ (J.over U) V := T.2
    rw [GrothendieckTopology.mem_over_iff] at hT'
    exact hT'
  have hCoverSieve :
      (Sieve.overEquiv V) T.1 =
        Sieve.ofArrows (fun A : T.Arrow ↦ A.Y.left) (fun A : T.Arrow ↦ A.f.left) := by
    ext W g
    constructor
    · intro hg
      -- Proof comment: an arrow in the forgotten covering sieve is one of the cover arrows,
      -- viewed downstairs in `C`.
      rw [Sieve.overEquiv_iff] at hg
      rw [Sieve.mem_ofArrows_iff]
      refine ⟨⟨Over.mk (g ≫ V.hom), Over.homMk g (by simp), ?_⟩, 𝟙 _, ?_⟩
      · simpa using hg
      · simp
    · intro hg
      -- Proof comment: a downstairs factorization through one of the underlying cover arrows
      -- lifts uniquely to the corresponding slice morphism.
      rw [Sieve.overEquiv_iff]
      rw [Sieve.mem_ofArrows_iff] at hg
      rcases hg with ⟨A, a, ha⟩
      have hcomp : a ≫ A.f.left ≫ V.hom = g ≫ V.hom := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ V.hom) ha.symm
      have hcomp' : a ≫ A.Y.hom = g ≫ V.hom := by
        have hArrow : A.Y.hom = A.f.left ≫ V.hom := by
          simpa using A.f.w.symm
        calc
          a ≫ A.Y.hom = a ≫ (A.f.left ≫ V.hom) := by
            rw [hArrow]
            rfl
          _ = g ≫ V.hom := by simpa [Category.assoc] using hcomp
      let aOver : Over.mk (g ≫ V.hom) ⟶ A.Y := Over.homMk a hcomp'
      have hOver : aOver ≫ A.f = Over.homMk g (by simp) := by
        ext
        simpa using ha.symm
      exact hOver ▸ T.1.downward_closed A.hf aOver
  have hCover :
      Sieve.ofArrows (fun A : T.Arrow ↦ A.Y.left) (fun A : T.Arrow ↦ A.f.left) ∈ J V.left := by
    rwa [← hCoverSieve]
  simpa using hCover

/-- Helper for Lemma 17.9.3: composing a covering family of `U` with covering families on each
member yields a sigma-indexed covering family of `U`. -/
private theorem coversTopSigmaComp
    {U : C} {I : Type (max u v)} {X : I → Over U}
    (hX : (J.over U).CoversTop X)
    {K : I → Type (max u v)} {Y : ∀ i : I, K i → Over (X i).left}
    (hY : ∀ i : I, (J.over (X i).left).CoversTop (Y i)) :
    (J.over U).CoversTop
      (fun a : Σ i : I, K i ↦ Over.mk ((Y a.1 a.2).hom ≫ (X a.1).hom)) := by
  -- Proof comment: first translate the two slice covers to ambient arrow-generated sieves,
  -- then compose them with the standard `bindOfArrows` transitivity lemma.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal
    (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff, over_sieve_of_objects_eq_of_arrows]
  have hX' :
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈ J U := by
    have hXTerminal :
        Sieve.ofObjects X (Over.mk (𝟙 U)) ∈ (J.over U) (Over.mk (𝟙 U)) :=
      (GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal) X).1 hX
    rw [GrothendieckTopology.mem_over_iff, over_sieve_of_objects_eq_of_arrows] at hXTerminal
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
    rw [GrothendieckTopology.mem_over_iff, over_sieve_of_objects_eq_of_arrows] at hYTerminal
    exact hYTerminal
  simpa [Presieve.bindOfArrows_ofArrows] using
    J.bindOfArrows
      (h := hX')
      (R := fun i ↦ Presieve.ofArrows (fun k ↦ (Y i k).left) (fun k ↦ (Y i k).hom))
      (fun i ↦ by simpa using hY' i)

/-- Helper for Lemma 17.9.3: a finite family of sections over the terminal object of the slice
site admits a common refinement on which all sections lift simultaneously. -/
private theorem liftedGeneratingFamilyCover
    {U : C} {M N : SheafOfModules (R.over U)}
    (σ : N.GeneratingSections) [σ.IsFiniteType] (p : M ⟶ N) [Epi p] :
    ∃ (κ : Type (max u v)) (cover : κ → Over U), (J.over U).CoversTop cover ∧
      ∀ k : κ, ∀ i : σ.I,
        ∃ t : M.val.obj (op (cover k)),
          (p.val.app (op (cover k))) t =
            N.val.map (Over.mkIdTerminal.from (cover k)).op
              ((σ.s i).1 (op (Over.mk (𝟙 U)))) := by
  -- TODO for Lemma 17.9.3: perform the finite simultaneous-lifting induction after the ambient
  -- local lifting and cover-composition helpers are repaired.
  sorry

/-- Helper for Lemma 17.9.3: a quotient of a finite-type module sheaf is finite type. -/
theorem isFiniteType_of_epi
    {M N : SheafOfModules R} (p : M ⟶ N) [Epi p] [M.IsFiniteType] :
    N.IsFiniteType := by
  -- TODO for Lemma 17.9.3: reuse the ambient local-generator cover and push each chartwise
  -- generating family through the repaired restricted epimorphism.
  sorry

/-- Finite-type sheaves of modules are closed under quotients. -/
instance isFiniteType_isClosedUnderQuotients :
    ObjectProperty.IsClosedUnderQuotients
      (SheafOfModules.IsFiniteType : ObjectProperty (SheafOfModules R)) := by
  refine ⟨?_⟩
  intro M N p _ hM
  -- Proof comment: quotient-closure is the public `ObjectProperty` packaging of
  -- `isFiniteType_of_epi`.
  letI : M.IsFiniteType := hM
  exact isFiniteType_of_epi (R := R) p

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Helper for Lemma 17.9.3: finite-type sheaves of modules remain finite type after transport
across an isomorphism. -/
lemma finite_type_closed_under_isomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (SheafOfModules.IsFiniteType : ObjectProperty (SheafOfModules R)) where
  of_iso := by
    -- TODO for Lemma 17.9.3: transport local finite generating data across the isomorphism once
    -- the restriction functor block is stabilized.
    sorry

/-- Helper for Lemma 17.9.3: a morphism out of a sheaf generated by `σ` is zero once it kills
all generators in `σ`. -/
private theorem hom_eq_zero_of_vanishing_on_generators
    {M N : SheafOfModules R} (σ : M.GeneratingSections) (φ : M ⟶ N)
    (_hφ : True) : True := by
  -- TODO for Lemma 17.9.3: restore the intended generator-vanishing statement after replacing the
  -- unsupported `0 : N.sections` spelling with the correct zero-section API.
  sorry

/-- Helper for Lemma 17.9.3: once quotient generators are lifted to the middle term of a short
exact sequence, adjoining them to generators of the kernel gives a generating family of the middle
term. -/
private theorem epi_sumGeneratingSections_of_shortExact
    {U : C} {S : ShortComplex (SheafOfModules (R.over U))} (hS : S.ShortExact)
    (σ₁ : S.X₁.GeneratingSections) (σ₃ : S.X₃.GeneratingSections)
    (lift : σ₃.I → S.X₂.sections)
    (hlift : ∀ i : σ₃.I, SheafOfModules.sectionsMap S.g (lift i) = σ₃.s i) :
    True := by
  -- TODO for Lemma 17.9.3: show the cokernel of the summed generating map vanishes by combining
  -- exact descent along `g` with generator-vanishing on both summands.
  let _ := hS
  let _ := σ₁
  let _ := σ₃
  let _ := lift
  let _ := hlift
  sorry

/-- Helper for Lemma 17.9.3: the combined generating family has finite index type whenever both
the kernel generators and quotient generators do. -/
private theorem isFiniteType_sumGeneratingSections
    {U : C} {S : ShortComplex (SheafOfModules (R.over U))}
    (σ₁ : S.X₁.GeneratingSections) (σ₃ : S.X₃.GeneratingSections)
    (lift : σ₃.I → S.X₂.sections)
    [σ₁.IsFiniteType] [σ₃.IsFiniteType] :
    True := by
  -- TODO for Lemma 17.9.3: once the summed generating family is packaged without elaboration
  -- issues, its finite index type is the finite sum of the two chartwise index types.
  let _ := S
  let _ := σ₁
  let _ := σ₃
  let _ := lift
  sorry

-- Proof sketch: in a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0`, locally lift finite generators
-- of `ℱ₃` along the epimorphism and adjoin finite generators of `ℱ₁`; these jointly generate
-- `ℱ₂`.
/-- Finite-type sheaves of modules are closed under extensions. -/
instance isFiniteType_isClosedUnderExtensions :
    ObjectProperty.IsClosedUnderExtensions
      (SheafOfModules.IsFiniteType : ObjectProperty (SheafOfModules R)) := by
  -- TODO for Lemma 17.9.3: after the slice restriction and lifting helpers are repaired, choose
  -- finite local generators on `S.X₁` and `S.X₃`, refine the covers, lift the right generators
  -- locally, adjoin the left generators, and package the resulting finite local data for `S.X₂`.
  sorry

/-- Helper for Lemma 17.9.3: once quotients are known to preserve finite type, the coimage of a
map from a finite-type module sheaf is finite type. -/
private theorem isFiniteType_coimage_of_finiteType
    {M N : SheafOfModules R} (φ : M ⟶ N) [M.IsFiniteType] :
    (Abelian.coimage φ).IsFiniteType := by
  -- Proof comment: `Abelian.coimage.π φ` is epic, so the quotient-closure instance applies
  -- directly to the source object `M`.
  exact isFiniteType_of_epi (R := R) (Abelian.coimage.π φ)

/-- Lemma 17.9.3 (1): the image of a morphism from a finite-type sheaf of modules is again of
finite type. -/
@[stacks 01B7]
theorem isFiniteType_image (φ : ℱ ⟶ 𝒢) [ℱ.IsFiniteType] :
    (Abelian.image φ).IsFiniteType := by
  -- TODO for Lemma 17.9.3: once quotient-closure is restored without placeholder owners, factor
  -- through the coimage and transport finite type across `Abelian.coimageIsoImage φ`.
  sorry

-- Proof sketch: this is exactly the extension-closure statement for the object property
-- attached to `SheafOfModules.IsFiniteType`.
omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Lemma 17.9.3 (2): in a short exact sequence of sheaves of modules, if the left and right terms
are of finite type, then the middle term is of finite type. -/
@[stacks 01B7]
theorem isFiniteType_of_shortExact
    {ℱ₁ ℱ₂ ℱ₃ : SheafOfModules R}
    (f : ℱ₁ ⟶ ℱ₂) (g : ℱ₂ ⟶ ℱ₃) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [ℱ₁.IsFiniteType] [ℱ₃.IsFiniteType] :
    ℱ₂.IsFiniteType := by
  -- TODO for Lemma 17.9.3: once the extension-closure instance is repaired, discharge this by
  -- the owner theorem `ObjectProperty.prop_X₂_of_shortExact`.
  let _ := f
  let _ := g
  let _ := hfg
  let _ := hS
  sorry

end SheafOfModules
