import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe u v

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J RingCat.{u}}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
variable [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Domain-style sampling for Lemma 18.24.1:
- primary domain: finite type and finite presentation for sheaves of modules over a sheaf of
  rings on a site, with ringed sites as the source-facing specialization;
- inspected owner declarations:
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`,
  `SheafOfModules.Presentation`,
  `SheafOfModules.isFiniteType_kernel_of_epi_of_finitePresentation`;
- best owner abstraction:
  the generic owner category `SheafOfModules 𝒪`, with finite type / finite presentation as the
  canonical owner predicates and `cokernel` as derived abelian-category data;
- primitive data:
  a morphism `φ : 𝒢 ⟶ ℱ` together with `[𝒢.IsFiniteType]` and `[ℱ.IsFinitePresentation]`;
- derived API:
  the finite-presentation conclusion for `cokernel φ`.

Source/core/bridge triage:
- `source-facing`: the ringed-site statement of Stacks Project Lemma 18.24.1;
- `core/canonical`: the generic owner theorem
  `SheafOfModules.isFinitePresentation_cokernel`;
- `bridge/view`: ringed-space and ringed-site specializations obtained by instantiating the
  ambient sheaf of rings.

No upstream theorem with this interface is available in mathlib or earlier project files. This
file is therefore the owner declaration for the generic `SheafOfModules` statement, and downstream
ringed-space or ringed-site formulations should recall it rather than introducing parallel local
wrappers.
-/

open CategoryTheory.ObjectProperty

variable {M N : SheafOfModules 𝒪}

/-- Helper for Lemma 18.24.1: transporting generating sections across the inverse of an
isomorphism rewrites the associated presentation map as postcomposition by that inverse. -/
private theorem generatingSections_ofEpi_pi
    (e : M ≅ N) (σ : N.GeneratingSections) :
    σ.π ≫ e.inv = (σ.ofEpi e.inv).π := by
  -- Proof comment: `GeneratingSections.ofEpi` only changes the target by postcomposing the
  -- original presentation map with the chosen epimorphism.
  simp

/-- Helper for Lemma 18.24.1: pushing a finite generating family through an epimorphism preserves
finiteness of the indexing type because `ofEpi` does not change the index set. -/
private theorem generatingSections_isFiniteType_ofEpi
    {A B : SheafOfModules 𝒪} (σ : A.GeneratingSections) [σ.IsFiniteType]
    (p : A ⟶ B) [Epi p] :
    (σ.ofEpi p).IsFiniteType := by
  -- Proof comment: `GeneratingSections.ofEpi` keeps the same index type, so only the original
  -- finiteness witness is used.
  refine ⟨?_⟩
  simpa [SheafOfModules.GeneratingSections.ofEpi] using (inferInstance : Finite σ.I)

/-- Helper for Lemma 18.24.1: the relation sheaf attached to a generating family transports
across an isomorphism. -/
private noncomputable def generatorsRelationTransportIso
    (e : M ≅ N) (σ : N.GeneratingSections) :
    kernel σ.π ≅ kernel (σ.ofEpi e.inv).π :=
  -- Proof comment: first compare kernels under postcomposition with the monomorphism `e.inv`,
  -- then rewrite the postcomposed map to the `ofEpi` presentation map.
  (kernelCompMono _ e.inv).symm.trans <|
    eqToIso (congrArg (fun f ↦ kernel f) (generatingSections_ofEpi_pi e σ))

/-- Helper for Lemma 18.24.1: a presentation transports across an isomorphism without changing
its generator and relation index types. -/
private noncomputable def presentationOfIso
    (e : M ≅ N) (P : N.Presentation) :
    M.Presentation where
  generators := P.generators.ofEpi e.inv
  relations := P.relations.ofEpi (generatorsRelationTransportIso e P.generators).hom

/-- Helper for Lemma 18.24.1: transporting a finite presentation across an isomorphism preserves
finiteness of the chosen generators and relations. -/
private theorem presentationOfIso_isFinite
    (e : M ≅ N) (P : N.Presentation) [P.IsFinite] :
    (presentationOfIso e P).IsFinite := by
  constructor
  · -- Proof comment: the transported generators are the original generators pushed through the
    -- inverse isomorphism, so the same finite index type still generates.
    simpa [presentationOfIso] using
      (generatingSections_isFiniteType_ofEpi (σ := P.generators) (p := e.inv))
  · -- Proof comment: the transported relation generators live on an isomorphic kernel, so their
    -- finite index type is unchanged as well.
    simpa [presentationOfIso, SheafOfModules.GeneratingSections.ofEpi] using
      (SheafOfModules.Presentation.IsFinite.finite_relations (p := P))

/-- Helper for Lemma 18.24.1: transporting generating sections across an isomorphism on a slice
site rewrites the presentation map as postcomposition by that inverse. -/
private theorem generatingSections_ofEpi_over_pi
    {U : C} {M N : SheafOfModules (𝒪.over U)}
    (e : M ≅ N) (σ : N.GeneratingSections) :
    σ.π ≫ e.inv = (σ.ofEpi e.inv).π := by
  -- Proof comment: the slice-site `ofEpi` construction is the same postcomposition operation as
  -- on the ambient site.
  simp

/-- Helper for Lemma 18.24.1: on a slice site, pushing a finite generating family through an
epimorphism preserves the finiteness of the indexing type. -/
private theorem generatingSections_isFiniteType_ofEpi_over
    {U : C} {A B : SheafOfModules (𝒪.over U)} (σ : A.GeneratingSections) [σ.IsFiniteType]
    (p : A ⟶ B) [Epi p] :
    (σ.ofEpi p).IsFiniteType := by
  -- Proof comment: `GeneratingSections.ofEpi` leaves the index type unchanged on the slice site
  -- just as it does on the ambient site.
  refine ⟨?_⟩
  simpa [SheafOfModules.GeneratingSections.ofEpi] using (inferInstance : Finite σ.I)

/-- Helper for Lemma 18.24.1: the relation sheaf attached to a generating family transports
across an isomorphism on a slice site. -/
private noncomputable def generatorsRelationTransportOverIso
    {U : C} {M N : SheafOfModules (𝒪.over U)}
    (e : M ≅ N) (σ : N.GeneratingSections) :
    kernel σ.π ≅ kernel (σ.ofEpi e.inv).π :=
  -- Proof comment: compare kernels under postcomposition with `e.inv`, then rewrite the target
  -- map to the canonical `ofEpi` presentation map on the slice site.
  (kernelCompMono _ e.inv).symm.trans <|
    eqToIso (congrArg (fun f ↦ kernel f) (generatingSections_ofEpi_over_pi e σ))

/-- Helper for Lemma 18.24.1: a presentation on a slice site transports across an isomorphism
without changing its generator and relation index types. -/
private noncomputable def presentationOfOverIso
    {U : C} {M N : SheafOfModules (𝒪.over U)}
    (e : M ≅ N) (P : N.Presentation) :
    M.Presentation where
  generators := P.generators.ofEpi e.inv
  relations := P.relations.ofEpi (generatorsRelationTransportOverIso e P.generators).hom

/-- Helper for Lemma 18.24.1: transporting a finite presentation across an isomorphism on a slice
site preserves finiteness of the chosen generators and relations. -/
private theorem presentationOfOverIso_isFinite
    {U : C} {M N : SheafOfModules (𝒪.over U)}
    (e : M ≅ N) (P : N.Presentation) [P.IsFinite] :
    (presentationOfOverIso e P).IsFinite := by
  constructor
  · -- Proof comment: the transported generators on the slice keep the same finite index type.
    simpa [presentationOfOverIso] using
      (generatingSections_isFiniteType_ofEpi_over (σ := P.generators) (p := e.inv))
  · -- Proof comment: the transported relation family on the slice reuses the original finite
    -- relation index type.
    simpa [presentationOfOverIso, SheafOfModules.GeneratingSections.ofEpi] using
      (SheafOfModules.Presentation.IsFinite.finite_relations (p := P))

/-- Helper for Lemma 18.24.1: on the slice site over `U`, global sections are recovered by
evaluation at the terminal object `U ⟶ U`. -/
private noncomputable def overSectionsEquivEvaluation
    {U : C} (M : SheafOfModules (𝒪.over U)) :
    M.sections ≃ M.val.obj (Opposite.op (Over.mk (𝟙 U))) where
  toFun s := s.1 (Opposite.op (Over.mk (𝟙 U)))
  invFun m :=
    M.val.sectionsMk
      (fun W ↦ M.val.map ((Over.mkIdTerminal.from W.unop).op) m)
      (fun W Y f ↦ by
        -- Proof comment: every object of `Over U` has a unique map to the terminal object.
        have h :
            (Over.mkIdTerminal.from W.unop).op ≫ f = (Over.mkIdTerminal.from Y.unop).op := by
          apply Quiver.Hom.unop_inj
          simp only [Quiver.Hom.unop_op]
          exact Over.mkIdTerminal.hom_ext
            (f.unop ≫ Over.mkIdTerminal.from W.unop)
            (Over.mkIdTerminal.from Y.unop)
        rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := by
    -- Proof comment: a section on the slice is determined by its restrictions from the terminal
    -- object.
    ext W
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from W.unop).op)
  right_inv m := by
    -- Proof comment: the section reconstructed from a terminal value evaluates back to that value.
    change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h :
        Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 18.24.1: under terminal evaluation on a slice site, `sectionsMap` acts by
the terminal component of the underlying sheaf morphism. -/
private theorem overSectionsEquivEvaluation_sectionsMap
    {U : C} {M N : SheafOfModules (𝒪.over U)}
    (ψ : M ⟶ N) (s : M.sections) :
    overSectionsEquivEvaluation N (SheafOfModules.sectionsMap ψ s) =
      (ψ.val.app (Opposite.op (Over.mk (𝟙 U)))) (overSectionsEquivEvaluation M s) := by
  -- Proof comment: both sides are definitionally evaluation of the mapped section at the
  -- terminal object `U ⟶ U`.
  rfl

/-- Helper for Lemma 18.24.1: the inverse terminal-evaluation equivalence is natural in the
module morphism. -/
private theorem sectionsMap_overSectionsEquivEvaluation_symm
    {U : C} {M N : SheafOfModules (𝒪.over U)}
    (ψ : M ⟶ N) (m : M.val.obj (Opposite.op (Over.mk (𝟙 U)))) :
    SheafOfModules.sectionsMap ψ ((overSectionsEquivEvaluation M).symm m) =
      (overSectionsEquivEvaluation N).symm ((ψ.val.app (Opposite.op (Over.mk (𝟙 U)))) m) := by
  -- Proof comment: compare the two sections after evaluating both at the terminal object.
  apply (overSectionsEquivEvaluation N).injective
  rw [overSectionsEquivEvaluation_sectionsMap]
  simp

/-- Helper for Lemma 18.24.1: on a slice site, the relation map of a presentation is the composite
from the chosen relation generators into the free module on the chosen generators. -/
private noncomputable def presentationRelationMap
    {U : C} {M : SheafOfModules (𝒪.over U)} (P : M.Presentation) :=
  -- Proof comment: a presentation records generators for `M` and generators for the kernel of the
  -- generator map, so the relation map is just the kernel inclusion after the relation epimorphism.
  P.relations.π ≫ kernel.ι P.generators.π

/-- Helper for Lemma 18.24.1: the relation map of a presentation vanishes after the generator map.
-/
private theorem presentationRelationMap_comp_generators
    {U : C} {M : SheafOfModules (𝒪.over U)} (P : M.Presentation) :
    presentationRelationMap (𝒪 := 𝒪) P ≫ P.generators.π = 0 := by
  -- Proof comment: the relation map lands in the kernel of `P.generators.π` by construction.
  simp [presentationRelationMap, Category.assoc]

/-- Helper for Lemma 18.24.1: on a slice site, any presentation already realizes its generator map
as the cokernel of the corresponding relation map, without using the stronger `HasSheafify`
restriction API. -/
private theorem presentationGenerators_isCokernel
    {U : C} {M : SheafOfModules (𝒪.over U)} (P : M.Presentation) :
    IsColimit (CokernelCofork.ofπ P.generators.π
      (presentationRelationMap_comp_generators (𝒪 := 𝒪) P)) := by
  let K : Fork P.generators.π 0 :=
    Fork.ofι (kernel.ι P.generators.π) (by simp)
  let hK : IsLimit K := kernelIsKernel P.generators.π
  -- Proof comment: first view `P.generators.π` as the cokernel of the kernel inclusion, then
  -- precompose by the epimorphic relation map stored in `P.relations`.
  simpa [presentationRelationMap, K] using
    (isCokernelEpiComp (i := Abelian.epiIsCokernelOfKernel K hK) P.relations.π rfl)

/-- Helper for Lemma 18.24.1: finite presentation is invariant under isomorphism. -/
private theorem isFinitePresentation_of_iso
    (e : M ≅ N) [N.IsFinitePresentation] :
    M.IsFinitePresentation := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData N
  refine SheafOfModules.IsFinitePresentation.mk ?_
  refine ⟨{
    I := q.I
    X := q.X
    coversTop := q.coversTop
    presentation := fun i ↦ ?_
  }, ?_⟩
  · -- Proof comment: restrict the global isomorphism to the current chart and transport the
    -- chosen local presentation across that restricted isomorphism.
    let eOver : M.over (q.X i) ≅ N.over (q.X i) :=
      (SheafOfModules.pushforward (𝟙 (𝒪.over (q.X i)))).mapIso e
    exact presentationOfOverIso eOver
      (q.presentation i)
  · constructor
    intro i
    -- Proof comment: each transported chart presentation keeps the same finite generator and
    -- relation index types as the original chart presentation.
    let eOver : M.over (q.X i) ≅ N.over (q.X i) :=
      (SheafOfModules.pushforward (𝟙 (𝒪.over (q.X i)))).mapIso e
    simpa using presentationOfOverIso_isFinite eOver
      (q.presentation i)

-- Proof sketch: view `cokernel φ` as the quotient of `ℱ` by the image of `φ`. The image of a
-- finite type sheaf is finite type, and the local definition of finite presentation is stable
-- under quotienting a finitely presented sheaf by a finite type submodule.
/-- Lemma 18.24.1: for a morphism `φ : 𝒢 ⟶ ℱ` of `\mathcal O`-modules on a ringed site, if `𝒢`
is of finite type and `ℱ` is finitely presented, then the cokernel of `φ` is finitely
presented. -/
@[stacks 0H98]
theorem isFinitePresentation_cokernel
    {𝒢 ℱ : SheafOfModules 𝒪} (φ : 𝒢 ⟶ ℱ) [𝒢.IsFiniteType] [ℱ.IsFinitePresentation] :
    (cokernel φ).IsFinitePresentation := by
  -- Route correction: the actual normalization issue is now isolated. Restriction does preserve
  -- cokernels on slice sites, so the remaining work is the local presentation engine turning a
  -- finite-type source and a finite presentation of the target into a finite presentation of the
  -- restricted cokernel on each chart of a finite-presentation cover of `ℱ`.
  -- TODO: construct that slice-level cokernel presentation explicitly, then glue the chartwise
  -- finite presentations back with the Chapter 18 cover criterion.
  sorry

end SheafOfModules
