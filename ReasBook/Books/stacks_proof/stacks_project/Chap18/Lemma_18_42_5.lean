import Mathlib
import stacks_proof.stacks_project.Chap07.Definition_7_42_1
import stacks_proof.stacks_project.Chap07.Lemma_7_42_2
import stacks_proof.stacks_project.Chap18.Lemma_18_42_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory

/- Domain-style sampling for Lemma 18.42.5:
- primary domain: constant sheaves of `\Lambda`-modules on a site, with canonical source-facing
  owner `((constantSheaf J (ModuleCat.{w} Λ)).obj M)`;
- sampled owner declarations from the surrounding chapter/project:
  `constantSheaf`,
  `PresheafOfModules.sheafification`,
  `SheafOfModules`,
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.IsFinitePresentation`;
- best owner abstraction: the source-facing object is the constant sheaf
  `((constantSheaf J (ModuleCat.{w} Λ)).obj M)`, while finite type and finite presentation are
  canonically owned by `SheafOfModules`; the needed bridge is therefore the generic view from a
  `ModuleCat`-valued sheaf to a `SheafOfModules` over the constant ring sheaf `\underline{\Lambda}`,
  obtained by module sheafification along the canonical map from the constant ring presheaf to
  the constant ring sheaf;
- source-facing owner added here: `Sheaf.IsFinitePresentation` for `Sheaf J (ModuleCat Λ)`,
  defined by transporting the canonical `SheafOfModules.IsFinitePresentation` predicate across the
  bridge `toConstantModuleSheaf` in the same assumption layer where that owner is available;
- primitive data: a sheaf `F : Sheaf J (ModuleCat.{w} Λ)` and its underlying presheaf of
  `\Lambda`-modules;
- derived API: the bridge `Sheaf.toConstantModuleSheaf`, the source-facing finite-presentation
  owner on `Sheaf J (ModuleCat Λ)`, and the finite-type / finite-presentation comparison lemmas
  below for the constant sheaf.

Source/core/bridge triage:
- `source-facing`: the finite-type and finite-presentation characterizations for the constant sheaf
  `\underline M`, together with `Sheaf.IsFinitePresentation` on `Sheaf J (ModuleCat Λ)`;
- `core/canonical`: `constantSheaf` and the owner predicates
  `SheafOfModules.IsFiniteType` / `SheafOfModules.IsFinitePresentation`;
- `bridge/view`: the generic sheaf-level view
  `F.toConstantModuleSheaf : SheafOfModules ((constantSheaf J RingCat.{w}).obj (RingCat.of Λ))`,
  used because the canonical finite-presentation owner lives on `SheafOfModules`. -/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J RingCat.{w}]
variable [J.WEqualsLocallyBijective RingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

namespace Sheaf

/-- The underlying presheaf of `\Lambda`-modules of a `ModuleCat`-valued sheaf, regarded as a
presheaf of modules over the constant `RingCat`-valued presheaf with value `\Lambda`. -/
private abbrev toConstantModulePresheaf (F : Sheaf J (ModuleCat.{w} Λ)) :
    PresheafOfModules ((Functor.const Cᵒᵖ).obj (RingCat.of Λ)) :=
  let P : Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
    F.1 ⋙ forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}
  letI (X : Cᵒᵖ) : Module ↑(((Functor.const Cᵒᵖ).obj (RingCat.of Λ)).obj X) ↑(P.obj X) := by
    change Module Λ ↑(F.1.obj X)
    infer_instance
  PresheafOfModules.ofPresheaf P
    (fun {X Y} f r m ↦ by
      change ((F.1.map f).hom) (r • m) = (RingHom.id Λ) r • ((F.1.map f).hom m)
      exact (F.1.map f).hom.map_smul r m)

/-- The canonical view of a sheaf of `\Lambda`-modules as a sheaf of modules over the constant
ring sheaf `\underline{\Lambda}`. This is a view bridge, not a new owner: it is obtained by
sheafifying the underlying presheaf of `\Lambda`-modules along the canonical map from the
constant ring presheaf to the constant ring sheaf. -/
noncomputable abbrev toConstantModuleSheaf (F : Sheaf J (ModuleCat.{w} Λ)) :
    SheafOfModules ((constantSheaf J RingCat.{w}).obj (RingCat.of Λ)) :=
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  letI : Presheaf.IsLocallyInjective J α := (J.W_toSheafify _).isLocallyInjective
  letI : Presheaf.IsLocallySurjective J α := (J.W_toSheafify _).isLocallySurjective
  (PresheafOfModules.sheafification α).obj (toConstantModulePresheaf F)

/-- Helper for Lemma 18.42.5: a morphism of `ModuleCat`-valued sheaves induces the corresponding
morphism between the associated constant-ring presheaves of modules. -/
private theorem toConstantModulePresheafHom_naturality
    {F G : Sheaf J (ModuleCat.{w} Λ)} (η : F ⟶ G)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (toConstantModulePresheaf F).map f ≫ η.1.app V =
      η.1.app U ≫ (toConstantModulePresheaf G).map f := by
  -- Proof comment: this is exactly the naturality square of the original sheaf morphism.
  ext x
  exact ConcreteCategory.congr_hom (η.1.naturality f) x

/-- Helper for Lemma 18.42.5: package the constant-module presheaf bridge functorially so later
exactness and quotient arguments can talk about actual morphisms in `SheafOfModules`. -/
private def toConstantModulePresheafHom
    {F G : Sheaf J (ModuleCat.{w} Λ)} (η : F ⟶ G) :
    toConstantModulePresheaf F ⟶ toConstantModulePresheaf G where
  app U := η.1.app U
  naturality := toConstantModulePresheafHom_naturality (Λ := Λ) η

/-- Helper for Lemma 18.42.5: sheafify the constant-ring presheaf bridge functorially. -/
private noncomputable def toConstantModuleSheafMap
    {F G : Sheaf J (ModuleCat.{w} Λ)} (η : F ⟶ G) :
    F.toConstantModuleSheaf ⟶ G.toConstantModuleSheaf :=
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  letI : Presheaf.IsLocallyInjective J α := (J.W_toSheafify _).isLocallyInjective
  letI : Presheaf.IsLocallySurjective J α := (J.W_toSheafify _).isLocallySurjective
  (PresheafOfModules.sheafification α).map (toConstantModulePresheafHom (Λ := Λ) η)
end Sheaf

variable [HasWeakSheafify J (ModuleCat.{w} Λ)]

variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

-- The owner predicates `IsFiniteType` and `IsFinitePresentation` live on `SheafOfModules`, so the
-- bridge object `F.toConstantModuleSheaf` below is only the `ModuleCat`-valued sheaf `F` viewed
-- in that owner category over the constant ring sheaf.

namespace Sheaf

/-- Source-facing finite presentation for a sheaf of `\Lambda`-modules, obtained by viewing it as
a sheaf of modules over the constant ring sheaf `\underline{\Lambda}`. -/
abbrev IsFinitePresentation (F : Sheaf J (ModuleCat.{w} Λ)) : Prop :=
  F.toConstantModuleSheaf.IsFinitePresentation

/-- Helper for Lemma 18.42.5: the constant sheaf map attached to a `\Lambda`-linear map, viewed
in the owner category `SheafOfModules` over the constant ring sheaf. -/
private noncomputable def constantModuleSheafMap
    {M N : ModuleCat.{w} Λ} (f : M ⟶ N) :
    (((constantSheaf J (ModuleCat.{w} Λ)).obj M).toConstantModuleSheaf) ⟶
      (((constantSheaf J (ModuleCat.{w} Λ)).obj N).toConstantModuleSheaf) :=
  toConstantModuleSheafMap (Λ := Λ) ((constantSheaf J (ModuleCat.{w} Λ)).map f)

end Sheaf

/-- Helper for Lemma 18.42.5: a finite `\Lambda`-module is the quotient of a finite free
`\Lambda`-module. -/
private theorem finiteModuleExistsFiniteFreeSurjection
    (M : ModuleCat.{w} Λ) [Module.Finite Λ M] :
    ∃ n : ℕ, ∃ φ : ModuleCat.of Λ (Fin n → Λ) ⟶ M, Function.Surjective φ.hom := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := Λ) (M := M)
  let ψ : (Fin n → Λ) ≃ₗ[Λ] (Fin n →₀ Λ) :=
    (Finsupp.linearEquivFunOnFinite Λ Λ (Fin n)).symm
  let φLinear : (Fin n → Λ) →ₗ[Λ] M :=
    Finsupp.linearCombination Λ s ∘ₗ ψ.toLinearMap
  have hφ_range : LinearMap.range φLinear = ⊤ := by
    -- Proof comment: the chosen finite family spans `M`, and the finite-support model for
    -- `Fin n → Λ` transfers that spanning statement to the linear map `φLinear`.
    rw [LinearMap.range_comp_of_range_eq_top _ ψ.range]
    rw [Finsupp.range_linearCombination]
    exact hs
  have hφ_surj : Function.Surjective φLinear := by
    intro m
    have hm : m ∈ LinearMap.range φLinear := by
      rw [hφ_range]
      trivial
    rcases hm with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  exact ⟨n, ModuleCat.ofHom φLinear, hφ_surj⟩

/-- Helper for Lemma 18.42.5: a finitely presented `\Lambda`-module admits an exact presentation
by finite free `\Lambda`-modules. -/
private theorem finitelyPresentedModuleExistsFiniteFreePresentation
    (M : ModuleCat.{w} Λ) [Module.FinitePresentation Λ M] :
    ∃ (m n : ℕ) (f : ModuleCat.of Λ (Fin m → Λ) ⟶ ModuleCat.of Λ (Fin n → Λ))
      (g : ModuleCat.of Λ (Fin n → Λ) ⟶ M),
      Function.Exact f.hom g.hom ∧ Function.Surjective g.hom := by
  classical
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin Λ M
  obtain ⟨t, ht⟩ := hK
  let generators : t → (Fin n → Λ) := fun i ↦ i.1
  let ψ :
      (Fin t.card → Λ) ≃ₗ[Λ] t →₀ Λ :=
    (Finsupp.linearEquivFunOnFinite Λ Λ (Fin t.card)).symm ≪≫ₗ
      Finsupp.domLCongr t.equivFin.symm
  let φ :
      (Fin t.card → Λ) →ₗ[Λ] (Fin n → Λ) :=
    Finsupp.linearCombination Λ generators ∘ₗ ψ.toLinearMap
  have hφ_range : LinearMap.range φ = K := by
    have hgenerators :
        LinearMap.range (Finsupp.linearCombination Λ generators) = K := by
      -- Proof comment: the generating family of the relation submodule is encoded by the chosen
      -- finite subset `t`.
      rw [Finsupp.range_linearCombination]
      simpa [generators, Subtype.range_coe_subtype] using ht
    rw [LinearMap.range_comp_of_range_eq_top _ ψ.range]
    exact hgenerators
  let gLinear : (Fin n → Λ) →ₗ[Λ] M :=
    e.symm.toLinearMap.comp K.mkQ
  have hg_ker : LinearMap.ker gLinear = K := by
    have heker : LinearMap.ker e.symm.toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.mpr e.symm.injective
    -- Proof comment: the quotient map contributes kernel `K`, and the final linear equivalence
    -- does not change kernels.
    change LinearMap.ker (e.symm.toLinearMap.comp K.mkQ) = K
    rw [LinearMap.ker_comp, heker, Submodule.comap_bot, Submodule.ker_mkQ]
  have hExact : Function.Exact φ gLinear := by
    -- Proof comment: exactness is exactly the range-kernel description of the chosen module
    -- presentation.
    rw [LinearMap.exact_iff, hφ_range, hg_ker]
  have hgSurj : Function.Surjective gLinear := by
    -- Proof comment: the quotient map is surjective, and composing with a linear equivalence
    -- preserves surjectivity.
    exact e.symm.surjective.comp (Submodule.mkQ_surjective K)
  exact ⟨t.card, n, ModuleCat.ofHom φ, ModuleCat.ofHom gLinear, hExact, hgSurj⟩

/-- Helper for Lemma 18.42.5: a surjective module homomorphism induces a surjective map on
sections of the associated constant module sheaves. -/
private lemma constantModuleForgetSectionsNaturality
    {A B : ModuleCat.{w} Λ} (u : A ⟶ B) (U : C)
    (x : (((constantSheaf J (ModuleCat.{w} Λ)).obj A).obj.obj (op U))) :
    let E := constantCommuteCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
    let eA := ((sheafToPresheaf J AddCommGrpCat.{w}).mapIso (E.app A)).app (op U)
    let eB := ((sheafToPresheaf J AddCommGrpCat.{w}).mapIso (E.app B)).app (op U)
    eB.hom ((((constantSheaf J (ModuleCat.{w} Λ)).map u).hom.app (op U)) x) =
      (((constantSheaf J AddCommGrpCat.{w}).map
          ((forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map u)).hom.app (op U))
        (eA.hom x) := by
  let E := constantCommuteCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})
  let eA := ((sheafToPresheaf J AddCommGrpCat.{w}).mapIso (E.app A)).app (op U)
  let eB := ((sheafToPresheaf J AddCommGrpCat.{w}).mapIso (E.app B)).app (op U)
  -- Proof comment: evaluate the naturality square of `constantCommuteCompose` at `U`.
  have hnat :
      ((((constantSheaf J (ModuleCat.{w} Λ) ⋙
          sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).map u) ≫
          (E.hom.app B)).hom.app (op U)) =
        (((E.hom.app A) ≫
          ((forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) ⋙
            constantSheaf J AddCommGrpCat.{w}).map
              ((forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}).map u)).hom.app (op U)) := by
    exact
      congrArg
        (fun α :
          ((constantSheaf J (ModuleCat.{w} Λ) ⋙
              sheafCompose J (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})).obj A) ⟶
            ((forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w} ⋙
                constantSheaf J AddCommGrpCat.{w}).obj B) =>
          α.hom.app (op U))
        (E.hom.naturality u)
  simpa [E, eA, eB] using ConcreteCategory.congr_hom hnat x

/-- Helper for Lemma 18.42.5: a surjective module homomorphism induces a surjective map on
sections of the associated constant module sheaves. -/
private lemma constantModuleSheafAppSurjective
    {A B : ModuleCat.{w} Λ} (u : A ⟶ B)
    (hu : Function.Surjective u.hom) (U : C) :
    Function.Surjective (((constantSheaf J (ModuleCat.{w} Λ)).map u).hom.app (op U)) := by
  classical
  let F := forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}
  let S : ShortComplex AddCommGrpCat.{w} :=
    ShortComplex.mk (0 : (0 : AddCommGrpCat.{w}) ⟶ F.obj A) (F.map u) (by simp)
  let E := constantCommuteCompose J F
  let eA := ((sheafToPresheaf J AddCommGrpCat.{w}).mapIso (E.app A)).app (op U)
  let eB := ((sheafToPresheaf J AddCommGrpCat.{w}).mapIso (E.app B)).app (op U)
  let s : S.X₃ → S.X₂ := fun b ↦ Classical.choose (hu b)
  have hs : Function.RightInverse s S.g.hom := by
    intro b
    exact Classical.choose_spec (hu b)
  have hAddSurj :
      Function.Surjective
        ((((S.map (constantSheaf J AddCommGrpCat.{w})).map
            (sheafToPresheaf J AddCommGrpCat.{w})).map
            ((evaluation Cᵒᵖ AddCommGrpCat.{w}).obj (op U))).g).hom :=
    constant_abelian_sheaf_app_surjective (J := J) S s hs U
  intro y
  obtain ⟨x', hx'⟩ := hAddSurj (eB.hom y)
  refine ⟨eA.inv x', ?_⟩
  have heB :
      Function.LeftInverse eB.inv eB.hom := by
    intro z
    exact CategoryTheory.hom_inv_id_apply eB z
  apply heB.injective
  -- Proof comment: transport sectionwise surjectivity back across the forgetful comparison.
  have hnat :=
    constantModuleForgetSectionsNaturality
      (J := J) (Λ := Λ) u U (eA.inv x')
  calc
    eB.hom ((((constantSheaf J (ModuleCat.{w} Λ)).map u).hom.app (op U)) (eA.inv x')) =
        (((constantSheaf J AddCommGrpCat.{w}).map (F.map u)).hom.app (op U))
          (eA.hom (eA.inv x')) := hnat
    _ = (((constantSheaf J AddCommGrpCat.{w}).map (F.map u)).hom.app (op U)) x' := by
      rw [CategoryTheory.hom_inv_id_apply eA x']
    _ = eB.hom y := hx'

/-- Helper for Lemma 18.42.5: a surjective module map yields an epimorphism after passing to the
constant sheaf view in `SheafOfModules`. -/
private theorem constantModuleSheafMap_epi_of_surjective
    {M N : ModuleCat.{w} Λ} (f : M ⟶ N) (hf : Function.Surjective f.hom) :
    Epi (Sheaf.constantModuleSheafMap (J := J) (Λ := Λ) f) := by
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  letI : Presheaf.IsLocallyInjective J α := (J.W_toSheafify _).isLocallyInjective
  letI : Presheaf.IsLocallySurjective J α := (J.W_toSheafify _).isLocallySurjective
  let p :
      Sheaf.toConstantModulePresheaf ((constantSheaf J (ModuleCat.{w} Λ)).obj M) ⟶
        Sheaf.toConstantModulePresheaf ((constantSheaf J (ModuleCat.{w} Λ)).obj N) :=
    Sheaf.toConstantModulePresheafHom (Λ := Λ)
      ((constantSheaf J (ModuleCat.{w} Λ)).map f)
  have hp_surj : ∀ ⦃X : Cᵒᵖ⦄, Function.Surjective (p.app X) := by
    intro X
    -- Proof comment: the presheaf-level map is the original constant-sheaf map on sections.
    simpa [p, Sheaf.toConstantModulePresheafHom] using
      constantModuleSheafAppSurjective (J := J) (Λ := Λ) f hf X.unop
  letI : Epi p := PresheafOfModules.epi_of_surjective hp_surj
  have hmap : Epi ((PresheafOfModules.sheafification α).map p) := by
    infer_instance
  -- Proof comment: `constantModuleSheafMap` is exactly the sheafification of the presheaf-level
  -- map, so epimorphy is preserved by the sheafification functor.
  simpa [Sheaf.constantModuleSheafMap, Sheaf.toConstantModuleSheafMap, p, α] using hmap

/-- Helper for Lemma 18.42.5: on the slice site over `U`, global sections of a
`\underline{\Lambda}`-module sheaf are recovered by evaluation at the terminal object
`U ⟶ U`. -/
private noncomputable def overSectionsEquivEvaluation
    {U : C}
    (M : SheafOfModules
      (((constantSheaf J RingCat.{w}).obj (RingCat.of Λ)).over U)) :
    M.sections ≃ M.val.obj (op (Over.mk (𝟙 U))) where
  toFun s := s.1 (op (Over.mk (𝟙 U)))
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
    -- Proof comment: a slice-site section is determined by its restrictions from the terminal
    -- object.
    ext W
    simpa using PresheafOfModules.sections_property s ((Over.mkIdTerminal.from W.unop).op)
  right_inv m := by
    -- Proof comment: the reconstructed section evaluates back to the chosen terminal value.
    change M.val.map ((Over.mkIdTerminal.from (Over.mk (𝟙 U))).op) m = m
    have h :
        Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 (Over.mk (𝟙 U)) :=
      Over.mkIdTerminal.hom_ext _ _
    simpa using M.val.congr_map_apply (congrArg Quiver.Hom.op h) m

/-- Helper for Lemma 18.42.5: on a slice site, `unitHomEquiv` is computed by evaluating the
corresponding unit morphism on the terminal section `1`. -/
private theorem unitHomEquiv_apply_terminal
    {U : C}
    (M : SheafOfModules
      (((constantSheaf J RingCat.{w}).obj (RingCat.of Λ)).over U))
    (φ : SheafOfModules.unit (((constantSheaf J RingCat.{w}).obj (RingCat.of Λ)).over U) ⟶ M) :
    (SheafOfModules.unitHomEquiv M φ).1 (op (Over.mk (𝟙 U))) =
      (φ.val.app (op (Over.mk (𝟙 U))))
        (show ((SheafOfModules.unit
            (((constantSheaf J RingCat.{w}).obj (RingCat.of Λ)).over U)).val.obj
            (op (Over.mk (𝟙 U)))) from
          (1 : (((constantSheaf J RingCat.{w}).obj (RingCat.of Λ)).over U).val.obj
            (op (Over.mk (𝟙 U))))) := by
  -- Proof comment: `unitHomEquiv` is defined by evaluating the unit morphism on the terminal
  -- section `1`.
  rfl

/-- Helper for Chap18 Lemma 18 42 5: the sieve on `U` generated by a slice-site family agrees
with the ambient sieve generated by the underlying arrows. -/
private theorem overSieveOfObjectsEqOfArrows
    {U : C} {I : Type*} (X : I → Over U) :
    (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects X (Over.mk (𝟙 U))) =
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) := by
  ext W g
  constructor
  · intro hg
    -- Proof comment: forgetting a factorization in the slice site gives the same factorization
    -- in the ambient site.
    rw [Sieve.overEquiv_iff] at hg
    rw [Sieve.mem_ofObjects_iff] at hg
    rcases hg with ⟨i, ⟨a⟩⟩
    rw [Sieve.mem_ofArrows_iff]
    exact ⟨i, a.left, by simpa using a.w.symm⟩
  · intro hg
    -- Proof comment: conversely, any ambient factorization lifts uniquely to a slice morphism.
    rw [Sieve.overEquiv_iff]
    rw [Sieve.mem_ofArrows_iff] at hg
    rcases hg with ⟨i, a, ha⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk a (by simpa using ha.symm)⟩⟩

/-- Helper for Chap18 Lemma 18 42 5: a cover of the terminal object in `J.over U` contains some
member whose source is not sheaf theoretically empty whenever `U` itself is not sheaf
theoretically empty. -/
private theorem overCover_hasNonemptyMember
    {U : C} {I : Type*} (X : I → Over U)
    (hX : (J.over U).CoversTop X)
    (hU : ¬ J.IsSheafTheoreticallyEmpty U) :
    ∃ i : I, ¬ J.IsSheafTheoreticallyEmpty (X i).left := by
  classical
  by_contra hEmpty
  push_neg at hEmpty
  have hX' :
      Sieve.ofArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom) ∈ J U := by
    have hXTerminal :
        Sieve.ofObjects X (Over.mk (𝟙 U)) ∈ (J.over U) (Over.mk (𝟙 U)) :=
      (GrothendieckTopology.coversTop_iff_of_isTerminal
        (J := J.over U) (X := Over.mk (𝟙 U)) (hX := Over.mkIdTerminal) X).1 hX
    rw [GrothendieckTopology.mem_over_iff, overSieveOfObjectsEqOfArrows] at hXTerminal
    exact hXTerminal
  have hBindBot :
      Presieve.bindOfArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom)
        (fun i ↦ (⊥ : Presieve (X i).left)) =
        (⊥ : Presieve U) := by
    funext W f
    apply propext
    constructor
    · intro hf
      cases hf with
      | mk i g hg =>
          exact hg
    · intro hf
      exact False.elim hf
  have hBot : (⊥ : Sieve U) ∈ J U := by
    have hBind :
        Sieve.generate
            (Presieve.bindOfArrows (fun i ↦ (X i).left) (fun i ↦ (X i).hom)
              (fun i ↦ (⊥ : Presieve (X i).left))) ∈ J U := by
      exact J.bindOfArrows hX' fun i ↦ by
        simpa [GrothendieckTopology.isSheafTheoreticallyEmpty_iff_bot_mem] using hEmpty i
    simpa [hBindBot] using hBind
  exact hU <| by
    rwa [GrothendieckTopology.isSheafTheoreticallyEmpty_iff_bot_mem] at hBot

-- Proof sketch: if `M` is finitely generated, its generators define global sections of the
-- constant sheaf that generate it locally, so `\underline M` is of finite type. Conversely,
-- choose an object of the site that is not sheaf theoretically empty; local finite generation on
-- that object comes from finitely many elements of `M`, and injectivity of restriction to a
-- nonempty object shows those elements already generate `M`.
/-- Lemma 18.42.5 (1): the constant sheaf `\underline M` of `\underline{\Lambda}`-modules is of
finite type if and only if the `\Lambda`-module `M` is finite, assuming the sheaf topos of the
site is not empty. -/
@[stacks 093N]
theorem isFiniteType_constantSheaf_iff_module_finite
    (M : ModuleCat.{w} Λ)
    (hne : ∃ U : C, ¬ J.IsSheafTheoreticallyEmpty U) :
    (((constantSheaf J (ModuleCat.{w} Λ)).obj M).toConstantModuleSheaf).IsFiniteType ↔
      Module.Finite Λ M := by
  constructor
  · intro hF
    -- Route correction: the right abstraction is to descend a finite local generating family on a
    -- non-sheaf-theoretically-empty chart back to finitely many elements of `M`.
    -- TODO: choose `U` from `hne`, refine the `IsFiniteType` witness on `U`, and compare
    -- `(((constantSheaf J _).obj M).toConstantModuleSheaf).over U` with a slice-site constant
    -- module sheaf strongly enough to turn owner-level generating sections into finitely many
    -- actual elements of `M`. The remaining blocker is the missing descent bridge from
    -- `SheafOfModules.IsFiniteGloballyGenerated` for the owner view back to generators of the
    -- underlying `ModuleCat` object on a non-sheaf-theoretically-empty chart.
    sorry
  · intro hM
    let _ : Module.Finite Λ M := hM
    obtain ⟨n, φ, hφ⟩ := finiteModuleExistsFiniteFreeSurjection (Λ := Λ) M
    -- TODO: use `Sheaf.constantModuleSheafMap φ` to transport the finite free surjection, then
    -- compare the source constant sheaf of `Fin n → Λ` with the canonical owner-level free sheaf
    -- over the constant ring sheaf. The remaining blocker is the missing comparison isomorphism
    -- between this constant free module sheaf and `SheafOfModules.free`, which is exactly the API
    -- needed to invoke the finite-type closure theorem `SheafOfModules.isFiniteType_of_epi`.
    sorry

-- Proof sketch: finite presentation of `\underline M` implies finite type by the first clause.
-- Choose a finite generating set of `M`, use the induced short exact sequence
-- `0 → K → Λ^{\oplus r} → M → 0`, pass to constant sheaves using exactness of the constant sheaf
-- functor, and apply the finite-presentation kernel criterion to conclude that `K` is finite.
-- The converse follows by sheafifying a finite presentation of `M`.
/-- Lemma 18.42.5 (2): the constant sheaf `\underline M` of `\underline{\Lambda}`-modules is
finitely presented if and only if the `\Lambda`-module `M` is finitely presented, assuming the
sheaf topos of the site is not empty. -/
@[stacks 093N]
theorem isFinitePresentation_constantSheaf_iff_module_finitePresentation
    (M : ModuleCat.{w} Λ)
    (hne : ∃ U : C, ¬ J.IsSheafTheoreticallyEmpty U) :
    (((constantSheaf J (ModuleCat.{w} Λ)).obj M).toConstantModuleSheaf).IsFinitePresentation ↔
      Module.FinitePresentation Λ M := by
  constructor
  · intro hF
    -- TODO: first derive `Module.Finite Λ M` from the finite-type half above, then choose a
    -- finite free cover of `M`, transport its exact sequence through `Sheaf.constantModuleSheafMap`,
    -- apply the owner-level kernel theorem, and descend finite generation of the relation module.
    -- This branch is blocked by the same descent bridge as part (1), now additionally needed for
    -- the kernel object coming from the transported finite free presentation.
    sorry
  · intro hM
    let _ : Module.FinitePresentation Λ M := hM
    obtain ⟨m, n, f, g, hExact, hg⟩ :=
      finitelyPresentedModuleExistsFiniteFreePresentation (Λ := Λ) M
    -- TODO: transport the finite free presentation along `constantSheaf` and
    -- `Sheaf.toConstantModuleSheafMap`, use finite presentation of the finite free owner-level
    -- source, and identify the resulting cokernel with the target constant module sheaf. The
    -- remaining blocker is again the missing constant-free comparison isomorphism, now needed for
    -- both source terms in the finite free presentation.
    sorry

end CategoryTheory
