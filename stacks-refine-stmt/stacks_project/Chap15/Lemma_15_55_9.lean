import stacks_project.Chap12.Definition_12_27_5
import stacks_project.Chap15.Lemma_15_55_7
import stacks_project.Chap15.Lemma_15_55_8

universe u

namespace CategoryTheory

noncomputable section

open ModuleCat

/- Domain-style sampling for Lemma 15.55.9:
- primary domain: the Chapter 15 construction of functorial injective embeddings in `ModuleCat R`
  from the explicit targets `J(M)`;
- sampled owner-level declarations:
  `jModule`,
  `CharacterModule.eval`,
  `CharacterModule.eval_injective`,
  `NatTrans.arrowFunctor`,
  `ModuleCat.restrictCoextendScalarsAdj`,
  `HasFunctorialInjectiveEmbeddings`;
- best owner abstraction:
  `source-facing`: the canonical natural transformation `𝟭 ⟶ jFunctor R` whose component at `M`
    is the explicit embedding `M ⟶ J(M)` into the module `jModule R M` of Lemma `15.55.8`;
  `core/canonical`: the Chapter 12 owner `HasFunctorialInjectiveEmbeddings (ModuleCat R)`;
  `bridge/view`: the induced Arrow-valued functor `(jEmbeddingNatTrans R).arrowFunctor` and the
    resulting `HasFunctorialInjectiveEmbeddings` instance;
- primitive data: the explicit target `jModule R M` and the canonical evaluation map
  `CharacterModule.eval`, transported through `restrictCoextendScalarsAdj (algebraMap ℤ R)`;
- derived API: objectwise injectivity of the map `M ⟶ J(M)`, the Arrow-valued view provided by
  `NatTrans.arrowFunctor`, and the induced
  `HasFunctorialInjectiveEmbeddings` instance.

This file is `source-facing`: Stacks Lemma `15.55.9` is about the specific construction
`M ↦ (M ⟶ J(M))`, not merely about existence of some functorial injective embeddings. The chapter
owner `HasFunctorialInjectiveEmbeddings` is therefore derived from the explicit natural
transformation `jEmbeddingNatTrans R` via the canonical bridge `NatTrans.arrowFunctor`, rather than
used as a replacement for the source construction. -/

variable (R : Type u) [Ring R]

namespace ModuleCat

open RestrictionCoextensionAdj.HomEquiv

private noncomputable def jEvaluate (M : ModuleCat.{u} R) :
    let _ : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    (restrictScalars (algebraMap ℤ R)).obj M ⟶
      ModuleCat.of ℤ (M^∨ → ULift.{u} (AddCircle (1 : ℚ))) :=
  by
    let _ : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    exact
      ModuleCat.ofHom
        { toFun := fun m χ ↦ ULift.up (χ m)
          map_add' := by
            sorry
          map_smul' := by
            sorry }

private noncomputable def jPrecompose {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    ModuleCat.of ℤ (M^∨ → ULift.{u} (AddCircle (1 : ℚ))) ⟶
      ModuleCat.of ℤ (N^∨ → ULift.{u} (AddCircle (1 : ℚ))) :=
  ModuleCat.ofHom
    { toFun := fun ψ χ ↦ ψ (((CharacterModule.functor R).map f.op) χ)
      map_add' := by
        intro ψ ψ'
        ext χ
        rfl
      map_smul' := by
        intro n ψ
        ext χ
        rfl }

/-- The textbook assignment `M ↦ J(M)` of Lemma `15.55.8`, made functorial by precomposition on
the character-module variable. -/
noncomputable def jFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  { obj := fun M ↦ jModule R M
    map {M N} f := (coextendScalars (algebraMap ℤ R)).map (jPrecompose R f)
    map_id M := by
      ext ψ
      rfl
    map_comp f g := by
      ext ψ
      rfl }

/-- The explicit embedding `M ⟶ J(M)` obtained from pointwise evaluation by the
restriction/coextension adjunction. -/
noncomputable def jEmbedding (M : ModuleCat.{u} R) : M ⟶ jModule R M :=
  fromRestriction (algebraMap ℤ R) (jEvaluate R M)

@[simp] theorem jEmbedding_apply_apply (M : ModuleCat.{u} R) (m : M) (r : R)
    (χ : M^∨) :
    jEmbedding R M m r χ = ULift.up (χ (r • m)) := by
  rw [jEmbedding, fromRestriction_hom_apply_apply]
  rfl

/-- The explicit embeddings `M ⟶ J(M)` assemble into a natural transformation
`𝟭 (ModuleCat R) ⟶ jFunctor R`. -/
noncomputable def jEmbeddingNatTrans : 𝟭 (ModuleCat.{u} R) ⟶ jFunctor R where
  app M := jEmbedding R M
  naturality {X} {Y} f := by
    sorry

/-- The textbook embedding `M ⟶ J(M)` is injective on underlying elements. -/
theorem jEmbedding_injective (M : ModuleCat.{u} R) :
    Function.Injective (jEmbedding R M) := by
  sorry

/-- Lemma 15.55.9, in the Chapter 12 owner language: the explicit Arrow-valued functor
`M ↦ (M ⟶ J(M))` determines functorial injective embeddings in `ModuleCat R`. -/
noncomputable instance :
    HasFunctorialInjectiveEmbeddings (ModuleCat.{u} R) where
  J := (jEmbeddingNatTrans R).arrowFunctor
  leftFunc_comp_J := NatTrans.arrowFunctor_leftFunc_comp _
  mono_obj M := by
    change Mono (jEmbedding R M)
    exact (ModuleCat.mono_iff_injective _).2 (jEmbedding_injective R M)
  injective_obj M := by
    change Injective (jModule R M)
    exact (Module.injective_iff_injective_object R (jModule R M)).1 (jModule_injective R M)

end ModuleCat

end

end CategoryTheory
