import stacks_proof.stacks_project.Chap12.Definition_12_27_5
import stacks_proof.stacks_project.Chap15.Lemma_15_55_7
import stacks_proof.stacks_project.Chap15.Lemma_15_55_8
import Mathlib.Tactic.StacksAttribute

universe u v

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

/-- Helper for Lemma 15.55.9: pointwise evaluation is additive as a map into the function
module on the character module. -/
private theorem jEvaluate_map_add (M : ModuleCat.{max u v} R) [Module ℤ M] (m m' : M) :
    (fun χ : M^∨ ↦ ULift.up (χ (m + m'))) =
      (fun χ : M^∨ ↦ ULift.up (χ m)) + fun χ : M^∨ ↦ ULift.up (χ m') := by
  -- Check additivity pointwise on each character.
  funext (χ : M^∨)
  simpa only [Pi.add_apply] using congrArg ULift.up (map_add χ m m')

/-- Helper for Lemma 15.55.9: pointwise evaluation is `ℤ`-linear on the restricted-scalars
module. -/
private theorem jEvaluate_map_smul (M : ModuleCat.{max u v} R) (n : ℤ) (m : M) :
    (fun χ : M^∨ ↦ ULift.up (χ ((algebraMap ℤ R n) • m))) =
      (RingHom.id ℤ) n • fun χ : M^∨ ↦ ULift.up (χ m) := by
  -- After rewriting the restricted `ℤ`-action as ordinary `zsmul`, each character preserves the
  -- scalar action pointwise.
  funext (χ : M^∨)
  have hχ : χ ((algebraMap ℤ R n) • m) = n • χ m := by
    have hm : ((algebraMap ℤ R n) • m : M) = n • m := by
      simpa using int_smul_eq_zsmul (Module.compHom M (algebraMap ℤ R)) n m
    rw [hm]
    exact map_zsmul χ n m
  change ULift.up (χ ((algebraMap ℤ R n) • m)) = ULift.up (n • χ m)
  exact congrArg ULift.up hχ

private noncomputable def jEvaluate (M : ModuleCat.{max u v} R) :
    let _ : Module ℤ M := Module.compHom M (algebraMap ℤ R)
    (restrictScalars (algebraMap ℤ R)).obj M ⟶
      ModuleCat.of ℤ (M^∨ → ULift.{max u v} (AddCircle (1 : ℚ))) :=
  let _ : Module ℤ M := Module.compHom M (algebraMap ℤ R)
  ModuleCat.ofHom
    { toFun := fun m χ ↦ ULift.up (χ m)
      map_add' := fun m m' ↦ jEvaluate_map_add (R := R) M m m'
      map_smul' := fun n m ↦ jEvaluate_map_smul (R := R) M n m }

private noncomputable def jPrecompose {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    ModuleCat.of ℤ (M^∨ → ULift.{max u v} (AddCircle (1 : ℚ))) ⟶
      ModuleCat.of ℤ (N^∨ → ULift.{max u v} (AddCircle (1 : ℚ))) :=
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
noncomputable def jFunctor : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
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
noncomputable def jEmbedding (M : ModuleCat.{max u v} R) : M ⟶ jModule R M :=
  fromRestriction (algebraMap ℤ R) (jEvaluate R M)

@[simp] theorem jEmbedding_apply_apply (M : ModuleCat.{max u v} R) (m : M) (r : R)
    (χ : M^∨) :
    jEmbedding R M m r χ = ULift.up (χ (r • m)) := by
  -- Evaluate the adjoint transpose with the standard pointwise formula for `fromRestriction`.
  have h :=
    fromRestriction_hom_apply_apply (f := algebraMap ℤ R) (g := jEvaluate R M) m r
  -- The codomain of `jEvaluate` is itself a function module, so evaluate the adjunction formula
  -- once more on the chosen character.
  simpa [jEmbedding, jEvaluate] using congrArg (fun ψ ↦ ψ χ) h

/-- Helper for Lemma 15.55.9: the explicit embeddings commute with module maps after transporting
characters by precomposition. -/
private theorem jEmbedding_naturality {X Y : ModuleCat.{max u v} R} (f : X ⟶ Y) :
    f ≫ jEmbedding R Y = jEmbedding R X ≫ (jFunctor R).map f := by
  -- Compare both sides first on a module element, then pointwise in the target function module.
  ext m
  change jEmbedding R Y (f m) =
    (ConcreteCategory.hom ((jFunctor R).map f)) (jEmbedding R X m)
  apply LinearMap.ext
  intro r
  apply funext
  intro χ
  change jEmbedding R Y (f m) r χ =
    (((coextendScalars (algebraMap ℤ R)).map (jPrecompose R f)) (jEmbedding R X m) r) χ
  rw [jEmbedding_apply_apply, CoextendScalars.map_apply]
  -- Route correction: keep the source adjunction route and only unfold the functorial
  -- precomposition on characters at the final pointwise comparison.
  change ULift.up (χ (r • f m)) =
    (((jEmbedding R X m) r) (((CharacterModule.functor R).map f.op) χ))
  rw [jEmbedding_apply_apply]
  -- The character-module functor acts by precomposition with `f`, and linearity moves the scalar
  -- through `f`.
  simp only [CharacterModule.functor]
  change ULift.up (χ (r • (ConcreteCategory.hom f) m)) =
    ULift.up (χ ((ConcreteCategory.hom f) (r • m)))
  exact congrArg ULift.up (congrArg χ ((ConcreteCategory.hom f).map_smul r m).symm)

/-- Helper for Lemma 15.55.9: evaluating the explicit embedding at `1` recovers the canonical
double-character evaluation map. -/
@[simp] private theorem jEmbedding_apply_one_down_eq_eval_apply (M : ModuleCat.{max u v} R)
    (m : M) (χ : M^∨) :
    ULift.down (jEmbedding R M m (1 : R) χ) = (CharacterModule.eval R m) χ := by
  -- Specializing the scalar parameter to `1` removes the extra `R`-action in the formula.
  simpa [CharacterModule.eval_apply] using
    congrArg ULift.down (jEmbedding_apply_apply (R := R) M m (1 : R) χ)

/-- The explicit embeddings `M ⟶ J(M)` assemble into a natural transformation
`𝟭 (ModuleCat R) ⟶ jFunctor R`. -/
noncomputable def jEmbeddingNatTrans : 𝟭 (ModuleCat.{max u v} R) ⟶ jFunctor R where
  app M := jEmbedding R M
  naturality := fun {_ _} f ↦ jEmbedding_naturality (R := R) f

/-- The textbook embedding `M ⟶ J(M)` is injective on underlying elements. -/
theorem jEmbedding_injective (M : ModuleCat.{max u v} R) :
    Function.Injective (jEmbedding R M) := by
  intro m m' h
  -- Compare the explicit embedding with the canonical evaluation map at the scalar `1`.
  have hEval : CharacterModule.eval R m = CharacterModule.eval R m' := by
    ext χ
    have hχ := congrArg (fun ψ : jModule R M ↦ ULift.down ((ψ (1 : R)) χ)) h
    change
      ULift.down (jEmbedding R M m (1 : R) χ) =
        ULift.down (jEmbedding R M m' (1 : R) χ) at hχ
    rw [jEmbedding_apply_one_down_eq_eval_apply (R := R) M m χ,
      jEmbedding_apply_one_down_eq_eval_apply (R := R) M m' χ] at hχ
    exact hχ
  exact (CharacterModule.eval_injective (R := R) (M := M)) hEval

/-- Helper for Lemma 15.55.9: the explicit embedding is a monomorphism in `ModuleCat R`. -/
private theorem jEmbedding_mono (M : ModuleCat.{max u v} R) :
    Mono (jEmbedding R M) :=
  (ModuleCat.mono_iff_injective _).2 (jEmbedding_injective R M)

/-- Helper for Lemma 15.55.9: the explicit target `J(M)` is injective as an object of
`ModuleCat R`. -/
private theorem jModule_injective_object (M : ModuleCat.{max u v} R) :
    Injective (jModule R M) :=
  (Module.injective_iff_injective_object R (jModule R M)).1 (jModule_injective R M)

/-- Helper for Lemma 15.55.9: the Arrow-valued functor built from `jEmbeddingNatTrans` is objectwise
mono on its chosen embedding map. -/
private theorem jEmbeddingNatTrans_arrow_mono (M : ModuleCat.{max u v} R) :
    Mono (((jEmbeddingNatTrans R).arrowFunctor.obj M).hom) := by
  -- The Arrow object at `M` is definitionally the map `jEmbedding R M`.
  simpa [NatTrans.arrowFunctor, jEmbeddingNatTrans] using jEmbedding_mono (R := R) M

/-- Helper for Lemma 15.55.9: the Arrow-valued functor built from `jEmbeddingNatTrans` has
injective target object at each module. -/
private theorem jEmbeddingNatTrans_arrow_injective (M : ModuleCat.{max u v} R) :
    Injective (((jEmbeddingNatTrans R).arrowFunctor.obj M).right) := by
  -- The Arrow target at `M` is definitionally `jModule R M`.
  simpa [NatTrans.arrowFunctor, jEmbeddingNatTrans, jFunctor] using
    jModule_injective_object (R := R) M

/-- Lemma 15.55.9, in the Chapter 12 owner language: the explicit Arrow-valued functor
`M ↦ (M ⟶ J(M))` determines functorial injective embeddings in `ModuleCat R`. -/
@[stacks 01DD]
noncomputable instance :
    HasFunctorialInjectiveEmbeddings (ModuleCat.{max u v} R) where
  J := (jEmbeddingNatTrans R).arrowFunctor
  leftFunc_comp_J := NatTrans.arrowFunctor_leftFunc_comp _
  mono_obj := jEmbeddingNatTrans_arrow_mono (R := R)
  injective_obj := jEmbeddingNatTrans_arrow_injective (R := R)

end ModuleCat

end

end CategoryTheory
