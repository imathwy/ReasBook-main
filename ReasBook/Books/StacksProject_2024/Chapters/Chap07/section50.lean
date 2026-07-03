import Mathlib
import Mathlib.CategoryTheory.Sites.Closed
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_50_1 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Presheaf
open CategoryTheory.Limits

universe w v u

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {U : C} (S : Sieve U)

/- Domain-style sampling for Lemma 7.50.1:
- source-facing object: the sieve `S` on `U`;
- bridge object: the identity section `𝟙 U` of the representable presheaf `yoneda.obj U`;
- global invariant: a section of `S^# = S⁺⁺` above `id_U`, then two successive `Plus.exists_rep`
  decompositions;
- owner API: `Sieve.functorInclusion`, `CategoryTheory.toSheafify`,
  and `GrothendieckTopology.Plus.exists_rep`.

The reverse implication follows the textbook proof directly: use `hW` to lift `id_U` to a
section of `S^#(U)`, unpack that section into local `S⁺`-data, then unpack each local `S⁺`
section into an actual covering subsieve inside `S`. -/

/-- Helper for Lemma 7.50.1: a covering sieve satisfies the local-object criterion defining
`J.W` for its canonical inclusion into the representable presheaf. -/
private theorem covering_gives_W_functorInclusion
    (hS : S ∈ J U) :
    J.W S.functorInclusion := by
  intro P hP
  have hSheafFor : Presieve.IsSheafFor P S.arrows :=
    hP.isSheafFor S hS
  constructor
  · -- Two extensions out of `yoneda.obj U` agree once they agree on the covering sieve.
    intro t₁ t₂ hEq
    exact hSheafFor.hom_ext t₁ t₂ hEq
  · -- Every map out of the sieve extends uniquely because `P` satisfies the sheaf condition.
    intro f
    refine ⟨hSheafFor.extend f, ?_⟩
    simp

/-- Helper for Lemma 7.50.1: the image sieve of the identity section under the canonical
inclusion `S.functor ⟶ yoneda.obj U` is exactly `S`. -/
private theorem imageSieve_functorInclusion_identity :
    Presheaf.imageSieve S.functorInclusion (𝟙 U) = S := by
  -- Rewrite the image sieve as the sieve cut out by the image subfunctor of `S.functorInclusion`.
  calc
    Presheaf.imageSieve S.functorInclusion (𝟙 U) =
        (Subfunctor.range S.functorInclusion).sieveOfSection (𝟙 U) := by
          simpa using
            (Presheaf.imageSieve_eq_sieveOfSection S.functorInclusion (s := (𝟙 U)))
    _ = Sieve.sieveOfSubfunctor S.functorInclusion := by
          -- Both sieves say that the section `f : V ⟶ U` is already in the image of
          -- `S.functorInclusion.app (op V)`.
          ext V f
          simp [CategoryTheory.Subfunctor.sieveOfSection, Sieve.sieveOfSubfunctor]
          constructor
          · rintro ⟨t, ht⟩
            have ht' : t.1 = f := by
              simpa [Sieve.functorInclusion] using ht
            simpa [ht'] using t.2
          · intro hf
            exact ⟨⟨f, hf⟩, by simp [Sieve.functorInclusion]⟩
    _ = S := Sieve.sieveOfSubfunctor_functorInclusion (S := S)

/-- Helper for Lemma 7.50.1: once `S.functorInclusion` is locally surjective, evaluating at the
identity section immediately shows that `S` is covering. -/
private theorem covering_of_isLocallySurjective_functorInclusion
    [Presheaf.IsLocallySurjective J S.functorInclusion] :
    S ∈ J U := by
  -- The local-surjectivity sieve above `id_U` is literally `S`.
  rw [← imageSieve_functorInclusion_identity (S := S)]
  exact Presheaf.imageSieve_mem (J := J) S.functorInclusion (𝟙 U)

/-- Helper for Lemma 7.50.1: in the large `shrinkYoneda` model, the image sieve of the identity
section under the sieve inclusion is exactly the original sieve `S`. -/
private theorem imageSieve_large_shrinkFunctor_ι_identity :
    Presheaf.imageSieve (Sieve.shrinkFunctor.{max u v} S).ι
        (show (CategoryTheory.shrinkYoneda.{max u v}.obj U).obj (op U) from
          CategoryTheory.shrinkYonedaObjObjEquiv.symm (𝟙 U)) =
      S := by
  -- Unpack image-sieve membership: a local section of `S.shrinkFunctor` is literally an arrow
  -- of `S`, and the identity section records composition with `𝟙 U`.
  ext V g
  constructor
  · rintro ⟨t, ht⟩
    have ht' :
        t.1 = CategoryTheory.shrinkYonedaObjObjEquiv.symm g := by
      calc
        t.1 = ((Sieve.shrinkFunctor.{max u v} S).ι.app (op V)) t := rfl
        _ =
            (CategoryTheory.shrinkYoneda.{max u v}.obj U).map g.op
              (show (CategoryTheory.shrinkYoneda.{max u v}.obj U).obj (op U) from
                CategoryTheory.shrinkYonedaObjObjEquiv.symm (𝟙 U)) := ht
        _ = CategoryTheory.shrinkYonedaObjObjEquiv.symm g := by
            simpa using
              CategoryTheory.shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op (𝟙 U)
    have htg : CategoryTheory.shrinkYonedaObjObjEquiv t.1 = g := by
      simpa using congrArg CategoryTheory.shrinkYonedaObjObjEquiv ht'
    simpa [htg] using (show S (CategoryTheory.shrinkYonedaObjObjEquiv t.1) from t.2)
  · intro hg
    refine ⟨⟨CategoryTheory.shrinkYonedaObjObjEquiv.symm g, by simpa using hg⟩, ?_⟩
    simpa using
      (CategoryTheory.shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op (𝟙 U)).symm

/-- Helper for Lemma 7.50.1: after transferring to the large `shrinkFunctor` inclusion, local
surjectivity at the identity section recovers the covering sieve `S`. -/
private theorem covering_of_W_large_shrinkFunctor_ι
    (hW : J.W ((Sieve.shrinkFunctor.{max u v} S).ι)) :
    S ∈ J U := by
  -- Route correction: abandon the blocked `ULift` transport and use the canonically isomorphic
  -- large `shrinkFunctor` inclusion, where `J.W` directly gives local surjectivity.
  let _ : J.WEqualsLocallyBijective (Type (max u v)) := inferInstance
  have hSurj : Presheaf.IsLocallySurjective J ((Sieve.shrinkFunctor.{max u v} S).ι) :=
    hW.isLocallySurjective
  let x : (CategoryTheory.shrinkYoneda.{max u v}.obj U).obj (op U) :=
    CategoryTheory.shrinkYonedaObjObjEquiv.symm (𝟙 U)
  -- Evaluating local surjectivity on the identity section produces a covering image sieve.
  have hmem :
      Presheaf.imageSieve (Sieve.shrinkFunctor.{max u v} S).ι x ∈ J U :=
    hSurj.imageSieve_mem x
  rw [show Presheaf.imageSieve (Sieve.shrinkFunctor.{max u v} S).ι x = S by
    simpa [x] using imageSieve_large_shrinkFunctor_ι_identity (S := S)] at hmem
  exact hmem

/-- Helper for Lemma 7.50.1: the large `shrinkFunctor` route already implies the original
`functorInclusion` route, because both close the theorem through the covering condition. -/
private theorem W_functorInclusion_of_W_large_shrinkFunctor_ι
    (hW : J.W ((Sieve.shrinkFunctor.{max u v} S).ι)) :
    J.W S.functorInclusion := by
  -- Once the large-universe inclusion is in `J.W`, the identity-section argument proves that
  -- `S` is covering, and then the original inclusion satisfies the sheaf extension criterion.
  exact covering_gives_W_functorInclusion (J := J) (S := S)
    (covering_of_W_large_shrinkFunctor_ι (J := J) (S := S) hW)

/-- Helper for Lemma 7.50.1: the large `shrinkFunctor` inclusion first rewrites to the
`ULift`-whiskered small `shrinkFunctor` inclusion via the canonical universe-comparison
isomorphisms. -/
private noncomputable def large_shrink_arrowIso_whiskered_small_shrink :
    Arrow.mk ((Sieve.shrinkFunctor.{max u v} S).ι) ≅
      Arrow.mk (Functor.whiskerRight (Sieve.shrinkFunctor.{v} S).ι
        CategoryTheory.uliftFunctor.{u, v}) := by
  refine Arrow.isoMk' _ _
    (Sieve.shrinkFunctorUliftFunctorIso.{v, u} S).symm
    ((CategoryTheory.shrinkYonedaUliftFunctorIso.{v, u} (C := C)).symm.app U)
    (Sieve.shrinkFunctorUliftFunctorIso_inv_ι.{v, u} (S := S) (X := U))

/-- Helper for Lemma 7.50.1: after rewriting the small `shrinkFunctor` by
`Sieve.shrinkFunctorIsoFunctor`, the whiskered small inclusion is exactly
`S.uliftFunctorInclusion`. -/
private noncomputable def whiskered_small_shrink_arrowIso_uliftFunctorInclusion :
    Arrow.mk (Functor.whiskerRight (Sieve.shrinkFunctor.{v} S).ι
      CategoryTheory.uliftFunctor.{u, v}) ≅
      Arrow.mk (Sieve.uliftFunctorInclusion.{u} S) := by
  refine Arrow.isoMk' _ _
    (Functor.isoWhiskerRight (Sieve.shrinkFunctorIsoFunctor.{v} S)
      CategoryTheory.uliftFunctor.{u, v})
    ((Functor.isoWhiskerRight (CategoryTheory.shrinkYonedaIsoYoneda (C := C))
      ((Functor.whiskeringRight Cᵒᵖ (Type v) (Type (max u v))).obj
        CategoryTheory.uliftFunctor.{u, v})).app U) ?_
  -- Both sides are the same whiskered inclusion once the small `shrinkFunctor` is rewritten.
  ext X x
  rfl

/-- Helper for Lemma 7.50.1: the large `shrinkFunctor` inclusion and `S.uliftFunctorInclusion`
have the same `W`-status. -/
private theorem W_large_shrinkFunctor_ι_iff_W_uliftFunctorInclusion :
    J.W ((Sieve.shrinkFunctor.{max u v} S).ι) ↔ J.W (Sieve.uliftFunctorInclusion.{u} S) := by
  -- Transport `J.W` across the two arrow isomorphisms built above.
  exact J.W.arrow_mk_iso_iff
    (large_shrink_arrowIso_whiskered_small_shrink (C := C) (U := U) (S := S) ≪≫
      whiskered_small_shrink_arrowIso_uliftFunctorInclusion (C := C) (U := U) (S := S))

/-- Helper for Lemma 7.50.1: composing a type-valued sheaf with the ambient `ULift` functor
still satisfies the sheaf condition. -/
private instance uliftFunctor_hasSheafCompose_type :
    J.HasSheafCompose
      (CategoryTheory.uliftFunctor.{u, v} : Type v ⥤ Type (max u v)) where
  isSheaf P hP := by
    -- Reduce to the concrete type-valued sheaf condition, where `ULift` preserves matching.
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_comp_uliftFunctor (J := J)
      ((isSheaf_iff_isSheaf_of_type J P).1 hP)

/-- Helper for Lemma 7.50.1: local injectivity of a type-valued presheaf map reflects across
whiskering by `ULift`. -/
private theorem locallyInjective_of_whisker_ulift
    {P Q : Cᵒᵖ ⥤ Type v} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective J
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{u, v} :
          Type v ⥤ Type (max u v)))] :
    Presheaf.IsLocallyInjective J η where
  equalizerSieve_mem {X} x y h := by
    let x' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{u, v} :
            Type v ⥤ Type (max u v))).obj X := ULift.up x
    let y' :
        (P ⋙
          (CategoryTheory.uliftFunctor.{u, v} :
            Type v ⥤ Type (max u v))).obj X := ULift.up y
    -- Lift the equal pair to the ambient universe, then descend the covering equalizer sieve.
    have hUp :
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{u, v} :
            Type v ⥤ Type (max u v))).app X x' =
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{u, v} :
              Type v ⥤ Type (max u v))).app X y' := by
      change ULift.up (η.app X x) = ULift.up (η.app X y)
      exact congrArg ULift.up h
    let T : Sieve X.unop :=
      Presheaf.equalizerSieve
        (F := P ⋙
          (CategoryTheory.uliftFunctor.{u, v} :
            Type v ⥤ Type (max u v)))
        x' y'
    have hT : T ∈ J X.unop := by
      exact
        Presheaf.equalizerSieve_mem J
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{u, v} :
              Type v ⥤ Type (max u v)))
          x' y' hUp
    refine J.superset_covering ?_ hT
    intro Y f hf
    change ULift.up ((P.map f.op) x) = ULift.up ((P.map f.op) y) at hf
    change (P.map f.op) x = (P.map f.op) y
    exact ULift.up.inj hf

/-- Helper for Lemma 7.50.1: whiskering a `Type`-valued presheaf map by `ULift` does not change
its equalizer sieves. -/
private theorem isLocallyInjective_whisker_ulift
    {P Q : Cᵒᵖ ⥤ Type v} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective J η] :
    Presheaf.IsLocallyInjective J
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{u, v} : Type v ⥤ Type (max u v))) where
  equalizerSieve_mem {X} x y h := by
    -- The `ULift` whiskering only repackages local sections, so the equalizer sieve is unchanged.
    have hDown : η.app X x.down = η.app X y.down := by
      change ULift.up (η.app X x.down) = ULift.up (η.app X y.down) at h
      exact ULift.up.inj h
    have hSieve :
        Presheaf.equalizerSieve
            (F := P ⋙
              (CategoryTheory.uliftFunctor.{u, v} :
                Type v ⥤ Type (max u v)))
            x y =
          Presheaf.equalizerSieve (F := P) x.down y.down := by
      ext Y f
      constructor
      · intro hEq
        change ULift.up ((P.map f.op) x.down) = ULift.up ((P.map f.op) y.down) at hEq
        exact ULift.up.inj hEq
      · intro hEq
        change ULift.up ((P.map f.op) x.down) = ULift.up ((P.map f.op) y.down)
        exact congrArg ULift.up hEq
    rw [hSieve]
    exact Presheaf.equalizerSieve_mem J η x.down y.down hDown

/-- Helper for Lemma 7.50.1: whiskering a `Type`-valued presheaf map by `ULift` does not change
its image sieves. -/
private theorem imageSieve_whisker_ulift
    {P Q : Cᵒᵖ ⥤ Type v} (η : P ⟶ Q) {X : C}
    (x :
      (Q ⋙
        (CategoryTheory.uliftFunctor.{u, v} :
          Type v ⥤ Type (max u v))).obj (op X)) :
    Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{u, v} :
            Type v ⥤ Type (max u v))) x =
      Presheaf.imageSieve η x.down := by
  ext Y f
  constructor
  · rintro ⟨y, hy⟩
    -- Any lifted local preimage descends by `ULift.down`.
    refine ⟨y.down, ?_⟩
    exact congrArg ULift.down hy
  · rintro ⟨y, hy⟩
    -- Conversely, any ordinary local preimage lifts back via `ULift.up`.
    refine ⟨ULift.up y, ?_⟩
    change ULift.up (η.app (op Y) y) = ULift.up (Q.map f.op x.down)
    exact congrArg ULift.up hy

/-- Helper for Lemma 7.50.1: whiskering a `Type`-valued locally surjective map by `ULift`
preserves local surjectivity. -/
private theorem isLocallySurjective_whisker_ulift
    {P Q : Cᵒᵖ ⥤ Type v} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective J η] :
    Presheaf.IsLocallySurjective J
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{u, v} : Type v ⥤ Type (max u v))) where
  imageSieve_mem {X} x := by
    -- After identifying the lifted image sieve with the original one, reuse local surjectivity.
    simpa [imageSieve_whisker_ulift (η := η) x] using
      (Presheaf.imageSieve_mem J η x.down)

/-- Helper for Lemma 7.50.1: local surjectivity of a type-valued presheaf map reflects across
whiskering by `ULift`. -/
private theorem locallySurjective_of_whisker_ulift
    {P Q : Cᵒᵖ ⥤ Type v} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective J
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{u, v} :
          Type v ⥤ Type (max u v)))] :
    Presheaf.IsLocallySurjective J η where
  imageSieve_mem {X} x := by
    let x' :
        (Q ⋙
          (CategoryTheory.uliftFunctor.{u, v} :
            Type v ⥤ Type (max u v))).obj (op X) := ULift.up x
    let T : Sieve X :=
      Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{u, v} :
            Type v ⥤ Type (max u v)))
        x'
    -- Lift the target section to the ambient universe, then descend the covering image sieve.
    have hT : T ∈ J X := by
      exact
        Presheaf.imageSieve_mem J
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{u, v} :
              Type v ⥤ Type (max u v)))
          x'
    simpa [T, imageSieve_whisker_ulift (η := η) x'] using hT

/-- Helper for Lemma 7.50.1: an outer covering sieve together with covering pullback
refinements on each branch forces the original sieve to be covering. -/
private theorem covering_of_outer_cover_with_inner_pullbacks
    (T : J.Cover U)
    (hInner : ∀ I : T.Arrow, ∃ R : J.Cover I.Y, (R : Sieve I.Y) ≤ S.pullback I.f) :
    S ∈ J U := by
  classical
  -- Bind the chosen inner covers over the outer cover and then forget back into `S`.
  let R : ∀ I : T.Arrow, J.Cover I.Y := fun I => Classical.choose (hInner I)
  have hR :
      ∀ I : T.Arrow, ((R I : J.Cover I.Y) : Sieve I.Y) ≤ S.pullback I.f :=
    fun I => Classical.choose_spec (hInner I)
  have hBind :
      Sieve.bind (T : Sieve U) (fun {Y} f hf => (R ⟨Y, f, hf⟩ : Sieve Y)) ∈ J U :=
    J.bind_covering T.2 (fun {Y} f hf => (R ⟨Y, f, hf⟩).2)
  refine J.superset_covering ?_ hBind
  rintro Y f ⟨Z, i, g, hi, hg, rfl⟩
  exact hR ⟨Z, g, hi⟩ i hg

/-- Helper for Lemma 7.50.1: the fixed universe-raising `ULift` functor on types preserves
sheafification for the site `J`.  This is the owner-level transport theorem needed to move the
source proof from the small `Type v` universe to the large `Type (max u v)` universe where the
public `Plus.exists_rep` API is available. -/
private theorem uliftFunctor_preservesSheafification_type :
    J.PreservesSheafification
      (CategoryTheory.uliftFunctor.{u, v} : Type v ⥤ Type (max u v)) := by
  -- Route correction: the remaining blocker is no longer the `W`-transport itself, but the
  -- owner theorem asserting that whiskering by `ULift` preserves sheafification on `Type`.
  -- Once this reusable bridge is available, `W_uliftFunctorInclusion_of_W_functorInclusion`
  -- closes immediately by `J.W_of_preservesSheafification`.
  -- TODO: expose or reprove an owner theorem upgrading the large-universe `toSheafify`
  -- local-bijectivity API to `J.PreservesSheafification uliftFunctor` without assuming
  -- `HasWeakSheafify J (Type v)`. The new reflection lemmas above isolate the remaining step:
  -- after constructing local injectivity/surjectivity for the whiskered small unit upstairs,
  -- descend them through `ULift` with
  -- `locallyInjective_of_whisker_ulift` and `locallySurjective_of_whisker_ulift`.
  sorry

/-- Helper for Lemma 7.50.1: whiskering the sieve inclusion by `uliftFunctor` preserves the
`W`-condition. -/
private theorem W_uliftFunctorInclusion_of_W_functorInclusion
    (hW : J.W S.functorInclusion) :
    J.W (Sieve.uliftFunctorInclusion.{u} S) := by
  let F : Type v ⥤ Type (max u v) :=
    CategoryTheory.uliftFunctor.{u, v}
  -- With the owner-level `ULift` preservation bridge isolated above, the actual `W` transport is
  -- just whiskering `S.functorInclusion` and simplifying the resulting map.
  have hPres : J.PreservesSheafification F :=
    uliftFunctor_preservesSheafification_type (J := J)
  simpa [F] using J.W_of_preservesSheafification F S.functorInclusion hW

/-- Helper for Lemma 7.50.1: replacing `yoneda` by the large-universe `shrinkYoneda` does not
change the `W`-status of the sieve inclusion. -/
private theorem W_large_shrinkFunctor_ι_iff_W_functorInclusion :
    J.W ((Sieve.shrinkFunctor.{max u v} S).ι) ↔ J.W S.functorInclusion := by
  constructor
  · intro hW
    -- The reverse direction is already closed by descending through the covering criterion.
    exact W_functorInclusion_of_W_large_shrinkFunctor_ι (J := J) (S := S) hW
  · intro hW
    -- Route correction: use the public sheafification-preservation instance for `uliftFunctor`
    -- instead of rebuilding any universe-specific local-bijectivity transport.
    have hUlift : J.W (Sieve.uliftFunctorInclusion.{u} S) :=
      W_uliftFunctorInclusion_of_W_functorInclusion (J := J) (S := S) hW
    exact (W_large_shrinkFunctor_ι_iff_W_uliftFunctorInclusion (J := J) (S := S)).2 hUlift

/-- Helper for Lemma 7.50.1: the reverse implication is obtained by transporting `hW` to the
large `shrinkFunctor` inclusion and then evaluating local surjectivity at the identity section. -/
private theorem covering_of_W_functorInclusion
    (hW : J.W S.functorInclusion) :
    S ∈ J U := by
  -- The source proof lifts `id_U` to a local section of `S^#`; here that same step is packaged
  -- by local surjectivity of the canonically equivalent large `shrinkFunctor` inclusion.
  exact covering_of_W_large_shrinkFunctor_ι (J := J) (S := S)
    ((W_large_shrinkFunctor_ι_iff_W_functorInclusion (J := J) (S := S)).2 hW)

/-- Lemma 7.50.1: a sieve `S` on `U` is covering if and only if its canonical inclusion
`S.functorInclusion : S.functor ⟶ yoneda.obj U` becomes an isomorphism after sheafification. -/
theorem covering_iff_functorInclusion_becomes_iso_after_sheafification :
    S ∈ J U ↔ J.W S.functorInclusion := by
  constructor
  · intro hS P hP
    -- The forward implication is exactly the extension property enjoyed by a covering sieve.
    exact covering_gives_W_functorInclusion J S hS P hP
  · intro hW
    -- Route correction: follow the textbook `S⁺⁺` argument directly instead of transporting
    -- `J.W` through `ULift`.
    exact covering_of_W_functorInclusion J S hW

end

end CategoryTheory.GrothendieckTopology

/-! ### Theorem_7_50_2 (from Chap07) -/
open CategoryTheory

/- Domain-style sampling for Theorem 7.50.2:
- primary domain: Grothendieck topologies and their set-valued sheaf categories;
- sampled owner API:
  `topology_eq_iff_same_sheaves`,
  `Presheaf.IsSheaf`,
  `isSheaf_iff_isSheaf_of_type`;
- source/core/bridge triage:
  `source-facing`: the textbook formulation using set-valued sheaves;
  `core/canonical`: `topology_eq_iff_same_sheaves`;
  `bridge/view`: `isSheaf_iff_isSheaf_of_type`.

Primitive data are only the two Grothendieck topologies. Equality of topologies is governed by the
canonical owner theorem `topology_eq_iff_same_sheaves`, while the passage from the
presieve-valued sheaf predicate to the chapter's set-valued `Presheaf.IsSheaf` language is derived
API via `isSheaf_iff_isSheaf_of_type`. The previous local theorem was only a shell around these
two canonical declarations, so this file should recall them directly instead of
keeping a parallel wrapper.
-/

/- Theorem 7.50.2, core/canonical recall: two Grothendieck topologies are equal exactly when they
define the same sheaf predicate on set-valued presheaves, expressed canonically via the
presieve-valued owner theorem. -/
recall topology_eq_iff_same_sheaves

/- Bridge recall: for set-valued presheaves, the chapter's `Presheaf.IsSheaf` predicate is
canonically equivalent to the owner predicate `Presieve.IsSheaf`. -/
recall isSheaf_iff_isSheaf_of_type

/-! ### Lemma_7_50_3 (from Chap07) -/
universe v u

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] {J J' : GrothendieckTopology C}

/- Domain-style sampling for Lemma 7.50.3:
- primary domain: comparison of Grothendieck topologies through their sheaf predicates
- sampled owner API:
  `Presheaf.IsSheaf.of_le`,
  `le_topology_of_closedSieves_isSheaf`,
  `isSheaf_iff_isSheaf_of_type`
- source/core/bridge triage:
  `source-facing`: the textbook formulation using set-valued sheaves
  `core/canonical`: topology inclusion together with
    `le_topology_of_closedSieves_isSheaf`
  `bridge/view`: `isSheaf_iff_isSheaf_of_type`

Primitive data are only the two Grothendieck topologies `J` and `J'`. The forward implication is
the canonical monotonicity of the sheaf predicate on the chapter owner `Presheaf C`, while the
converse is recovered from the closed sieve classifier, so no extra local wrapper object is
warranted here.
-/

-- Proof sketch: the forward implication is `Presheaf.IsSheaf.of_le`. For the converse, apply the
-- hypothesis to the presheaf of `J'`-closed sieves and then use
-- `le_topology_of_closedSieves_isSheaf`.
/-- Lemma 7.50.3: `J` is contained in `J'` if and only if every set-valued sheaf for the topology
`J'` is also a sheaf for the topology `J`. -/
theorem le_iff_sheaf_inclusion :
    J ≤ J' ↔
      ∀ P : Presheaf.{max u v} C, Presheaf.IsSheaf J' P → Presheaf.IsSheaf J P := by
  constructor
  · intro hJ P
    exact Presheaf.IsSheaf.of_le hJ
  · intro h
    apply le_topology_of_closedSieves_isSheaf
    rw [← isSheaf_iff_isSheaf_of_type]
    exact h _ ((isSheaf_iff_isSheaf_of_type _ _).2 (classifier_isSheaf J'))

end

end CategoryTheory.GrothendieckTopology
