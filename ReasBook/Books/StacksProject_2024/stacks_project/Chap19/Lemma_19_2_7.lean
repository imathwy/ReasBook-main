import Mathlib
import StacksProject_2024.stacks_project.Chap19.«19_2_6_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped DirectSum

universe u

/- Domain-style sampling for Lemma 19.2.7:
- primary domain: functoriality of pushouts and commutative squares in `ModuleCat R`;
- sampled owner API:
  `CategoryTheory.CommSq`,
  `pushout.map`,
  `baerModuleStep_square_commutes`,
  `𝐌(M)`,
  `𝟭 (ModuleCat R) ⟶ baerModuleStepFunctor R`;
- best owner abstraction: the natural transformation from the identity functor to the Baer
  one-step functor `M ↦ 𝐌(M)`, with source-facing square statements expressed as `CommSq`;
- primitive data: the Baer pushout span, its induced pushout maps, and the functorial
  `pushout.map`;
- derived API: the naturality squares and the resulting natural transformation.

Source/core/bridge triage:
- `source-facing`: the functoriality square for `M ⟶ \mathbf{M}(M)` and the extension square for
  ideal maps;
- `core/canonical`: `CommSq` for commuting squares and the natural transformation
  `𝟭 (ModuleCat R) ⟶ baerModuleStepFunctor R`;
- `bridge/view`: the explicit Baer pushout maps whose commutativity witnesses are packaged by
  those owner abstractions. -/

section

variable (R : Type u) [Ring R]

/-- The map on Baer indices induced by an `R`-linear map of modules. -/
private abbrev baerModuleIndexMap {M N : ModuleCat R} (f : M ⟶ N) :
    baerModuleIndex R M → baerModuleIndex R N :=
  fun j ↦ ⟨j.1, f.hom.comp j.2⟩

/-- The map on the direct sum of ideals induced by an `R`-linear map of modules. -/
private noncomputable abbrev baerModuleIdealDirectSumMap {M N : ModuleCat R} (f : M ⟶ N) :
    baerModuleIdealDirectSum R M ⟶ baerModuleIdealDirectSum R N :=
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  let _ : DecidableEq (baerModuleIndex R N) := Classical.decEq _
  ModuleCat.ofHom <|
    DirectSum.toModule R (baerModuleIndex R M)
      (⨁ j : baerModuleIndex R N, j.1)
      (fun j ↦
        DirectSum.lof R (baerModuleIndex R N) (fun j ↦ j.1)
          (baerModuleIndexMap R f j))

/-- The map on the direct sum of copies of `R` induced by an `R`-linear map of modules. -/
private noncomputable abbrev baerModuleRingDirectSumMap {M N : ModuleCat R} (f : M ⟶ N) :
    baerModuleRingDirectSum R M ⟶ baerModuleRingDirectSum R N :=
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  let _ : DecidableEq (baerModuleIndex R N) := Classical.decEq _
  ModuleCat.ofHom <|
    DirectSum.toModule R (baerModuleIndex R M)
      (⨁ _j : baerModuleIndex R N, R)
      (fun j ↦
        DirectSum.lof R (baerModuleIndex R N) (fun _j ↦ R)
          (baerModuleIndexMap R f j))

/-- Helper for Lemma 19.2.7: the canonical coprojection of the ideal summand indexed by `j` into
the source direct sum. -/
private noncomputable abbrev baerModuleIdealSummandIn (M : ModuleCat R) (j : baerModuleIndex R M) :
    ModuleCat.of R j.1 ⟶ baerModuleIdealDirectSum R M :=
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  ModuleCat.ofHom (DirectSum.lof R (baerModuleIndex R M) (fun i ↦ i.1) j)

/-- Helper for Lemma 19.2.7: the canonical coprojection of the `R`-summand indexed by `j` into the
target ring direct sum. -/
private noncomputable abbrev baerModuleRingSummandIn (M : ModuleCat R) (j : baerModuleIndex R M) :
    ModuleCat.of R R ⟶ baerModuleRingDirectSum R M :=
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  ModuleCat.ofHom (DirectSum.lof R (baerModuleIndex R M) (fun _ ↦ R) j)

/-- Helper for Lemma 19.2.7: the reindexing map on ideal direct sums sends each source coprojection
to the corresponding target coprojection. -/
private theorem baerModuleIdealDirectSumMap_comp_lof {M N : ModuleCat R} (f : M ⟶ N)
    (j : baerModuleIndex R M) :
    baerModuleIdealSummandIn R M j ≫ baerModuleIdealDirectSumMap R f =
      baerModuleIdealSummandIn R N (baerModuleIndexMap R f j) := by
  classical
  -- Route correction: first normalize the reindexing map on source coprojections so later
  -- naturality and functoriality proofs reduce to literal equalities on generators.
  refine ModuleCat.hom_ext ?_
  -- Evaluating on a generator of the `j`th ideal summand exposes the defining `DirectSum.toModule`.
  ext x i
  simp [baerModuleIdealSummandIn, baerModuleIdealDirectSumMap, baerModuleIndexMap]

/-- Helper for Lemma 19.2.7: the reindexing map on the `R`-summand direct sums sends each source
coprojection to the corresponding target coprojection. -/
private theorem baerModuleRingDirectSumMap_comp_lof {M N : ModuleCat R} (f : M ⟶ N)
    (j : baerModuleIndex R M) :
    baerModuleRingSummandIn R M j ≫ baerModuleRingDirectSumMap R f =
      baerModuleRingSummandIn R N (baerModuleIndexMap R f j) := by
  classical
  -- Evaluating on the chosen `R`-summand generator gives the defining target coprojection.
  refine ModuleCat.hom_ext ?_
  ext x i
  simp [baerModuleRingSummandIn, baerModuleRingDirectSumMap, baerModuleIndexMap]

/-- Helper for Lemma 19.2.7: precomposing the left vertical span map with a source coprojection
recovers the ideal inclusion into the corresponding `R`-summand. -/
private theorem baerModuleLeftVertical_comp_source_lof {M : ModuleCat R}
    (j : baerModuleIndex R M) :
    baerModuleIdealSummandIn R M j ≫ baerModuleLeftVertical R M =
      ModuleCat.ofHom j.1.subtype ≫ baerModuleRingSummandIn R M j := by
  classical
  -- The left span map is defined by the ideal inclusion followed by the target coprojection.
  refine ModuleCat.hom_ext ?_
  ext x i
  simp [baerModuleIdealSummandIn, baerModuleRingSummandIn, baerModuleLeftVertical]

/-- Helper for Lemma 19.2.7: precomposing the top span map with a source coprojection recovers the
indexed ideal map itself. -/
private theorem baerModuleTopMap_comp_source_lof {M : ModuleCat R} (j : baerModuleIndex R M) :
    baerModuleIdealSummandIn R M j ≫ baerModuleTopMap R M =
      ModuleCat.ofHom j.2 := by
  classical
  -- Evaluating on the `j`th source summand exposes the defining map `j.2`.
  refine ModuleCat.hom_ext ?_
  ext x
  simp [baerModuleIdealSummandIn, baerModuleTopMap]

/-- Helper for Lemma 19.2.7: reindexing along a composite map is the same as iterated
reindexing on Baer indices. -/
private theorem baerModuleIndexMap_comp {M N P : ModuleCat R} (f : M ⟶ N) (g : N ⟶ P)
    (j : baerModuleIndex R M) :
    baerModuleIndexMap R (f ≫ g) j = baerModuleIndexMap R g (baerModuleIndexMap R f j) := by
  -- The ideal is unchanged and the attached map is composed associatively.
  cases j
  rfl

/-- Helper for Lemma 19.2.7: the ideal coprojection indexed by a composite agrees with the
iterated reindexing coprojection. -/
private theorem baerModuleIdealSummandIn_indexMap_comp {M N P : ModuleCat R} (f : M ⟶ N)
    (g : N ⟶ P) (j : baerModuleIndex R M) :
    baerModuleIdealSummandIn R P (baerModuleIndexMap R (f ≫ g) j) =
      baerModuleIdealSummandIn R P (baerModuleIndexMap R g (baerModuleIndexMap R f j)) := by
  -- Consume the sigma-index equality before entering direct-sum extensionality.
  cases j
  rfl

/-- Helper for Lemma 19.2.7: the `R`-summand coprojection indexed by a composite agrees with the
iterated reindexing coprojection. -/
private theorem baerModuleRingSummandIn_indexMap_comp {M N P : ModuleCat R} (f : M ⟶ N)
    (g : N ⟶ P) (j : baerModuleIndex R M) :
    baerModuleRingSummandIn R P (baerModuleIndexMap R (f ≫ g) j) =
      baerModuleRingSummandIn R P (baerModuleIndexMap R g (baerModuleIndexMap R f j)) := by
  -- The ring-side summand index is transported by the same literal index equality.
  cases j
  rfl

/-- Helper for Lemma 19.2.7: maps out of the ideal direct sum are determined by their values on
the canonical source summands. -/
private theorem baerModuleIdealSummandIn_hom_ext {M X : ModuleCat R}
    {f g : baerModuleIdealDirectSum R M ⟶ X}
    (hfg : ∀ j : baerModuleIndex R M,
      baerModuleIdealSummandIn R M j ≫ f = baerModuleIdealSummandIn R M j ≫ g) :
    f = g := by
  classical
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  -- Route correction: package the `ModuleCat`-to-`LinearMap` boundary once so later proofs can
  -- stay on the source coprojection route from the textbook.
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext R
  intro j
  apply LinearMap.ext
  intro x
  simpa [baerModuleIdealSummandIn] using
    congrArg (fun k : j.1 →ₗ[R] X => k x) (congrArg ModuleCat.Hom.hom (hfg j))

/-- Helper for Lemma 19.2.7: maps out of the direct sum of `R`-summands are determined by their
values on the canonical coprojections. -/
private theorem baerModuleRingSummandIn_hom_ext {M X : ModuleCat R}
    {f g : baerModuleRingDirectSum R M ⟶ X}
    (hfg : ∀ j : baerModuleIndex R M,
      baerModuleRingSummandIn R M j ≫ f = baerModuleRingSummandIn R M j ≫ g) :
    f = g := by
  classical
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  -- As on the ideal side, reduce once to equality of the underlying linear maps on generators.
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext R
  intro j
  apply LinearMap.ext
  intro x
  simpa [baerModuleRingSummandIn] using
    congrArg (fun k : R →ₗ[R] X => k x) (congrArg ModuleCat.Hom.hom (hfg j))

/-- The left side of the Baer pushout square is natural in the module. -/
-- Proof sketch: both composites send the summand indexed by `(𝔞, φ)` to the copy of `R`
-- indexed by `(𝔞, f ∘ φ)` using the same inclusion `𝔞 ↪ R`, so they agree by extensionality of
-- maps out of a direct sum.
private theorem baerModuleLeftVertical_natural {M N : ModuleCat R} (f : M ⟶ N) :
    CommSq (baerModuleLeftVertical R M) (baerModuleIdealDirectSumMap R f)
      (baerModuleRingDirectSumMap R f) (baerModuleLeftVertical R N) := by
  classical
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  let _ : DecidableEq (baerModuleIndex R N) := Classical.decEq _
  refine ⟨?_⟩
  -- Compare the two composites on each generator of the source direct sum.
  refine ModuleCat.hom_ext ?_
  apply DirectSum.linearMap_ext R
  intro j
  apply LinearMap.ext
  intro x
  ext i
  simp [baerModuleLeftVertical, baerModuleIdealDirectSumMap,
    baerModuleRingDirectSumMap, baerModuleIndexMap]

/-- The top map in the Baer pushout square is natural in the module. -/
-- Proof sketch: on the summand indexed by `(𝔞, φ)`, the top map followed by `f` is exactly the
-- composite `f ∘ φ`, which is also the map defining the target summand indexed by `(𝔞, f ∘ φ)`.
private theorem baerModuleTopMap_natural {M N : ModuleCat R} (f : M ⟶ N) :
    CommSq (baerModuleTopMap R M) (baerModuleIdealDirectSumMap R f) f
      (baerModuleTopMap R N) := by
  classical
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  let _ : DecidableEq (baerModuleIndex R N) := Classical.decEq _
  refine ⟨?_⟩
  -- On the summand indexed by `(I, φ)`, both composites evaluate to `f ∘ φ`.
  refine ModuleCat.hom_ext ?_
  apply DirectSum.linearMap_ext R
  intro j
  apply LinearMap.ext
  intro x
  simp [baerModuleTopMap, baerModuleIdealDirectSumMap, baerModuleIndexMap]

/-- Helper for Lemma 19.2.7: the direct-sum map on ideal summands is the identity on identity
maps. -/
private theorem baerModuleIdealDirectSumMap_id (M : ModuleCat R) :
    baerModuleIdealDirectSumMap R (𝟙 M) = 𝟙 (baerModuleIdealDirectSum R M) := by
  classical
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  -- Check the identity case on each source coprojection and reassemble by the new adapter.
  refine ModuleCat.hom_ext ?_
  apply DirectSum.linearMap_ext R
  intro j
  apply LinearMap.ext
  intro x
  ext i
  simp [baerModuleIdealDirectSumMap, baerModuleIndexMap]

/-- Helper for Lemma 19.2.7: the direct-sum map on ideal summands respects composition. -/
private theorem baerModuleIdealDirectSumMap_comp {M N P : ModuleCat.{u} R} (f : M ⟶ N)
    (g : N ⟶ P) :
    baerModuleIdealDirectSumMap R (f ≫ g) =
      baerModuleIdealDirectSumMap R f ≫ baerModuleIdealDirectSumMap R g := by
  classical
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  let _ : DecidableEq (baerModuleIndex R N) := Classical.decEq _
  let _ : DecidableEq (baerModuleIndex R P) := Classical.decEq _
  -- Route correction: compare both morphisms after precomposing with each source coprojection,
  -- and use the literal summand transport lemma before any direct-sum extensionality.
  refine ModuleCat.hom_ext ?_
  apply DirectSum.linearMap_ext R
  intro j
  simpa [baerModuleIdealSummandIn, Category.assoc] using
    congrArg ModuleCat.Hom.hom
      (show baerModuleIdealSummandIn R M j ≫ baerModuleIdealDirectSumMap R (f ≫ g) =
          baerModuleIdealSummandIn R M j ≫
            (baerModuleIdealDirectSumMap R f ≫ baerModuleIdealDirectSumMap R g) from by
        calc
          baerModuleIdealSummandIn R M j ≫ baerModuleIdealDirectSumMap R (f ≫ g) =
              baerModuleIdealSummandIn R P (baerModuleIndexMap R (f ≫ g) j) := by
                simpa using baerModuleIdealDirectSumMap_comp_lof R (f ≫ g) j
          _ = baerModuleIdealSummandIn R P
                (baerModuleIndexMap R g (baerModuleIndexMap R f j)) := by
                simpa using baerModuleIdealSummandIn_indexMap_comp R f g j
          _ = baerModuleIdealSummandIn R N (baerModuleIndexMap R f j) ≫
                baerModuleIdealDirectSumMap R g := by
                symm
                simpa using
                  baerModuleIdealDirectSumMap_comp_lof R g (baerModuleIndexMap R f j)
          _ = baerModuleIdealSummandIn R M j ≫
                (baerModuleIdealDirectSumMap R f ≫ baerModuleIdealDirectSumMap R g) := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ k ≫ baerModuleIdealDirectSumMap R g)
                    (baerModuleIdealDirectSumMap_comp_lof R f j).symm)

/-- Helper for Lemma 19.2.7: the direct-sum map on copies of `R` is the identity on identity
maps. -/
private theorem baerModuleRingDirectSumMap_id (M : ModuleCat R) :
    baerModuleRingDirectSumMap R (𝟙 M) = 𝟙 (baerModuleRingDirectSum R M) := by
  classical
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  -- The identity morphism leaves each `R`-summand coprojection fixed.
  refine ModuleCat.hom_ext ?_
  apply DirectSum.linearMap_ext R
  intro j
  apply LinearMap.ext
  intro r
  ext i
  simp [baerModuleRingDirectSumMap, baerModuleIndexMap]

/-- Helper for Lemma 19.2.7: the direct-sum map on copies of `R` respects composition. -/
private theorem baerModuleRingDirectSumMap_comp {M N P : ModuleCat.{u} R} (f : M ⟶ N)
    (g : N ⟶ P) :
    baerModuleRingDirectSumMap R (f ≫ g) =
      baerModuleRingDirectSumMap R f ≫ baerModuleRingDirectSumMap R g := by
  classical
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  let _ : DecidableEq (baerModuleIndex R N) := Classical.decEq _
  let _ : DecidableEq (baerModuleIndex R P) := Classical.decEq _
  -- The ring-side direct sum follows the same summandwise argument as the ideal side.
  refine ModuleCat.hom_ext ?_
  apply DirectSum.linearMap_ext R
  intro j
  simpa [baerModuleRingSummandIn, Category.assoc] using
    congrArg ModuleCat.Hom.hom
      (show baerModuleRingSummandIn R M j ≫ baerModuleRingDirectSumMap R (f ≫ g) =
          baerModuleRingSummandIn R M j ≫
            (baerModuleRingDirectSumMap R f ≫ baerModuleRingDirectSumMap R g) from by
        calc
          baerModuleRingSummandIn R M j ≫ baerModuleRingDirectSumMap R (f ≫ g) =
              baerModuleRingSummandIn R P (baerModuleIndexMap R (f ≫ g) j) := by
                simpa using baerModuleRingDirectSumMap_comp_lof R (f ≫ g) j
          _ = baerModuleRingSummandIn R P
                (baerModuleIndexMap R g (baerModuleIndexMap R f j)) := by
                simpa using baerModuleRingSummandIn_indexMap_comp R f g j
          _ = baerModuleRingSummandIn R N (baerModuleIndexMap R f j) ≫
                baerModuleRingDirectSumMap R g := by
                symm
                simpa using
                  baerModuleRingDirectSumMap_comp_lof R g (baerModuleIndexMap R f j)
          _ = baerModuleRingSummandIn R M j ≫
                (baerModuleRingDirectSumMap R f ≫ baerModuleRingDirectSumMap R g) := by
                simpa [Category.assoc] using
                  congrArg (fun k ↦ k ≫ baerModuleRingDirectSumMap R g)
                    (baerModuleRingDirectSumMap_comp_lof R f j).symm)

/-- The map `\mathbf{M}(M) → \mathbf{M}(N)` induced by a morphism `M ⟶ N`. -/
private noncomputable abbrev baerModuleStepMap {M N : ModuleCat R} (f : M ⟶ N) :
    𝐌(M) ⟶ 𝐌(N) :=
  pushout.map (baerModuleLeftVertical R M) (baerModuleTopMap R M)
    (baerModuleLeftVertical R N) (baerModuleTopMap R N)
    (baerModuleRingDirectSumMap R f) f (baerModuleIdealDirectSumMap R f)
    (baerModuleLeftVertical_natural R f).w (baerModuleTopMap_natural R f).w

/-- The canonical map on Baer pushouts acts as the identity on identity morphisms. -/
-- Proof sketch: this is the identity case of `pushout.map`, using the identity maps on all three
-- corners of the defining span.
private theorem baerModuleStepMap_id (M : ModuleCat R) :
    baerModuleStepMap R (𝟙 M) = 𝟙 (𝐌(M)) := by
  -- Rewrite the three side maps to identities and invoke the pushout identity formula.
  simpa [baerModuleStepMap, baerModuleIdealDirectSumMap_id, baerModuleRingDirectSumMap_id] using
    (pushout.map_id (f := baerModuleLeftVertical R M) (g := baerModuleTopMap R M))

/-- The canonical map on Baer pushouts respects composition. -/
-- Proof sketch: functoriality of `pushout.map` gives the compatibility with composition once the
-- naturality relations for the two sides of the defining span are inserted.
private theorem baerModuleStepMap_comp {M N P : ModuleCat.{u} R} (f : M ⟶ N) (g : N ⟶ P) :
    baerModuleStepMap R (f ≫ g) =
      baerModuleStepMap R f ≫ baerModuleStepMap R g := by
  -- The comparison maps between pushouts compose as soon as the span maps do.
  simpa [baerModuleStepMap, baerModuleIdealDirectSumMap_comp, baerModuleRingDirectSumMap_comp] using
    (pushout.map_comp
      (i₁ := baerModuleIdealDirectSumMap R f)
      (j₁ := baerModuleIdealDirectSumMap R g)
      (i₂ := baerModuleRingDirectSumMap R f)
      (j₂ := baerModuleRingDirectSumMap R g)
      (i₃ := f)
      (j₃ := g)
      (e₁ := (baerModuleLeftVertical_natural R f).w)
      (e₂ := (baerModuleTopMap_natural R f).w)
      (e₃ := (baerModuleLeftVertical_natural R g).w)
      (e₄ := (baerModuleTopMap_natural R g).w)).symm

/-- The Baer construction `M ↦ \mathbf{M}(M)` as an endofunctor on `ModuleCat R`. -/
noncomputable def baerModuleStepFunctor : ModuleCat R ⥤ ModuleCat R where
  obj := baerModuleStep R
  map := baerModuleStepMap R
  map_id := baerModuleStepMap_id R
  map_comp := baerModuleStepMap_comp R

/-- The canonical extension map `R ⟶ \mathbf{M}(M)` attached to an ideal map `𝔞 → M`. -/
noncomputable abbrev baerModuleIdealLift (M : ModuleCat R) (I : Ideal R) (φ : I →ₗ[R] M) :
    ModuleCat.of R R ⟶ 𝐌(M) :=
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  ModuleCat.ofHom
      (DirectSum.lof R (baerModuleIndex R M) (fun _j ↦ R) ⟨I, φ⟩) ≫
    baerModuleStepFromRingDirectSum R M

-- Proof sketch: the morphisms `baerModuleStepMap R f` assemble the one-step Baer construction
-- into an endofunctor, and the canonical inclusions from `M` into the pushouts commute with these
-- induced maps by the universal property of `pushout.map`.
/-- Lemma 19.2.7 (1): the canonical maps `M ⟶ \mathbf{M}(M)` are functorial in `M`. -/
theorem baerModuleStepInclusion_natural {M N : ModuleCat R} (f : M ⟶ N) :
    CommSq f (baerModuleStepInclusion R M) (baerModuleStepInclusion R N)
      ((baerModuleStepFunctor R).map f) := by
  refine ⟨?_⟩
  symm
  -- The induced pushout map is the universal descendant with `inr`-leg `f ≫ inr`.
  change
    pushout.inr (baerModuleLeftVertical R M) (baerModuleTopMap R M) ≫
        pushout.desc
          (baerModuleRingDirectSumMap R f ≫
            pushout.inl (baerModuleLeftVertical R N) (baerModuleTopMap R N))
          (f ≫ pushout.inr (baerModuleLeftVertical R N) (baerModuleTopMap R N))
          (by
            calc
              baerModuleLeftVertical R M ≫ baerModuleRingDirectSumMap R f ≫
                  pushout.inl (baerModuleLeftVertical R N) (baerModuleTopMap R N) =
                  baerModuleIdealDirectSumMap R f ≫ baerModuleLeftVertical R N ≫
                    pushout.inl (baerModuleLeftVertical R N) (baerModuleTopMap R N) := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun k ↦ k ≫ pushout.inl (baerModuleLeftVertical R N) (baerModuleTopMap R N))
                        (baerModuleLeftVertical_natural R f).w
              _ = baerModuleIdealDirectSumMap R f ≫ baerModuleTopMap R N ≫
                  pushout.inr (baerModuleLeftVertical R N) (baerModuleTopMap R N) := by
                    simpa [Category.assoc] using
                      congrArg
                        (fun k ↦ baerModuleIdealDirectSumMap R f ≫ k)
                        (pushout.condition (f := baerModuleLeftVertical R N) (g := baerModuleTopMap R N))
              _ = baerModuleTopMap R M ≫ f ≫
                  pushout.inr (baerModuleLeftVertical R N) (baerModuleTopMap R N) := by
                    simpa [Category.assoc] using
                      (congrArg
                        (fun k ↦ k ≫ pushout.inr (baerModuleLeftVertical R N) (baerModuleTopMap R N))
                        (baerModuleTopMap_natural R f).w).symm)
      =
      f ≫ pushout.inr (baerModuleLeftVertical R N) (baerModuleTopMap R N)
  rw [pushout.inr_desc]

/-- The natural transformation from the identity functor on `R`-modules to the one-step Baer
functor. -/
noncomputable def baerModuleStepInclusionNatTrans :
    𝟭 (ModuleCat R) ⟶ baerModuleStepFunctor R where
  app M := baerModuleStepInclusion R M
  naturality := fun {_ _} f ↦ (baerModuleStepInclusion_natural R f).w

-- Proof sketch: in the Baer pushout construction one adjoins copies of `R` to force extensions of
-- maps from ideals into `M`, but no relation identifies two distinct elements already lying in
-- `M`; this yields injectivity of the canonical inclusion.
/-- Helper for Lemma 19.2.7: the left vertical map sends a generator of the `j`th ideal summand to
the corresponding generator of the `j`th copy of `R`, labeled by the same index. -/
private theorem baerModuleLeftVertical_apply_of {M : ModuleCat.{u} R}
    (j : baerModuleIndex R M) (x : j.1) :
    let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
    (baerModuleLeftVertical R M).hom
        (DirectSum.of (fun i : baerModuleIndex R M ↦ i.1) j x) =
      DirectSum.of (fun _j : baerModuleIndex R M ↦ R) j (j.1.subtype x) := by
  classical
  -- Route correction: evaluate the already-proved coprojection equality on one generator, then
  -- rewrite both coprojections into a single classical `DirectSum.of` surface.
  simpa [baerModuleIdealSummandIn, baerModuleRingSummandIn, DirectSum.lof_eq_of] using
    congrArg (fun k : j.1 →ₗ[R] baerModuleRingDirectSum R M => k x)
      (congrArg ModuleCat.Hom.hom
        (baerModuleLeftVertical_comp_source_lof (R := R) (M := M) (j := j)))

/-- Helper for Lemma 19.2.7: after precomposing with the `j`th source coprojection, the `j`th
component of the left vertical map is the ideal inclusion `j.1 ↪ R`. -/
private theorem baerModuleLeftVertical_component_comp_lof_self {M : ModuleCat.{u} R}
    (j : baerModuleIndex R M) :
    let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
    DirectSum.component R (baerModuleIndex R M) (fun _j ↦ R) j ∘ₗ
        (baerModuleLeftVertical R M).hom ∘ₗ
        DirectSum.lof R (baerModuleIndex R M) (fun i ↦ i.1) j =
      j.1.subtype := by
  classical
  -- Once the index instance is fixed to the same classical one as `baerModuleLeftVertical`,
  -- the diagonal formula is the defining `DirectSum.toModule` computation on one generator.
  ext x
  simp [baerModuleLeftVertical]

/-- Helper for Lemma 19.2.7: after precomposing with a different source coprojection, the `j`th
component of the left vertical map vanishes. -/
private theorem baerModuleLeftVertical_component_comp_lof_ne {M : ModuleCat.{u} R}
    {j k : baerModuleIndex R M} (hjk : k ≠ j) :
    let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
    DirectSum.component R (baerModuleIndex R M) (fun _j ↦ R) j ∘ₗ
        (baerModuleLeftVertical R M).hom ∘ₗ
        DirectSum.lof R (baerModuleIndex R M) (fun i ↦ i.1) k =
      0 := by
  classical
  -- Off the diagonal, the defining `DirectSum.component.of` formula collapses to zero.
  ext x
  simp [baerModuleLeftVertical, DirectSum.component.of, hjk]

/-- Helper for Lemma 19.2.7: projecting the left vertical map to the `j`th copy of `R` recovers
the inclusion of the `j`th ideal summand into `R`. -/
private theorem baerModuleLeftVertical_component {M : ModuleCat.{u} R} (j : baerModuleIndex R M) :
    DirectSum.component R (baerModuleIndex R M) (fun _j ↦ R) j ∘ₗ
        (baerModuleLeftVertical R M).hom =
      j.1.subtype.comp
        (DirectSum.component R (baerModuleIndex R M) (fun k ↦ k.1) j) := by
  classical
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  -- Compare both linear maps on the source coprojections of the ideal direct sum.
  apply DirectSum.linearMap_ext R
  intro k
  by_cases hk : k = j
  · subst k
    -- On the diagonal summand, both sides are the ideal inclusion.
    calc
      (DirectSum.component R (baerModuleIndex R M) (fun _j ↦ R) j ∘ₗ
          (baerModuleLeftVertical R M).hom).comp
          (DirectSum.lof R (baerModuleIndex R M) (fun i ↦ i.1) j) =
          j.1.subtype := baerModuleLeftVertical_component_comp_lof_self R j
      _ =
          (j.1.subtype.comp
              (DirectSum.component R (baerModuleIndex R M) (fun k ↦ k.1) j)).comp
            (DirectSum.lof R (baerModuleIndex R M) (fun i ↦ i.1) j) := by
            ext x
            simp
  · -- Off the diagonal, both sides vanish because the `j`th component misses the `k`th summand.
    calc
      (DirectSum.component R (baerModuleIndex R M) (fun _j ↦ R) j ∘ₗ
          (baerModuleLeftVertical R M).hom).comp
          (DirectSum.lof R (baerModuleIndex R M) (fun i ↦ i.1) k) =
          0 := by
            simpa using baerModuleLeftVertical_component_comp_lof_ne R (M := M) (j := j) hk
      _ =
          (j.1.subtype.comp
              (DirectSum.component R (baerModuleIndex R M) (fun i ↦ i.1) j)).comp
            (DirectSum.lof R (baerModuleIndex R M) (fun i ↦ i.1) k) := by
            symm
            ext x
            change
              j.1.subtype
                  (DirectSum.component R (baerModuleIndex R M) (fun i ↦ i.1) j
                    ((DirectSum.lof R (baerModuleIndex R M) (fun i ↦ i.1) k) x)) =
                0
            simp [DirectSum.component.of, hk]

/-- Helper for Lemma 19.2.7: the left vertical map in the Baer pushout span is injective. -/
private theorem baerModuleLeftVertical_hom_injective (M : ModuleCat.{u} R) :
    Function.Injective (baerModuleLeftVertical R M).hom := by
  classical
  let _ : DecidableEq (baerModuleIndex R M) := Classical.decEq _
  -- Equality in the target direct sum forces equality of every source ideal component.
  intro x y hxy
  apply DirectSum.ext_component R
  intro j
  have hcomponent :
      DirectSum.component R (baerModuleIndex R M) (fun _j ↦ R) j
          ((baerModuleLeftVertical R M).hom x) =
        DirectSum.component R (baerModuleIndex R M) (fun _j ↦ R) j
          ((baerModuleLeftVertical R M).hom y) := by
    exact congrArg
      (fun z ↦ DirectSum.component R (baerModuleIndex R M) (fun _j ↦ R) j z) hxy
  have hsubtype :
      j.1.subtype (DirectSum.component R (baerModuleIndex R M) (fun k ↦ k.1) j x) =
        j.1.subtype (DirectSum.component R (baerModuleIndex R M) (fun k ↦ k.1) j y) := by
    -- Rewrite each target component through the diagonal formula from the previous lemma.
    have hxrewrite :
        (DirectSum.component R (baerModuleIndex R M) (fun _j ↦ R) j)
            ((baerModuleLeftVertical R M).hom x) =
          j.1.subtype (DirectSum.component R (baerModuleIndex R M) (fun k ↦ k.1) j x) := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun k : baerModuleIdealDirectSum R M →ₗ[R] R => k x)
          (baerModuleLeftVertical_component R (M := M) j)
    have hyrewrite :
        (DirectSum.component R (baerModuleIndex R M) (fun _j ↦ R) j)
            ((baerModuleLeftVertical R M).hom y) =
          j.1.subtype (DirectSum.component R (baerModuleIndex R M) (fun k ↦ k.1) j y) := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun k : baerModuleIdealDirectSum R M →ₗ[R] R => k y)
          (baerModuleLeftVertical_component R (M := M) j)
    calc
      j.1.subtype (DirectSum.component R (baerModuleIndex R M) (fun k ↦ k.1) j x) =
          (DirectSum.component R (baerModuleIndex R M) (fun _j ↦ R) j)
            ((baerModuleLeftVertical R M).hom x) := by
            symm
            exact hxrewrite
      _ =
          (DirectSum.component R (baerModuleIndex R M) (fun _j ↦ R) j)
            ((baerModuleLeftVertical R M).hom y) := hcomponent
      _ =
          j.1.subtype (DirectSum.component R (baerModuleIndex R M) (fun k ↦ k.1) j y) := by
            exact hyrewrite
  exact Subtype.coe_injective hsubtype

/-- Lemma 19.2.7 (2): the canonical map `M ⟶ \mathbf{M}(M)` is injective. -/
theorem baerModuleStepInclusion_injective (M : ModuleCat.{u} R) :
    Function.Injective (baerModuleStepInclusion R M).hom := by
  have hmonoLeft : Mono (baerModuleLeftVertical R M) :=
    (ModuleCat.mono_iff_injective _).2 (baerModuleLeftVertical_hom_injective R M)
  letI : Mono (baerModuleLeftVertical R M) := hmonoLeft
  -- In an abelian category, pushout `inr` is mono when the left leg is mono.
  have hmonoInclusion : Mono (baerModuleStepInclusion R M) := by
    simpa [baerModuleStepInclusion] using
      (CategoryTheory.Abelian.mono_inr_of_isColimit
        (baerModuleLeftVertical R M) (baerModuleTopMap R M)
        (pushout.isColimit (baerModuleLeftVertical R M) (baerModuleTopMap R M)))
  exact (ModuleCat.mono_iff_injective _).1 hmonoInclusion

-- Proof sketch: the pair `(I, φ)` indexing the chosen ideal map contributes a distinguished `R`
-- summand to the left side of the pushout, and composing its coprojection with the pushout map
-- produces the required extension square.
/-- Lemma 19.2.7 (3): every `R`-linear map from an ideal `I ⊆ R` to `M` extends to a map
`R ⟶ \mathbf{M}(M)` compatible with the canonical inclusion `M ⟶ \mathbf{M}(M)`. -/
theorem baerModuleIdealLift_comp_subtype (M : ModuleCat R) (I : Ideal R) (φ : I →ₗ[R] M) :
    CommSq (ModuleCat.ofHom I.subtype) (ModuleCat.ofHom φ)
      (baerModuleIdealLift R M I φ) (baerModuleStepInclusion R M) := by
  refine ⟨?_⟩
  -- Precompose the defining pushout square with the summand indexed by `(I, φ)`.
  have hsquare :
      baerModuleIdealSummandIn R M ⟨I, φ⟩ ≫ baerModuleLeftVertical R M ≫
          baerModuleStepFromRingDirectSum R M =
        baerModuleIdealSummandIn R M ⟨I, φ⟩ ≫ baerModuleTopMap R M ≫
          baerModuleStepInclusion R M := by
    exact
    congrArg (fun k ↦ baerModuleIdealSummandIn R M ⟨I, φ⟩ ≫ k)
      (baerModuleStep_square_commutes R M).w
  calc
    ModuleCat.ofHom I.subtype ≫ baerModuleIdealLift R M I φ =
        baerModuleIdealSummandIn R M ⟨I, φ⟩ ≫ baerModuleLeftVertical R M ≫
          baerModuleStepFromRingDirectSum R M := by
            simpa [baerModuleIdealLift, Category.assoc] using
              congrArg (fun k ↦ k ≫ baerModuleStepFromRingDirectSum R M)
                (baerModuleLeftVertical_comp_source_lof (R := R) (M := M) (j := ⟨I, φ⟩)).symm
    _ = baerModuleIdealSummandIn R M ⟨I, φ⟩ ≫ baerModuleTopMap R M ≫
          baerModuleStepInclusion R M := hsquare
    _ = ModuleCat.ofHom φ ≫ baerModuleStepInclusion R M := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ baerModuleStepInclusion R M)
              (baerModuleTopMap_comp_source_lof (R := R) (M := M) (j := ⟨I, φ⟩))

end
