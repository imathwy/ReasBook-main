import Mathlib
import StacksProject_2024.Chap14.Definition_14_26_6
import StacksProject_2024.Chap14.Example_14_34_5
import StacksProject_2024.Chap14.Lemma_14_34_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmented
open CommRingCat
open scoped Simplicial

universe u

noncomputable section

namespace CategoryTheory

variable (A : CommRingCat.{u})

/- Domain-style sampling for Example 14.34.8:
- primary domain: simplicial resolutions attached to the free-forgetful adjunctions on
  `Under A` and on `CommRingCat`, together with the explicit `fromZero` sections giving iterated
  bracket inverse maps;
- sampled same-kind owner declarations:
  `polynomialAlgebraAugmentedUnderlyingSet`,
  `prePostcomposeAugmented`,
  `iteratedEndofunctorAugmentation`,
  `SimplicialObject.fromZero`;
- best owner abstraction: the public owners are the augmented resolutions already present upstream
  in the chapter, namely `polynomialAlgebraAugmentedUnderlyingSet A B` and the evaluated
  `commRingFreeForgetSetAugmentedResolution E`; the explicit degree-`0` unit maps and their
  induced `fromZero` morphisms are bridge/view data derived from those owners;
- primitive data vs. derived API:
  primitive data are the upstream augmented owners and the degree-`0` unit-induced section maps;
  derived API is the underlying simplicial object view, the induced iterated-bracket inverse maps,
  and the existence of homotopy equivalences with those specified forward and inverse maps.

Source/core/bridge triage:
- `source-facing`: the augmented simplicial resolutions appearing in Example 14.34.8;
- `core/canonical`: `prePostcomposeAugmented`, `iteratedEndofunctorAugmentation`, and
  `SimplicialObject.Augmented`;
- `bridge/view`: the degree-`0` maps and the induced `fromZero` simplicial morphisms. -/

-- Proof sketch: degree `0` of the augmented Čech nerve of `A[B] ⟶ B` is the source object
-- `A[B]`; forgetting the `A`-algebra structure gives the underlying set of that ring.
/-- The degree-`0` simplicial set of the polynomial resolution is the underlying set of `A[B]`. -/
theorem polynomialAlgebraAugmentedUnderlyingSet_obj_zero_eq (B : Under A) :
    (polynomialAlgebraAugmentedUnderlyingSet A B).left _⦋0⦌ =
      (Under.forget A ⋙ forget CommRingCat).obj ((Under.costar A).obj B.right) := by
  -- Route correction: compute only the degree-`0` owner of the whiskered augmented Čech nerve.
  simp [polynomialAlgebraAugmentedUnderlyingSet, polynomialAlgebraAugmentedResolution]

-- Proof sketch: this is the commutative square expressing that the unit of the adjunction
-- `Under.costarAdjForget A` is a morphism in the under-category of `A`.
private theorem polynomialAlgebraResolutionForgetInverseZeroMap_sq (B : Under A) :
    CommSq B.hom (𝟙 A) ((Under.costarAdjForget A).unit.app B.right)
      ((Under.costar A).obj B.right).hom := by
  -- Route correction: use the under-category commutativity of the unit map directly.
  refine ⟨?_⟩
  ext x
  simp [Under.costarAdjForget]

private abbrev polynomialAlgebraResolutionForgetInverseZeroHom (B : Under A) :
    B ⟶ (Under.costar A).obj B.right :=
  Under.homMk
    ((Under.costarAdjForget A).unit.app B.right)
    (polynomialAlgebraResolutionForgetInverseZeroMap_sq A B).w

/-- The degree-`0` iterated-bracket map from the underlying set of `B` into the polynomial
resolution. -/
abbrev polynomialAlgebraResolutionForgetInverseZeroMap (B : Under A) :
    (polynomialAlgebraAugmentedUnderlyingSet A B).right ⟶
      (polynomialAlgebraAugmentedUnderlyingSet A B).left _⦋0⦌ :=
  (Under.forget A ⋙ forget CommRingCat).map
      (polynomialAlgebraResolutionForgetInverseZeroHom A B) ≫
    eqToHom (polynomialAlgebraAugmentedUnderlyingSet_obj_zero_eq A B).symm

/-- The simplicial-set map sending an element `b` to the iterated bracket simplex
`[\ldots [b] \ldots ]` in each degree. -/
abbrev polynomialAlgebraResolutionForgetInverse (B : Under A) :
    (const (Type u)).obj (polynomialAlgebraAugmentedUnderlyingSet A B).right ⟶
      (polynomialAlgebraAugmentedUnderlyingSet A B).left :=
  (polynomialAlgebraAugmentedUnderlyingSet A B).left.fromZero
    (polynomialAlgebraResolutionForgetInverseZeroMap A B)

/-- Helper for Example 14.34.8: a strict simplicial section of a homotopy-equivalence morphism is
itself a homotopy inverse. -/
private theorem homotopy_equiv_of_section
    {C : Type*} [Category C] {X Y : SimplicialObject C}
    {f : X ⟶ Y} (hf : IsHomotopyEquivalence f)
    (g : Y ⟶ X) (hg : g ≫ f = 𝟙 Y) :
    HomotopyEquiv X Y := by
  rcases hf with ⟨e, rfl⟩
  refine
    { hom := e.hom
      inv := g
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · -- Compare the chosen strict section with the inverse supplied by the existing witness.
    have h_inv : Homotopic e.inv g := by
      simpa [Category.assoc, hg] using e.homotopyHomInvId.precomp g
    have h_comp : Homotopic (e.hom ≫ e.inv) (e.hom ≫ g) := h_inv.precomp e.hom
    exact h_comp.symm.trans e.homotopyHomInvId
  · -- The section equation upgrades immediately to the required homotopy on the constant target.
    simpa [hg] using (Homotopic.refl (𝟙 Y : Y ⟶ Y))

/-- Helper for Example 14.34.8: the degree-`0` iterated-bracket map is a section of the degree-`0`
augmentation for the polynomial resolution. -/
private theorem polynomialAlgebraResolutionForgetInverseZeroMap_comp_app_zero
    (B : Under A) :
    polynomialAlgebraResolutionForgetInverseZeroMap A B ≫
        (polynomialAlgebraAugmentedUnderlyingSet A B).hom.app (op ⦋0⦌) =
      𝟙 (polynomialAlgebraAugmentedUnderlyingSet A B).right := by
  -- Route correction: rewrite the degree-`0` augmentation to the forgotten counit and then apply
  -- the adjunction triangle identity after forgetting to sets.
  simpa [polynomialAlgebraResolutionForgetInverseZeroMap,
    polynomialAlgebraResolutionForgetInverseZeroHom, polynomialAlgebraAugmentedUnderlyingSet,
    polynomialAlgebraAugmentedResolution] using
    congrArg ((forget CommRingCat).map) ((Under.costarAdjForget A).right_triangle_components B)

/-- Helper for Example 14.34.8: the iterated-bracket simplicial map is a strict section of the
polynomial-resolution augmentation. -/
private theorem polynomialAlgebraResolutionForgetInverse_comp_augmentation_eq_id
    (B : Under A) :
    polynomialAlgebraResolutionForgetInverse A B ≫
        (polynomialAlgebraAugmentedUnderlyingSet A B).hom =
      𝟙 ((const (Type u)).obj (polynomialAlgebraAugmentedUnderlyingSet A B).right) := by
  -- Extend the verified degree-`0` section along the unique maps to `[0]`.
  simpa [polynomialAlgebraResolutionForgetInverse] using
    SimplicialObject.fromZero_comp_hom
      (polynomialAlgebraAugmentedUnderlyingSet A B)
      (polynomialAlgebraResolutionForgetInverseZeroMap A B)
      (polynomialAlgebraResolutionForgetInverseZeroMap_comp_app_zero A B)

-- Proof sketch: specialize Lemma 14.34.3 to the adjunction `Under.costarAdjForget A`, then
-- evaluate the resulting statement on the `A`-algebra `B`. This identifies the standard
-- adjunction resolution with the augmented Cech nerve used in Example 14.34.5 and hence with the
-- displayed simplicial ring `A[A[\cdots[A[B]]\cdots]]` after forgetting to sets.
/- Example 14.34.8 (1) reuses the owner-level augmentation theorem from
`Example_14_34_5`. -/
recall polynomialAlgebraResolutionForgetAugmentation_isHomotopyEquivalence

-- Proof sketch: use the explicit section in the proof of Lemma 14.34.3 for the adjunction
-- `Under.costarAdjForget A`. In degree `0` it is the unit map `B → A[B]`, and `fromZero`
-- propagates that section to degree `n` by composing with the unique map `[n] → [0]`, which gives
-- the iterated-bracket formula.
/-- Example 14.34.8 (2): the homotopy inverse for the augmentation in (1) can be chosen to be the
simplicial map whose degree-`n` component sends `b` to the nested bracket simplex
`[\ldots [b] \ldots ]`. -/
theorem polynomialAlgebraResolutionForgetAugmentation_has_iterated_bracket_inverse
    (B : Under A) :
    ∃ e : HomotopyEquiv
        (polynomialAlgebraAugmentedUnderlyingSet A B).left
        ((const (Type u)).obj (polynomialAlgebraAugmentedUnderlyingSet A B).right),
      e.hom = (polynomialAlgebraAugmentedUnderlyingSet A B).hom ∧
      e.inv = polynomialAlgebraResolutionForgetInverse A B := by
  -- Reuse the existing homotopy-equivalence theorem and replace its inverse by the explicit
  -- iterated-bracket section, which is strict on the augmentation.
  refine ⟨homotopy_equiv_of_section
      (polynomialAlgebraResolutionForgetAugmentation_isHomotopyEquivalence A B)
      (polynomialAlgebraResolutionForgetInverse A B)
      (polynomialAlgebraResolutionForgetInverse_comp_augmentation_eq_id A B), rfl, rfl⟩

/-- The augmented simplicial commutative ring obtained by evaluating the canonical precomposed
free-forgetful adjunction resolution at a set `E`, with augmentation target `A[E]`. -/
abbrev commRingFreeForgetSetAugmentedResolution (E : Type u) :
    SimplicialObject.Augmented CommRingCat :=
  (whiskeringObj (Type u ⥤ CommRingCat) CommRingCat
      ((evaluation (Type u) CommRingCat).obj E)).obj
    (prePostcomposeAugmented free (𝟭 CommRingCat)
      (iteratedEndofunctorAugmentation
        adj.toComonad.ε
        adj.toComonad.δ
        (iteratedEndofunctorResolution_realization
          adj.toComonad.ε
          adj.toComonad.δ
          (adjunction_iteratedEndofunctor_hσδ₀ adj)
          (adjunction_iteratedEndofunctor_hσδ₁ adj)
          (adjunction_iteratedEndofunctor_hσσ adj))))

/-- The underlying simplicial commutative ring of
`commRingFreeForgetSetAugmentedResolution E`; its degree-`0` term is `A[A[E]]`, and it augments
to `A[E]`. -/
abbrev commRingFreeForgetSetResolution (E : Type u) : SimplicialObject CommRingCat :=
  (commRingFreeForgetSetAugmentedResolution E).left

/-- Helper for Example 14.34.8: the canonical iterated-endofunctor realization for the
free-forgetful adjunction on `CommRingCat`. -/
private abbrev commRingFreeForgetSetResolution_realization :
    IteratedEndofunctorRealization
      CommRingCat.adj.toComonad.ε
      CommRingCat.adj.toComonad.δ
      (iteratedEndofunctorResolution
        CommRingCat.adj.toComonad.ε
        CommRingCat.adj.toComonad.δ
        (adjunction_iteratedEndofunctor_hσδ₀ CommRingCat.adj)
        (adjunction_iteratedEndofunctor_hσδ₁ CommRingCat.adj)
        (adjunction_iteratedEndofunctor_hσσ CommRingCat.adj)) :=
  iteratedEndofunctorResolution_realization
    CommRingCat.adj.toComonad.ε
    CommRingCat.adj.toComonad.δ
    (adjunction_iteratedEndofunctor_hσδ₀ CommRingCat.adj)
    (adjunction_iteratedEndofunctor_hσδ₁ CommRingCat.adj)
    (adjunction_iteratedEndofunctor_hσσ CommRingCat.adj)

-- Proof sketch: in degree `0`, the precomposed standard resolution applies `CommRingCat.free` to
-- the underlying set of `A[E]`, giving `A[A[E]]`.
/-- The degree-`0` simplicial ring of the free-forgetful resolution on `E` is `A[A[E]]`. -/
theorem commRingFreeForgetSetResolution_obj_zero_eq (E : Type u) :
    (commRingFreeForgetSetResolution E) _⦋0⦌ =
      free.obj ((forget CommRingCat).obj (free.obj E)) := by
  -- Evaluate the canonical realization equality in degree `0` at the free commutative ring `A[E]`.
  simpa [commRingFreeForgetSetResolution, commRingFreeForgetSetAugmentedResolution,
    prePostcomposeAugmented, Functor.comp_obj] using
    congrArg (fun Z : CommRingCat ⥤ CommRingCat ↦ Z.obj (free.obj E))
      (commRingFreeForgetSetResolution_realization.obj_eq 0)

/-- The degree-`0` iterated-bracket map `A[E] → A[A[E]]` coming from the unit of the
free-forgetful adjunction. -/
abbrev commRingFreeForgetSetInverseZeroMap (E : Type u) :
    free.obj E ⟶ (commRingFreeForgetSetResolution E) _⦋0⦌ :=
  free.map (adj.unit.app E) ≫
    eqToHom (commRingFreeForgetSetResolution_obj_zero_eq E).symm

/-- The simplicial ring map whose degree-`n` component brackets each generator one more time. -/
abbrev commRingFreeForgetSetInverse (E : Type u) :
    (const CommRingCat).obj (free.obj E) ⟶
      commRingFreeForgetSetResolution E :=
  (commRingFreeForgetSetResolution E).fromZero
    (commRingFreeForgetSetInverseZeroMap E)

/-- Helper for Example 14.34.8: the degree-`0` bracket map for the free-forgetful resolution is a
section of the degree-`0` augmentation. -/
private theorem commRingFreeForgetSetInverseZeroMap_comp_app_zero
    (E : Type u) :
    commRingFreeForgetSetInverseZeroMap E ≫
        (commRingFreeForgetSetAugmentedResolution E).hom.app (op ⦋0⦌) =
      𝟙 (free.obj E) := by
  -- Evaluate the generic degree-`0` section equation for the precomposed adjunction resolution
  -- at `E` and identify the resulting map with the explicit iterated-bracket zero-simplex map.
  simpa [commRingFreeForgetSetInverseZeroMap, commRingFreeForgetSetResolution_obj_zero_eq,
    commRingFreeForgetSetAugmentedResolution, prePostcomposeAugmented,
    precompose_adjunctionResolutionAugmentation_zeroSection, Functor.comp_obj, Functor.comp_map] using
    congrArg (fun η : CommRingCat.adj.left ⟶ CommRingCat.adj.left ↦ η.app E)
      (precompose_adjunctionResolutionAugmentation_zeroSection_comp_app_zero
        (adj := CommRingCat.adj)
        (hX := commRingFreeForgetSetResolution_realization))

/-- Helper for Example 14.34.8: the iterated-bracket simplicial ring map is a strict section of
the free-forgetful-resolution augmentation. -/
private theorem commRingFreeForgetSetInverse_comp_augmentation_eq_id
    (E : Type u) :
    commRingFreeForgetSetInverse E ≫ (commRingFreeForgetSetAugmentedResolution E).hom =
      𝟙 ((const CommRingCat).obj (free.obj E)) := by
  -- Extend the verified degree-`0` section to all simplicial degrees by `fromZero`.
  simpa [commRingFreeForgetSetInverse] using
    SimplicialObject.fromZero_comp_hom
      (commRingFreeForgetSetAugmentedResolution E)
      (commRingFreeForgetSetInverseZeroMap E)
      (commRingFreeForgetSetInverseZeroMap_comp_app_zero E)

/-- Helper for Example 14.34.8: evaluating a functor-valued simplicial homotopy equivalence at a
set `E` preserves the homotopy-equivalence property. -/
private theorem evaluation_preserves_homotopy_equivalence
    (E : Type u)
    {X Y : SimplicialObject (Type u ⥤ CommRingCat)}
    {f : X ⟶ Y}
    (hf : IsHomotopyEquivalence f) :
    IsHomotopyEquivalence
      (Functor.whiskerRight f ((evaluation (Type u) CommRingCat).obj E)) := by
  rcases hf with ⟨e, rfl⟩
  refine ⟨?_, rfl⟩
  refine
    { hom := Functor.whiskerRight e.hom ((evaluation (Type u) CommRingCat).obj E)
      inv := Functor.whiskerRight e.inv ((evaluation (Type u) CommRingCat).obj E)
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · -- Evaluating the source-side homotopy witness at `E` preserves the homotopy relation.
    simpa using
      Homotopic.whiskerRight e.homotopyHomInvId ((evaluation (Type u) CommRingCat).obj E)
  · -- The target-side homotopy is preserved by the same evaluation functor.
    simpa using
      Homotopic.whiskerRight e.homotopyInvHomId ((evaluation (Type u) CommRingCat).obj E)

-- Proof sketch: apply the precomposition half of Lemma 14.34.3 to the free-forgetful adjunction
-- `CommRingCat.adj`, then evaluate the resulting simplicial homotopy equivalence at the set `E`.
/-- Example 14.34.8 (3): for every set `E`, the simplicial commutative ring built from the
free-forgetful adjunction on `E` is simplicially homotopy equivalent to the constant simplicial
ring on `A[E]`. -/
theorem commRingFreeForgetSetResolutionAugmentation_isHomotopyEquivalence
    (E : Type u) :
    IsHomotopyEquivalence
      (commRingFreeForgetSetAugmentedResolution E).hom := by
  -- Evaluate the functor-valued witness from Lemma 14.34.3 at `E`.
  simpa [commRingFreeForgetSetAugmentedResolution, prePostcomposeAugmented] using
    evaluation_preserves_homotopy_equivalence E
      (precompose_adjunctionResolutionAugmentation_isHomotopyEquivalence
        (adj := CommRingCat.adj)
        (hX := commRingFreeForgetSetResolution_realization))

-- Proof sketch: in the proof of Lemma 14.34.3, the degree-`0` section is obtained by applying the
-- free functor to the unit map `E → A[E]`. The associated `fromZero` morphism therefore sends a
-- polynomial `∑ a_{e₁,\ldots,e_p}[e₁]\cdots[e_p]` to the same coefficient sum with every generator
-- replaced by its iterated bracket in the target degree.
/-- Example 14.34.8 (4): the homotopy inverse in (3) can be chosen so that in degree `n` it sends
`∑ a_{e₁,\ldots,e_p}[e₁]\cdots[e_p]` to the corresponding sum with each generator replaced by its
nested bracket `[\ldots [e_i] \ldots ]`. -/
theorem commRingFreeForgetSetResolutionAugmentation_has_iterated_bracket_inverse
    (E : Type u) :
    ∃ e : HomotopyEquiv
        (commRingFreeForgetSetResolution E)
        ((const CommRingCat).obj (free.obj E)),
      e.hom = (commRingFreeForgetSetAugmentedResolution E).hom ∧
      e.inv = commRingFreeForgetSetInverse E := by
  -- Repackage the owner-level homotopy equivalence with the explicit `fromZero` inverse.
  refine ⟨homotopy_equiv_of_section
      (commRingFreeForgetSetResolutionAugmentation_isHomotopyEquivalence E)
      (commRingFreeForgetSetInverse E)
      (commRingFreeForgetSetInverse_comp_augmentation_eq_id E), rfl, rfl⟩

end CategoryTheory
