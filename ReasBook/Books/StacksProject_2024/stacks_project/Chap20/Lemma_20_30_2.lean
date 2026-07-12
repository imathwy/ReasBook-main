import StacksProject_2024.Chap20.Lemma_20_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry
open ComplexShape HomologicalComplex HomologicalComplex₂
open scoped HomologicalComplex₂

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.30.2:
- primary domain: bounded-below flasque replacements of cochain complexes of `𝒪_X`-
  modules on a ringed space, obtained from the Godement construction and measured stalkwise on the
  one-point ringed spaces `({x}, 𝒪_{X, x})`;
- sampled owner declarations:
  `CochainComplex.Plus`,
  `CochainComplex.Plus.ι`,
  `exists_functorial_godement_resolution`,
  `moduleUnderlyingSheaf`,
  `RingedSpace.stalkModuleFunctor`,
  `moduleTotalCechComplexToPlus`;
- best owner abstraction:
  `CochainComplex.Plus`, while Lemma `20.30.1` now provides the Godement complex, augmentation,
  and their source-facing quasi-isomorphism / flasqueness / stalkwise homotopy theorems directly;
  the termwise underlying additive sheaf is canonically owned by `moduleUnderlyingSheaf X`, so the
  present lemma should therefore remain a source-facing existential statement over
  `CochainComplex.Plus`, not a second packaged Godement API;
- primitive vs derived: the primitive existential data here are only the replacement object
  `G : CochainComplex.Plus (RingedSpace.Modules X)` and the bounded-below morphism
  `φ : F ⟶ G`. Quasi-isomorphism, termwise flasqueness, and pointwise homotopy equivalence are
  derived properties of that pair, while bounded-below-ness is carried canonically by the `Plus`
  owner rather than by separate witness fields.

Source/core/bridge triage:
- `source-facing`: existence of a bounded-below flasque replacement of a bounded-below complex;
- `core/canonical`: `CochainComplex.Plus` together with the direct functorial Godement-resolution
  existence theorem from Lemma `20.30.1`;
- `bridge/view`: this lemma, which extracts one replacement complex and augmentation from the
  Godement resolution and totalization construction. -/

-- Proof sketch: apply Lemma `20.30.1` in the abelian category of complexes of
-- `𝒪_X`-modules to obtain a termwise Godement resolution of `F`. Totalizing the resulting
-- double complex gives a bounded below complex `G` whose terms are finite direct sums of flasque
-- sheaves, hence flasque. The induced map on stalk complexes is a homotopy equivalence by the
-- stalkwise version of the Godement construction together with the totalization lemma
-- `12.25.5`, and therefore the augmentation is a quasi-isomorphism.
/-- The bounded-below flasque replacement from Lemma `20.30.2` may be chosen so that, for every
point `x : X`, the induced map on stalk complexes is a homotopy equivalence. -/
theorem exists_quasiIso_to_termwise_flasque_of_boundedBelow_with_pointwise_homotopy
    (F : CochainComplex.Plus X.Modules) :
    ∃ (G : CochainComplex.Plus X.Modules) (φ : F ⟶ G),
      QuasiIso φ.hom ∧
      (∀ n : ℤ, TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj (G.obj.X n))) ∧
      ∀ x : X,
        HomologicalComplex.homotopyEquivalences
          (ModuleCat (X.presheaf.stalk x))
          (up ℤ)
          (((stalkModuleFunctor x).mapHomologicalComplex (up ℤ)).map φ.hom) := by
  classical
  obtain ⟨G, η, hquasi, hflasque, hstalk⟩ := exists_functorial_godement_resolution X
  -- The source proof applies the chosen functorial Godement resolution termwise to `F`,
  -- forms the associated flipped bicomplex, and then totalizes along antidiagonals.
  -- The resulting bounded-below complex carries the desired quasi-isomorphism, flasqueness,
  -- and stalkwise homotopy-equivalence properties.
  sorry

/-- Lemma 20.30.2: if `𝓕•` is a bounded-below complex of `𝒪_X`-modules on a ringed space
`(X, 𝒪_X)`, then there exists a quasi-isomorphism `𝓕• ⟶ 𝓖•` with `𝓖•` bounded below and termwise
flasque. In the chapter’s canonical API, the bounded-below input and output are objects of
`CochainComplex.Plus`. The stronger companion theorem
`exists_quasiIso_to_termwise_flasque_of_boundedBelow_with_pointwise_homotopy` keeps the same
replacement together with the stalkwise homotopy-equivalence clause used later in the repository.
-/
@[stacks 0FKT]
theorem exists_quasiIso_to_termwise_flasque_of_boundedBelow
    (F : CochainComplex.Plus X.Modules) :
    ∃ (G : CochainComplex.Plus X.Modules) (φ : F ⟶ G),
      QuasiIso φ.hom ∧
      ∀ n : ℤ, TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj (G.obj.X n)) := by
  obtain ⟨G, φ, hquasi, hflasque, _⟩ :=
    exists_quasiIso_to_termwise_flasque_of_boundedBelow_with_pointwise_homotopy F
  exact ⟨G, φ, hquasi, hflasque⟩

end AlgebraicGeometry.RingedSpace
