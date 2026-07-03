import Mathlib
import stacks_project.Chap06.ClosedSubsetInclusion
import stacks_project.Chap17.Lemma_17_19_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Topology
open scoped TopCat

noncomputable section

universe u

section

variable {X : TopCat.{u}}

local notation:max "i[" Z "]" => X.closedSubsetInclusion (Z : Set X)

/- Domain-style sampling for Lemma 17.19.4:
- primary domain: set-valued sheaves on spectral spaces and embeddings into finite products of
  pushforwards from closed subspaces;
- sampled owner declarations:
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn`,
  `exists_finite_sober_sheaf_model_of_constructible_set_presentation`,
  `TopCat.closedSubsetInclusion`,
  `Sheaf.pushforward`,
  `constantSheaf`;
- best owner abstraction: on the spectral-space branch, the source-facing hypothesis should use
  the compact-open owner
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn (fun U ↦ IsCompact (U : Set X))`,
  while the individual product factors should be stated directly using the canonical closed-subset
  inclusion and ambient sheaf pushforward rather than a local wrapper built from `TopCat.of Z` and
  `Subtype.val`;
- primitive data: a finite family of constructible closed subsets of `X` together with finite
  value types, indexed by an arbitrary finite type rather than a numbered model;
- derived API: the product sheaf built from those factors and the monomorphism from `ℱ`.

Source/core/bridge triage:
- `source-facing`: the finite-product embedding statement from constructible closed pieces;
- `core/canonical`: `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn`,
  `TopCat.closedSubsetInclusion`, `Sheaf.pushforward`, `constantSheaf`;
- `bridge/view`: the finite-sober descent input from Lemma `17.19.3`.
-/

-- Proof sketch: use Lemma `17.19.3` to descend `ℱ` to a sheaf with finite stalks on a finite sober
-- space `Y`. On `Y`, the canonical map into the product of the skyscraper sheaves
-- `∏_{y ∈ Y} i_{y, *} \underline{\mathcal G_y}` is monic. Pull this embedding back along the
-- spectral map `X ⟶ Y`; the inverse images of the point closures in `Y` are constructible closed
-- subsets of `X`, and the corresponding finite stalk sets give the required finite product.
/-- Lemma 17.19.4: a set-valued sheaf on a spectral space satisfying the finite coequalizer
presentation from `17.19.2.1` on quasi-compact opens embeds into a finite product of pushforwards
of constant finite sheaves from constructible closed subsets. -/
theorem exists_mono_to_finite_product_of_constructible_closed_pushforward_constant_sheaves
    [SpectralSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
    (ℱ : Sh(X))
    (hℱ :
      HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn
        (fun U ↦ IsCompact (U : Set X)) ℱ) :
    ∃ (ι : Type u) (_ : Fintype ι) (Z : ι → Closeds X)
      (hZ_constructible : ∀ a, IsConstructible (Z a : Set X))
      (A : ι → Type u) (hA_finite : ∀ a, Finite (A a)),
      let factor : Closeds X → Type u → Sh(X) := fun Z A ↦
        (Sheaf.pushforward (Type u) i[Z]).obj
          ((constantSheaf
              (Opens.grothendieckTopology (TopCat.of (Z : Set X)))
              (Type u)).obj A)
      ∃ φ : ℱ ⟶ ∏ᶜ fun a : ι ↦ factor (Z a) (A a),
        Mono φ := sorry

end
