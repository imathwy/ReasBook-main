import Mathlib
import stacks_project.Chap06.Lemma_6_31_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace

universe u

/-
Domain-style sampling for Lemma 17.3.4:
- primary domain: extension by zero / by the initial object for sheaves of abelian groups along an
  open immersion of topological spaces;
- sampled owner declarations:
  `openSubsetSheafExtensionByInitialObject`,
  `OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalkDescription`,
  `Topology.IsEmbedding.toHomeomorph`,
  `TopCat.isoOfHomeo`;
- owner abstraction: the Chapter 6 owner remains the open-subset functor
  `openSubsetSheafExtensionByInitialObject U`; for a general open immersion `j : U ⟶ X`, the
  source-facing `j_!` functor should be obtained by transporting sheaves along the canonical
  homeomorphism `U ≃ j(U)` and then applying that owner. Since `TopCat` keeps open immersions
  unbundled as a morphism together with `Topology.IsOpenEmbedding j`, the public source-facing
  surface in this file should be a short `j_!`-style notation for that transport bridge rather
  than a second owner declaration;
- primitive data: the open immersion `j`, its open image `j(U)`, and the canonical isomorphism
  from `U` to the corresponding open subspace of `X`;
- derived API: the owner-level exactness statement for `j! U` and the thin general open-immersion
  bridge theorem obtained by transport along `U ≅ j(U)`.

Source/core/bridge triage:
- `source-facing`: exactness of `j_!` for a general open immersion `j : U ⟶ X`;
- `core/canonical`: `openSubsetSheafExtensionByInitialObject` on an open subset of `X`;
- `bridge/view`: the thin implementation bridge underlying the notation `j![j; hj]`, which
  transports sheaves along the canonical homeomorphism `U ≅ j(U)` and then applies the Chapter 6
  owner. -/

section AbelianExtensionByZero

variable {X U : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

private abbrev AbCat (Y : TopCat.{u})
    [HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}] :=
  TopCat.Sheaf AddCommGrpCat.{u} Y

local notation "Ab(" X ")" => AbCat X

private abbrev openImmersionImage
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j) : Opens X :=
  ⟨Set.range j, hj.isOpen_range⟩

private noncomputable abbrev openImmersionImageIso
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j) :
    U ≅ extensionByZeroOpenSubsetSpace (openImmersionImage j hj) :=
  show U ≅ extensionByZeroOpenSubsetSpace (openImmersionImage j hj) from
    TopCat.isoOfHomeo hj.1.toHomeomorph

/-- The open-subset owner-level form of Lemma 17.3.4: for an open subset `U ⊆ X`, the Chapter 6
extension-by-zero functor `j! U : Ab(U) ⥤ Ab(X)` is exact. -/
theorem openSubsetAbelianSheafExtensionByZero_exact
    (U : Opens X) :
    exactFunctor (Ab(extensionByZeroOpenSubsetSpace U)) (Ab(X)) (j! U) := sorry

/-- The implementation bridge for extension by zero along an open immersion `j : U ⟶ X`,
underlying the source-facing notation `j![j; hj]`. It transports sheaves from `U` to the open
image `j(U)` and then applies the Chapter 6 owner `j!`. -/
noncomputable abbrev openImmersionAbelianSheafExtensionByZero
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j) :
    Ab(U) ⥤ Ab(X) :=
  TopCat.Sheaf.pushforward AddCommGrpCat (openImmersionImageIso j hj).hom ⋙
    j! (openImmersionImage j hj)

notation:max "j![" j:max "; " hj:max "]" =>
  openImmersionAbelianSheafExtensionByZero j hj

-- Proof sketch: reduce the statement to the open-subset owner
-- `openSubsetSheafExtensionByInitialObject ⟨Set.range j, hj.isOpen_range⟩` via the canonical
-- homeomorphism `U ≃ j(U)`. Stalkwise, `OpenSubsetExtensionByInitial.sheafExtensionByInitial_
-- stalkDescription` identifies the stalks over points in the image with the original stalks and
-- the stalks off the image with zero, so exactness is checked on stalks.
/-- Lemma 17.3.4: if `j : U ⟶ X` is an open immersion, then the extension-by-zero functor
`j_! : Ab(U) ⥤ Ab(X)` is exact. In this formalization the source-facing functor is written
`j![j; hj]`; the extra `hj` is the Lean witness that the unbundled morphism `j` is an open
immersion. -/
theorem openImmersionAbelianSheafExtensionByZero_exact
    (j : U ⟶ X) (hj : Topology.IsOpenEmbedding j) :
    exactFunctor (Ab(U)) (Ab(X)) (j![j; hj]) := sorry

end AbelianExtensionByZero
