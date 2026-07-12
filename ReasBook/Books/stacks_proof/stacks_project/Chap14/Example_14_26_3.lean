import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable {X Y : SimplicialObject C} {f g : X ⟶ Y}

noncomputable section

namespace Homotopy

/- Domain-style sampling for Example 14.26.3:
- primary domain: simplicial homotopies between morphisms of simplicial objects;
- sampled owner API:
  `CategoryTheory.SimplicialObject.Homotopy`,
  `Homotopy.refl`,
  `Homotopy.precomp`,
  `Homotopy.postcomp`;
- best owner abstraction: the canonical owner is `CategoryTheory.SimplicialObject.Homotopy`;
- primitive data: a homotopy is given by its degreewise components `Homotopy.h` and the simplicial
  face/degeneracy relations bundled in the owner structure;
- derived API: `Homotopy.refl`, whiskering, and pre/postcomposition. The present example is only a
  `bridge/view`, transporting the canonical reflexive homotopy with components
  `X.σ i ≫ f.app _` along an equality of morphisms.

Source/core/bridge triage:
- `source-facing`: the textbook observation that equal maps are simplicially homotopic;
- `core/canonical`: `CategoryTheory.SimplicialObject.Homotopy` and its constant homotopy
  constructor `Homotopy.refl`;
- `bridge/view`: equality transport from `f = g` to a term of `Homotopy f g`. -/
recall Homotopy.refl (f : X ⟶ Y) : Homotopy f f

/-- Example 14.26.3: if `f = g`, then transporting the canonical constant simplicial homotopy
`Homotopy.refl f` along this equality gives a simplicial homotopy from `f` to `g`, with
components `h_{n,i} = X.σ i ≫ f.app _` (equivalently `X.σ i ≫ g.app _` after rewriting by
`h`). -/
@[stacks 07KA]
def ofEq (hfg : f = g) : Homotopy f g :=
  hfg ▸ Homotopy.refl f

@[simp] theorem ofEq_h {n : ℕ} (hfg : f = g) (i : Fin (n + 1)) :
    (ofEq hfg).h i = X.σ i ≫ f.app _ := by
  subst hfg
  rfl

end Homotopy

end

end CategoryTheory.SimplicialObject
