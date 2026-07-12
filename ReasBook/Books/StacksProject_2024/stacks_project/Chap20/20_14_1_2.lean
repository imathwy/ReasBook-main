import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.AddCommGrpCat

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat
open TopCat.Sheaf

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

/- Textbook surface notation for direct image of abelian sheaves on topological spaces. -/
local notation:max f:max " _*" => TopCat.Sheaf.pushforward AddCommGrpCat.{u} f

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]
variable {ℱ : X.Sheaf AddCommGrpCat.{u}} {𝒢 : Y.Sheaf AddCommGrpCat.{u}}
variable (i : ℕ) (φ : 𝒢 ⟶ (f _*).obj ℱ)

local notation "SiteY" => Opens.grothendieckTopology Y
local notation "TopOpenY" => (⊤ : Opens Y)

/- Domain-style sampling for 20.14.1.2:
- primary domain: sheaf-cohomology functoriality for an `f`-map `φ : 𝒢 ⟶ f_* ℱ`;
- inspected owner declarations:
  `TopCat.Sheaf.pushforward AddCommGrpCat.{u} f`,
  `Sheaf.cohomologyPresheafFunctor`,
  `Sheaf.H'`;
- owner abstraction: the canonical owner is the cohomology presheaf functor, and the source-facing
  global map is its terminal-open component;
- primitive data: the continuous map `f` and the `f`-map `φ`;
- derived API: the induced morphism on degree-`i` cohomology.

Source/core/bridge triage:
- `source-facing`: the induced map `H^i(Y, 𝒢) ⟶ H^i(Y, f_* ℱ)`;
- `core/canonical`: `(f _*)` and
  `cohomologyPresheafFunctor`;
- `bridge/view`: evaluation of the mapped cohomology presheaf at `op (⊤ : Opens Y)`. -/

/-- Helper for 20.14.1.2: the induced cohomology-presheaf morphism evaluated on the terminal open
of `Y`, rewritten into the public `H'` notation. -/
private theorem cohomologyPresheafMapOnTopOpen :
    𝒢.H' i TopOpenY ⟶ ((f _*).obj ℱ).H' i TopOpenY := by
  simpa [Sheaf.H'] using
    (((cohomologyPresheafFunctor SiteY i).map φ).app (op TopOpenY))

/-- 20.14.1.2: an `f`-map `φ : 𝒢 ⟶ f_* ℱ` induces the canonical morphism
`H^i(Y, 𝒢) ⟶ H^i(Y, f_* ℱ)`, namely the terminal-open component of the cohomology-presheaf map
induced by `φ`. -/
@[stacks 01FA]
abbrev cohomologyMapOfFMap :
    𝒢.H' i TopOpenY ⟶ ((f _*).obj ℱ).H' i TopOpenY :=
  -- Evaluate the canonical cohomology-presheaf map on the terminal open of `Y`.
  cohomologyPresheafMapOnTopOpen (f := f) (i := i) (φ := φ)

end Sheaf
end CategoryTheory
