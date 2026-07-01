import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat
open TopCat.Sheaf

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat]
variable [HasExt (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat)]
variable {ℱ : X.Sheaf AddCommGrpCat} {𝒢 : Y.Sheaf AddCommGrpCat}
variable (i : ℕ) (φ : 𝒢 ⟶ (pushforward AddCommGrpCat f).obj ℱ)

/- Domain-style sampling for 20.14.1.2:
- primary domain: sheaf-cohomology functoriality for an `f`-map `φ : 𝒢 ⟶ f_* ℱ`;
- inspected owner declarations:
  `TopCat.Sheaf.pushforward`,
  `Sheaf.cohomologyPresheafFunctor`,
  `Sheaf.cohomologyPresheaf`,
  `Sheaf.H'`;
- owner abstraction: the canonical owner is the mapped natural transformation
  `(cohomologyPresheafFunctor _ i).map φ`, and the textbook cohomology morphism is its component
  at the terminal open `⊤`;
- primitive data: the continuous map `f` and the `f`-map `φ`;
- derived API: the induced morphism on degree-`i` cohomology.

Source/core/bridge triage:
- `source-facing`: the induced map `H^i(Y, 𝒢) ⟶ H^i(Y, f_* ℱ)`;
- `core/canonical`: `pushforward` and `cohomologyPresheafFunctor`;
- `bridge/view`: evaluation of the mapped natural transformation at `op (⊤ : Opens Y)`. -/

/- 20.14.1.2: an `f`-map `φ : 𝒢 ⟶ f_* ℱ` induces the canonical morphism
`H^i(Y, 𝒢) ⟶ H^i(Y, f_* ℱ)`, namely the terminal-open component of the cohomology-presheaf map
induced by `φ`. -/
#check ((((cohomologyPresheafFunctor _ i).map φ).app (op ⊤)) :
  𝒢.H' i ⊤ ⟶ ((pushforward AddCommGrpCat f).obj ℱ).H' i ⊤)

end Sheaf
end CategoryTheory
