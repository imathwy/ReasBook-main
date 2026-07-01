import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace TopCat

noncomputable section

universe u

namespace CategoryTheory
namespace Sheaf

variable {X Z : TopCat.{u}}

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology Z) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u})]

-- Proof sketch: by Modules, Lemma `17.6.1`, pushforward along a closed immersion is exact, so its
-- higher right derived functors vanish. Apply Lemma `20.13.6` to the morphism `i`.
/-- Lemma 20.20.1: if `i : Z ⟶ X` is a closed immersion of topological spaces and `F` is an
abelian sheaf on `Z`, then the global degree-`p` cohomology of `F` on `Z` is canonically
isomorphic to the global degree-`p` cohomology of `i_* F` on `X`. -/
theorem global_cohomology_iso_pushforward_of_isClosedEmbedding
    (i : Z ⟶ X) (hi : Topology.IsClosedEmbedding i) (F : Z.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIsomorphic (F.H' p (⊤ : Opens Z))
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i).obj F).H' p (⊤ : Opens X)) := sorry

end Sheaf
end CategoryTheory
