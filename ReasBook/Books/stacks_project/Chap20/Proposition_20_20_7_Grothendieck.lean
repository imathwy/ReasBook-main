import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CategoryTheory
namespace Sheaf

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

-- Proof sketch: argue by induction on `d`. First use the finite decomposition of a Noetherian
-- space into irreducible components to reduce, via the short exact sequence for an open subset and
-- its closed complement together with Lemma `20.20.1`, to the case that `X` is irreducible. For
-- irreducible `X`, the case `d = 0` follows from Lemma `20.20.2`, and the case `d > 0` reduces by
-- Lemma `20.20.4` to extension-by-zero constant sheaves on opens, where the standard short exact
-- sequence with the constant sheaf on `X` and the induction hypothesis on the closed complement
-- gives the vanishing in degrees `p > d`.
/-- Proposition 20.20.7 (Grothendieck): if `X` is a Noetherian topological space of Krull
dimension at most `d`, then every abelian sheaf on `X` has vanishing global cohomology in degrees
strictly larger than `d`. -/
theorem isZero_higherCohomology_of_noetherianSpace_of_topologicalKrullDim_le
    (d : ℕ) (hXdim : topologicalKrullDim X ≤ d)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) {p : ℕ} (hp : d < p) :
    IsZero (F.H' p (⊤ : Opens X)) := sorry

end Sheaf
end CategoryTheory
