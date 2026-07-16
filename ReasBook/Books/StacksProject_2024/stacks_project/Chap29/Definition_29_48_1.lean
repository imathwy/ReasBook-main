import StacksProject_2024.stacks_project.Chap18.Definition_18_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}}

local notation "SiteFiniteLocallyFree" =>
  @SheafOfModules.RingedSite.IsFiniteLocallyFree
    (Opens S) _ (Opens.grothendieckTopology S) S.sheaf _
local notation "SiteFiniteLocallyFreeOfRank" =>
  @SheafOfModules.RingedSite.IsFiniteLocallyFreeOfRank
    (Opens S) _ (Opens.grothendieckTopology S) S.sheaf _

namespace Scheme.Hom

/-- The direct image `f_* \mathcal O_X`, viewed as an `\mathcal O_S`-module. -/
noncomputable abbrev pushforwardStructureSheafModule (f : X ⟶ S) : S.Modules :=
  (Scheme.Modules.pushforward f).obj
    (SheafOfModules.unit X.ringCatSheaf : X.Modules)

end Scheme.Hom

-- Semantic recall / analogue check:
-- - `lean_leansearch` surfaced the scheme-level owners `IsAffineHom` and
--   `Scheme.Modules.pushforward`, but no existing scheme-morphism owner for “finite locally free”;
-- - the canonical sheaf-side owners live in Chapter 18 as the opens-site predicates
--   `SheafOfModules.RingedSite.IsFiniteLocallyFree` and
--   `SheafOfModules.RingedSite.IsFiniteLocallyFreeOfRank`;
-- - the source-facing owner here is therefore a morphism property asserting affineness together
--   with finite local freeness of the pushforward structure sheaf.

/-- Definition 29.48.1 (1): a morphism of schemes `f : X ⟶ S` is finite locally free if `f` is
affine and the pushforward `f_* \mathcal O_X` is a finite locally free `\mathcal O_S`-module. -/
class IsFiniteLocallyFree (f : X ⟶ S) : Prop extends IsAffineHom f where
  /-- The pushforward of the structure sheaf along a finite locally free morphism is finite
  locally free as an `\mathcal O_S`-module. -/
  pushforwardStructureSheafModule_isFiniteLocallyFree :
    SiteFiniteLocallyFree f.pushforwardStructureSheafModule

/-- For a finite locally free morphism, the pushforward structure sheaf is finite locally free. -/
instance (f : X ⟶ S) [h : IsFiniteLocallyFree f] :
    SiteFiniteLocallyFree f.pushforwardStructureSheafModule :=
  h.pushforwardStructureSheafModule_isFiniteLocallyFree

/-- Definition 29.48.1 (2): a finite locally free morphism `f : X ⟶ S` has rank or degree `d` if
the pushforward `f_* \mathcal O_X` is finite locally free of rank `d` as an `\mathcal O_S`-module.
-/
class IsFiniteLocallyFreeOfRank (f : X ⟶ S) (d : ℕ) : Prop extends IsFiniteLocallyFree f where
  /-- The pushforward structure sheaf of a degree-`d` finite locally free morphism has rank `d`.
  -/
  pushforwardStructureSheafModule_isFiniteLocallyFreeOfRank :
    SiteFiniteLocallyFreeOfRank d f.pushforwardStructureSheafModule

/-- A finite locally free morphism of rank `d` is finite locally free. -/
theorem isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank (f : X ⟶ S) (d : ℕ)
    [h : IsFiniteLocallyFreeOfRank f d] : IsFiniteLocallyFree f :=
  inferInstance

/-- For a finite locally free morphism of rank `d`, the pushforward structure sheaf is finite
locally free of rank `d`. -/
instance (f : X ⟶ S) (d : ℕ) [h : IsFiniteLocallyFreeOfRank f d] :
    SiteFiniteLocallyFreeOfRank d f.pushforwardStructureSheafModule :=
  h.pushforwardStructureSheafModule_isFiniteLocallyFreeOfRank

end

end AlgebraicGeometry
