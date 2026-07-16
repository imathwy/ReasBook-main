import Mathlib
import StacksProject_2024.stacks_project.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open TopCat
open TopCat.Sheaf
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable {O : X.Sheaf CommRingCat.{u}}
variable [(Opens.grothendieckTopology X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]

/-- The category of cochain complexes of sheaves of `O`-modules on the opens site of `X`. -/
abbrev moduleComplex (O : X.Sheaf CommRingCat.{u}) :=
  CochainComplex (ringedSiteModuleCategory (Opens.grothendieckTopology X) O) ℤ

/-- The linearized six-term cohomology segment attached to a morphism
`c : f^*NL_{Y/Z} ⟶ Cone(NL_{X/Z} ⟶ NL_{X/Y})[-1]`. It is written as
`H^{-1}(f^*NL_{Y/Z}) ⟶ H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) ⟶ H^0(f^*NL_{Y/Z}) ⟶
H^0(NL_{X/Z}) ⟶ H^0(NL_{X/Y})`. -/
noncomputable def naiveCotangent_six_term_segment
    (pullbackNaiveCotangent naiveCotangentXZ naiveCotangentXY : moduleComplex O)
    (comparison : naiveCotangentXZ ⟶ naiveCotangentXY)
    [HomologicalComplex.HasHomotopyCofiber comparison]
    (c : pullbackNaiveCotangent ⟶ CochainComplex.mappingCocone comparison)
    [hc0 : IsIso (HomologicalComplex.homologyMap c 0)] :
    ComposableArrows (ringedSiteModuleCategory (Opens.grothendieckTopology X) O) 5 :=
  mk₅
    (HomologicalComplex.homologyMap (c ≫ CochainComplex.mappingCocone.fst comparison) (-1))
    (HomologicalComplex.homologyMap comparison (-1))
    (CochainComplex.homologyδOfTriangle (CochainComplex.mappingCocone.triangle comparison) (-1) 0 ≫
      @inv _ _ _ _ (HomologicalComplex.homologyMap c 0) hc0)
    (HomologicalComplex.homologyMap (c ≫ CochainComplex.mappingCocone.fst comparison) 0)
    (HomologicalComplex.homologyMap comparison 0)

-- Proof sketch: compare the standard exact five-arrow homology segment of the mapping-cocone
-- triangle for `comparison` with the segment obtained by transporting the cocone term along `c`.
-- The isomorphism on `H^0` transports the boundary map, and the epimorphism on `H^{-1}` preserves
-- the image of the first map.
/-- Lemma 17.31.7 (1): for a chosen transitivity map
`f^*NL_{Y/Z} ⟶ Cone(NL_{X/Z} ⟶ NL_{X/Y})[-1]` whose induced map on `H^0` is an isomorphism and on
`H^{-1}` is an epimorphism, the associated six-term cohomology segment
`H^{-1}(f^*NL_{Y/Z}) ⟶ H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) ⟶ H^0(f^*NL_{Y/Z}) ⟶
H^0(NL_{X/Z}) ⟶ H^0(NL_{X/Y})`
is exact. -/
theorem naiveCotangent_six_term_segment_exact
    (pullbackNaiveCotangent naiveCotangentXZ naiveCotangentXY : moduleComplex O)
    (comparison : naiveCotangentXZ ⟶ naiveCotangentXY)
    [HomologicalComplex.HasHomotopyCofiber comparison]
    (c : pullbackNaiveCotangent ⟶ CochainComplex.mappingCocone comparison)
    [hc0 : IsIso (HomologicalComplex.homologyMap c 0)]
    [Epi (HomologicalComplex.homologyMap c (-1))] :
    (naiveCotangent_six_term_segment
      pullbackNaiveCotangent naiveCotangentXZ naiveCotangentXY comparison c).Exact := sorry

-- Proof sketch: the long exact homology sequence of the mapping-cocone triangle ends with
-- `H^0(NL_{X/Z}) ⟶ H^0(NL_{X/Y}) ⟶ H^1(Cone(NL_{X/Z} ⟶ NL_{X/Y})[-1])`. Transport the last term
-- across the `H^0`-isomorphism induced by `c`, and use the vanishing of `H^1(f^*NL_{Y/Z})`.
/-- Lemma 17.31.7 (2): if `H^1(f^*NL_{Y/Z}) = 0`, then the final map
`H^0(NL_{X/Z}) ⟶ H^0(NL_{X/Y})` in the six-term sequence is an epimorphism, i.e. the displayed
sequence continues with `H^0(NL_{X/Y}) ⟶ 0`. -/
theorem naiveCotangent_h0_map_epi
    (pullbackNaiveCotangent naiveCotangentXZ naiveCotangentXY : moduleComplex O)
    (comparison : naiveCotangentXZ ⟶ naiveCotangentXY)
    [HomologicalComplex.HasHomotopyCofiber comparison]
    (c : pullbackNaiveCotangent ⟶ CochainComplex.mappingCocone comparison)
    [hc0 : IsIso (HomologicalComplex.homologyMap c 0)]
    (hH1 : Limits.IsZero (HomologicalComplex.homology pullbackNaiveCotangent 1)) :
    Epi (HomologicalComplex.homologyMap comparison 0) := sorry

end TopCat.Sheaf
