import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ComposableArrows
open AlgebraicGeometry
open TopCat
open TopCat.Sheaf

noncomputable section

universe u

/-- The structure sheaf of a ringed space, viewed as a sheaf with values in `RingCat`. -/
abbrev ringedSpaceRingCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj X.sheaf

/-- The category of `\mathcal O_X`-module cochain complexes attached to a ringed space `X`. -/
abbrev ringedSpaceModuleComplex (X : RingedSpace.{u}) :=
  CochainComplex (SheafOfModules (ringedSpaceRingCatSheaf X)) ℤ

/-- The linearized six-term cohomology segment attached to a morphism
`c : f^*NL_{Y/Z} ⟶ Cone(NL_{X/Z} ⟶ NL_{X/Y})[-1]`. It is written as
`H^{-1}(f^*NL_{Y/Z}) ⟶ H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) ⟶ H^0(f^*NL_{Y/Z}) ⟶
H^0(NL_{X/Z}) ⟶ H^0(NL_{X/Y})`. -/
noncomputable def ringedSpace_naiveCotangent_six_term_segment
    {X : RingedSpace.{u}}
    (pullbackNaiveCotangent naiveCotangentXZ naiveCotangentXY : ringedSpaceModuleComplex X)
    (comparison : naiveCotangentXZ ⟶ naiveCotangentXY)
    [HomologicalComplex.HasHomotopyCofiber comparison]
    (c : pullbackNaiveCotangent ⟶ CochainComplex.mappingCocone comparison)
    [hc0 : IsIso (HomologicalComplex.homologyMap c 0)] :
    ComposableArrows (SheafOfModules (ringedSpaceRingCatSheaf X)) 5 :=
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
theorem ringedSpace_naiveCotangent_six_term_segment_exact
    {X : RingedSpace.{u}}
    (pullbackNaiveCotangent naiveCotangentXZ naiveCotangentXY : ringedSpaceModuleComplex X)
    (comparison : naiveCotangentXZ ⟶ naiveCotangentXY)
    [HomologicalComplex.HasHomotopyCofiber comparison]
    (c : pullbackNaiveCotangent ⟶ CochainComplex.mappingCocone comparison)
    [hc0 : IsIso (HomologicalComplex.homologyMap c 0)]
    [Epi (HomologicalComplex.homologyMap c (-1))] :
    (ringedSpace_naiveCotangent_six_term_segment
      pullbackNaiveCotangent naiveCotangentXZ naiveCotangentXY comparison c).Exact := sorry

-- Proof sketch: the long exact homology sequence of the mapping-cocone triangle ends with
-- `H^0(NL_{X/Z}) ⟶ H^0(NL_{X/Y}) ⟶ H^1(Cone(NL_{X/Z} ⟶ NL_{X/Y})[-1])`. Transport the last term
-- across the `H^0`-isomorphism induced by `c`, and use the vanishing of `H^1(f^*NL_{Y/Z})`.
/-- Lemma 17.31.7 (2): if `H^1(f^*NL_{Y/Z}) = 0`, then the final map
`H^0(NL_{X/Z}) ⟶ H^0(NL_{X/Y})` in the six-term sequence is an epimorphism, i.e. the displayed
sequence continues with `H^0(NL_{X/Y}) ⟶ 0`. -/
theorem ringedSpace_naiveCotangent_h0_map_epi
    {X : RingedSpace.{u}}
    (pullbackNaiveCotangent naiveCotangentXZ naiveCotangentXY : ringedSpaceModuleComplex X)
    (comparison : naiveCotangentXZ ⟶ naiveCotangentXY)
    [HomologicalComplex.HasHomotopyCofiber comparison]
    (c : pullbackNaiveCotangent ⟶ CochainComplex.mappingCocone comparison)
    [hc0 : IsIso (HomologicalComplex.homologyMap c 0)]
    (hH1 : Limits.IsZero (HomologicalComplex.homology pullbackNaiveCotangent 1)) :
    Epi (HomologicalComplex.homologyMap comparison 0) := sorry
