module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory

/-- Helper for Theorem 63.8: the mod-two singular chain complex of a topological space. -/
abbrev modTwoSingularChainComplex (X : TopCat) :
    ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  ((singularChainComplexFunctor (ModuleCat (ZMod 2))).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))).obj X

/-- Helper for Theorem 63.8: mod-two singular cochains in one degree are the
linear dual of mod-two singular chains. -/
abbrev modTwoSingularCochainGroup (X : TopCat) (n : ℕ) : ModuleCat (ZMod 2) :=
  ModuleCat.of (ZMod 2)
    (Module.Dual (ZMod 2) ((modTwoSingularChainComplex X).X n))

/-- Helper for Theorem 63.8: the mod-two singular coboundary is dual to the next
singular boundary map. -/
@[expose]
def modTwoSingularCoboundary (X : TopCat) (n : ℕ) :
    modTwoSingularCochainGroup X n ⟶ modTwoSingularCochainGroup X (n + 1) :=
  ModuleCat.ofHom
    (((modTwoSingularChainComplex X).d (n + 1) n).hom.dualMap)

/-- Helper for Theorem 63.8: the underlying linear map of the mod-two singular
coboundary is the dual of the adjacent singular boundary. -/
lemma modTwoSingularCoboundary_hom (X : TopCat) (n : ℕ) :
    (modTwoSingularCoboundary X n).hom =
      ((modTwoSingularChainComplex X).d (n + 1) n).hom.dualMap := by
  -- Expose the defining computation without unfolding the cochain construction downstream.
  rfl

/-- Helper for Theorem 63.8: two consecutive mod-two singular coboundaries
compose to zero. -/
lemma modTwoSingularCoboundary_sq (X : TopCat) (n : ℕ) :
    modTwoSingularCoboundary X n ≫ modTwoSingularCoboundary X (n + 1) = 0 := by
  -- Dualize the square-zero identity for consecutive singular-chain boundaries.
  ext φ x
  simpa only [modTwoSingularCoboundary, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, LinearMap.dualMap_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero] using
    congrArg (fun f ↦ φ (f.hom x))
      ((modTwoSingularChainComplex X).d_comp_d (n + 1 + 1) (n + 1) n)

/-- Helper for Theorem 63.8: the mod-two singular cochain complex of a
topological space. -/
@[expose]
def modTwoSingularCochainComplex (X : TopCat) :
    CochainComplex (ModuleCat (ZMod 2)) ℕ :=
  CochainComplex.of (modTwoSingularCochainGroup X)
    (modTwoSingularCoboundary X) (modTwoSingularCoboundary_sq X)

/-- Helper for Theorem 63.8: the packaged mod-two singular cochain differential
in adjacent degrees is the defining coboundary. -/
lemma modTwoSingularCochainComplex_d (X : TopCat) (n : ℕ) :
    (modTwoSingularCochainComplex X).d n (n + 1) =
      modTwoSingularCoboundary X n := by
  -- Compute the adjacent differential of the complex built with `CochainComplex.of`.
  simp only [modTwoSingularCochainComplex, CochainComplex.of_d]

/-- Helper for Theorem 63.8: mod-two singular cohomology in degree `n`. -/
abbrev ModTwoSingularCohomology (X : TopCat) (n : ℕ) :=
  (modTwoSingularCochainComplex X).homology n

/-- Helper for Theorem 63.8: a continuous map acts contravariantly on each
group of mod-two singular cochains. -/
def modTwoSingularCochainMapComponent {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    modTwoSingularCochainGroup Y n ⟶ modTwoSingularCochainGroup X n :=
  ModuleCat.ofHom
    (((((singularChainComplexFunctor (ModuleCat (ZMod 2))).obj
      (ModuleCat.of (ZMod 2) (ZMod 2))).map f).f n).hom.dualMap)

/-- Helper for Theorem 63.8: contravariant mod-two cochain components commute
with the singular coboundaries. -/
lemma modTwoSingularCochainMapComponent_comm {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    modTwoSingularCochainMapComponent f n ≫ modTwoSingularCoboundary X n =
      modTwoSingularCoboundary Y n ≫ modTwoSingularCochainMapComponent f (n + 1) := by
  -- Dualize the degree-`n` chain-map square for the singular-chain functor.
  ext φ x
  simpa only [modTwoSingularCochainMapComponent, modTwoSingularCoboundary,
    ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.dualMap_apply] using
    congrArg (fun g ↦ φ (g.hom x))
      (((((singularChainComplexFunctor (ModuleCat (ZMod 2))).obj
        (ModuleCat.of (ZMod 2) (ZMod 2))).map f).comm (n + 1) n).symm)

/-- Helper for Theorem 63.8: the cochain-map commutation identity in the
packaged cochain-complex spelling. -/
lemma modTwoSingularCochainMap_comm {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    modTwoSingularCochainMapComponent f n ≫
        (modTwoSingularCochainComplex X).d n (n + 1) =
      (modTwoSingularCochainComplex Y).d n (n + 1) ≫
        modTwoSingularCochainMapComponent f (n + 1) := by
  -- Expose only the computation rule for a cochain complex built with `of`.
  simpa only [modTwoSingularCochainComplex, CochainComplex.of_d] using
    modTwoSingularCochainMapComponent_comm f n

/-- Helper for Theorem 63.8: a continuous map induces the contravariant map of
mod-two singular cochain complexes. -/
def modTwoSingularCochainMap {X Y : TopCat} (f : X ⟶ Y) :
    modTwoSingularCochainComplex Y ⟶ modTwoSingularCochainComplex X :=
  CochainComplex.ofHom (fun n ↦ modTwoSingularCochainMapComponent f n)
    (modTwoSingularCochainMap_comm f)

/-- Helper for Theorem 63.8: the identity map induces the identity on mod-two
singular cochains. -/
lemma modTwoSingularCochainMap_id (X : TopCat) :
    modTwoSingularCochainMap (𝟙 X) = 𝟙 (modTwoSingularCochainComplex X) := by
  -- Compare the cochain maps degreewise and evaluate their dual maps on chains.
  ext n φ
  apply LinearMap.ext
  intro x
  simp [modTwoSingularCochainMap, modTwoSingularCochainMapComponent,
    modTwoSingularChainComplex, ModuleCat.hom_id, LinearMap.id_apply]
  rfl

/-- Helper for Theorem 63.8: mod-two singular cochain maps reverse composition. -/
lemma modTwoSingularCochainMap_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modTwoSingularCochainMap (f ≫ g) =
      modTwoSingularCochainMap g ≫ modTwoSingularCochainMap f := by
  -- Compare components and use singular-chain functoriality before dualizing.
  ext n φ
  apply LinearMap.ext
  intro x
  simp [modTwoSingularCochainMap, modTwoSingularCochainMapComponent,
    modTwoSingularChainComplex]
  rfl

/-- Helper for Theorem 63.8: the cochain maps from the two sides of a
homeomorphism cancel in the forward order. -/
lemma modTwoSingularCochainMap_hom_inv_id {X Y : TopCat} (e : X ≅ Y) :
    modTwoSingularCochainMap e.inv ≫ modTwoSingularCochainMap e.hom =
      𝟙 (modTwoSingularCochainComplex X) := by
  -- Reverse functoriality turns the composite into the map of `e.hom ≫ e.inv`.
  rw [← modTwoSingularCochainMap_comp, e.hom_inv_id,
    modTwoSingularCochainMap_id]

/-- Helper for Theorem 63.8: the cochain maps from the two sides of a
homeomorphism cancel in the reverse order. -/
lemma modTwoSingularCochainMap_inv_hom_id {X Y : TopCat} (e : X ≅ Y) :
    modTwoSingularCochainMap e.hom ≫ modTwoSingularCochainMap e.inv =
      𝟙 (modTwoSingularCochainComplex Y) := by
  -- Reverse functoriality turns the composite into the map of `e.inv ≫ e.hom`.
  rw [← modTwoSingularCochainMap_comp, e.inv_hom_id,
    modTwoSingularCochainMap_id]

/-- Helper for Theorem 63.8: a homeomorphism induces an isomorphism of mod-two
singular cochain complexes. -/
def modTwoSingularCochainMapIso {X Y : TopCat} (e : X ≅ Y) :
    modTwoSingularCochainComplex X ≅ modTwoSingularCochainComplex Y :=
  { hom := modTwoSingularCochainMap e.inv
    inv := modTwoSingularCochainMap e.hom
    hom_inv_id := modTwoSingularCochainMap_hom_inv_id e
    inv_hom_id := modTwoSingularCochainMap_inv_hom_id e }

/-- Helper for Theorem 63.8: a homeomorphism transports mod-two singular
cohomology in every degree. -/
def modTwoSingularCohomologyMapIso {X Y : TopCat} (e : X ≅ Y) (n : ℕ) :
    ModTwoSingularCohomology X n ≅ ModTwoSingularCohomology Y n :=
  HomologicalComplex.homologyMapIso (modTwoSingularCochainMapIso e) n

end AlgebraicTopology

end
