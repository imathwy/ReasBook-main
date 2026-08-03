module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.LinearAlgebra.Dual.Defs

public section

noncomputable section

namespace AlgebraicTopology

open CategoryTheory

/-- Helper for Remark 60.1: the integral singular chain complex of a topological
space, in a stable spelling for the dual construction below. -/
abbrev integralSingularChainComplex (X : TopCat) : ChainComplex (ModuleCat ℤ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X

/-- Helper for Remark 60.1: the integral singular cochains in one degree are the
integer-linear dual of the singular chains in that degree. -/
abbrev integralSingularCochainGroup (X : TopCat) (n : ℕ) : ModuleCat ℤ :=
  ModuleCat.of ℤ
    (Module.Dual ℤ ((integralSingularChainComplex X).X n))

/-- Helper for Remark 60.1: the singular coboundary is dual to the next singular
boundary map. -/
def integralSingularCoboundary (X : TopCat) (n : ℕ) :
    integralSingularCochainGroup X n ⟶ integralSingularCochainGroup X (n + 1) :=
  ModuleCat.ofHom
    (((integralSingularChainComplex X).d (n + 1) n).hom.dualMap)

/-- Helper for Remark 60.1: the integral singular coboundary evaluates by
precomposing a cochain with the singular boundary. -/
lemma integralSingularCoboundary_apply (X : TopCat) (n : ℕ)
    (φ : integralSingularCochainGroup X n)
    (x : (integralSingularChainComplex X).X (n + 1)) :
    integralSingularCoboundary X n φ x =
      φ (((integralSingularChainComplex X).d (n + 1) n) x) := by
  -- Expose the owner-side computation without unfolding the dual map downstream.
  rfl

/-- Helper for Remark 60.1: two consecutive integral singular coboundaries compose
to zero. -/
lemma integralSingularCoboundary_sq (X : TopCat) (n : ℕ) :
    integralSingularCoboundary X n ≫ integralSingularCoboundary X (n + 1) = 0 := by
  -- Dualize the square-zero identity for consecutive singular-chain boundaries.
  ext φ x
  simpa only [integralSingularCoboundary, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, LinearMap.dualMap_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero] using
    congrArg (fun f ↦ φ (f.hom x))
      ((integralSingularChainComplex X).d_comp_d (n + 1 + 1) (n + 1) n)

/-- Helper for Remark 60.1: the integral singular cochain complex of a topological
space. -/
@[expose]
def integralSingularCochainComplex (X : TopCat) : CochainComplex (ModuleCat ℤ) ℕ :=
  CochainComplex.of (integralSingularCochainGroup X)
    (integralSingularCoboundary X) (integralSingularCoboundary_sq X)

/-- Helper for Remark 60.1: the adjacent differential of the packaged
integral cochain complex is the named singular coboundary. -/
lemma integralSingularCochainComplex_d (X : TopCat) (n : ℕ) :
    (integralSingularCochainComplex X).d n (n + 1) =
      integralSingularCoboundary X n := by
  -- Apply the adjacent-differential computation rule of `CochainComplex.of`.
  simpa only [integralSingularCochainComplex] using
    (CochainComplex.of_d (integralSingularCochainGroup X)
      (integralSingularCoboundary X) n)

/-- Helper for Remark 60.1: the adjacent differential of the packaged
integral singular cochain complex evaluates by precomposition. -/
lemma integralSingularCochainComplex_d_apply (X : TopCat) (n : ℕ)
    (φ : integralSingularCochainGroup X n) :
    ((integralSingularCochainComplex X).d n (n + 1)).hom φ =
      φ.comp ((integralSingularChainComplex X).d (n + 1) n).hom := by
  -- Use the `CochainComplex.of` computation rule and the owner-side coboundary API.
  rw [integralSingularCochainComplex_d]
  apply LinearMap.ext
  intro x
  change integralSingularCoboundary X n φ x =
    φ (((integralSingularChainComplex X).d (n + 1) n) x)
  exact integralSingularCoboundary_apply X n φ x

/-- Helper for Remark 60.1: integral singular cohomology in degree `n`. -/
abbrev IntegralSingularCohomology (X : TopCat) (n : ℕ) :=
  (integralSingularCochainComplex X).homology n

/-- Helper for Remark 60.1: a continuous map acts contravariantly on each group of
integral singular cochains. -/
def integralSingularCochainMapComponent {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    integralSingularCochainGroup Y n ⟶ integralSingularCochainGroup X n :=
  ModuleCat.ofHom
    (((((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map f).f n).hom.dualMap)

/-- Helper for Remark 60.1: contravariant cochain components commute with the
singular coboundaries. -/
lemma integralSingularCochainMapComponent_comm {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    integralSingularCochainMapComponent f n ≫ integralSingularCoboundary X n =
      integralSingularCoboundary Y n ≫ integralSingularCochainMapComponent f (n + 1) := by
  -- Dualize the degree-`n` chain-map square for the singular-chain functor.
  ext φ x
  simpa only [integralSingularCochainMapComponent, integralSingularCoboundary,
    ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.dualMap_apply] using
    congrArg (fun g ↦ φ (g.hom x))
      (((((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map f).comm
        (n + 1) n).symm)

/-- Helper for Remark 60.1: the component commutation identity in the packaged
cochain-complex spelling. -/
lemma integralSingularCochainMap_comm {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    integralSingularCochainMapComponent f n ≫
        (integralSingularCochainComplex X).d n (n + 1) =
      (integralSingularCochainComplex Y).d n (n + 1) ≫
        integralSingularCochainMapComponent f (n + 1) := by
  -- Expose only the computation rule for a cochain complex built with `of`.
  simpa only [integralSingularCochainComplex, CochainComplex.of_d] using
    integralSingularCochainMapComponent_comm f n

/-- Helper for Remark 60.1: a continuous map induces the contravariant map of
integral singular cochain complexes. -/
def integralSingularCochainMap {X Y : TopCat} (f : X ⟶ Y) :
    integralSingularCochainComplex Y ⟶ integralSingularCochainComplex X :=
  CochainComplex.ofHom (fun n ↦ integralSingularCochainMapComponent f n)
    (integralSingularCochainMap_comm f)

/-- Helper for Remark 60.1: the identity map induces the identity on integral
singular cochains. -/
lemma integralSingularCochainMap_id (X : TopCat) :
    integralSingularCochainMap (𝟙 X) = 𝟙 (integralSingularCochainComplex X) := by
  -- Compare the cochain maps degreewise and evaluate the dual maps on chains.
  ext n φ
  apply LinearMap.ext
  intro x
  simp [integralSingularCochainMap, integralSingularCochainMapComponent,
    integralSingularChainComplex, ModuleCat.hom_id, LinearMap.id_apply]
  rfl

/-- Helper for Remark 60.1: integral singular cochain maps reverse composition. -/
lemma integralSingularCochainMap_comp {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    integralSingularCochainMap (f ≫ g) =
      integralSingularCochainMap g ≫ integralSingularCochainMap f := by
  -- Compare components and use functoriality of singular chains before dualizing.
  ext n φ
  apply LinearMap.ext
  intro x
  simp [integralSingularCochainMap, integralSingularCochainMapComponent,
    integralSingularChainComplex]
  rfl

/-- Helper for Remark 60.1: the cochain maps induced by the two sides of a
homeomorphism cancel in the forward order. -/
lemma integralSingularCochainMap_hom_inv_id {X Y : TopCat} (e : X ≅ Y) :
    integralSingularCochainMap e.inv ≫ integralSingularCochainMap e.hom =
      𝟙 (integralSingularCochainComplex X) := by
  -- Reverse functoriality turns the composite into the map of `e.hom ≫ e.inv`.
  rw [← integralSingularCochainMap_comp, e.hom_inv_id,
    integralSingularCochainMap_id]

/-- Helper for Remark 60.1: the cochain maps induced by the two sides of a
homeomorphism cancel in the reverse order. -/
lemma integralSingularCochainMap_inv_hom_id {X Y : TopCat} (e : X ≅ Y) :
    integralSingularCochainMap e.hom ≫ integralSingularCochainMap e.inv =
      𝟙 (integralSingularCochainComplex Y) := by
  -- Reverse functoriality turns the composite into the map of `e.inv ≫ e.hom`.
  rw [← integralSingularCochainMap_comp, e.inv_hom_id,
    integralSingularCochainMap_id]

/-- Helper for Remark 60.1: a homeomorphism induces an isomorphism of integral
singular cochain complexes. -/
def integralSingularCochainMapIso {X Y : TopCat} (e : X ≅ Y) :
    integralSingularCochainComplex X ≅ integralSingularCochainComplex Y :=
  { hom := integralSingularCochainMap e.inv
    inv := integralSingularCochainMap e.hom
    hom_inv_id := integralSingularCochainMap_hom_inv_id e
    inv_hom_id := integralSingularCochainMap_inv_hom_id e }

/-- Helper for Remark 60.1: a homeomorphism transports integral singular
cohomology in every degree. -/
def integralSingularCohomologyMapIso {X Y : TopCat} (e : X ≅ Y) (n : ℕ) :
    IntegralSingularCohomology X n ≅ IntegralSingularCohomology Y n :=
  HomologicalComplex.homologyMapIso (integralSingularCochainMapIso e) n

end AlgebraicTopology
