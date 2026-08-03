module

public import Topology_Munkres_2000.Book.Exercise_79_4
public import Topology_Munkres_2000.Book.Theorem_79_1
public import Topology_Munkres_2000.Book.Exercise_54_8
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Covering.Basic

public section

universe u

noncomputable section

namespace TorusAutomorphism

/-- Helper for Exercise 79.5: the first standard generator of the integer-coordinate group of
the torus. -/
def firstGenerator : Multiplicative ℤ × Multiplicative ℤ :=
  (Multiplicative.ofAdd 1, 1)

/-- Helper for Exercise 79.5: the second standard generator of the integer-coordinate group of
the torus. -/
def secondGenerator : Multiplicative ℤ × Multiplicative ℤ :=
  (1, Multiplicative.ofAdd 1)

/-- Helper for Exercise 79.5: the monomial torus map associated to an endomorphism of its
integer-coordinate group, in the first circle coordinate. -/
def firstCoordinateMap
    (φ : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ × Multiplicative ℤ) :
    C(Circle × Circle, Circle) :=
  ((CircleMap.zpower ((φ firstGenerator).1.toAdd)).comp ContinuousMap.fst) *
    ((CircleMap.zpower ((φ secondGenerator).1.toAdd)).comp ContinuousMap.snd)

/-- Helper for Exercise 79.5: the monomial torus map associated to an endomorphism of its
integer-coordinate group, in the second circle coordinate. -/
def secondCoordinateMap
    (φ : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ × Multiplicative ℤ) :
    C(Circle × Circle, Circle) :=
  ((CircleMap.zpower ((φ firstGenerator).2.toAdd)).comp ContinuousMap.fst) *
    ((CircleMap.zpower ((φ secondGenerator).2.toAdd)).comp ContinuousMap.snd)

/-- Helper for Exercise 79.5: the monomial torus map associated to an endomorphism of its
integer-coordinate group. -/
def continuousMap
    (φ : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ × Multiplicative ℤ) :
    C(Circle × Circle, Circle × Circle) :=
  (firstCoordinateMap φ).prodMk (secondCoordinateMap φ)

/-- Helper for Exercise 79.5: evaluation of the monomial torus map in the two standard
coordinates. -/
lemma continuousMap_apply
    (φ : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ × Multiplicative ℤ)
    (z w : Circle) :
    continuousMap φ (z, w) =
      (z ^ ((φ firstGenerator).1.toAdd) * w ^ ((φ secondGenerator).1.toAdd),
        z ^ ((φ firstGenerator).2.toAdd) * w ^ ((φ secondGenerator).2.toAdd)) := by
  -- Unfold only the map interface; the continuous-map operations then evaluate pointwise.
  simp [continuousMap, firstCoordinateMap, secondCoordinateMap, CircleMap.zpower_apply]

/-- Helper for Exercise 79.5: every integer-coordinate pair is the product of powers of the two
standard generators. -/
private lemma generator_decomposition (x : Multiplicative ℤ × Multiplicative ℤ) :
    firstGenerator ^ x.1.toAdd * secondGenerator ^ x.2.toAdd = x := by
  -- Check the two integer coordinates separately.
  ext
  · simp [firstGenerator, secondGenerator]
  · simp [firstGenerator, secondGenerator]

/-- Helper for Exercise 79.5: the first coordinate of a homomorphism on `ℤ × ℤ` is the
integer linear combination of its values on the standard generators. -/
private lemma firstCoordinate_apply
    (φ : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ × Multiplicative ℤ)
    (x : Multiplicative ℤ × Multiplicative ℤ) :
    (φ x).1.toAdd =
      x.1.toAdd * (φ firstGenerator).1.toAdd +
        x.2.toAdd * (φ secondGenerator).1.toAdd := by
  -- Expand `x` in the standard basis and apply the homomorphism coordinatewise.
  have hmap : φ x =
      φ firstGenerator ^ x.1.toAdd * φ secondGenerator ^ x.2.toAdd := by
    rw [← map_zpow, ← map_zpow, ← map_mul, generator_decomposition]
  have hcoordinate := congrArg (fun y ↦ y.1.toAdd) hmap
  simpa [toAdd_zpow, zsmul_eq_mul, mul_comm] using hcoordinate

/-- Helper for Exercise 79.5: the second coordinate of a homomorphism on `ℤ × ℤ` is the
integer linear combination of its values on the standard generators. -/
private lemma secondCoordinate_apply
    (φ : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ × Multiplicative ℤ)
    (x : Multiplicative ℤ × Multiplicative ℤ) :
    (φ x).2.toAdd =
      x.1.toAdd * (φ firstGenerator).2.toAdd +
        x.2.toAdd * (φ secondGenerator).2.toAdd := by
  -- The same basis expansion computes the second coordinate.
  have hmap : φ x =
      φ firstGenerator ^ x.1.toAdd * φ secondGenerator ^ x.2.toAdd := by
    rw [← map_zpow, ← map_zpow, ← map_mul, generator_decomposition]
  have hcoordinate := congrArg (fun y ↦ y.2.toAdd) hmap
  simpa [toAdd_zpow, zsmul_eq_mul, mul_comm] using hcoordinate

/-- Helper for Exercise 79.5: a homomorphism of the integer-coordinate group acts by the two
monomials determined by its values on the standard generators. -/
private lemma apply_eq_monomials
    (φ : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ × Multiplicative ℤ)
    (x : Multiplicative ℤ × Multiplicative ℤ) :
    φ x =
      (x.1 ^ (φ firstGenerator).1.toAdd * x.2 ^ (φ secondGenerator).1.toAdd,
        x.1 ^ (φ firstGenerator).2.toAdd * x.2 ^ (φ secondGenerator).2.toAdd) := by
  -- Equality in each multiplicative integer coordinate is detected after applying `toAdd`.
  apply Prod.ext
  · apply Multiplicative.ext
    rw [firstCoordinate_apply]
    simp only [toAdd_mul, Int.toAdd_zpow]
  · apply Multiplicative.ext
    rw [secondCoordinate_apply]
    simp only [toAdd_mul, Int.toAdd_zpow]

/-- Helper for Exercise 79.5: the monomial construction turns composition of integer-coordinate
homomorphisms into composition of torus maps. -/
lemma continuousMap_comp
    (φ ψ : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ × Multiplicative ℤ) :
    continuousMap ψ ∘ continuousMap φ = continuousMap (ψ.comp φ) := by
  -- Evaluate both maps, collect the four integer exponents, and identify them using the
  -- coordinate formulas for the composite homomorphism.
  funext x
  rcases x with ⟨z, w⟩
  have hfirstOne := firstCoordinate_apply ψ (φ firstGenerator)
  have hfirstTwo := firstCoordinate_apply ψ (φ secondGenerator)
  have hsecondOne := secondCoordinate_apply ψ (φ firstGenerator)
  have hsecondTwo := secondCoordinate_apply ψ (φ secondGenerator)
  rw [Function.comp_apply, continuousMap_apply, continuousMap_apply, continuousMap_apply]
  apply Prod.ext
  · simp only [mul_zpow, ← zpow_mul]
    rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add, ← hfirstOne, ← hfirstTwo]
    rfl
  · simp only [mul_zpow, ← zpow_mul]
    rw [mul_mul_mul_comm, ← zpow_add, ← zpow_add, ← hsecondOne, ← hsecondTwo]
    rfl

/-- Helper for Exercise 79.5: the monomial torus map of the identity integer-coordinate
homomorphism is the identity map. -/
lemma continuousMap_id :
    continuousMap (MonoidHom.id (Multiplicative ℤ × Multiplicative ℤ)) =
      ContinuousMap.id (Circle × Circle) := by
  -- The two standard basis columns give exponents `(1, 0)` and `(0, 1)`.
  apply ContinuousMap.ext
  intro x
  rcases x with ⟨z, w⟩
  rw [continuousMap_apply]
  simp [firstGenerator, secondGenerator]

/-- Helper for Exercise 79.5: the monomial maps attached to inverse integer-coordinate
isomorphisms are inverse functions. -/
lemma continuousMap_inverse
    (φ : Multiplicative ℤ × Multiplicative ℤ ≃* Multiplicative ℤ × Multiplicative ℤ) :
    Function.LeftInverse (continuousMap φ.symm.toMonoidHom) (continuousMap φ.toMonoidHom) ∧
      Function.RightInverse (continuousMap φ.symm.toMonoidHom)
        (continuousMap φ.toMonoidHom) := by
  -- Functoriality reduces both inverse laws to the corresponding inverse laws of `φ`.
  have hleft : φ.symm.toMonoidHom.comp φ.toMonoidHom =
      MonoidHom.id (Multiplicative ℤ × Multiplicative ℤ) := by
    exact DFunLike.ext _ _ φ.symm_apply_apply
  have hright : φ.toMonoidHom.comp φ.symm.toMonoidHom =
      MonoidHom.id (Multiplicative ℤ × Multiplicative ℤ) := by
    exact DFunLike.ext _ _ φ.apply_symm_apply
  constructor
  · intro x
    have hcomp := congrFun (continuousMap_comp φ.toMonoidHom φ.symm.toMonoidHom) x
    rw [hleft, continuousMap_id] at hcomp
    exact hcomp
  · intro x
    have hcomp := congrFun (continuousMap_comp φ.symm.toMonoidHom φ.toMonoidHom) x
    rw [hright, continuousMap_id] at hcomp
    exact hcomp

/-- Helper for Exercise 79.5: an integer-coordinate automorphism determines a monomial
self-homeomorphism of the torus. -/
def homeomorph
    (φ : Multiplicative ℤ × Multiplicative ℤ ≃* Multiplicative ℤ × Multiplicative ℤ) :
    Circle × Circle ≃ₜ Circle × Circle :=
  { toFun := continuousMap φ.toMonoidHom
    invFun := continuousMap φ.symm.toMonoidHom
    left_inv := (continuousMap_inverse φ).1
    right_inv := (continuousMap_inverse φ).2
    continuous_toFun := (continuousMap φ.toMonoidHom).continuous
    continuous_invFun := (continuousMap φ.symm.toMonoidHom).continuous }

/-- Helper for Exercise 79.5: every monomial torus map fixes the standard basepoint. -/
lemma continuousMap_basepoint
    (φ : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ × Multiplicative ℤ) :
    continuousMap φ (1, 1) = (1, 1) := by
  -- Every integer power of `1` is `1` in both coordinates.
  rw [continuousMap_apply]
  simp

/-- Helper for Exercise 79.5: the first coordinate of a monomial torus map fixes `1`. -/
private lemma firstCoordinateMap_basepoint
    (φ : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ × Multiplicative ℤ) :
    firstCoordinateMap φ (1, 1) = 1 := by
  -- Both monomial factors evaluate to `1`.
  simp [firstCoordinateMap, CircleMap.zpower_apply]

/-- Helper for Exercise 79.5: the second coordinate of a monomial torus map fixes `1`. -/
private lemma secondCoordinateMap_basepoint
    (φ : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ × Multiplicative ℤ) :
    secondCoordinateMap φ (1, 1) = 1 := by
  -- Both monomial factors evaluate to `1`.
  simp [secondCoordinateMap, CircleMap.zpower_apply]

/-- Helper for Exercise 79.5: projecting the induced map of a product-valued based map recovers
the induced map of its first coordinate. -/
private lemma projLeft_mapOfEq_prodMk {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (x : X) (y : Y) (z : Z) (f : C(X, Y)) (g : C(X, Z))
    (hf : f x = y) (_hg : g x = z) (hfg : f.prodMk g x = (y, z))
    (a : FundamentalGroup X x) :
    Path.Homotopic.projLeft (FundamentalGroup.mapOfEq (f.prodMk g) hfg a) =
      FundamentalGroup.mapOfEq f hf a := by
  -- On a representative loop, projection cancels the product constructor pointwise.
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_cast, ← Path.Homotopic.Quotient.mk_cast]
      rfl

/-- Helper for Exercise 79.5: projecting the induced map of a product-valued based map recovers
the induced map of its second coordinate. -/
private lemma projRight_mapOfEq_prodMk {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (x : X) (y : Y) (z : Z) (f : C(X, Y)) (g : C(X, Z))
    (_hf : f x = y) (hg : g x = z) (hfg : f.prodMk g x = (y, z))
    (a : FundamentalGroup X x) :
    Path.Homotopic.projRight (FundamentalGroup.mapOfEq (f.prodMk g) hfg a) =
      FundamentalGroup.mapOfEq g hg a := by
  -- The second projection is the symmetric pointwise computation.
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_cast, ← Path.Homotopic.Quotient.mk_cast]
      rfl

/-- Helper for Exercise 79.5: based fundamental-group maps preserve composition, independently
of the chosen proofs of the endpoint equations. -/
private lemma mapOfEq_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) (hgf : (g.comp f) x = z) :
    (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf) =
      FundamentalGroup.mapOfEq (g.comp f) hgf := by
  -- Normalize the intermediate and target basepoints, then use functoriality of quotient maps.
  subst y
  subst z
  have hg_rfl : hg = rfl := Subsingleton.elim _ _
  cases hg_rfl
  ext a
  simp only [MonoidHom.coe_comp, Function.comp_apply, FundamentalGroup.mapOfEq_apply,
    Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.Quotient.map_comp]
  apply eq_of_heq
  exact Path.Homotopic.Quotient.cast_heq _ _

/-- Helper for Exercise 79.5: the based map induced by the first projection is the first
projection of loop classes. -/
private lemma mapOfEq_fst_apply (a : FundamentalGroup (Circle × Circle) (1, 1)) :
    FundamentalGroup.mapOfEq ContinuousMap.fst rfl a = Path.Homotopic.projLeft a := by
  -- The endpoint cast is reflexive, so the quotient map is exactly the projected loop.
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  unfold Path.Homotopic.projLeft
  congr

/-- Helper for Exercise 79.5: the based map induced by the second projection is the second
projection of loop classes. -/
private lemma mapOfEq_snd_apply (a : FundamentalGroup (Circle × Circle) (1, 1)) :
    FundamentalGroup.mapOfEq ContinuousMap.snd rfl a = Path.Homotopic.projRight a := by
  -- The endpoint cast is reflexive, so the quotient map is exactly the projected loop.
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  unfold Path.Homotopic.projRight
  congr

/-- Helper for Exercise 79.5: the fundamental-group map of a pointwise product of based maps
into a topological group is the product of their induced maps. -/
private lemma mapOfEq_mul_apply {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [IsTopologicalGroup G] (x : X) (f g : C(X, G))
    (hf : f x = 1) (hg : g x = 1) (hfg : (f * g) x = 1)
    (a : FundamentalGroup X x) :
    FundamentalGroup.mapOfEq (f * g) hfg a =
      FundamentalGroup.mapOfEq f hf a * FundamentalGroup.mapOfEq g hg a := by
  -- Reduce to a representative loop; mapping by pointwise multiplication is then literally
  -- pointwise multiplication of the two mapped representatives.
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply,
    FundamentalGroup.mapOfEq_apply, ← FundamentalGroup.pointwiseMul_eq_mul]
  induction a using Path.Homotopic.Quotient.ind with
  | mk p =>
      rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
        ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast,
        ← Path.Homotopic.Quotient.mk_cast, ← Path.Homotopic.Quotient.mk_cast,
        FundamentalGroup.pointwiseMul_mk]
      congr 1
      ext t
      simp [Path.pointwiseMul_apply, ContinuousMap.mul_apply]

/-- Helper for Exercise 79.5: in the standard integer coordinates on the torus fundamental
group, the monomial map associated to `φ` induces exactly `φ`. -/
lemma continuousMap_induced
    (φ : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ × Multiplicative ℤ) :
    fundamentalGroup_circle_prod_circle.toMonoidHom.comp
        (FundamentalGroup.mapOfEq (continuousMap φ) (continuousMap_basepoint φ)) =
      φ.comp fundamentalGroup_circle_prod_circle.toMonoidHom := by
  -- Split the target product and expose the two coordinate maps of the monomial construction.
  apply DFunLike.ext
  intro a
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  change fundamentalGroup_circle_prod_circle
      (FundamentalGroup.mapOfEq (continuousMap φ) (continuousMap_basepoint φ) a) =
    φ (fundamentalGroup_circle_prod_circle a)
  rw [fundamentalGroup_circle_prod_circle_apply,
    fundamentalGroup_circle_prod_circle_apply]
  have hprojLeft :
      Path.Homotopic.projLeft
          (FundamentalGroup.mapOfEq (continuousMap φ) (continuousMap_basepoint φ) a) =
        FundamentalGroup.mapOfEq (firstCoordinateMap φ) (firstCoordinateMap_basepoint φ) a :=
    projLeft_mapOfEq_prodMk (1, 1) 1 1 (firstCoordinateMap φ) (secondCoordinateMap φ)
      (firstCoordinateMap_basepoint φ) (secondCoordinateMap_basepoint φ)
      (continuousMap_basepoint φ) a
  have hprojRight :
      Path.Homotopic.projRight
          (FundamentalGroup.mapOfEq (continuousMap φ) (continuousMap_basepoint φ) a) =
        FundamentalGroup.mapOfEq (secondCoordinateMap φ) (secondCoordinateMap_basepoint φ) a :=
    projRight_mapOfEq_prodMk (1, 1) 1 1 (firstCoordinateMap φ) (secondCoordinateMap φ)
      (firstCoordinateMap_basepoint φ) (secondCoordinateMap_basepoint φ)
      (continuousMap_basepoint φ) a
  rw [hprojLeft, hprojRight, apply_eq_monomials]
  have hfstBase : (ContinuousMap.fst : C(Circle × Circle, Circle)) (1, 1) = 1 := rfl
  have hsndBase : (ContinuousMap.snd : C(Circle × Circle, Circle)) (1, 1) = 1 := rfl
  have hfstApply : FundamentalGroup.mapOfEq ContinuousMap.fst hfstBase a =
      Path.Homotopic.projLeft a := mapOfEq_fst_apply a
  have hsndApply : FundamentalGroup.mapOfEq ContinuousMap.snd hsndBase a =
      Path.Homotopic.projRight a := mapOfEq_snd_apply a
  apply Prod.ext
  · -- The first coordinate is the product of the two power maps on projected loops.
    unfold firstCoordinateMap
    have hfirstBase :
        ((CircleMap.zpower ((φ firstGenerator).1.toAdd)).comp ContinuousMap.fst)
            ((1 : Circle), (1 : Circle)) =
          1 := by
      exact CircleMap.zpower_one _
    have hsecondBase :
        ((CircleMap.zpower ((φ secondGenerator).1.toAdd)).comp ContinuousMap.snd)
            ((1 : Circle), (1 : Circle)) =
          1 := by
      exact CircleMap.zpower_one _
    have hmul := mapOfEq_mul_apply ((1 : Circle), (1 : Circle))
      ((CircleMap.zpower ((φ firstGenerator).1.toAdd)).comp ContinuousMap.fst)
      ((CircleMap.zpower ((φ secondGenerator).1.toAdd)).comp ContinuousMap.snd)
      hfirstBase hsecondBase (firstCoordinateMap_basepoint φ) a
    rw [hmul]
    have hfirst := DFunLike.congr_fun
      (mapOfEq_comp ContinuousMap.fst
        (CircleMap.zpower ((φ firstGenerator).1.toAdd)) hfstBase
        (CircleMap.zpower_one ((φ firstGenerator).1.toAdd)) hfirstBase) a
    have hsecond := DFunLike.congr_fun
      (mapOfEq_comp ContinuousMap.snd
        (CircleMap.zpower ((φ secondGenerator).1.toAdd)) hsndBase
        (CircleMap.zpower_one ((φ secondGenerator).1.toAdd)) hsecondBase) a
    rw [← hfirst, ← hsecond]
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [hfstApply, hsndApply, CircleMap.mapOfEq_apply_zpower,
      CircleMap.mapOfEq_apply_zpower, map_mul, map_zpow, map_zpow]
  · -- The second coordinate is the analogous product with the second row of exponents.
    unfold secondCoordinateMap
    have hfirstBase :
        ((CircleMap.zpower ((φ firstGenerator).2.toAdd)).comp ContinuousMap.fst)
            ((1 : Circle), (1 : Circle)) =
          1 := by
      exact CircleMap.zpower_one _
    have hsecondBase :
        ((CircleMap.zpower ((φ secondGenerator).2.toAdd)).comp ContinuousMap.snd)
            ((1 : Circle), (1 : Circle)) =
          1 := by
      exact CircleMap.zpower_one _
    have hmul := mapOfEq_mul_apply ((1 : Circle), (1 : Circle))
      ((CircleMap.zpower ((φ firstGenerator).2.toAdd)).comp ContinuousMap.fst)
      ((CircleMap.zpower ((φ secondGenerator).2.toAdd)).comp ContinuousMap.snd)
      hfirstBase hsecondBase (secondCoordinateMap_basepoint φ) a
    rw [hmul]
    have hfirst := DFunLike.congr_fun
      (mapOfEq_comp ContinuousMap.fst
        (CircleMap.zpower ((φ firstGenerator).2.toAdd)) hfstBase
        (CircleMap.zpower_one ((φ firstGenerator).2.toAdd)) hfirstBase) a
    have hsecond := DFunLike.congr_fun
      (mapOfEq_comp ContinuousMap.snd
        (CircleMap.zpower ((φ secondGenerator).2.toAdd)) hsndBase
        (CircleMap.zpower_one ((φ secondGenerator).2.toAdd)) hsecondBase) a
    rw [← hfirst, ← hsecond]
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [hfstApply, hsndApply, CircleMap.mapOfEq_apply_zpower,
      CircleMap.mapOfEq_apply_zpower, map_mul, map_zpow, map_zpow]

end TorusAutomorphism

/-- Helper for Exercise 79.5: a Smith-normal-form basis presents its submodule as the span of
the diagonal multiples of the ambient basis vectors. -/
private lemma smithNormalForm_eq_span_range
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {N : Submodule R M} {ι : Type*} {n : ℕ}
    (snf : Module.Basis.SmithNormalForm N ι n) :
    N = Submodule.span R (Set.range (fun i ↦ snf.a i • snf.bM (snf.f i))) := by
  -- Map the span of the submodule basis through the inclusion and rewrite every basis vector by
  -- the Smith relation.
  calc
    N = LinearMap.range N.subtype := N.range_subtype.symm
    _ = Submodule.map N.subtype ⊤ := (Submodule.map_top N.subtype).symm
    _ = Submodule.map N.subtype (Submodule.span R (Set.range snf.bN)) :=
      congrArg (Submodule.map N.subtype) snf.bN.span_eq.symm
    _ = Submodule.span R (N.subtype '' Set.range snf.bN) :=
      Submodule.map_span N.subtype (Set.range snf.bN)
    _ = Submodule.span R (Set.range (N.subtype ∘ snf.bN)) := by
      rw [Set.range_comp]
    _ = Submodule.span R (Set.range (fun i ↦ snf.a i • snf.bM (snf.f i))) := by
      congr 2
      funext i
      exact snf.snf i

/-- Helper for Exercise 79.5: every `ℤ`-submodule of `ℤ × ℤ` has rank zero, one, or two
and is diagonal in a suitable ambient basis. -/
private lemma intPairSubmoduleNormalForm (N : Submodule ℤ (ℤ × ℤ)) :
    ∃ b : Module.Basis (Fin 2) ℤ (ℤ × ℤ),
      N = ⊥ ∨
        (∃ a : ℤ, a ≠ 0 ∧ N = Submodule.span ℤ {a • b 0}) ∨
          ∃ a c : ℤ, a ≠ 0 ∧ c ≠ 0 ∧
            N = Submodule.span ℤ {a • b 0, c • b 1} := by
  -- Smith normal form supplies a basis of `N` indexed by `Fin n` and an embedding into `Fin 2`.
  classical
  let ⟨n, snf⟩ := N.smithNormalForm (Module.Basis.finTwoProd ℤ)
  have hn : n ≤ 2 := by
    simpa using Fintype.card_le_of_embedding snf.f
  have hn_cases : n = 0 ∨ n = 1 ∨ n = 2 := by
    omega
  rcases hn_cases with hn_zero | hn_one | hn_two
  · subst n
    refine ⟨snf.bM, Or.inl ?_⟩
    -- With no basis vectors the Smith span is the zero submodule.
    simpa using smithNormalForm_eq_span_range snf
  · subst n
    have ha : snf.a 0 ≠ 0 := by
      intro ha_zero
      apply snf.bN.ne_zero 0
      apply Subtype.ext
      simpa [ha_zero] using snf.snf 0
    have hindex : snf.f 0 = 0 ∨ snf.f 0 = 1 := by
      omega
    rcases hindex with hindex | hindex
    · refine ⟨snf.bM, Or.inr (Or.inl ⟨snf.a 0, ha, ?_⟩)⟩
      simpa [hindex, Set.range_unique] using smithNormalForm_eq_span_range snf
    · let b : Module.Basis (Fin 2) ℤ (ℤ × ℤ) :=
        snf.bM.reindex (Equiv.swap 0 1)
      refine ⟨b, Or.inr (Or.inl ⟨snf.a 0, ha, ?_⟩)⟩
      simpa [b, hindex, Set.range_unique] using smithNormalForm_eq_span_range snf
  · subst n
    have hf_bijective : Function.Bijective snf.f :=
      (Fintype.bijective_iff_injective_and_card snf.f).mpr
        ⟨snf.f.injective, Fintype.card_fin 2⟩
    let e : Fin 2 ≃ Fin 2 := Equiv.ofBijective snf.f hf_bijective
    let b : Module.Basis (Fin 2) ℤ (ℤ × ℤ) := snf.bM.reindex e.symm
    have ha : snf.a 0 ≠ 0 := by
      intro ha_zero
      apply snf.bN.ne_zero 0
      apply Subtype.ext
      simpa [ha_zero] using snf.snf 0
    have hc : snf.a 1 ≠ 0 := by
      intro hc_zero
      apply snf.bN.ne_zero 1
      apply Subtype.ext
      simpa [hc_zero] using snf.snf 1
    have hrange :
        Set.range (fun i : Fin 2 ↦ snf.a i • snf.bM (snf.f i)) =
          {snf.a 0 • snf.bM (snf.f 0), snf.a 1 • snf.bM (snf.f 1)} := by
      -- Enumerate the two possible indices to expose the range as a two-element set.
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · simp
        · simp
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    refine ⟨b, Or.inr (Or.inr ⟨snf.a 0, snf.a 1, ha, hc, ?_⟩)⟩
    calc
      N = Submodule.span ℤ
          (Set.range (fun i : Fin 2 ↦ snf.a i • snf.bM (snf.f i))) :=
        smithNormalForm_eq_span_range snf
      _ = Submodule.span ℤ
          {snf.a 0 • snf.bM (snf.f 0), snf.a 1 • snf.bM (snf.f 1)} :=
        congrArg (Submodule.span ℤ) hrange
      _ = Submodule.span ℤ {snf.a 0 • b 0, snf.a 1 • b 1} := by
        simp only [b, Module.Basis.reindex_apply, e, Equiv.ofBijective_apply,
          Equiv.symm_symm]

/-- Helper for Exercise 79.5: the integer submodule generated by one vector corresponds to
the cyclic subgroup generated by its multiplicative image. -/
private lemma intPairZPowers_toIntSubmodule (x : ℤ × ℤ) :
    (Subgroup.toAddSubgroup' (Subgroup.zpowers (Multiplicative.ofAdd x))).toIntSubmodule =
      Submodule.span ℤ {x} := by
  -- Pass both generated objects to additive subgroups, where closure of a singleton agrees.
  apply Submodule.toAddSubgroup_injective
  rw [AddSubgroup.toIntSubmodule_toAddSubgroup,
    Submodule.span_int_eq_addSubgroupClosure, Subgroup.zpowers_eq_closure,
    Subgroup.toAddSubgroup'_closure]
  congr

/-- Helper for Exercise 79.5: the span of two integer vectors corresponds to the join of their
cyclic multiplicative subgroups. -/
private lemma intPairZPowersSup_toIntSubmodule (x y : ℤ × ℤ) :
    (Subgroup.toAddSubgroup'
      (Subgroup.zpowers (Multiplicative.ofAdd x) ⊔
        Subgroup.zpowers (Multiplicative.ofAdd y))).toIntSubmodule =
      Submodule.span ℤ {x, y} := by
  -- Order equivalences preserve joins, reducing the claim to the one-generator calculation.
  rw [map_sup, map_sup, intPairZPowers_toIntSubmodule,
    intPairZPowers_toIntSubmodule, Submodule.span_insert]

/-- Helper for Exercise 79.5: replacing an integer coefficient by its absolute value does not
change the cyclic subgroup generated by the corresponding multiple. -/
private lemma intPairZPowers_natAbs (a : ℤ) (x : ℤ × ℤ) :
    Subgroup.zpowers (Multiplicative.ofAdd ((a.natAbs : ℤ) • x)) =
      Subgroup.zpowers (Multiplicative.ofAdd (a • x)) := by
  -- The original coefficient is either the absolute value or its negative; inversion preserves
  -- a cyclic subgroup.
  let m := a.natAbs
  have hm : m = a.natAbs := rfl
  have ha : a = (m : ℤ) ∨ a = -(m : ℤ) := by
    simpa [m] using Int.natAbs_eq a
  rw [← hm]
  rcases ha with ha | ha
  · have hx : a • x = (m : ℤ) • x := congrArg (fun z : ℤ ↦ z • x) ha
    rw [hx]
  · have hx : a • x = -((m : ℤ) • x) := by
      rw [ha, neg_smul]
    rw [hx]
    exact Subgroup.zpowers_inv.symm

/-- Helper for Exercise 79.5: an integer basis determines an automorphism of the standard
multiplicative coordinate group of the torus. -/
private def intPairBasisAutomorphism (b : Module.Basis (Fin 2) ℤ (ℤ × ℤ)) :
    Multiplicative ℤ × Multiplicative ℤ ≃* Multiplicative ℤ × Multiplicative ℤ :=
  (MulEquiv.prodMultiplicative ℤ ℤ).symm.trans
    (((Module.Basis.finTwoProd ℤ).equiv b (Equiv.refl (Fin 2))).toAddEquiv.toMultiplicative.trans
      (MulEquiv.prodMultiplicative ℤ ℤ))

/-- Helper for Exercise 79.5: the basis automorphism sends a multiple of the first standard
generator to the same multiple of the first basis vector. -/
private lemma intPairBasisAutomorphism_firstGenerator
    (b : Module.Basis (Fin 2) ℤ (ℤ × ℤ)) (a : ℤ) :
    intPairBasisAutomorphism b (Multiplicative.ofAdd a, 1) =
      (MulEquiv.prodMultiplicative ℤ ℤ) (Multiplicative.ofAdd (a • b 0)) := by
  -- Express the coordinate generator as the first standard basis vector before applying the
  -- basis equivalence.
  have hlinear :
      ((Module.Basis.finTwoProd ℤ).equiv b (Equiv.refl (Fin 2))) (a, 0) = a • b 0 := by
    calc
      ((Module.Basis.finTwoProd ℤ).equiv b (Equiv.refl (Fin 2))) (a, 0) =
          ((Module.Basis.finTwoProd ℤ).equiv b (Equiv.refl (Fin 2)))
            (a • Module.Basis.finTwoProd ℤ 0) := by simp
      _ = a • ((Module.Basis.finTwoProd ℤ).equiv b (Equiv.refl (Fin 2)))
          (Module.Basis.finTwoProd ℤ 0) := map_smul _ _ _
      _ = a • b 0 := by
        rw [Module.Basis.equiv_apply]
        rfl
  have hpair : (Multiplicative.ofAdd a, 1) =
      (MulEquiv.prodMultiplicative ℤ ℤ) (Multiplicative.ofAdd (a, 0)) := by
    rfl
  rw [hpair]
  simp only [intPairBasisAutomorphism, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    AddEquiv.toMultiplicative_apply_apply]
  congr 1

/-- Helper for Exercise 79.5: the basis automorphism sends a multiple of the second standard
generator to the same multiple of the second basis vector. -/
private lemma intPairBasisAutomorphism_secondGenerator
    (b : Module.Basis (Fin 2) ℤ (ℤ × ℤ)) (a : ℤ) :
    intPairBasisAutomorphism b (1, Multiplicative.ofAdd a) =
      (MulEquiv.prodMultiplicative ℤ ℤ) (Multiplicative.ofAdd (a • b 1)) := by
  -- Repeat the basis-coordinate computation for the second standard vector.
  have hlinear :
      ((Module.Basis.finTwoProd ℤ).equiv b (Equiv.refl (Fin 2))) (0, a) = a • b 1 := by
    calc
      ((Module.Basis.finTwoProd ℤ).equiv b (Equiv.refl (Fin 2))) (0, a) =
          ((Module.Basis.finTwoProd ℤ).equiv b (Equiv.refl (Fin 2)))
            (a • Module.Basis.finTwoProd ℤ 1) := by simp
      _ = a • ((Module.Basis.finTwoProd ℤ).equiv b (Equiv.refl (Fin 2)))
          (Module.Basis.finTwoProd ℤ 1) := map_smul _ _ _
      _ = a • b 1 := by
        rw [Module.Basis.equiv_apply]
        rfl
  have hpair : (1, Multiplicative.ofAdd a) =
      (MulEquiv.prodMultiplicative ℤ ℤ) (Multiplicative.ofAdd (0, a)) := by
    rfl
  rw [hpair]
  simp only [intPairBasisAutomorphism, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    AddEquiv.toMultiplicative_apply_apply]
  congr 1

/-- Helper for Exercise 79.5: every subgroup of the standard rank-two integer coordinate group
is, after an automorphism, trivial, cyclic along the first axis, or rectangular. -/
private lemma intProductSubgroupNormalForm
    (H : Subgroup (Multiplicative ℤ × Multiplicative ℤ)) :
    ∃ ψ : Multiplicative ℤ × Multiplicative ℤ ≃*
        Multiplicative ℤ × Multiplicative ℤ,
      H = ⊥ ∨
        (∃ m : ℕ, 0 < m ∧
          H = (Subgroup.zpowers (Multiplicative.ofAdd (m : ℤ), 1)).map ψ.toMonoidHom) ∨
        ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
          H = (Subgroup.zpowers (Multiplicative.ofAdd (m : ℤ), 1) ⊔
            Subgroup.zpowers (1, Multiplicative.ofAdd (n : ℤ))).map ψ.toMonoidHom := by
  -- Pull the subgroup back to `Multiplicative (ℤ × ℤ)` and apply Smith normal form to
  -- its associated integer submodule.
  let q : Multiplicative (ℤ × ℤ) ≃* Multiplicative ℤ × Multiplicative ℤ :=
    MulEquiv.prodMultiplicative ℤ ℤ
  let K : Subgroup (Multiplicative (ℤ × ℤ)) := H.comap q.toMonoidHom
  let N : Submodule ℤ (ℤ × ℤ) := K.toAddSubgroup'.toIntSubmodule
  obtain ⟨b, hnormal⟩ := intPairSubmoduleNormalForm N
  let ψ := intPairBasisAutomorphism b
  refine ⟨ψ, ?_⟩
  have hmapK : K.map q.toMonoidHom = H := by
    apply Subgroup.map_comap_eq_self
    intro x hx
    exact ⟨q.symm x, q.apply_symm_apply x⟩
  have hq_apply (x : Multiplicative (ℤ × ℤ)) : q.toMonoidHom x = q x := rfl
  have hψ_apply (x : Multiplicative ℤ × Multiplicative ℤ) : ψ.toMonoidHom x = ψ x := rfl
  rcases hnormal with hzero | hone | htwo
  · left
    have hK : K = ⊥ := by
      apply Subgroup.toAddSubgroup'.injective
      apply AddSubgroup.toIntSubmodule.injective
      simpa [N] using hzero
    calc
      H = K.map q.toMonoidHom := hmapK.symm
      _ = ⊥ := by simp [hK]
  · rcases hone with ⟨a, ha, hone⟩
    right
    left
    refine ⟨a.natAbs, Int.natAbs_pos.mpr ha, ?_⟩
    have hK : K = Subgroup.zpowers (Multiplicative.ofAdd (a • b 0)) := by
      apply Subgroup.toAddSubgroup'.injective
      apply AddSubgroup.toIntSubmodule.injective
      exact hone.trans (intPairZPowers_toIntSubmodule (a • b 0)).symm
    have hsign := congrArg (Subgroup.map q.toMonoidHom) (intPairZPowers_natAbs a (b 0))
    simp only [MonoidHom.map_zpowers, hq_apply] at hsign
    have hψ : ψ (Multiplicative.ofAdd (a.natAbs : ℤ), 1) =
        q (Multiplicative.ofAdd ((a.natAbs : ℤ) • b 0)) := by
      simpa [ψ, q] using intPairBasisAutomorphism_firstGenerator b (a.natAbs : ℤ)
    calc
      H = K.map q.toMonoidHom := hmapK.symm
      _ = Subgroup.zpowers (q (Multiplicative.ofAdd (a • b 0))) := by
        rw [hK, MonoidHom.map_zpowers, hq_apply]
      _ = Subgroup.zpowers (q (Multiplicative.ofAdd ((a.natAbs : ℤ) • b 0))) :=
        hsign.symm
      _ = Subgroup.zpowers (ψ (Multiplicative.ofAdd (a.natAbs : ℤ), 1)) := by
        rw [hψ]
      _ = (Subgroup.zpowers (Multiplicative.ofAdd (a.natAbs : ℤ), 1)).map
          ψ.toMonoidHom := (MonoidHom.map_zpowers ψ.toMonoidHom _).symm
  · rcases htwo with ⟨a, c, ha, hc, htwo⟩
    right
    right
    refine ⟨a.natAbs, c.natAbs, Int.natAbs_pos.mpr ha, Int.natAbs_pos.mpr hc, ?_⟩
    have hK : K = Subgroup.zpowers (Multiplicative.ofAdd (a • b 0)) ⊔
        Subgroup.zpowers (Multiplicative.ofAdd (c • b 1)) := by
      apply Subgroup.toAddSubgroup'.injective
      apply AddSubgroup.toIntSubmodule.injective
      exact htwo.trans (intPairZPowersSup_toIntSubmodule (a • b 0) (c • b 1)).symm
    have hsignFirst :=
      congrArg (Subgroup.map q.toMonoidHom) (intPairZPowers_natAbs a (b 0))
    have hsignSecond :=
      congrArg (Subgroup.map q.toMonoidHom) (intPairZPowers_natAbs c (b 1))
    simp only [MonoidHom.map_zpowers, hq_apply] at hsignFirst hsignSecond
    have hψFirst : ψ (Multiplicative.ofAdd (a.natAbs : ℤ), 1) =
        q (Multiplicative.ofAdd ((a.natAbs : ℤ) • b 0)) := by
      simpa [ψ, q] using intPairBasisAutomorphism_firstGenerator b (a.natAbs : ℤ)
    have hψSecond : ψ (1, Multiplicative.ofAdd (c.natAbs : ℤ)) =
        q (Multiplicative.ofAdd ((c.natAbs : ℤ) • b 1)) := by
      simpa [ψ, q] using intPairBasisAutomorphism_secondGenerator b (c.natAbs : ℤ)
    calc
      H = K.map q.toMonoidHom := hmapK.symm
      _ = Subgroup.zpowers (q (Multiplicative.ofAdd (a • b 0))) ⊔
          Subgroup.zpowers (q (Multiplicative.ofAdd (c • b 1))) := by
        rw [hK, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
          hq_apply, hq_apply]
      _ = Subgroup.zpowers (q (Multiplicative.ofAdd ((a.natAbs : ℤ) • b 0))) ⊔
          Subgroup.zpowers (q (Multiplicative.ofAdd ((c.natAbs : ℤ) • b 1))) :=
        congrArg₂ (fun A B : Subgroup (Multiplicative ℤ × Multiplicative ℤ) ↦ A ⊔ B)
          hsignFirst.symm hsignSecond.symm
      _ = Subgroup.zpowers (ψ (Multiplicative.ofAdd (a.natAbs : ℤ), 1)) ⊔
          Subgroup.zpowers (ψ (1, Multiplicative.ofAdd (c.natAbs : ℤ))) := by
        rw [hψFirst, hψSecond]
      _ = (Subgroup.zpowers (Multiplicative.ofAdd (a.natAbs : ℤ), 1) ⊔
          Subgroup.zpowers (1, Multiplicative.ofAdd (c.natAbs : ℤ))).map
            ψ.toMonoidHom := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers,
          hψ_apply, hψ_apply]

/-- Helper for Exercise 79.5: a local homeomorphism into a locally path-connected space has a
locally path-connected source. -/
theorem IsLocalHomeomorph.locallyPathConnectedSpace
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyPathConnectedSpace Y] {f : X → Y} (hf : IsLocalHomeomorph f) :
    LocallyPathConnectedSpace X := by
  -- Work in one local-homeomorphism chart and transfer a path-connected neighborhood basis
  -- from its open source subtype back to the ambient source space.
  refine ⟨fun x ↦ ?_⟩
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨e, hx, he⟩ := hf x
  let xSource : e.source := ⟨x, hx⟩
  letI : LocallyPathConnectedSpace e.source :=
    e.isOpenEmbedding_restrict.locallyPathConnectedSpace
  have hpreimage : Subtype.val ⁻¹' U ∈ nhds xSource := continuousAt_subtype_val hU
  obtain ⟨S, ⟨hSnhds, hSpath⟩, hSsub⟩ :=
    (path_connected_basis xSource).mem_iff.mp hpreimage
  let W : Set X := Subtype.val '' S
  have hWmap : W ∈ Filter.map Subtype.val (nhds xSource) :=
    Filter.image_mem_map hSnhds
  have hWnhds : W ∈ nhds x := by
    rw [e.open_source.isOpenEmbedding_subtypeVal.map_nhds_eq xSource] at hWmap
    exact hWmap
  refine ⟨W, hWnhds, hSpath.image continuous_subtype_val, ?_⟩
  rintro y ⟨ySource, hySource, rfl⟩
  exact hSsub hySource

/-- Helper for Exercise 79.5: the usual coordinate identification is a homeomorphism from
`ℝ × ℝ` to the two-dimensional Euclidean space. -/
private def realPairHomeomorphEuclideanPlane :
    ℝ × ℝ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  (((WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).trans
    (LinearEquiv.finTwoArrow ℝ ℝ)).toContinuousLinearEquiv.toHomeomorph).symm

/-- Helper for Exercise 79.5: postcomposing a covering of the torus with a monomial torus
automorphism is again a covering. -/
private lemma TorusAutomorphism.continuousMap_comp_isCoveringMap
    {X : Type*} [TopologicalSpace X] (q : C(X, Circle × Circle))
    (hq : IsCoveringMap q)
    (ψ : Multiplicative ℤ × Multiplicative ℤ ≃*
      Multiplicative ℤ × Multiplicative ℤ) :
    IsCoveringMap ((continuousMap ψ.toMonoidHom).comp q) := by
  -- The continuous monomial map is the forward map of the corresponding homeomorphism.
  simpa [homeomorph] using hq.homeomorph_comp (homeomorph ψ)

/-- Helper for Exercise 79.5: postcomposition by a based torus map sends the coordinate range
of a based map through the induced integer-coordinate homomorphism. -/
private lemma torusCoordinateRange_comp
    {X : Type*} [TopologicalSpace X] (x : X)
    (q : C(X, Circle × Circle)) (hq : q x = (1, 1))
    (h : C(Circle × Circle, Circle × Circle)) (hh : h (1, 1) = (1, 1))
    (ψ : Multiplicative ℤ × Multiplicative ℤ ≃*
      Multiplicative ℤ × Multiplicative ℤ)
    (hinduced : fundamentalGroup_circle_prod_circle.toMonoidHom.comp
        (FundamentalGroup.mapOfEq h hh) =
      ψ.toMonoidHom.comp fundamentalGroup_circle_prod_circle.toMonoidHom)
    (hcomp : (h.comp q) x = (1, 1)) :
    (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
      (FundamentalGroup.mapOfEq (h.comp q) hcomp)).range =
      (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
        (FundamentalGroup.mapOfEq q hq)).range.map ψ.toMonoidHom := by
  -- First identify the induced map of the composite, then take its range and use `range_comp`.
  have hmaps := TorusAutomorphism.mapOfEq_comp q h hq hh hcomp
  have hhom :
      fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq (h.comp q) hcomp) =
        ψ.toMonoidHom.comp
          (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
            (FundamentalGroup.mapOfEq q hq)) := by
    calc
      fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq (h.comp q) hcomp) =
        fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          ((FundamentalGroup.mapOfEq h hh).comp
            (FundamentalGroup.mapOfEq q hq)) :=
          congrArg fundamentalGroup_circle_prod_circle.toMonoidHom.comp hmaps.symm
      _ = (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq h hh)).comp
            (FundamentalGroup.mapOfEq q hq) := rfl
      _ = (ψ.toMonoidHom.comp fundamentalGroup_circle_prod_circle.toMonoidHom).comp
          (FundamentalGroup.mapOfEq q hq) :=
        congrArg (fun k ↦ k.comp (FundamentalGroup.mapOfEq q hq)) hinduced
      _ = ψ.toMonoidHom.comp
          (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
            (FundamentalGroup.mapOfEq q hq)) := rfl
  rw [hhom, MonoidHom.range_comp]

/-- Helper for Exercise 79.5: equality of torus fundamental-group ranges can be reflected from
their images in the standard integer coordinates. -/
private lemma torusFundamentalGroupRange_eq_of_coordinateRange_eq
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y) (f : C(X, Circle × Circle)) (g : C(Y, Circle × Circle))
    (hf : f x = (1, 1)) (hg : g y = (1, 1))
    (hcoordinate :
      (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
        (FundamentalGroup.mapOfEq f hf)).range =
      (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
        (FundamentalGroup.mapOfEq g hg)).range) :
    (FundamentalGroup.mapOfEq f hf).range = (FundamentalGroup.mapOfEq g hg).range := by
  -- Mapping both subgroups through the injective coordinate equivalence reduces the claim to
  -- the supplied coordinate equality.
  apply Subgroup.map_injective
    (f := fundamentalGroup_circle_prod_circle.toMonoidHom)
    fundamentalGroup_circle_prod_circle.injective
  rw [← MonoidHom.range_comp, ← MonoidHom.range_comp]
  exact hcoordinate

/-- Helper for Exercise 79.5: range equality computed with extensionally equal continuous-map
packages gives equality of the covering maps' canonical fundamental-group ranges. -/
private lemma coveringFundamentalGroupMapRange_eq_of_continuousMapRanges_eq
    {E E' B : Type*} [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    {p : E → B} {p' : E' → B} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
    (b : B) (e : E) (e' : E') (he : p e = b) (he' : p' e' = b)
    (f : C(E, B)) (g : C(E', B)) (hf : f e = b) (hg : g e' = b)
    (hfp : f = ⟨p, hp.continuous⟩) (hgp : g = ⟨p', hp'.continuous⟩)
    (hrange : (FundamentalGroup.mapOfEq f hf).range =
      (FundamentalGroup.mapOfEq g hg).range) :
    hp.fundamentalGroupMapRange he = hp'.fundamentalGroupMapRange he' := by
  -- Replace the auxiliary continuous-map packages by the canonical packages used in the
  -- definition; proof irrelevance then identifies the endpoint witnesses.
  unfold IsCoveringMap.fundamentalGroupMapRange
  subst f
  subst g
  exact hrange

/-- Exercise 79.5 (1): every automorphism of the fundamental group of the torus is induced
by a basepoint-preserving self-homeomorphism of the torus. -/
theorem torusFundamentalGroupAutomorphism_induced
    (e : FundamentalGroup (Circle × Circle) (1, 1) ≃*
      FundamentalGroup (Circle × Circle) (1, 1)) :
    ∃ (h : Circle × Circle ≃ₜ Circle × Circle) (hbase : h (1, 1) = (1, 1)),
      FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hbase = e.toMonoidHom := by
  -- Conjugate the given automorphism into the standard integer coordinates and realize that
  -- coordinate automorphism by the monomial homeomorphism constructed above.
  let φ : Multiplicative ℤ × Multiplicative ℤ ≃* Multiplicative ℤ × Multiplicative ℤ :=
    (fundamentalGroup_circle_prod_circle.symm.trans e).trans
      fundamentalGroup_circle_prod_circle
  let h : Circle × Circle ≃ₜ Circle × Circle := TorusAutomorphism.homeomorph φ
  have hbase : h (1, 1) = (1, 1) := TorusAutomorphism.continuousMap_basepoint φ.toMonoidHom
  refine ⟨h, hbase, ?_⟩
  -- The coordinate equivalence is injective, so the verified coordinate square can be canceled.
  apply DFunLike.ext
  intro a
  apply fundamentalGroup_circle_prod_circle.injective
  have hinduced := DFunLike.congr_fun
    (TorusAutomorphism.continuousMap_induced φ.toMonoidHom) a
  calc
    fundamentalGroup_circle_prod_circle
        (FundamentalGroup.mapOfEq ⟨h, h.continuous⟩ hbase a) =
      φ (fundamentalGroup_circle_prod_circle a) := hinduced
    _ = fundamentalGroup_circle_prod_circle (e a) := by
      change fundamentalGroup_circle_prod_circle
          (e (fundamentalGroup_circle_prod_circle.symm
            (fundamentalGroup_circle_prod_circle a))) =
        fundamentalGroup_circle_prod_circle (e a)
      rw [fundamentalGroup_circle_prod_circle.symm_apply_apply]

/-- Exercise 79.5 (2): every connected covering space of the torus is
homeomorphic to the plane, the infinite cylinder, or the torus. -/
theorem coveringSpaceOfTorus_homeomorph (E : Type u)
    [TopologicalSpace E] [PathConnectedSpace E]
    (p : E → Circle × Circle) (hp : IsCoveringMap p) :
    Nonempty (E ≃ₜ EuclideanSpace ℝ (Fin 2)) ∨
      Nonempty (E ≃ₜ Circle × ℝ) ∨ Nonempty (E ≃ₜ Circle × Circle) := by
  -- Install local path-connectedness on the circle and lift it through the covering charts to
  -- the total space, as required by the covering-equivalence theorem.
  classical
  letI : LocallyPathConnectedSpace (Circle × Circle) :=
    (torusCover_universal.1.isQuotientMap
      torusCover_universal.1.surjective_of_pathConnected).locallyPathConnectedSpace
  letI : LocallyPathConnectedSpace E := hp.isLocalHomeomorph.locallyPathConnectedSpace
  obtain ⟨e₀, he₀⟩ := hp.surjective_of_pathConnected (1, 1)
  let pMap : C(E, Circle × Circle) := ⟨p, hp.continuous⟩
  have hpMap : pMap = ⟨p, hp.continuous⟩ := rfl
  let H : Subgroup (Multiplicative ℤ × Multiplicative ℤ) :=
    (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
      (FundamentalGroup.mapOfEq pMap he₀)).range
  obtain ⟨ψ, hcases⟩ := intProductSubgroupNormalForm H
  let h : C(Circle × Circle, Circle × Circle) :=
    TorusAutomorphism.continuousMap ψ.toMonoidHom
  have hh : h (1, 1) = (1, 1) := TorusAutomorphism.continuousMap_basepoint ψ.toMonoidHom
  have hinduced : fundamentalGroup_circle_prod_circle.toMonoidHom.comp
      (FundamentalGroup.mapOfEq h hh) =
        ψ.toMonoidHom.comp fundamentalGroup_circle_prod_circle.toMonoidHom := by
    simpa [h] using TorusAutomorphism.continuousMap_induced ψ.toMonoidHom
  rcases hcases with hzero | hcyclic | hrectangular
  · -- The trivial subgroup is represented by the universal cover `ℝ × ℝ`.
    left
    have huniversal := torusCover_universal
    have hbase : (h.comp TorusCover.universal) (0, 0) = (1, 1) := by
      rw [ContinuousMap.comp_apply, TorusCover.universal_basepoint, hh]
    have hcover : IsCoveringMap (h.comp TorusCover.universal) :=
      TorusAutomorphism.continuousMap_comp_isCoveringMap
        TorusCover.universal huniversal.1 ψ
    have htwistedCoordinate := torusCoordinateRange_comp (0, 0)
      TorusCover.universal TorusCover.universal_basepoint h hh ψ hinduced hbase
    have htwistedCoordinate' :
        (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq (h.comp TorusCover.universal) hbase)).range = ⊥ := by
      have hmappedBottom := congrArg (Subgroup.map ψ.toMonoidHom) huniversal.2
      exact htwistedCoordinate.trans (hmappedBottom.trans (Subgroup.map_bot ψ.toMonoidHom))
    have hcoordinate :
        H = (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq (h.comp TorusCover.universal) hbase)).range :=
      hzero.trans htwistedCoordinate'.symm
    have hcoordinateMaps :
        (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq pMap he₀)).range =
        (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq (h.comp TorusCover.universal) hbase)).range := by
      simpa [H] using hcoordinate
    have hplainRange := torusFundamentalGroupRange_eq_of_coordinateRange_eq
      e₀ (0, 0) pMap (h.comp TorusCover.universal) he₀ hbase hcoordinateMaps
    have hcoverMap : h.comp TorusCover.universal =
        (⟨h.comp TorusCover.universal, hcover.continuous⟩ : C(ℝ × ℝ, Circle × Circle)) := by
      apply ContinuousMap.ext
      intro z
      rfl
    have hrange := coveringFundamentalGroupMapRange_eq_of_continuousMapRanges_eq
      hp hcover (1, 1) e₀ (0, 0) he₀ hbase pMap (h.comp TorusCover.universal)
      he₀ hbase hpMap hcoverMap hplainRange
    have hequivalent := hp.equivalent_of_fundamentalGroupMapRange_eq hcover
      (1, 1) e₀ (0, 0) he₀ hbase hrange
    obtain ⟨coverHomeomorph, hcommutes⟩ := CoveringMap.equivalent_iff.mp hequivalent
    exact ⟨coverHomeomorph.trans realPairHomeomorphEuclideanPlane⟩
  · -- A cyclic subgroup is represented by the cover `Circle × ℝ` of the matching degree.
    right
    left
    rcases hcyclic with ⟨m, hm, hH⟩
    have hstandard := torusCover_firstCyclic m hm
    letI : LocallyPathConnectedSpace (Circle × ℝ) :=
      hstandard.1.isLocalHomeomorph.locallyPathConnectedSpace
    have hbase : (h.comp (TorusCover.firstCyclic m)) (1, 0) = (1, 1) := by
      rw [ContinuousMap.comp_apply, TorusCover.firstCyclic_basepoint, hh]
    have hcover : IsCoveringMap (h.comp (TorusCover.firstCyclic m)) :=
      TorusAutomorphism.continuousMap_comp_isCoveringMap
        (TorusCover.firstCyclic m) hstandard.1 ψ
    have htwistedCoordinate := torusCoordinateRange_comp (1, 0)
      (TorusCover.firstCyclic m) (TorusCover.firstCyclic_basepoint m)
      h hh ψ hinduced hbase
    have htwistedCoordinate' :
        (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq (h.comp (TorusCover.firstCyclic m)) hbase)).range =
        (Subgroup.zpowers (Multiplicative.ofAdd (m : ℤ), 1)).map ψ.toMonoidHom := by
      exact htwistedCoordinate.trans
        (congrArg (Subgroup.map ψ.toMonoidHom) hstandard.2)
    have hcoordinate :
        H = (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq (h.comp (TorusCover.firstCyclic m)) hbase)).range :=
      hH.trans htwistedCoordinate'.symm
    have hcoordinateMaps :
        (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq pMap he₀)).range =
        (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq (h.comp (TorusCover.firstCyclic m)) hbase)).range := by
      simpa [H] using hcoordinate
    have hplainRange := torusFundamentalGroupRange_eq_of_coordinateRange_eq
      e₀ (1, 0) pMap (h.comp (TorusCover.firstCyclic m)) he₀ hbase hcoordinateMaps
    have hcoverMap : h.comp (TorusCover.firstCyclic m) =
        (⟨h.comp (TorusCover.firstCyclic m), hcover.continuous⟩ :
          C(Circle × ℝ, Circle × Circle)) := by
      apply ContinuousMap.ext
      intro z
      rfl
    have hrange := coveringFundamentalGroupMapRange_eq_of_continuousMapRanges_eq
      hp hcover (1, 1) e₀ (1, 0) he₀ hbase pMap
      (h.comp (TorusCover.firstCyclic m)) he₀ hbase hpMap hcoverMap hplainRange
    have hequivalent := hp.equivalent_of_fundamentalGroupMapRange_eq hcover
      (1, 1) e₀ (1, 0) he₀ hbase hrange
    obtain ⟨coverHomeomorph, hcommutes⟩ := CoveringMap.equivalent_iff.mp hequivalent
    exact ⟨coverHomeomorph⟩
  · -- A rank-two subgroup is represented by the rectangular finite-sheeted torus cover.
    right
    right
    rcases hrectangular with ⟨m, n, hm, hn, hH⟩
    have hstandard := torusCover_rectangular m n hm hn
    have hbase : (h.comp (TorusCover.rectangular m n)) (1, 1) = (1, 1) := by
      rw [ContinuousMap.comp_apply, TorusCover.rectangular_basepoint, hh]
    have hcover : IsCoveringMap (h.comp (TorusCover.rectangular m n)) :=
      TorusAutomorphism.continuousMap_comp_isCoveringMap
        (TorusCover.rectangular m n) hstandard.1 ψ
    have htwistedCoordinate := torusCoordinateRange_comp (1, 1)
      (TorusCover.rectangular m n) (TorusCover.rectangular_basepoint m n)
      h hh ψ hinduced hbase
    have htwistedCoordinate' :
        (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq (h.comp (TorusCover.rectangular m n)) hbase)).range =
        (Subgroup.zpowers (Multiplicative.ofAdd (m : ℤ), 1) ⊔
          Subgroup.zpowers (1, Multiplicative.ofAdd (n : ℤ))).map ψ.toMonoidHom := by
      exact htwistedCoordinate.trans
        (congrArg (Subgroup.map ψ.toMonoidHom) hstandard.2)
    have hcoordinate :
        H = (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq (h.comp (TorusCover.rectangular m n)) hbase)).range :=
      hH.trans htwistedCoordinate'.symm
    have hcoordinateMaps :
        (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq pMap he₀)).range =
        (fundamentalGroup_circle_prod_circle.toMonoidHom.comp
          (FundamentalGroup.mapOfEq (h.comp (TorusCover.rectangular m n)) hbase)).range := by
      simpa [H] using hcoordinate
    have hplainRange := torusFundamentalGroupRange_eq_of_coordinateRange_eq
      e₀ (1, 1) pMap (h.comp (TorusCover.rectangular m n)) he₀ hbase hcoordinateMaps
    have hcoverMap : h.comp (TorusCover.rectangular m n) =
        (⟨h.comp (TorusCover.rectangular m n), hcover.continuous⟩ :
          C(Circle × Circle, Circle × Circle)) := by
      apply ContinuousMap.ext
      intro z
      rfl
    have hrange := coveringFundamentalGroupMapRange_eq_of_continuousMapRanges_eq
      hp hcover (1, 1) e₀ (1, 1) he₀ hbase pMap
      (h.comp (TorusCover.rectangular m n)) he₀ hbase hpMap hcoverMap hplainRange
    have hequivalent := hp.equivalent_of_fundamentalGroupMapRange_eq hcover
      (1, 1) e₀ (1, 1) he₀ hbase hrange
    obtain ⟨coverHomeomorph, hcommutes⟩ := CoveringMap.equivalent_iff.mp hequivalent
    exact ⟨coverHomeomorph⟩
