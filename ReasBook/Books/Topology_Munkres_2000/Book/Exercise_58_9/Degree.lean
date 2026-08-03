module

public import Topology_Munkres_2000.Book.Exercise_54_6.Power
public import Topology_Munkres_2000.Book.Exercise_58_9.BasedClassification
public import Topology_Munkres_2000.Book.Theorem_54_5.FundamentalGroup
import Topology_Munkres_2000.Book.Exercise_52_6
import Topology_Munkres_2000.Book.Exercise_52_7.LoopGroup
import Topology_Munkres_2000.Book.Exercise_52_2.BasepointChange
import Topology_Munkres_2000.Book.Lemma_58_4
import Topology_Munkres_2000.Book.Proposition_52_2
import Topology_Munkres_2000.Book.Theorem_52_4.Functoriality
import Mathlib.GroupTheory.ArchimedeanDensely

noncomputable section

public section

namespace Circle

/-- Integer coordinates determined by a choice of generator of `π₁(S¹, 1)`. -/
abbrev FundamentalOrientation := FundamentalGroup Circle 1 ≃* Multiplicative ℤ

/-- The fundamental group of the circle admits integer coordinates. -/
theorem nonemptyFundamentalOrientation : Nonempty FundamentalOrientation :=
  ⟨fundamentalGroupEquivInt⟩

namespace FundamentalOrientation

/-- Transport an orientation at `1` to integer coordinates at any basepoint. -/
def equiv (orientation : FundamentalOrientation) (x : Circle) :
    FundamentalGroup Circle x ≃* Multiplicative ℤ :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x 1).trans orientation

/-- Basepoint transport along any path preserves the transported integer coordinates. -/
theorem map_path (orientation : FundamentalOrientation) {x y : Circle} (p : Path x y) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p).trans (orientation.equiv y) =
      orientation.equiv x := by
  -- Integer coordinates make every circle fundamental group commutative.
  have commutative : IsMulCommutative π₁(Circle, x) :=
    IsMulCommutative.of_comm fun a b ↦ by
      apply MulOpposite.unop_injective
      apply (orientation.equiv x).injective
      simp only [MulOpposite.unop_mul, map_mul]
      exact mul_comm _ _
  -- Path independence identifies the given basepoint change with the chosen one.
  let q : Path y 1 := PathConnectedSpace.somePath y 1
  have path_eq :=
    (FundamentalGroup.LeftToRight.mulEquivOfPath_independent_iff x 1).mpr commutative
      (p.trans q) (PathConnectedSpace.somePath x 1)
  rw [FundamentalGroup.LeftToRight.mulEquivOfPath_trans] at path_eq
  unfold equiv
  exact congrArg (fun e ↦ e.trans orientation) (congrArg MulEquiv.unop path_eq)

/-- Helper for Exercise 58.9: left-to-right basepoint change preserves orientation
coordinates after returning to the raw fundamental group. -/
private lemma map_path_unop (orientation : FundamentalOrientation) {x y : Circle}
    (p : Path x y) (a : π₁(Circle, x)) :
    orientation.equiv y ((FundamentalGroup.LeftToRight.mulEquivOfPath p a).unop) =
      orientation.equiv x a.unop := by
  -- Evaluate the raw basepoint-change coordinate identity on the underlying loop.
  exact DFunLike.congr_fun (map_path orientation p) a.unop

end FundamentalOrientation

end Circle

namespace CircleMap

/-- The degree of a continuous circle map computed at a specified basepoint. -/
def degreeAt (orientation : Circle.FundamentalOrientation) (h : C(Circle, Circle))
    (x : Circle) : ℤ :=
  Multiplicative.toAdd
    (orientation.equiv (h x)
      (FundamentalGroup.map h x
        ((orientation.equiv x).symm (Multiplicative.ofAdd 1))))

/-- The degree of a continuous circle map, computed at the standard basepoint `1`. -/
def degree (orientation : Circle.FundamentalOrientation) (h : C(Circle, Circle)) : ℤ :=
  degreeAt orientation h 1

/-- Helper for Exercise 58.9: the induced map sends integer coordinate `n` to
`degreeAt orientation h x * n`. -/
lemma degreeAt_map_integer (orientation : Circle.FundamentalOrientation)
    (h : C(Circle, Circle)) (x : Circle) (n : ℤ) :
    orientation.equiv (h x)
        (FundamentalGroup.map h x
          ((orientation.equiv x).symm (Multiplicative.ofAdd n))) =
      Multiplicative.ofAdd (degreeAt orientation h x * n) := by
  -- Express the input as an integer power of the chosen generator and map that power.
  have input_power :
      (orientation.equiv x).symm (Multiplicative.ofAdd n) =
        ((orientation.equiv x).symm (Multiplicative.ofAdd 1)) ^ n := by
    rw [← map_zpow]
    exact congrArg (orientation.equiv x).symm
      (by rw [← ofAdd_zsmul]; simp)
  rw [input_power, map_zpow, map_zpow]
  unfold degreeAt
  rw [← ofAdd_toAdd ((orientation.equiv (h x))
    ((FundamentalGroup.map h x) ((orientation.equiv x).symm (Multiplicative.ofAdd 1))) ^ n)]
  simp only [toAdd_zpow, zsmul_eq_mul, Int.cast_id]
  rw [mul_comm]

/-- Helper for Exercise 58.9: the pointed induced map sends the chosen generator
to the multiplicative integer representing the degree at that basepoint. -/
lemma degreeAt_mapOfEq (orientation : Circle.FundamentalOrientation)
    (h : C(Circle, Circle)) (x y : Circle) (hx : h x = y) :
    orientation.equiv y
        (FundamentalGroup.mapOfEq h hx
          ((orientation.equiv x).symm (Multiplicative.ofAdd 1))) =
      Multiplicative.ofAdd (degreeAt orientation h x) := by
  -- Eliminate the endpoint equality so the pointed map reduces to the raw induced map.
  subst y
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  unfold degreeAt FundamentalGroup.map
  exact ofAdd_toAdd _

/-- Helper for Exercise 58.9: a pointed induced map with a reflexive endpoint proof
is the ordinary induced map in left-to-right convention. -/
private lemma mapOfEq_rfl {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    FundamentalGroup.LeftToRight.mapOfEq f (rfl : f x = f x) = (f₍x₎)₊ := by
  -- Extensionality reduces the adapter to the quotient's reflexive cast computation.
  ext a
  simp only [FundamentalGroup.LeftToRight.mapOfEq_apply,
    FundamentalGroup.LeftToRight.map_apply, Path.Homotopic.Quotient.cast_rfl_rfl,
    FundamentalGroup.map_apply]

/-- Helper for Exercise 58.9: the left-to-right pointed induced map has degree
coordinate on the chosen generator. -/
private lemma degreeAt_leftMapOfEq (orientation : Circle.FundamentalOrientation)
    (h : C(Circle, Circle)) (x y : Circle) (hx : h x = y) :
    orientation.equiv y
        ((FundamentalGroup.LeftToRight.mapOfEq h hx
          (MulOpposite.op
            ((orientation.equiv x).symm (Multiplicative.ofAdd 1)))).unop) =
      Multiplicative.ofAdd (degreeAt orientation h x) := by
  -- Unopping the left-to-right map exposes the raw pointed induced map.
  exact degreeAt_mapOfEq orientation h x y hx

/-- Helper for Exercise 58.9: the left-to-right induced map sends integer
coordinate `n` to multiplication by the degree at the source basepoint. -/
private lemma degreeAt_leftMap_integer (orientation : Circle.FundamentalOrientation)
    (h : C(Circle, Circle)) (x : Circle) (n : ℤ) :
    orientation.equiv (h x)
        (((h₍x₎)₊
          (MulOpposite.op
            ((orientation.equiv x).symm (Multiplicative.ofAdd n)))).unop) =
      Multiplicative.ofAdd (degreeAt orientation h x * n) := by
  -- Unopping the left-to-right map exposes the raw induced-map formula.
  exact degreeAt_map_integer orientation h x n

/-- Helper for Exercise 58.9: the left-to-right pointed induced map sends every
integer coordinate to multiplication by the degree. -/
private lemma degreeAt_leftMapOfEq_integer (orientation : Circle.FundamentalOrientation)
    (h : C(Circle, Circle)) (x y : Circle) (hx : h x = y) (n : ℤ) :
    orientation.equiv y
        ((FundamentalGroup.LeftToRight.mapOfEq h hx
          (MulOpposite.op
            ((orientation.equiv x).symm (Multiplicative.ofAdd n)))).unop) =
      Multiplicative.ofAdd (degreeAt orientation h x * n) := by
  -- Eliminate the endpoint equality and reuse the stable raw integer-coordinate formula.
  subst y
  rw [mapOfEq_rfl]
  exact degreeAt_leftMap_integer orientation h x n

/-- Helper for Exercise 58.9: a commuting basepoint-change square has equal degree
coordinates when evaluated on the chosen orientation generator. -/
private lemma degreeAt_eq_of_generatorSquare (orientation : Circle.FundamentalOrientation)
    (h k : C(Circle, Circle)) (x y x' y' : Circle)
    (hx : h x = x') (hy : k y = y') (p : Path x y) (q : Path x' y')
    (square :
      (FundamentalGroup.LeftToRight.mulEquivOfPath q).toMonoidHom.comp
          (FundamentalGroup.LeftToRight.mapOfEq h hx) =
        (FundamentalGroup.LeftToRight.mapOfEq k hy).comp
          (FundamentalGroup.LeftToRight.mulEquivOfPath p).toMonoidHom) :
    degreeAt orientation h x = degreeAt orientation k y := by
  -- Evaluate the supplied square only on the orientation generator at `x`.
  have evaluated := DFunLike.congr_fun square
    (MulOpposite.op ((orientation.equiv x).symm (Multiplicative.ofAdd 1)))
  change FundamentalGroup.LeftToRight.mulEquivOfPath q
      (FundamentalGroup.LeftToRight.mapOfEq h hx
        (MulOpposite.op ((orientation.equiv x).symm (Multiplicative.ofAdd 1)))) =
    FundamentalGroup.LeftToRight.mapOfEq k hy
      (FundamentalGroup.LeftToRight.mulEquivOfPath p
        (MulOpposite.op ((orientation.equiv x).symm (Multiplicative.ofAdd 1)))) at evaluated
  have generator_transport :
      FundamentalGroup.LeftToRight.mulEquivOfPath p
          (MulOpposite.op ((orientation.equiv x).symm (Multiplicative.ofAdd 1))) =
        MulOpposite.op ((orientation.equiv y).symm (Multiplicative.ofAdd 1)) := by
    -- Orientation coordinates identify the transported generator with coordinate one.
    apply MulOpposite.unop_injective
    apply (orientation.equiv y).injective
    calc
      orientation.equiv y
          ((FundamentalGroup.LeftToRight.mulEquivOfPath p
            (MulOpposite.op
              ((orientation.equiv x).symm (Multiplicative.ofAdd 1)))).unop) =
          orientation.equiv x
            ((MulOpposite.op
              ((orientation.equiv x).symm (Multiplicative.ofAdd 1))).unop) :=
        Circle.FundamentalOrientation.map_path_unop orientation p _
      _ = Multiplicative.ofAdd 1 :=
        MulEquiv.apply_symm_apply (orientation.equiv x) (Multiplicative.ofAdd 1)
      _ = orientation.equiv y
            ((MulOpposite.op
              ((orientation.equiv y).symm (Multiplicative.ofAdd 1))).unop) :=
        (MulEquiv.apply_symm_apply (orientation.equiv y) (Multiplicative.ofAdd 1)).symm
  -- Rewrite each pointed-map edge and each path-transport edge in integer coordinates.
  have coordinate_eq :
      Multiplicative.ofAdd (degreeAt orientation h x) =
        Multiplicative.ofAdd (degreeAt orientation k y) := by
    have transported := congrArg (fun a : π₁(Circle, y') ↦ orientation.equiv y' a.unop)
      evaluated
    have left_coordinate :
        orientation.equiv y'
            ((FundamentalGroup.LeftToRight.mulEquivOfPath q
              (FundamentalGroup.LeftToRight.mapOfEq h hx
                (MulOpposite.op
                  ((orientation.equiv x).symm (Multiplicative.ofAdd 1))))).unop) =
          Multiplicative.ofAdd (degreeAt orientation h x) := by
      rw [Circle.FundamentalOrientation.map_path_unop, degreeAt_leftMapOfEq]
    have right_coordinate :
        orientation.equiv y'
            ((FundamentalGroup.LeftToRight.mapOfEq k hy
              (FundamentalGroup.LeftToRight.mulEquivOfPath p
                (MulOpposite.op
                  ((orientation.equiv x).symm (Multiplicative.ofAdd 1))))).unop) =
          Multiplicative.ofAdd (degreeAt orientation k y) := by
      rw [generator_transport, degreeAt_leftMapOfEq]
    calc
      Multiplicative.ofAdd (degreeAt orientation h x) =
          orientation.equiv y'
            ((FundamentalGroup.LeftToRight.mulEquivOfPath q
              (FundamentalGroup.LeftToRight.mapOfEq h hx
                (MulOpposite.op
                  ((orientation.equiv x).symm (Multiplicative.ofAdd 1))))).unop) :=
        left_coordinate.symm
      _ = orientation.equiv y'
            ((FundamentalGroup.LeftToRight.mapOfEq k hy
              (FundamentalGroup.LeftToRight.mulEquivOfPath p
                (MulOpposite.op
                  ((orientation.equiv x).symm (Multiplicative.ofAdd 1))))).unop) := by
        exact transported
      _ = Multiplicative.ofAdd (degreeAt orientation k y) := right_coordinate
  -- Return from multiplicative integers to ordinary integers.
  exact congrArg Multiplicative.toAdd coordinate_eq

/-- Computing the degree at any basepoint gives the degree at the standard basepoint. -/
theorem degreeAt_eq_degree (orientation : Circle.FundamentalOrientation)
    (h : C(Circle, Circle)) (x : Circle) :
    degreeAt orientation h x = degree orientation h := by
  -- Apply pointed-map naturality along a path from `x` to the standard basepoint.
  let p : Path x 1 := PathConnectedSpace.somePath x 1
  have square := FundamentalGroup.LeftToRight.mapOfEq_naturality_hom
    h x 1 (h x) (h 1) rfl rfl p
  have degree_at_eq := degreeAt_eq_of_generatorSquare orientation h h x 1 (h x) (h 1)
    rfl rfl p (p.map h.continuous) square
  simpa only [degree] using degree_at_eq

/-- Helper for Exercise 58.9: changing integer coordinates between two circle
orientations is either the identity or negation. -/
private lemma orientationChange_eq_refl_or_neg
    (orientation₁ orientation₂ : Circle.FundamentalOrientation) :
    let change :=
      ((orientation₁.equiv 1).symm.trans (orientation₂.equiv 1)).toAdditive
    change = AddEquiv.refl ℤ ∨ change = AddEquiv.neg ℤ := by
  -- Classify the additive automorphism underlying the coordinate change.
  exact Int.addEquiv_eq_refl_or_neg _

/-- Helper for Exercise 58.9: changing between two orientations is independent
of the basepoint used to express the integer coordinates. -/
private lemma orientationChange_eq (orientation₁ orientation₂ : Circle.FundamentalOrientation)
    (x : Circle) :
    (orientation₁.equiv x).symm.trans (orientation₂.equiv x) =
      (orientation₁.equiv 1).symm.trans (orientation₂.equiv 1) := by
  -- Both transported orientations contain the same basepoint-change equivalence,
  -- which cancels from the coordinate comparison.
  ext a
  simp [Circle.FundamentalOrientation.equiv]

/-- Helper for Exercise 58.9: the orientation change computes coordinates at
every basepoint by the same additive automorphism of integers. -/
private lemma orientationChange_apply (orientation₁ orientation₂ : Circle.FundamentalOrientation)
    (x : Circle) (n : ℤ) :
    orientation₂.equiv x
        ((orientation₁.equiv x).symm (Multiplicative.ofAdd n)) =
      Multiplicative.ofAdd
        (((orientation₁.equiv 1).symm.trans
          (orientation₂.equiv 1)).toAdditive n) := by
  -- Rewrite to the basepoint-independent coordinate change and evaluate it at `n`.
  have change_eq := DFunLike.congr_fun
    (orientationChange_eq orientation₁ orientation₂ x) (Multiplicative.ofAdd n)
  exact change_eq

/-- The degree of a circle map is independent of the chosen fundamental orientation. -/
theorem degree_eq (orientation₁ orientation₂ : Circle.FundamentalOrientation)
    (h : C(Circle, Circle)) : degree orientation₁ h = degree orientation₂ h := by
  -- Route correction: classify the complete integer coordinate change, rather than
  -- transporting a single generator through raw fundamental-group maps.
  let change :=
    ((orientation₁.equiv 1).symm.trans (orientation₂.equiv 1)).toAdditive
  rcases orientationChange_eq_refl_or_neg orientation₁ orientation₂ with change_eq | change_eq
  · -- In identical coordinates, the two degree computations agree directly.
    have change_apply (n : ℤ) :
        ((orientation₁.equiv 1).symm.trans
          (orientation₂.equiv 1)).toAdditive n = n := by
      exact DFunLike.congr_fun change_eq n
    have source_generator :
        (orientation₂.equiv 1).symm (Multiplicative.ofAdd 1) =
          (orientation₁.equiv 1).symm (Multiplicative.ofAdd 1) := by
      apply (orientation₂.equiv 1).injective
      rw [orientationChange_apply orientation₁ orientation₂, change_apply]
      exact MulEquiv.apply_symm_apply _ _
    have mapped_generator :
        FundamentalGroup.map h 1
            ((orientation₁.equiv 1).symm (Multiplicative.ofAdd 1)) =
          (orientation₁.equiv (h 1)).symm
            (Multiplicative.ofAdd (degree orientation₁ h)) := by
      apply (orientation₁.equiv (h 1)).injective
      simpa [degree] using
        degreeAt_map_integer orientation₁ h 1 1
    have coordinate_eq :
        orientation₂.equiv (h 1)
            (FundamentalGroup.map h 1
              ((orientation₂.equiv 1).symm (Multiplicative.ofAdd 1))) =
          Multiplicative.ofAdd (degree orientation₁ h) := by
      rw [source_generator, mapped_generator,
        orientationChange_apply orientation₁ orientation₂, change_apply]
      rfl
    simpa [degree, degreeAt] using (congrArg Multiplicative.toAdd coordinate_eq).symm
  · -- Negating both source and target coordinates leaves the multiplier unchanged.
    have change_apply (n : ℤ) :
        ((orientation₁.equiv 1).symm.trans
          (orientation₂.equiv 1)).toAdditive n = -n := by
      exact DFunLike.congr_fun change_eq n
    have source_generator :
        (orientation₂.equiv 1).symm (Multiplicative.ofAdd 1) =
          (orientation₁.equiv 1).symm (Multiplicative.ofAdd (-1)) := by
      apply (orientation₂.equiv 1).injective
      rw [orientationChange_apply orientation₁ orientation₂, change_apply]
      rw [MulEquiv.apply_symm_apply]
      exact congrArg Multiplicative.ofAdd (neg_neg (1 : ℤ))
    have mapped_generator :
        FundamentalGroup.map h 1
            ((orientation₁.equiv 1).symm (Multiplicative.ofAdd (-1))) =
          (orientation₁.equiv (h 1)).symm
            (Multiplicative.ofAdd (-(degree orientation₁ h))) := by
      apply (orientation₁.equiv (h 1)).injective
      simpa [degree] using
        degreeAt_map_integer orientation₁ h 1 (-1)
    have coordinate_eq :
        orientation₂.equiv (h 1)
            (FundamentalGroup.map h 1
              ((orientation₂.equiv 1).symm (Multiplicative.ofAdd 1))) =
          Multiplicative.ofAdd (degree orientation₁ h) := by
      rw [source_generator, mapped_generator,
        orientationChange_apply orientation₁ orientation₂, change_apply]
      exact congrArg Multiplicative.ofAdd (neg_neg (degree orientation₁ h))
    simpa [degree, degreeAt] using (congrArg Multiplicative.toAdd coordinate_eq).symm

/-- Homotopic continuous circle maps have equal degrees. -/
theorem degree_eq_of_homotopic (orientation : Circle.FundamentalOrientation)
    (h k : C(Circle, Circle)) (homotopic : h.Homotopic k) :
    degree orientation h = degree orientation k := by
  -- Evaluate the homotopy at the standard basepoint to obtain its target path and square.
  obtain ⟨q, square⟩ :=
    FundamentalGroup.exists_path_map_eq_basepointChange_comp_of_homotopic h k 1 homotopic
  have refl_change :
      (FundamentalGroup.LeftToRight.mulEquivOfPath
        (Path.refl (1 : Circle))).toMonoidHom = MonoidHom.id _ := by
    -- Orientation coordinates show that reflexive basepoint change fixes every loop.
    ext a
    apply MulOpposite.unop_injective
    apply (orientation.equiv 1).injective
    change orientation.equiv 1
        ((FundamentalGroup.LeftToRight.mulEquivOfPath (Path.refl (1 : Circle)) a).unop) =
      orientation.equiv 1 a.unop
    exact Circle.FundamentalOrientation.map_path_unop orientation
      (Path.refl (1 : Circle)) a
  have pointed_square :
      (FundamentalGroup.LeftToRight.mulEquivOfPath q).toMonoidHom.comp
          (FundamentalGroup.LeftToRight.mapOfEq h rfl) =
        (FundamentalGroup.LeftToRight.mapOfEq k rfl).comp
          (FundamentalGroup.LeftToRight.mulEquivOfPath
            (Path.refl (1 : Circle))).toMonoidHom := by
    rw [mapOfEq_rfl, mapOfEq_rfl]
    calc
      (FundamentalGroup.LeftToRight.mulEquivOfPath q).toMonoidHom.comp (h₍1₎)₊ =
          (k₍1₎)₊ := square.symm
      _ = (k₍1₎)₊.comp
          (FundamentalGroup.LeftToRight.mulEquivOfPath
            (Path.refl (1 : Circle))).toMonoidHom := by
        ext a
        simp only [MonoidHom.comp_apply, refl_change, MonoidHom.id_apply]
  -- The generator-square interface converts this commuting square to degree equality.
  exact degreeAt_eq_of_generatorSquare orientation h k 1 1 (h 1) (k 1)
    rfl rfl (Path.refl (1 : Circle)) q pointed_square

/-- Helper for Exercise 58.9: the induced map of a composite multiplies integer
coordinates successively by the degrees of its two factors. -/
private lemma degreeAt_comp_coordinate (orientation : Circle.FundamentalOrientation)
    (h k : C(Circle, Circle)) (x : Circle) (n : ℤ) :
    orientation.equiv ((h.comp k) x)
        ((((h.comp k)₍x₎)₊
          (MulOpposite.op
            ((orientation.equiv x).symm (Multiplicative.ofAdd n)))).unop) =
      Multiplicative.ofAdd
        (degreeAt orientation h (k x) * degreeAt orientation k x * n) := by
  -- First identify the inner induced-map value by its integer coordinate.
  have inner_eq :
      (k₍x₎)₊
          (MulOpposite.op
            ((orientation.equiv x).symm (Multiplicative.ofAdd n))) =
        MulOpposite.op
          ((orientation.equiv (k x)).symm
            (Multiplicative.ofAdd (degreeAt orientation k x * n))) := by
    apply MulOpposite.unop_injective
    apply (orientation.equiv (k x)).injective
    calc
      orientation.equiv (k x)
          (((k₍x₎)₊
            (MulOpposite.op
              ((orientation.equiv x).symm (Multiplicative.ofAdd n)))).unop) =
          Multiplicative.ofAdd (degreeAt orientation k x * n) :=
        degreeAt_leftMap_integer orientation k x n
      _ = orientation.equiv (k x)
          ((MulOpposite.op
            ((orientation.equiv (k x)).symm
              (Multiplicative.ofAdd (degreeAt orientation k x * n)))).unop) := by
        exact (MulEquiv.apply_symm_apply (orientation.equiv (k x)) _).symm
  -- Functoriality exposes the two induced maps, after which the outer coordinate
  -- formula supplies the second degree factor.
  have core :
      orientation.equiv (h (k x))
          ((((h₍(k x)₎)₊.comp (k₍x₎)₊)
            (MulOpposite.op
              ((orientation.equiv x).symm (Multiplicative.ofAdd n)))).unop) =
        Multiplicative.ofAdd
          (degreeAt orientation h (k x) * degreeAt orientation k x * n) := by
    rw [MonoidHom.comp_apply]
    rw [inner_eq]
    simpa only [mul_assoc] using
      degreeAt_leftMap_integer orientation h (k x) (degreeAt orientation k x * n)
  rw [FundamentalGroup.LeftToRight.map_comp]
  exact core

/-- The degree of a composite of continuous circle maps is the product of their degrees. -/
theorem degree_comp (orientation : Circle.FundamentalOrientation) (h k : C(Circle, Circle)) :
    degree orientation (h.comp k) = degree orientation h * degree orientation k := by
  -- Evaluate the composite-coordinate formula on the standard generator.
  have coordinate := degreeAt_comp_coordinate orientation h k 1 1
  have degree_at_comp :
      degreeAt orientation (h.comp k) 1 =
        degreeAt orientation h (k 1) * degreeAt orientation k 1 := by
    have direct := degreeAt_leftMap_integer orientation (h.comp k) 1 1
    have multiplicative_eq := direct.symm.trans coordinate
    simpa using congrArg Multiplicative.toAdd multiplicative_eq
  rw [degree, degree_at_comp, degreeAt_eq_degree orientation h (k 1),
    degreeAt_eq_degree orientation k 1]

/-- Every constant continuous self-map of the circle has degree zero. -/
theorem degree_const (orientation : Circle.FundamentalOrientation) (c : Circle) :
    degree orientation (ContinuousMap.const Circle c) = 0 := by
  -- Every two constant circle maps are homotopic because the circle is path connected.
  have constants_homotopic :
      (ContinuousMap.const Circle c).Homotopic (ContinuousMap.const Circle (1 : Circle)) := by
    rw [ContinuousMap.homotopic_const_iff]
    exact ⟨PathConnectedSpace.somePath c 1⟩
  have zpower_zero : zpower 0 = ContinuousMap.const Circle (1 : Circle) := by
    ext z
    simp [zpower_apply]
  have zero_degree : degree orientation (zpower 0) = 0 := by
    -- Evaluate the known pointed induced-map formula on the chosen generator.
    have induced := DFunLike.congr_fun (induced_zpower 0 (orientation.equiv 1))
      ((orientation.equiv 1).symm (Multiplicative.ofAdd 1))
    change orientation.equiv 1
        (FundamentalGroup.mapOfEq (zpower 0) (zpower_one 0)
          ((orientation.equiv 1).symm (Multiplicative.ofAdd 1))) =
      zpowGroupHom 0 (orientation.equiv 1
        ((orientation.equiv 1).symm (Multiplicative.ofAdd 1))) at induced
    rw [degreeAt_mapOfEq orientation (zpower 0) 1 1 (zpower_one 0)] at induced
    simp only [MulEquiv.apply_symm_apply, zpowGroupHom_apply] at induced
    simpa [degree] using congrArg Multiplicative.toAdd induced
  -- Homotopy invariance reduces the constant map to the zero-th power map.
  calc
    degree orientation (ContinuousMap.const Circle c) =
        degree orientation (ContinuousMap.const Circle (1 : Circle)) :=
      degree_eq_of_homotopic orientation _ _ constants_homotopic
    _ = degree orientation (zpower 0) := congrArg (degree orientation) zpower_zero.symm
    _ = 0 := zero_degree

/-- Reflection across the real axis, realized as inversion on the complex unit circle. -/
def reflection : C(Circle, Circle) :=
  (ContinuousMap.id Circle)⁻¹

/-- Helper for Exercise 58.9: every integer-power circle map has its exponent as degree. -/
lemma degree_zpower (orientation : Circle.FundamentalOrientation) (k : ℤ) :
    degree orientation (zpower k) = k := by
  -- Evaluate the known pointed induced-map formula on the chosen coordinate-one generator.
  have induced := DFunLike.congr_fun (induced_zpower k (orientation.equiv 1))
    ((orientation.equiv 1).symm (Multiplicative.ofAdd 1))
  change orientation.equiv 1
      (FundamentalGroup.mapOfEq (zpower k) (zpower_one k)
        ((orientation.equiv 1).symm (Multiplicative.ofAdd 1))) =
    zpowGroupHom k (orientation.equiv 1
      ((orientation.equiv 1).symm (Multiplicative.ofAdd 1))) at induced
  rw [degreeAt_mapOfEq orientation (zpower k) 1 1 (zpower_one k)] at induced
  simp only [MulEquiv.apply_symm_apply, zpowGroupHom_apply] at induced
  simpa [degree] using congrArg Multiplicative.toAdd induced

/-- The identity continuous self-map of the circle has degree one. -/
theorem degree_id (orientation : Circle.FundamentalOrientation) :
    degree orientation (ContinuousMap.id Circle) = 1 := by
  -- Identify the identity map with the first integer-power map.
  have map_eq : (ContinuousMap.id Circle) = zpower 1 := by
    ext z
    simp [zpower_apply]
  rw [map_eq]
  exact degree_zpower orientation 1

/-- Reflection across the real axis has degree negative one. -/
theorem degree_reflection (orientation : Circle.FundamentalOrientation) :
    degree orientation reflection = -1 := by
  -- Identify inversion with the negative-first integer-power map.
  have map_eq : reflection = zpower (-1) := by
    ext z
    simp [reflection, zpower_apply]
  rw [map_eq]
  exact degree_zpower orientation (-1)

/-- The map `z ↦ z ^ n` has degree `n`. -/
theorem degree_power (orientation : Circle.FundamentalOrientation) (n : ℕ) :
    degree orientation (zpower (n : ℤ)) = (n : ℤ) := by
  -- Specialize the integer-power computation to a natural exponent.
  exact degree_zpower orientation n

/-- Helper for Exercise 58.9: normalize a circle map by translating its value at
the standard basepoint to the identity. -/
private def basedNormalize (h : C(Circle, Circle)) : C(Circle, Circle) :=
  (ContinuousMap.mulLeft (h 1)⁻¹).comp h

/-- Helper for Exercise 58.9: the normalized map is pointwise left translation
by the inverse of the original basepoint value. -/
private lemma basedNormalize_apply (h : C(Circle, Circle)) (z : Circle) :
    basedNormalize h z = (h 1)⁻¹ * h z := by
  -- Unfold the composition and the canonical left-multiplication map.
  rfl

/-- Helper for Exercise 58.9: the normalized map fixes the standard basepoint. -/
private lemma basedNormalize_one (h : C(Circle, Circle)) : basedNormalize h 1 = 1 := by
  -- The translating factor is the inverse of the basepoint value.
  rw [basedNormalize_apply, inv_mul_cancel]

/-- Helper for Exercise 58.9: left translation supplies a homotopy from a map to
its based normalization. -/
private lemma homotopic_basedNormalize (h : C(Circle, Circle)) :
    h.Homotopic (basedNormalize h) := by
  -- Move the left factor from `1` to `(h 1)⁻¹` along a path in the circle.
  have constants_homotopic :
      (ContinuousMap.const Circle (1 : Circle)).Homotopic
        (ContinuousMap.const Circle (h 1)⁻¹) := by
    rw [ContinuousMap.homotopic_const_iff]
    exact ⟨PathConnectedSpace.somePath 1 (h 1)⁻¹⟩
  have paired := constants_homotopic.prodMk (ContinuousMap.Homotopic.refl h)
  let multiply : C(Circle × Circle, Circle) := ⟨fun z ↦ z.1 * z.2, continuous_mul⟩
  have multiplied := (ContinuousMap.Homotopic.refl multiply).comp paired
  have source_eq :
      multiply.comp ((ContinuousMap.const Circle (1 : Circle)).prodMk h) = h := by
    ext z
    simp [multiply]
  have target_eq :
      multiply.comp ((ContinuousMap.const Circle (h 1)⁻¹).prodMk h) = basedNormalize h := by
    ext z
    simp [multiply, basedNormalize_apply]
  -- Replace the multiplication homotopy's endpoints by the intended maps.
  rw [source_eq, target_eq] at multiplied
  exact multiplied

/-- Helper for Exercise 58.9: normalization preserves degree. -/
private lemma degree_basedNormalize (orientation : Circle.FundamentalOrientation)
    (h : C(Circle, Circle)) :
    degree orientation (basedNormalize h) = degree orientation h := by
  -- Homotopy invariance identifies the degree before and after normalization.
  exact (degree_eq_of_homotopic orientation h (basedNormalize h)
    (homotopic_basedNormalize h)).symm

/-- Helper for Exercise 58.9: based circle maps with equal degree induce the
same homomorphism on the fundamental group at the standard basepoint. -/
private lemma induced_eq_of_based_degree_eq (orientation : Circle.FundamentalOrientation)
    (f g : C(Circle, Circle)) (hf : f 1 = 1) (hg : g 1 = 1)
    (degree_eq : degree orientation f = degree orientation g) :
    FundamentalGroup.LeftToRight.mapOfEq f hf =
      FundamentalGroup.LeftToRight.mapOfEq g hg := by
  -- Every loop has a unique integer coordinate, so compare both induced maps there.
  ext a
  apply MulOpposite.unop_injective
  apply (orientation.equiv 1).injective
  let n : ℤ := Multiplicative.toAdd (orientation.equiv 1 a.unop)
  have a_eq :
      a = MulOpposite.op ((orientation.equiv 1).symm (Multiplicative.ofAdd n)) := by
    apply MulOpposite.unop_injective
    apply (orientation.equiv 1).injective
    simp [n]
  rw [a_eq]
  rw [degreeAt_leftMapOfEq_integer orientation f 1 1 hf n,
    degreeAt_leftMapOfEq_integer orientation g 1 1 hg n]
  exact congrArg Multiplicative.ofAdd (congrArg (fun d : ℤ ↦ d * n) degree_eq)

/-- Helper for Exercise 58.9: based circle maps with equal induced maps are
homotopic. -/
private lemma basedHomotopic_of_induced_eq (f g : C(Circle, Circle))
    (hf : f 1 = 1) (hg : g 1 = 1)
    (induced_eq : FundamentalGroup.LeftToRight.mapOfEq f hf =
      FundamentalGroup.LeftToRight.mapOfEq g hg) :
    f.Homotopic g := by
  -- Route correction: avoid the transport-heavy pointwise quotient and lift the
  -- two based maps separately to the universal cover.
  obtain ⟨F, d, hF0, hF_lifts, hF_translate⟩ :=
    exists_basedLift_with_deckTranslation f hf
  obtain ⟨G, e, hG0, hG_lifts, hG_translate⟩ :=
    exists_basedLift_with_deckTranslation g hg
  -- Evaluate the induced-map equality on the fixed positive turn loop.
  let generator : π₁(Circle, 1) :=
    MulOpposite.op (Path.Homotopic.Quotient.mk standardTurnLoop)
  have mapped_generator_eq := DFunLike.congr_fun induced_eq generator
  have mapped_loop_eq :
      (FundamentalGroup.fromPath ((Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk standardTurnLoop) f).cast hf.symm hf.symm)) =
      FundamentalGroup.fromPath ((Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk standardTurnLoop) g).cast hg.symm hg.symm) := by
    have unop_eq := congrArg MulOpposite.unop mapped_generator_eq
    simpa only [generator, FundamentalGroup.LeftToRight.mapOfEq_apply,
      MulOpposite.unop_op] using unop_eq
  -- Monodromy turns equality of mapped loop classes into equality of lift endpoints.
  have endpoint_eq : F 1 = G 1 := by
    have monodromy_eq := congrArg
      (fun γ : FundamentalGroup Circle 1 ↦
        (Circle.isCoveringMap_turnExp.monodromy (FundamentalGroup.toPath γ)
          ⟨0, Circle.turnExp_zero⟩).1) mapped_loop_eq
    rw [monodromy_map_turnPath_eq_lift_one f hf F hF0 hF_lifts,
      monodromy_map_turnPath_eq_lift_one g hg G hG0 hG_lifts] at monodromy_eq
    exact monodromy_eq
  -- The endpoint of each lift is its displayed integral deck translation.
  have d_eq_e : d = e := by
    have F_one : F 1 = (d : ℝ) := by
      have translated := hF_translate 0
      simpa [hF0] using translated
    have G_one : G 1 = (e : ℝ) := by
      have translated := hG_translate 0
      simpa [hG0] using translated
    exact_mod_cast F_one.symm.trans (endpoint_eq.trans G_one)
  subst e
  -- The common deck translation makes the affine interpolation descend.
  exact homotopic_of_basedLifts_sameDeckTranslation f g F G d hF_lifts hG_lifts
    hF_translate hG_translate

/-- Continuous circle maps with equal degrees are homotopic. -/
theorem homotopic_of_degree_eq (orientation : Circle.FundamentalOrientation)
    (h k : C(Circle, Circle)) (degree_eq : degree orientation h = degree orientation k) :
    h.Homotopic k := by
  -- Normalize both maps, compare their based induced maps, and use based classification.
  have normalized_degree_eq :
      degree orientation (basedNormalize h) = degree orientation (basedNormalize k) := by
    rw [degree_basedNormalize, degree_basedNormalize, degree_eq]
  have normalized_induced_eq :
      FundamentalGroup.LeftToRight.mapOfEq (basedNormalize h) (basedNormalize_one h) =
        FundamentalGroup.LeftToRight.mapOfEq (basedNormalize k) (basedNormalize_one k) :=
    induced_eq_of_based_degree_eq orientation (basedNormalize h) (basedNormalize k)
      (basedNormalize_one h) (basedNormalize_one k) normalized_degree_eq
  have normalized_homotopic := basedHomotopic_of_induced_eq (basedNormalize h)
    (basedNormalize k) (basedNormalize_one h) (basedNormalize_one k) normalized_induced_eq
  exact (homotopic_basedNormalize h).trans
    (normalized_homotopic.trans (homotopic_basedNormalize k).symm)


end CircleMap
