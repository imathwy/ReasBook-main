module

public import Topology_Munkres_2000.Book.Example_54_1
public import Topology_Munkres_2000.Book.Definition_52_5.Convention
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Algebra.Module.LocallyConvex

noncomputable section

public section

namespace Circle

/-- Helper for Exercise 58.9: two real parameters have the same image under
`turnExp` exactly when they differ by an integer. -/
theorem turnExp_eq_iff_sub_int (x y : ℝ) :
    turnExp x = turnExp y ↔ ∃ n : ℤ, x = y + n := by
  -- Reduce equality in the covering fiber to the standard exponential period.
  constructor
  · intro hxy
    have exponential_eq :
        Circle.exp (2 * Real.pi * x) = Circle.exp (2 * Real.pi * y) := by
      apply Circle.ext
      have hval := congrArg Subtype.val hxy
      rw [Circle.coe_turnExp, Circle.coe_turnExp] at hval
      simpa [Circle.coe_exp, Complex.exp_mul_I] using hval
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp exponential_eq
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    apply (mul_left_cancel₀ hpi)
    calc
      (2 * Real.pi) * x = 2 * Real.pi * x := rfl
      _ = 2 * Real.pi * y + n * (2 * Real.pi) := hn
      _ = (2 * Real.pi) * (y + n) := by ring
  · rintro ⟨n, rfl⟩
    have exponential_eq :
        Circle.exp (2 * Real.pi * (y + n)) = Circle.exp (2 * Real.pi * y) := by
      apply Circle.exp_eq_exp.mpr
      refine ⟨n, ?_⟩
      ring
    apply Circle.ext
    have hval := congrArg Subtype.val exponential_eq
    rw [Circle.coe_turnExp, Circle.coe_turnExp]
    simpa [Circle.coe_exp, Complex.exp_mul_I] using hval

/-- Helper for Exercise 58.9: translating a real parameter by an integer does
not change its image under `turnExp`. -/
theorem turnExp_add_int (x : ℝ) (n : ℤ) : turnExp (x + n) = turnExp x := by
  -- Apply the fiber characterization with the displayed integer translation.
  exact (turnExp_eq_iff_sub_int (x + n) x).2 ⟨n, rfl⟩

end Circle

namespace CircleMap

/-- Helper for Exercise 58.9: the standard positive turn, regarded as a loop
at the circle basepoint. -/
noncomputable def standardTurnLoop : Path (1 : Circle) 1 :=
  (Circle.turnPath 1).cast rfl Circle.turnExp_one.symm

/-- Helper for Exercise 58.9: monodromy of the mapped standard turn loop is
the endpoint of any specified based lift. -/
theorem monodromy_map_turnPath_eq_lift_one (f : C(Circle, Circle))
    (hf : f 1 = 1) (F : C(ℝ, ℝ)) (hF0 : F 0 = 0)
    (hF_lifts : Circle.turnExp ∘ F =
      f.comp ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩) :
    (Circle.isCoveringMap_turnExp.monodromy
      ((Path.Homotopic.Quotient.map
        (Path.Homotopic.Quotient.mk standardTurnLoop) f).cast hf.symm hf.symm)
      ⟨0, Circle.turnExp_zero⟩).1 = F 1 := by
  -- Map the explicit real lift of one turn through `F`.
  let liftedTurn : Path (0 : ℝ) (F 1) :=
    ((Circle.turnLift 1).map F.continuous).cast hF0.symm rfl
  let liftedClass : Path.Homotopic.Quotient (0 : ℝ) (F 1) :=
    Path.Homotopic.Quotient.mk liftedTurn
  have endpoint_fiber : Circle.turnExp (F 1) = 1 := by
    have endpoint := congrFun hF_lifts 1
    change Circle.turnExp (F 1) = f (Circle.turnExp 1) at endpoint
    rwa [Circle.turnExp_one, hf] at endpoint
  have mapped_class_eq :
      liftedClass.map
          ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩ =
        ((Path.Homotopic.Quotient.map
          (Path.Homotopic.Quotient.mk standardTurnLoop) f).cast hf.symm hf.symm).cast
            Circle.turnExp_zero endpoint_fiber := by
    -- Both quotient classes are represented by the same pointwise path after
    -- using the lift equation and the fixed endpoint casts.
    let mappedTurn : Path (Circle.turnExp 0) (Circle.turnExp (F 1)) :=
      (((standardTurnLoop.map f.continuous).cast hf.symm hf.symm).cast
        Circle.turnExp_zero endpoint_fiber)
    have path_eq :
        liftedTurn.map Circle.isCoveringMap_turnExp.continuous = mappedTurn := by
      apply Path.ext
      apply funext
      intro s
      change Circle.turnExp (F (1 * (s : ℝ))) = f (Circle.turnExp (1 * (s : ℝ)))
      exact congrFun hF_lifts (1 * (s : ℝ))
    calc
      liftedClass.map
          ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩ =
          Path.Homotopic.Quotient.mk
            (liftedTurn.map Circle.isCoveringMap_turnExp.continuous) := by
        exact (Path.Homotopic.Quotient.mk_map liftedTurn
          ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩).symm
      _ = Path.Homotopic.Quotient.mk mappedTurn := congrArg _ path_eq
      _ = ((Path.Homotopic.Quotient.map
          (Path.Homotopic.Quotient.mk standardTurnLoop) f).cast hf.symm hf.symm).cast
            Circle.turnExp_zero endpoint_fiber := by
        simp only [mappedTurn, Path.Homotopic.Quotient.mk_cast,
          Path.Homotopic.Quotient.mk_map]
  have monodromy_eq := Circle.isCoveringMap_turnExp.monodromy_eq_of_map_eq
    (γ := ((Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk standardTurnLoop) f).cast hf.symm hf.symm))
    (ex := ⟨0, Circle.turnExp_zero⟩) (ey := ⟨F 1, endpoint_fiber⟩)
    liftedClass mapped_class_eq
  exact congrArg Subtype.val monodromy_eq

/-- Helper for Exercise 58.9: a based circle map has a real lift starting at
zero and equivariant under translation by one. -/
theorem exists_basedLift_with_deckTranslation (f : C(Circle, Circle))
    (hf : f 1 = 1) :
    ∃ (F : C(ℝ, ℝ)) (d : ℤ), F 0 = 0 ∧
      Circle.turnExp ∘ F = f.comp ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩ ∧
      ∀ x : ℝ, F (x + 1) = F x + d := by
  -- Lift the composite from the simply connected universal-cover domain.
  let turnExpMap : C(ℝ, Circle) :=
    ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩
  have basepoint_eq : Circle.turnExp 0 = (f.comp turnExpMap) 0 := by
    change Circle.turnExp 0 = f (Circle.turnExp 0)
    rw [Circle.turnExp_zero, hf]
  obtain ⟨F, ⟨hF0, hF⟩, -⟩ :=
    Circle.isCoveringMap_turnExp.existsUnique_continuousMap_lifts
      (f.comp turnExpMap) 0 0 basepoint_eq
  -- The lifted endpoint over one lies in the integral fiber over the basepoint.
  have hF1_fiber : Circle.turnExp (F 1) = 1 := by
    have endpoint := congrFun hF 1
    change Circle.turnExp (F 1) = f (Circle.turnExp 1) at endpoint
    rw [Circle.turnExp_one, hf] at endpoint
    exact endpoint
  obtain ⟨d, hF1⟩ := (Circle.turnExp_eq_one_iff (F 1)).1 hF1_fiber
  refine ⟨F, d, hF0, hF, fun x ↦ ?_⟩
  -- Uniqueness of covering lifts compares translation in the domain and range.
  let shiftedDomain : ℝ → ℝ := fun z ↦ F (z + 1)
  let shiftedRange : ℝ → ℝ := fun z ↦ F z + d
  have shiftedDomain_continuous : Continuous shiftedDomain := by
    fun_prop
  have shiftedRange_continuous : Continuous shiftedRange := by
    fun_prop
  have shifted_comp : Circle.turnExp ∘ shiftedDomain =
      Circle.turnExp ∘ shiftedRange := by
    funext z
    have at_z_add_one := congrFun hF (z + 1)
    have at_z := congrFun hF z
    have turnExp_add_one : Circle.turnExp (z + 1) = Circle.turnExp z := by
      simpa using Circle.turnExp_add_int z (1 : ℤ)
    calc
      Circle.turnExp (shiftedDomain z) = f (Circle.turnExp (z + 1)) := at_z_add_one
      _ = f (Circle.turnExp z) := congrArg f turnExp_add_one
      _ = Circle.turnExp (F z) := at_z.symm
      _ = Circle.turnExp (shiftedRange z) := by
        symm
        exact Circle.turnExp_add_int (F z) d
  have shifted_zero : shiftedDomain 0 = shiftedRange 0 := by
    simp only [shiftedDomain, shiftedRange, zero_add, hF0, zero_add]
    exact hF1
  have shifted_eq := Circle.isCoveringMap_turnExp.eq_of_comp_eq
    shiftedDomain_continuous shiftedRange_continuous shifted_comp 0 shifted_zero
  exact congrFun shifted_eq x

/-- Helper for Exercise 58.9: a unit deck-translation formula iterates over
every integer translation. -/
theorem lift_add_int (F : ℝ → ℝ) (d : ℤ)
    (hF_translate : ∀ x : ℝ, F (x + 1) = F x + d) (x : ℝ) (n : ℤ) :
    F (x + n) = F x + (d : ℝ) * n := by
  -- Subtract the linear drift, leaving a genuinely periodic function.
  let periodicPart : ℝ → ℝ := fun z ↦ F z - (d : ℝ) * z
  have periodicPart_periodic : Function.Periodic periodicPart 1 := by
    intro z
    dsimp only [periodicPart]
    rw [hF_translate]
    ring
  have periodicPart_eq := (periodicPart_periodic.int_mul n) x
  dsimp only [periodicPart] at periodicPart_eq
  ring_nf at periodicPart_eq ⊢
  linarith

/-- Helper for Exercise 58.9: two based lifts with the same deck translation
descend their affine interpolation to a homotopy of circle maps. -/
theorem homotopic_of_basedLifts_sameDeckTranslation
    (f g : C(Circle, Circle)) (F G : C(ℝ, ℝ)) (d : ℤ)
    (hF_lifts : Circle.turnExp ∘ F =
      f.comp ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩)
    (hG_lifts : Circle.turnExp ∘ G =
      g.comp ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩)
    (hF_translate : ∀ x : ℝ, F (x + 1) = F x + d)
    (hG_translate : ∀ x : ℝ, G (x + 1) = G x + d) :
    f.Homotopic g := by
  -- Interpolate in the universal cover before passing to the quotient circle.
  let interpolation : C(unitInterval × ℝ, Circle) :=
    ⟨fun z ↦ Circle.turnExp
      ((1 - (z.1 : ℝ)) * F z.2 + (z.1 : ℝ) * G z.2),
      Circle.isCoveringMap_turnExp.continuous.comp (by fun_prop)⟩
  let turnExpMap : C(ℝ, Circle) :=
    ⟨Circle.turnExp, Circle.isCoveringMap_turnExp.continuous⟩
  let quotientMap : C(unitInterval × ℝ, unitInterval × Circle) :=
    ⟨fun z ↦ (z.1, Circle.turnExp z.2),
      continuous_fst.prodMk (Circle.isCoveringMap_turnExp.continuous.comp continuous_snd)⟩
  have quotientMap_isQuotient : Topology.IsQuotientMap quotientMap := by
    have turnExp_isOpenQuotient : IsOpenQuotientMap Circle.turnExp :=
      ⟨Circle.turnExp_surjective, Circle.isCoveringMap_turnExp.continuous,
        Circle.isCoveringMap_turnExp.isOpenMap⟩
    exact (IsOpenQuotientMap.id.prodMap turnExp_isOpenQuotient).isQuotientMap
  have interpolation_factors : Function.FactorsThrough interpolation quotientMap := by
    intro a b hab
    change (a.1, Circle.turnExp a.2) = (b.1, Circle.turnExp b.2) at hab
    have time_eq : a.1 = b.1 :=
      congrArg (fun z : unitInterval × Circle ↦ z.1) hab
    have circle_eq : Circle.turnExp a.2 = Circle.turnExp b.2 := by
      exact congrArg Prod.snd hab
    obtain ⟨n, hn⟩ := (Circle.turnExp_eq_iff_sub_int a.2 b.2).1 circle_eq
    have hF_int := lift_add_int F d hF_translate b.2 n
    have hG_int := lift_add_int G d hG_translate b.2 n
    have affine_eq :
        (1 - (a.1 : ℝ)) * F a.2 + (a.1 : ℝ) * G a.2 =
          ((1 - (b.1 : ℝ)) * F b.2 + (b.1 : ℝ) * G b.2) + (d * n : ℤ) := by
      rw [time_eq, hn, hF_int, hG_int]
      push_cast
      ring
    change Circle.turnExp
        ((1 - (a.1 : ℝ)) * F a.2 + (a.1 : ℝ) * G a.2) =
      Circle.turnExp ((1 - (b.1 : ℝ)) * F b.2 + (b.1 : ℝ) * G b.2)
    rw [affine_eq]
    exact Circle.turnExp_add_int _ (d * n)
  let descended : C(unitInterval × Circle, Circle) :=
    quotientMap_isQuotient.lift interpolation interpolation_factors
  have descended_comp : descended.comp quotientMap = interpolation := by
    exact Topology.IsQuotientMap.lift_comp _ _ _
  -- Identify both endpoint maps after precomposition with the surjective cover.
  have zero_endpoint :
      descended.comp ((ContinuousMap.const Circle (0 : unitInterval)).prodMk
        (ContinuousMap.id Circle)) =
        f := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Circle.turnExp_surjective z
    have at_zero := DFunLike.congr_fun descended_comp ((0 : unitInterval), x)
    change descended (0, Circle.turnExp x) = _ at at_zero
    change descended (0, Circle.turnExp x) = f (Circle.turnExp x)
    calc
      descended (0, Circle.turnExp x) = interpolation (0, x) := at_zero
      _ = Circle.turnExp (F x) := by
        change Circle.turnExp ((1 - (0 : ℝ)) * F x + (0 : ℝ) * G x) = _
        ring_nf
      _ = f (Circle.turnExp x) := congrFun hF_lifts x
  have one_endpoint :
      descended.comp ((ContinuousMap.const Circle (1 : unitInterval)).prodMk
        (ContinuousMap.id Circle)) =
        g := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Circle.turnExp_surjective z
    have at_one := DFunLike.congr_fun descended_comp ((1 : unitInterval), x)
    change descended (1, Circle.turnExp x) = _ at at_one
    change descended (1, Circle.turnExp x) = g (Circle.turnExp x)
    calc
      descended (1, Circle.turnExp x) = interpolation (1, x) := at_one
      _ = Circle.turnExp (G x) := by
        change Circle.turnExp ((1 - (1 : ℝ)) * F x + (1 : ℝ) * G x) = _
        ring_nf
      _ = g (Circle.turnExp x) := congrFun hG_lifts x
  -- Package the descended map with the two endpoint equations.
  refine ⟨{
    toContinuousMap := descended
    map_zero_left := fun x ↦ DFunLike.congr_fun zero_endpoint x
    map_one_left := fun x ↦ DFunLike.congr_fun one_endpoint x
  }⟩

end CircleMap
