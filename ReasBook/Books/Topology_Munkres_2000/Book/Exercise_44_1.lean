module

public import Topology_Munkres_2000.Book.Theorem_44_1
public import Mathlib.Topology.Homeomorph.Lemmas

public section

/-- Helper for Exercise 44.1: products of continuous images of `unitInterval` are again
continuous images of `unitInterval`. -/
private lemma existsContinuousSurjectiveProd
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (hX : ∃ f : C(unitInterval, X), Function.Surjective f)
    (hY : ∃ g : C(unitInterval, Y), Function.Surjective g) :
    ∃ h : C(unitInterval, X × Y), Function.Surjective h := by
  -- First fill the square, and then apply the two given maps coordinatewise.
  obtain ⟨squareMap, hSquareMap⟩ := existsContinuousSurjectiveUnitSquare
  obtain ⟨f, hf⟩ := hX
  obtain ⟨g, hg⟩ := hY
  refine ⟨(ContinuousMap.prodMap f g).comp squareMap, ?_⟩
  -- Both the coordinatewise product and the square map are surjective.
  exact (hf.prodMap hg).comp hSquareMap

/-- Helper for Exercise 44.1: adjoining one coordinate identifies
`(Fin n → X) × X` homeomorphically with `Fin (n + 1) → X`. -/
private def finSuccArrowHomeomorph (X : Type*) [TopologicalSpace X] (n : ℕ) :
    ((Fin n → X) × X) ≃ₜ (Fin (n + 1) → X) :=
  (Homeomorph.prodCongr (Homeomorph.refl (Fin n → X))
    (Homeomorph.funUnique (Fin 1) X).symm).trans
      (Fin.appendHomeomorph n 1)

/-- Helper for Exercise 44.1: the empty finite power of any topological space is a
continuous image of `unitInterval`. -/
private lemma existsContinuousSurjectiveFinZero (X : Type*) [TopologicalSpace X] :
    ∃ f : C(unitInterval, Fin 0 → X), Function.Surjective f := by
  -- The unique map into the empty product is continuous and surjective.
  refine ⟨ContinuousMap.const unitInterval (fun i ↦ Fin.elim0 i), ?_⟩
  exact Function.surjective_to_subsingleton _

/-- Helper for Exercise 44.1: adjoining one continuously parametrized coordinate preserves
the existence of a continuous surjection from `unitInterval`. -/
private lemma existsContinuousSurjectiveFinSucc
    {X : Type*} [TopologicalSpace X] (n : ℕ)
    (hCube : ∃ f : C(unitInterval, Fin n → X), Function.Surjective f)
    (hCoordinate : ∃ g : C(unitInterval, X), Function.Surjective g) :
    ∃ h : C(unitInterval, Fin (n + 1) → X), Function.Surjective h := by
  -- Form the product parametrization supplied by the square-filling curve.
  obtain ⟨productMap, hProductMap⟩ :=
    existsContinuousSurjectiveProd hCube hCoordinate
  -- Transport the product map across the canonical successor-cube homeomorphism.
  refine ⟨(finSuccArrowHomeomorph X n :
    C((Fin n → X) × X, Fin (n + 1) → X)).comp productMap, ?_⟩
  exact (finSuccArrowHomeomorph X n).surjective.comp hProductMap

/-- Exercise 44.1: For every `n`, there is a continuous surjection from the closed unit
interval onto its `n`-fold product. -/
theorem existsContinuousSurjectiveUnitCube (n : ℕ) :
    ∃ g : C(unitInterval, Fin n → unitInterval), Function.Surjective g := by
  -- Induct on the number of coordinates, adding one coordinate via the square map.
  induction n with
  | zero =>
      exact existsContinuousSurjectiveFinZero unitInterval
  | succ n ih =>
      refine existsContinuousSurjectiveFinSucc n ih ?_
      -- The identity supplies the required one-coordinate parametrization.
      refine ⟨ContinuousMap.id unitInterval, ?_⟩
      exact Function.surjective_id

/-- Every finite-dimensional unit cube is a Peano space. -/
instance instPeanoSpaceUnitCube (n : ℕ) : PeanoSpace (Fin n → unitInterval) where
  toT2Space := inferInstance
  exists_surjective := existsContinuousSurjectiveUnitCube n
