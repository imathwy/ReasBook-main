import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology Topology.Homotopy unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi` and `Cube.boundary` are the cubical
-- owners for ordinary homotopy groups, while local Chapter 9 precedent uses
-- `relativeHomotopyGroup` for the pair-relative owner from Definition 9.1.5. This item is
-- therefore formalized as the concrete triple-map quotient that represents that existing owner.

/-- The path-space model for `relativeHomotopyGroup n A x` uses the `(n - 1)`-cube. -/
abbrev relativePathSpaceIndex (n : ℕ+) :=
  Fin ((n : ℕ) - 1)

/-- The cube `I^n` in Definition 9.2.3 is modeled as `I^(relativePathSpaceIndex n ⊕ Unit)`, i.e.
`I^(n - 1) × I`. -/
abbrev relativeCubeIndex (n : ℕ+) :=
  relativePathSpaceIndex n ⊕ Unit

/-- The path-space representatives whose homotopy classes define `relativeHomotopyGroup n A x`. -/
abbrev relativePathSpaceLoop (n : ℕ+) (A : Set X) (x : A) :=
  Ω^ (relativePathSpaceIndex n) (PathToSet A x.1) (PathToSet.refl x)

/-- The subset `boundary(I^(n - 1)) × I` inside the cubical model `I^(relativeCubeIndex n)` for
`I^n`. -/
def relativeCubeVerticalBoundary (n : ℕ+) : Set (I^(relativeCubeIndex n)) :=
  { y | y ∘ Sum.inl ∈ Cube.boundary (relativePathSpaceIndex n) }

/-- The subset `I^(n - 1) × {0}` inside the cubical model `I^(relativeCubeIndex n)` for `I^n`.
-/
def relativeCubeBottomFace (n : ℕ+) : Set (I^(relativeCubeIndex n)) :=
  { y | y (Sum.inr ()) = 0 }

/-- The cubical subset `J^n = boundary(I^(n - 1)) × I ∪ I^(n - 1) × {0}` used in
Definition 9.2.3. -/
def relativeCubeJ (n : ℕ+) : Set (I^(relativeCubeIndex n)) :=
  relativeCubeVerticalBoundary n ∪ relativeCubeBottomFace n

/-- Membership in `relativeCubeJ n` is exactly the source formula
`boundary(I^(n - 1)) × I ∪ I^(n - 1) × {0}`. -/
@[simp] theorem mem_relativeCubeJ_iff (n : ℕ+) (y : I^(relativeCubeIndex n)) :
    y ∈ relativeCubeJ n ↔
      y ∘ Sum.inl ∈ Cube.boundary (relativePathSpaceIndex n) ∨ y (Sum.inr ()) = 0 := by
  rfl

/-- Membership in the full boundary of `I^n = I^(relativeCubeIndex n)` splits into the boundary
of the first `(n - 1)` coordinates or one of the two endpoints of the last coordinate. -/
@[simp] theorem mem_relativeCubeBoundary_iff (n : ℕ+) (y : I^(relativeCubeIndex n)) :
    y ∈ Cube.boundary (relativeCubeIndex n) ↔
      y ∘ Sum.inl ∈ Cube.boundary (relativePathSpaceIndex n) ∨
        y (Sum.inr ()) = 0 ∨ y (Sum.inr ()) = 1 := by
  change y ∈ Cube.boundary (relativePathSpaceIndex n ⊕ Unit) ↔
      y ∘ Sum.inl ∈ Cube.boundary (relativePathSpaceIndex n) ∨
        y (Sum.inr ()) = 0 ∨ y (Sum.inr ()) = 1
  rw [Cube.boundary_sum_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · rcases h with ⟨u, h | h⟩
      · cases u
        exact Or.inr <| Or.inl h
      · cases u
        exact Or.inr <| Or.inr h
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · rcases h with h | h
      · exact Or.inr ⟨(), Or.inl h⟩
      · exact Or.inr ⟨(), Or.inr h⟩

/-- A map `I^n → X` is a map of triples `(I^n, boundary I^n, J^n) → (X, A, *)` when it sends the
full cubical boundary into `A` and the distinguished subspace `J^n` to the basepoint `x`. -/
def IsRelativeCubeTripleMap (n : ℕ+) (A : Set X) (x : A)
    (f : C(I^(relativeCubeIndex n), X)) : Prop :=
  (∀ y ∈ Cube.boundary (relativeCubeIndex n), f y ∈ A) ∧
    ∀ y ∈ relativeCubeJ n, f y = x.1

/-- Unfolding `IsRelativeCubeTripleMap` recovers the two defining conditions for a map of triples
`(I^n, boundary I^n, J^n) → (X, A, *)`. -/
@[simp] theorem isRelativeCubeTripleMap_iff (n : ℕ+) (A : Set X) (x : A)
    (f : C(I^(relativeCubeIndex n), X)) :
    IsRelativeCubeTripleMap n A x f ↔
      (∀ y ∈ Cube.boundary (relativeCubeIndex n), f y ∈ A) ∧
        ∀ y ∈ relativeCubeJ n, f y = x.1 := by
  rfl

/-- The concrete maps of triples `(I^n, boundary I^n, J^n) → (X, A, *)`. -/
abbrev relativeCubeMap (n : ℕ+) (A : Set X) (x : A) :=
  { f : C(I^(relativeCubeIndex n), X) // IsRelativeCubeTripleMap n A x f }

/-- Homotopies through maps of triples `(I^n, boundary I^n, J^n) → (X, A, *)`. -/
def relativeCubeHomotopic (n : ℕ+) (A : Set X) (x : A)
    (f g : relativeCubeMap n A x) : Prop :=
  ContinuousMap.HomotopicWith f.1 g.1 (IsRelativeCubeTripleMap n A x)

/-- Unfolding `relativeCubeHomotopic` recovers homotopy through relative cube maps. -/
@[simp] theorem relativeCubeHomotopic_iff (n : ℕ+) (A : Set X) (x : A)
    (f g : relativeCubeMap n A x) :
    relativeCubeHomotopic n A x f g ↔
      ContinuousMap.HomotopicWith f.1 g.1 (IsRelativeCubeTripleMap n A x) := by
  rfl

/-- Two maps of triples are equivalent when they are homotopic through maps of the same triple
type. -/
instance relativeCubeMapSetoid (n : ℕ+) (A : Set X) (x : A) :
    Setoid (relativeCubeMap n A x) where
  r := relativeCubeHomotopic n A x
  iseqv :=
    ⟨fun f ↦ ContinuousMap.HomotopicWith.refl f.1 f.2,
      fun {_ _} hfg ↦ ContinuousMap.HomotopicWith.symm hfg,
      fun {_ _ _} hfg hgh ↦ ContinuousMap.HomotopicWith.trans hfg hgh⟩

/-- The quotient of maps of triples `(I^n, boundary I^n, J^n) → (X, A, *)` by homotopy through
maps of the same triple type. -/
abbrev relativeCubeHomotopyClass (n : ℕ+) (A : Set X) (x : A) :=
  Quotient (relativeCubeMapSetoid n A x)

/-- Unfolding `relativeCubeHomotopyClass` gives the quotient of `relativeCubeMap n A x` by
homotopy through triple maps. -/
theorem relativeCubeHomotopyClass_def (n : ℕ+) (A : Set X) (x : A) :
    relativeCubeHomotopyClass n A x = Quotient (relativeCubeMapSetoid n A x) := rfl

/-- A relative cube map sends the full cubical boundary of `I^n` into `A`. -/
theorem relativeCubeMap_mapsTo_boundary
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x)
    {y : I^(relativeCubeIndex n)} (hy : y ∈ Cube.boundary (relativeCubeIndex n)) :
    f.1 y ∈ A :=
  f.2.1 y hy

/-- A relative cube map sends the distinguished cubical subset `J^n` to the basepoint `x`. -/
theorem relativeCubeMap_mapsTo_J
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x)
    {y : I^(relativeCubeIndex n)} (hy : y ∈ relativeCubeJ n) :
    f.1 y = x.1 :=
  f.2.2 y hy

/-- Evaluating a representative of `relativeHomotopyGroup n A x` along the last cube coordinate
produces the underlying function `I^n → X`. -/
def relativeHomotopyRepresentativeToRelativeCubeFun
    (n : ℕ+) (A : Set X) (x : A) (p : relativePathSpaceLoop n A x) :
    (I^(relativeCubeIndex n)) → X :=
  fun y ↦ p (y ∘ Sum.inl) (y (Sum.inr ()))

/-- Evaluating a representative of `relativeHomotopyGroup n A x` along the last cube coordinate
produces a concrete cube map `I^n → X`. -/
theorem continuous_relativeHomotopyRepresentativeToRelativeCubeContinuousMap
    (n : ℕ+) (A : Set X) (x : A)
    (p : relativePathSpaceLoop n A x) :
    Continuous (relativeHomotopyRepresentativeToRelativeCubeFun n A x p) := by
  let pathPoint : (I^(relativeCubeIndex n)) → PathToSet A x.1 := fun y ↦ p (y ∘ Sum.inl)
  -- Restrict to the first `(n - 1)` coordinates to get a continuous family of `PathToSet` points.
  have hpathPoint : Continuous pathPoint := by
    exact p.1.continuous.comp (by fun_prop)
  have hpathComponent :
      Continuous fun y : I^(relativeCubeIndex n) =>
        (PathToSet.endpointAndPath A x (pathPoint y)).2 := by
    -- The path component is continuous because `PathToSet` has the induced topology.
    exact continuous_snd.comp (continuous_induced_dom.comp hpathPoint)
  -- Evaluate the continuous family of paths at the last cube coordinate.
  simpa [relativeHomotopyRepresentativeToRelativeCubeFun, pathPoint] using
    (continuous_eval.comp <|
      hpathComponent.prodMk (by
        fun_prop : Continuous fun y : I^(relativeCubeIndex n) => y (Sum.inr ())))

/-- Evaluating a representative of `relativeHomotopyGroup n A x` along the last cube coordinate
gives the source cube map `I^n → X`. -/
def relativeHomotopyRepresentativeToRelativeCubeContinuousMap
    (n : ℕ+) (A : Set X) (x : A)
    (p : relativePathSpaceLoop n A x) :
    C(I^(relativeCubeIndex n), X) where
  toFun := relativeHomotopyRepresentativeToRelativeCubeFun n A x p
  continuous_toFun :=
    continuous_relativeHomotopyRepresentativeToRelativeCubeContinuousMap n A x p

/-- Helper for Definition 9.2.3: points of `J^n` are sent to the basepoint by the evaluated cube
representative attached to a path-space loop. -/
theorem relativeHomotopyRepresentative_eq_basepoint_of_memJ
    (n : ℕ+) (A : Set X) (x : A) (p : relativePathSpaceLoop n A x)
    {y : I^(relativeCubeIndex n)} (hy : y ∈ relativeCubeJ n) :
    relativeHomotopyRepresentativeToRelativeCubeFun n A x p y = x.1 := by
  rcases (mem_relativeCubeJ_iff n y).mp hy with hyBoundary | hyBottom
  · -- On the vertical boundary, the path-space loop is the constant path `PathToSet.refl x`.
    have hp : p (y ∘ Sum.inl) = PathToSet.refl x := p.2 _ hyBoundary
    simpa [relativeHomotopyRepresentativeToRelativeCubeFun, PathToSet.refl] using
      congrArg (fun γ : PathToSet A x.1 => γ (y (Sum.inr ()))) hp
  · -- On the bottom face, every path is evaluated at its source `x`.
    simpa [relativeHomotopyRepresentativeToRelativeCubeFun, hyBottom] using
      (p (y ∘ Sum.inl)).path.source'

/-- The evaluated cube map associated to a representative of `relativeHomotopyGroup n A x`
satisfies the triple-map conditions from Definition 9.2.3. -/
theorem relativeHomotopyRepresentativeToRelativeCubeContinuousMap_property
    (n : ℕ+) (A : Set X) (x : A)
    (p : relativePathSpaceLoop n A x) :
    IsRelativeCubeTripleMap n A x
      (relativeHomotopyRepresentativeToRelativeCubeContinuousMap n A x p) := by
  constructor
  · intro y hy
    rcases (mem_relativeCubeBoundary_iff n y).mp hy with hyBoundary | hyBottom | hyTop
    · -- On `boundary(I^(n - 1)) × I`, the source loop is the constant path at `x`.
      have hp : p (y ∘ Sum.inl) = PathToSet.refl x := p.2 _ hyBoundary
      have hvalue :
          relativeHomotopyRepresentativeToRelativeCubeFun n A x p y = x.1 := by
        simpa [relativeHomotopyRepresentativeToRelativeCubeFun, PathToSet.refl] using
          congrArg (fun γ : PathToSet A x.1 => γ (y (Sum.inr ()))) hp
      change relativeHomotopyRepresentativeToRelativeCubeFun n A x p y ∈ A
      rw [hvalue]
      exact x.2
    · -- On `I^(n - 1) × {0}`, we evaluate every path at its source.
      have hvalue :
          relativeHomotopyRepresentativeToRelativeCubeFun n A x p y = x.1 := by
        simpa [relativeHomotopyRepresentativeToRelativeCubeFun, hyBottom] using
          (p (y ∘ Sum.inl)).path.source'
      change relativeHomotopyRepresentativeToRelativeCubeFun n A x p y ∈ A
      rw [hvalue]
      exact x.2
    · -- On the top face, the path endpoint lies in `A`.
      change relativeHomotopyRepresentativeToRelativeCubeFun n A x p y ∈ A
      simpa [relativeHomotopyRepresentativeToRelativeCubeFun, hyTop] using
        PathToSet.endpoint_mem (p (y ∘ Sum.inl))
  · intro y hy
    -- The distinguished subspace `J^n` is sent to the basepoint.
    exact relativeHomotopyRepresentative_eq_basepoint_of_memJ n A x p hy

/-- A representative of `relativeHomotopyGroup n A x` determines a map of triples
`(I^n, boundary I^n, J^n) → (X, A, *)`. -/
def relativeHomotopyRepresentativeToRelativeCubeMap
    (n : ℕ+) (A : Set X) (x : A)
    (p : relativePathSpaceLoop n A x) :
    relativeCubeMap n A x :=
  ⟨relativeHomotopyRepresentativeToRelativeCubeContinuousMap n A x p,
    relativeHomotopyRepresentativeToRelativeCubeContinuousMap_property n A x p⟩

/-- Homotopic representatives in the path-space model induce homotopic cube maps of triples. -/
theorem relativeHomotopyRepresentativeToRelativeCubeMap_respects
    (n : ℕ+) (A : Set X) (x : A)
    {p q : relativePathSpaceLoop n A x}
    (hpq : GenLoop.Homotopic p q) :
    relativeCubeHomotopic n A x
      (relativeHomotopyRepresentativeToRelativeCubeMap n A x p)
      (relativeHomotopyRepresentativeToRelativeCubeMap n A x q) := by
  rcases hpq with ⟨H⟩
  refine ⟨{
    toHomotopy := {
      toFun := fun z ↦ H (z.1, z.2 ∘ Sum.inl) (z.2 (Sum.inr ()))
      continuous_toFun := by
        let pathPoint : (I × (I^(relativeCubeIndex n))) → PathToSet A x.1 :=
          fun z ↦ H (z.1, z.2 ∘ Sum.inl)
        -- Evaluate the homotopy slice in `PathToSet` at the last cube coordinate.
        have hpathPoint : Continuous pathPoint := by
          exact H.continuous.comp (by fun_prop)
        have hpathComponent :
            Continuous fun z : I × (I^(relativeCubeIndex n)) =>
              (PathToSet.endpointAndPath A x (pathPoint z)).2 := by
          exact continuous_snd.comp (continuous_induced_dom.comp hpathPoint)
        simpa [pathPoint] using
          (continuous_eval.comp <|
            hpathComponent.prodMk (by
              fun_prop :
                Continuous fun z : I × (I^(relativeCubeIndex n)) => z.2 (Sum.inr ())))
      map_zero_left := by
        intro y
        simpa using congrArg (fun γ : PathToSet A x.1 => γ (y (Sum.inr ())))
          (H.apply_zero (y ∘ Sum.inl))
      map_one_left := by
        intro y
        simpa using congrArg (fun γ : PathToSet A x.1 => γ (y (Sum.inr ())))
          (H.apply_one (y ∘ Sum.inl))
    }
    prop' := fun t => by
      constructor
      · intro y hy
        rcases (mem_relativeCubeBoundary_iff n y).mp hy with hyBoundary | hyBottom | hyTop
        · -- Boundary points in the first coordinates stay fixed at the constant path.
          have hconst : H (t, y ∘ Sum.inl) = PathToSet.refl x := by
            have hfixed : H (t, y ∘ Sum.inl) = p (y ∘ Sum.inl) := by
              simpa using H.prop t (y ∘ Sum.inl) hyBoundary
            exact hfixed.trans (p.2 _ hyBoundary)
          have hvalue :
              H (t, y ∘ Sum.inl) (y (Sum.inr ())) = x.1 := by
            simpa [PathToSet.refl] using
              congrArg (fun γ : PathToSet A x.1 => γ (y (Sum.inr ()))) hconst
          change H (t, y ∘ Sum.inl) (y (Sum.inr ())) ∈ A
          rw [hvalue]
          exact x.2
        · -- The bottom face still evaluates paths at the source.
          have hvalue : H (t, y ∘ Sum.inl) (y (Sum.inr ())) = x.1 := by
            simpa [hyBottom] using (H (t, y ∘ Sum.inl)).path.source'
          change H (t, y ∘ Sum.inl) (y (Sum.inr ())) ∈ A
          rw [hvalue]
          exact x.2
        · -- The top face still evaluates at an endpoint in `A`.
          change H (t, y ∘ Sum.inl) (y (Sum.inr ())) ∈ A
          simpa [hyTop] using PathToSet.endpoint_mem (H (t, y ∘ Sum.inl))
      · intro y hy
        rcases (mem_relativeCubeJ_iff n y).mp hy with hyBoundary | hyBottom
        · -- The `boundary(I^(n - 1)) × I` part is fixed to the basepoint.
          have hconst : H (t, y ∘ Sum.inl) = PathToSet.refl x := by
            have hfixed : H (t, y ∘ Sum.inl) = p (y ∘ Sum.inl) := by
              simpa using H.prop t (y ∘ Sum.inl) hyBoundary
            exact hfixed.trans (p.2 _ hyBoundary)
          simpa [PathToSet.refl] using
            congrArg (fun γ : PathToSet A x.1 => γ (y (Sum.inr ()))) hconst
        · -- The `I^(n - 1) × {0}` part evaluates every path at the source.
          simpa [hyBottom] using (H (t, y ∘ Sum.inl)).path.source'
  }⟩

/-- Passing to quotients sends a relative homotopy-group class to its cube-model class. -/
def relativeHomotopyGroupToRelativeCubeHomotopyClass
    (n : ℕ+) (A : Set X) (x : A) :
    relativeHomotopyGroup n A x → relativeCubeHomotopyClass n A x :=
  Quotient.map
    (relativeHomotopyRepresentativeToRelativeCubeMap n A x)
    (fun _ _ hpq ↦ relativeHomotopyRepresentativeToRelativeCubeMap_respects n A x hpq)

/-- Restricting a cube map along the last coordinate gives a path in `X` for each
`(n - 1)`-cube parameter. -/
def relativeCubeCurriedFun
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x)
    (a : I^(relativePathSpaceIndex n)) : I → X :=
  fun t ↦ f.1 (Sum.elim a (fun _ ↦ t))

/-- Restricting a cube map along the last coordinate gives a path in `X` for each
`(n - 1)`-cube parameter. -/
theorem continuous_relativeCubeCurriedContinuousMap
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x)
    (a : I^(relativePathSpaceIndex n)) :
    Continuous (relativeCubeCurriedFun n A x f a) := by
  -- Fix the first `(n - 1)` coordinates and restrict the cube map to the last coordinate.
  have hsum : Continuous fun t : I => (fun i : relativeCubeIndex n => Sum.elim a (fun _ : Unit => t) i) := by
    refine continuous_pi ?_
    intro i
    cases i with
    | inl i => simpa using continuous_const
    | inr u =>
        cases u
        simpa using continuous_id
  simpa [relativeCubeCurriedFun] using f.1.continuous.comp hsum

/-- The top face of a relative cube map lands in `A`. -/
theorem relativeCubeTopFace_mem
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x)
    (a : I^(relativePathSpaceIndex n)) :
    f.1 (Sum.elim a (fun _ ↦ (1 : I))) ∈ A := by
  have hy : Sum.elim a (fun _ ↦ (1 : I)) ∈ Cube.boundary (relativeCubeIndex n) := by
    rw [mem_relativeCubeBoundary_iff]
    exact Or.inr <| Or.inr rfl
  -- The top face is part of the full cube boundary.
  exact relativeCubeMap_mapsTo_boundary n A x f hy

/-- Currying a relative cube map along the last coordinate yields a continuous path in `X`. -/
def relativeCubeCurriedContinuousMap
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x)
    (a : I^(relativePathSpaceIndex n)) :
    C(I, X) where
  toFun := relativeCubeCurriedFun n A x f a
  continuous_toFun := continuous_relativeCubeCurriedContinuousMap n A x f a

/-- The endpoint at `t = 1` of a relative cube map lies in `A`. -/
def relativeCubeTopFacePoint
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x)
    (a : I^(relativePathSpaceIndex n)) : A :=
  ⟨f.1 (Sum.elim a (fun _ ↦ (1 : I))), relativeCubeTopFace_mem n A x f a⟩

/-- The curried path associated to a relative cube map starts at the basepoint `x`. -/
theorem relativeCubeCurriedContinuousMap_source
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x)
    (a : I^(relativePathSpaceIndex n)) :
    relativeCubeCurriedContinuousMap n A x f a 0 = x.1 := by
  have hy : Sum.elim a (fun _ ↦ (0 : I)) ∈ relativeCubeJ n := by
    rw [mem_relativeCubeJ_iff]
    exact Or.inr rfl
  -- The bottom face of the cube is sent to the basepoint.
  simpa [relativeCubeCurriedContinuousMap, relativeCubeCurriedFun] using
    relativeCubeMap_mapsTo_J n A x f hy

/-- The curried path associated to a relative cube map ends at the corresponding top-face point. -/
theorem relativeCubeCurriedContinuousMap_target
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x)
    (a : I^(relativePathSpaceIndex n)) :
    relativeCubeCurriedContinuousMap n A x f a 1 =
      (relativeCubeTopFacePoint n A x f a).1 := by
  -- The target is the top-face value by construction.
  rfl

/-- For a fixed `(n - 1)`-cube parameter, currying a relative cube map along the last coordinate
produces the corresponding point of `PathToSet A x.1`. -/
def relativeCubePathToSetPoint
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x)
    (a : I^(relativePathSpaceIndex n)) : PathToSet A x.1 :=
  { endpoint := relativeCubeTopFacePoint n A x f a
    path := Path.mk
      (relativeCubeCurriedContinuousMap n A x f a)
      (relativeCubeCurriedContinuousMap_source n A x f a)
      (relativeCubeCurriedContinuousMap_target n A x f a) }

/-- Currying a relative cube map along the last coordinate produces a path-space representative. -/
theorem continuous_relativeCubeRepresentativeToRelativePathToSetMap
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x) :
    Continuous (fun a : I^(relativePathSpaceIndex n) ↦ relativeCubePathToSetPoint n A x f a) :=
  by
    have hpath :
        Continuous fun a : I^(relativePathSpaceIndex n) =>
          relativeCubeCurriedContinuousMap n A x f a := by
      -- Curry the cube map along the last coordinate to obtain a continuous family of paths.
      have hsum : Continuous fun z : (I^(relativePathSpaceIndex n)) × I =>
          (fun i : relativeCubeIndex n => Sum.elim z.1 (fun _ : Unit => z.2) i) := by
        refine continuous_pi ?_
        intro i
        cases i with
        | inl i =>
            simpa using (continuous_apply i).comp continuous_fst
        | inr u =>
            cases u
            simpa using continuous_snd
      refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
      simpa [relativeCubeCurriedContinuousMap, relativeCubeCurriedFun, Function.uncurry] using
        f.1.continuous.comp hsum
    have hendpoint :
        Continuous fun a : I^(relativePathSpaceIndex n) =>
          relativeCubeTopFacePoint n A x f a := by
      -- The endpoint coordinate is the `t = 1` evaluation of the curried path.
      refine Continuous.subtype_mk ((continuous_eval_const (1 : I)).comp hpath) ?_
    -- Work through the induced topology on `PathToSet A x.1`.
    rw [continuous_induced_rng]
    change Continuous fun a : I^(relativePathSpaceIndex n) =>
      (relativeCubeTopFacePoint n A x f a, relativeCubeCurriedContinuousMap n A x f a)
    exact hendpoint.prodMk hpath

/-- Currying a relative cube map along the last coordinate gives a continuous map into
`PathToSet A x.1`. -/
def relativeCubeRepresentativeToRelativePathToSetMap
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x) :
    C(I^(relativePathSpaceIndex n), PathToSet A x.1) where
  toFun := relativeCubePathToSetPoint n A x f
  continuous_toFun := continuous_relativeCubeRepresentativeToRelativePathToSetMap n A x f

/-- Helper for Definition 9.2.3: when the parameter lies on `boundary(I^(n - 1))`, the curried
path of a relative cube map is the constant path `PathToSet.refl x`. -/
theorem relativeCubePathToSetPoint_eq_refl_of_memBoundary
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x)
    {a : I^(relativePathSpaceIndex n)} (ha : a ∈ Cube.boundary (relativePathSpaceIndex n)) :
    relativeCubePathToSetPoint n A x f a = PathToSet.refl x := by
  apply (PathToSet.endpointAndPath_injective (A := A) (x := x))
  -- Compare the endpoint and the underlying path separately.
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    have hy : Sum.elim a (fun _ ↦ (1 : I)) ∈ relativeCubeJ n := by
      rw [mem_relativeCubeJ_iff]
      exact Or.inl ha
    simpa [relativeCubePathToSetPoint, PathToSet.endpointAndPath, relativeCubeTopFacePoint] using
      relativeCubeMap_mapsTo_J n A x f hy
  · apply ContinuousMap.ext
    intro t
    have hy : Sum.elim a (fun _ ↦ t) ∈ relativeCubeJ n := by
      rw [mem_relativeCubeJ_iff]
      exact Or.inl ha
    -- Every point on `boundary(I^(n - 1)) × I` is sent to the basepoint.
    simpa [relativeCubePathToSetPoint, PathToSet.endpointAndPath, relativeCubeCurriedContinuousMap,
      relativeCubeCurriedFun] using relativeCubeMap_mapsTo_J n A x f hy

/-- The path-space map associated to a relative cube map is constant on the boundary of
`I^(n - 1)`. -/
theorem relativeCubeRepresentativeToRelativePathToSetMap_property
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x)
    (a : I^(relativePathSpaceIndex n)) (ha : a ∈ Cube.boundary (relativePathSpaceIndex n)) :
    relativeCubeRepresentativeToRelativePathToSetMap n A x f a = PathToSet.refl x := by
  -- Boundary parameters give the constant path by the defining `J^n` condition.
  simpa [relativeCubeRepresentativeToRelativePathToSetMap] using
    relativeCubePathToSetPoint_eq_refl_of_memBoundary n A x f ha

/-- A relative cube map determines a generalized loop in `PathToSet A x.1` based at
`PathToSet.refl x`. -/
def relativeCubeRepresentativeToRelativePathLoop
    (n : ℕ+) (A : Set X) (x : A) (f : relativeCubeMap n A x) :
    relativePathSpaceLoop n A x :=
  ⟨relativeCubeRepresentativeToRelativePathToSetMap n A x f,
    relativeCubeRepresentativeToRelativePathToSetMap_property n A x f⟩

/-- Homotopic relative cube maps induce homotopic generalized loops in `PathToSet A x.1`. -/
theorem relativeCubeRepresentativeToRelativePathLoop_respects
    (n : ℕ+) (A : Set X) (x : A) {f g : relativeCubeMap n A x}
    (hfg : relativeCubeHomotopic n A x f g) :
    GenLoop.Homotopic
      (relativeCubeRepresentativeToRelativePathLoop n A x f)
      (relativeCubeRepresentativeToRelativePathLoop n A x g) := by
  rcases hfg with ⟨H⟩
  let slice : I → relativeCubeMap n A x := fun t ↦ ⟨H.toHomotopy.curry t, H.prop t⟩
  refine ⟨{
    toHomotopy := {
      toFun := fun z ↦ relativeCubePathToSetPoint n A x (slice z.1) z.2
      continuous_toFun := by
        have hpath :
            Continuous fun z : I × (I^(relativePathSpaceIndex n)) =>
              relativeCubeCurriedContinuousMap n A x (slice z.1) z.2 := by
          -- Uncurry the homotopy of cube maps to a continuous family of paths.
          have hsum :
              Continuous fun w : (I × (I^(relativePathSpaceIndex n))) × I =>
                (w.1.1, (fun i : relativeCubeIndex n => Sum.elim w.1.2 (fun _ : Unit => w.2) i)) := by
            refine continuous_fst.fst'.prodMk ?_
            refine continuous_pi ?_
            intro i
            cases i with
            | inl i =>
                simpa using (continuous_apply i).comp (continuous_snd.comp continuous_fst)
            | inr u =>
                cases u
                simpa using continuous_snd
          refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
          simpa [slice, relativeCubeCurriedContinuousMap, relativeCubeCurriedFun, Function.uncurry]
            using H.continuous.comp hsum
        have hendpoint :
            Continuous fun z : I × (I^(relativePathSpaceIndex n)) =>
              relativeCubeTopFacePoint n A x (slice z.1) z.2 := by
          -- The endpoint coordinate is again the `t = 1` evaluation of the curried path.
          refine Continuous.subtype_mk ((continuous_eval_const (1 : I)).comp hpath) ?_
        rw [continuous_induced_rng]
        change Continuous fun z : I × (I^(relativePathSpaceIndex n)) =>
          (relativeCubeTopFacePoint n A x (slice z.1) z.2,
            relativeCubeCurriedContinuousMap n A x (slice z.1) z.2)
        exact hendpoint.prodMk hpath
      map_zero_left := by
        intro a
        have hslice : slice 0 = f := by
          apply Subtype.ext
          ext y
          simpa [slice] using H.apply_zero y
        change relativeCubePathToSetPoint n A x (slice 0) a =
          relativeCubePathToSetPoint n A x f a
        simpa [hslice]
      map_one_left := by
        intro a
        have hslice : slice 1 = g := by
          apply Subtype.ext
          ext y
          simpa [slice] using H.apply_one y
        change relativeCubePathToSetPoint n A x (slice 1) a =
          relativeCubePathToSetPoint n A x g a
        simpa [hslice]
    }
    prop' := fun t a ha => by
      -- Each time slice stays constant on the boundary of `I^(n - 1)`.
      have hs :
          relativeCubePathToSetPoint n A x (slice t) a = PathToSet.refl x := by
        simpa [slice] using
          relativeCubePathToSetPoint_eq_refl_of_memBoundary n A x (slice t) ha
      have hf : (relativeCubeRepresentativeToRelativePathLoop n A x f) a = PathToSet.refl x := by
        exact relativeCubeRepresentativeToRelativePathToSetMap_property n A x f a ha
      exact hs.trans hf.symm
  }⟩

/-- Passing to quotients sends a cube-model class back to the Chapter 9 relative homotopy-group
owner. -/
def relativeCubeHomotopyClassToRelativeHomotopyGroup
    (n : ℕ+) (A : Set X) (x : A) :
    relativeCubeHomotopyClass n A x → relativeHomotopyGroup n A x :=
  Quotient.map
    (relativeCubeRepresentativeToRelativePathLoop n A x)
    (fun _ _ hfg ↦ relativeCubeRepresentativeToRelativePathLoop_respects n A x hfg)

/-- Helper for Definition 9.2.3: evaluating a path-space representative to a cube and currying it
back recovers the original representative. -/
theorem relativePathLoop_roundTrip
    (n : ℕ+) (A : Set X) (x : A) (p : relativePathSpaceLoop n A x) :
    relativeCubeRepresentativeToRelativePathLoop n A x
      (relativeHomotopyRepresentativeToRelativeCubeMap n A x p) = p := by
  apply Subtype.ext
  ext a
  -- Compare the recovered `PathToSet` point with the original endpoint and path.
  apply (PathToSet.endpointAndPath_injective (A := A) (x := x))
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    -- The recovered endpoint is the original endpoint at `t = 1`.
    change (p a).path 1 = (p a).endpoint.1
    exact (p a).path.target'
  · apply ContinuousMap.ext
    intro t
    -- The recovered path evaluates the original path at the same parameter `t`.
    change (p a).path t = (p a).path t
    rfl

/-- The forward cube-model quotient map and the backward path-space quotient map are inverse on
`relativeHomotopyGroup n A x`. -/
theorem relativeHomotopyGroupCubeEquiv_left_inv
    (n : ℕ+) (A : Set X) (x : A) :
    Function.LeftInverse
      (relativeCubeHomotopyClassToRelativeHomotopyGroup n A x)
      (relativeHomotopyGroupToRelativeCubeHomotopyClass n A x) := by
  intro u
  refine Quotient.inductionOn u ?_
  intro p
  change Quotient.mk _ (relativeCubeRepresentativeToRelativePathLoop n A x
    (relativeHomotopyRepresentativeToRelativeCubeMap n A x p)) = Quotient.mk _ p
  -- The representative-level round-trip is already exact.
  simpa [relativePathLoop_roundTrip n A x p]

/-- The backward path-space quotient map and the forward cube-model quotient map are inverse on
`relativeCubeHomotopyClass n A x`. -/
theorem relativeHomotopyGroupCubeEquiv_right_inv
    (n : ℕ+) (A : Set X) (x : A) :
    Function.RightInverse
      (relativeCubeHomotopyClassToRelativeHomotopyGroup n A x)
      (relativeHomotopyGroupToRelativeCubeHomotopyClass n A x) := by
  intro u
  refine Quotient.inductionOn u ?_
  intro f
  have hround :
      relativeHomotopyRepresentativeToRelativeCubeMap n A x
        (relativeCubeRepresentativeToRelativePathLoop n A x f) = f := by
    apply Subtype.ext
    ext y
    have hsplit :
        Sum.elim (y ∘ Sum.inl) (fun _ ↦ y (Sum.inr ())) = y := by
      ext i
      cases i <;> rfl
    -- The cube representative is recovered by reassembling the split coordinates.
    change f.1 (Sum.elim (y ∘ Sum.inl) (fun _ ↦ y (Sum.inr ()))) = f.1 y
    rw [hsplit]
  change Quotient.mk _ (relativeHomotopyRepresentativeToRelativeCubeMap n A x
    (relativeCubeRepresentativeToRelativePathLoop n A x f)) = Quotient.mk _ f
  simpa [hround]

/-- Definition 9.2.3: for positive degree `n`, the relative homotopy group `π_n(X, A, *)` from
Definition 9.1.5 is represented by the homotopy classes of maps of triples
`(I^n, boundary I^n, J^n) → (X, A, *)`, where
`J^n = boundary(I^(n - 1)) × I ∪ I^(n - 1) × {0}`. This is formalized by the explicit
equivalence between the Chapter 9 owner `relativeHomotopyGroup n A x` and the concrete cube-model
quotient `relativeCubeHomotopyClass n A x`. -/
def relativeHomotopyGroupCubeEquiv
    (n : ℕ+) (A : Set X) (x : A) :
    relativeHomotopyGroup n A x ≃ relativeCubeHomotopyClass n A x where
  toFun := relativeHomotopyGroupToRelativeCubeHomotopyClass n A x
  invFun := relativeCubeHomotopyClassToRelativeHomotopyGroup n A x
  left_inv := relativeHomotopyGroupCubeEquiv_left_inv n A x
  right_inv := relativeHomotopyGroupCubeEquiv_right_inv n A x

/-- Applying `relativeHomotopyGroupCubeEquiv` is the forward quotient map from the path-space
model to the cube-model quotient. -/
@[simp] theorem relativeHomotopyGroupCubeEquiv_apply
    (n : ℕ+) (A : Set X) (x : A) (u : relativeHomotopyGroup n A x) :
    relativeHomotopyGroupCubeEquiv n A x u =
      relativeHomotopyGroupToRelativeCubeHomotopyClass n A x u := rfl

/-- Applying `(relativeHomotopyGroupCubeEquiv n A x).symm` is the backward quotient map from the
cube-model quotient to the path-space model. -/
@[simp] theorem relativeHomotopyGroupCubeEquiv_symm_apply
    (n : ℕ+) (A : Set X) (x : A) (u : relativeCubeHomotopyClass n A x) :
    (relativeHomotopyGroupCubeEquiv n A x).symm u =
      relativeCubeHomotopyClassToRelativeHomotopyGroup n A x u := rfl
