import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_5

open scoped Topology Topology.Homotopy

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The `n`-fold iterated loop space of the relative path-space model `PathToSet A x.1`
appearing in Observation 9.1.7. -/
abbrev relativePathSpaceIteratedLoopSpace (n : ℕ) (A : Set X) (x : A) :=
  Ω^ (Fin n) (PathToSet A x.1) (PathToSet.refl x)

private theorem genLoop_homotopic_iff_joined
    {N : Type*} {x : X} {p q : Ω^ N X x} :
    GenLoop.Homotopic p q ↔ Joined p q := by
  constructor
  · rintro ⟨H⟩
    let curriedHomotopy := H.toHomotopy.curry
    refine ⟨Path.mk
      ⟨fun t ↦
          (⟨curriedHomotopy t, fun y hy ↦ (H.prop t y hy).trans (p.property y hy)⟩ :
            Ω^ N X x),
        Continuous.subtype_mk curriedHomotopy.continuous ?_⟩
      ?_ ?_⟩
    · intro t y hy
      exact (H.prop t y hy).trans (p.property y hy)
    · ext y
      exact H.apply_zero y
    · ext y
      exact H.apply_one y
  · rintro ⟨γ⟩
    refine ⟨⟨⟨
      (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ γ.toContinuousMap).uncurry,
      ?_, ?_⟩, ?_⟩⟩
    · intro y
      change γ 0 y = p y
      exact congrArg (fun r : Ω^ N X x ↦ r y) γ.source
    · intro y
      change γ 1 y = q y
      exact congrArg (fun r : Ω^ N X x ↦ r y) γ.target
    · intro t y hy
      exact ((γ t).property y hy).trans (p.property y hy).symm

private abbrev homotopyGroupEquivZerothHomotopyGenLoop
    (N : Type*) (x : X) :
    HomotopyGroup N X x ≃ ZerothHomotopy (Ω^ N X x) :=
  Quotient.congr (Equiv.refl _) fun _ _ ↦ genLoop_homotopic_iff_joined

/-- Observation 9.1.7: writing the source degree as `n + 1`, Definition 9.1.5 identifies
`π_(n + 1)(X, A, x)` with `π_ n P(X; *, A)`, and Observation 9.1.3 rewrites the latter as
`π_0` of the `n`-fold iterated loop space of `P(X; *, A)`. -/
def relativeHomotopyGroupSuccEquivPi0IteratedPathSpace
    (n : ℕ) (A : Set X) (x : A) :
    relativeHomotopyGroup n.succPNat A x ≃
      π_ 0 (relativePathSpaceIteratedLoopSpace n A x) GenLoop.const :=
  let pathBasepoint : PathToSet A x.1 := PathToSet.refl x
  (Equiv.cast (relativeHomotopyGroup_succ n A x)).trans
    ((homotopyGroupEquivZerothHomotopyGenLoop (Fin n) pathBasepoint).trans
      ((HomotopyGroup.pi0EquivZerothHomotopy :
          π_ 0 (relativePathSpaceIteratedLoopSpace n A x) GenLoop.const ≃
            ZerothHomotopy (relativePathSpaceIteratedLoopSpace n A x)).symm))

/-- Observation 9.1.7: the Chapter 9 owner `relativeHomotopyGroup (n + 1) A x` is the zeroth
homotopy set of the `n`-fold iterated loop space of the relative path-space model `P(X; *, A)`. -/
def relativeHomotopyGroupSuccEquivZerothHomotopyIteratedPathSpace
    (n : ℕ) (A : Set X) (x : A) :
    relativeHomotopyGroup n.succPNat A x ≃
      ZerothHomotopy (relativePathSpaceIteratedLoopSpace n A x) :=
  let pathBasepoint : PathToSet A x.1 := PathToSet.refl x
  (Equiv.cast (relativeHomotopyGroup_succ n A x)).trans
    (homotopyGroupEquivZerothHomotopyGenLoop (Fin n) pathBasepoint)
