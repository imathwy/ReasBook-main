import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_2_2

open scoped Topology Topology.Homotopy unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall via `lean_leansearch`: mathlib surfaced the general owner `HomotopyGroup` but
-- no pre-existing pair-relative connecting morphism in the cubical model. Chapter 9 already fixes
-- `pairHomotopyBoundaryMap` as the abstract boundary map and `relativeHomotopyGroupCubeEquiv` as
-- the concrete cube-model comparison, so this item formalizes the source description by adding
-- the explicit top-face restriction on cube representatives.

/-- Restricting a relative cube representative to the top face `I^(q + 1) × {1}` gives a
continuous map `I^(q + 1) → A`. -/
def relativeCubeTopFaceMap
    (q : ℕ) (A : Set X) (x : A) (f : relativeCubeMap (q + 1).succPNat A x) :
    C(I^(relativePathSpaceIndex ((q + 1).succPNat)), A) :=
  (pairRelativeEndpointMap A x).comp
    (relativeCubeRepresentativeToRelativePathToSetMap (q + 1).succPNat A x f)

/-- The top-face restriction is the endpoint map applied to the path-space representative from
Definition 9.2.3. -/
@[simp] theorem relativeCubeTopFaceMap_apply
    (q : ℕ) (A : Set X) (x : A) (f : relativeCubeMap (q + 1).succPNat A x)
    (a : I^(relativePathSpaceIndex ((q + 1).succPNat))) :
    relativeCubeTopFaceMap q A x f a =
      pairRelativeEndpointMap A x
        (relativeCubeRepresentativeToRelativePathToSetMap (q + 1).succPNat A x f a) := rfl

/-- The top-face restriction of a relative cube representative sends the boundary of `I^(q + 1)`
to the basepoint `x`. -/
theorem relativeCubeTopFaceMap_boundary
    (q : ℕ) (A : Set X) (x : A) (f : relativeCubeMap (q + 1).succPNat A x)
    (a : I^(relativePathSpaceIndex ((q + 1).succPNat)))
    (ha : a ∈ Cube.boundary (relativePathSpaceIndex ((q + 1).succPNat))) :
    relativeCubeTopFaceMap q A x f a = x := by
  rw [relativeCubeTopFaceMap_apply,
    relativeCubeRepresentativeToRelativePathToSetMap_property (q + 1).succPNat A x f a ha,
    pairRelativeEndpointMap_refl]

/-- Restricting a relative cube representative to the top face produces a generalized loop in
`A` based at `x`. -/
def relativeCubeTopFaceGenLoop
    (q : ℕ) (A : Set X) (x : A) (f : relativeCubeMap (q + 1).succPNat A x) :
    Ω^ (relativePathSpaceIndex ((q + 1).succPNat)) A x :=
  ⟨relativeCubeTopFaceMap q A x f, relativeCubeTopFaceMap_boundary q A x f⟩

/-- Homotopic relative cube representatives have homotopic top-face restrictions in `A`. -/
theorem relativeCubeTopFaceGenLoop_respects
    (q : ℕ) (A : Set X) (x : A) {f g : relativeCubeMap (q + 1).succPNat A x}
    (hfg : relativeCubeHomotopic (q + 1).succPNat A x f g) :
    GenLoop.Homotopic
      (relativeCubeTopFaceGenLoop q A x f)
      (relativeCubeTopFaceGenLoop q A x g) := sorry

/-- Passing to homotopy classes sends a relative cube class to the class of its top-face
restriction `I^(q + 1) × {1} ⟶ A`. -/
def relativeCubeBoundaryMap
    (q : ℕ) (A : Set X) (x : A) :
    relativeCubeHomotopyClass (q + 1).succPNat A x → π_ (q + 1) A x :=
  Quotient.map
    (relativeCubeTopFaceGenLoop q A x)
    (fun _ _ hfg ↦ relativeCubeTopFaceGenLoop_respects q A x hfg)

/-- Construction 9.2.4: after identifying `π_(q + 2)(X, A, x)` with the cube-model quotient from
Definition 9.2.3, the connecting homomorphism
`π_(q + 2)(X, A, x) → π_(q + 1)(A, x)` from Theorem 9.2.2 is the map obtained by restricting a
representative `I^(q + 2) → X` to the top face `I^(q + 1) × {1}`. -/
theorem pairHomotopyBoundaryMap_apply_eq_relativeCubeBoundaryMap
    (q : ℕ) (A : Set X) (x : A) (u : relativeHomotopyGroup (q + 1).succPNat A x) :
    pairHomotopyBoundaryMap A x q u =
      relativeCubeBoundaryMap q A x
        (relativeHomotopyGroupCubeEquiv (q + 1).succPNat A x u) := sorry

/-- On cube-model classes, Construction 9.2.4 rewrites the source-facing top-face restriction as
the canonical connecting morphism from Theorem 9.2.2. -/
theorem relativeCubeBoundaryMap_apply_eq_pairHomotopyBoundaryMap
    (q : ℕ) (A : Set X) (x : A) (u : relativeCubeHomotopyClass (q + 1).succPNat A x) :
    relativeCubeBoundaryMap q A x u =
      pairHomotopyBoundaryMap A x q
        ((relativeHomotopyGroupCubeEquiv (q + 1).succPNat A x).symm u) := by
  simpa only [Equiv.apply_symm_apply] using
    (pairHomotopyBoundaryMap_apply_eq_relativeCubeBoundaryMap q A x
      ((relativeHomotopyGroupCubeEquiv (q + 1).succPNat A x).symm u)).symm
