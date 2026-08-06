import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_5_2

universe u

variable {X : Type u} [TopologicalSpace X]
  [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]

-- Semantic recall via repository reuse: `Definition_9_5_2` already owns the Chapter 9
-- basepoint-change equivalence on path components of the sphere-evaluation fibers, together with
-- its computation rule.

/- Lemma 9.5.3: a path class `α : Path.Homotopic.Quotient x x'` induces the corresponding
equivalence on path components of the sphere-evaluation fibers over `x` and `x'`. -/
#check (sphereBasepointFiberZerothEquivOfPathClass :
  ∀ (n : ℕ) {x x' : X}, Path.Homotopic.Quotient x x' →
    ZerothHomotopy (sphereBasepointFiber n x) ≃ ZerothHomotopy (sphereBasepointFiber n x'))

/- Applying `sphereBasepointFiberZerothEquivOfPathClass n α` is exactly the transported map
`sphereBasepointFiberZerothMap n α` on path components. -/
#check (sphereBasepointFiberZerothEquivOfPathClass_apply :
  ∀ (n : ℕ) {x x' : X} (α : Path.Homotopic.Quotient x x')
    (a : ZerothHomotopy (sphereBasepointFiber n x)),
      sphereBasepointFiberZerothEquivOfPathClass n α a = sphereBasepointFiberZerothMap n α a)
