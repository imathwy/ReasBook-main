import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_5_6

open scoped Topology Topology.Homotopy

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]
variable {A : Set X} {n : ℕ+}

-- Semantic recall via `lean_leansearch`: no direct mathlib owner surfaced for relative
-- basepoint-independence of `π_n(X, A)`. Chapter 9 already provides
-- `relativeHomotopyGroupEquivOfPathClass`, relative to an explicit disk-boundary model
-- comparison, so this corollary packages the "same path component of `A`" hypothesis as
-- `Joined a a'` in the subtype `A`.

/-- Corollary 9.5.9: if `a` and `a'` are joined in the subtype `A`, then the relative homotopy
groups `π_n(X, A, a)` and `π_n(X, A, a')` are equivalent. This is the `Joined`-form of the
Chapter 9 basepoint-change equivalence `relativeHomotopyGroupEquivOfPathClass`. -/
noncomputable def relativeHomotopyGroupEquivOfJoined
    (e :
      ∀ a : A, relativeHomotopyGroup n A a ≃ basedDiskBoundaryPairMapHomotopyClass n A a)
    {a a' : A} (h : Joined a a') :
    relativeHomotopyGroup n A a ≃ relativeHomotopyGroup n A a' :=
  relativeHomotopyGroupEquivOfPathClass e ⟦h.somePath⟧

/-- In particular, `π_n(X, A, a)` and `π_n(X, A, a')` are noncanonically isomorphic whenever `a`
and `a'` are joined in the subtype `A`. -/
theorem relativeHomotopyGroupEquivOfJoined_nonempty
    (e :
      ∀ a : A, relativeHomotopyGroup n A a ≃ basedDiskBoundaryPairMapHomotopyClass n A a)
    {a a' : A} (h : Joined a a') :
    Nonempty (relativeHomotopyGroup n A a ≃ relativeHomotopyGroup n A a') :=
  ⟨relativeHomotopyGroupEquivOfJoined e h⟩
