import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Convention_5_2_7

universe u v w z

-- Semantic recall via `lean_leansearch` did not surface a canonical weak-product owner for based
-- compactly generated spaces in the current environment, so this item is formalized directly as
-- the compactly generated subspace of the product whose tuples differ from the basepoint only at
-- finitely many coordinates.

variable {ι : Type v}

/-- A tuple in a family of based spaces has finite non-basepoint support when it is equal to the
distinguished basepoint at all but finitely many coordinates. -/
def hasFiniteNonbasepointSupport (X : ι → PointedCompactlyGenerated.{u, w})
    (f : ∀ i, (X i).toCompactlyGenerated) : Prop :=
  { i | f i ≠ (X i).point }.Finite

/-- The finite-support condition for tuples in a family of based spaces is exactly finiteness of
the set of indices where the tuple differs from the distinguished basepoint. -/
theorem hasFiniteNonbasepointSupport_iff (X : ι → PointedCompactlyGenerated.{u, w})
    (f : ∀ i, (X i).toCompactlyGenerated) :
    hasFiniteNonbasepointSupport X f ↔ { i | f i ≠ (X i).point }.Finite :=
  Iff.rfl

/-- The weak product sits inside the full product as the subset of tuples with finite non-basepoint
support. -/
def weakProductSet (X : ι → PointedCompactlyGenerated.{u, w}) :
    Set (∀ i, (X i).toCompactlyGenerated) :=
  { f | hasFiniteNonbasepointSupport X f }

/-- Membership in `weakProductSet X` is exactly the finite non-basepoint support condition. -/
@[simp] theorem mem_weakProductSet (X : ι → PointedCompactlyGenerated.{u, w})
    (f : ∀ i, (X i).toCompactlyGenerated) :
    f ∈ weakProductSet X ↔ hasFiniteNonbasepointSupport X f :=
  Iff.rfl

/-- The carrier of the weak product is the subtype of the full product consisting of tuples with
finite non-basepoint support. -/
abbrev weakProductType (X : ι → PointedCompactlyGenerated.{u, w}) :=
  weakProductSet X

instance weakProductTypeCoeFun (X : ι → PointedCompactlyGenerated.{u, w}) :
    CoeFun (weakProductType X) (fun _ ↦ ∀ i, (X i).toCompactlyGenerated) where
  coe f := f.1

/-- The constant tuple of distinguished basepoints has finite non-basepoint support. -/
theorem hasFiniteNonbasepointSupport_basepoint
    (X : ι → PointedCompactlyGenerated.{u, w}) :
    hasFiniteNonbasepointSupport X (fun i ↦ (X i).point) := by
  simp [hasFiniteNonbasepointSupport]

/-- The distinguished basepoint of the weak product is the tuple whose every coordinate is the
distinguished basepoint of the corresponding factor. -/
def weakProductPoint (X : ι → PointedCompactlyGenerated.{u, w}) : weakProductType X :=
  ⟨fun i ↦ (X i).point, hasFiniteNonbasepointSupport_basepoint X⟩

/-- Each coordinate of `weakProductPoint X` is the distinguished basepoint of the corresponding
factor. -/
@[simp] theorem weakProductPoint_apply (X : ι → PointedCompactlyGenerated.{u, w}) (i : ι) :
    weakProductPoint X i = (X i).point :=
  rfl

/-- Helper for Definition 22.1.4: the `k`-ification of any topology is
`UCompactlyGeneratedSpace`. -/
private theorem uCompactlyGeneratedSpace_compactlyGenerated
    (Y : Type z) [TopologicalSpace Y] :
    @UCompactlyGeneratedSpace.{u} Y (TopologicalSpace.compactlyGenerated.{u} Y) := by
  let f : (Σ (i : (S : CompHaus.{u}) × C(S, Y)), i.fst) → Y := fun y ↦ y.1.2 y.2
  -- The evaluation map is continuous by construction for the coinduced topology.
  have hf : @Continuous ((Σ (i : (S : CompHaus.{u}) × C(S, Y)), i.fst)) Y
      instTopologicalSpaceSigma (TopologicalSpace.coinduced f inferInstance) f := by
    rw [continuous_iff_coinduced_le]
  -- The standard coinduced presentation of `TopologicalSpace.compactlyGenerated` gives the result.
  exact @uCompactlyGeneratedSpace_of_coinduced.{u, _, _}
    ((Σ (i : (S : CompHaus.{u}) × C(S, Y)), i.fst)) Y instTopologicalSpaceSigma
    (TopologicalSpace.coinduced f inferInstance) inferInstance f hf rfl

/-- Definition 22.1.4. The weak product of a family of based spaces is the subspace of the full
product consisting of tuples that equal the distinguished basepoint at all but finitely many
coordinates, formalized here in `PointedCompactlyGenerated` as the compactly generated subspace of
the product with finite non-basepoint support. -/
def weakProduct (X : ι → PointedCompactlyGenerated.{u, w}) : PointedCompactlyGenerated :=
  let t0 : TopologicalSpace (weakProductType X) := inferInstance
  letI : TopologicalSpace (weakProductType X) :=
    @TopologicalSpace.compactlyGenerated.{u} (weakProductType X) t0
  -- Replace the ordinary subtype topology by its compactly generated reflection.
  letI : UCompactlyGeneratedSpace.{u} (weakProductType X) :=
    @uCompactlyGeneratedSpace_compactlyGenerated (weakProductType X) t0
  -- Package the finite-support subtype together with the existing basepoint tuple.
  PointedCompactlyGenerated.of
    (CompactlyGenerated.of (weakProductType X))
    (weakProductPoint X)
