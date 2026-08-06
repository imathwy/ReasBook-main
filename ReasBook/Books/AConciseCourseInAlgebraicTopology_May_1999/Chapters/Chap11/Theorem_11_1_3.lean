import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Definition_6_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Construction_13_2_4

open scoped Topology unitInterval

universe u

noncomputable section

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

-- Semantic recall via `lean_leansearch`: only homological mapping-cone/cofiber owners surfaced,
-- not a verified topological owner for the unbased mapping cone of a map of spaces. This file
-- therefore uses the local Chapter 6 mapping cylinder together with the Chapter 13 quotient model
-- `collapseSubsetType` for collapsing the top copy of `X`.

/-- The copy of `X` sitting at the top `t = 1` of the cylinder summand of `M_f`. -/
def mappingCylinderTopInclusion (f : C(X, Y)) : C(X, f.mappingCylinder) :=
  (ContinuousMap.mappingCylinderCylinderInclusion f).comp
    ((ContinuousMap.id X).prodMk (ContinuousMap.const X (1 : I)))

/-- The distinguished copy of `X` inside `M_f`, modeled as the range of the top inclusion. -/
abbrev mappingCylinderTopSubspace (f : C(X, Y)) : Set f.mappingCylinder :=
  Set.range (mappingCylinderTopInclusion f)

/-- The pair `(M_f, X)` consisting of the mapping cylinder and its top copy of `X`. -/
abbrev mappingCylinderPair (f : C(X, Y)) : SpacePair where
  space := f.mappingCylinder
  subspace := mappingCylinderTopSubspace f

/-- The mapping cone `C_f` obtained by collapsing the top copy of `X` inside `M_f`. -/
abbrev mappingCone (f : C(X, Y)) :=
  collapseSubsetType f.mappingCylinder (mappingCylinderTopSubspace f)

/-- The quotient map `M_f ⟶ C_f` collapsing the top copy of `X` to the cone point. -/
def mappingConeQuotientMap (f : C(X, Y)) : C(f.mappingCylinder, mappingCone f) :=
  ⟨fun z ↦ Quotient.mk'' z, continuous_quotient_mk'⟩

/-- The collapsed image of the top copy of `X` inside `C_f`. -/
def mappingConePointMap (f : C(X, Y)) : C(X, mappingCone f) :=
  (mappingConeQuotientMap f).comp (mappingCylinderTopInclusion f)

/-- A chosen representative of the cone point of `C_f`, obtained from any witness that `X` is
nonempty. -/
def mappingConePoint (f : C(X, Y)) (hX₀ : Nonempty X) : mappingCone f :=
  mappingConePointMap f (Classical.choice hX₀)

/-- Every point of the top copy of `X` has the same image in `C_f` as the chosen cone point. -/
theorem mappingConePointMap_eq_conePoint (f : C(X, Y)) (hX₀ : Nonempty X) (x : X) :
    mappingConePointMap f x = mappingConePoint f hX₀ := sorry

/-- The canonical image of the top copy of `X` inside `C_f`; this is the distinguished collapsed
subspace of the target pair. -/
abbrev mappingConeImage (f : C(X, Y)) : Set (mappingCone f) :=
  Set.range fun x : X ↦ mappingConePointMap f x

/-- If `X` is nonempty, the canonical image of the top copy of `X` in `C_f` is the singleton
consisting of the chosen cone point. -/
theorem mappingConeImage_eq_pointSet (f : C(X, Y)) (hX₀ : Nonempty X) :
    mappingConeImage f = ({mappingConePoint f hX₀} : Set (mappingCone f)) := sorry

/-- The pair `(C_f, *)` consisting of the mapping cone and its canonical collapsed image. -/
abbrev mappingConePair (f : C(X, Y)) : SpacePair where
  space := TopCat.of (mappingCone f)
  subspace := mappingConeImage f

/-- The quotient map `M_f ⟶ C_f` sends the top copy of `X` in `M_f` into the canonical collapsed
subspace of `C_f`. -/
theorem mappingConeQuotientMap_maps_topSubspace (f : C(X, Y)) (z : f.mappingCylinder)
    (hz : z ∈ mappingCylinderTopSubspace f) :
    mappingConeQuotientMap f z ∈ mappingConeImage f := sorry

/-- The quotient map of mapping-cylinder spaces induces a map of pairs `(M_f, X) ⟶ (C_f, *)`. -/
def mappingConePairMap (f : C(X, Y)) :
    mappingCylinderPair f ⟶ mappingConePair f where
  hom := TopCat.ofHom (mappingConeQuotientMap f)
  map_subspace' := by
    intro z hz
    exact mappingConeQuotientMap_maps_topSubspace f z hz

/-- The source `(n - 2)`-connectedness hypothesis used in Theorem 11.1.3: for `n = 1` it is
just `Nonempty`, and for `n ≥ 2` it is `Nonempty` together with `NConnectedSpace ((n : ℕ) - 2)`.
-/
abbrev mappingConeConnectivityHypothesis (n : ℕ+) (Z : Type u) [TopologicalSpace Z] : Prop :=
  Nonempty Z ∧ match (n : ℕ) with
    | 0 => True
    | 1 => True
    | m + 2 => NConnectedSpace m Z

/-- Theorem 11.1.3 (1): if `f : C(X, Y)` is an `((n : ℕ) - 1)`-equivalence and both `X` and `Y`
are `((n : ℕ) - 2)`-connected, then the quotient map of pairs `(M_f, X) ⟶ (C_f, *)` is a
`(2 * (n : ℕ) - 2)`-equivalence. The source connectivity meaning is recorded by
`mappingConeConnectivityHypothesis n Z`, which is just `Nonempty Z` when `n = 1` and otherwise
adds the `NConnectedSpace ((n : ℕ) - 2) Z` hypothesis tracked by this project. -/
theorem mappingConePairMap_isNEquivalence (f : C(X, Y)) (n : ℕ+)
    (hX : mappingConeConnectivityHypothesis n X)
    (hY : mappingConeConnectivityHypothesis n Y)
    (hf : IsNEquivalence ((n : ℕ) - 1) f)
    : SpacePair.Hom.IsNEquivalence (2 * (n : ℕ) - 2) (mappingConePairMap f) := sorry

/-- If `X` is nonempty, then the mapping cone `C_f` is nonempty via its cone point. -/
theorem mappingCone_nonempty (f : C(X, Y)) (hX₀ : Nonempty X) :
    Nonempty (mappingCone f) := sorry

/-- Theorem 11.1.3 (2): under the same hypotheses, the mapping cone `C_f` is
`((n : ℕ) - 1)`-connected in the full source-facing sense, namely it is nonempty and satisfies
`NConnectedSpace ((n : ℕ) - 1)`. The companion theorem `mappingCone_nonempty` isolates the
nonemptiness clause, while this labeled statement records the complete textbook conclusion. The
hypothesis `mappingConeConnectivityHypothesis n Z` ensures the domain and codomain assumptions
match the source `(n - 2)`-connected meaning at `n = 1` as well as for larger `n`. -/
theorem mappingCone_nConnectedSpace (f : C(X, Y)) (n : ℕ+)
    (hX : mappingConeConnectivityHypothesis n X)
    (hY : mappingConeConnectivityHypothesis n Y)
    (hf : IsNEquivalence ((n : ℕ) - 1) f)
    : Nonempty (mappingCone f) ∧ NConnectedSpace ((n : ℕ) - 1) (mappingCone f) := sorry
