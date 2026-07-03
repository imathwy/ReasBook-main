import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_3_5_1 (from Items/Chap03) -/
universe u

set_option autoImplicit false

noncomputable section

open GroupPresentation

/-!
Primary domain: planar Cayley complexes and quadratic relator-root systems.

Layer triage:
- `source-facing`: a Cayley complex `C(X; R)` realized as an actual `TwoComplex`, together with a
  planar realization of that complex and the conclusion that the root system `S` of the relators
  is quadratic over the generator set `X`.
- `core/canonical`: `PresentationCoordinates C R` is the chapter owner for realizing an actual
  `TwoComplex` as `C(X; R)`, `C.EmbedsInPlane` is the chapter owner for planarity, and
  `IsQuadraticWordSet` is the chapter owner predicate for “quadratic over `X`”.
- `bridge/view`: `GroupPresentation.IsRelatorRootSet R S` is the source-facing bridge
  identifying `S` as a chosen relator-root system attached to `R`.

Domain sampling:
1. `PresentationCoordinates C R` from Proposition `3-4-1` is the owner abstraction for an actual
   Cayley complex with presentation data `(X; R)`.
2. `C.EmbedsInPlane` from Proposition `3-5-6` is the chapter owner proposition for planarity,
   with `TwoComplex.TwoManifoldEmbedding` as its witness layer.
3. `GroupPresentation.IsRelatorRootSet` from Definition `3-5-3` is the source-facing owner
   predicate identifying a chosen relator-root family attached to a relator family.
4. `IsQuadraticWordSet` from Proposition `1-7-4` is the chapter owner predicate for quadraticity
   over the canonical basis of `FreeGroup X`.

Primitive vs. derived:
- primitive data: the actual Cayley complex `C`, its coordinate realization over `(X; R)`, the
  planar hypothesis, and the source-facing root set `S`;
- derived API: the quadraticity conclusion on `S`, stated directly through
  `IsQuadraticWordSet`.
-/

namespace CayleyComplex.Coordinates

variable {X : Type u} {R : Set (FreeGroup X)} {C : TwoComplex}

/-- Proposition 3-5-1: if a Cayley complex `C(X; R)` is planar and `S` is a chosen relator-root
family for `R`, then `S` is quadratic over `X`. -/
-- Proof sketch: at a fixed vertex of the planar Cayley complex, each signed generator determines
-- a unique incident oriented edge. Planarity bounds the number of face-boundary loops beginning
-- with that edge by `2`, and the cyclic-permutation correspondence between relators and their
-- chosen roots transfers this bound to the occurrences of each generator in the chosen root
-- system.
theorem quadraticWordSet_of_planar
    (coords : PresentationCoordinates C R)
    (hplanar : C.EmbedsInPlane)
    {S : Set (FreeGroup X)}
    (hS : IsRelatorRootSet R S) :
    IsQuadraticWordSet (FreeGroupBasis.ofFreeGroup X) S := sorry

end CayleyComplex.Coordinates

/-! ### Definition_3_5_3 (from Items/Chap03) -/
universe u

set_option autoImplicit false

noncomputable section

variable {X : Type u}

open FreeGroup.Finset

-- Layer triage:
-- `source-facing`: a group together with a finite presentation `G = (X; R)` and a finite chosen
-- relator-root family `S`, with `S` strictly quadratic and having cyclic star graph.
-- `core/canonical`: `PresentedGroup R` for groups given by generators and relations, `Finite X`
-- for the finite generator datum, `Set.Finite R` as the derived finiteness predicate for relator
-- families coming from finite root systems, `SignedLetter X` for the
-- signed-basis vocabulary, `IsStrictlyQuadraticSet` from Proposition `1-7-6`,
-- `FreeGroup.Finset.sigmaGraph` from Proposition `1-7-8`, and `SimpleGraph.IsCycles` for the
-- graph-theoretic cycle condition.
-- `bridge/view`: the textbook phrase "the chosen set `S` of relator roots" is
-- expressed by `GroupPresentation.IsRelatorRootSet`; the star-graph condition is
-- expressed directly by the owner predicates `(sigmaGraph S).Connected` and
-- `(sigmaGraph S).IsCycles`.
-- Domain sampling:
-- 1. `PresentedGroup R`, together with `Finite X`, is the
--    canonical owner layer for finite presentations.
-- 2. `IsStrictlyQuadraticSet` from Proposition `1-7-6` is the chapter owner for strict
--    quadraticity of finite free-group word systems, so this file reuses it directly.
-- 3. `FreeGroup.Finset.sigmaGraph` from Proposition `1-7-8` is the chapter owner construction
--    for the star graph attached to a finite system of reduced words.
-- 4. `GroupPresentation` from Chapter `2` is the natural owner namespace for auxiliary
--    presentation-level predicates, so the relator-root and relator-power relations live there
--    rather than as bare globals.
-- 5. `Set.Finite.image` is the canonical finiteness API showing that a relator set realized as the
--    image of a finite root family under `s ↦ s ^ m s` is finite, so that finiteness is derived
--    rather than stored as primitive data.
-- 6. `SimpleGraph.IsCycles` is mathlib's owner predicate for graphs whose nonisolated vertices all
--    have degree `2`, so together with connectedness it captures the textbook "cyclic graph"
--    condition.
-- Primitive vs. derived:
-- the primitive source data are the finite presentation `(X; R)` and the finite chosen relator
-- root system `S`, expressed source-facing by `GroupPresentation.IsRelatorRootSet` and canonically
-- by a multiplicity witness for `GroupPresentation.IsRelatorPowerFamily`. The finiteness of `R`,
-- strict quadraticity, and the star graph are derived through the owner predicates already
-- available upstream.

namespace GroupPresentation

/-- A multiplicity function `m` realizes `R` as the relator power family on `S` when the
relators are exactly the powers `s ^ m(s)` with `s ∈ S`. -/
def IsRelatorPowerFamily
    (R : Set (FreeGroup X)) (S : Set (FreeGroup X)) (m : FreeGroup X → ℕ+) : Prop :=
  R = Set.image (fun s : FreeGroup X ↦ s ^ (m s : ℕ)) S

/-- A multiplicity function `m` realizes `R` as a primitive relator power family on `S` when the
relators are exactly the powers `s ^ m(s)` with `s ∈ S` and every chosen root in `S` is
primitive. -/
def IsPrimitiveRelatorPowerFamily
    (R : Set (FreeGroup X)) (S : Set (FreeGroup X)) (m : FreeGroup X → ℕ+) : Prop :=
  IsRelatorPowerFamily R S m ∧ ∀ ⦃s : FreeGroup X⦄, s ∈ S → ¬ IsProperPower s

/-- A set `S` is a chosen relator-root family for `R` when some multiplicity function realizes the
relators exactly as the powers `s ^ m(s)` with `s ∈ S`. -/
def IsRelatorRootSet (R : Set (FreeGroup X)) (S : Set (FreeGroup X)) : Prop :=
  ∃ m : FreeGroup X → ℕ+, IsRelatorPowerFamily R S m

theorem IsRelatorPowerFamily.isRelatorRootSet
    {R S : Set (FreeGroup X)} {m : FreeGroup X → ℕ+}
    (hR : IsRelatorPowerFamily R S m) :
    IsRelatorRootSet R S :=
  ⟨m, hR⟩

theorem IsPrimitiveRelatorPowerFamily.isRelatorPowerFamily
    {R S : Set (FreeGroup X)} {m : FreeGroup X → ℕ+}
    (hR : IsPrimitiveRelatorPowerFamily R S m) :
    IsRelatorPowerFamily R S m :=
  hR.1

theorem IsPrimitiveRelatorPowerFamily.isRelatorRootSet
    {R S : Set (FreeGroup X)} {m : FreeGroup X → ℕ+}
    (hR : IsPrimitiveRelatorPowerFamily R S m) :
    IsRelatorRootSet R S :=
  hR.isRelatorPowerFamily.isRelatorRootSet

/-- A relator family realized by powers of a finite chosen root system is finite. -/
theorem IsRelatorRootSet.finite_relators
    {R : Set (FreeGroup X)} {S : Finset (FreeGroup X)}
    (hR : IsRelatorRootSet R S) :
    R.Finite := by
  rcases hR with ⟨m, hm⟩
  rw [hm]
  exact (S.finite_toSet.image fun s : FreeGroup X ↦ s ^ (m s : ℕ))

/-- A primitive chosen relator root is a relator root that is not itself a proper power. -/
def IsPrimitiveRelatorRoot (S : Set (FreeGroup X)) (s : FreeGroup X) : Prop :=
  s ∈ S ∧ ¬ IsProperPower s

theorem IsPrimitiveRelatorPowerFamily.isPrimitiveRelatorRoot
    {R S : Set (FreeGroup X)} {m : FreeGroup X → ℕ+}
    (hR : IsPrimitiveRelatorPowerFamily R S m) {s : FreeGroup X} (hs : s ∈ S) :
    IsPrimitiveRelatorRoot S s :=
  ⟨hs, hR.2 hs⟩

end GroupPresentation

/-- Definition 3-5-3: an `F`-group is a group admitting a finite presentation `G = (X; R)` whose
finite chosen relator-root system `S` is strictly quadratic over `X` and has cyclic star graph. -/
class IsFGroup (G : Type u) [Group G] : Prop where
  /-- An `F`-group admits finite presentation data whose finite chosen relator-root system is
  strictly quadratic and has cyclic star graph. -/
  exists_presentation :
    ∃ (X : Type u) (_ : Finite X) (R : Set (FreeGroup X)) (S : Finset (FreeGroup X)),
      ∃ _ : PresentedGroup R ≃* G,
        GroupPresentation.IsRelatorRootSet R S ∧
        IsStrictlyQuadraticSet S ∧
        (sigmaGraph S).Connected ∧
        (sigmaGraph S).IsCycles

end

/-! ### Proposition_3_5_4 (from Items/Chap03) -/
universe u

open scoped Classical
open FreeGroupBasis

set_option autoImplicit false

noncomputable section

namespace FGroupPresentation

/-
Primary domain: combinatorial group theory of finite presentations of `F`-groups.

Layer triage:
- `source-facing`: a concrete finite presentation on generators `x_i` and `y_j` with torsion
  relators `x_i ^ {m_i}` and one final relator `x_1 ... x_p q`, where `q` is an orientable or
  nonorientable quadratic surface word.
- `core/canonical`: `PresentedGroup` is the owner object for groups given by generators and
  relators, `IsFGroup` from Definition `3-5-3` is the owner predicate for the hypothesis,
  `(ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct` is the chapter owner for the orientable
  surface relator, and `SurfaceGroup.nonorientableRelator` is the chapter owner for the
  nonorientable surface relator.
- `bridge/view`: the theorem below expresses the textbook normal form as a concrete pair of
  canonical relator families for `PresentedGroup`.

Domain sampling:
1. `PresentedGroup` is the canonical mathlib object for a group with a specified presentation.
2. `IsFGroup` from Definition `3-5-3` is the project owner predicate for the hypothesis.
3. `(ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct` from Proposition `1-6-8` is the
   project owner relator for the orientable surface word, so this file should not rebuild it by
   hand with `Fin (2 * g)` arithmetic.
4. `SurfaceGroup.nonorientableRelator` from Proposition `2-5-13` is the project owner relator for
   the nonorientable surface word.
Primitive vs. derived:
- primitive data: the torsion exponents `m : Fin p → ℕ` and the canonical surface relator from
  the orientable or nonorientable branch;
- derived API: the relator families `orientableStandardRelators` and
  `nonorientableStandardRelators` built by adjoining the torsion relators and the ordered product
  `x₁ ⋯ xₚ`.
-/

/-- The ordered product `x_1 ... x_p` of the torsion generators. -/
def xProduct (p : ℕ) (Y : Type*) : FreeGroup (Fin p ⊕ Y) :=
  (List.ofFn fun i : Fin p ↦ FreeGroup.of (Sum.inl i)).prod

/-- The torsion relators `x_i ^ {m_i}` appearing in the normal form presentation. -/
def torsionRelators {p : ℕ} {Y : Type*} (m : Fin p → ℕ) : Set (FreeGroup (Fin p ⊕ Y)) :=
  Set.range fun i : Fin p ↦ FreeGroup.of (Sum.inl i) ^ m i

/-- The orientable relator family from Proposition `3-5-4`, using the canonical paired-index
surface relator from Proposition `1-6-8`. -/
def orientableStandardRelators (p g : ℕ) (m : Fin p → ℕ) :
    Set (FreeGroup (Fin p ⊕ (Fin g ⊕ Fin g))) :=
  torsionRelators m ∪
    {xProduct p (Fin g ⊕ Fin g) *
      FreeGroup.map Sum.inr (ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct}

/-- The nonorientable relator family from Proposition `3-5-4`, using the canonical nonorientable
surface relator from Proposition `2-5-13`. -/
def nonorientableStandardRelators (p g : ℕ) (m : Fin p → ℕ) :
    Set (FreeGroup (Fin p ⊕ Fin g)) :=
  torsionRelators m ∪
    {xProduct p (Fin g) *
      FreeGroup.map Sum.inr (SurfaceGroup.nonorientableRelator g)}

@[simp] theorem xProduct_zero (Y : Type*) :
    xProduct 0 Y = 1 := by
  simp [xProduct]

@[simp] theorem torsionRelators_zero (Y : Type*) :
    torsionRelators (fun i : Fin 0 ↦ nomatch i) = (∅ : Set (FreeGroup (Fin 0 ⊕ Y))) := by
  ext w
  simp [torsionRelators]

@[simp] theorem orientableStandardRelators_zero (g : ℕ) :
    orientableStandardRelators 0 g (fun i ↦ nomatch i) =
      {FreeGroup.map Sum.inr (ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct} := by
  simp [orientableStandardRelators]

@[simp] theorem nonorientableStandardRelators_zero (g : ℕ) :
    nonorientableStandardRelators 0 g (fun i ↦ nomatch i) =
      {FreeGroup.map Sum.inr (SurfaceGroup.nonorientableRelator g)} := by
  simp [nonorientableStandardRelators]

@[simp] theorem freeGroupCongr_emptySum_map_inr {Y : Type*} (w : FreeGroup Y) :
    FreeGroup.freeGroupCongr (Equiv.emptySum (Fin 0) Y) (FreeGroup.map Sum.inr w) = w := by
  calc
    FreeGroup.freeGroupCongr (Equiv.emptySum (Fin 0) Y) (FreeGroup.map Sum.inr w)
      = FreeGroup.map (Equiv.emptySum (Fin 0) Y) (FreeGroup.map Sum.inr w) := rfl
    _ = FreeGroup.map ((Equiv.emptySum (Fin 0) Y) ∘ Sum.inr) w := by
      rw [FreeGroup.map.comp]
    _ = FreeGroup.map (fun y ↦ y) w := by
      refine congrArg (fun f ↦ FreeGroup.map f w) ?_
      ext y
      simp
    _ = w := FreeGroup.map.id' w

@[simp] theorem freeGroupCongr_emptySum_image_orientableStandardRelators_zero (g : ℕ) :
    FreeGroup.freeGroupCongr (Equiv.emptySum (Fin 0) (Fin g ⊕ Fin g)) ''
      orientableStandardRelators 0 g (fun i ↦ nomatch i) =
        {(ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct} := by
  rw [orientableStandardRelators_zero, Set.image_singleton]
  rw [freeGroupCongr_emptySum_map_inr]

@[simp] theorem freeGroupCongr_emptySum_image_nonorientableStandardRelators_zero (g : ℕ) :
    FreeGroup.freeGroupCongr (Equiv.emptySum (Fin 0) (Fin g)) ''
      nonorientableStandardRelators 0 g (fun i ↦ nomatch i) =
        {SurfaceGroup.nonorientableRelator g} := by
  rw [nonorientableStandardRelators_zero, Set.image_singleton]
  rw [freeGroupCongr_emptySum_map_inr]

/-- The torsion-free orientable standard presentation is the canonical orientable surface-group
owner from Chapter `2`. -/
def orientableStandardMulEquivSurfaceGroup (g : ℕ) :
    PresentedGroup (orientableStandardRelators 0 g (fun i ↦ nomatch i)) ≃*
      SurfaceGroup.Orientable g := by
  let e :=
    PresentedGroup.equivPresentedGroup
      (orientableStandardRelators 0 g (fun i ↦ nomatch i))
      (Equiv.emptySum (Fin 0) (Fin g ⊕ Fin g))
  let hrels :
      FreeGroup.freeGroupCongr (Equiv.emptySum (Fin 0) (Fin g ⊕ Fin g)) ''
        orientableStandardRelators 0 g (fun i ↦ nomatch i) =
          {(ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct} :=
    freeGroupCongr_emptySum_image_orientableStandardRelators_zero g
  show PresentedGroup (orientableStandardRelators 0 g (fun i ↦ nomatch i)) ≃*
      PresentedGroup {(ofFreeGroup (Fin g ⊕ Fin g)).pairedCommutatorProduct}
  exact
    cast
      (congrArg
        (fun S ↦
          PresentedGroup (orientableStandardRelators 0 g (fun i ↦ nomatch i)) ≃*
            PresentedGroup S)
        hrels)
      e

/-- The torsion-free nonorientable standard presentation is the canonical nonorientable
surface-group owner from Chapter `2`. -/
def nonorientableStandardMulEquivSurfaceGroup (g : ℕ) :
    PresentedGroup (nonorientableStandardRelators 0 g (fun i ↦ nomatch i)) ≃*
      SurfaceGroup.Nonorientable g := by
  let e :=
    PresentedGroup.equivPresentedGroup
      (nonorientableStandardRelators 0 g (fun i ↦ nomatch i))
      (Equiv.emptySum (Fin 0) (Fin g))
  let hrels :
      FreeGroup.freeGroupCongr (Equiv.emptySum (Fin 0) (Fin g)) ''
        nonorientableStandardRelators 0 g (fun i ↦ nomatch i) =
          {SurfaceGroup.nonorientableRelator g} :=
    freeGroupCongr_emptySum_image_nonorientableStandardRelators_zero g
  show PresentedGroup (nonorientableStandardRelators 0 g (fun i ↦ nomatch i)) ≃*
      PresentedGroup {SurfaceGroup.nonorientableRelator g}
  exact
    cast
      (congrArg
        (fun S ↦
          PresentedGroup (nonorientableStandardRelators 0 g (fun i ↦ nomatch i)) ≃*
            PresentedGroup S)
        hrels)
      e

variable {G : Type u} [Group G]

/-- Proposition 3-5-4: every `F`-group admits either an orientable standard presentation with
relator family `x_i ^ {m_i}` together with `x_1 ... x_p [y_1, y_2] ... [y_{2g-1}, y_{2g}]`, or a
nonorientable standard presentation with relator family `x_i ^ {m_i}` together with
`x_1 ... x_p y_1^2 ... y_g^2`, with all exponents `m_i > 1`. -/
-- Proof sketch: begin with the strictly quadratic relator-root presentation furnished by
-- `IsFGroup`, apply the Nielsen normalization cited in the text to isolate the torsion generators
-- `x_i`, and then use the final Tietze transformation introducing `x_p` so that the last relator
-- becomes `x_1 ... x_p q`; the cyclic quadratic word `q` is either the orientable or the
-- nonorientable surface word.
theorem exists_standard_surface_presentation_of_isFGroup (hG : IsFGroup G) :
    (∃ (p g : ℕ) (m : Fin p → ℕ),
      ∃ _ : PresentedGroup (orientableStandardRelators p g m) ≃* G,
        ∀ i, 1 < m i) ∨
    (∃ (p g : ℕ) (m : Fin p → ℕ),
      ∃ _ : PresentedGroup (nonorientableStandardRelators p g m) ≃* G,
        ∀ i, 1 < m i) := sorry

/-- A standard surface presentation of the form exhibited in Proposition `3-5-4` makes the
ambient group into an `F`-group. -/
-- Proof sketch: rewrite the displayed standard presentation as the finite presentation required by
-- Definition `3-5-3`. The relator roots are the torsion generators together with the surface
-- relator, which form a finite strictly quadratic system with cyclic star graph by the
-- normalization analysis behind Proposition `3-5-4`.
theorem isFGroup_of_standardSurfacePresentation
    (hG :
      (∃ (p g : ℕ) (m : Fin p → ℕ),
        ∃ _ : PresentedGroup (orientableStandardRelators p g m) ≃* G,
          ∀ i, 1 < m i) ∨
      (∃ (p g : ℕ) (m : Fin p → ℕ),
        ∃ _ : PresentedGroup (nonorientableStandardRelators p g m) ≃* G,
          ∀ i, 1 < m i)) :
    IsFGroup G := sorry

end FGroupPresentation

/-! ### Proposition_3_5_5 (from Items/Chap03) -/
universe u v w z

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)
local notation "𝔻²" => Metric.closedBall (0 : 𝔼²) 1

/-!
Primary domain: planar Cayley complexes, topological surfaces, and free products of cyclic groups.

Layer triage:
- `source-facing`: a concrete Cayley-complex realization of a presentation of `G` whose Cayley
  complex embeds in a `2`-manifold.
- `core/canonical`: `CayleyComplex.Coordinates` is the owner for a Cayley-complex realization,
  `ChartedSpace 𝔼² S` is the standard local-Euclidean owner for a
  topological `2`-manifold model, and `Monoid.CoprodI` is mathlib's owner for indexed free
  products.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding` is the cellwise topological-realization owner
  for a `2`-complex in a surface, and `TwoComplex.EmbedsInTwoManifold` /
  `IsFreeProductOfCyclicGroups` expose the source-facing existence hypotheses and conclusions
  directly.

Domain sampling:
1. `CayleyComplex.Coordinates` is the canonical chapter owner for the actual Cayley complex
   attached to a presentation.
2. `ChartedSpace 𝔼² S` is mathlib's standard local-Euclidean owner for a topological
   `2`-manifold model.
3. `Monoid.CoprodI A` is mathlib's owner for free products indexed by a family of groups, while
   `IsCyclic (A i)` is the owner predicate for cyclic factors.

Primitive vs. derived:
- primitive data: the actual vertex placement together with closed-interval edge maps and
  closed-disk face maps that are topological embeddings into the ambient surface;
- derived API: the closed edge-images and face-images, their opposite-orientation invariance, and
  the source-style manifold-embeddability predicate.
-/

namespace TwoComplex

/-- A `2`-complex embedding into a topological surface consists of an injective placement of
vertices together with compatible closed-interval edge maps and closed-disk face maps. -/
structure TwoManifoldEmbedding (C : TwoComplex) (S : Type v) [TopologicalSpace S] where
  /-- The placement of vertices in the ambient surface. -/
  vertexMap : C.skeleton → S
  /-- A cellwise realization of each oriented edge by a closed interval. -/
  edgeMap : C.skeleton.Edge → Set.Icc (0 : ℝ) 1 → S
  /-- A cellwise realization of each oriented face by a closed disk. -/
  faceMap : C.Face → 𝔻² → S
  /-- Distinct vertices have distinct images. -/
  vertex_injective : Function.Injective vertexMap
  /-- Each oriented edge is realized by a closed topological embedding of the closed interval. -/
  edge_isClosedEmbedding (e : C.skeleton.Edge) : Topology.IsClosedEmbedding (edgeMap e)
  /-- Each oriented face is realized by a closed topological embedding of the closed disk. -/
  face_isClosedEmbedding (D : C.Face) : Topology.IsClosedEmbedding (faceMap D)
  /-- The initial vertex of an oriented edge is the left endpoint of its realized interval. -/
  source_eq_edgeMap_zero (e : C.skeleton.Edge) :
    edgeMap e ⟨0, by norm_num, by norm_num⟩ = vertexMap (C.skeleton.initial e)
  /-- The terminal vertex of an oriented edge is the right endpoint of its realized interval. -/
  target_eq_edgeMap_one (e : C.skeleton.Edge) :
    edgeMap e ⟨1, by norm_num, by norm_num⟩ = vertexMap (C.skeleton.terminal e)
  /-- Opposite orientations of an edge have the same closed image. -/
  edgeInv_range (e : C.skeleton.Edge) :
    Set.range (edgeMap (C.skeleton.edgeInv e)) = Set.range (edgeMap e)
  /-- Opposite orientations of a face have the same closed image. -/
  faceInv_range (D : C.Face) :
    Set.range (faceMap (C.faceInv D)) = Set.range (faceMap D)
  /-- Every boundary edge of a face is contained in the realized image of that face. -/
  boundary_edge_subset_face {D : C.Face} {a : Quiver.Total C.skeleton} (ha : a ∈ (C.boundary D).1) :
    Set.range (edgeMap a.hom.1) ⊆ Set.range (faceMap D)
  /-- Every vertex on the boundary of a face lies in the realized image of that face. -/
  boundary_vertex_mem_face {D : C.Face} {x : C.skeleton} :
    C.VertexOnFace x D → vertexMap x ∈ Set.range (faceMap D)

namespace TwoManifoldEmbedding

variable {C : TwoComplex} {S : Type v} [TopologicalSpace S]

/-- The closed image of an oriented edge in a surface embedding. -/
def edgeSet (embedding : TwoManifoldEmbedding C S) (e : C.skeleton.Edge) : Set S :=
  Set.range (embedding.edgeMap e)

/-- The closed image of an oriented face in a surface embedding. -/
def faceSet (embedding : TwoManifoldEmbedding C S) (D : C.Face) : Set S :=
  Set.range (embedding.faceMap D)

/-- The initial vertex of an oriented edge lies in its closed image. -/
theorem source_mem_edge (embedding : TwoManifoldEmbedding C S) (e : C.skeleton.Edge) :
    embedding.vertexMap (C.skeleton.initial e) ∈ embedding.edgeSet e := by
  exact ⟨⟨0, by norm_num, by norm_num⟩, embedding.source_eq_edgeMap_zero e⟩

/-- The terminal vertex of an oriented edge lies in its closed image. -/
theorem target_mem_edge (embedding : TwoManifoldEmbedding C S) (e : C.skeleton.Edge) :
    embedding.vertexMap (C.skeleton.terminal e) ∈ embedding.edgeSet e := by
  exact ⟨⟨1, by norm_num, by norm_num⟩, embedding.target_eq_edgeMap_one e⟩

/-- Each oriented edge has a closed geometric image. -/
theorem edge_isClosed (embedding : TwoManifoldEmbedding C S) (e : C.skeleton.Edge) :
    IsClosed (embedding.edgeSet e) :=
  (embedding.edge_isClosedEmbedding e).isClosed_range

/-- Each oriented face has a closed geometric image. -/
theorem face_isClosed (embedding : TwoManifoldEmbedding C S) (D : C.Face) :
    IsClosed (embedding.faceSet D) :=
  (embedding.face_isClosedEmbedding D).isClosed_range

/-- Opposite orientations of an edge have the same geometric image. -/
theorem edgeInv_set (embedding : TwoManifoldEmbedding C S) (e : C.skeleton.Edge) :
    embedding.edgeSet (C.skeleton.edgeInv e) = embedding.edgeSet e :=
  embedding.edgeInv_range e

/-- Opposite orientations of a face have the same geometric image. -/
theorem faceInv_set (embedding : TwoManifoldEmbedding C S) (D : C.Face) :
    embedding.faceSet (C.faceInv D) = embedding.faceSet D :=
  embedding.faceInv_range D

/-- The geometric image of an unoriented face, obtained by quotienting the oriented-face image
along reversal. -/
def geometricFaceSet (embedding : TwoManifoldEmbedding C S) :
    TwoComplex.GeometricFace C → Set S :=
  Quotient.lift embedding.faceSet fun D E h ↦ by
    rcases h with rfl | h
    · rfl
    · simpa [h] using embedding.faceInv_set E

@[simp] theorem geometricFaceSet_mk
    (embedding : TwoManifoldEmbedding C S) (D : C.Face) :
    embedding.geometricFaceSet ⟦D⟧ = embedding.faceSet D :=
  rfl

/-- The union of the geometric images of a family of unoriented faces. -/
def geometricFaceUnion (embedding : TwoManifoldEmbedding C S)
    (faces : Set (TwoComplex.GeometricFace C)) : Set S :=
  ⋃ D ∈ faces, embedding.geometricFaceSet D

/-- An ambient homeomorphism realizes a `2`-complex automorphism when it carries each geometric
face image to the image of its image face. -/
def RealizesAutomorphism
    (embedding : TwoManifoldEmbedding C S)
    (α : TwoComplex.Aut C) (φ : Homeomorph S S) : Prop :=
  ∀ D : TwoComplex.GeometricFace C,
    φ '' embedding.geometricFaceSet D = embedding.geometricFaceSet (α.geometricFacePerm D)

end TwoManifoldEmbedding

/-- A `2`-complex embeds in a `2`-manifold when it admits a geometric embedding into a Hausdorff
charted space locally modelled on `ℝ²`. -/
def EmbedsInTwoManifold (C : TwoComplex) : Prop :=
  ∃ (S : Type z) (_ : TopologicalSpace S) (_ : T2Space S) (_ : ChartedSpace 𝔼² S),
      Nonempty (TwoManifoldEmbedding C S)

end TwoComplex

/-- A group is a free product of cyclic groups when it is isomorphic to an indexed free product
`Monoid.CoprodI A` with cyclic factor groups. -/
def IsFreeProductOfCyclicGroups (G : Type u) [Group G] : Prop :=
  ∃ (ι : Type v) (A : ι → Type w) (_ : ∀ i, Group (A i)) (_ : ∀ i, IsCyclic (A i)),
    Nonempty (Monoid.CoprodI A ≃* G)

section Proposition355

variable {G : Type u} [Group G]
variable {X : Type v} {R : Set (FreeGroup X)} {C : TwoComplex}

/-- Proposition 3-5-5: every group admitting a presentation whose Cayley complex embeds in a
`2`-manifold is either an `F`-group or a free product of cyclic groups. -/
-- Proof sketch: analyze the relator-root system of the given planar Cayley presentation as in the
-- text. A finite strictly quadratic connected component gives an `F`-group by Proposition
-- `3-5-4`; otherwise each component normalizes to cyclic relators, and the presentation splits as
-- a free product of cyclic groups.
theorem isFGroup_or_isFreeProductOfCyclicGroups_of_cayleyComplex_embedsInTwoManifold
    (coords : CayleyComplex.Coordinates.PresentationCoordinates C R)
    (e : PresentedGroup R ≃* G) (hC : C.EmbedsInTwoManifold) :
    IsFGroup G ∨ IsFreeProductOfCyclicGroups G := sorry

end Proposition355

/-! ### Proposition_3_5_6 (from Items/Chap03) -/
universe u v w z

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)
local notation "𝕊²" =>
  { x : EuclideanSpace ℝ (Fin 3) // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 }

/-!
Primary domain: Cayley complexes, planar/spherical embeddings, and free products of cyclic groups.

Layer triage:
- `source-facing`: groups `G` that are either `F`-groups or free products of at most countably
  many cyclic groups, together with presentations whose Cayley complexes admit embeddings in the
  sphere or in the plane.
- `core/canonical`: `PresentedGroup R` is the owner for the presented group,
  `CayleyComplex.Coordinates.PresentationCoordinates C R` is the chapter owner for an actual
  Cayley complex with its standard coordinates, `TwoComplex.EmbedsInTwoManifold` from Proposition
  `3-5-5` is the intrinsic owner for embeddability in a `2`-manifold, and
  `IsFreeProductOfCyclicGroups` from Proposition `3-5-5` is the chapter owner for cyclic free
  products.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding` from Proposition `3-5-5` is the cellwise
  topological witness layer, the planar and spherical notions in this file are source-facing
  specializations to `ℝ²` and `𝕊²` that bridge back to `EmbedsInTwoManifold`, and
  `IsCountableFreeProductOfCyclicGroups` below is the source-facing countable refinement of the
  owner predicate `IsFreeProductOfCyclicGroups`, built from mathlib's indexed free-product owner
  `Monoid.CoprodI A`, the canonical cyclicity predicate `IsCyclic (A i)`, and a `Countable`
  indexing type.

Domain sampling:
1. `CayleyComplex.Coordinates.PresentationCoordinates C R` from Proposition `3-4-1` is the owner
   for an actual Cayley complex `C(X; R)` with coordinates over `PresentedGroup R`.
2. `TwoComplex.EmbedsInTwoManifold` from Proposition `3-5-5` is the intrinsic owner for the
   embeddability conclusion used across the chapter.
3. `TwoComplex.TwoManifoldEmbedding` from Proposition `3-5-5` is the chapter owner for the
   primitive geometric embedding data behind that intrinsic owner.
4. `IsFreeProductOfCyclicGroups` from Proposition `3-5-5` is the owner predicate for cyclic
   free-product decompositions, and the countable variant in this file should refine that owner
   instead of inlining a fresh existential package in each theorem statement.
-/

namespace TwoComplex

/-- A `2`-complex embeds in the plane when it admits a surface embedding into `ℝ²`. -/
def EmbedsInPlane (C : TwoComplex) : Prop :=
  Nonempty (TwoManifoldEmbedding C 𝔼²)

/-- A `2`-complex embeds in the `2`-sphere when it admits a surface embedding into `𝕊²`. -/
def EmbedsInSphere (C : TwoComplex) : Prop :=
  Nonempty (TwoManifoldEmbedding C 𝕊²)

/-- A planar embedding is, in particular, an embedding into a `2`-manifold. -/
-- Proof sketch: `ℝ²` is itself a Hausdorff charted `2`-manifold, so the planar witness is a
-- special case of the owner predicate `EmbedsInTwoManifold`.
theorem embedsInTwoManifold_of_embedsInPlane {C : TwoComplex} (hC : C.EmbedsInPlane) :
    TwoComplex.EmbedsInTwoManifold.{0} C := by
  exact ⟨𝔼², inferInstance, inferInstance, inferInstance, hC⟩

/-- A spherical embedding is, in particular, an embedding into a `2`-manifold. -/
-- Proof sketch: the standard unit sphere `𝕊²` carries its canonical Hausdorff charted
-- `2`-manifold structure, so a spherical embedding is a specialization of
-- `EmbedsInTwoManifold`.
theorem embedsInTwoManifold_of_embedsInSphere {C : TwoComplex} (hC : C.EmbedsInSphere) :
    TwoComplex.EmbedsInTwoManifold.{0} C := by
  exact ⟨𝕊², inferInstance, inferInstance, inferInstance, hC⟩

namespace TwoManifoldEmbedding

/-- Restricting a surface embedding along a nested subcomplex keeps the same geometric cell images
on the smaller carried complex. -/
def restrict {C : TwoComplex} {X : Type v} [TopologicalSpace X] {S T : Subcomplex C}
    (embedding : TwoComplex.TwoManifoldEmbedding S.complex X)
    (hvertex : T.skeleton.vertexSet ⊆ S.skeleton.vertexSet)
    (hedge : T.skeleton.edgeSet ⊆ S.skeleton.edgeSet)
    (hface : T.faceSet ⊆ S.faceSet) :
    TwoComplex.TwoManifoldEmbedding T.complex X := by
  refine
    { vertexMap := fun v ↦ embedding.vertexMap ⟨v.1, hvertex v.2⟩
      edgeMap := fun e ↦ embedding.edgeMap ⟨e.1, hedge e.2⟩
      faceMap := fun D ↦ embedding.faceMap ⟨D.1, hface D.2⟩
      vertex_injective := ?_
      edge_isClosedEmbedding := ?_
      face_isClosedEmbedding := ?_
      source_eq_edgeMap_zero := ?_
      target_eq_edgeMap_one := ?_
      edgeInv_range := ?_
      faceInv_range := ?_
      boundary_edge_subset_face := ?_
      boundary_vertex_mem_face := ?_ }
  · intro v w h
    apply Subtype.ext
    exact congrArg (fun x : S.skeleton.vertexSet ↦ x.1) (embedding.vertex_injective h)
  · intro e
    simpa using embedding.edge_isClosedEmbedding ⟨e.1, hedge e.2⟩
  · intro D
    simpa using embedding.face_isClosedEmbedding ⟨D.1, hface D.2⟩
  · intro e
    simpa using embedding.source_eq_edgeMap_zero ⟨e.1, hedge e.2⟩
  · intro e
    simpa using embedding.target_eq_edgeMap_one ⟨e.1, hedge e.2⟩
  · intro e
    simpa using embedding.edgeInv_range ⟨e.1, hedge e.2⟩
  · intro D
    simpa using embedding.faceInv_range ⟨D.1, hface D.2⟩
  · sorry
  · intro D v hv
    exact embedding.boundary_vertex_mem_face
      (Subcomplex.vertexOnFace_of_subset S T hvertex hedge hface hv)

/-- A planar surface embedding fills the plane when the union of all oriented face images is all
of `ℝ²`. -/
def FillsPlane
    {C : TwoComplex}
    (embedding : TwoManifoldEmbedding C 𝔼²) : Prop :=
  (⋃ D : C.Face, embedding.faceSet D) = Set.univ

/-- Filling the plane means exactly that every point of `ℝ²` lies in the image of some oriented
face. -/
-- Proof sketch: unfold `FillsPlane` and rewrite membership in the union of the face images.
theorem fillsPlane_iff
    {C : TwoComplex}
    (embedding : TwoManifoldEmbedding C 𝔼²) :
    embedding.FillsPlane ↔
      ∀ x : 𝔼², ∃ D : C.Face, x ∈ embedding.faceSet D := by
  constructor
  · intro h x
    have hx : x ∈ ⋃ D : C.Face, embedding.faceSet D := by
      rw [h]
      simp
    simpa [Set.mem_iUnion] using hx
  · intro h
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases h x with ⟨D, hD⟩
      simpa [Set.mem_iUnion] using Exists.intro D hD

end TwoManifoldEmbedding

end TwoComplex

/-- A group is a countable free product of cyclic groups when it is isomorphic to an indexed free
product `Monoid.CoprodI A` of cyclic groups over a countable index type. -/
def IsCountableFreeProductOfCyclicGroups (G : Type u) [Group G] : Prop :=
  ∃ (ι : Type v) (_ : Countable ι) (A : ι → Type w) (_ : ∀ i, Group (A i))
    (_ : ∀ i, IsCyclic (A i)), Nonempty (Monoid.CoprodI A ≃* G)

/-- A countable free product of cyclic groups is, in particular, a free product of cyclic
groups. -/
theorem IsCountableFreeProductOfCyclicGroups.isFreeProductOfCyclicGroups
    {G : Type u} [Group G] (hG : IsCountableFreeProductOfCyclicGroups G) :
    IsFreeProductOfCyclicGroups G := sorry

section Proposition356

variable {G : Type u} [Group G]

/-- Proposition 3-5-6 (1): if `G` is either an `F`-group or a free product of at most countably
many cyclic groups, and `G` is finite, then `G` has a presentation whose Cayley complex embeds in
the `2`-sphere. -/
-- Proof sketch: choose the Section `5` presentation of `G` with strictly quadratic root system
-- and cyclic star graph. The local cyclicity makes the Cayley complex into a connected
-- simply-connected `2`-manifold without boundary. Finite `G` gives finitely many face orbits, so
-- the resulting surface is compact; classification of simply-connected surfaces then identifies it
-- with the sphere.
theorem exists_spherical_cayley_presentation
    (hG : IsFGroup G ∨ IsCountableFreeProductOfCyclicGroups G)
    (hfin : Finite G) :
    ∃ (X : Type v) (R : Set (FreeGroup X)) (C : TwoComplex)
      (coords : CayleyComplex.Coordinates.PresentationCoordinates C R)
      (e : PresentedGroup R ≃* G), C.EmbedsInSphere := sorry

/-- Proposition 3-5-6 (2): if `G` is either an `F`-group or a free product of at most countably
many cyclic groups, and `G` is infinite, then `G` has a presentation whose Cayley complex embeds
in the plane. -/
-- Proof sketch: use the same Section `5` presentation to obtain a connected simply-connected
-- surface without boundary. Infinite `G` forces the Cayley complex to be noncompact, and the
-- increasing-disc exhaustion from the textbook rules out the sphere. The remaining simply
-- connected surface is the plane.
theorem exists_planar_cayley_presentation
    (hG : IsFGroup G ∨ IsCountableFreeProductOfCyclicGroups G)
    (hinf : Infinite G) :
    ∃ (X : Type v) (R : Set (FreeGroup X)) (C : TwoComplex)
      (coords : CayleyComplex.Coordinates.PresentationCoordinates C R)
      (e : PresentedGroup R ≃* G), C.EmbedsInPlane := sorry

end Proposition356

/-! ### Lemma_3_5_7 (from Items/Chap03) -/
import CombinatorialGroupTheory_Magnus_2004.Items.Chap01.SignedLetter
import CombinatorialGroupTheory_Magnus_2004.Items.Chap02.Definition_2_1_4
import CombinatorialGroupTheory_Magnus_2004.Items.Chap03.Definition_3_2_3
import CombinatorialGroupTheory_Magnus_2004.Items.Chap03.Lemma_3_3_8
import CombinatorialGroupTheory_Magnus_2004.Items.Chap03.Proposition_3_4_1

universe u

set_option autoImplicit false

namespace GroupPresentation

-- Layer triage:
-- `source-facing`: the word-metric balls around `1` in the Cayley graph of a presentation
-- `(X; R)`, and the consequence that effective finite construction of all such balls yields a
-- solution to the word problem.
-- `core/canonical`: `PresentedGroup R` is mathlib's owner for the group presented by `R`,
-- `HasSolvableWordProblem R` is the chapter owner predicate for decidability of the word problem,
-- `cayleyOneComplex R` below is the intrinsic Cayley `1`-skeleton of the presentation, and
-- `OneComplex.Subcomplex` is the chapter owner for the ball `Bₙ(C, 1)` as a genuine `1`-skeleton.
-- `bridge/view`: `wordMetricBallSubcomplex R n` is the source-facing ball inside the ambient
-- Cayley `1`-skeleton, while `WordMetricBall R n` is the derived `1`-complex carried by that
-- subcomplex.
-- Domain sampling:
-- 1. `PresentedGroup R` is mathlib's owner abstraction for the group with presentation `(X; R)`.
-- 2. `HasSolvableWordProblem R` from Definition `2-1-4` is the project owner predicate for the
--    conclusion of the lemma.
-- 3. `OneComplex.Subcomplex` from Lemma `3-3-8` is the chapter owner for intrinsic `1`-skeleton
--    subobjects, so the ball should be expressed as a genuine subcomplex of the Cayley graph.
-- 4. `SignedLetter.inv` and `SignedLetter.value` are the chapter owners for orientation reversal
--    and evaluation of a signed generator, so the intrinsic Cayley graph should reuse them rather
--    than keeping parallel local copies.
-- 5. `FreeGroup.norm` is the canonical owner for reduced-word length on `FreeGroup X`, so the
--    textbook metric ball is organized around that owner rather than raw list length.
-- Primitive vs. derived:
-- the primitive data are the relator set `R`, the radius `n`, and the actual Cayley `1`-skeleton;
-- `wordMetricBallSubcomplex R n` is the source-facing ball object, `WordMetricBall R n` is the
-- derived `1`-complex it carries, and the extra effective data needed for Lemma `3-5-7` are only
-- a finite codable structure on the actual vertex carrier of that intrinsic ball together with the
-- computable source-facing evaluation map sending a bounded signed word to its canonical ball
-- vertex. The oriented-edge carrier of the same ball remains derived structure of the owner
-- `1`-complex, not primitive public data of the effective hypothesis.

variable {X : Type u}

/-- The bounded signed words of length at most `n`. -/
abbrev BoundedSignedWord (X : Type u) (n : ℕ) :=
  { L : List (SignedLetter X) // L.length ≤ n }

instance instPrimcodableBoundedSignedWord [Primcodable X] (n : ℕ) :
    Primcodable (BoundedSignedWord X n) := by
  dsimp [BoundedSignedWord]
  exact Primcodable.subtype ((Primrec.nat_le).comp Primrec.list_length (Primrec.const n))

/-- A vertex of the Cayley graph of `(X; R)` lies in the closed word-metric ball of radius `n`
when some representing word has reduced-word length at most `n`. -/
noncomputable def InWordMetricBall (R : Set (FreeGroup X)) (n : ℕ) (g : PresentedGroup R) : Prop :=
  by
    classical
    exact ∃ w : FreeGroup X, PresentedGroup.mk R w = g ∧ FreeGroup.norm w ≤ n

/-- The intrinsic Cayley `1`-skeleton of the presentation `(X; R)`. -/
def cayleyOneComplex (R : Set (FreeGroup X)) : OneComplex where
  Vertex := PresentedGroup R
  Edge := PresentedGroup R × SignedLetter X
  initial := Prod.fst
  terminal := fun e ↦ e.1 * SignedLetter.value PresentedGroup.of e.2
  edgeInv := fun e ↦ (e.1 * SignedLetter.value PresentedGroup.of e.2, e.2⁻¹)
  edgeInv_involutive := by
    rintro ⟨g, letter⟩
    rcases letter with ⟨x, b⟩
    cases b <;> ext <;> simp [mul_assoc]
  edgeInv_ne := by
    intro e h
    rcases e with ⟨g, x, b⟩
    have hletter : (x, b)⁻¹ = (x, b) := congrArg Prod.snd h
    cases b <;> simp at hletter
  initial_edgeInv := by
    intro e
    rfl

/-- The signed-generator word read along a path in the intrinsic Cayley `1`-skeleton of the
presentation `(X; R)`. -/
def cayleyPathLabel (R : Set (FreeGroup X)) {a b : cayleyOneComplex R} (p : Quiver.Path a b) :
    List (SignedLetter X) :=
  (Quiver.Path.edgeList p).map fun e ↦ e.hom.1.2

/-- Membership in a smaller word ball implies membership in every larger one. -/
theorem inWordMetricBall_mono (R : Set (FreeGroup X)) {m n : ℕ} (hmn : m ≤ n)
    {g : PresentedGroup R} (hg : InWordMetricBall R m g) :
    InWordMetricBall R n g := by
  rcases hg with ⟨w, rfl, hw⟩
  exact ⟨w, rfl, hw.trans hmn⟩

/-- The radius-`n` word ball `Bₙ(C, 1)` as a genuine subcomplex of the intrinsic Cayley
`1`-skeleton. -/
def wordMetricBallSubcomplex (R : Set (FreeGroup X)) (n : ℕ) :
    OneComplex.Subcomplex (cayleyOneComplex R) where
  vertexSet := InWordMetricBall R n
  edgeSet := { e | InWordMetricBall R n ((cayleyOneComplex R).initial e) ∧
    InWordMetricBall R n ((cayleyOneComplex R).terminal e) }
  initial_mem := fun h ↦ h.1
  terminal_mem := fun h ↦ h.2
  edgeInv_mem := by
    intro e h
    rcases h with ⟨hinitial, hterminal⟩
    constructor
    · simpa [cayleyOneComplex] using hterminal
    · rcases e with ⟨g, letter⟩
      rcases letter with ⟨x, b⟩
      cases b <;> simpa [cayleyOneComplex, mul_assoc] using hinitial

/-- The intrinsic `1`-skeleton carried by the closed radius-`n` word ball `Bₙ(C, 1)`. -/
abbrev WordMetricBall (R : Set (FreeGroup X)) (n : ℕ) :=
  (wordMetricBallSubcomplex R n).toOneComplex

/-- The identity element of a presented group lies in every closed word-metric ball. -/
-- Proof sketch: represent `1` by the empty word in `FreeGroup X`, whose reduced-word length is
-- `0`.
theorem one_mem_inWordMetricBall (R : Set (FreeGroup X)) (n : ℕ) :
    InWordMetricBall R n 1 := by
  classical
  refine ⟨1, rfl, ?_⟩
  simp

/-- The quotient image of a signed word lies in the word ball of radius equal to its length. -/
-- Proof sketch: use the word itself as the witnessing representative.
theorem mk_mem_inWordMetricBall (R : Set (FreeGroup X)) (L : List (SignedLetter X)) :
    InWordMetricBall R L.length (PresentedGroup.mk R (FreeGroup.mk L)) := by
  classical
  refine ⟨FreeGroup.mk L, rfl, ?_⟩
  exact (show FreeGroup.norm (FreeGroup.mk L) ≤ L.length from FreeGroup.norm_mk_le)

/-- A bounded signed word determines canonically a vertex of the corresponding radius word ball.
-/
def boundedSignedWordVertex (R : Set (FreeGroup X)) {n : ℕ} :
    BoundedSignedWord X n → WordMetricBall R n
  | ⟨L, hL⟩ =>
      ⟨PresentedGroup.mk R (FreeGroup.mk L),
        inWordMetricBall_mono R hL (mk_mem_inWordMetricBall R L)⟩

@[simp] theorem boundedSignedWordVertex_val (R : Set (FreeGroup X)) {n : ℕ}
    (L : BoundedSignedWord X n) :
    (boundedSignedWordVertex R L).1 =
      PresentedGroup.mk R (FreeGroup.mk L.1) := by
  cases L
  rfl

/-- A radius-`n` word ball is finite and effectively constructible for Lemma `3-5-7` when its
intrinsic vertex type is finite and effectively codable, and the canonical source-facing map
`boundedSignedWordVertex` from bounded signed words to ball vertices is computable. The ambient
`1`-skeleton data of the same ball already come from the owner object `WordMetricBall R n`, so the
effective hypothesis does not repackage oriented-edge data as primitive public fields. -/
def HasFiniteConstructibleWordMetricBall [Primcodable X] (R : Set (FreeGroup X)) (n : ℕ) : Prop :=
  ∃ (_ : Fintype (WordMetricBall R n)) (_ : Primcodable (WordMetricBall R n)),
    Computable (boundedSignedWordVertex R : BoundedSignedWord X n → WordMetricBall R n)

section

variable [Primcodable X]

/-- Lemma 3-5-7: if every ball `Bₙ(C, 1)` in the Cayley graph of the presentation `(X; R)` has
finite, effectively constructible vertex set, then the presentation has solvable word problem. In
the owner formulation, each intrinsic ball `WordMetricBall R n` is already an actual `1`-complex,
and the effective hypothesis supplies only the vertex-side data used by the word-problem argument:
a finite codable structure on the genuine ball vertices together with the computable source-facing
evaluation map from bounded signed words into that intrinsic ball. -/
-- Proof sketch: on an input signed word `L`, work in the finite model of the radius-`L.length`
-- ball. Compare the canonical ball vertex of `L` with the canonical base vertex `1` inside that
-- finite ball. Since both points already live in the actual ball `1`-skeleton, equality of those
-- ball vertices is exactly equality of their images in `PresentedGroup R`, so `L` represents `1`
-- precisely when those two vertices agree.
theorem hasSolvableWordProblem_of_finite_effective_wordMetricBalls
    (R : Set (FreeGroup X))
    (hball : ∀ n, HasFiniteConstructibleWordMetricBall R n) :
    HasSolvableWordProblem R := sorry

end

end GroupPresentation

/-! ### Proposition_3_5_9 (from Items/Chap03) -/
universe u

open Quiver.Path

set_option autoImplicit false

namespace CayleyComplex.Coordinates

variable {X : Type u} {R : Set (FreeGroup X)} {C : TwoComplex}

/-- The canonical sign-sensitive map from the intrinsic Cayley graph of `(X; R)` to the chosen
actual Cayley `1`-skeleton. The coordinate formulas for positive and negative letters are derived
API of this owner map, rather than primitive public data in downstream theorems. -/
def fromIntrinsicCayley (coords : PresentationCoordinates C R) :
    OneComplex.Hom (GroupPresentation.cayleyOneComplex R) C.skeleton where
  toVertex := coords.vertexEquiv.symm
  toEdge := coords.edgeEquiv.symm
  map_initial := by
    intro e
    sorry
  map_terminal := by
    intro e
    sorry
  map_edgeInv := by
    intro e
    sorry

@[simp] theorem fromIntrinsicCayley_toVertex (coords : PresentationCoordinates C R)
    (g : PresentedGroup R) :
    (fromIntrinsicCayley coords).toVertex g = coords.vertexEquiv.symm g :=
  rfl

@[simp] theorem fromIntrinsicCayley_toEdge (coords : PresentationCoordinates C R)
    (e : (GroupPresentation.cayleyOneComplex R).Edge) :
    (fromIntrinsicCayley coords).toEdge e = coords.edgeEquiv.symm e :=
  rfl

/-- The signed-generator word read along a path in the chosen actual Cayley `1`-skeleton. -/
def pathLabel (coords : PresentationCoordinates C R) {a b : C.skeleton} :
    Quiver.Path a b → List (SignedLetter X)
  | .nil => []
  | .cons p e => pathLabel coords p ++ [(coords.edgeEquiv e.1).2]

@[simp] theorem pathLabel_nil (coords : PresentationCoordinates C R) (a : C.skeleton) :
    pathLabel coords (Quiver.Path.nil : Quiver.Path a a) = [] :=
  rfl

@[simp] theorem pathLabel_cons (coords : PresentationCoordinates C R) {a b c : C.skeleton}
    (p : Quiver.Path a b) (e : b ⟶ c) :
    pathLabel coords (.cons p e) = pathLabel coords p ++ [(coords.edgeEquiv e.1).2] :=
  rfl

/-- The signed-generator boundary word read directly from an actual Cayley loop. -/
def boundaryLabel (coords : PresentationCoordinates C R) (p : Loop C.skeleton) :
    List (SignedLetter X) :=
  pathLabel coords p.2

/-- Transporting an intrinsic Cayley path into the chosen actual Cayley coordinates preserves its
signed-generator label word exactly. -/
@[simp] theorem pathLabel_fromIntrinsicCayley_mapPath (coords : PresentationCoordinates C R)
    {a b : GroupPresentation.cayleyOneComplex R} (p : Quiver.Path a b) :
    pathLabel coords ((fromIntrinsicCayley coords).mapPath p) =
      GroupPresentation.cayleyPathLabel R p := by
  induction p with
  | nil =>
      rfl
  | cons p e ih =>
      simpa [pathLabel, GroupPresentation.cayleyPathLabel, Quiver.Path.edgeList] using
        And.intro ih <| by
          change (coords.edgeEquiv ((fromIntrinsicCayley coords).toEdge e.1)).2 = e.1.2
          simp [fromIntrinsicCayley]

/-- Transporting an intrinsic Cayley loop into the chosen actual Cayley coordinates preserves its
boundary word exactly. -/
@[simp] theorem boundaryLabel_fromIntrinsicCayley_mapLoop (coords : PresentationCoordinates C R)
    (p : Loop (GroupPresentation.cayleyOneComplex R)) :
    boundaryLabel coords ((fromIntrinsicCayley coords).mapLoop p) =
      GroupPresentation.cayleyPathLabel R p.2 :=
  pathLabel_fromIntrinsicCayley_mapPath coords p.2

/-- The actual radius-`n` word ball in the chosen Cayley `1`-skeleton, obtained by transporting
the intrinsic ball along the Cayley coordinates. -/
def wordMetricBallSubcomplex (coords : PresentationCoordinates C R) (n : ℕ) :
    OneComplex.Subcomplex C.skeleton where
  vertexSet := fun v ↦ GroupPresentation.InWordMetricBall R n (coords.vertexEquiv v)
  edgeSet := fun e ↦
    GroupPresentation.InWordMetricBall R n (coords.vertexEquiv (C.skeleton.initial e)) ∧
      GroupPresentation.InWordMetricBall R n (coords.vertexEquiv (C.skeleton.terminal e))
  initial_mem := by
    intro e he
    exact he.1
  terminal_mem := by
    intro e he
    exact he.2
  edgeInv_mem := by
    intro e he
    constructor
    · convert he.2 using 1
      exact congrArg coords.vertexEquiv (C.skeleton.initial_edgeInv e)
    · convert he.1 using 1
      exact congrArg coords.vertexEquiv (C.skeleton.terminal_edgeInv e)

@[simp] theorem mem_wordMetricBallSubcomplex_vertex (coords : PresentationCoordinates C R)
    (n : ℕ) (v : C.skeleton) :
    v ∈ (wordMetricBallSubcomplex coords n).vertexSet ↔
      GroupPresentation.InWordMetricBall R n (coords.vertexEquiv v) :=
  Iff.rfl

@[simp] theorem mem_wordMetricBallSubcomplex_edge (coords : PresentationCoordinates C R)
    (n : ℕ) (e : C.skeleton.Edge) :
    e ∈ (wordMetricBallSubcomplex coords n).edgeSet ↔
      GroupPresentation.InWordMetricBall R n (coords.vertexEquiv (C.skeleton.initial e)) ∧
        GroupPresentation.InWordMetricBall R n (coords.vertexEquiv (C.skeleton.terminal e)) :=
  Iff.rfl

/-- A based loop lies in the radius-`n` word ball when every vertex visited by the loop is
represented by a word of length at most `n`. -/
def LoopInWordMetricBall (coords : PresentationCoordinates C R) (n : ℕ)
    (p : Loop C.skeleton) : Prop :=
  ∀ v ∈ p.2.vertices, v ∈ (wordMetricBallSubcomplex coords n).vertexSet

/-- The constant loop at a vertex already lying in the radius-`n` ball also lies in that ball. -/
-- Proof sketch: the empty loop visits only its basepoint, so the given ball condition on that
-- basepoint is exactly the required statement.
theorem nil_loopInWordMetricBall (coords : PresentationCoordinates C R) (n : ℕ) (a : C.skeleton)
    (ha : a ∈ (wordMetricBallSubcomplex coords n).vertexSet) :
    LoopInWordMetricBall coords n ⟨a, Quiver.Path.nil⟩ := sorry

/-- Two loops at the same basepoint are `2`-equivalent within the radius-`n` word ball when they
are joined by a finite chain of elementary `2`-reductions whose endpoints stay inside that same
ball at every step. -/
def PathTwoEquivWithinWordMetricBall (coords : PresentationCoordinates C R) (n : ℕ)
    {a : C.skeleton} (p q : Quiver.Path a a) : Prop :=
  Relation.EqvGen
    (fun r s : Quiver.Path a a ↦
      C.path_two_reduction_step r s ∧
        LoopInWordMetricBall coords n ⟨a, r⟩ ∧
        LoopInWordMetricBall coords n ⟨a, s⟩)
    p q

/-- A loop is `2`-equivalent to itself within a fixed word ball as soon as it lies in that ball.
-/
-- Proof sketch: use reflexivity of `Relation.EqvGen`.
theorem pathTwoEquivWithinWordMetricBall_refl (coords : PresentationCoordinates C R) (n : ℕ)
    {a : C.skeleton} (p : Quiver.Path a a) (hp : LoopInWordMetricBall coords n ⟨a, p⟩) :
    PathTwoEquivWithinWordMetricBall coords n p p := sorry

/-- A Cayley complex satisfies the maximum principle when every null-homotopic loop contained in a
word ball contracts to the empty loop through elementary `2`-reductions that remain inside the
same word ball. -/
def SatisfiesMaximumPrinciple (coords : PresentationCoordinates C R) : Prop :=
  ∀ (n : ℕ) (a : C.skeleton) (p : Quiver.Path a a),
    LoopInWordMetricBall coords n ⟨a, p⟩ →
      C.path_two_equiv p (Quiver.Path.nil : Quiver.Path a a) →
      PathTwoEquivWithinWordMetricBall coords n p (Quiver.Path.nil : Quiver.Path a a)

/-- Under the maximum principle, any null-homotopic loop contained in a fixed word ball contracts
to the empty loop inside that same ball. -/
-- Proof sketch: this is exactly the defining clause of
-- `SatisfiesMaximumPrinciple`.
theorem pathTwoEquivWithinWordMetricBall_of_maximumPrinciple
    (coords : PresentationCoordinates C R) (hmax : SatisfiesMaximumPrinciple coords) (n : ℕ)
    (a : C.skeleton) (p : Quiver.Path a a) (hp : LoopInWordMetricBall coords n ⟨a, p⟩)
    (hnull : C.path_two_equiv p (Quiver.Path.nil : Quiver.Path a a)) :
    PathTwoEquivWithinWordMetricBall coords n p (Quiver.Path.nil : Quiver.Path a a) := sorry

variable [Primcodable X] [Finite X]

/-- Proposition 3-5-9: if the Cayley complex of a finite presentation `(X; R)` satisfies the
maximum principle, then the presentation has solvable word problem. -/
-- Proof sketch: for each radius `n`, the maximum principle turns any null-homotopic loop whose
-- vertices lie in the radius-`n` word ball into a contraction that stays inside the same finite
-- ball. The bounded `2`-equivalence quotient of that finite ball is therefore finite and
-- constructible, so Lemma `3-5-7` applies to decide whether a word of length at most `n`
-- represents `1` in the presented group.
theorem hasSolvableWordProblem_of_maximumPrinciple
    (coords : PresentationCoordinates C R) (hR : Set.Finite R)
    (hmax : SatisfiesMaximumPrinciple coords) :
    GroupPresentation.HasSolvableWordProblem R := sorry

end CayleyComplex.Coordinates
