import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_7_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_1_2

open CategoryTheory
open scoped unitInterval

universe u w

-- Semantic recall: `lean_leansearch` surfaced mathlib's canonical loop-space owner, and this
-- project already formalizes the suspension-loop adjunction by `suspensionLoopAdjunctionUnitPath`
-- and `Ω`. The source definition is therefore stated directly on the local
-- `Prespectrum` owner via the explicit adjoint structure maps.

/-- The degree-`n` structure map of a prespectrum sends the suspension basepoint to the basepoint
of `T (n + 1)`. -/
theorem adjointStructureMapPath_cast_eq (T : Prespectrum.{u, w}) (n : ℕ) :
    (T (n + 1)).point =
      CategoryTheory.ConcreteCategory.hom (PointedCompactlyGenerated.Hom.hom (T.sigma n))
        (reducedSuspensionPoint (T n)) := by
  simpa using (PointedCompactlyGenerated.Hom.map_point (T.sigma n)).symm

/-- The image of the suspension-loop unit meridian under the degree-`n` structure map of a
prespectrum, viewed as a loop in `T (n + 1)`. -/
def adjointStructureMapPath (T : Prespectrum.{u, w}) (n : ℕ) (x : (T n).toCompactlyGenerated) :
    Path (T (n + 1)).point (T (n + 1)).point :=
  (((suspensionLoopAdjunctionUnitPath (T n) x).map
      (PointedCompactlyGenerated.Hom.hom (T.sigma n)).hom.hom.continuous).cast
    (show (T (n + 1)).point =
        CategoryTheory.ConcreteCategory.hom (PointedCompactlyGenerated.Hom.hom (T.sigma n))
          (reducedSuspensionPoint (T n)) from
      adjointStructureMapPath_cast_eq T n)
    (show (T (n + 1)).point =
        CategoryTheory.ConcreteCategory.hom (PointedCompactlyGenerated.Hom.hom (T.sigma n))
          (reducedSuspensionPoint (T n)) from
      adjointStructureMapPath_cast_eq T n))

/-- Helper for Definition 22.2.5: `adjointStructureMapPath T n x` is the cast of the mapped
suspension-loop unit meridian. -/
theorem adjointStructureMapPath_eq
    (T : Prespectrum.{u, w}) (n : ℕ) (x : (T n).toCompactlyGenerated) :
    adjointStructureMapPath T n x =
      (((suspensionLoopAdjunctionUnitPath (T n) x).map
          (PointedCompactlyGenerated.Hom.hom (T.sigma n)).hom.hom.continuous).cast
        (show (T (n + 1)).point =
            CategoryTheory.ConcreteCategory.hom (PointedCompactlyGenerated.Hom.hom (T.sigma n))
              (reducedSuspensionPoint (T n)) from
          adjointStructureMapPath_cast_eq T n)
        (show (T (n + 1)).point =
            CategoryTheory.ConcreteCategory.hom (PointedCompactlyGenerated.Hom.hom (T.sigma n))
              (reducedSuspensionPoint (T n)) from
          adjointStructureMapPath_cast_eq T n)) := by
  rfl

/-- Helper for Definition 22.2.5: evaluating the adjoint structure-map path applies the degree-`n`
structure map to the suspension meridian `(x, t)`. -/
@[simp] theorem adjointStructureMapPath_apply
    (T : Prespectrum.{u, w}) (n : ℕ) (x : (T n).toCompactlyGenerated) (t : I) :
    adjointStructureMapPath T n x t =
      CategoryTheory.ConcreteCategory.hom (PointedCompactlyGenerated.Hom.hom (T.sigma n))
        (reducedSuspensionMk (T n) (x, t)) := by
  -- Unfold the casted mapped path to its pointwise evaluation formula.
  rw [adjointStructureMapPath_eq]
  rfl

/-- Helper for Definition 22.2.5: a continuous map from a compact Hausdorff source remains
continuous after replacing the codomain by its compactly generated topology. -/
private theorem continuousCompHausToCompactlyGenerated
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {Y : Type w} [TopologicalSpace Y] {f : K → Y} (hf : Continuous f) :
    @Continuous K Y ‹TopologicalSpace K› (TopologicalSpace.compactlyGenerated.{u, w} Y) f := by
  let F : (Σ (j : (S : CompHaus.{u}) × C(S, Y)), j.fst) → Y := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{u}) × C(S, Y) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-source map is one of the generators for the compactly generated topology.
  have hgenerator :
      ∀ j : (S : CompHaus.{u}) × C(S, Y),
        @Continuous j.fst Y inferInstance (TopologicalSpace.compactlyGenerated.{u, w} Y)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  simpa [F, i] using hgenerator i

/-- Helper for Definition 22.2.5: a continuous map from a `UCompactlyGeneratedSpace` domain
remains continuous after replacing the codomain by its compactly generated topology. -/
private theorem continuousToCompactlyGeneratedOfContinuousOfUCompactlyGenerated
    {X : Type w} [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X]
    {Y : Type w} [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) :
    @Continuous X Y ‹TopologicalSpace X› (TopologicalSpace.compactlyGenerated.{u, w} Y) f := by
  -- Test continuity against compact Hausdorff probes into the compactly generated domain.
  exact continuous_from_uCompactlyGeneratedSpace
    (tY := TopologicalSpace.compactlyGenerated.{u, w} Y) f fun S g ↦ by
      simpa [Function.comp] using
        (continuousCompHausToCompactlyGenerated (Y := Y) (f := f ∘ g)
          (hf := hf.comp g.continuous))

/-- The adjoint structure-map path varies continuously with the source point. -/
theorem adjointStructureMapContinuous
    (T : Prespectrum.{u, w}) (n : ℕ) :
    Continuous fun x : (T n).toCompactlyGenerated ↦
      (show (Ω (T (n + 1))).toCompactlyGenerated from adjointStructureMapPath T n x) := by
  -- Route correction: the adjoint family must land in the kified loop topology carried by `Ω`.
  have hraw : Continuous fun x : (T n).toCompactlyGenerated ↦ adjointStructureMapPath T n x := by
    -- First prove continuity for the raw path topology using the uncurry criterion.
    rw [← Path.continuous_uncurry_iff]
    simpa [Function.uncurry, adjointStructureMapPath_apply] using
      (PointedCompactlyGenerated.Hom.hom (T.sigma n)).hom.hom.continuous.comp
        (continuous_reducedSuspensionMk (T n))
  -- Then upgrade the codomain topology to the compactly generated loop-space topology.
  exact continuousToCompactlyGeneratedOfContinuousOfUCompactlyGenerated
    (Y := Path (T (n + 1)).point (T (n + 1)).point) hraw

/-- The continuous map underlying the adjoint degree-`n` structure map `T n ⟶ Ω T (n + 1)`. -/
def adjointStructureMapContinuousMap (T : Prespectrum.{u, w}) (n : ℕ) :
    C((T n).toCompactlyGenerated, (Ω (T (n + 1))).toCompactlyGenerated) :=
  ⟨fun x ↦ show (Ω (T (n + 1))).toCompactlyGenerated from adjointStructureMapPath T n x,
    adjointStructureMapContinuous T n⟩

/-- The adjoint structure-map continuous map sends the basepoint of `T n` to the constant loop at
the basepoint of `T (n + 1)`. -/
theorem adjointStructureMapContinuousMap_map_point
    (T : Prespectrum.{u, w}) (n : ℕ) :
    adjointStructureMapContinuousMap T n (T n).point = Path.refl (T (n + 1)).point := by
  -- Compare the two loops pointwise after reducing the adjoint path to the meridian formula.
  change adjointStructureMapPath T n (T n).point = Path.refl (T (n + 1)).point
  ext t
  rw [adjointStructureMapPath_apply]
  simpa using (adjointStructureMapPath_cast_eq T n).symm

/-- The adjoint degree-`n` structure map of a prespectrum as a based map `T n ⟶ Ω T (n + 1)`. -/
theorem adjointStructureMap_w (T : Prespectrum.{u, w}) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (T n).hom
        (ConcreteCategory.ofHom (adjointStructureMapContinuousMap T n)) =
      (Ω (T (n + 1))).hom := by
  -- Both maps from the terminal source pick out the constant loop at the target basepoint.
  ext x
  cases x
  exact adjointStructureMapContinuousMap_map_point T n

/-- The adjoint degree-`n` structure map of a prespectrum as a based map `T n ⟶ Ω T (n + 1)`. -/
def adjointStructureMap (T : Prespectrum.{u, w}) (n : ℕ) :
    T n ⟶ Ω (T (n + 1)) :=
  Under.homMk
    (ConcreteCategory.ofHom (adjointStructureMapContinuousMap T n))
    (adjointStructureMap_w T n)

/-- The underlying `CompactlyGenerated` morphism of `adjointStructureMap T n` is
`ConcreteCategory.ofHom (adjointStructureMapContinuousMap T n)`. -/
@[simp] theorem adjointStructureMap_hom
    (T : Prespectrum.{u, w}) (n : ℕ) :
    PointedCompactlyGenerated.Hom.hom (adjointStructureMap T n) =
      ConcreteCategory.ofHom (adjointStructureMapContinuousMap T n) :=
by
  -- Unpack `Under.homMk`: the based adjoint map stores `adjointStructureMapContinuousMap`.
  rfl

/-- Evaluating the adjoint degree-`n` structure map recovers the explicit adjoint path formula. -/
@[simp] theorem adjointStructureMap_hom_apply
    (T : Prespectrum.{u, w}) (n : ℕ) (x : (T n).toCompactlyGenerated) :
    PointedCompactlyGenerated.Hom.hom (adjointStructureMap T n) x = adjointStructureMapPath T n x :=
by
  -- Evaluate the stored continuous map at `x`.
  change adjointStructureMapContinuousMap T n x = adjointStructureMapPath T n x
  rfl

/-- Definition 22.2.5: an Omega-prespectrum is a prespectrum whose adjoint structure maps
`T n ⟶ Ω T (n + 1)` are weak equivalences. -/
@[mk_iff omegaPrespectrum_iff]
class OmegaPrespectrum (T : Prespectrum.{u, w}) : Prop where
  /-- Each adjoint structure map `T n ⟶ Ω T (n + 1)` is a weak equivalence. -/
  isWeakEquivalence :
    ∀ n : ℕ, IsWeakEquivalence (adjointStructureMapContinuousMap T n)

/-- In an Omega-prespectrum, each adjoint structure map is a weak equivalence. -/
instance isWeakEquivalence_adjointStructureMap
    (T : Prespectrum.{u, w}) [h : OmegaPrespectrum T] (n : ℕ) :
    IsWeakEquivalence (adjointStructureMapContinuousMap T n) :=
  h.isWeakEquivalence n

/-- In an Omega-prespectrum, the underlying continuous map of each based adjoint structure map is a
weak equivalence. -/
instance isWeakEquivalence_adjointStructureMap_hom
    (T : Prespectrum.{u, w}) [OmegaPrespectrum T] (n : ℕ) :
    IsWeakEquivalence
      ((PointedCompactlyGenerated.Hom.hom (adjointStructureMap T n)).hom.hom) := by
  simpa [adjointStructureMap_hom] using
    (show IsWeakEquivalence (adjointStructureMapContinuousMap T n) from inferInstance)
