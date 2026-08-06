import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Lemmas
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap

open scoped ContinuousMap Topology
open CategoryTheory Limits HomotopicalAlgebra

-- Semantic recall: mathlib uses `ContinuousMap.HomotopyEquiv` for homotopy type and
-- `TopCat.CWComplex` for CW-complex structures. Chapter 10 already packages “has the homotopy
-- type of a CW complex” as `∃ Y : TopCat, Nonempty (TopCat.CWComplex Y) ∧ Nonempty (X ≃ₕ Y)`, so
-- this file keeps that source-facing existential shape and adds only a direct companion theorem
-- for the fixed-CW-complex use case.

/-- The subset `X = {0} ∪ {1 / n | n ∈ ℕ+}` of `ℝ` from Problem 10.8.2. -/
def convergentSequenceSubset : Set ℝ :=
  {0} ∪ Set.range fun n : ℕ+ ↦ (1 : ℝ) / n

/-- A point lies in `convergentSequenceSubset` exactly when it is `0` or `1 / n` for some
positive integer `n`. -/
theorem mem_convergentSequenceSubset_iff {x : ℝ} :
    x ∈ convergentSequenceSubset ↔ x = 0 ∨ ∃ n : ℕ+, x = (1 : ℝ) / n := by
  change x ∈ ({0} ∪ Set.range fun n : ℕ+ ↦ (1 : ℝ) / n) ↔
    x = 0 ∨ ∃ n : ℕ+, x = (1 : ℝ) / n
  constructor
  · rintro (rfl | ⟨n, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨n, rfl⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨n, rfl⟩

/-- The space `X = {0} ∪ {1 / n | n ∈ ℕ+}` from Problem 10.8.2, regarded as a subspace of `ℝ`. -/
def convergentSequenceSpace : TopCat :=
  TopCat.of convergentSequenceSubset

/-- Helper for Problem 10.8.2: the distinguished limit point `0 ∈ X`. -/
noncomputable def convergentSequenceZero : convergentSequenceSpace :=
  ⟨0, Or.inl rfl⟩

/-- Helper for Problem 10.8.2: the point `1 / n` of the convergent-sequence space. -/
noncomputable def convergentSequencePoint (n : ℕ+) : convergentSequenceSpace :=
  ⟨(1 : ℝ) / n, Or.inr ⟨n, rfl⟩⟩

/-- Helper for Problem 10.8.2: the nonzero points of `X` indexed by `n : ℕ` as `1 / (n + 1)`. -/
noncomputable def convergentSequencePointNat (n : ℕ) : convergentSequenceSpace :=
  convergentSequencePoint ⟨n + 1, Nat.succ_pos _⟩

/-- Helper for Problem 10.8.2: every point of `X` is either `0` or one of the terms `1 / (n + 1)`.
-/
theorem eq_convergentSequenceZero_or_pointNat (x : convergentSequenceSpace) :
    x = convergentSequenceZero ∨ ∃ n : ℕ, x = convergentSequencePointNat n := by
  -- We reduce membership in the subtype to the explicit description of the subset.
  rcases (mem_convergentSequenceSubset_iff.mp x.2) with h0 | ⟨n, hn⟩
  · left
    apply Subtype.ext
    simpa [convergentSequenceZero] using h0
  · refine Or.inr ⟨n - 1, ?_⟩
    -- Reindex the positive integer `n` as a natural number plus one.
    apply Subtype.ext
    rw [hn]
    simp [convergentSequencePointNat, convergentSequencePoint]

/-- Helper for Problem 10.8.2: the subset `X` is countable. -/
theorem convergentSequenceSubset_countable : convergentSequenceSubset.Countable := by
  -- `X` is a singleton union the range of a sequence.
  simpa [convergentSequenceSubset] using
    (Set.countable_singleton (0 : ℝ)).union (Set.countable_range fun n : ℕ+ ↦ (1 : ℝ) / n)

/-- Helper for Problem 10.8.2: the convergent-sequence subspace is totally disconnected. -/
theorem convergentSequenceSpace_totallyDisconnected :
    TotallyDisconnectedSpace convergentSequenceSpace := by
  -- Countable subsets of metric spaces are totally disconnected, and the subtype inherits this.
  change TotallyDisconnectedSpace convergentSequenceSubset
  rw [totallyDisconnectedSpace_subtype_iff]
  exact Set.Countable.isTotallyDisconnected convergentSequenceSubset_countable

/-- Helper for Problem 10.8.2: every path component in `X` is a singleton. -/
theorem pathComponent_eq_singleton_convergentSequenceSpace (x : convergentSequenceSpace) :
    pathComponent x = {x} := by
  -- Total disconnectedness collapses connected components to singletons, so path components do too.
  let _ : TotallyDisconnectedSpace convergentSequenceSpace :=
    convergentSequenceSpace_totallyDisconnected
  apply Set.Subset.antisymm
  · intro y hy
    have hy' : y ∈ connectedComponent x := pathComponent_subset_component x hy
    simpa [connectedComponent_eq_singleton x] using hy'
  · intro y hy
    simp [Set.mem_singleton_iff.mp hy]

/-- Helper for Problem 10.8.2: the points `1 / (n + 1)` are pairwise distinct in `X`. -/
theorem convergentSequencePointNat_injective :
    Function.Injective convergentSequencePointNat := by
  intro m n h
  have hval :
      ((1 : ℝ) / (m + 1) : ℝ) = ((1 : ℝ) / (n + 1) : ℝ) := by
    simpa [convergentSequencePointNat, convergentSequencePoint] using congrArg Subtype.val h
  have hcast : ((m + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := by
    exact inv_injective (by simpa [one_div] using hval)
  exact Nat.succ.inj (Nat.cast_inj.mp hcast)

/-- Helper for Problem 10.8.2: the path-component classes of `1 / (n + 1)` are pairwise distinct.
-/
theorem zerothHomotopy_convergentSequencePointNat_injective :
    Function.Injective fun n : ℕ ↦
      (⟦convergentSequencePointNat n⟧ : ZerothHomotopy convergentSequenceSpace) := by
  intro m n h
  have hjoined : Joined (convergentSequencePointNat m) (convergentSequencePointNat n) :=
    Quotient.exact h
  have hmemb :
      convergentSequencePointNat n ∈ pathComponent (convergentSequencePointNat m) := hjoined
  have hEq :
      convergentSequencePointNat n = convergentSequencePointNat m := by
    simpa [pathComponent_eq_singleton_convergentSequenceSpace (convergentSequencePointNat m)] using
      hmemb
  exact convergentSequencePointNat_injective hEq.symm

/-- Helper for Problem 10.8.2: the sequence `1 / (n + 1)` converges to `0` in the subspace `X`. -/
theorem tendsto_convergentSequencePointNat :
    Filter.Tendsto convergentSequencePointNat Filter.atTop (𝓝 convergentSequenceZero) := by
  -- We push convergence down to the ambient real line, where the standard limit theorem applies.
  refine (tendsto_subtype_rng.2 ?_)
  simpa [convergentSequencePointNat, convergentSequencePoint, convergentSequenceZero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat :
      Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) Filter.atTop (𝓝 0))

/-- Helper for Problem 10.8.2: an eventually constant sequence has finite range. -/
theorem finiteRange_of_eventually_constant {α : Type*} (s : ℕ → α) (c : α)
    (h : ∃ N : ℕ, ∀ n ≥ N, s n = c) :
    (Set.range s).Finite := by
  rcases h with ⟨N, hN⟩
  -- Split the range into the finite initial segment and the eventual constant value.
  refine ((Set.finite_range fun n : Fin N ↦ s n).insert c).subset ?_
  rintro y ⟨n, rfl⟩
  by_cases hn : n < N
  · exact Or.inr ⟨⟨n, hn⟩, rfl⟩
  · exact Or.inl (hN n (le_of_not_gt hn))

/-- Helper for Problem 10.8.2: a continuous map from `X` to a discrete space is eventually constant
on the tail `1 / (n + 1) → 0`. -/
theorem eventuallyEq_zero_of_continuousMapFromConvergentSequenceSpace
    {β : Type*} [TopologicalSpace β] [DiscreteTopology β]
    (f : C(convergentSequenceSpace, β)) :
    ∃ N : ℕ, ∀ n ≥ N, f (convergentSequencePointNat n) = f convergentSequenceZero := by
  -- Continuity transfers the convergence `1 / (n + 1) → 0` to the discrete codomain.
  have hTendsto :
      Filter.Tendsto (fun n : ℕ ↦ f (convergentSequencePointNat n)) Filter.atTop
        (𝓝 (f convergentSequenceZero)) :=
    f.continuous.continuousAt.tendsto.comp tendsto_convergentSequencePointNat
  have hSingleton : {f convergentSequenceZero} ∈ 𝓝 (f convergentSequenceZero) :=
    (discreteTopology_iff_singleton_mem_nhds.mp ‹DiscreteTopology β›) _
  have hEventually :
      ∀ᶠ n : ℕ in Filter.atTop, f (convergentSequencePointNat n) = f convergentSequenceZero := by
    filter_upwards [hTendsto hSingleton] with n hn
    simpa using hn
  simpa [Filter.eventually_atTop] using hEventually

/-- Helper for Problem 10.8.2: every continuous map from `X` to a discrete space has finite image.
-/
theorem finiteRange_of_continuousMapFromConvergentSequenceSpace
    {β : Type*} [TopologicalSpace β] [DiscreteTopology β] (f : C(convergentSequenceSpace, β)) :
    (Set.range f).Finite := by
  -- First show that the sequence of nonzero points contributes only finitely many values.
  have hPointRange :
      (Set.range fun n : ℕ ↦ f (convergentSequencePointNat n)).Finite :=
    finiteRange_of_eventually_constant
      (fun n : ℕ ↦ f (convergentSequencePointNat n))
      (f convergentSequenceZero)
      (eventuallyEq_zero_of_continuousMapFromConvergentSequenceSpace f)
  -- Then every point of `X` is either `0` or one of those nonzero terms.
  refine (hPointRange.insert (f convergentSequenceZero)).subset ?_
  rintro y ⟨x, rfl⟩
  rcases eq_convergentSequenceZero_or_pointNat x with rfl | ⟨n, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨n, rfl⟩

/-- Helper for Problem 10.8.2: a continuous map sends joined points to joined points. -/
theorem joined_map_of_continuous
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} {x y : X} (h : Joined x y) :
    Joined (f x) (f y) := by
  -- We upgrade the path in the source to a path in the image.
  exact (JoinedIn.map (joinedIn_univ.mpr h) f.continuous).joined

/-- Helper for Problem 10.8.2: the quotient map to path components, composed with a continuous map.
-/
def continuousToZerothHomotopy
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    C(X, ZerothHomotopy Y) where
  toFun x := ⟦f x⟧
  continuous_toFun := continuous_quotient_mk'.comp f.continuous

/-- Helper for Problem 10.8.2: a homotopy joins the pointwise values of its endpoint maps. -/
theorem joined_apply_of_homotopy
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : f.Homotopic g) (x : X) :
    Joined (f x) (g x) := by
  -- The homotopy line at a fixed point is the required path.
  rcases H with ⟨H⟩
  refine ⟨Path.mk ⟨fun t ↦ H (t, x), ?_⟩ ?_ ?_⟩
  · fun_prop
  · simp [H.apply_zero x]
  · simp [H.apply_one x]

/-- Helper for Problem 10.8.2: a homotopy equivalence induces an equivalence on path-component
quotients. -/
def homotopyEquivZerothHomotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    ZerothHomotopy X ≃ ZerothHomotopy Y where
  toFun := zerothHomotopyMap e.toFun
  invFun := zerothHomotopyMap e.invFun
  left_inv := by
    -- The homotopy inverse data shows that the induced maps compose to the identity on classes.
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    change (⟦e.invFun (e.toFun x)⟧ : ZerothHomotopy X) = ⟦x⟧
    exact Quotient.sound (joined_apply_of_homotopy e.left_inv x)
  right_inv := by
    -- The same argument applies on the CW side.
    intro q
    refine Quotient.inductionOn q ?_
    intro y
    change (⟦e.toFun (e.invFun y)⟧ : ZerothHomotopy Y) = ⟦y⟧
    exact Quotient.sound (joined_apply_of_homotopy e.right_inv y)

/-- Helper for Problem 10.8.2: each disk `TopCat.disk n` is locally path connected. -/
theorem disk_locPathConnectedSpace (n : ℕ) : LocPathConnectedSpace (TopCat.disk n) := by
  -- The closed ball model of the disk is convex, hence locally path connected.
  let _ : LocPathConnectedSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).locPathConnectedSpace
  -- The `ULift` wrapper used in `TopCat.disk` preserves the topology up to homeomorphism.
  simpa [TopCat.disk] using
    (Homeomorph.ulift.isOpenEmbedding.locPathConnectedSpace :
      LocPathConnectedSpace (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))

/-- Helper for Problem 10.8.2: a colimit of locally path connected spaces in `TopCat`
is locally path connected. -/
theorem locPathConnectedSpaceOfIsColimit {J : Type*} [Category J] {F : J ⥤ TopCat}
    (c : Cocone F) (hc : IsColimit c) (hF : ∀ j, LocPathConnectedSpace (F.obj j)) :
    LocPathConnectedSpace c.pt := by
  let _ : ∀ j, LocPathConnectedSpace (F.obj j) := hF
  let desc : (Σ j, F.obj j) → c.pt := fun x ↦ c.ι.app x.1 x.2
  have hsurj : Function.Surjective desc := by
    intro x
    obtain ⟨j, y, rfl⟩ :=
      CategoryTheory.Limits.Types.jointly_surjective_of_isColimit
        (F := F ⋙ forget TopCat) (t := (forget TopCat).mapCocone c)
        (isColimitOfPreserves (forget TopCat) hc) x
    exact ⟨⟨j, y⟩, rfl⟩
  have hquot : Topology.IsQuotientMap desc := by
    rw [Topology.isQuotientMap_iff]
    constructor
    · exact hsurj
    · intro U
      -- Openness on the sigma source is checked fiberwise, exactly matching the colimit criterion.
      rw [isOpen_sigma_iff, TopCat.isOpen_iff_of_isColimit _ hc]
      refine forall_congr' fun j ↦ ?_
      change IsOpen ((fun x : F.obj j ↦ desc ⟨j, x⟩) ⁻¹' U) ↔ IsOpen ((c.ι.app j) ⁻¹' U)
      simp [desc]
  -- The colimit is a quotient of the sigma coproduct of the locally path connected stages.
  exact hquot.locPathConnectedSpace

/-- Helper for Problem 10.8.2: attaching locally path connected cells to a locally path connected
space preserves local path connectedness. -/
theorem locPathConnectedSpaceOfAttachCells {α : Type*} {A B : α → TopCat}
    (g : ∀ a, A a ⟶ B a) {X₁ X₂ : TopCat} {f : X₁ ⟶ X₂}
    (c : HomotopicalAlgebra.AttachCells g f) (hX₁ : LocPathConnectedSpace X₁)
    (hB : ∀ a, LocPathConnectedSpace (B a)) : LocPathConnectedSpace X₂ := by
  let _ : LocPathConnectedSpace X₁ := hX₁
  let _ : ∀ a, LocPathConnectedSpace (B a) := hB
  let inlMap : X₁ ⟶ TopCat.of (X₁ ⊕ c.cofan₂.pt) :=
    TopCat.ofHom ⟨Sum.inl, by continuity⟩
  let inrMap : c.cofan₂.pt ⟶ TopCat.of (X₁ ⊕ c.cofan₂.pt) :=
    TopCat.ofHom ⟨Sum.inr, by continuity⟩
  let qLeft : c.cofan₁.pt ⟶ TopCat.of (X₁ ⊕ c.cofan₂.pt) := c.g₁ ≫ inlMap
  let qRight : c.cofan₁.pt ⟶ TopCat.of (X₁ ⊕ c.cofan₂.pt) := c.m ≫ inrMap
  let t : TopCat.of (X₁ ⊕ c.cofan₂.pt) ⟶ X₂ :=
    TopCat.ofHom
      { toFun := Sum.elim f c.g₂
        continuous_toFun := by
          continuity }
  have hcofork :
      CategoryTheory.Limits.IsColimit
        (Cofork.ofπ (f := qLeft) (g := qRight) t
          (by
            simpa [qLeft, qRight, t, inlMap, inrMap] using c.isPushout.w)) := by
    -- The coequalizer on the explicit sum coproduct restates the pushout universal property.
    refine CategoryTheory.Limits.Cofork.IsColimit.mk' _ ?_
    intro s
    let l : X₂ ⟶ s.pt :=
      c.isPushout.desc
        (inlMap ≫ s.π)
        (inrMap ≫ s.π)
        (by
          simpa using s.condition)
    refine ⟨l, ?_, ?_⟩
    · -- The descended map coequalizes the explicit sum map by the pushout equations.
      ext x
      cases x with
      | inl x =>
          exact ConcreteCategory.congr_hom
            (c.isPushout.inl_desc (inlMap ≫ s.π) (inrMap ≫ s.π) (by simpa using s.condition)) x
      | inr x =>
          exact ConcreteCategory.congr_hom
            (c.isPushout.inr_desc (inlMap ≫ s.π) (inrMap ≫ s.π) (by simpa using s.condition)) x
    · intro m hm
      apply c.isPushout.hom_ext
      · have hmInl : f ≫ m = inlMap ≫ s.π := by
          simpa [t, inlMap] using congrArg (fun k ↦ inlMap ≫ k) hm
        have hlInl : f ≫ l = inlMap ≫ s.π :=
          c.isPushout.inl_desc (inlMap ≫ s.π) (inrMap ≫ s.π) (by simpa using s.condition)
        exact hmInl.trans hlInl.symm
      · have hmInr : c.g₂ ≫ m = inrMap ≫ s.π := by
          simpa [t, inrMap] using congrArg (fun k ↦ inrMap ≫ k) hm
        have hlInr : c.g₂ ≫ l = inrMap ≫ s.π :=
          c.isPushout.inr_desc (inlMap ≫ s.π) (inrMap ≫ s.π) (by simpa using s.condition)
        exact hmInr.trans hlInr.symm
  have hcoprod₂ : LocPathConnectedSpace c.cofan₂.pt := by
    -- The cell coproduct is itself a colimit of the locally path connected cell spaces.
    exact locPathConnectedSpaceOfIsColimit c.cofan₂ c.isColimit₂ (fun i ↦ hB (c.π i.as))
  let _ : LocPathConnectedSpace (TopCat.of (X₁ ⊕ c.cofan₂.pt)) := by
    -- The pushout is a quotient of a disjoint union of locally path connected spaces.
    change LocPathConnectedSpace (X₁ ⊕ c.cofan₂.pt)
    infer_instance
  exact (TopCat.isQuotientMap_of_isColimit_cofork _ hcofork).locPathConnectedSpace

/-- Helper for Problem 10.8.2: every skeleton in an abstract CW complex is locally
path connected. -/
theorem cwStage_locPathConnectedSpace {Y : TopCat} (hY : TopCat.CWComplex Y) :
    ∀ n : ℕ, LocPathConnectedSpace (hY.F.obj n)
  | 0 => by
      let e : hY.F.obj 0 ≅ TopCat.of PEmpty :=
        hY.isoBot ≪≫ TopCat.initialIsoPEmpty
      have hEmpty : IsEmpty (hY.F.obj 0) := by
        refine ⟨fun x ↦ ?_⟩
        exact (e.hom x).elim
      -- The initial skeleton is empty, hence trivially locally path connected.
      let _ : LocPathConnectedSpace (hY.F.obj 0) := by
        rw [locPathConnectedSpace_iff_isOpen_pathComponentIn]
        intro x
        exact (hEmpty.false x).elim
      infer_instance
  | n + 1 => by
      have hn : ¬ IsMax n := not_isMax_iff.mpr ⟨n + 1, Nat.lt_succ_self n⟩
      -- The successor skeleton is obtained by attaching `n`-disks to the previous skeleton.
      simpa using
        locPathConnectedSpaceOfAttachCells
          (g := TopCat.RelativeCWComplex.basicCell n) (c := hY.attachCells n hn)
          (cwStage_locPathConnectedSpace hY n) (fun _ ↦ disk_locPathConnectedSpace n)

/-- Helper for Problem 10.8.2: an abstract `TopCat.CWComplex` is locally path connected.

TODO: mathlib currently exposes `TopCat.CWComplex` only through the abstract relative-cell-complex
definition, and `Mathlib/Topology/CWComplex/Abstract/Basic.lean` explicitly notes that there is not
yet an equivalence to the classical CW API. The remaining proof obligation is therefore the
primitive bridge from the abstract CW witness to local path connectedness. -/
theorem locPathConnectedSpace_of_cwComplex {Y : TopCat} (hY : TopCat.CWComplex Y) :
    LocPathConnectedSpace Y := by
  -- Route correction: prove local path connectedness from the abstract CW colimit, not from the
  -- unavailable classical-CW equivalence.
  simpa using
    locPathConnectedSpaceOfIsColimit (c := Cocone.mk Y hY.incl) hY.isColimit
      (cwStage_locPathConnectedSpace hY)

/-- Helper for Problem 10.8.2: a CW complex has discrete path-component quotient.

TODO: prove this from the `TopCat.CWComplex` witness, or replace it with the existing owner lemma if
mathlib exposes the local path connectedness/discrete-π₀ bridge under a different name. At
present, direct typeclass search after installing `hY` as `[TopCat.CWComplex Y]` still fails to
find either `LocPathConnectedSpace Y` or `DiscreteTopology (ZerothHomotopy Y)`. -/
theorem cwComplex_discreteZerothHomotopy {Y : TopCat} (hY : TopCat.CWComplex Y) :
    DiscreteTopology (ZerothHomotopy Y) := by
  -- Route correction: once `Y` is locally path connected, discreteness of `π₀(Y)` is a library
  -- instance.
  let _ : LocPathConnectedSpace Y := locPathConnectedSpace_of_cwComplex hY
  infer_instance

/-- Problem 10.8.2: if `X = {0} ∪ {1 / n | n ∈ ℕ+}` is regarded as a subspace of `ℝ`, then `X`
does not have the homotopy type of a CW complex. -/
theorem convergentSequenceSpace_notHomotopyTypeOfCWComplex :
    ¬ ∃ Y : TopCat, Nonempty (TopCat.CWComplex Y) ∧ Nonempty (convergentSequenceSpace ≃ₕ Y) :=
  by
    rintro ⟨Y, ⟨hY⟩, ⟨e⟩⟩
    -- Route correction: work on the path-component quotient rather than on point-set surjectivity.
    have hDiscrete : DiscreteTopology (ZerothHomotopy Y) := cwComplex_discreteZerothHomotopy hY
    -- The quotient map `X → π₀(Y)` has finite image because `π₀(Y)` is discrete.
    have hFiniteImage :
        (Set.range (continuousToZerothHomotopy e.toFun)).Finite :=
      finiteRange_of_continuousMapFromConvergentSequenceSpace (continuousToZerothHomotopy e.toFun)
    have hSurjRange :
        Set.range (continuousToZerothHomotopy e.toFun) = Set.univ := by
      -- Surjectivity comes from the induced equivalence on path components.
      ext q
      constructor
      · intro _
        simp
      · intro _
        rcases (homotopyEquivZerothHomotopyEquiv e).surjective q with ⟨p, hp⟩
        rcases Quotient.exists_rep p with ⟨x, rfl⟩
        exact ⟨x, by simpa [homotopyEquivZerothHomotopyEquiv, zerothHomotopyMap,
          continuousToZerothHomotopy] using hp⟩
    have hFiniteTargetUniv : (Set.univ : Set (ZerothHomotopy Y)).Finite := by
      simpa [hSurjRange] using hFiniteImage
    have hFiniteSourceUniv : (Set.univ : Set (ZerothHomotopy convergentSequenceSpace)).Finite := by
      -- The homotopy equivalence transports finiteness back to the source quotient.
      refine Set.Finite.preimage (f := homotopyEquivZerothHomotopyEquiv e) ?_ hFiniteTargetUniv
      intro a _ b _ hab
      exact (homotopyEquivZerothHomotopyEquiv e).injective hab
    have hInfiniteSourceRange :
        (Set.range fun n : ℕ ↦
          (⟦convergentSequencePointNat n⟧ : ZerothHomotopy convergentSequenceSpace)).Infinite :=
      Set.infinite_range_of_injective zerothHomotopy_convergentSequencePointNat_injective
    have hFiniteSourceRange :
        (Set.range fun n : ℕ ↦
          (⟦convergentSequencePointNat n⟧ : ZerothHomotopy convergentSequenceSpace)).Finite :=
      hFiniteSourceUniv.subset (by intro x _; simp)
    exact hInfiniteSourceRange.not_finite hFiniteSourceRange

/-- A fixed CW complex cannot be homotopy equivalent to the convergent-sequence space from
Problem 10.8.2. -/
theorem convergentSequenceSpace_notNonempty_homotopyEquiv
    {Y : TopCat} (hY : TopCat.CWComplex Y) :
    ¬ Nonempty (convergentSequenceSpace ≃ₕ Y) := by
  intro hEquiv
  exact convergentSequenceSpace_notHomotopyTypeOfCWComplex ⟨Y, ⟨hY⟩, hEquiv⟩
