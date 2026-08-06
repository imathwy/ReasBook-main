import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Example_5_1_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap

noncomputable section

universe u

open scoped TopCat Topology Topology.Homotopy
open Path.Homotopic.Quotient

/-- Helper for Remark 9.4.13: two generalized loops represent the same path component exactly
when they are homotopic rel boundary. -/
theorem genLoop_homotopic_iff_joined
    {X : Type*} [TopologicalSpace X] {N : Type*} {x : X} {p q : Ω^ N X x} :
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

/-- Helper for Remark 9.4.13: quotienting generalized loops by homotopy identifies `π_q(X, x)`
with the path components of the iterated loop-space owner `Ω^ (Fin q) X x`. -/
abbrev homotopyGroupEquivZerothHomotopyGenLoop
    {X : Type*} [TopologicalSpace X] (q : ℕ) (x : X) :
    π_ q X x ≃ ZerothHomotopy (Ω^ (Fin q) X x) :=
  Quotient.congr (Equiv.refl _) fun _ _ ↦ genLoop_homotopic_iff_joined

/-- Helper for Remark 9.4.13: the Section 9.5 sphere-fiber model identifies `π_q(S^n, x)` with
the path components of the evaluation fiber over `x`. -/
noncomputable def sphereHomotopyGroupEquivSphereBasepointFiberZeroth
    {q n : ℕ} (x : (𝕊 n : TopCat.{u})) :
    π_ q (𝕊 n : TopCat.{u}) x ≃ ZerothHomotopy (sphereBasepointFiber q x) :=
  let e := Classical.choice (sphereBasepointFiber_homeomorphic_iteratedLoopSpace q x)
  -- First rewrite `π_q` as path components of the iterated loop-space owner, then apply the
  -- chosen Section 9.5 homeomorphism.
  (homotopyGroupEquivZerothHomotopyGenLoop q x).trans
    (zerothHomotopyEquivOfHomotopyEquiv e.symm.toHomotopyEquiv)

/-- Helper for Remark 9.4.13: a path between sphere basepoints induces an equivalence on the
corresponding homotopy groups. -/
noncomputable def sphereBasepointFiberZerothEquivOfPath
    {q n : ℕ} {x x' : (𝕊 n : TopCat.{u})} (β : Path x x') :
    ZerothHomotopy (sphereBasepointFiber q x) ≃ ZerothHomotopy (sphereBasepointFiber q x') :=
  by
    letI : CompactSpace (𝕊 n : TopCat.{u}) := by
      change CompactSpace
        (ULift.{u, 0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
      infer_instance
    letI : T2Space (𝕊 n : TopCat.{u}) := by
      change T2Space
        (ULift.{u, 0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
      infer_instance
    letI : WeaklyLocallyCompactSpace (𝕊 n : TopCat.{u}) := inferInstance
    letI : LocallyCompactSpace (𝕊 n : TopCat.{u}) := inferInstance
    letI : CompactlyGeneratedWeakHausdorffSpace.{u, u} (𝕊 n : TopCat.{u}) :=
      instCompactlyGeneratedWeakHausdorffSpaceOfLocallyCompact
    -- Reuse the Section 9.5 transport on the convenient (k-ified) mapping-space owner.
    exact sphereBasepointFiberZerothEquivOfPathClass q (mk β)

/-- Helper for Remark 9.4.13: a path between sphere basepoints induces an equivalence on the
corresponding homotopy groups. -/
noncomputable def sphereHomotopyGroupBasepointChangeEquiv
    {q n : ℕ} {x x' : (𝕊 n : TopCat.{u})} (β : Path x x') :
    π_ q (𝕊 n : TopCat.{u}) x ≃ π_ q (𝕊 n : TopCat.{u}) x' :=
  -- Compare both homotopy groups with the Section 9.5 sphere-fiber owner and transport through
  -- the induced path-class equivalence there.
  (sphereHomotopyGroupEquivSphereBasepointFiberZeroth (q := q) x).trans
    ((sphereBasepointFiberZerothEquivOfPath (q := q) β).trans
      (sphereHomotopyGroupEquivSphereBasepointFiberZeroth (q := q) x').symm)

/-- Helper for Remark 9.4.13: a chosen path to `sphereBasepoint n` identifies the homotopy group
at `x` with the standard-basepoint homotopy group. -/
noncomputable def sphereHomotopyGroupEquivStandardBasepoint
    {q n : ℕ} {x : (𝕊 n : TopCat.{u})}
    (β : Path x (sphereBasepoint n : (𝕊 n : TopCat.{u}))) :
    π_ q (𝕊 n : TopCat.{u}) x ≃
      π_ q (𝕊 n : TopCat.{u}) (sphereBasepoint n : (𝕊 n : TopCat.{u})) :=
  sphereHomotopyGroupBasepointChangeEquiv (q := q) β

/-- Helper for Remark 9.4.13: finiteness at the standard sphere basepoint transports to any
chosen basepoint via a path. -/
theorem sphereHomotopyGroupFiniteOfStandardBasepoint
    {q n : ℕ} (x : (𝕊 n : TopCat.{u}))
    (β : Path x (sphereBasepoint n : (𝕊 n : TopCat.{u})))
    (hbase : Finite (π_ q (𝕊 n : TopCat.{u}) (sphereBasepoint n : (𝕊 n : TopCat.{u})))) :
    Finite (π_ q (𝕊 n : TopCat.{u}) x) := by
  let e := sphereHomotopyGroupEquivStandardBasepoint (q := q) β
  -- Transfer finiteness across the basepoint-change equivalence.
  letI :
      Finite (π_ q (𝕊 n : TopCat.{u}) (sphereBasepoint n : (𝕊 n : TopCat.{u}))) := hbase
  exact Finite.of_injective e e.injective
