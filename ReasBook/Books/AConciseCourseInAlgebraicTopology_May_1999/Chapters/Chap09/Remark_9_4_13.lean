import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Metrizable.ContinuousMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Proposition_2_4_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Example_3_2_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Example_5_1_12
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_4_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Remark_9_4_13.BasepointTransport

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped TopCat Topology Topology.Homotopy unitInterval
open CategoryTheory FundamentalGroupoid FundamentalGroupoidFunctor TopologicalSpace

/-- For sphere targets the raw compact-open mapping space is metrizable (the source sphere is
compact and the target sphere is metrizable), hence it is a valid compactly generated weak
Hausdorff space for the Chapter 7 transport used below. -/
private noncomputable instance sphereMapSpaceCompactlyGeneratedWeakHausdorff
    (q n : ℕ) :
    CompactlyGeneratedWeakHausdorffSpace.{u, u}
      C((𝕊 q : TopCat.{u}), (𝕊 n : TopCat.{u})) := by
  letI : CompactSpace (𝕊 q : TopCat.{u}) := by
    change CompactSpace
      (ULift.{u, 0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1))
    infer_instance
  letI : T2Space (𝕊 q : TopCat.{u}) := by
    change T2Space
      (ULift.{u, 0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (q + 1))) 1))
    infer_instance
  letI : WeaklyLocallyCompactSpace (𝕊 q : TopCat.{u}) := inferInstance
  letI : SigmaCompactSpace (𝕊 q : TopCat.{u}) := inferInstance
  letI : MetrizableSpace (𝕊 n : TopCat.{u}) := by
    change MetrizableSpace
      (ULift.{u, 0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    infer_instance
  letI : MetrizableSpace C((𝕊 q : TopCat.{u}), (𝕊 n : TopCat.{u})) := inferInstance
  letI : WeaklyHausdorffSpace.{u, u}
      C((𝕊 q : TopCat.{u}), (𝕊 n : TopCat.{u})) := inferInstance
  exact instCompactlyGeneratedWeakHausdorffSpaceOfFirstCountable

-- Semantic recall: `HomotopyGroup.Pi` is the canonical owner for `π_ q (𝕊 n) x`; no existing
-- local theorem matching this Serre-style finiteness remark was found, so we record the source as
-- two source-faithful declarations.

/-- Helper for Remark 9.4.13: every point on `𝕊 n` with `n > 1` is connected to the standard
sphere basepoint. -/
private theorem sphereDimensionTwoLeOfOneLt {n : ℕ} (hn : 1 < n) : 2 ≤ n := by
  -- Convert the source-side hypothesis `1 < n` into the path-connectedness threshold `2 ≤ n`.
  omega

/-- Helper for Remark 9.4.13: every point on `𝕊 n` with `n > 1` is connected to the standard
sphere basepoint. -/
noncomputable def spherePathToStandardBasepoint {n : ℕ} (hn : 1 < n)
    (x : (𝕊 n : TopCat.{u})) :
    Path x (sphereBasepoint n : (𝕊 n : TopCat.{u})) :=
  -- Use sphere path-connectedness above dimension one to choose a path to the standard basepoint.
  @PathConnectedSpace.somePath
    (𝕊 n : TopCat.{u})
    _
    (sphere_pathConnectedSpace_of_two_le (sphereDimensionTwoLeOfOneLt hn))
    x
    (sphereBasepoint n : (𝕊 n : TopCat.{u}))

/-- Helper for Remark 9.4.13: Serre's standard-basepoint finiteness theorem for nonexceptional
sphere homotopy groups. -/
theorem standardSphereHomotopyGroupFiniteOfNotExceptional {q n : ℕ}
    (hq : n < q) (hn : 1 < n)
    (h_exception : ¬ ∃ m : ℕ, n = 2 * m ∧ q = 4 * m - 1) :
    Finite (π_ q (𝕊 n : TopCat.{u}) (sphereBasepoint n : (𝕊 n : TopCat.{u}))) := by
  -- TODO: supply the dependency-closed Serre finiteness input at the standard sphere basepoint.
  -- The public finiteness theorem already reduces to this exact source-facing premise.
  let _ := hq
  let _ := hn
  let _ := h_exception
  sorry

/-- Helper for Remark 9.4.13: the executable exceptional base case identifies `π₃(S²)` with
`Multiplicative ℤ × PUnit`. -/
theorem sphereTwoPiThreeMulEquivIntProdPUnit :
    Nonempty
      (π_ 3 (𝕊 2 : TopCat.{u}) (sphereBasepoint 2 : (𝕊 2 : TopCat.{u})) ≃*
        (Multiplicative ℤ × PUnit)) := by
  -- Compare `π₃(S²)` with `π₃(S³)`, then use the standard `π₃(S³) ≃* Multiplicative ℤ`
  -- computation and package the trivial finite factor separately.
  rcases sphereThree_pi_geThree_mulEquiv_sphereTwo.{u, u} 0 with ⟨eSphere⟩
  rcases standardSpherePiSelfMulEquivInt.{u} 3 with ⟨eSelf⟩
  refine ⟨eSphere.symm.trans (eSelf.trans ?_)⟩
  -- The product with the unique group `PUnit` is canonically equivalent to `Multiplicative ℤ`.
  exact (MulEquiv.prodUnique (M := Multiplicative ℤ) (N := PUnit)).symm

/-- Helper for Remark 9.4.13: the exceptional family `S^(2 * n + 2)` lies in dimension above
one, so the general path-to-standard-basepoint helper applies. -/
private theorem exceptionalEvenSphereDimensionOneLt (n : ℕ) : 1 < 2 * n + 2 := by
  -- The exceptional family starts at `S²`, and the dimension only increases with `n`.
  omega

/-- Helper for Remark 9.4.13: the base exceptional case already has the required infinite cyclic
summand, with trivial finite factor. -/
theorem standardExceptionalEvenSphereHomotopyGroupHasIntSummandZero :
    ∃ (T : Type) (_ : CommGroup T) (_ : Finite T),
      Nonempty
        (π_ 3 (𝕊 2 : TopCat.{u}) (sphereBasepoint 2 : (𝕊 2 : TopCat.{u})) ≃*
          (Multiplicative ℤ × T)) := by
  -- Reuse the explicit `PUnit`-valued base-case splitting so only the finite factor data remains
  -- to be packaged.
  refine ⟨PUnit, inferInstance, inferInstance, ?_⟩
  -- The preceding helper already supplies the required equivalence.
  exact sphereTwoPiThreeMulEquivIntProdPUnit

/-- Helper for Remark 9.4.13: the remaining exceptional even spheres should be handled as a
single successor-family Serre input at the standard sphere basepoint. -/
theorem standardExceptionalEvenSphereHomotopyGroupHasIntSummandSucc {n : ℕ} :
    ∃ (T : Type) (_ : CommGroup T) (_ : Finite T),
      Nonempty
        (π_ (4 * (n + 1) + 3) (𝕊 (2 * (n + 1) + 2) : TopCat.{u})
            (sphereBasepoint (2 * (n + 1) + 2) :
              (𝕊 (2 * (n + 1) + 2) : TopCat.{u})) ≃*
          (Multiplicative ℤ × T)) := by
  -- Route correction: isolate the unresolved Serre exceptional input for the successor family so
  -- the public theorem below is just a case split over the already proved base case.
  -- TODO: supply Serre's standard-basepoint exceptional splitting for `S^(2 * (n + 1) + 2)` in
  -- degree `4 * (n + 1) + 3`, independent of the positive-degree basepoint transport.
  sorry

/-- Helper for Remark 9.4.13: any multiplicative equivalence transports an exceptional
`Multiplicative ℤ × T` splitting back to the source group. -/
theorem transportExceptionalSplittingAlongMulEquiv
    {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H)
    (hH :
      ∃ (T : Type) (_ : CommGroup T) (_ : Finite T),
        Nonempty (H ≃* (Multiplicative ℤ × T))) :
    ∃ (T : Type) (_ : CommGroup T) (_ : Finite T),
      Nonempty (G ≃* (Multiplicative ℤ × T)) := by
  -- Unpack the target-side splitting and precompose it with the supplied `MulEquiv`.
  rcases hH with ⟨T, hT, hfinite, ⟨eT⟩⟩
  let _ : CommGroup T := hT
  let _ : Finite T := hfinite
  -- The same finite torsion factor works on the source once the groups are identified.
  exact ⟨T, hT, hfinite, ⟨e.trans eT⟩⟩

/-- Helper for Remark 9.4.13: a continuous map whose target basepoint is identified with a chosen
point induces a specialized map on positive homotopy groups. -/
private def homotopyGroupMapOverEq
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (n : ℕ) :
    π_ (n + 1) A a → π_ (n + 1) B b :=
  match hf with
  | rfl => homotopyGroupMap f (n + 1) a

/-- Helper for Remark 9.4.13: changing only the proof of the target-basepoint equality does not
change `homotopyGroupMapOverEq`. -/
private theorem homotopyGroupMapOverEq_proofIrrel
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (h₁ h₂ : f a = b) (n : ℕ) :
    homotopyGroupMapOverEq f h₁ n = homotopyGroupMapOverEq f h₂ n := by
  -- The target-point equality proof is proposition-valued, so the specialized map is
  -- proof-irrelevant.
  cases h₁
  cases h₂
  rfl

/-- Helper for Remark 9.4.13: equal continuous maps induce equal specialized maps on positive
homotopy groups. -/
private theorem homotopyGroupMapOverEq_congr
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(A, B)} (hfg : f = g) {a : A} {b : B}
    (hf : f a = b) (hg : g a = b) (n : ℕ) :
    homotopyGroupMapOverEq f hf n = homotopyGroupMapOverEq g hg n := by
  -- After rewriting the map, only proof irrelevance remains.
  subst hfg
  exact homotopyGroupMapOverEq_proofIrrel f hf hg n

/-- Helper for Remark 9.4.13: postcomposition on homotopy groups respects composition. -/
private theorem homotopyGroupMap_comp
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (q : ℕ) (a : A) :
    homotopyGroupMap (g.comp f) q a =
      (homotopyGroupMap g q (f a)) ∘ homotopyGroupMap f q a := by
  -- On generalized-loop representatives, both sides are literally the same postcomposition.
  funext x
  refine Quotient.inductionOn x ?_
  intro γ
  rfl

/-- Helper for Remark 9.4.13: the specialized positive-degree map preserves multiplication. -/
private theorem homotopyGroupMapOverEq_mul
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (n : ℕ)
    (p q : π_ (n + 1) A a) :
    homotopyGroupMapOverEq f hf n (p * q) =
      homotopyGroupMapOverEq f hf n p * homotopyGroupMapOverEq f hf n q := by
  -- Once the basepoint transport is discharged, this is the usual multiplicativity theorem.
  subst hf
  exact homotopyGroupMap_mul f n a p q

/-- Helper for Remark 9.4.13: the specialized positive-degree map preserves the unit class. -/
private theorem homotopyGroupMapOverEq_one
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (n : ℕ) :
    homotopyGroupMapOverEq f hf n (1 : π_ (n + 1) A a) = 1 := by
  -- Once the basepoint transport is discharged, this is the ordinary unit law.
  subst hf
  exact homotopyGroupMap_one f n a

/-- Helper for Remark 9.4.13: the specialized positive-degree map can be bundled as a monoid
homomorphism. -/
private def homotopyGroupMapOverEqMulHom
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (n : ℕ) :
    π_ (n + 1) A a →* π_ (n + 1) B b where
  toFun := homotopyGroupMapOverEq f hf n
  map_one' := by
    -- The unit statement is exactly the isolated companion lemma above.
    exact homotopyGroupMapOverEq_one f hf n
  map_mul' := by
    -- Multiplicativity is exactly the isolated companion lemma above.
    exact homotopyGroupMapOverEq_mul f hf n

/-- Helper for Remark 9.4.13: composing specialized positive-degree maps matches specializing the
composite map. -/
private theorem homotopyGroupMapOverEq_comp
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C))
    {a : A} {b : B} {c : C} (hf : f a = b) (hg : g b = c) (n : ℕ) :
    (homotopyGroupMapOverEq g hg n) ∘ (homotopyGroupMapOverEq f hf n) =
      homotopyGroupMapOverEq (g.comp f)
        (by simpa [ContinuousMap.comp_apply, hf] using hg) n := by
  -- Remove the proof transports and apply functoriality of `homotopyGroupMap`.
  funext x
  subst hf
  subst hg
  simpa [homotopyGroupMapOverEq] using
    congrFun (homotopyGroupMap_comp f g (n + 1) a).symm x

/-- Helper for Remark 9.4.13: the specialized map of the identity is the identity. -/
private theorem homotopyGroupMapOverEq_id
    {A : Type*} [TopologicalSpace A] (a : A) (n : ℕ) :
    homotopyGroupMapOverEq (ContinuousMap.id A) (a := a) (b := a) rfl n = id := by
  -- With no transport remaining, this is the identity-induced map on `π_(n + 1)`.
  funext x
  simp [homotopyGroupMapOverEq, homotopyGroupMap_id]

/-- Helper for Remark 9.4.13: a homeomorphism with exact basepoint match induces a bijection on
positive homotopy groups. -/
private theorem homotopyGroupMapOverEqMulHom_bijectiveOfHomeomorph
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {a : A} {b : B} (h : e a = b) (n : ℕ) :
    Function.Bijective
      (homotopyGroupMapOverEqMulHom
        (f := ⟨e, e.continuous⟩) h n) := by
  let f : C(A, B) := ⟨e, e.continuous⟩
  let g : C(B, A) := ⟨e.symm, e.symm.continuous⟩
  have hsymm : g b = a := by
    -- The inverse homeomorphism returns the chosen target basepoint to the source basepoint.
    exact (e.symm_apply_eq).2 h.symm
  have hfgComp :
      (homotopyGroupMapOverEq g hsymm n) ∘
          (homotopyGroupMapOverEq f h n) =
        homotopyGroupMapOverEq (g.comp f)
          (by simpa [f, g, ContinuousMap.comp_apply, h] using hsymm) n := by
    -- Functoriality identifies the composite specialized map with the specialization of the
    -- composite homeomorphism.
    exact homotopyGroupMapOverEq_comp f g h hsymm n
  have hfgId :
      homotopyGroupMapOverEq (g.comp f)
          (by simpa [f, g, ContinuousMap.comp_apply, h] using hsymm) n =
        (id : π_ (n + 1) A a → π_ (n + 1) A a) := by
    -- The composite homeomorphism is the identity on the source space.
    calc
      homotopyGroupMapOverEq (g.comp f)
          (by simpa [f, g, ContinuousMap.comp_apply, h] using hsymm) n =
        homotopyGroupMapOverEq (ContinuousMap.id A) rfl n := by
          apply homotopyGroupMapOverEq_congr
          ext x
          simp [f, g]
      _ = (id : π_ (n + 1) A a → π_ (n + 1) A a) := homotopyGroupMapOverEq_id a n
  have hfg :
      (homotopyGroupMapOverEq g hsymm n) ∘
          (homotopyGroupMapOverEq f h n) =
        (id : π_ (n + 1) A a → π_ (n + 1) A a) := by
    -- Compose the specialized-map functoriality with the identity comparison.
    exact hfgComp.trans hfgId
  have hgfComp :
      (homotopyGroupMapOverEq f h n) ∘
          (homotopyGroupMapOverEq g hsymm n) =
        homotopyGroupMapOverEq (f.comp g)
          (by simpa [f, g, ContinuousMap.comp_apply, hsymm] using h) n := by
    -- Functoriality gives the target-side composite comparison as well.
    exact homotopyGroupMapOverEq_comp g f hsymm h n
  have hgfId :
      homotopyGroupMapOverEq (f.comp g)
          (by simpa [f, g, ContinuousMap.comp_apply, hsymm] using h) n =
        (id : π_ (n + 1) B b → π_ (n + 1) B b) := by
    -- The opposite composite homeomorphism is the identity on the target space.
    calc
      homotopyGroupMapOverEq (f.comp g)
          (by simpa [f, g, ContinuousMap.comp_apply, hsymm] using h) n =
        homotopyGroupMapOverEq (ContinuousMap.id B) rfl n := by
          apply homotopyGroupMapOverEq_congr
          ext x
          simp [f, g]
      _ = (id : π_ (n + 1) B b → π_ (n + 1) B b) := homotopyGroupMapOverEq_id b n
  have hgf :
      (homotopyGroupMapOverEq f h n) ∘
          (homotopyGroupMapOverEq g hsymm n) =
        (id : π_ (n + 1) B b → π_ (n + 1) B b) := by
    -- Compose the target-side functoriality with the identity comparison.
    exact hgfComp.trans hgfId
  refine ⟨?_, ?_⟩
  · -- A left inverse gives injectivity.
    exact Function.LeftInverse.injective (fun x ↦ congrFun hfg x)
  · -- A right inverse gives surjectivity.
    exact Function.RightInverse.surjective (fun x ↦ congrFun hgf x)

/-- Helper for Remark 9.4.13: a homeomorphism that matches chosen basepoints exactly induces a
multiplicative equivalence on positive homotopy groups. -/
private noncomputable def homotopyGroupMulEquivOfHomeomorphOverEq
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {a : A} {b : B} (h : e a = b) (n : ℕ) :
    π_ (n + 1) A a ≃* π_ (n + 1) B b :=
  -- Bundle the previously isolated specialized map together with its homeomorphism-induced
  -- bijectivity.
  MulEquiv.ofBijective
    (homotopyGroupMapOverEqMulHom (f := ⟨e, e.continuous⟩) h n)
    (homotopyGroupMapOverEqMulHom_bijectiveOfHomeomorph e h n)

/-- Helper for Remark 9.4.13: the positive-degree homotopy group is multiplicatively identified
with the fundamental group of the iterated loop-space owner at coordinate `0`. -/
noncomputable def piSuccMulEquivFundamentalGroupAtZero
    {X : Type*} [TopologicalSpace X] {m : ℕ} {x : X} :
    π_ (m + 1) X x ≃*
      FundamentalGroup (Ω^ {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x) GenLoop.const where
  toEquiv := homotopyGroupEquivFundamentalGroup (X := X) (x := x) (i := (0 : Fin (m + 1)))
  map_mul' := by
    -- Compare multiplication on both sides by their explicit representative formulas.
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    have hsource :
        ((· * ·) : π_ (m + 1) X x → π_ (m + 1) X x → π_ (m + 1) X x) ⟦p⟧ ⟦q⟧ =
          ⟦GenLoop.transAt (0 : Fin (m + 1)) q p⟧ := by
      rw [HomotopyGroup.mul_spec (i := (0 : Fin (m + 1))) (p := p) (q := q)]
    have hloop :
        GenLoop.toLoop (0 : Fin (m + 1)) (GenLoop.transAt (0 : Fin (m + 1)) q p) =
          (GenLoop.toLoop (0 : Fin (m + 1)) q).trans
            (GenLoop.toLoop (0 : Fin (m + 1)) p) := by
      -- The loop-space owner was defined so that `fromLoop` is inverse to `toLoop`.
      calc
        GenLoop.toLoop (0 : Fin (m + 1)) (GenLoop.transAt (0 : Fin (m + 1)) q p) =
            GenLoop.toLoop (0 : Fin (m + 1))
              (GenLoop.fromLoop (0 : Fin (m + 1))
                ((GenLoop.toLoop (0 : Fin (m + 1)) q).trans
                  (GenLoop.toLoop (0 : Fin (m + 1)) p))) := by
                  rw [GenLoop.fromLoop_trans_toLoop (i := (0 : Fin (m + 1))) (p := q) (q := p)]
        _ =
            (GenLoop.toLoop (0 : Fin (m + 1)) q).trans
              (GenLoop.toLoop (0 : Fin (m + 1)) p) := by
                rw [GenLoop.to_from]
    let gp :
        FundamentalGroup (Ω^ {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x) GenLoop.const :=
      ⟦GenLoop.toLoop (0 : Fin (m + 1)) p⟧
    let gq :
        FundamentalGroup (Ω^ {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x) GenLoop.const :=
      ⟦GenLoop.toLoop (0 : Fin (m + 1)) q⟧
    let gmul :
        FundamentalGroup (Ω^ {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x) GenLoop.const :=
      (fun u v :
          FundamentalGroup (Ω^ {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x) GenLoop.const ↦
        u * v) gp gq
    have htarget :
        (⟦(GenLoop.toLoop (0 : Fin (m + 1)) q).trans
            (GenLoop.toLoop (0 : Fin (m + 1)) p)⟧ :
          FundamentalGroup (Ω^ {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x)
            GenLoop.const) =
          gmul := by
      simpa [gmul, gp, gq, FundamentalGroupoid.comp_eq] using
        (CategoryTheory.End.mul_def gp gq).symm
    -- Move the source multiplication across `homotopyGroupEquivFundamentalGroup`.
    have hfinal :
        homotopyGroupEquivFundamentalGroup (X := X) (x := x) (i := (0 : Fin (m + 1)))
            (((· * ·) : π_ (m + 1) X x → π_ (m + 1) X x → π_ (m + 1) X x) ⟦p⟧ ⟦q⟧) =
          gmul := by
      have hmid :
        homotopyGroupEquivFundamentalGroup (X := X) (x := x) (i := (0 : Fin (m + 1)))
            (((· * ·) : π_ (m + 1) X x → π_ (m + 1) X x → π_ (m + 1) X x) ⟦p⟧ ⟦q⟧)
            =
          homotopyGroupEquivFundamentalGroup (X := X) (x := x) (i := (0 : Fin (m + 1)))
            (⟦GenLoop.transAt (0 : Fin (m + 1)) q p⟧ : π_ (m + 1) X x) := by
              simpa using congrArg
                (homotopyGroupEquivFundamentalGroup (X := X) (x := x) (i := (0 : Fin (m + 1))))
                hsource
      have hloopImage :
          homotopyGroupEquivFundamentalGroup (X := X) (x := x) (i := (0 : Fin (m + 1)))
              (⟦GenLoop.transAt (0 : Fin (m + 1)) q p⟧ : π_ (m + 1) X x) =
          (⟦GenLoop.toLoop (0 : Fin (m + 1))
              (GenLoop.transAt (0 : Fin (m + 1)) q p)⟧ :
            FundamentalGroup (Ω^ {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x)
              GenLoop.const) := by
                rfl
      have hloopTransport :
          (⟦GenLoop.toLoop (0 : Fin (m + 1))
              (GenLoop.transAt (0 : Fin (m + 1)) q p)⟧ :
            FundamentalGroup (Ω^ {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x)
              GenLoop.const) =
          (⟦(GenLoop.toLoop (0 : Fin (m + 1)) q).trans
              (GenLoop.toLoop (0 : Fin (m + 1)) p)⟧ :
            FundamentalGroup (Ω^ {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x)
              GenLoop.const) := by
                simpa using congrArg Path.Homotopic.Quotient.mk hloop
      exact hmid.trans (hloopImage.trans (hloopTransport.trans htarget))
    simpa [gp, gq, gmul] using hfinal

/-- Helper for Remark 9.4.13: a homotopy equivalence transports fundamental groups
multiplicatively. -/
noncomputable def fundamentalGroupMulEquivOfHomotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  let hF := E.fullyFaithfulFunctor
  -- A categorical equivalence is fully faithful, so it identifies endomorphism monoids.
  simpa [FundamentalGroup, E] using hF.mulEquivEnd (FundamentalGroupoid.mk x)

/-- Helper for Remark 9.4.13: evaluating a homotopy between continuous maps at a point yields a
path-component witness between the endpoint values. -/
private theorem joined_of_homotopic_eval
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {g h : C(A, B)} (hgh : ContinuousMap.Homotopic g h) (a : A) :
    Joined (g a) (h a) := by
  -- Evaluate the chosen homotopy along the constant map at `a` to obtain a path in `B`.
  refine ⟨Path.mk
    ((hgh.some.toContinuousMap).comp ((ContinuousMap.id I).prodMk (ContinuousMap.const I a)))
    ?_ ?_⟩
  · change (hgh.some.toContinuousMap) (0, a) = g a
    exact hgh.some.map_zero_left a
  · change (hgh.some.toContinuousMap) (1, a) = h a
    exact hgh.some.map_one_left a

/-- Helper for Remark 9.4.13: the constant sphere map at `x` is a point of the evaluation fiber
over `x`. -/
private def sphereBasepointFiberConstPoint {q n : ℕ} (x : (𝕊 n : TopCat.{u})) :
    sphereBasepointFiber q x :=
  ⟨ContinuousMap.const (𝕊 q : TopCat.{u}) x, by
    simp [mem_sphereBasepointFiber_iff]⟩

/-- Helper for Remark 9.4.13: a path between sphere basepoints yields a path between the
corresponding constant sphere maps. -/
private noncomputable def sphereConstMapPath {q n : ℕ} {x x' : (𝕊 n : TopCat.{u})}
    (β : Path x x') :
    Path (ContinuousMap.const (𝕊 q : TopCat.{u}) x)
      (ContinuousMap.const (𝕊 q : TopCat.{u}) x') where
  toFun t := ContinuousMap.const (𝕊 q : TopCat.{u}) (β t)
  continuous_toFun := by
    -- The compact-open constant-map family is continuous in the chosen value.
    exact ContinuousMap.continuous_const'.comp β.continuous
  source' := by
    -- At time `0` the family is the constant map at the source of `β`.
    ext s
    simp [Path.source]
  target' := by
    -- At time `1` the family is the constant map at the target of `β`.
    ext s
    simp [Path.target]

/-- Helper for Remark 9.4.13: evaluating the constant-map path at the chosen sphere basepoint
recovers the original path of sphere basepoints. -/
private theorem sphereConstMapPath_comp_evalAtBasepoint
    {q n : ℕ} {x x' : (𝕊 n : TopCat.{u})} (β : Path x x') :
    (sphereMapEvalAtBasepoint q (sphereBasepoint q : (𝕊 q : TopCat.{u}))).comp
        (sphereConstMapPath (q := q) β).toContinuousMap =
      β.toContinuousMap := by
  -- Evaluating a constant sphere map at the chosen sphere basepoint returns its chosen value.
  ext t
  rfl

/-- Helper for Remark 9.4.13: translating the constant point in the sphere-evaluation fiber along
`β` lands in the same path component as the target constant point. -/
private theorem sphereBasepointFiberConstPoint_joined_fiberTranslation
    {m n : ℕ} {x x' : (𝕊 n : TopCat.{u})} (β : Path x x') :
    Joined
      (fiberTranslationMapOfPath
        (sphereMapEvalAtBasepoint (m + 1) (sphereBasepoint (m + 1) : (𝕊 (m + 1) : TopCat.{u})))
        β
        (sphereBasepointFiberConstPoint (q := m + 1) x))
      (sphereBasepointFiberConstPoint (q := m + 1) x') := by
  let p : C(C((𝕊 (m + 1) : TopCat.{u}), (𝕊 n : TopCat.{u})), (𝕊 n : TopCat.{u})) :=
    sphereMapEvalAtBasepoint (m + 1) (sphereBasepoint (m + 1) : (𝕊 (m + 1) : TopCat.{u}))
  let z₀ : fiber p x := sphereBasepointFiberConstPoint (q := m + 1) x
  let z₁ : fiber p x' := sphereBasepointFiberConstPoint (q := m + 1) x'
  let s : C(ULift.{u, 0} PUnit, fiber p x) := ContinuousMap.const _ z₀
  let f₀ : C(ULift.{u, 0} PUnit, fiber p x') :=
    ContinuousMap.const _ (fiberTranslationMapOfPath p β z₀)
  let f₁ : C(ULift.{u, 0} PUnit, fiber p x') := ContinuousMap.const _ z₁
  let restrictSource : C(I × ULift.{u, 0} PUnit, I × fiber p x) :=
    ⟨fun tu ↦ (tu.1, z₀), by fun_prop⟩
  rcases Classical.choose_spec (exists_fiberInclusionHomotopyLiftEndpoint p β) with ⟨Graw, hGraw⟩
  let G₀ : ((fiberInclusion p x).comp s).Homotopy ((fiberInclusion p x').comp f₀) :=
    { toContinuousMap := Graw.toContinuousMap.comp restrictSource
      map_zero_left := by
        intro u
        cases u
        exact by
          simpa [restrictSource, s] using Graw.apply_zero z₀
      map_one_left := by
        intro u
        cases u
        change Graw (1, z₀) = ((fiberTranslationMapOfPath p β z₀ : fiber p x') :
          C((𝕊 (m + 1) : TopCat.{u}), (𝕊 n : TopCat.{u})))
        exact by
          simpa [fiberTranslationMapOfPath] using Graw.apply_one z₀ }
  let G₁ : ((fiberInclusion p x).comp s).Homotopy ((fiberInclusion p x').comp f₁) :=
    { toContinuousMap := (sphereConstMapPath (q := m + 1) β).toContinuousMap.comp
        (ContinuousMap.fst : C(I × ULift.{u, 0} PUnit, I))
      map_zero_left := by
        intro u
        cases u
        -- At time `0`, the explicit lift is the constant map at the source point.
        ext y
        exact congrArg
          (fun f : C((𝕊 (m + 1) : TopCat.{u}), (𝕊 n : TopCat.{u})) ↦ f y)
          (sphereConstMapPath (q := m + 1) β).source
      map_one_left := by
        intro u
        cases u
        -- At time `1`, the explicit lift is the constant map at the target point.
        ext y
        exact congrArg
          (fun f : C((𝕊 (m + 1) : TopCat.{u}), (𝕊 n : TopCat.{u})) ↦ f y)
          (sphereConstMapPath (q := m + 1) β).target }
  have hG₀ :
      p.comp G₀.toContinuousMap =
        (β.toHomotopyConst (Y := ULift.{u, 0} PUnit)).toContinuousMap := by
    -- The chosen Chapter 7 lift projects to the constant family of the original path `β`.
    ext tu
    rcases tu with ⟨t, u⟩
    cases u
    simpa [G₀, restrictSource, s, Path.toHomotopyConst] using
      ContinuousMap.congr_fun hGraw (t, z₀)
  have hG₁ :
      p.comp G₁.toContinuousMap =
        (β.toHomotopyConst (Y := ULift.{u, 0} PUnit)).toContinuousMap := by
    -- The explicit constant-map lift has the same projected base homotopy after evaluation.
    ext tu
    rcases tu with ⟨t, u⟩
    cases u
    simpa [G₁, Path.toHomotopyConst] using
      ContinuousMap.congr_fun
        (sphereConstMapPath_comp_evalAtBasepoint (q := m + 1) β) t
  have hEndpoint : ContinuousMap.Homotopic f₀ f₁ := by
    -- Two endpoint maps over the same projected lift are homotopic in the target fiber.
    exact endpointHomotopic_of_sameProjectedLift
      (q := p) (s := s) (G₀ := G₀) (G₁ := G₁) hG₀ hG₁
  have hClass :
      (⟦fiberTranslationMapOfPath p β z₀⟧ : ZerothHomotopy (fiber p x')) = ⟦z₁⟧ := by
    -- Evaluate the endpoint homotopy on the unique point of `PUnit`.
    simpa [f₀, f₁, z₀, z₁] using
      congrFun (zerothHomotopyMap_eq_of_homotopic hEndpoint) ⟦ULift.up PUnit.unit⟧
  -- Equality in `ZerothHomotopy` is exactly the path relation `Joined`.
  exact Quotient.exact hClass

/-- Helper for Remark 9.4.13: the constant sphere map at `x` is also the distinguished point of
the concrete based-map-space owner. -/
private def sphereBasepointBasedMapSpaceConstPoint {q n : ℕ} (x : (𝕊 n : TopCat.{u})) :
    sphereBasepointBasedMapSpace q x :=
  ⟨ContinuousMap.const (𝕊 q : TopCat.{u}) x, by
    simp [mem_sphereBasepointFiber_iff]⟩

/-- Helper for Remark 9.4.13: in positive degree, the Section 9.5 based-map-space comparison
should be chosen together with the normalization sending the constant based sphere map to
`GenLoop.const`. -/
private theorem existsSphereBasepointBasedMapSpaceHomeomorphIteratedLoopSpaceSucc
    {m n : ℕ} (x : (𝕊 n : TopCat.{u})) :
    ∃ e : sphereBasepointBasedMapSpace (m + 1) x ≃ₜ Ω^ (Fin (m + 1)) (𝕊 n : TopCat.{u}) x,
      e (sphereBasepointBasedMapSpaceConstPoint (q := m + 1) x) = GenLoop.const := by
  -- Route correction: only positive-degree transport is used below, so the missing Section 9.5
  -- owner is isolated at the successor surface `m + 1` instead of an unused generic `q`.
  -- TODO: construct the pointed comparison explicitly from the Section 9.5 fiber model so the
  -- constant based sphere map is sent exactly to `GenLoop.const`.
  sorry

/-- Helper for Remark 9.4.13: the Section 9.5 comparison is read first as an explicit based-map
space comparison in positive degree and only then as a fiber comparison. -/
private noncomputable def sphereBasepointBasedMapSpaceHomeomorphIteratedLoopSpaceSucc
    {m n : ℕ} (x : (𝕊 n : TopCat.{u})) :
    sphereBasepointBasedMapSpace (m + 1) x ≃ₜ Ω^ (Fin (m + 1)) (𝕊 n : TopCat.{u}) x :=
  -- Route correction: choose the Section 9.5 comparison from the pointed existence theorem so the
  -- constant-map normalization becomes a direct `Classical.choose_spec` rewrite.
  Classical.choose (existsSphereBasepointBasedMapSpaceHomeomorphIteratedLoopSpaceSucc (m := m) x)

/-- Helper for Remark 9.4.13: the chosen based-map-space comparison must still normalize the
constant based sphere map to the constant generalized loop in positive degree. -/
private theorem sphereBasepointBasedMapSpaceHomeomorphIteratedLoopSpaceSucc_const
    {m n : ℕ} (x : (𝕊 n : TopCat.{u})) :
    sphereBasepointBasedMapSpaceHomeomorphIteratedLoopSpaceSucc (m := m) x
        (sphereBasepointBasedMapSpaceConstPoint (q := m + 1) x) =
      GenLoop.const := by
  -- The normalization is bundled into the pointed choice used to define the comparison.
  exact
    Classical.choose_spec
      (existsSphereBasepointBasedMapSpaceHomeomorphIteratedLoopSpaceSucc (m := m) x)

/-- Helper for Remark 9.4.13: the chosen based-map-space comparison also recovers the constant
based sphere map from the constant generalized loop in positive degree. -/
private theorem sphereBasepointBasedMapSpaceHomeomorphIteratedLoopSpaceSucc_symm_const
    {m n : ℕ} (x : (𝕊 n : TopCat.{u})) :
    (sphereBasepointBasedMapSpaceHomeomorphIteratedLoopSpaceSucc (m := m) x).symm GenLoop.const =
      sphereBasepointBasedMapSpaceConstPoint (q := m + 1) x := by
  -- Apply the inverse of the chosen comparison to the normalized constant-loop identity.
  apply (sphereBasepointBasedMapSpaceHomeomorphIteratedLoopSpaceSucc (m := m) x).injective
  simpa using
    (sphereBasepointBasedMapSpaceHomeomorphIteratedLoopSpaceSucc_const (m := m) x).symm

/-- Helper for Remark 9.4.13: a pointed Section 9.5 comparison from the evaluation fiber to the
iterated loop-space owner in positive degree. -/
private noncomputable def pointedSphereBasepointFiberHomeomorphSucc
    {m n : ℕ} (x : (𝕊 n : TopCat.{u})) :
    sphereBasepointFiber (m + 1) x ≃ₜ Ω^ (Fin (m + 1)) (𝕊 n : TopCat.{u}) x :=
  -- Route correction: consume the explicit based-map-space comparison through the owner API from
  -- `Construction_9_5_1` instead of introducing a second existential fiber bridge.
  sphereBasepointFiberHomeomorphOf (m + 1) x
    (sphereBasepointBasedMapSpaceHomeomorphIteratedLoopSpaceSucc (m := m) x)

/-- Helper for Remark 9.4.13: the chosen pointed Section 9.5 comparison sends the constant fiber
point to the constant generalized loop in positive degree. -/
private theorem pointedSphereBasepointFiberHomeomorphSucc_constPoint
    {m n : ℕ} (x : (𝕊 n : TopCat.{u})) :
    pointedSphereBasepointFiberHomeomorphSucc (m := m) x
        (sphereBasepointFiberConstPoint (q := m + 1) x) =
      GenLoop.const := by
  -- The fiber-side adapter is exactly the explicit based-map-space comparison evaluated at the
  -- constant based sphere map.
  simpa [pointedSphereBasepointFiberHomeomorphSucc, sphereBasepointFiberConstPoint,
    sphereBasepointBasedMapSpaceConstPoint] using
    sphereBasepointBasedMapSpaceHomeomorphIteratedLoopSpaceSucc_const (m := m) x

/-- Helper for Remark 9.4.13: the inverse pointed Section 9.5 comparison recovers the constant
fiber point from the constant generalized loop in positive degree. -/
private theorem pointedSphereBasepointFiberHomeomorphSucc_symm_constPoint
    {m n : ℕ} (x : (𝕊 n : TopCat.{u})) :
    (pointedSphereBasepointFiberHomeomorphSucc (m := m) x).symm GenLoop.const =
      sphereBasepointFiberConstPoint (q := m + 1) x := by
  -- Apply the inverse pointed comparison to the normalized constant-loop identity.
  apply (pointedSphereBasepointFiberHomeomorphSucc (m := m) x).injective
  simpa using (pointedSphereBasepointFiberHomeomorphSucc_constPoint (m := m) x).symm

/-- Helper for Remark 9.4.13: omitting coordinate `0` from `Fin (m + 1)` identifies the tail
loop-space owner with the canonical `Fin m` owner. -/
private noncomputable def tailLoopOwnerHomeomorph
    {X : Type*} [TopologicalSpace X] (m : ℕ) (x : X) :
    Ω^ {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x ≃ₜ Ω^ (Fin m) X x :=
  -- Rename the index set by deleting the distinguished coordinate `0`.
  GenLoop.congr x ((finSuccAboveEquiv (0 : Fin (m + 1))).symm)

/-- Helper for Remark 9.4.13: the tail-owner homeomorphism preserves the constant generalized
loop exactly. -/
@[simp] private theorem tailLoopOwnerHomeomorph_const
    {X : Type*} [TopologicalSpace X] (m : ℕ) (x : X) :
    tailLoopOwnerHomeomorph m x GenLoop.const = GenLoop.const := by
  -- Reindexing the coordinates leaves the constant loop unchanged pointwise.
  ext t
  rfl

/-- Helper for Remark 9.4.13: after deleting the distinguished coordinate `0`, `π_(m + 1)` is
nonempty-equivalent to the fundamental group of the canonical `m`-fold loop-space owner. -/
private theorem existsPiSuccMulEquivFundamentalGroupTailLoopOwner
    {X : Type*} [TopologicalSpace X] {m : ℕ} {x : X} :
    Nonempty (π_ (m + 1) X x ≃* FundamentalGroup (Ω^ (Fin m) X x) GenLoop.const) := by
  let eTail :
      Ω^ {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x ≃ₜ Ω^ (Fin m) X x :=
    tailLoopOwnerHomeomorph m x
  have hTail :
      eTail GenLoop.const = GenLoop.const := by
    -- The tail-owner comparison keeps the constant generalized loop fixed.
    simpa [eTail] using tailLoopOwnerHomeomorph_const m x
  -- First rewrite `π_(m + 1)` as the fundamental group at the omitted-zero owner.
  refine ⟨(piSuccMulEquivFundamentalGroupAtZero (X := X) (m := m) (x := x)).trans ?_⟩
  -- Then transport that fundamental group to the canonical `Fin m` loop-space owner.
  exact
    ((HomotopyGroup.pi1MulEquivFundamentalGroup GenLoop.const).symm).trans
      ((homotopyGroupMulEquivOfHomeomorphOverEq eTail hTail 0).trans
        (HomotopyGroup.pi1MulEquivFundamentalGroup GenLoop.const))

/-- Helper for Remark 9.4.13: the chosen tail-owner bridge from `π_(m + 1)` to the fundamental
group of the canonical `m`-fold loop-space owner. -/
private noncomputable def piSuccMulEquivFundamentalGroupTailLoopOwner
    {X : Type*} [TopologicalSpace X] {m : ℕ} {x : X} :
    π_ (m + 1) X x ≃* FundamentalGroup (Ω^ (Fin m) X x) GenLoop.const :=
  Classical.choice (existsPiSuccMulEquivFundamentalGroupTailLoopOwner (m := m) (x := x))

/-- Helper for Remark 9.4.13: a path between sphere basepoints yields a homotopy equivalence
between the corresponding iterated loop-space owners in positive degree. -/
noncomputable def sphereIteratedLoopSpaceHomotopyEquivOfPath
    {m n : ℕ} {x x' : (𝕊 n : TopCat.{u})} (β : Path x x') :
    ContinuousMap.HomotopyEquiv
      (Ω^ (Fin (m + 1)) (𝕊 n : TopCat.{u}) x)
      (Ω^ (Fin (m + 1)) (𝕊 n : TopCat.{u}) x') := by
  let p : C(C((𝕊 (m + 1) : TopCat.{u}), (𝕊 n : TopCat.{u})), (𝕊 n : TopCat.{u})) :=
    sphereMapEvalAtBasepoint (m + 1) (sphereBasepoint (m + 1) : (𝕊 (m + 1) : TopCat.{u}))
  let eSource := pointedSphereBasepointFiberHomeomorphSucc (m := m) x
  let eTarget := pointedSphereBasepointFiberHomeomorphSucc (m := m) x'
  let eFiber := Classical.choose (exists_homotopyEquiv_fiberTranslationPath p β)
  -- Route correction: only the successor-degree loop owners appear in the multiplicative
  -- transport proof, so translate the canonical Section 9.5 sphere fibers directly there.
  exact eSource.symm.toHomotopyEquiv.trans (eFiber.trans eTarget.toHomotopyEquiv)

/-- Helper for Remark 9.4.13: the path-induced iterated-loop homotopy equivalence sends the
constant generalized loop into the path component of the target constant loop. -/
private theorem sphereIteratedLoopSpaceHomotopyEquivOfPath_imageConst_joined
    {m n : ℕ} {x x' : (𝕊 n : TopCat.{u})} (β : Path x x') :
    Joined ((sphereIteratedLoopSpaceHomotopyEquivOfPath (m := m) β) GenLoop.const) GenLoop.const := by
  let p : C(C((𝕊 (m + 1) : TopCat.{u}), (𝕊 n : TopCat.{u})), (𝕊 n : TopCat.{u})) :=
    sphereMapEvalAtBasepoint (m + 1) (sphereBasepoint (m + 1) : (𝕊 (m + 1) : TopCat.{u}))
  let eSource := pointedSphereBasepointFiberHomeomorphSucc (m := m) x
  let eTarget := pointedSphereBasepointFiberHomeomorphSucc (m := m) x'
  let eFiber := Classical.choose (exists_homotopyEquiv_fiberTranslationPath p β)
  have hSource :
      eSource.symm GenLoop.const = sphereBasepointFiberConstPoint (q := m + 1) x := by
    -- The inverse pointed comparison recovers the distinguished constant fiber point exactly.
    simpa [eSource] using pointedSphereBasepointFiberHomeomorphSucc_symm_constPoint (m := m) x
  have hTarget :
      eTarget (sphereBasepointFiberConstPoint (q := m + 1) x') = GenLoop.const := by
    -- The target pointed comparison was chosen to send the constant fiber point to `GenLoop.const`.
    simpa using pointedSphereBasepointFiberHomeomorphSucc_constPoint (m := m) x'
  have hFiberClass :
      (⟦eFiber.toFun⟧ : fiberMapHomotopyClasses p x x') =
        (⟦fiberTranslationMapOfPath p β⟧ : fiberMapHomotopyClasses p x x') := by
    -- Both maps represent the canonical translation class along `β` in Chapter 7.
    calc
      (⟦eFiber.toFun⟧ : fiberMapHomotopyClasses p x x') =
          fiberTranslationClass p (Path.Homotopic.Quotient.mk β) := by
            exact Classical.choose_spec (exists_homotopyEquiv_fiberTranslationPath p β)
      _ = (⟦fiberTranslationMapOfPath p β⟧ : fiberMapHomotopyClasses p x x') := by
            simpa using (fiberTranslationMapOfPath_class p β).symm
  have hFiberHomotopic :
      ContinuousMap.Homotopic eFiber.toFun (fiberTranslationMapOfPath p β) := by
    -- Equality in the quotient of fiber maps is exactly homotopy.
    exact Quotient.exact hFiberClass
  have hEval :
      Joined
        (eFiber.toFun (sphereBasepointFiberConstPoint (q := m + 1) x))
        (fiberTranslationMapOfPath p β (sphereBasepointFiberConstPoint (q := m + 1) x)) := by
    -- Evaluate the chosen homotopy between the two fiber maps at the constant source point.
    exact joined_of_homotopic_eval hFiberHomotopic (sphereBasepointFiberConstPoint (q := m + 1) x)
  have hFiberEndpoint :
      Joined
        (eFiber.toFun (sphereBasepointFiberConstPoint (q := m + 1) x))
        (sphereBasepointFiberConstPoint (q := m + 1) x') := by
    -- Chain the evaluated homotopy with the already proved endpoint translation statement.
    exact hEval.trans (sphereBasepointFiberConstPoint_joined_fiberTranslation (m := m) β)
  have hTargetJoined :
      Joined
        (eTarget (eFiber.toFun (sphereBasepointFiberConstPoint (q := m + 1) x)))
        (eTarget (sphereBasepointFiberConstPoint (q := m + 1) x')) := by
    -- Push the endpoint path across the target pointed comparison.
    exact ⟨hFiberEndpoint.somePath.map eTarget.continuous⟩
  -- Rewrite the endpoints into the loop-owner transport and the target constant loop.
  change Joined (eTarget (eFiber.toFun (eSource.symm GenLoop.const))) GenLoop.const
  rw [hSource]
  simpa [hTarget] using hTargetJoined

/-- Helper for Remark 9.4.13: the multiplicative transport to the standard basepoint factors
through the canonical `m`-fold loop-space owners. -/
private theorem existsSphereHomotopyGroupMulEquivToStandardBasepoint
    {m n : ℕ} {x : (𝕊 n : TopCat.{u})}
    (β : Path x (sphereBasepoint n : (𝕊 n : TopCat.{u}))) :
    Nonempty
      (π_ (m + 1) (𝕊 n : TopCat.{u}) x ≃*
        π_ (m + 1) (𝕊 n : TopCat.{u}) (sphereBasepoint n : (𝕊 n : TopCat.{u}))) := by
  cases m with
  | zero =>
      -- Route correction: in degree one the loop owner is just the sphere itself, so the chosen
      -- path `β` directly gives the required basepoint-change equivalence on fundamental groups.
      exact ⟨
        (HomotopyGroup.pi1MulEquivFundamentalGroup x).trans
          ((FundamentalGroup.fundamentalGroupMulEquivOfPath β).trans
            (HomotopyGroup.pi1MulEquivFundamentalGroup
              (sphereBasepoint n : (𝕊 n : TopCat.{u}))).symm)⟩
  | succ m =>
      let eSource :
          π_ (m + 2) (𝕊 n : TopCat.{u}) x ≃*
            FundamentalGroup (Ω^ (Fin (m + 1)) (𝕊 n : TopCat.{u}) x) GenLoop.const :=
        piSuccMulEquivFundamentalGroupTailLoopOwner (m := m + 1) (x := x)
      let eTarget :
          π_ (m + 2) (𝕊 n : TopCat.{u}) (sphereBasepoint n : (𝕊 n : TopCat.{u})) ≃*
            FundamentalGroup
              (Ω^ (Fin (m + 1)) (𝕊 n : TopCat.{u}) (sphereBasepoint n : (𝕊 n : TopCat.{u})))
              GenLoop.const :=
        piSuccMulEquivFundamentalGroupTailLoopOwner
          (m := m + 1) (x := (sphereBasepoint n : (𝕊 n : TopCat.{u})))
      let eLoop := sphereIteratedLoopSpaceHomotopyEquivOfPath (m := m) β
      have hLoopConst :
          Joined (eLoop GenLoop.const) GenLoop.const := by
        -- The positive-degree loop-owner transport lands in the component of the constant loop.
        simpa [eLoop] using sphereIteratedLoopSpaceHomotopyEquivOfPath_imageConst_joined (m := m) β
      -- Transport on the canonical positive-degree loop owners, then correct the target basepoint
      -- by the joined witness on that owner.
      exact ⟨
        eSource.trans
          ((fundamentalGroupMulEquivOfHomotopyEquiv eLoop GenLoop.const).trans
            ((FundamentalGroup.fundamentalGroupMulEquivOfPath hLoopConst.somePath).trans
              eTarget.symm))⟩

/-- Helper for Remark 9.4.13: the chosen multiplicative transport equivalence to the standard
sphere basepoint. -/
private noncomputable def sphereHomotopyGroupMulEquivToStandardBasepoint
    {m n : ℕ} {x : (𝕊 n : TopCat.{u})}
    (β : Path x (sphereBasepoint n : (𝕊 n : TopCat.{u}))) :
    π_ (m + 1) (𝕊 n : TopCat.{u}) x ≃*
      π_ (m + 1) (𝕊 n : TopCat.{u}) (sphereBasepoint n : (𝕊 n : TopCat.{u})) :=
  Classical.choice (existsSphereHomotopyGroupMulEquivToStandardBasepoint (m := m) β)

/-- Helper for Remark 9.4.13: positive-degree basepoint transport on sphere homotopy groups is
multiplicative. -/
noncomputable def sphereHomotopyGroupMulEquivStandardBasepoint
    {m n : ℕ} {x : (𝕊 n : TopCat.{u})}
    (β : Path x (sphereBasepoint n : (𝕊 n : TopCat.{u}))) :
    π_ (m + 1) (𝕊 n : TopCat.{u}) x ≃*
      π_ (m + 1) (𝕊 n : TopCat.{u}) (sphereBasepoint n : (𝕊 n : TopCat.{u})) :=
  -- Keep the definition body term-style by delegating the proof to the preceding theorem.
  sphereHomotopyGroupMulEquivToStandardBasepoint (m := m) β

/-- Helper for Remark 9.4.13: Serre's exceptional-family splitting at the standard sphere
basepoint. -/
theorem standardExceptionalEvenSphereHomotopyGroupHasIntSummand {n : ℕ} :
    ∃ (T : Type) (_ : CommGroup T) (_ : Finite T),
      Nonempty
        (π_ (4 * n + 3) (𝕊 (2 * n + 2) : TopCat.{u})
            (sphereBasepoint (2 * n + 2) : (𝕊 (2 * n + 2) : TopCat.{u})) ≃*
          (Multiplicative ℤ × T)) := by
  cases n with
  | zero =>
      -- The `n = 0` exceptional case is exactly the already proved `π₃(S²)` computation.
      simpa using standardExceptionalEvenSphereHomotopyGroupHasIntSummandZero
  | succ n =>
      -- The remaining exceptional cases are isolated in the successor-family Serre input.
      simpa using standardExceptionalEvenSphereHomotopyGroupHasIntSummandSucc (n := n)

/-- Helper for Remark 9.4.13: Serre's exceptional-family splitting transports from the standard
sphere basepoint to any chosen basepoint once positive-degree multiplicative transport is known. -/
theorem exceptionalEvenSphereHomotopyGroupHasIntSummandAtBasepoint {n : ℕ}
    (x : (𝕊 (2 * n + 2) : TopCat.{u})) :
    ∃ (T : Type) (_ : CommGroup T) (_ : Finite T),
      Nonempty
        (π_ (4 * n + 3) (𝕊 (2 * n + 2) : TopCat.{u})
            x ≃*
          (Multiplicative ℤ × T)) := by
  let β :=
    spherePathToStandardBasepoint (n := 2 * n + 2) (exceptionalEvenSphereDimensionOneLt n) x
  -- Route correction: reduce the arbitrary-basepoint statement to the standard-basepoint
  -- exceptional splitting plus the positive-degree multiplicative transport bridge.
  exact
    transportExceptionalSplittingAlongMulEquiv
      (sphereHomotopyGroupMulEquivStandardBasepoint (m := 4 * n + 2) β)
      (standardExceptionalEvenSphereHomotopyGroupHasIntSummand (n := n))

/-- Remark 9.4.13 (1): for `q > n > 1`, the homotopy group `π_ q (𝕊 n) x` is finite unless
`(q, n) = (4 * m - 1, 2 * m)` for some `m : ℕ`. -/
theorem sphere_homotopyGroup_finite_of_not_exceptional {q n : ℕ}
    (hq : n < q) (hn : 1 < n)
    (h_exception : ¬ ∃ m : ℕ, n = 2 * m ∧ q = 4 * m - 1)
    (x : (𝕊 n : TopCat.{u})) :
    Finite (π_ q (𝕊 n) x) := by
  -- Route correction: keep the public theorem as a one-step transport wrapper around the
  -- canonical standard-basepoint finiteness input.
  let β := spherePathToStandardBasepoint hn x
  -- Move from the chosen basepoint `x` to the standard sphere basepoint, then apply the
  -- standard-basepoint Serre finiteness theorem.
  exact sphereHomotopyGroupFiniteOfStandardBasepoint
    (q := q)
    x
    β
    (standardSphereHomotopyGroupFiniteOfNotExceptional hq hn h_exception)

/-- Remark 9.4.13 (2): reindexing the exceptional family `π_ (4 * m - 1) (𝕊 (2 * m))` by
`m = n + 1`, the group `π_ (4 * n + 3) (𝕊 (2 * n + 2))` has an infinite cyclic summand together
with a finite torsion factor. -/
theorem exceptional_evenSphere_homotopyGroup_has_int_summand {n : ℕ}
    (x : (𝕊 (2 * n + 2) : TopCat.{u})) :
    ∃ (T : Type) (_ : CommGroup T) (_ : Finite T),
      Nonempty (π_ (4 * n + 3) (𝕊 (2 * n + 2)) x ≃* (Multiplicative ℤ × T)) := by
  -- Route correction: consume the arbitrary-basepoint exceptional theorem directly instead of
  -- reopening positive-degree basepoint transport in this file.
  exact exceptionalEvenSphereHomotopyGroupHasIntSummandAtBasepoint x

/-- Helper for Remark 9.4.13: a multiplicative equivalence to `Multiplicative ℤ × T` forces
infinitude when the torsion factor `T` is finite. -/
lemma mulEquivInfinite_ofFiniteRightFactor {G T : Type*} [Group G] [CommGroup T] [Finite T]
    (e : G ≃* (Multiplicative ℤ × T)) : Infinite G := by
  -- Transfer infinitude across the equivalence once the product is known to be infinite.
  refine (e.toEquiv.infinite_iff).2 ?_
  -- The `ℤ` factor is infinite, and a product with a nonempty finite group stays infinite.
  exact Prod.infinite_of_left

/-- The exceptional even-sphere homotopy groups from Remark 9.4.13 are infinite. -/
theorem exceptional_evenSphere_homotopyGroup_infinite {n : ℕ}
    (x : (𝕊 (2 * n + 2) : TopCat.{u})) :
    Infinite (π_ (4 * n + 3) (𝕊 (2 * n + 2)) x) := by
  -- Use the explicit `ℤ × T` splitting from the exceptional-family theorem as the entire input.
  rcases exceptional_evenSphere_homotopyGroup_has_int_summand x with ⟨T, hT, hfinite, ⟨e⟩⟩
  let _ : CommGroup T := hT
  let _ : Finite T := hfinite
  -- The finite torsion factor does not affect infinitude once the `ℤ` summand is exposed.
  exact mulEquivInfinite_ofFiniteRightFactor e
