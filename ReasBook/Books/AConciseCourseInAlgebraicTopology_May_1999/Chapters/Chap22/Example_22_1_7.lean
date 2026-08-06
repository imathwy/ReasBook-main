import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.SuspensionSphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Definition_22_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap22.Theorem_22_1_3

open CategoryTheory

noncomputable section

universe u w

-- The source-facing example uses the Chapter 11 sphere owner `suspensionSphere` and the Chapter
-- 22 prespectrum-homology owner `connectivePrespectrumReducedHomology`. The reusable API here is
-- the sphere prespectrum together with the Chapter 22 hypothesis companions that let later files
-- invoke `connectivePrespectrumDefinesReducedHomologyTheory` directly on this example.

/-- The sphere prespectrum, modeled as the suspension prespectrum on the Chapter 11 sphere owner
`suspensionSphere n = Σ^n S⁰`. -/
def spherePrespectrum : Prespectrum where
  spaces := suspensionSphere
  structureMap n := 𝟙 (suspensionSphere (n + 1))

/-- Evaluating `spherePrespectrum` at `n` recovers the Chapter 11 sphere `Σ^n S⁰`. -/
@[simp] theorem spherePrespectrum_apply (n : ℕ) :
    spherePrespectrum n = suspensionSphere n := rfl

/-- The degree-`n` structure map of `spherePrespectrum` is the identity
`Σ(suspensionSphere n) ⟶ suspensionSphere (n + 1)`. -/
@[simp] theorem spherePrespectrum_sigma (n : ℕ) :
    spherePrespectrum.sigma n = 𝟙 (suspensionSphere (n + 1)) := rfl

private abbrev BasedCWCompactlyGeneratedType (X : BasedCWComplex.{u}) : Type u :=
  ↥X.1.right

private theorem uCompactlyGeneratedSpace_compactlyGenerated
    (X : Type u) [TopologicalSpace X] :
    @UCompactlyGeneratedSpace.{w} X (TopologicalSpace.compactlyGenerated.{w} X) := by
  let f : (Σ (i : (S : CompHaus.{w}) × C(S, X)), i.fst) → X := fun x ↦ x.1.2 x.2
  have hf : @Continuous ((Σ (i : (S : CompHaus.{w}) × C(S, X)), i.fst)) X
      instTopologicalSpaceSigma (TopologicalSpace.coinduced f inferInstance) f := by
    rw [continuous_iff_coinduced_le]
  exact @uCompactlyGeneratedSpace_of_coinduced.{w, _, _}
    ((Σ (i : (S : CompHaus.{w}) × C(S, X)), i.fst)) X instTopologicalSpaceSigma
    (TopologicalSpace.coinduced f inferInstance) inferInstance f hf rfl

/-- The pointed compactly generated space underlying `X`, obtained by replacing the carrier
topology with its compactly generated reflection and preserving the chosen basepoint. -/
abbrev basedCWComplexToPointedCompactlyGenerated
    (X : BasedCWComplex.{u}) : PointedCompactlyGenerated.{w, u} :=
  let t0 : TopologicalSpace (BasedCWCompactlyGeneratedType X) := inferInstance
  letI : TopologicalSpace (BasedCWCompactlyGeneratedType X) :=
    @TopologicalSpace.compactlyGenerated.{w} (BasedCWCompactlyGeneratedType X) t0
  letI : UCompactlyGeneratedSpace.{w} (BasedCWCompactlyGeneratedType X) :=
    @uCompactlyGeneratedSpace_compactlyGenerated (BasedCWCompactlyGeneratedType X) t0
  PointedCompactlyGenerated.of
    (CompactlyGenerated.of (BasedCWCompactlyGeneratedType X))
    (underTopBasepoint X.1)

/-- The sphere prespectrum satisfies the connectivity hypothesis used in
`connectivePrespectrumDefinesReducedHomologyTheory`. -/
theorem spherePrespectrum_connectivity (n : ℕ) :
    prespectrumConnectivityHypothesis n (spherePrespectrum n) := by
  sorry

/-- The sphere prespectrum has stagewise CW type in the sense of
`prespectrumCWHypothesis`. -/
theorem spherePrespectrum_cw : prespectrumCWHypothesis spherePrespectrum := by
  sorry

/-- Each stage of the sphere prespectrum is well pointed. -/
theorem spherePrespectrum_wellPointed (n : ℕ) :
    WellPointedSpace (spherePrespectrum n) := by
  sorry

/-- Example 22.1.7: the sphere prespectrum represents stable homotopy theory by admitting one
Chapter 22 presentation whose represented `ℤ`-graded functor is a reduced homology theory on
based CW complexes and whose represented reduced homology groups in degree `(q : ℤ)` are
canonically isomorphic, after viewing their additive groups multiplicatively, to the
stable-homotopy groups `π_q^s(X)` for every nonnegative degree `q` as in Definition 11.2.5 and
every based CW complex `X`. -/
theorem spherePrespectrumRepresentsStableHomotopy
    [HomotopicalAlgebra.CategoryWithCofibrations BasedCWComplex] :
    ∃ presentation : ConnectivePrespectrumReducedHomologyPresentation spherePrespectrum,
      ∃ setup : BasedCWReducedSuspensionCofiberSetup,
        ∃ comparison :
          ∀ q : ℕ, ∀ X : BasedCWComplex,
            GrpCat.of
                (Multiplicative
                  ((connectivePrespectrumReducedHomology spherePrespectrum presentation
                    (q : ℤ)).obj X)) ≅
              stableHomotopyGroup (basedCWComplexToPointedCompactlyGenerated X) q,
          ReducedHomologyTheoryOnBasedCWComplexes.{w}
            setup.suspension setup.cofiber setup.cofiberMap
            (connectivePrespectrumReducedHomology spherePrespectrum presentation) := sorry
