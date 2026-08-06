import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Homotopy.Equiv
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.Problem_13_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Construction_20_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Proposition_20_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Corollary_20_1_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Theorem_20_1_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Theorem_20_3_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.ManifoldEulerCharacteristic

open AlgebraicTopology
open CategoryTheory CategoryTheory.Limits Topology Simplicial
open scoped BigOperators ContinuousMap Manifold Topology.CWComplex

noncomputable section

section

variable {K : Type} [Field K]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace H M] [CompactSpace M] [IsManifold I ⊤ M]

/-- Helper for Proposition 21.1.2: the chapter-local Euler characteristic is the alternating
`finsum` of the chapter-local Betti numbers. -/
theorem manifoldEulerCharacteristic_eq_finsum_betti :
    manifoldEulerCharacteristic K M =
      ∑ᶠ i : ℕ, Int.negOnePow i * (manifoldBettiNumber K i M : ℤ) := by
  let e : ModuleCat.of K (ULift K) ≅ ModuleCat.of K K :=
    LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift K ≃ₗ[K] K)
  have hfinrank (i : ℕ) :
      Module.finrank K ((fieldTopologicalSingularChains K (TopCat.of M)).homology i) =
        manifoldBettiNumber K i M := by
    simpa [manifoldBettiNumber, fieldTopologicalSingularChains,
      AlgebraicTopology.singularHomologyFunctor] using
      LinearEquiv.finrank_eq
        ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat K) i).mapIso e).app
          (TopCat.of M)).toLinearEquiv)
  apply finsum_congr
  intro i
  rw [hfinrank i, downNatEulerSign_eq_negOnePow]

/-- Helper for Proposition 21.1.2: if the Betti numbers vanish above degree `n`, then the
chapter-local Euler characteristic is the finite alternating Betti sum up to degree `n`. -/
theorem manifoldEulerCharacteristic_eq_sum_range_of_bettiSupport (n : ℕ)
    (hvanish : ∀ i : ℕ, n < i → manifoldBettiNumber K i M = 0) :
    manifoldEulerCharacteristic K M =
      Finset.sum (Finset.range (n + 1)) fun i ↦
        Int.negOnePow i * (manifoldBettiNumber K i M : ℤ) := by
  let f : ℕ → ℤ := fun i ↦ Int.negOnePow i * (manifoldBettiNumber K i M : ℤ)
  have hsupport : Function.support f ⊆ Finset.range (n + 1) := by
    intro i hi
    by_contra hmem
    have hle : n + 1 ≤ i := by
      exact Nat.not_lt.mp (fun hlt ↦ hmem (Finset.mem_range.mpr hlt))
    have hni : n < i := lt_of_lt_of_le (Nat.lt_succ_self n) hle
    have hzero : f i = 0 := by
      simp [f, hvanish i hni]
    exact hi hzero
  -- First rewrite `χ(M)` as the chapter-local `finsum`, then truncate that support.
  rw [manifoldEulerCharacteristic_eq_finsum_betti]
  simpa [f] using finsum_eq_sum_of_support_subset f hsupport

/-- Helper for Proposition 21.1.2: any finite CW model computes the chapter-local Euler
characteristic. -/
theorem manifoldEulerCharacteristic_eq_cwEulerCharacteristic_of_homotopyEquiv
    {X : Type} [TopologicalSpace X] [CWComplex (Set.univ : Set X)]
    [CWComplex.Finite (Set.univ : Set X)] (e : M ≃ₕ X) :
    manifoldEulerCharacteristic K M = cwEulerCharacteristic (Set.univ : Set X) := by
  -- First move the singular-homology Euler characteristic across the chosen homotopy model.
  calc
    manifoldEulerCharacteristic K M =
        fieldTopologicalSingularHomologyEulerChar K (TopCat.of X) := by
          simpa [manifoldEulerCharacteristic] using
            singularHomologyEulerChar_eq_of_homotopyEquivMixed (k := K) e
    -- Then identify the field-homology Euler characteristic of the finite CW model with its
    -- intrinsic CW Euler characteristic.
    _ = cwEulerCharacteristic (Set.univ : Set X) := by
          simpa using
            (finiteCWEulerCharacteristic_eq_singularHomologyEulerChar (X := X) (k := K)).symm

/-- Helper for Proposition 21.1.2: the Chapter 20 constant-coefficient owner is canonically the
ordinary unit `K`-module. -/
private noncomputable def constantCoefficientModuleIsoUnit :
    constantCoefficientModule K ≅ ModuleCat.of K K :=
  LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift K ≃ₗ[K] K)

/-- Helper for Proposition 21.1.2: the Chapter 20 owner `rSingularHomology K i` is canonically
the Chapter 21 Betti-number owner in degree `i`. -/
private noncomputable def rSingularHomologyIsoManifoldBettiOwner (i : ℕ) :
    rSingularHomology K i (TopCat.of M) ≅
      ((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj (TopCat.of M) :=
  (((singularHomologyFunctor (ModuleCat K) i).mapIso constantCoefficientModuleIsoUnit).app
    (TopCat.of M))

/-- Helper for Proposition 21.1.2: transporting along the constant-coefficient comparison turns
the Chapter 20 homology owner into the chapter-local Betti number. -/
theorem finrank_rSingularHomology_eq_manifoldBettiNumber (i : ℕ) :
    Module.finrank K (rSingularHomology K i (TopCat.of M)) = manifoldBettiNumber K i M := by
  -- Compare the two homology owners by the canonical constant-coefficient/unit-module isomorphism.
  simpa [manifoldBettiNumber] using
    LinearEquiv.finrank_eq (rSingularHomologyIsoManifoldBettiOwner (K := K) (M := M) i).toLinearEquiv

/-- Helper for Proposition 21.1.2: the Chapter 20 constant `ℤ`-coefficient owner is the ordinary
integral unit module. -/
private noncomputable def constantCoefficientModuleIsoInt :
    constantCoefficientModule ℤ ≅ ModuleCat.of ℤ ℤ :=
  LinearEquiv.toModuleIso (ULift.moduleEquiv : ULift ℤ ≃ₗ[ℤ] ℤ)

/-- Helper for Proposition 21.1.2: ordinary integral singular homology agrees with the Chapter 20
owner `rSingularHomology ℤ`. -/
private noncomputable def integralSingularHomologyIsoRSingularHomology
    (X : TopCat) (i : ℕ) :
    integralSingularHomology i X ≅ rSingularHomology ℤ i X := by
  -- Compare the two integral owners by the same constant-coefficient/unit-module identification.
  simpa [integralSingularHomology, rSingularHomology] using
    (((singularHomologyFunctor (ModuleCat ℤ) i).mapIso constantCoefficientModuleIsoInt).app X).symm

/-- Helper for Proposition 21.1.2: the singular simplicial set of `X` in degree `i`. -/
private abbrev proposition21SingularSSetSimplex (X : TopCat) (i : ℕ) : Type _ :=
  (TopCat.toSSet.obj X) _⦋i⦌

/-- Helper for Proposition 21.1.2: in degree `i`, the unit-owner `K` singular chain group is the
coproduct of one copy of `K` for each singular `i`-simplex. -/
private noncomputable def unitSingularChainDegreeIsoCoproduct
    (X : TopCat) (i : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat K)).obj (ModuleCat.of K K)).obj X).X i) ≅
      ∐ fun _ : singularSimplex i X ↦ ModuleCat.of K K :=
  -- First expose the simplicial-set coproduct model, then reindex by continuous simplices.
  (eqToIso rfl) ≪≫
    show (∐ fun _ : proposition21SingularSSetSimplex X i ↦ ModuleCat.of K K) ≅
        ∐ fun _ : singularSimplex i X ↦ ModuleCat.of K K from
      Limits.Sigma.whiskerEquiv (singularSimplexEquiv i X)
        (fun _ ↦ Iso.refl (ModuleCat.of K K))

/-- Helper for Proposition 21.1.2: restricting scalars along `ℤ → K` reflects zero objects for
`K`-module owners, because the underlying carrier type is unchanged. -/
private theorem fieldModule_isZero_of_restrictScalars
    (A : ModuleCat K)
    (hA : IsZero ((ModuleCat.restrictScalars (Int.castRingHom K)).obj A)) :
    IsZero A := by
  -- First forget from `K` to `ℤ`, so zero-object information becomes a subsingleton statement.
  have hsub : Subsingleton A := by
    simpa using (ModuleCat.isZero_iff_subsingleton.mp hA)
  let _ : Subsingleton A := hsub
  -- Then repackage the unchanged carrier as a zero object back in `ModuleCat K`.
  exact ModuleCat.isZero_of_subsingleton A

/-- Helper for Proposition 21.1.2: after restricting scalars to `ℤ`, the Chapter 20
constant-coefficient `K` homology owner agrees with the chapter-local unit-coefficient owner. -/
private noncomputable def fieldRestrictedCoefficientHomologyIsoManifoldBettiOwner (i : ℕ) :
    ((ModuleCat.restrictScalars (Int.castRingHom K)).obj
        (rSingularHomology K i (TopCat.of M))) ≅
      ((ModuleCat.restrictScalars (Int.castRingHom K)).obj
        (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
          (TopCat.of M))) := by
  -- Restrict scalars so both `K`-linear homology owners live in the common category `ModuleCat ℤ`.
  simpa using
    ((ModuleCat.restrictScalars (Int.castRingHom K)).mapIso
      (rSingularHomologyIsoManifoldBettiOwner (K := K) (M := M) i))

/-- Helper for Proposition 21.1.2: vanishing of the exact Chapter 21 Betti owner forces the Betti
number itself to be zero. -/
private theorem manifoldBettiNumber_eq_zero_of_isZeroOwner (i : ℕ)
    (hzero :
      IsZero
        (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj (TopCat.of M))) :
    manifoldBettiNumber K i M = 0 := by
  -- Convert zero-object information into a subsingleton owner before taking the finite rank.
  let _ :
      Subsingleton
        (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
          (TopCat.of M)) :=
    ModuleCat.subsingleton_of_isZero hzero
  -- Then the finite-rank owner definition collapses immediately.
  simpa [manifoldBettiNumber] using
    (Module.finrank_eq_zero_of_subsingleton
      (R := K)
      (M := (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
        (TopCat.of M))))

/-- Helper for Proposition 21.1.2: the empty coproduct of copies of the unit `K`-module is a
zero object. -/
private theorem emptyUnitCoefficientCoproduct_isZero :
    IsZero (∐ fun _ : TopCat.of PEmpty ↦ ModuleCat.of K K) := by
  -- The indexing category is empty, so its coproduct is initial and hence zero.
  let diagram : Discrete (TopCat.of PEmpty) ⥤ ModuleCat K :=
    Discrete.functor (fun _ : TopCat.of PEmpty ↦ ModuleCat.of K K)
  let hinit : IsInitial (∐ fun _ : TopCat.of PEmpty ↦ ModuleCat.of K K) :=
    (@CategoryTheory.Limits.isColimitEquivIsInitialOfIsEmpty (ModuleCat K) _ _ _ _ _
      (colimit.cocone diagram)).toFun (colimit.isColimit diagram)
  exact hinit.isZero

/-- Helper for Proposition 21.1.2: the degree-zero unit-coefficient singular homology of the empty
space vanishes because the point-indexed coproduct in the totally disconnected computation is
empty. -/
private theorem unitCoefficientHomologyPEmpty_zero :
    IsZero
      (((singularHomologyFunctor (ModuleCat K) 0).obj (ModuleCat.of K K)).obj
        (TopCat.of PEmpty)) := by
  -- Compute `H₀(PEmpty; K)` as the coproduct of one copy of `K` for each point of `PEmpty`.
  exact
    IsZero.of_iso
      (emptyUnitCoefficientCoproduct_isZero (K := K))
      (singularHomologyFunctorZeroOfTotallyDisconnectedSpace
        (C := ModuleCat K) (R := ModuleCat.of K K) (X := TopCat.of PEmpty))

/-- Helper for Proposition 21.1.2: every unit-coefficient singular homology owner of an empty
space is zero. -/
private theorem unitCoefficientHomology_isZero_of_isEmpty (i : ℕ) [IsEmpty M] :
    IsZero
      (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
        (TopCat.of M)) := by
  -- Compare the empty manifold with `PEmpty`, where totally disconnectedness computes homology.
  let e : TopCat.of M ≅ TopCat.of PEmpty :=
    TopCat.isoOfHomeo (Homeomorph.empty : M ≃ₜ PEmpty)
  by_cases hi0 : i = 0
  · subst hi0
    exact
      IsZero.of_iso
        (unitCoefficientHomologyPEmpty_zero (K := K))
        (((singularHomologyFunctor (ModuleCat K) 0).obj (ModuleCat.of K K)).mapIso e)
  · have hPEmpty :
        IsZero
          (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
            (TopCat.of PEmpty)) := by
      -- Positive-degree singular homology of a totally disconnected space vanishes.
      simpa using
        (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
          (C := ModuleCat K) (n := i) (R := ModuleCat.of K K) (X := TopCat.of PEmpty) hi0)
    exact
      IsZero.of_iso
        hPEmpty
        (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).mapIso e)

/-- Helper for Proposition 21.1.2: every Betti number of an empty manifold vanishes. -/
private theorem manifoldBettiNumber_eq_zero_of_isEmpty (i : ℕ) [IsEmpty M] :
    manifoldBettiNumber K i M = 0 := by
  -- First show the exact Betti owner is zero, then collapse the finite-rank definition.
  exact
    manifoldBettiNumber_eq_zero_of_isZeroOwner
      (K := K) (M := M) i
      (unitCoefficientHomology_isZero_of_isEmpty (K := K) (M := M) i)

/-- Helper for Proposition 21.1.2: an integral orientation determines a compatible integral
fundamental class on the same compact manifold. -/
theorem existsIntegralCompatibleFundamentalClass_of_orientedLocal {n : ℕ}
    [Fact (Module.finrank ℝ E = n)]
    (h_oriented : Nonempty (ROrientedManifold ℤ I n M)) :
    ∃ o : ROrientedManifold ℤ I n M,
      ∃ z : rSingularHomology ℤ n (TopCat.of M), IsRFundamentalClassFor o z := by
  rcases h_oriented with ⟨o⟩
  -- Choose the unique integral fundamental class attached to the given global orientation.
  rcases
      existsUnique_rFundamentalClassFor_of_rOrientedManifold
        (ROrientedManifold.toGlobalOrientation o) with
    ⟨z, hz, _⟩
  -- Then unpack the global-orientation witness to recover a representative oriented atlas.
  rcases (isRFundamentalClassForGlobalOrientation_iff _ _).mp hz with ⟨o', -, hz'⟩
  exact ⟨o', z, hz'⟩

/-- Helper for Proposition 21.1.2: an integral orientation gives an intrinsic integral
fundamental class. -/
theorem existsIntegralFundamentalClass_of_orientedLocal {n : ℕ}
    [Fact (Module.finrank ℝ E = n)]
    (h_oriented : Nonempty (ROrientedManifold ℤ I n M)) :
    ∃ z : rSingularHomology ℤ n (TopCat.of M), IsRFundamentalClass ℤ n M z := by
  -- First choose a compatible oriented atlas and its integral fundamental class.
  rcases
      existsIntegralCompatibleFundamentalClass_of_orientedLocal
        (E := E) (I := I) (M := M) h_oriented with
    ⟨o, z, hz⟩
  -- Then forget the chosen atlas and keep only the intrinsic fundamental-class condition.
  exact ⟨z, hz.isRFundamentalClass⟩

/-- Helper for Proposition 21.1.2: an isomorphism on the degree-`i` cap-with-fundamental-class
map identifies the degree-`i` cohomology owner with the complementary Betti owner. -/
private theorem cohomologyFinrank_eq_complementaryManifoldBettiNumber_of_capIsIso
    {n i : ℕ}
    {z : rSingularHomology K n (TopCat.of M)}
    [hcap : IsIso (ModuleCat.ofHom (capWithFundamentalClass z i))] :
    Module.finrank K (rSingularCohomology K (TopCat.of M) i) =
      manifoldBettiNumber K (n - i) M := by
  -- TODO: compose the cap-product isomorphism with the field universal-coefficient comparison
  -- from unit-coefficient homology to the ordinary singular-homology owner.
  sorry

/-- Helper for Proposition 21.1.2: a compatible field-coefficient fundamental class gives equal
finite ranks in complementary cohomological degrees. -/
private theorem cohomologyFinrank_eq_complementaryCohomology_of_isRFundamentalClassFor
    {n i : ℕ} [Fact (Module.finrank ℝ E = n)]
    {o : ROrientedManifold K I n M}
    {z : rSingularHomology K n (TopCat.of M)}
    (hz : IsRFundamentalClassFor o z) (hi : i ≤ n) :
    Module.finrank K (rSingularCohomology K (TopCat.of M) i) =
      Module.finrank K (rSingularCohomology K (TopCat.of M) (n - i)) := by
  -- The Chapter 20 perfect pairing is the finite-rank comparison input on cohomology.
  let _ :
      (poincareDualityCohomologyPairing z i hi).IsPerfPair :=
    poincareDualityCohomologyPairing_isPerfPair_of_isRFundamentalClassFor o z hz i hi
  let _ : Module.IsReflexive K (rSingularCohomology K (TopCat.of M) i) :=
    Module.IsReflexive.of_isPerfPair (poincareDualityCohomologyPairing z i hi)
  -- A perfect pairing over a field forces the two cohomology owners to have equal finite rank.
  simpa using
    (Module.finrank_of_isPerfPair
      (p := poincareDualityCohomologyPairing z i hi))

/-- Helper for Proposition 21.1.2: once the source-facing cap-with-fundamental-class family is
known to satisfy the Chapter 20 local-coefficient Poincare-duality specification, each degreewise
cap map is an isomorphism. -/
private theorem capWithFundamentalClass_isIso_of_isLocalCoefficientPoincareDualityMap
    {n : ℕ} [Fact (Module.finrank ℝ E = n)]
    {o : ROrientedManifold K I n M}
    {z : rSingularHomology K n (TopCat.of M)}
    (hdual :
      IsLocalCoefficientPoincareDualityMap o
        ((Functor.const (FundamentalGroupoid M)).obj (ModuleCat.of K K))
        z
        (fun p ↦ rSingularCohomology K (TopCat.of M) p)
        (fun q ↦ singularHomologyWithCoefficients K (TopCat.of M) (ModuleCat.of K K) q)
        (fun p ↦ ModuleCat.ofHom (capWithFundamentalClass z p))) :
    ∀ p : ℕ, IsIso (ModuleCat.ofHom (capWithFundamentalClass z p)) := by
  intro p
  -- Apply the Chapter 20 duality API directly to the degree-`p` cap map.
  exact
    isIso_of_isLocalCoefficientPoincareDualityMap
      o
      ((Functor.const (FundamentalGroupoid M)).obj (ModuleCat.of K K))
      z
      (fun p ↦ rSingularCohomology K (TopCat.of M) p)
      (fun q ↦ singularHomologyWithCoefficients K (TopCat.of M) (ModuleCat.of K K) q)
      (fun p ↦ ModuleCat.ofHom (capWithFundamentalClass z p))
      hdual
      p

/-- Helper for Proposition 21.1.2: once a field-valued fundamental class and a matching
source-facing Chapter 20 duality witness are available, the orientable branch gets both a
compatible `K`-orientation and the resulting cap-product isomorphisms. -/
private theorem fieldCoefficientCapDualitySetup_of_fieldFundamentalClass
    {n : ℕ} [Fact (Module.finrank ℝ E = n)]
    {zK : rSingularHomology K n (TopCat.of M)}
    (hzGlobal : IsRFundamentalClass K n M zK)
    (hdual :
      ∀ ⦃oK : ROrientedManifold K I n M⦄,
        IsRFundamentalClassFor oK zK →
          IsLocalCoefficientPoincareDualityMap oK
            ((Functor.const (FundamentalGroupoid M)).obj (ModuleCat.of K K))
            zK
            (fun p ↦ rSingularCohomology K (TopCat.of M) p)
            (fun q ↦ singularHomologyWithCoefficients K (TopCat.of M) (ModuleCat.of K K) q)
            (fun p ↦ ModuleCat.ofHom (capWithFundamentalClass zK p))) :
    ∃ oK : ROrientedManifold K I n M,
      IsRFundamentalClassFor oK zK ∧
        ∀ p : ℕ, IsIso (ModuleCat.ofHom (capWithFundamentalClass zK p)) := by
  -- First recover a compatible field orientation from the intrinsic field fundamental class.
  rcases exists_rOrientedManifold_of_isRFundamentalClass (I := I) hzGlobal with ⟨oK, hzK⟩
  refine ⟨oK, hzK, ?_⟩
  -- Then the source-facing duality witness upgrades capping with `zK` to an isomorphism.
  exact
    capWithFundamentalClass_isIso_of_isLocalCoefficientPoincareDualityMap
      (K := K) (E := E) (I := I) (M := M) (o := oK) (z := zK) (hdual hzK)

/-- Helper for Proposition 21.1.2: from an integral orientation, the orientable branch only needs
a compatible field-valued fundamental class and the resulting cap-product isomorphisms. -/
private theorem fieldFundamentalClass_of_integralFundamentalClass {n : ℕ}
    [Fact (Module.finrank ℝ E = n)]
    {zZ : rSingularHomology ℤ n (TopCat.of M)}
    (hzZ : IsRFundamentalClass ℤ n M zZ) :
    ∃ zK : rSingularHomology K n (TopCat.of M), IsRFundamentalClass K n M zK := by
  -- TODO: rewrite `IsRFundamentalClass` with `isRFundamentalClass_iff`, transport `zZ` through
  -- the coefficient-change morphism on absolute homology, and compare each local image via the
  -- corresponding coefficient-change map on `localTopHomologyGroup`.
  sorry

/-- Helper for Proposition 21.1.2: a compatible field-valued fundamental class gives the
source-facing Chapter 20 cap-product duality package needed to deduce that each cap map is an
isomorphism. -/
private theorem capWithFundamentalClass_isLocalCoefficientPoincareDualityMap_of_isRFundamentalClassFor
    {n : ℕ} [Fact (Module.finrank ℝ E = n)]
    {o : ROrientedManifold K I n M}
    {z : rSingularHomology K n (TopCat.of M)}
    (hM : Nonempty M)
    (hz : IsRFundamentalClassFor o z) :
    IsLocalCoefficientPoincareDualityMap o
      ((Functor.const (FundamentalGroupoid M)).obj (ModuleCat.of K K))
      z
      (fun p ↦ rSingularCohomology K (TopCat.of M) p)
      (fun q ↦ singularHomologyWithCoefficients K (TopCat.of M) (ModuleCat.of K K) q)
      (fun p ↦ ModuleCat.ofHom (capWithFundamentalClass z p)) := by
  -- Route correction: the source-facing Chapter 20 specification is based, so this helper must
  -- carry the nonemptiness hypothesis needed to choose the basepoint `x : M`.
  let _ := hM
  -- TODO: choose the based universal-cover chain model and comparison isomorphisms witnessing the
  -- Chapter 20 duality package for `z`, then identify the transported local-coefficient map with
  -- the source-facing `capWithFundamentalClass`.
  sorry

/-- Helper for Proposition 21.1.2: from an integral orientation, the orientable branch only needs
a compatible field-valued fundamental class and the resulting cap-product isomorphisms. -/
private theorem fieldCoefficientCapDualitySetup_of_orientedLocal {n : ℕ}
    [Fact (Module.finrank ℝ E = n)]
    (hM : Nonempty M)
    (h_oriented : Nonempty (ROrientedManifold ℤ I n M)) :
    ∃ oK : ROrientedManifold K I n M,
      ∃ zK : rSingularHomology K n (TopCat.of M),
        IsRFundamentalClassFor oK zK ∧
          ∀ p : ℕ, IsIso (ModuleCat.ofHom (capWithFundamentalClass zK p)) := by
  let _ := hM
  rcases
      existsIntegralFundamentalClass_of_orientedLocal
        (E := E) (I := I) (M := M) h_oriented with
    ⟨zZ, hzZ⟩
  rcases
      fieldFundamentalClass_of_integralFundamentalClass
        (K := K) (E := E) (M := M) hzZ with
    ⟨zK, hzK⟩
  -- Route correction: the remaining orientable input is now isolated to the two dedicated
  -- bridges, namely coefficient-change for the intrinsic fundamental class and the source-facing
  -- cap-duality witness for that field-valued class.
  have hsetup :=
    fieldCoefficientCapDualitySetup_of_fieldFundamentalClass
      (K := K) (E := E) (I := I) (M := M) hzK (by
        intro oK hoK
        exact
          capWithFundamentalClass_isLocalCoefficientPoincareDualityMap_of_isRFundamentalClassFor
            (K := K) (E := E) (I := I) (M := M) hM hoK)
  rcases hsetup with ⟨oK, hzKFor, hcap⟩
  exact ⟨oK, zK, hzKFor, hcap⟩

/-- Helper for Proposition 21.1.2: on a compact oriented `n`-manifold, the degree-`i`
cohomology owner has the same finite rank as the complementary Betti number `β_{n-i}`. -/
theorem cohomologyFinrank_eq_complementaryManifoldBettiNumber_of_orientedLocal {n i : ℕ}
    [Fact (Module.finrank ℝ E = n)]
    (hM : Nonempty M) (h_oriented : Nonempty (ROrientedManifold ℤ I n M)) (hi : i ≤ n) :
    Module.finrank K (rSingularCohomology K (TopCat.of M) i) =
      manifoldBettiNumber K (n - i) M := by
  -- Route correction: the proposition only needs the complementary-degree cap-duality bridge
  -- `dim H^i(M; K) = β_{n-i}(M)`, not a same-degree cohomology/homology comparison.
  rcases
      fieldCoefficientCapDualitySetup_of_orientedLocal
        (K := K) (E := E) (I := I) (M := M) hM h_oriented with
    ⟨oK, zK, hzK, hcap⟩
  -- Once the compatible field class is chosen, the complementary-degree cap isomorphism closes
  -- the finite-rank comparison immediately.
  let _ : IsIso (ModuleCat.ofHom (capWithFundamentalClass zK i)) := hcap i
  let _ := oK
  let _ := hzK
  exact
    cohomologyFinrank_eq_complementaryManifoldBettiNumber_of_capIsIso
      (K := K) (M := M) (n := n) (i := i) (z := zK)

/-- Helper for Proposition 21.1.2: any chosen-model comparison theorem transports the absolute
dimension-vanishing statement of Theorem 20.3.2 to the corresponding degreewise homology owner. -/
private theorem localCoefficientHomology_isZero_of_gt_dimension_of_computesHomology
    {n i : ℕ} [Fact (Module.finrank ℝ E = n)]
    (π : FundamentalGroupoid M ⥤ ModuleCat ℤ) {x : M}
    (C : ChosenUniversalCoverChainModel π x)
    (Hπ : ℕ → ModuleCat ℤ)
    (hHπ : C.ComputesHomology Hπ) (hi : n < i) :
    IsZero (Hπ i) := by
  -- This is exactly the absolute dimension cutoff furnished by Theorem 20.3.2.
  exact
    isZero_localCoefficientHomology_of_lt
      π C Hπ hHπ hi

/-- Helper for Proposition 21.1.2: once the constant local-system owner is compared with the
restricted-scalar image of the Chapter 21 unit-coefficient owner, the absolute dimension cutoff
forces the Betti owner to vanish. -/
private theorem unitCoefficientHomology_isZero_of_integralCoefficientIso
    {i : ℕ}
    (hzero :
      IsZero
        (singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ K) i))
    (hcompare :
      singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ K) i ≅
        ((ModuleCat.restrictScalars (Int.castRingHom K)).obj
          (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
            (TopCat.of M)))) :
    IsZero
      (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
        (TopCat.of M)) := by
  have hRestrict :
      IsZero
        ((ModuleCat.restrictScalars (Int.castRingHom K)).obj
          (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
            (TopCat.of M))) :=
    -- First transport the zero owner across the explicit integral-to-unit comparison.
    IsZero.of_iso hzero hcompare.symm
  -- Then reflect zero-object information back across restriction of scalars.
  exact
    fieldModule_isZero_of_restrictScalars
      ((((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
        (TopCat.of M)))
      hRestrict

/-- Helper for Proposition 21.1.2: once the constant local-system owner is compared with the
restricted-scalar image of the Chapter 21 unit-coefficient owner, the absolute dimension cutoff
forces the Betti owner to vanish. -/
private theorem unitCoefficientHomology_isZero_of_gt_dimension_of_integralComparison
    {n i : ℕ} [Fact (Module.finrank ℝ E = n)] {x : M}
    (C :
      ChosenUniversalCoverChainModel
        ((Functor.const (FundamentalGroupoid M)).obj (ModuleCat.of ℤ K)) x)
    (hHπ :
      C.ComputesHomology
        (fun q ↦ singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ K) q))
    (hcompare :
      singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ K) i ≅
        ((ModuleCat.restrictScalars (Int.castRingHom K)).obj
          (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
            (TopCat.of M))))
    (hi : n < i) :
    IsZero
      (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
        (TopCat.of M)) := by
  have hCoeff :
      IsZero
        (singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ K) i) :=
    localCoefficientHomology_isZero_of_gt_dimension_of_computesHomology
      (E := E) (M := M)
      (n := n) (i := i)
      (π := (Functor.const (FundamentalGroupoid M)).obj (ModuleCat.of ℤ K))
      C
      (fun q ↦ singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ K) q)
      hHπ
      hi
  -- Route correction: isolate the restricted-scalar transport into a dedicated helper before
  -- using the absolute dimension cutoff.
  exact
    unitCoefficientHomology_isZero_of_integralCoefficientIso
      (K := K) (M := M) hCoeff hcompare

/-- Helper for Proposition 21.1.2: the Betti numbers of a compact `n`-manifold vanish above
degree `n`. -/
private noncomputable def constantIntegralLocalSystemComputesHomology (x : M) :
    Σ C :
        ChosenUniversalCoverChainModel
          ((Functor.const (FundamentalGroupoid M)).obj (ModuleCat.of ℤ K)) x,
      C.ComputesHomology
        (fun q ↦ singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ K) q) := by
  -- TODO: choose the Chapter 20 based universal-cover chain model for the constant local system
  -- at `x`, then identify its homology owner with
  -- `singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ K)` degreewise.
  sorry

/-- Helper for Proposition 21.1.2: integral singular homology with coefficients in the constant
`ℤ`-module `K` agrees, after restricting scalars, with the exact Chapter 21 unit-coefficient
Betti owner. -/
private noncomputable def integralCoefficientHomologyIsoRestrictedUnitCoefficientHomology (i : ℕ) :
    singularHomologyWithCoefficients ℤ (TopCat.of M) (ModuleCat.of ℤ K) i ≅
      ((ModuleCat.restrictScalars (Int.castRingHom K)).obj
        (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
          (TopCat.of M))) := by
  -- TODO: compare the constant-`ℤ` coefficient chain complex with the restricted Chapter 21
  -- unit-coefficient chain complex and pass the resulting chain-level identification to homology.
  sorry

/-- Helper for Proposition 21.1.2: the Betti numbers of a compact `n`-manifold vanish above
degree `n`. -/
private theorem unitCoefficientHomology_isZero_of_gt_dimension {n i : ℕ}
    [Fact (Module.finrank ℝ E = n)] (hM : Nonempty M) (hi : n < i) :
    IsZero
      (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj (TopCat.of M)) := by
  classical
  rcases hM with ⟨x⟩
  rcases
      constantIntegralLocalSystemComputesHomology
        (K := K) (M := M) x with
    ⟨C, hHπ⟩
  -- Route correction: the dimension-vanishing step is now reduced to two explicit owner bridges,
  -- namely the chosen-model computation for the constant local system and the degreewise
  -- restricted-scalar comparison back to the Chapter 21 Betti owner.
  exact
    unitCoefficientHomology_isZero_of_gt_dimension_of_integralComparison
      (K := K) (E := E) (M := M) (n := n) (i := i)
      C
      hHπ
      (integralCoefficientHomologyIsoRestrictedUnitCoefficientHomology
        (K := K) (M := M) i)
      hi

/-- Helper for Proposition 21.1.2: the Betti numbers of a compact `n`-manifold vanish above
degree `n`. -/
theorem manifoldBettiNumber_eq_zero_of_gt_dimension {n i : ℕ}
    [Fact (Module.finrank ℝ E = n)] (hi : n < i) : manifoldBettiNumber K i M = 0 := by
  classical
  by_cases hM : Nonempty M
  · -- In the nonempty case, the remaining work is exactly the chosen-model transport blocker.
    have hzero :
        IsZero
          (((singularHomologyFunctor (ModuleCat K) i).obj (ModuleCat.of K K)).obj
            (TopCat.of M)) :=
    unitCoefficientHomology_isZero_of_gt_dimension
        (K := K) (E := E) (M := M) hM hi
    -- Once the owner vanishes, the Betti number is definitionally zero.
    exact manifoldBettiNumber_eq_zero_of_isZeroOwner (K := K) (M := M) i hzero
  · -- Empty manifolds have no singular homology in any degree.
    have hEmpty : IsEmpty M := not_nonempty_iff.mp hM
    let _ : IsEmpty M := hEmpty
    exact manifoldBettiNumber_eq_zero_of_isEmpty (K := K) (M := M) i

/-- Helper for Proposition 21.1.2: Poincare duality identifies complementary Betti numbers on a
compact oriented `n`-manifold. -/
theorem manifoldBettiNumber_symm_of_orientedLocal {n i : ℕ}
    [Fact (Module.finrank ℝ E = n)]
    (hM : Nonempty M) (h_oriented : Nonempty (ROrientedManifold ℤ I n M)) (hi : i ≤ n) :
    manifoldBettiNumber K i M = manifoldBettiNumber K (n - i) M := by
  -- Route correction: compare `β_i` and `β_{n-i}` through the complementary-degree cap bridge
  -- at degrees `i` and `n - i`, then use the perfect pairing on cohomology to match those
  -- two cohomology finite ranks.
  rcases
      fieldCoefficientCapDualitySetup_of_orientedLocal
        (K := K) (E := E) (I := I) (M := M) hM h_oriented with
    ⟨oK, zK, hzK, hcap⟩
  have hleft :
      Module.finrank K (rSingularCohomology K (TopCat.of M) i) =
        manifoldBettiNumber K (n - i) M := by
    -- First use the degree-`i` cap isomorphism to compare cohomology with the complementary Betti
    -- owner.
    let _ : IsIso (ModuleCat.ofHom (capWithFundamentalClass zK i)) := hcap i
    exact
      cohomologyFinrank_eq_complementaryManifoldBettiNumber_of_capIsIso
        (K := K) (M := M) (n := n) (i := i) (z := zK)
  have hright :
      Module.finrank K (rSingularCohomology K (TopCat.of M) (n - i)) =
        manifoldBettiNumber K i M := by
    -- Then repeat the same cap-isomorphism comparison in complementary degree.
    let _ : IsIso (ModuleCat.ofHom (capWithFundamentalClass zK (n - i))) := hcap (n - i)
    simpa [Nat.sub_sub_self hi] using
      (cohomologyFinrank_eq_complementaryManifoldBettiNumber_of_capIsIso
        (K := K) (M := M) (n := n) (i := n - i) (z := zK))
  have hcoh :
      Module.finrank K (rSingularCohomology K (TopCat.of M) i) =
        Module.finrank K (rSingularCohomology K (TopCat.of M) (n - i)) :=
    cohomologyFinrank_eq_complementaryCohomology_of_isRFundamentalClassFor
      (K := K) (E := E) (I := I) (M := M) (o := oK) (z := zK) hzK hi
  -- Reassemble the two Betti numbers from the cap-duality bridge and the cohomology symmetry.
  calc
    manifoldBettiNumber K i M =
        Module.finrank K (rSingularCohomology K (TopCat.of M) (n - i)) := hright.symm
    _ = Module.finrank K (rSingularCohomology K (TopCat.of M) i) := hcoh.symm
    _ = manifoldBettiNumber K (n - i) M := hleft

/-- Helper for Proposition 21.1.2: an odd-length alternating sum vanishes when complementary
terms agree. -/
theorem pairedAlternatingSum_eq_zero_of_oddSymmetry (b : ℕ → ℤ) :
    ∀ m : ℕ,
      (∀ i : ℕ, i ≤ 2 * m + 1 → b i = b (2 * m + 1 - i)) →
      (Finset.sum (Finset.range (2 * m + 2)) fun i ↦ Int.negOnePow i * b i) = 0 := by
  intro m hsymm
  let f : ℕ → ℤ := fun i ↦ Int.negOnePow i * b i
  let S : ℤ := ∑ j ∈ Finset.range (2 * m + 2), f j
  -- Reflect the finite range to pair the `j` and `2 * m + 1 - j` summands.
  have hreflect : S = ∑ j ∈ Finset.range (2 * m + 2), f (2 * m + 1 - j) := by
    simpa [S, f, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Finset.sum_range_reflect f (2 * m + 2)).symm
  -- Complementary odd-degree terms pick up a minus sign after reflection.
  have hneg : ∑ j ∈ Finset.range (2 * m + 2), f (2 * m + 1 - j) = -S := by
    calc
      ∑ j ∈ Finset.range (2 * m + 2), f (2 * m + 1 - j)
          = ∑ j ∈ Finset.range (2 * m + 2), -f j := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hj' : j ≤ 2 * m + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              have hterm :
                  Int.negOnePow (2 * m + 1 - j) * b (2 * m + 1 - j) =
                    -(Int.negOnePow j * b j) := by
                have hsign : ((Int.negOnePow (2 * m + 1 - j) : ℤ)) =
                    -((Int.negOnePow j : ℤ)) := by
                  rw [Int.negOnePow_sub, Int.negOnePow_add, Int.negOnePow_one]
                  simp
                rw [hsign, ← hsymm j hj']
                simp
              simpa [f, Nat.cast_sub hj'] using hterm
      _ = -S := by
            simpa [S] using
              (Finset.sum_neg_distrib :
                (∑ j ∈ Finset.range (2 * m + 2), -f j) =
                  -∑ j ∈ Finset.range (2 * m + 2), f j)
  -- The reflected sum is both `S` and `-S`, so the alternating sum vanishes.
  have hs : S = -S := hreflect.trans hneg
  have hsum : S + S = 0 := by
    calc
      S + S = S + (-S) := congrArg (fun t : ℤ => S + t) hs
      _ = 0 := by simp
  have htwo : (2 : ℤ) * S = 0 := by
    simpa [two_mul] using hsum
  have hS : S = 0 := (Int.mul_eq_zero.mp htwo).resolve_left (by norm_num)
  simpa [S, f] using hS

/-- Helper for Proposition 21.1.2: pairing complementary terms in an even-length alternating sum
isolates the middle degree. -/
theorem pairedAlternatingSum_eq_evenFormula_of_evenSymmetry (b : ℕ → ℤ) :
    ∀ m : ℕ,
      (∀ i : ℕ, i ≤ 2 * m → b i = b (2 * m - i)) →
      (Finset.sum (Finset.range (2 * m + 1)) fun i ↦ Int.negOnePow i * b i) =
        2 * (Finset.sum (Finset.range m) fun i ↦ Int.negOnePow i * b i) + Int.negOnePow m * b m := by
  intro m hsymm
  let f : ℕ → ℤ := fun i ↦ Int.negOnePow i * b i
  have hmUpper : m + 1 ≤ 2 * m + 1 := by
    simp [two_mul, add_assoc]
  -- Split the full sum into the lower half, the middle term, and the upper half.
  have hsplit :
      (∑ i ∈ Finset.range (2 * m + 1), f i) =
        (∑ i ∈ Finset.range m, f i) + f m +
          ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), f i := by
    calc
      ∑ i ∈ Finset.range (2 * m + 1), f i =
          ∑ i ∈ Finset.Ico 0 (2 * m + 1), f i := by simp
      _ =
          (∑ i ∈ Finset.Ico 0 (m + 1), f i) +
            ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), f i := by
              symm
              exact Finset.sum_Ico_consecutive f (Nat.zero_le (m + 1)) hmUpper
      _ =
          (∑ i ∈ Finset.Ico 0 m, f i) + f m +
            ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), f i := by
              rw [Finset.sum_Ico_succ_top (Nat.zero_le m)]
      _ =
          (∑ i ∈ Finset.range m, f i) + f m +
            ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), f i := by
              simp [Nat.Ico_zero_eq_range]
  -- Reflect the upper half back to the lower half.
  have hupper :
      (∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), f i) =
        ∑ i ∈ Finset.range m, f (2 * m - i) := by
    have hm : m ≤ 2 * m + 1 := by
      simp [two_mul, add_assoc]
    simpa [Nat.Ico_zero_eq_range, two_mul, add_assoc, add_left_comm, add_comm] using
      (Finset.sum_Ico_reflect f 0 (m := m) (n := 2 * m) hm).symm
  -- Even symmetry identifies those reflected terms with the lower half.
  have hupperSymm : (∑ i ∈ Finset.range m, f (2 * m - i)) = ∑ i ∈ Finset.range m, f i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have him : i ≤ 2 * m := by
      calc
        i ≤ m := Nat.le_of_lt (Finset.mem_range.mp hi)
        _ ≤ 2 * m := by simp [two_mul]
    have hterm : Int.negOnePow (2 * m - i) * b (2 * m - i) = Int.negOnePow i * b i := by
      have hsign : ((Int.negOnePow (2 * m - i) : ℤ)) = (Int.negOnePow i : ℤ) := by
        rw [Int.negOnePow_sub]
        simp
      rw [hsign, ← hsymm i him]
    simpa [f, Nat.cast_sub him] using hterm
  -- Reassemble the paired sum and isolate the middle degree.
  calc
    ∑ i ∈ Finset.range (2 * m + 1), f i =
        (∑ i ∈ Finset.range m, f i) + f m +
          ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), f i := hsplit
    _ = (∑ i ∈ Finset.range m, f i) + f m + ∑ i ∈ Finset.range m, f (2 * m - i) := by
          rw [hupper]
    _ = (∑ i ∈ Finset.range m, f i) + f m + ∑ i ∈ Finset.range m, f i := by
          rw [hupperSymm]
    _ = 2 * (∑ i ∈ Finset.range m, f i) + f m := by
          simp [two_mul, add_left_comm, add_comm]
    _ = 2 * (Finset.sum (Finset.range m) fun i ↦ Int.negOnePow i * b i) +
          Int.negOnePow m * b m := by
          simp [f]

/-- Helper for Proposition 21.1.2: once odd-dimensional Betti numbers vanish above degree
`2 * m + 1` and satisfy Poincare-style symmetry, the Euler characteristic is zero. -/
theorem manifoldEulerCharacteristic_eq_zero_of_oddDimension_of_bettiSupportSymm (m : ℕ)
    (hvanish : ∀ i : ℕ, 2 * m + 1 < i → manifoldBettiNumber K i M = 0)
    (hsymm :
      ∀ i : ℕ, i ≤ 2 * m + 1 →
        manifoldBettiNumber K i M = manifoldBettiNumber K (2 * m + 1 - i) M) :
    manifoldEulerCharacteristic K M = 0 := by
  -- Rewrite `χ(M)` as the finite odd-length alternating Betti sum.
  rw [manifoldEulerCharacteristic_eq_sum_range_of_bettiSupport
    (K := K) (M := M) (n := 2 * m + 1) hvanish]
  -- Then pair complementary degrees using the odd-symmetry cancellation lemma.
  exact pairedAlternatingSum_eq_zero_of_oddSymmetry
    (b := fun i ↦ (manifoldBettiNumber K i M : ℤ)) m (by
      intro i hi
      exact congrArg (fun x : ℕ ↦ (x : ℤ)) (hsymm i hi))

/-- Helper for Proposition 21.1.2: the odd-dimensional nonorientable branch should be handled
through the orientation cover or an equivalent covering/additivity comparison. -/
theorem manifoldEulerCharacteristic_eq_zero_of_oddDimension_of_nonorientable (m : ℕ)
    [Fact (Module.finrank ℝ E = 2 * m + 1)]
    (hM : Nonempty M)
    (h_nonorientable : ¬ Nonempty (ROrientedManifold ℤ I (2 * m + 1) M)) :
    manifoldEulerCharacteristic K M = 0 := by
  -- Route correction: once the nonempty orientable branch is stabilized, this last branch should
  -- be purely geometric.
  -- TODO: split `M` into connected components, pass each nonorientable component to its
  -- orientation cover, use `OrientationCover.connectedSpace_iff_nonorientable` and the two-sheet
  -- covering comparison to identify `2 * χ(component)`, and close each lifted component by the
  -- already established odd orientable argument.
  let _ := hM
  let _ := h_nonorientable
  sorry

include I

/-- Proposition 21.1.2 (1). If `M` is a compact manifold of odd dimension `2 * m + 1`, then
`χ(M) = 0`. Here `χ(M)` is formalized as `manifoldEulerCharacteristic K M`, computed from
singular homology with coefficients in the field `K`. -/
theorem manifoldEulerCharacteristic_eq_zero_of_oddDimension (m : ℕ)
    [Fact (Module.finrank ℝ E = 2 * m + 1)] :
    manifoldEulerCharacteristic K M = 0 := by
  classical
  by_cases hM : Nonempty M
  · by_cases h_oriented : Nonempty (ROrientedManifold ℤ I (2 * m + 1) M)
    · -- Route correction: once `M` is nonempty, the orientable odd branch is purely
      -- finite-support normalization plus complementary Betti symmetry.
      have hvanish : ∀ i : ℕ, 2 * m + 1 < i → manifoldBettiNumber K i M = 0 := by
        intro i hi
        exact manifoldBettiNumber_eq_zero_of_gt_dimension
          (K := K) (E := E) (M := M) hi
      have hsymm :
          ∀ i : ℕ, i ≤ 2 * m + 1 →
            manifoldBettiNumber K i M = manifoldBettiNumber K (2 * m + 1 - i) M := by
        intro i hi
        exact manifoldBettiNumber_symm_of_orientedLocal
          (K := K) (E := E) (I := I) (M := M) hM h_oriented hi
      -- The odd orientable case is now a pure alternating-sum cancellation argument.
      exact manifoldEulerCharacteristic_eq_zero_of_oddDimension_of_bettiSupportSymm
        (K := K) (M := M) m hvanish hsymm
    · -- The remaining geometric blocker is now isolated to the nonempty nonorientable branch.
      exact manifoldEulerCharacteristic_eq_zero_of_oddDimension_of_nonorientable
        (K := K) (E := E) (I := I) (M := M) m hM h_oriented
  · have hEmpty : IsEmpty M := not_nonempty_iff.mp hM
    let _ : IsEmpty M := hEmpty
    have hvanish : ∀ i : ℕ, 2 * m + 1 < i → manifoldBettiNumber K i M = 0 := by
      intro i _
      exact manifoldBettiNumber_eq_zero_of_isEmpty (K := K) (M := M) i
    have hsymm :
        ∀ i : ℕ, i ≤ 2 * m + 1 →
          manifoldBettiNumber K i M = manifoldBettiNumber K (2 * m + 1 - i) M := by
      intro i hi
      rw [manifoldBettiNumber_eq_zero_of_isEmpty (K := K) (M := M) i]
      rw [manifoldBettiNumber_eq_zero_of_isEmpty (K := K) (M := M) (2 * m + 1 - i)]
    -- Empty manifolds have vanishing Betti numbers in every degree, so the odd formula is trivial.
    exact manifoldEulerCharacteristic_eq_zero_of_oddDimension_of_bettiSupportSymm
      (K := K) (M := M) m hvanish hsymm

/-- Proposition 21.1.2 (2). If `M` is a compact oriented manifold of dimension `2 * m`, then
`χ(M) = 2 * ∑_{i < m} (-1)^i dim H_i(M) + (-1)^m dim H_m(M)`. Here `χ(M)` is formalized as
`manifoldEulerCharacteristic K M`, the dimensions are `manifoldBettiNumber K i M`, and
orientation is recorded by `Nonempty (ROrientedManifold ℤ I (2 * m) M)`. -/
theorem manifoldEulerCharacteristic_eq_evenDimensionFormula_of_oriented (m : ℕ)
    [Fact (Module.finrank ℝ E = 2 * m)]
    (h_oriented : Nonempty (ROrientedManifold ℤ I (2 * m) M)) :
    manifoldEulerCharacteristic K M =
      2 * (Finset.sum (Finset.range m)
        fun i ↦ Int.negOnePow i * (manifoldBettiNumber K i M : ℤ)) +
        Int.negOnePow m * (manifoldBettiNumber K m M : ℤ) := by
  classical
  by_cases hM : Nonempty M
  · have hvanish : ∀ i : ℕ, 2 * m < i → manifoldBettiNumber K i M = 0 := by
      -- Reduce the local vanishing claim to the dedicated dimension-vanishing helper.
      intro i hi
      exact manifoldBettiNumber_eq_zero_of_gt_dimension (K := K) (E := E) (M := M) hi
    have hsymm :
        ∀ i : ℕ, i ≤ 2 * m → manifoldBettiNumber K i M = manifoldBettiNumber K (2 * m - i) M := by
      -- Reduce the local symmetry claim to the oriented Poincare-duality helper.
      intro i hi
      exact manifoldBettiNumber_symm_of_orientedLocal
        (K := K) (E := E) (I := I) (M := M) hM h_oriented hi
    -- Rewrite `χ(M)` as a finite alternating sum, then pair complementary degrees.
    rw [manifoldEulerCharacteristic_eq_sum_range_of_bettiSupport
      (K := K) (M := M) (n := 2 * m) hvanish]
    exact pairedAlternatingSum_eq_evenFormula_of_evenSymmetry
      (b := fun i ↦ (manifoldBettiNumber K i M : ℤ)) m (by
        intro i hi
        exact congrArg (fun x : ℕ ↦ (x : ℤ)) (hsymm i hi))
  · have hEmpty : IsEmpty M := not_nonempty_iff.mp hM
    let _ : IsEmpty M := hEmpty
    have hvanish : ∀ i : ℕ, 2 * m < i → manifoldBettiNumber K i M = 0 := by
      intro i _
      exact manifoldBettiNumber_eq_zero_of_isEmpty (K := K) (M := M) i
    have hsymm :
        ∀ i : ℕ, i ≤ 2 * m → manifoldBettiNumber K i M = manifoldBettiNumber K (2 * m - i) M := by
      intro i hi
      rw [manifoldBettiNumber_eq_zero_of_isEmpty (K := K) (M := M) i]
      rw [manifoldBettiNumber_eq_zero_of_isEmpty (K := K) (M := M) (2 * m - i)]
    -- Empty manifolds again reduce to the zero-valued even alternating-sum identity.
    rw [manifoldEulerCharacteristic_eq_sum_range_of_bettiSupport
      (K := K) (M := M) (n := 2 * m) hvanish]
    exact pairedAlternatingSum_eq_evenFormula_of_evenSymmetry
      (b := fun i ↦ (manifoldBettiNumber K i M : ℤ)) m (by
        intro i hi
        exact congrArg (fun x : ℕ ↦ (x : ℤ)) (hsymm i hi))

end
