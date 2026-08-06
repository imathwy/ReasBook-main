import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap14.HurewiczComparison
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Definition_19_2_1

open CategoryTheory
open HomotopicalAlgebra

noncomputable section

-- The local Chapter 19 reduced-cohomology API is organized around a chosen reduced suspension
-- functor on `nondegeneratelyBasedSpace`, so this corollary uses the iterated suspension owner
-- `Σ^n X` determined by that setup.

local notation "NBasedSpace" => nondegeneratelyBasedSpace

namespace ReducedSuspensionCofiberSetup

/-- An isomorphism in `NBasedSpace` induces an isomorphism of the underlying based spaces. -/
def objIso
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    {X Y : NBasedSpace} (e : X ≅ Y) :
    X.obj ≅ Y.obj where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := by
    exact congrArg (fun f : X ⟶ X ↦ f.hom) e.hom_inv_id
  inv_hom_id := by
    exact congrArg (fun f : Y ⟶ Y ↦ f.hom) e.inv_hom_id

/-- The `n`-fold reduced suspension `Σ^n X` determined by the chosen Chapter 19 suspension
endofunctor. -/
def iteratedSuspension
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (X : NBasedSpace) : ℕ → NBasedSpace
  | 0 => X
  | n + 1 => setup.suspension.obj (iteratedSuspension setup X n)

@[simp] theorem iteratedSuspension_zero
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (X : NBasedSpace) :
    setup.iteratedSuspension X 0 = X :=
  rfl

@[simp] theorem iteratedSuspension_succ
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (X : NBasedSpace) (n : ℕ) :
    setup.iteratedSuspension X (n + 1) =
      setup.suspension.obj (setup.iteratedSuspension X n) :=
  rfl

/-- Lean notation for the iterated reduced suspension determined by `setup`. -/
scoped notation "Σ[" setup "]^" n:max X:max =>
  ReducedSuspensionCofiberSetup.iteratedSuspension setup X n

end ReducedSuspensionCofiberSetup

open scoped ReducedSuspensionCofiberSetup

namespace ReducedSuspensionCofiberSetup

/-- A Chapter 19 comparison from the suspension tower `Σ[setup]^n sphereZero` to the repository's
canonical sphere owner `basedSphere n`. -/
structure SuspensionSphereComparison
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup) where
  /-- The chosen `S^0`-model at the bottom of the suspension tower. -/
  sphereZero : NBasedSpace
  /-- The underlying based space of the suspension tower `Σ[setup]^n sphereZero` is the
  repository's canonical sphere owner `basedSphere n`. -/
  suspensionSphereIso : ∀ n : ℕ, (Σ[setup]^n sphereZero).obj ≅ basedSphere n

/-- A bridge from chosen `NBasedSpace` models of `S^n` to a suspension-tower comparison with the
canonical spheres `basedSphere n`. -/
structure SphereComparison
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    extends setup.SuspensionSphereComparison where
  /-- The chosen `NBasedSpace` model of `S^n`. -/
  sphere : ℕ → NBasedSpace
  /-- Each chosen `S^n`-model is identified with the `n`-fold suspension `Σ[setup]^n sphereZero`.
  -/
  sphereToSuspension : ∀ n : ℕ, sphere n ≅ Σ[setup]^n sphereZero

namespace SuspensionSphereComparison

/-- The underlying based space of the chosen `S^0`-model is the canonical `basedSphere 0`. -/
abbrev sphereZeroUnderlyingIso
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup} (comparison : setup.SuspensionSphereComparison) :
    comparison.sphereZero.obj ≅ basedSphere 0 :=
  comparison.suspensionSphereIso 0

end SuspensionSphereComparison

namespace SphereComparison

/-- The chosen `S^0`-model of a Chapter 19 suspension-sphere comparison is identified with the
bottom of the suspension tower. -/
abbrev sphereZeroIso
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup} (comparison : setup.SphereComparison) :
    comparison.sphere 0 ≅ comparison.sphereZero :=
  comparison.sphereToSuspension 0

/-- The chosen `S^n`-model is identified with the underlying based space of the suspension tower
`Σ[setup]^n sphereZero`. -/
abbrev sphereToSuspensionObjIso
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup} (comparison : setup.SphereComparison)
    (n : ℕ) :
    (comparison.sphere n).obj ≅ (Σ[setup]^n comparison.sphereZero).obj :=
  ReducedSuspensionCofiberSetup.objIso (comparison.sphereToSuspension n)

/-- The underlying based space of each chosen `S^n`-model is the repository's canonical sphere
owner `basedSphere n`. -/
abbrev sphereIso
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup} (comparison : setup.SphereComparison)
    (n : ℕ) :
    (comparison.sphere n).obj ≅ basedSphere n :=
  comparison.sphereToSuspensionObjIso n ≪≫ comparison.suspensionSphereIso n

/-- The underlying based space of the chosen `S^0`-model is the canonical `basedSphere 0`. -/
abbrev sphereZeroUnderlyingIso
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    {setup : ReducedSuspensionCofiberSetup} (comparison : setup.SphereComparison) :
    (comparison.sphere 0).obj ≅ basedSphere 0 :=
  comparison.sphereIso 0

end SphereComparison

end ReducedSuspensionCofiberSetup

namespace ReducedCohomologyTheory

/-- Iterating the suspension axiom identifies `Ẽ^(r + n)(Σ^n X)` with `Ẽ^r(X)`. -/
noncomputable def iteratedSuspensionShiftIso
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheory setup E]
    (X : NBasedSpace) :
    (r : ℤ) → (n : ℕ) →
      (E (r + n)).obj (Opposite.op (Σ[setup]^n X)) ≅
        (E r).obj (Opposite.op X)
  | r, 0 =>
      (eqToIso (congrArg E (add_zero r))).app (Opposite.op X)
  | r, n + 1 =>
      let step :
          (E (r + (n + 1))).obj (Opposite.op (Σ[setup]^(n + 1) X)) ≅
            (E (r + n)).obj (Opposite.op (Σ[setup]^n X)) :=
        ReducedCohomologyTheory.suspensionIsoApp
            (r + (n + 1)) (Σ[setup]^n X) ≪≫
          (eqToIso (congrArg E (by simp [sub_eq_add_neg, add_assoc]))).app
            (Opposite.op (Σ[setup]^n X))
      step ≪≫ iteratedSuspensionShiftIso setup E X r n

end ReducedCohomologyTheory

/-- Iterating the Chapter 19 suspension axiom gives the direct shift isomorphism on the
suspension-generated sphere model `Σ[setup]^n sphereZero`. -/
noncomputable abbrev reducedCohomologySuspensionSphereShift
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheory setup E]
    (sphereZero : NBasedSpace)
    (q : ℤ) (n : ℕ) :
    (E q).obj (Opposite.op (Σ[setup]^n sphereZero)) ≅
      (E (q - n)).obj (Opposite.op sphereZero) :=
  (eqToIso (congrArg E (sub_add_cancel q (n : ℤ)).symm)).app
      (Opposite.op (Σ[setup]^n sphereZero)) ≪≫
    ReducedCohomologyTheory.iteratedSuspensionShiftIso setup E sphereZero (q - n) n

/-- Corollary 19.1.6: for a chosen Chapter 19 suspension-sphere comparison, the reduced
cohomology of the `S^n`-model `comparison.sphere n` is the `n`-fold shift of the reduced
cohomology of the chosen `S^0`-model `comparison.sphereZero`. The companion theorem
`comparison.sphereIso n` records that the underlying based space is the repository's canonical
sphere owner `basedSphere n`. -/
noncomputable abbrev reducedCohomologySphereShift
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheory setup E]
    (comparison : setup.SphereComparison)
    (q : ℤ) (n : ℕ) :
    (E q).obj (Opposite.op (comparison.sphere n)) ≅
      (E (q - n)).obj (Opposite.op comparison.sphereZero) :=
  (E q).mapIso (comparison.sphereToSuspension n).symm.op ≪≫
    reducedCohomologySuspensionSphereShift setup E comparison.sphereZero q n

/-- Unfolding `reducedCohomologySuspensionSphereShift` gives the iterated suspension-shift
isomorphism from `Ẽ^q(Σ[setup]^n sphereZero)` to `Ẽ^(q - n)(sphereZero)`. -/
theorem reducedCohomologySuspensionSphereShift_def
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheory setup E]
    (sphereZero : NBasedSpace)
    (q : ℤ) (n : ℕ) :
    reducedCohomologySuspensionSphereShift setup E sphereZero q n =
      (eqToIso (congrArg E (sub_add_cancel q (n : ℤ)).symm)).app
          (Opposite.op (Σ[setup]^n sphereZero)) ≪≫
        ReducedCohomologyTheory.iteratedSuspensionShiftIso setup E sphereZero (q - n) n :=
  rfl

/-- Unfolding `reducedCohomologySphereShift` transports the suspension-generated shift
isomorphism across the chosen `S^n ≅ Σ[setup]^n S^0` comparison. -/
theorem reducedCohomologySphereShift_def
    [CategoryWithCofibrations (Under (⊤_ TopCat))]
    [CategoryWithCofibrations NBasedSpace]
    [CategoryWithWeakEquivalences NBasedSpace]
    (setup : ReducedSuspensionCofiberSetup)
    (E : ℤ → NBasedSpaceᵒᵖ ⥤ AddCommGrpCat)
    [ReducedCohomologyTheory setup E]
    (comparison : setup.SphereComparison)
    (q : ℤ) (n : ℕ) :
    reducedCohomologySphereShift setup E comparison q n =
      (E q).mapIso (comparison.sphereToSuspension n).symm.op ≪≫
        reducedCohomologySuspensionSphereShift setup E comparison.sphereZero q n :=
  rfl
