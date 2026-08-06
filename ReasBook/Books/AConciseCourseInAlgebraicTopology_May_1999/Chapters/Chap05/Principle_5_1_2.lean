import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Definition_16_1_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap13.IntegralSingularHomology
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Proposition_5_2_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.TopCat.Subspace

open CategoryTheory
open Topology
open AlgebraicTopology
open scoped unitInterval Topology.Homotopy

universe u v w

-- Semantic recall: the chapter kification owner `Kified`, `TopCat.toSSetObjEquiv`, the canonical
-- singular homology owner `singularHomologyFunctor`, and the chapter-level specialization
-- `integralSingularHomology`.

/-- Helper for Principle 5.1.2: a continuous map from a compact Hausdorff source remains
continuous after replacing the codomain topology by `TopologicalSpace.compactlyGenerated`. -/
theorem continuousToCompactlyGeneratedOfCompactHaus
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type u} [TopologicalSpace X] {f : K → X} (hf : Continuous f) :
    @Continuous K X ‹TopologicalSpace K› (TopologicalSpace.compactlyGenerated.{v, u} X) f := by
  let F : (Σ (j : (S : CompHaus.{v}) × C(S, X)), j.fst) → X := fun x ↦ x.1.2 x.2
  let i : (S : CompHaus.{v}) × C(S, X) := ⟨CompHaus.of K, ⟨f, hf⟩⟩
  -- The chosen compact-source map is one of the generating probes for the compactly generated
  -- codomain topology.
  have hgenerator :
      ∀ j : (S : CompHaus.{v}) × C(S, X),
        @Continuous j.fst X inferInstance (TopologicalSpace.compactlyGenerated.{v, u} X)
          (fun a : j.fst ↦ F ⟨j, a⟩) := by
    rw [TopologicalSpace.compactlyGenerated, ← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  simpa [F, i] using hgenerator i

/-- Helper for Principle 5.1.2: a continuous map from a compact Hausdorff source stays continuous
after viewing the codomain inside its compactly generated refinement. -/
theorem continuousToKifiedOfCompactHaus
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type v} [TopologicalSpace X] (f : C(K, X)) :
    Continuous fun k : K ↦ Kified.mk (f k) := by
  let _ : UCompactlyGeneratedSpace K := inferInstance
  -- Compact Hausdorff spaces are compactly generated, so the chapter comparison applies.
  simpa using continuousToKifiedOfContinuous f.continuous

/-- Helper for Principle 5.1.2: forgetting the compactly generated refinement after the
continuous-map comparison is still continuous. -/
theorem continuousMapCompactlyGeneratedEquiv_symm_continuous
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type v} [TopologicalSpace X] (f : C(K, Kified X)) :
    Continuous fun k : K ↦ (f k).of := by
  -- The chapter's forgetful comparison `Kified X → X` is continuous.
  simpa using (continuousKifiedForget X).comp f.continuous

/-- Helper for Principle 5.1.2: the forward comparison on continuous maps changes only the
codomain topology. -/
noncomputable def continuousMapCompactlyGeneratedToFun
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type v} [TopologicalSpace X] :
    C(K, X) → C(K, Kified X) :=
  fun f ↦ ⟨fun k ↦ Kified.mk (f k), continuousToKifiedOfCompactHaus f⟩

/-- Helper for Principle 5.1.2: the inverse comparison on continuous maps forgets the kified
codomain. -/
noncomputable def continuousMapCompactlyGeneratedInvFun
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type v} [TopologicalSpace X] :
    C(K, Kified X) → C(K, X) :=
  fun f ↦ ⟨fun k ↦ (f k).of, continuousMapCompactlyGeneratedEquiv_symm_continuous f⟩

/-- Helper for Principle 5.1.2: forgetting after the forward comparison recovers the original
continuous map. -/
theorem continuousMapCompactlyGeneratedInvFun_left_inv
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type v} [TopologicalSpace X] (f : C(K, X)) :
    continuousMapCompactlyGeneratedInvFun (continuousMapCompactlyGeneratedToFun f) = f := by
  -- Both continuous maps agree pointwise.
  ext k
  rfl

/-- Helper for Principle 5.1.2: re-kifying after forgetting returns the original `Kified`-valued
continuous map. -/
theorem continuousMapCompactlyGeneratedToFun_right_inv
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type v} [TopologicalSpace X] (f : C(K, Kified X)) :
    continuousMapCompactlyGeneratedToFun
        (continuousMapCompactlyGeneratedInvFun f) = f := by
  -- Compare the maps pointwise in the `Kified` codomain.
  ext k
  change Kified.mk ((f k).of) = f k
  cases f k
  rfl

/-- Continuous maps from a compact Hausdorff source are unchanged by the compactly generated
refinement of the target topology. -/
noncomputable def continuousMapCompactlyGeneratedEquiv
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type v} [TopologicalSpace X] : C(K, X) ≃ C(K, Kified X) where
  toFun := continuousMapCompactlyGeneratedToFun
  invFun := continuousMapCompactlyGeneratedInvFun
  left_inv := continuousMapCompactlyGeneratedInvFun_left_inv
  right_inv := continuousMapCompactlyGeneratedToFun_right_inv

/-- Helper for Principle 5.1.2: when the compact source lives in universe `0`, lift it to the
codomain universe via `ULift` and transport the continuous-map comparison back down. -/
noncomputable def continuousMapCompactlyGeneratedEquivULiftSource
    {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type u} [TopologicalSpace X] : C(K, X) ≃ C(K, Kified X) :=
  ((Homeomorph.ulift.continuousMapCongr (Homeomorph.refl X)).symm.trans
      (continuousMapCompactlyGeneratedEquiv (K := ULift.{u} K) (X := X))).trans
    (Homeomorph.ulift.continuousMapCongr (Homeomorph.refl (Kified X)))

/-- Helper for Principle 5.1.2: the compactly generated comparison specialized to cube-valued
source maps. -/
noncomputable def cubeContinuousMapCompactlyGeneratedEquiv
    {X : Type u} [TopologicalSpace X] (n : ℕ) :
    C(Fin n → I, X) ≃ C(Fin n → I, Kified X) :=
  -- Route correction: the cube comparison is just the compact-source comparison specialized to
  -- `Fin n → I` after lifting the source to the codomain universe.
  continuousMapCompactlyGeneratedEquivULiftSource (K := Fin n → I) (X := X)

/-- Helper for Principle 5.1.2: the compactly generated comparison specialized to singular
simplex domains. -/
noncomputable def simplexContinuousMapCompactlyGeneratedEquiv
    (X : Type u) [TopologicalSpace X] (Δ : SimplexCategoryᵒᵖ) :
    C(stdSimplex ℝ (Fin (Δ.unop.len + 1)), X) ≃
      C(stdSimplex ℝ (Fin (Δ.unop.len + 1)), Kified X) :=
  -- Route correction: the simplex comparison is the same compact-source bridge specialized to
  -- the standard topological simplex after the same `ULift` source normalization.
  continuousMapCompactlyGeneratedEquivULiftSource
    (K := stdSimplex ℝ (Fin (Δ.unop.len + 1))) (X := X)

/-- The compactly generated comparison on continuous maps preserves the underlying function. -/
@[simp] theorem continuousMapCompactlyGeneratedEquiv_apply
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type v} [TopologicalSpace X] (f : C(K, X)) (x : K) :
    continuousMapCompactlyGeneratedEquiv f x =
      Kified.mk (f x) := by
  rfl

/-- The inverse compactly generated comparison on continuous maps preserves the underlying
function. -/
@[simp] theorem continuousMapCompactlyGeneratedEquiv_symm_apply
    {K : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type v} [TopologicalSpace X]
    (f : C(K, Kified X)) (x : K) :
    continuousMapCompactlyGeneratedEquiv.symm f x = (f x).of := by
  rfl

/-- Helper for Principle 5.1.2: the `ULift`-source comparison preserves pointwise values. -/
@[simp] theorem continuousMapCompactlyGeneratedEquivULiftSource_apply
    {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type u} [TopologicalSpace X] (f : C(K, X)) (x : K) :
    continuousMapCompactlyGeneratedEquivULiftSource f x = Kified.mk (f x) := by
  simpa [continuousMapCompactlyGeneratedEquivULiftSource] using
    (continuousMapCompactlyGeneratedEquiv_apply
      (((Homeomorph.ulift.continuousMapCongr (Homeomorph.refl X)).symm f))
      (Homeomorph.ulift.symm x))

/-- Helper for Principle 5.1.2: the inverse `ULift`-source comparison forgets the kified codomain
pointwise. -/
@[simp] theorem continuousMapCompactlyGeneratedEquivULiftSource_symm_apply
    {K : Type} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {X : Type u} [TopologicalSpace X] (f : C(K, Kified X)) (x : K) :
    continuousMapCompactlyGeneratedEquivULiftSource.symm f x = (f x).of := by
  simpa [continuousMapCompactlyGeneratedEquivULiftSource] using
    (continuousMapCompactlyGeneratedEquiv_symm_apply
      (((Homeomorph.ulift.continuousMapCongr (Homeomorph.refl (Kified X))).symm f))
      (Homeomorph.ulift.symm x))

/-- The boundary condition defining a generalized loop is preserved by the compactly generated
comparison map. -/
theorem genLoopCompactlyGeneratedMem
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
    (γ : Ω^ (Fin n) X x) :
    cubeContinuousMapCompactlyGeneratedEquiv (X := X) n γ ∈
      Ω^ (Fin n) (Kified X) (Kified.mk x) := by
  -- The cube comparison preserves the underlying values, so the boundary condition transports
  -- pointwise.
  intro t ht
  simpa [cubeContinuousMapCompactlyGeneratedEquiv] using
    congrArg Kified.mk (γ.property t ht)

/-- The boundary condition defining a generalized loop is preserved by the inverse comparison map
from the compactly generated refinement. -/
theorem genLoopOfCompactlyGeneratedMem
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
    (γ : Ω^ (Fin n) (Kified X) (Kified.mk x)) :
    (cubeContinuousMapCompactlyGeneratedEquiv (X := X) n).symm γ ∈ Ω^ (Fin n) X x := by
  -- Forgetting the kified codomain preserves the boundary values of the generalized loop.
  intro t ht
  simpa [cubeContinuousMapCompactlyGeneratedEquiv] using
    congrArg Kified.of (γ.property t ht)

/-- Generalized loops are unchanged by the compactly generated refinement of the ambient
topology. -/
noncomputable def genLoopCompactlyGeneratedToFun
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ} :
    Ω^ (Fin n) X x → Ω^ (Fin n) (Kified X) (Kified.mk x) :=
  fun γ ↦ ⟨cubeContinuousMapCompactlyGeneratedEquiv (X := X) n γ,
    genLoopCompactlyGeneratedMem γ⟩

/-- Helper for Principle 5.1.2: forgetting the compactly generated refinement on a generalized
loop recovers an ordinary generalized loop. -/
noncomputable def genLoopCompactlyGeneratedInvFun
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ} :
    Ω^ (Fin n) (Kified X) (Kified.mk x) → Ω^ (Fin n) X x :=
  fun γ ↦ ⟨(cubeContinuousMapCompactlyGeneratedEquiv (X := X) n).symm γ,
    genLoopOfCompactlyGeneratedMem γ⟩

/-- Helper for Principle 5.1.2: the loop-level forward comparison is left-inverse to forgetting
the kification. -/
theorem genLoopCompactlyGeneratedInvFun_left_inv
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
    (γ : Ω^ (Fin n) X x) :
    genLoopCompactlyGeneratedInvFun (genLoopCompactlyGeneratedToFun γ) = γ := by
  -- Reduce the subtype equality to the continuous-map left inverse on each cube point.
  ext t
  exact congrArg (fun f : C(Fin n → I, X) ↦ f t)
    ((cubeContinuousMapCompactlyGeneratedEquiv (X := X) n).left_inv γ)

/-- Helper for Principle 5.1.2: the loop-level inverse comparison is right-inverse to the
forward comparison. -/
theorem genLoopCompactlyGeneratedToFun_right_inv
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
    (γ : Ω^ (Fin n) (Kified X) (Kified.mk x)) :
    genLoopCompactlyGeneratedToFun (genLoopCompactlyGeneratedInvFun γ) = γ := by
  -- Again, compare generalized loops pointwise using the continuous-map right inverse.
  ext t
  exact congrArg (fun f : C(Fin n → I, Kified X) ↦ f t)
    ((cubeContinuousMapCompactlyGeneratedEquiv (X := X) n).right_inv γ)

/-- Generalized loops are unchanged by the compactly generated refinement of the ambient
topology. -/
noncomputable def genLoopCompactlyGeneratedEquiv
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ} :
    Ω^ (Fin n) X x ≃ Ω^ (Fin n) (Kified X) (Kified.mk x) where
  toFun := genLoopCompactlyGeneratedToFun
  invFun := genLoopCompactlyGeneratedInvFun
  left_inv := genLoopCompactlyGeneratedInvFun_left_inv
  right_inv := genLoopCompactlyGeneratedToFun_right_inv

/-- The compactly generated comparison on generalized loops preserves the underlying continuous
map. -/
@[simp] theorem genLoopCompactlyGeneratedEquiv_val
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
    (γ : Ω^ (Fin n) X x) :
    (genLoopCompactlyGeneratedEquiv γ).1 =
      cubeContinuousMapCompactlyGeneratedEquiv (X := X) n γ := by
  rfl

/-- The inverse compactly generated comparison on generalized loops preserves the underlying
continuous map. -/
@[simp] theorem genLoopCompactlyGeneratedEquiv_symm_val
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
    (γ : Ω^ (Fin n) (Kified X) (Kified.mk x)) :
    (genLoopCompactlyGeneratedEquiv.symm γ).1 =
      (cubeContinuousMapCompactlyGeneratedEquiv (X := X) n).symm γ := by
  rfl

/-- Relative homotopy classes of generalized loops are unchanged by the compactly generated
refinement of the ambient topology. -/
theorem genLoopCompactlyGeneratedEquiv_homotopic_iff
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ}
    {γ δ : Ω^ (Fin n) X x} :
    GenLoop.Homotopic γ δ ↔
      GenLoop.Homotopic (genLoopCompactlyGeneratedEquiv γ) (genLoopCompactlyGeneratedEquiv δ) :=
by
  constructor
  · rintro ⟨H⟩
    -- Transport the entire relative homotopy through the compact-source comparison on
    -- `I × I^(Fin n)`.
    let Hk :=
      continuousMapCompactlyGeneratedEquivULiftSource
        (K := I × I^(Fin n)) (X := X) H.toHomotopy.toContinuousMap
    refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
    ·
      refine
        { toFun := Hk
          map_zero_left := ?_
          map_one_left := ?_ }
      · intro a
        calc
          Hk (0, a) = Kified.mk (H.toHomotopy (0, a)) := by simp [Hk]
          _ = Kified.mk (γ a) := by
            exact congrArg Kified.mk (H.toHomotopy.apply_zero a)
          _ = (genLoopCompactlyGeneratedEquiv γ) a := by
            have hval :
                (genLoopCompactlyGeneratedEquiv γ) a =
                  cubeContinuousMapCompactlyGeneratedEquiv (X := X) n
                    (γ : C(Fin n → I, X)) a := by
              exact congrArg (fun f : C(Fin n → I, Kified X) ↦ f a)
                (genLoopCompactlyGeneratedEquiv_val (γ := γ))
            have hcube :
                Kified.mk (γ a) =
                  cubeContinuousMapCompactlyGeneratedEquiv (X := X) n
                    (γ : C(Fin n → I, X)) a := by
              simpa [cubeContinuousMapCompactlyGeneratedEquiv] using
                (continuousMapCompactlyGeneratedEquivULiftSource_apply
                  (f := (γ : C(Fin n → I, X))) (x := a)).symm
            exact
              hcube.trans hval.symm
      · intro a
        calc
          Hk (1, a) = Kified.mk (H.toHomotopy (1, a)) := by simp [Hk]
          _ = Kified.mk (δ a) := by
            exact congrArg Kified.mk (H.toHomotopy.apply_one a)
          _ = (genLoopCompactlyGeneratedEquiv δ) a := by
            have hval :
                (genLoopCompactlyGeneratedEquiv δ) a =
                  cubeContinuousMapCompactlyGeneratedEquiv (X := X) n
                    (δ : C(Fin n → I, X)) a := by
              exact congrArg (fun f : C(Fin n → I, Kified X) ↦ f a)
                (genLoopCompactlyGeneratedEquiv_val (γ := δ))
            have hcube :
                Kified.mk (δ a) =
                  cubeContinuousMapCompactlyGeneratedEquiv (X := X) n
                    (δ : C(Fin n → I, X)) a := by
              simpa [cubeContinuousMapCompactlyGeneratedEquiv] using
                (continuousMapCompactlyGeneratedEquivULiftSource_apply
                  (f := (δ : C(Fin n → I, X))) (x := a)).symm
            exact
              hcube.trans hval.symm
    · intro t a ha
      calc
        Hk (t, a) = Kified.mk (H (t, a)) := by simp [Hk]
        _ = Kified.mk (γ a) := by
          exact congrArg Kified.mk (H.prop t a ha)
        _ = (genLoopCompactlyGeneratedEquiv γ) a := by
          have hval :
              (genLoopCompactlyGeneratedEquiv γ) a =
                cubeContinuousMapCompactlyGeneratedEquiv (X := X) n
                  (γ : C(Fin n → I, X)) a := by
            exact congrArg (fun f : C(Fin n → I, Kified X) ↦ f a)
              (genLoopCompactlyGeneratedEquiv_val (γ := γ))
          have hcube :
              Kified.mk (γ a) =
                cubeContinuousMapCompactlyGeneratedEquiv (X := X) n
                  (γ : C(Fin n → I, X)) a := by
            simpa [cubeContinuousMapCompactlyGeneratedEquiv] using
              (continuousMapCompactlyGeneratedEquivULiftSource_apply
                (f := (γ : C(Fin n → I, X))) (x := a)).symm
          exact
            hcube.trans hval.symm
  · rintro ⟨H⟩
    -- Forget the codomain of the transported relative homotopy on the same compact product
    -- domain.
    let Hx :=
      (continuousMapCompactlyGeneratedEquivULiftSource
        (K := I × I^(Fin n)) (X := X)).symm H.toHomotopy.toContinuousMap
    refine ⟨{ toHomotopy := ?_, prop' := ?_ }⟩
    ·
      refine
        { toFun := Hx
          map_zero_left := ?_
          map_one_left := ?_ }
      · intro a
        calc
          Hx (0, a) = (H.toHomotopy (0, a)).of := by simp [Hx]
          _ = ((genLoopCompactlyGeneratedEquiv γ) a).of := by
            exact congrArg Kified.of (H.toHomotopy.apply_zero a)
          _ = γ a := by
            have hval :
                (genLoopCompactlyGeneratedEquiv γ) a =
                  cubeContinuousMapCompactlyGeneratedEquiv (X := X) n
                    (γ : C(Fin n → I, X)) a := by
              exact congrArg (fun f : C(Fin n → I, Kified X) ↦ f a)
                (genLoopCompactlyGeneratedEquiv_val (γ := γ))
            have hleft :
                (cubeContinuousMapCompactlyGeneratedEquiv (X := X) n).symm
                    (cubeContinuousMapCompactlyGeneratedEquiv (X := X) n
                      (γ : C(Fin n → I, X))) a =
                  γ a := by
              exact congrArg (fun f : C(Fin n → I, X) ↦ f a)
                ((cubeContinuousMapCompactlyGeneratedEquiv (X := X) n).left_inv
                  (γ : C(Fin n → I, X)))
            exact (congrArg Kified.of hval).trans <|
              by simpa [cubeContinuousMapCompactlyGeneratedEquiv] using hleft
      · intro a
        calc
          Hx (1, a) = (H.toHomotopy (1, a)).of := by simp [Hx]
          _ = ((genLoopCompactlyGeneratedEquiv δ) a).of := by
            exact congrArg Kified.of (H.toHomotopy.apply_one a)
          _ = δ a := by
            have hval :
                (genLoopCompactlyGeneratedEquiv δ) a =
                  cubeContinuousMapCompactlyGeneratedEquiv (X := X) n
                    (δ : C(Fin n → I, X)) a := by
              exact congrArg (fun f : C(Fin n → I, Kified X) ↦ f a)
                (genLoopCompactlyGeneratedEquiv_val (γ := δ))
            have hleft :
                (cubeContinuousMapCompactlyGeneratedEquiv (X := X) n).symm
                    (cubeContinuousMapCompactlyGeneratedEquiv (X := X) n
                      (δ : C(Fin n → I, X))) a =
                  δ a := by
              exact congrArg (fun f : C(Fin n → I, X) ↦ f a)
                ((cubeContinuousMapCompactlyGeneratedEquiv (X := X) n).left_inv
                  (δ : C(Fin n → I, X)))
            exact (congrArg Kified.of hval).trans <|
              by simpa [cubeContinuousMapCompactlyGeneratedEquiv] using hleft
    · intro t a ha
      calc
        Hx (t, a) = (H (t, a)).of := by simp [Hx]
        _ = ((genLoopCompactlyGeneratedEquiv γ) a).of := by
          exact congrArg Kified.of (H.prop t a ha)
        _ = γ a := by
          have hval :
              (genLoopCompactlyGeneratedEquiv γ) a =
                cubeContinuousMapCompactlyGeneratedEquiv (X := X) n
                  (γ : C(Fin n → I, X)) a := by
            exact congrArg (fun f : C(Fin n → I, Kified X) ↦ f a)
              (genLoopCompactlyGeneratedEquiv_val (γ := γ))
          have hleft :
              (cubeContinuousMapCompactlyGeneratedEquiv (X := X) n).symm
                  (cubeContinuousMapCompactlyGeneratedEquiv (X := X) n
                    (γ : C(Fin n → I, X))) a =
                γ a := by
            exact congrArg (fun f : C(Fin n → I, X) ↦ f a)
              ((cubeContinuousMapCompactlyGeneratedEquiv (X := X) n).left_inv
                (γ : C(Fin n → I, X)))
          exact (congrArg Kified.of hval).trans <|
            by simpa [cubeContinuousMapCompactlyGeneratedEquiv] using hleft

/-- Helper for Principle 5.1.2: after transporting singular simplices to continuous simplex maps,
the compactly generated comparison commutes with simplicial precomposition. -/
theorem simplexContinuousMapCompactlyGeneratedEquiv_naturality
    {X : Type u} [TopologicalSpace X] {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')
    (sig : (TopCat.toSSet.obj (TopCat.of X)).obj Δ) :
    TopCat.toSSetObjEquiv (TopCat.of (Kified X)) Δ'
        (((TopCat.toSSet.obj (TopCat.of (Kified X))).map f)
          ((TopCat.toSSetObjEquiv (TopCat.of (Kified X)) Δ).symm
            (simplexContinuousMapCompactlyGeneratedEquiv X Δ
              (TopCat.toSSetObjEquiv (TopCat.of X) Δ sig)))) =
      simplexContinuousMapCompactlyGeneratedEquiv X Δ'
        (TopCat.toSSetObjEquiv (TopCat.of X) Δ'
          (((TopCat.toSSet.obj (TopCat.of X)).map f) sig)) := by
  -- Route correction: write the naturality comparison directly on continuous simplices, where the
  -- two transports are definitionally the same pointwise map.
  rfl

/-- The singular simplicial sets of `X` and `TopologicalSpace.compactlyGenerated X` are naturally
isomorphic. -/
noncomputable def singularSetCompactlyGeneratedIso
    (X : Type u) [TopologicalSpace X] :
    TopCat.toSSet.obj (TopCat.of X) ≅ TopCat.toSSet.obj (TopCat.of (Kified X)) := by
  refine NatIso.ofComponents (fun Δ ↦ ?_) ?_
  · -- At each simplex dimension, the singular simplices are exactly continuous maps out of the
    -- standard simplex, so we transport across the compactly generated comparison there.
    exact Equiv.toIso <|
      (TopCat.toSSetObjEquiv (TopCat.of X) Δ).trans
        ((simplexContinuousMapCompactlyGeneratedEquiv X Δ).trans
          (TopCat.toSSetObjEquiv (TopCat.of (Kified X)) Δ).symm)
  · intro Δ Δ' f
    ext sig
    -- The componentwise continuous-simplex naturality theorem is the whole simplicial proof.
    apply (TopCat.toSSetObjEquiv (TopCat.of (Kified X)) Δ').injective
    simpa using simplexContinuousMapCompactlyGeneratedEquiv_naturality (X := X) f sig

/-- Generalized loops `I^(Fin n) → X` have compact image. -/
theorem genLoop_hasCompactRange
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ} (γ : Ω^ (Fin n) X x) :
    IsCompact (Set.range γ) := by
  -- The cube domain of a generalized loop is compact, so the image is compact.
  simpa using isCompact_range γ.1.continuous

/-- Singular `n`-simplices have compact image. -/
theorem singularSimplex_hasCompactRange
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    (simplex : C(stdSimplex ℝ (Fin (n + 1)), X)) : IsCompact (Set.range simplex) := by
  -- Standard simplices are compact, so every singular simplex has compact image.
  simpa using isCompact_range simplex.continuous

/-- Principle 5.1.2 (1): every class in `π_ n X x` admits a generalized-loop representative whose
image is contained in a compact subspace of `X`. -/
theorem homotopyClass_hasCompactRepresentative
    {X : Type u} [TopologicalSpace X] {x : X} {n : ℕ} (η : π_ n X x) :
    ∃ γ : Ω^ (Fin n) X x, η = (⟦γ⟧ : π_ n X x) ∧ IsCompact (Set.range γ) := by
  -- Every quotient class is represented by some generalized loop.
  refine Quotient.inductionOn η ?_
  intro γ
  refine ⟨γ, rfl, genLoop_hasCompactRange γ⟩

/-- A finite singular `n`-chain is supported in the union of the compact images of its simplices. -/
theorem singularChainSupport_hasCompactRange
    {X : Type u} [TopologicalSpace X] {n : ℕ}
    (c : FreeAbelianGroup (C(stdSimplex ℝ (Fin (n + 1)), X))) :
    IsCompact (⋃ simplex ∈ c.support, Set.range simplex) := by
  classical
  -- The support is finite, so the union of the compact simplex images is compact.
  simpa using c.support.isCompact_biUnion
    (fun simplex _ ↦ singularSimplex_hasCompactRange (n := n) simplex)

/-- Helper for Principle 5.1.2: degree `n` integral singular chains are the coproduct of one copy
of `ℤ` for each singular `n`-simplex. -/
noncomputable def integralSingularChainDegreeIsoCoproduct
    (X : TopCat) (n : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X).X n) ≅
      (∐ fun _ : singularSimplex n X ↦ ModuleCat.of ℤ ℤ) :=
  eqToIso rfl ≪≫
    Limits.Sigma.whiskerEquiv (singularSimplexEquiv n X) (fun _ ↦ Iso.refl (ModuleCat.of ℤ ℤ))

/-- Helper for Principle 5.1.2: degree `n` integral singular chains identify with the free
abelian group on singular `n`-simplices. -/
noncomputable def integralSingularChainDegreeIsoFreeAbelianGroup
    (X : TopCat) (n : ℕ) :
    ((((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X).X n) ≅
      ModuleCat.of ℤ (FreeAbelianGroup (singularSimplex n X)) :=
  let _ : DecidableEq (singularSimplex n X) := Classical.decEq _
  integralSingularChainDegreeIsoCoproduct X n ≪≫
    ModuleCat.coprodIsoDirectSum (R := ℤ) (Z := fun _ : singularSimplex n X ↦ ModuleCat.of ℤ ℤ) ≪≫
      (((finsuppLEquivDirectSum ℤ ℤ (singularSimplex n X)).symm.trans
          (FreeAbelianGroup.equivFinsupp (singularSimplex n X)).symm.toIntLinearEquiv).toModuleIso)

/-- Helper for Principle 5.1.2: the degree-`n` term of the integral singular chain complex. -/
private noncomputable abbrev integralSingularChainDegree
    (X : TopCat) (n : ℕ) : ModuleCat ℤ :=
  ((((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).obj X).X n)

/-- Helper for Principle 5.1.2: a singular simplex of `X` whose image lies in `K` factors
through the subtype `K`. -/
private theorem exists_restrictSingularSimplexToSubtype
    {X : Type u} [TopologicalSpace X] {n : ℕ} {K : Set X}
    (s : singularSimplex n X) (hs : Set.range s ⊆ K) :
    ∃ t : singularSimplex n K, (TopCat.subtypeInclusion K).hom.comp t = s := by
  -- Restrict the codomain pointwise to the subtype and use continuity of the subtype lift.
  refine ⟨⟨fun x ↦ ⟨s x, hs ⟨x, rfl⟩⟩, ?_⟩, ?_⟩
  · exact Continuous.subtype_mk s.continuous (fun x ↦ hs ⟨x, rfl⟩)
  · ext x
    rfl

/-- Helper for Principle 5.1.2: restricting a simplex along a codomain subtype produces a simplex
in that subtype. -/
private noncomputable def restrictSingularSimplexToSubtype
    {X : Type u} [TopologicalSpace X] {n : ℕ} {K : Set X}
    (s : singularSimplex n X) (hs : Set.range s ⊆ K) :
    singularSimplex n K :=
  Classical.choose (exists_restrictSingularSimplexToSubtype s hs)

/-- Helper for Principle 5.1.2: composing the restricted simplex with the subtype inclusion
recovers the original simplex. -/
private theorem subtypeInclusion_comp_restrictSingularSimplexToSubtype
    {X : Type u} [TopologicalSpace X] {n : ℕ} {K : Set X}
    (s : singularSimplex n X) (hs : Set.range s ⊆ K) :
    (TopCat.subtypeInclusion K).hom.comp (restrictSingularSimplexToSubtype s hs) = s := by
  -- This is the defining equality of the chosen restricted simplex.
  exact Classical.choose_spec (exists_restrictSingularSimplexToSubtype s hs)

/-- Helper for Principle 5.1.2: postcomposition with the subtype inclusion is injective on
singular simplices. -/
private theorem singularSimplexSubtypeInclusion_injective
    {X : Type u} [TopologicalSpace X] {n : ℕ} (K : Set X) :
    Function.Injective
      (fun s : singularSimplex n K ↦ (TopCat.subtypeInclusion K).hom.comp s) := by
  intro s t hst
  -- Compare the two subtype-valued simplices pointwise and use subtype extensionality.
  ext x
  simpa using congrArg (fun f : singularSimplex n X ↦ f x) hst

/-- Helper for Principle 5.1.2: `FreeAbelianGroup.toFinsupp` turns `FreeAbelianGroup.map f` into
`Finsupp.mapDomain f`. -/
private theorem freeAbelianGroup_toFinsupp_map
    {α : Type u} {β : Type v} (f : α → β) (x : FreeAbelianGroup α) :
    FreeAbelianGroup.toFinsupp (FreeAbelianGroup.map f x) =
      Finsupp.mapDomain f (FreeAbelianGroup.toFinsupp x) := by
  -- Both sides are additive in `x`, so it suffices to check the free generators.
  induction x using FreeAbelianGroup.induction_on with
  | zero =>
      simp
  | of a =>
      simp
  | neg a ha =>
      simpa using
        (Finsupp.mapDomain_single (f := f) (a := a) (b := (-1 : ℤ))).symm
  | add x y hx hy =>
      simpa [Finsupp.mapDomain_add] using congrArg₂ (· + ·) hx hy

/-- Helper for Principle 5.1.2: `FreeAbelianGroup.map f` is injective when `f` is injective. -/
private theorem freeAbelianGroup_map_injective_of_injective
    {α : Type u} {β : Type v} (f : α → β) (hf : Function.Injective f) :
    Function.Injective (FreeAbelianGroup.map f) := by
  intro x y hxy
  -- Transport to finitely supported coefficient functions, where `mapDomain` is injective.
  apply (FreeAbelianGroup.equivFinsupp α).injective
  apply Finsupp.mapDomain_injective hf
  simpa [freeAbelianGroup_toFinsupp_map] using congrArg FreeAbelianGroup.toFinsupp hxy

/-- Helper for Principle 5.1.2: under `singularSimplexEquiv`, the simplicial map induced by a
subtype inclusion is postcomposition with that inclusion. -/
private theorem singularSimplexEquiv_map_subtypeInclusion
    {X : Type u} [TopologicalSpace X] (K : Set X) (n : ℕ) (s : singularSimplex n K) :
    singularSimplexEquiv n (TopCat.of X)
        (((TopCat.toSSet.map (TopCat.subtypeInclusion K)).app
          (Opposite.op (SimplexCategory.mk n))
          ((singularSimplexEquiv n (TopCat.of ↥K)).symm s))) =
      (TopCat.subtypeInclusion K).hom.comp s := by
  -- Both sides are definitionally the same continuous simplex into `X`.
  rfl

/-- Helper for Principle 5.1.2: the canonical `Finsupp`/`FreeAbelianGroup` identification is
natural with respect to reindexing. -/
private theorem finsuppIsoFreeAbelianGroup_naturality
    {α : Type u} {β : Type u} (g : α → β) :
    let eα : ModuleCat.of ℤ (α →₀ ℤ) ≅ ModuleCat.of ℤ (FreeAbelianGroup α) :=
      (((FreeAbelianGroup.equivFinsupp α).symm.toIntLinearEquiv).toModuleIso)
    let eβ : ModuleCat.of ℤ (β →₀ ℤ) ≅ ModuleCat.of ℤ (FreeAbelianGroup β) :=
      (((FreeAbelianGroup.equivFinsupp β).symm.toIntLinearEquiv).toModuleIso)
    eα.inv ≫ ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ g) ≫ eβ.hom =
      ModuleCat.ofHom ((FreeAbelianGroup.map g).toIntLinearMap) := by
  -- Compare both morphisms after applying the canonical `FreeAbelianGroup → Finsupp`
  -- identification on the target.
  apply ModuleCat.hom_ext
  ext x
  apply (FreeAbelianGroup.equivFinsupp β).injective
  simpa [freeAbelianGroup_toFinsupp_map]

/-- Helper for Principle 5.1.2: a coproduct of copies of `ModuleCat.of ℤ ℤ` identifies with the
finitely supported integer-valued functions on the indexing type. -/
private noncomputable def constantIntCoproductIsoFinsupp
    (ι : Type) [DecidableEq ι] :
    (∐ fun _ : ι ↦ ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℤ (ι →₀ ℤ) :=
  ModuleCat.coprodIsoDirectSum (R := ℤ) (Z := fun _ : ι ↦ ModuleCat.of ℤ ℤ) ≪≫
    ((finsuppLEquivDirectSum ℤ ℤ ι).symm.toModuleIso)

/-- Helper for Principle 5.1.2: under the concrete `Finsupp` normalization of a constant
coproduct, the `i`th coproduct injection is `Finsupp.lsingle i`. -/
@[simp] private theorem sigma_ι_comp_constantIntCoproductIsoFinsupp_hom
    (ι : Type) [DecidableEq ι] (i : ι) :
    Limits.Sigma.ι (fun _ : ι ↦ ModuleCat.of ℤ ℤ) i ≫
      (constantIntCoproductIsoFinsupp ι).hom =
        ModuleCat.ofHom (Finsupp.lsingle i (R := ℤ) (M := ℤ)) := by
  -- Compare both morphisms pointwise on the unique generator of the `i`th coproduct summand.
  apply ModuleCat.hom_ext
  ext j
  have hcoprod :
      ModuleCat.Hom.hom
          ((ModuleCat.coprodIsoDirectSum
            (R := ℤ) (Z := fun _ : ι ↦ ModuleCat.of ℤ ℤ)).hom)
          (ModuleCat.Hom.hom (Limits.Sigma.ι (fun _ : ι ↦ ModuleCat.of ℤ ℤ) i) (1 : ℤ)) =
        DirectSum.lof ℤ ι (fun _ : ι ↦ ℤ) i 1 := by
    have hmor :
        Limits.Sigma.ι (fun _ : ι ↦ ModuleCat.of ℤ ℤ) i ≫
            (ModuleCat.coprodIsoDirectSum
              (R := ℤ) (Z := fun _ : ι ↦ ModuleCat.of ℤ ℤ)).hom =
          ModuleCat.ofHom (DirectSum.lof ℤ ι (fun _ : ι ↦ ℤ) i) := by
      simpa using
        (ModuleCat.ι_coprodIsoDirectSum_hom
          (R := ℤ) (Z := fun _ : ι ↦ ModuleCat.of ℤ ℤ) i)
    change
      ModuleCat.Hom.hom
          (Limits.Sigma.ι (fun _ : ι ↦ ModuleCat.of ℤ ℤ) i ≫
            (ModuleCat.coprodIsoDirectSum
              (R := ℤ) (Z := fun _ : ι ↦ ModuleCat.of ℤ ℤ)).hom) (1 : ℤ) =
        DirectSum.lof ℤ ι (fun _ : ι ↦ ℤ) i 1
    rw [hmor]
    rfl
  have hι :
      (finsuppLEquivDirectSum ℤ ℤ ι).symm
          (ModuleCat.Hom.hom
            ((ModuleCat.coprodIsoDirectSum
              (R := ℤ) (Z := fun _ : ι ↦ ModuleCat.of ℤ ℤ)).hom)
            (ModuleCat.Hom.hom (Limits.Sigma.ι (fun _ : ι ↦ ModuleCat.of ℤ ℤ) i) (1 : ℤ))) =
        Finsupp.single i (1 : ℤ) := by
    rw [hcoprod]
    simpa using
      finsuppLEquivDirectSum_symm_lof (R := ℤ) (M := ℤ) (ι := ι) i (1 : ℤ)
  -- Once the coproduct injection is rewritten as a direct-sum basis vector, the `Finsupp`
  -- computation is the standard `finsuppLEquivDirectSum_symm_lof` formula.
  calc
    ((ModuleCat.Hom.hom
          (Limits.Sigma.ι (fun _ : ι ↦ ModuleCat.of ℤ ℤ) i ≫
            (constantIntCoproductIsoFinsupp ι).hom)) 1) j =
      (Finsupp.single i (1 : ℤ)) j := by
          simpa [constantIntCoproductIsoFinsupp, Iso.trans_hom, Category.assoc] using
            congrArg (fun u : ι →₀ ℤ ↦ u j) hι
    _ = ((ModuleCat.Hom.hom (ModuleCat.ofHom (Finsupp.lsingle i (R := ℤ) (M := ℤ))) 1) j) := by
          rfl

/-- Helper for Principle 5.1.2: after normalizing constant coproducts of `ℤ`-modules to
`Finsupp`, the categorical reindexing map `Sigma.map'` becomes `Finsupp.lmapDomain`. -/
private theorem constantIntCoproductIsoFinsupp_inv_sigmaMap_hom
    {α : Type} {β : Type} [DecidableEq α] [DecidableEq β] (g : α → β) :
    (constantIntCoproductIsoFinsupp α).inv ≫
        Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of ℤ ℤ)) ≫
      (constantIntCoproductIsoFinsupp β).hom =
        ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ g) := by
  -- Compare both sides after precomposing with the coproduct injections, where every map
  -- computes on a single basis vector.
  apply (cancel_epi (constantIntCoproductIsoFinsupp α).hom).1
  refine Limits.Sigma.hom_ext _ _ fun i ↦ ?_
  calc
    Limits.Sigma.ι (fun _ : α ↦ ModuleCat.of ℤ ℤ) i ≫
        ((constantIntCoproductIsoFinsupp α).hom ≫
          ((constantIntCoproductIsoFinsupp α).inv ≫
            Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of ℤ ℤ)) ≫
              (constantIntCoproductIsoFinsupp β).hom)) =
      ModuleCat.ofHom (Finsupp.lsingle (g i) (R := ℤ) (M := ℤ)) := by
        simp [Category.assoc]
    _ = ModuleCat.ofHom (Finsupp.lsingle i (R := ℤ) (M := ℤ)) ≫
          ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ g) := by
        ext x j
        simp [Finsupp.lmapDomain]
    _ = Limits.Sigma.ι (fun _ : α ↦ ModuleCat.of ℤ ℤ) i ≫
          ((constantIntCoproductIsoFinsupp α).hom ≫
            ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ g)) := by
        change
          ModuleCat.ofHom (Finsupp.lsingle i (R := ℤ) (M := ℤ)) ≫
              ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ g) =
            (Limits.Sigma.ι (fun _ : α ↦ ModuleCat.of ℤ ℤ) i ≫
                (constantIntCoproductIsoFinsupp α).hom) ≫
              ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ g)
        have hι := sigma_ι_comp_constantIntCoproductIsoFinsupp_hom α i
        simpa [Category.assoc] using
          congrArg (fun f ↦ f ≫ ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ g)) hι.symm

/-- Helper for Principle 5.1.2: under the coproduct normalization of degree-`n` integral
singular chains, subtype inclusion is just categorical reindexing by postcomposition of
singular simplices. -/
private theorem integralSingularChainDegreeIsoCoproduct_subtypeInclusion_naturality
    {X : Type} [TopologicalSpace X] (K : Set X) (n : ℕ) :
    let F := ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
    let cK := integralSingularChainDegreeIsoCoproduct (TopCat.of ↥K) n
    let cX := integralSingularChainDegreeIsoCoproduct (TopCat.of X) n
    cK.inv ≫ (F.map (TopCat.subtypeInclusion K)).f n ≫ cX.hom =
      Limits.Sigma.map'
        (fun s : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp s)
        (fun _ ↦ 𝟙 (ModuleCat.of ℤ ℤ)) := by
  -- Route correction: compare both coproduct morphisms after precomposing with each simplex
  -- injection, where the simplicial map computes pointwise on a single simplex.
  refine Limits.Sigma.hom_ext _ _ fun s ↦ ?_
  -- After rewriting the two normalization isomorphisms, everything reduces to the singular
  -- simplex computation for `TopCat.subtypeInclusion`.
  simp [integralSingularChainDegreeIsoCoproduct, singularChainComplexFunctor,
    SSet.singularChainComplexFunctor, Category.assoc]
  -- The remaining equality is exactly the simplex-level naturality comparison transported
  -- through the target coproduct injection.
  apply congrArg
    (fun t : singularSimplex n X ↦
      Limits.Sigma.ι (fun _ : singularSimplex n X ↦ ModuleCat.of ℤ ℤ) t)
  simpa using singularSimplexEquiv_map_subtypeInclusion (K := K) (n := n) s

/-- Helper for Principle 5.1.2: when every simplex in a finitely supported chain lands in `K`,
the chain is the image of the corresponding `comapDomain` lift along subtype inclusion. -/
private theorem mapDomain_comap_restrictSingularSimplex_support
    {X : Type u} [TopologicalSpace X] {n : ℕ} {K : Set X}
    (c : singularSimplex n X →₀ ℤ)
    (hc : ∀ s ∈ c.support, Set.range s ⊆ K) :
    let f : singularSimplex n K → singularSimplex n X :=
      fun t : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp t
    Finsupp.mapDomain f
        (Finsupp.comapDomain f c
          (singularSimplexSubtypeInclusion_injective K).injOn) = c := by
  let f : singularSimplex n K → singularSimplex n X :=
    fun t : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp t
  have hf : Function.Injective f := singularSimplexSubtypeInclusion_injective K
  have hsupport : ↑c.support ⊆ Set.range f := by
    intro s hs
    refine ⟨restrictSingularSimplexToSubtype s (hc s hs), ?_⟩
    exact subtypeInclusion_comp_restrictSingularSimplexToSubtype s (hc s hs)
  -- The support hypothesis puts every simplex coefficient inside the image of subtype inclusion,
  -- so `mapDomain` inverts the `comapDomain` lift.
  simpa [f] using Finsupp.mapDomain_comapDomain f hf c hsupport

/-- Helper for Principle 5.1.2: after normalizing degree-`n` chains to free abelian groups on
singular simplices, the chain map induced by `TopCat.subtypeInclusion K` becomes
`FreeAbelianGroup.map` on simplices. -/
private theorem integralSingularChainDegreeIsoFreeAbelianGroup_subtypeInclusion_naturality
    {X : Type} [TopologicalSpace X] (K : Set X) (n : ℕ) :
    let F := ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
    let eK := integralSingularChainDegreeIsoFreeAbelianGroup (TopCat.of ↥K) n
    let eX := integralSingularChainDegreeIsoFreeAbelianGroup (TopCat.of X) n
    eK.inv ≫ (F.map (TopCat.subtypeInclusion K)).f n ≫ eX.hom =
      ModuleCat.ofHom
        ((FreeAbelianGroup.map
          fun s : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp s).toIntLinearMap) := by
  classical
  let F := ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
  let g : singularSimplex n K → singularSimplex n X :=
    fun s : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp s
  let cK := integralSingularChainDegreeIsoCoproduct (TopCat.of ↥K) n
  let cX := integralSingularChainDegreeIsoCoproduct (TopCat.of X) n
  let dK : (∐ fun _ : singularSimplex n K ↦ ModuleCat.of ℤ ℤ) ≅
      ModuleCat.of ℤ (singularSimplex n K →₀ ℤ) :=
    constantIntCoproductIsoFinsupp (singularSimplex n K)
  let dX : (∐ fun _ : singularSimplex n X ↦ ModuleCat.of ℤ ℤ) ≅
      ModuleCat.of ℤ (singularSimplex n X →₀ ℤ) :=
    constantIntCoproductIsoFinsupp (singularSimplex n X)
  let qK : ModuleCat.of ℤ (singularSimplex n K →₀ ℤ) ≅
      ModuleCat.of ℤ (FreeAbelianGroup (singularSimplex n K)) :=
    (((FreeAbelianGroup.equivFinsupp (singularSimplex n K)).symm.toIntLinearEquiv).toModuleIso)
  let qX : ModuleCat.of ℤ (singularSimplex n X →₀ ℤ) ≅
      ModuleCat.of ℤ (FreeAbelianGroup (singularSimplex n X)) :=
    (((FreeAbelianGroup.equivFinsupp (singularSimplex n X)).symm.toIntLinearEquiv).toModuleIso)
  let eK := integralSingularChainDegreeIsoFreeAbelianGroup (TopCat.of ↥K) n
  let eX := integralSingularChainDegreeIsoFreeAbelianGroup (TopCat.of X) n
  have hCoproduct :
      cK.inv ≫ (F.map (TopCat.subtypeInclusion K)).f n ≫ cX.hom =
        Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of ℤ ℤ)) := by
    simpa [F, cK, cX, g] using
      integralSingularChainDegreeIsoCoproduct_subtypeInclusion_naturality
        (K := K) (n := n)
  have hFinsupp :
      dK.inv ≫ Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of ℤ ℤ)) ≫ dX.hom =
        ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ g) := by
    simpa [dK, dX, g] using
      constantIntCoproductIsoFinsupp_inv_sigmaMap_hom g
  -- Route correction: normalize first to the coproduct owner, then to `Finsupp`, and only at the
  -- last stage use the `Finsupp`/`FreeAbelianGroup` naturality comparison.
  calc
    eK.inv ≫ (F.map (TopCat.subtypeInclusion K)).f n ≫ eX.hom =
      qK.inv ≫ dK.inv ≫ Limits.Sigma.map' g (fun _ ↦ 𝟙 (ModuleCat.of ℤ ℤ)) ≫ dX.hom ≫
        qX.hom := by
          simpa [F, g, cK, cX, dK, dX, qK, qX, eK, eX,
            integralSingularChainDegreeIsoFreeAbelianGroup, Category.assoc] using
            congrArg
              (fun f ↦ qK.inv ≫ dK.inv ≫ f ≫ dX.hom ≫ qX.hom)
              hCoproduct
    _ = qK.inv ≫ ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ g) ≫ qX.hom := by
          simpa [Category.assoc] using
            congrArg (fun f ↦ qK.inv ≫ f ≫ qX.hom) hFinsupp
    _ = ModuleCat.ofHom ((FreeAbelianGroup.map g).toIntLinearMap) := by
          simpa [qK, qX, g] using finsuppIsoFreeAbelianGroup_naturality g

/-- Helper for Principle 5.1.2: a finitely supported singular chain whose simplices all land in
`K` lifts to a singular chain on the subtype `K`. -/
private theorem exists_liftSingularChainToSubtype
    {X : Type u} [TopologicalSpace X] {n : ℕ} {K : Set X}
    (c : FreeAbelianGroup (singularSimplex n X))
    (hc : ∀ s ∈ c.support, Set.range s ⊆ K) :
    ∃ cK : FreeAbelianGroup (singularSimplex n K),
      FreeAbelianGroup.map
          (fun s : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp s) cK = c := by
  classical
  let cF : singularSimplex n X →₀ ℤ := FreeAbelianGroup.toFinsupp c
  let f : singularSimplex n K → singularSimplex n X :=
    fun s : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp s
  let cKF : singularSimplex n K →₀ ℤ :=
    Finsupp.comapDomain f cF (singularSimplexSubtypeInclusion_injective K).injOn
  refine ⟨(FreeAbelianGroup.equivFinsupp (singularSimplex n K)).symm cKF, ?_⟩
  -- Build the lift on the `Finsupp` owner and transport it back through the canonical
  -- `FreeAbelianGroup` equivalence.
  apply (FreeAbelianGroup.equivFinsupp (singularSimplex n X)).injective
  simpa [cF, cKF, f, freeAbelianGroup_toFinsupp_map] using
    mapDomain_comap_restrictSingularSimplex_support cF (by
      intro s hs
      simpa [cF] using hc s hs)

/-- Helper for Principle 5.1.2: degreewise subtype inclusion is injective on integral singular
chains. -/
private theorem integralSingularChainDegree_subtypeInclusion_injective
    {X : Type} [TopologicalSpace X] (K : Set X) (n : ℕ) :
    Function.Injective
      (((((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).map
        (TopCat.subtypeInclusion K)).f n).hom) := by
  let F := ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
  let eK := integralSingularChainDegreeIsoFreeAbelianGroup (TopCat.of ↥K) n
  let eX := integralSingularChainDegreeIsoFreeAbelianGroup (TopCat.of X) n
  intro x y hxy
  have hfreeMap :
      FreeAbelianGroup.map
          (fun s : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp s)
          (ModuleCat.Hom.hom eK.hom x) =
        FreeAbelianGroup.map
          (fun s : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp s)
          (ModuleCat.Hom.hom eK.hom y) := by
    calc
      FreeAbelianGroup.map
          (fun s : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp s)
          (ModuleCat.Hom.hom eK.hom x) =
        ModuleCat.Hom.hom eX.hom
          (ModuleCat.Hom.hom ((F.map (TopCat.subtypeInclusion K)).f n) x) := by
            simpa [eK, eX] using
              congrArg
                (fun f ↦ ModuleCat.Hom.hom f (ModuleCat.Hom.hom eK.hom x))
                (integralSingularChainDegreeIsoFreeAbelianGroup_subtypeInclusion_naturality
                  (K := K) (n := n)).symm
      _ = ModuleCat.Hom.hom eX.hom
          (ModuleCat.Hom.hom ((F.map (TopCat.subtypeInclusion K)).f n) y) := by
            simpa using congrArg (ModuleCat.Hom.hom eX.hom) hxy
      _ = FreeAbelianGroup.map
          (fun s : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp s)
          (ModuleCat.Hom.hom eK.hom y) := by
            simpa [eK, eX] using
              congrArg
                (fun f ↦ ModuleCat.Hom.hom f (ModuleCat.Hom.hom eK.hom y))
                (integralSingularChainDegreeIsoFreeAbelianGroup_subtypeInclusion_naturality
                  (K := K) (n := n))
  have hfree :
      ModuleCat.Hom.hom eK.hom x = ModuleCat.Hom.hom eK.hom y := by
    apply freeAbelianGroup_map_injective_of_injective
      (fun s : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp s)
      (singularSimplexSubtypeInclusion_injective K)
    exact hfreeMap
  exact (ModuleCat.mono_iff_injective eK.hom).1 inferInstance hfree

/-- Principle 5.1.2 (2): every class in ordinary singular `n`-homology with integer coefficients
is supported on a compact subspace of `X`. -/
theorem singularHomologyClass_hasCompactSupport
    {X : Type} [TopologicalSpace X] {n : ℕ}
    (η : integralSingularHomology n (TopCat.of X)) :
    ∃ K : Set X, IsCompact K ∧
      ∃ ηK : integralSingularHomology n (TopCat.of K),
        (((singularHomologyFunctor (ModuleCat ℤ) n).obj (ModuleCat.of ℤ ℤ)).map
          (TopCat.subtypeInclusion K)) ηK = η := by
  let F := ((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ))
  let CX := F.obj (TopCat.of X)
  -- Choose a cycle representative of the given homology class via surjectivity of `homologyπ`.
  obtain ⟨zX, hzX⟩ := (ModuleCat.epi_iff_surjective (CX.homologyπ n)).mp inferInstance η
  let xX : CX.X n := ModuleCat.Hom.hom (CX.iCycles n) zX
  let eX := integralSingularChainDegreeIsoFreeAbelianGroup (TopCat.of X) n
  let cX : FreeAbelianGroup (singularSimplex n X) := ModuleCat.Hom.hom eX.hom xX
  let K : Set X := ⋃ s ∈ cX.support, Set.range s
  have hKcompact : IsCompact K := by
    -- The chain uses only finitely many simplices, so the union of their compact images is
    -- compact.
    simpa [K, cX] using singularChainSupport_hasCompactRange cX
  have hsupport : ∀ s ∈ cX.support, Set.range s ⊆ K := by
    intro s hs y hy
    rcases hy with ⟨x, rfl⟩
    exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hs, ⟨x, rfl⟩⟩⟩
  -- Lift the finitely supported chain to the compact subtype determined by its support.
  obtain ⟨cK, hcKmap⟩ := exists_liftSingularChainToSubtype cX hsupport
  let CK := F.obj (TopCat.of K)
  let φ : CK ⟶ CX := F.map (TopCat.subtypeInclusion K)
  let eK := integralSingularChainDegreeIsoFreeAbelianGroup (TopCat.of ↥K) n
  let xK : CK.X n := ModuleCat.Hom.hom eK.inv cK
  have hxK :
      ModuleCat.Hom.hom (φ.f n) xK = xX := by
    -- Compare the lifted chain and the original chain after applying the free-chain
    -- normalization on `X`.
    apply (ModuleCat.mono_iff_injective eX.hom).1 inferInstance
    calc
      ModuleCat.Hom.hom eX.hom (ModuleCat.Hom.hom (φ.f n) xK) =
        FreeAbelianGroup.map
          (fun s : singularSimplex n K => (TopCat.subtypeInclusion K).hom.comp s) cK := by
            simpa [F, φ, eK, eX, xK] using
              congrArg (fun f ↦ ModuleCat.Hom.hom f cK)
                (integralSingularChainDegreeIsoFreeAbelianGroup_subtypeInclusion_naturality
                  (K := K) (n := n))
      _ = cX := hcKmap
      _ = ModuleCat.Hom.hom eX.hom xX := by
            rfl
  let j := (ComplexShape.down ℕ).next n
  have hxXcycle : ModuleCat.Hom.hom (CX.d n j) xX = 0 := by
    -- The chosen representative came from the cycles object, so its boundary vanishes.
    change ModuleCat.Hom.hom (CX.iCycles n ≫ CX.d n j) zX = 0
    simpa [xX] using
      congrArg (fun f ↦ ModuleCat.Hom.hom f zX)
        (HomologicalComplex.iCycles_d (K := CX) (i := n) (j := j))
  have hxKcycle_map :
      ModuleCat.Hom.hom (φ.f j) (ModuleCat.Hom.hom (CK.d n j) xK) = 0 := by
    -- Map the boundary of the lifted chain forward to `X`, where it identifies with the
    -- boundary of the original cycle representative.
    change ModuleCat.Hom.hom (CK.d n j ≫ φ.f j) xK = 0
    rw [← φ.comm]
    change ModuleCat.Hom.hom (CX.d n j) (ModuleCat.Hom.hom (φ.f n) xK) = 0
    rw [hxK]
    exact hxXcycle
  have hxKcycle : ModuleCat.Hom.hom (CK.d n j) xK = 0 := by
    -- Degreewise subtype inclusion is injective, so the lifted chain is also a cycle.
    exact (integralSingularChainDegree_subtypeInclusion_injective (K := K) (n := j))
      (by simpa using hxKcycle_map)
  let kX : ModuleCat.of ℤ ℤ ⟶ CX.X n := ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ xX)
  let kK : ModuleCat.of ℤ ℤ ⟶ CK.X n := ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ xK)
  have hkX : kX ≫ CX.d n j = 0 := by
    -- The singleton-span morphism represents the cycle element `xX`.
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (ModuleCat.Hom.hom (CX.d n j)) (ModuleCat.Hom.hom kX (1 : ℤ)) = 0
    rw [show ModuleCat.Hom.hom kX (1 : ℤ) = xX by
      simpa [kX] using LinearMap.toSpanSingleton_apply_one (R := ℤ) (M := CX.X n) xX]
    exact hxXcycle
  have hkK : kK ≫ CK.d n j = 0 := by
    -- The same singleton-span encoding works for the lifted cycle `xK`.
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (ModuleCat.Hom.hom (CK.d n j)) (ModuleCat.Hom.hom kK (1 : ℤ)) = 0
    rw [show ModuleCat.Hom.hom kK (1 : ℤ) = xK by
      simpa [kK] using LinearMap.toSpanSingleton_apply_one (R := ℤ) (M := CK.X n) xK]
    exact hxKcycle
  let zK : CK.cycles n := ModuleCat.Hom.hom (CK.liftCycles kK j rfl hkK) (1 : ℤ)
  have hzXlift : ModuleCat.Hom.hom (CX.liftCycles kX j rfl hkX) (1 : ℤ) = zX := by
    -- The lift of the singleton-span representative is the original cycle element because
    -- both have the same image under `iCycles`.
    apply (ModuleCat.mono_iff_injective (CX.iCycles n)).1 inferInstance
    calc
      ModuleCat.Hom.hom (CX.iCycles n)
          (ModuleCat.Hom.hom (CX.liftCycles kX j rfl hkX) (1 : ℤ)) =
        xX := by
          change ModuleCat.Hom.hom (CX.liftCycles kX j rfl hkX ≫ CX.iCycles n) (1 : ℤ) = xX
          rw [HomologicalComplex.liftCycles_i (K := CX) (k := kX) (j := j) (hj := rfl) (hk := hkX)]
          simpa [kX] using LinearMap.toSpanSingleton_apply_one (R := ℤ) (M := CX.X n) xX
      _ = ModuleCat.Hom.hom (CX.iCycles n) zX := by
          rfl
  have hkmap : kK ≫ φ.f n = kX := by
    -- The singleton-span morphisms agree because their values at `1` are exactly `xK` and `xX`.
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change (ModuleCat.Hom.hom (φ.f n)) (ModuleCat.Hom.hom kK (1 : ℤ)) =
      ModuleCat.Hom.hom kX (1 : ℤ)
    rw [show ModuleCat.Hom.hom kK (1 : ℤ) = xK by
      simpa [kK] using LinearMap.toSpanSingleton_apply_one (R := ℤ) (M := CK.X n) xK]
    rw [show ModuleCat.Hom.hom kX (1 : ℤ) = xX by
      simpa [kX] using LinearMap.toSpanSingleton_apply_one (R := ℤ) (M := CX.X n) xX]
    exact hxK
  have hzKmap :
      ModuleCat.Hom.hom (HomologicalComplex.cyclesMap φ n) zK = zX := by
    -- The cycle lifted from the compact subtype maps to the chosen representative on `X`.
    have hcycles :
        CK.liftCycles kK j rfl hkK ≫ HomologicalComplex.cyclesMap φ n =
          CX.liftCycles kX j rfl hkX := by
      simpa [hkmap] using
        HomologicalComplex.liftCycles_comp_cyclesMap
          (K := CK) (L := CX) (k := kK) (j := j) (hj := rfl) (hk := hkK) (φ := φ)
    calc
      ModuleCat.Hom.hom (HomologicalComplex.cyclesMap φ n) zK =
        ModuleCat.Hom.hom (CX.liftCycles kX j rfl hkX) (1 : ℤ) := by
          change ModuleCat.Hom.hom
              (CK.liftCycles kK j rfl hkK ≫ HomologicalComplex.cyclesMap φ n) (1 : ℤ) =
            ModuleCat.Hom.hom (CX.liftCycles kX j rfl hkX) (1 : ℤ)
          rw [hcycles]
      _ = zX := hzXlift
  refine ⟨K, hKcompact, ModuleCat.Hom.hom (CK.homologyπ n) zK, ?_⟩
  -- Finally, move the subtype-inclusion map on homology past `homologyπ` and use the cycle-level
  -- comparison established above.
  change ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ n)
      (ModuleCat.Hom.hom (CK.homologyπ n) zK) = η
  change ModuleCat.Hom.hom (CK.homologyπ n ≫ HomologicalComplex.homologyMap φ n) zK = η
  rw [HomologicalComplex.homologyπ_naturality]
  simpa [hzKmap] using hzX

/-- Principle 5.1.2 (3): for a weak Hausdorff space `X`, the compactly generated refinement
comparison `X ⟶ TopologicalSpace.compactlyGenerated X` induces an equivalence on `π_ n X x`. -/
noncomputable def homotopyGroupCompactlyGeneratedEquiv
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace X] {x : X} (n : ℕ) :
    π_ n X x ≃ HomotopyGroup (Fin n) (Kified X) (Kified.mk x) :=
  Quotient.congr genLoopCompactlyGeneratedEquiv fun _ _ ↦
    genLoopCompactlyGeneratedEquiv_homotopic_iff

/-- The compactly generated comparison on `π_ n X x` is induced by the comparison on generalized
loops. -/
@[simp] theorem homotopyGroupCompactlyGeneratedEquiv_mk
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace X] {x : X} (n : ℕ)
    (γ : Ω^ (Fin n) X x) :
    homotopyGroupCompactlyGeneratedEquiv n (⟦γ⟧ : π_ n X x) =
      (⟦genLoopCompactlyGeneratedEquiv γ⟧ :
        HomotopyGroup (Fin n) (Kified X) (Kified.mk x)) := by
  rfl

/-- The inverse compactly generated comparison on `π_ n X x` is induced by the inverse comparison
on generalized loops. -/
@[simp] theorem homotopyGroupCompactlyGeneratedEquiv_symm_mk
    {X : Type u} [TopologicalSpace X] [WeaklyHausdorffSpace X] {x : X} (n : ℕ)
    (γ : Ω^ (Fin n) (Kified X) (Kified.mk x)) :
    (homotopyGroupCompactlyGeneratedEquiv n).symm
        (⟦γ⟧ : HomotopyGroup (Fin n) (Kified X) (Kified.mk x)) =
      (⟦genLoopCompactlyGeneratedEquiv.symm γ⟧ : π_ n X x) :=
  rfl

/-- The coefficient-general compactly generated comparison on singular homology. -/
noncomputable def singularHomologyCompactlyGeneratedIsoWithCoefficients
    (C : Type u) [Category.{v} C] [Limits.HasCoproducts.{w} C] [Preadditive C]
    [CategoryWithHomology C] {X : Type w} [TopologicalSpace X] (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of X) ≅
      ((singularHomologyFunctor C n).obj R).obj (TopCat.of (Kified X)) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (((SSet.singularChainComplexFunctor C).obj R).mapIso (singularSetCompactlyGeneratedIso X))

/-- The coefficient-general compactly generated comparison on singular homology is the functorial
image of the comparison on singular simplicial sets. -/
@[simp] theorem singularHomologyCompactlyGeneratedIsoWithCoefficients_def
    (C : Type u) [Category.{v} C] [Limits.HasCoproducts.{w} C] [Preadditive C]
    [CategoryWithHomology C] {X : Type w} [TopologicalSpace X] (R : C) (n : ℕ) :
    singularHomologyCompactlyGeneratedIsoWithCoefficients C R n =
      (HomologicalComplex.homologyFunctor _ _ n).mapIso
        (((SSet.singularChainComplexFunctor C).obj R).mapIso
          (singularSetCompactlyGeneratedIso X)) :=
  rfl

/-- The compactly generated comparison on ordinary singular homology groups with integer
coefficients. -/
noncomputable def singularHomologyCompactlyGeneratedIso
    {X : Type} [TopologicalSpace X] (n : ℕ) :
    integralSingularHomology n (TopCat.of X) ≅ integralSingularHomology n (TopCat.of (Kified X)) :=
  singularHomologyCompactlyGeneratedIsoWithCoefficients (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) n

/-- The compactly generated comparison on ordinary singular homology groups is the specialization
of the comparison on singular simplicial sets to integer coefficients. -/
@[simp] theorem singularHomologyCompactlyGeneratedIso_def
    {X : Type} [TopologicalSpace X] (n : ℕ) :
    singularHomologyCompactlyGeneratedIso n =
      (HomologicalComplex.homologyFunctor _ _ n).mapIso
        (((SSet.singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
          (singularSetCompactlyGeneratedIso X)) :=
  rfl
