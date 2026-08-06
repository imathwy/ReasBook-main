import Mathlib.Algebra.Exact
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Criterion_8_5_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyInclusion

open CategoryTheory
open scoped Topology Topology.Homotopy

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

/-- The ordinary homotopy group of the actual fiber of a based fibration. -/
abbrev fibrationFiberHomotopyGroup {E B : BasedSpace} (p : E ⟶ B) (n : ℕ) :=
  π_ n (actualFiberSet p) (actualFiberBasepoint p)

/-- The ordinary homotopy group of the total space of a based fibration. -/
abbrev fibrationTotalHomotopyGroup {E B : BasedSpace} (p : E ⟶ B) (n : ℕ) :=
  let _ := p
  π_ n E.right (underTopBasepoint E)

/-- The loop-space model used for the fiber term `π_(q + 2)(F)` in the long exact sequence of a
fibration. -/
abbrev fibrationFiberLoopHomotopyGroup {E B : BasedSpace} (p : E ⟶ B) (q : ℕ) :=
  π_ (q + 1) (Ω (actualFiberSet p) (actualFiberBasepoint p)) (Path.refl (actualFiberBasepoint p))

/-- The loop-space model used for the total-space term `π_(q + 2)(E)` in the long exact sequence
of a fibration. -/
abbrev fibrationTotalLoopHomotopyGroup {E B : BasedSpace} (p : E ⟶ B) (q : ℕ) :=
  let _ := p
  π_ (q + 1) (Ω E.right (underTopBasepoint E)) (Path.refl (underTopBasepoint E))

/-- The inclusion of the actual fiber into the total space. -/
abbrev fibrationFiberInclusion {E B : BasedSpace} (p : E ⟶ B) :
    C(actualFiberSet p, E.right) :=
  fiberInclusion p.right.hom (underTopBasepoint B)

/-- The map on loop spaces induced by including the actual fiber into the total space. -/
def fibrationFiberLoopInclusionMap {E B : BasedSpace} (p : E ⟶ B) :
    C(Ω (actualFiberSet p) (actualFiberBasepoint p), Ω E.right (underTopBasepoint E)) where
  toFun γ := γ.map continuous_subtype_val
  continuous_toFun :=
    continuous_induced_rng.2 <|
      (ContinuousMap.continuous_postcomp ⟨Subtype.val, continuous_subtype_val⟩).comp
        continuous_induced_dom

/-- The map on loop spaces induced by the fibration map `p : E ⟶ B`. -/
abbrev fibrationLoopTotalToBaseMap {E B : BasedSpace} (p : E ⟶ B) :
    C(Ω E.right (underTopBasepoint E), Ω B.right (underTopBasepoint B)) :=
  loopBasedMapContinuousMap p

/-- The loop-space map induced by `p` sends the constant loop in `E` to the constant loop in
`B`. -/
  @[simp] theorem fibrationLoopTotalToBaseMap_refl {E B : BasedSpace} (p : E ⟶ B) :
    fibrationLoopTotalToBaseMap p (Path.refl (underTopBasepoint E)) =
      Path.refl (underTopBasepoint B) := by
  apply Path.ext
  ext t
  simpa only [fibrationLoopTotalToBaseMap, loopBasedMapContinuousMap, loopBasedMapPath, Path.refl]
    using fundamentalGroupFunctorMap_basepoint p

/-- The loop-space model used for the base term `π_(q + 2)(B)` in the long exact sequence of a
fibration. -/
abbrev fibrationBaseLoopHomotopyGroup (B : BasedSpace) (q : ℕ) :=
  π_ (q + 1) (Ω B.right (underTopBasepoint B)) (Path.refl (underTopBasepoint B))

/-- The inclusion-induced map `π_(q + 1)(F) → π_(q + 1)(E)` for the actual fiber `F`. -/
def fibrationFiberInclusionHomotopyGroupMap {E B : BasedSpace} (p : E ⟶ B) (q : ℕ) :
    fibrationFiberHomotopyGroup p (q + 1) → fibrationTotalHomotopyGroup p (q + 1) :=
  homotopyGroupMap (fibrationFiberInclusion p) (q + 1) (actualFiberBasepoint p)

/-- The loop-model inclusion-induced map `π_(q + 2)(F) → π_(q + 2)(E)` for the actual fiber
sequence. -/
def fibrationLoopFiberInclusionHomotopyGroupMap {E B : BasedSpace} (p : E ⟶ B) (q : ℕ) :
    fibrationFiberLoopHomotopyGroup p q → fibrationTotalLoopHomotopyGroup p q :=
  homotopyGroupMap (fibrationFiberLoopInclusionMap p) (q + 1) (Path.refl (actualFiberBasepoint p))

/-- The loop-model map `π_(q + 2)(E) → π_(q + 2)(B)` induced by the fibration map. -/
def fibrationLoopTotalToBaseHomotopyGroupMap {E B : BasedSpace} (p : E ⟶ B) (q : ℕ) :
    fibrationTotalLoopHomotopyGroup p q → fibrationBaseLoopHomotopyGroup B q :=
  cast
    (congrArg
      (fun y ↦
        fibrationTotalLoopHomotopyGroup p q →
          π_ (q + 1) (Ω B.right (underTopBasepoint B)) y)
      (fibrationLoopTotalToBaseMap_refl p))
    (homotopyGroupMap (fibrationLoopTotalToBaseMap p) (q + 1)
      (Path.refl (underTopBasepoint E)))

/-- The `π_ 0` loop-space model of `π_1(F)` for the actual fiber `F` of a based fibration. -/
abbrev fibrationFiberLoopPiZeroHomotopyGroup {E B : BasedSpace} (p : E ⟶ B) :=
  π_ 0 (Ω (actualFiberSet p) (actualFiberBasepoint p)) (Path.refl (actualFiberBasepoint p))

/-- The `π_ 0` loop-space model of `π_1(E)` for the total space of a based fibration. -/
abbrev fibrationTotalLoopPiZeroHomotopyGroup (E : BasedSpace) :=
  π_ 0 (Ω E.right (underTopBasepoint E)) (Path.refl (underTopBasepoint E))

/-- The `π_ 0` loop-space model of `π_1(B)` appearing in the long exact sequence tail. -/
abbrev fibrationBaseLoopPiZeroHomotopyGroup (B : BasedSpace) :=
  π_ 0 (Ω B.right (underTopBasepoint B)) (Path.refl (underTopBasepoint B))

/-- The map `π_1(F) → π_1(E)` written on the canonical `π_ 0` loop-space models. -/
def fibrationLoopFiberInclusionPiZeroMap {E B : BasedSpace} (p : E ⟶ B) :
    fibrationFiberLoopPiZeroHomotopyGroup p → fibrationTotalLoopPiZeroHomotopyGroup E :=
  homotopyGroupMap (fibrationFiberLoopInclusionMap p) 0 (Path.refl (actualFiberBasepoint p))

/-- The map `π_1(E) → π_1(B)` written on the canonical `π_ 0` loop-space models. -/
def fibrationLoopTotalToBasePiZeroMap {E B : BasedSpace} (p : E ⟶ B) :
    fibrationTotalLoopPiZeroHomotopyGroup E → fibrationBaseLoopPiZeroHomotopyGroup B :=
  cast
    (congrArg
      (fun y ↦
        fibrationTotalLoopPiZeroHomotopyGroup E →
          π_ 0 (Ω B.right (underTopBasepoint B)) y)
      (fibrationLoopTotalToBaseMap_refl p))
    (homotopyGroupMap (fibrationLoopTotalToBaseMap p) 0 (Path.refl (underTopBasepoint E)))

/-- The tail exactness condition
`π_1(F) ⟶ π_1(E) ⟶ π_1(B) ⟶ π₀(F) ⟶ π₀(E) ⟶ {*} `,
written with the canonical `π_0` loop-space models for the three `π₁` terms. -/
def fibrationHomotopyTailExact {E B : BasedSpace} (p : E ⟶ B)
    (boundaryZero :
      fibrationBaseLoopPiZeroHomotopyGroup B → ZerothHomotopy (actualFiberSet p)) : Prop :=
  (∀ g : fibrationTotalLoopPiZeroHomotopyGroup E,
      fibrationLoopTotalToBasePiZeroMap p g = default ↔
        ∃ a : fibrationFiberLoopPiZeroHomotopyGroup p,
          fibrationLoopFiberInclusionPiZeroMap p a = g) ∧
    (∀ r : fibrationBaseLoopPiZeroHomotopyGroup B,
      boundaryZero r = ⟦actualFiberBasepoint p⟧ ↔
        ∃ g : fibrationTotalLoopPiZeroHomotopyGroup E,
          fibrationLoopTotalToBasePiZeroMap p g = r) ∧
    (∀ a₀ : ZerothHomotopy (actualFiberSet p),
      zerothHomotopyInclusion (actualFiberSet p) a₀ = ⟦underTopBasepoint E⟧ ↔
        ∃ r : fibrationBaseLoopPiZeroHomotopyGroup B,
          boundaryZero r = a₀) ∧
    ∀ e₀ : ZerothHomotopy E.right,
      ∃ a₀ : ZerothHomotopy (actualFiberSet p),
        zerothHomotopyInclusion (actualFiberSet p) a₀ = e₀

/-- A source-facing specification of the long exact homotopy sequence of a based fibration,
written with explicit connecting maps and exactness clauses. -/
def fibrationHomotopyLongExactSequenceSpec {E B : BasedSpace} (p : E ⟶ B)
    (boundary :
      ∀ q : ℕ, fibrationBaseLoopHomotopyGroup B q → fibrationFiberHomotopyGroup p (q + 1))
    (boundaryZero :
      fibrationBaseLoopPiZeroHomotopyGroup B → ZerothHomotopy (actualFiberSet p)) : Prop :=
  (∀ q : ℕ,
      Function.MulExact
        (fibrationLoopFiberInclusionHomotopyGroupMap p q)
        (fibrationLoopTotalToBaseHomotopyGroupMap p q)) ∧
    (∀ q : ℕ,
      Function.MulExact
        (fibrationLoopTotalToBaseHomotopyGroupMap p q)
        (boundary q)) ∧
    (∀ q : ℕ,
      Function.MulExact
        (boundary q)
        (fibrationFiberInclusionHomotopyGroupMap p q)) ∧
    fibrationHomotopyTailExact p boundaryZero

/-- A long exact homotopy sequence for a based fibration `p`, written using the local Chapter 9
loop-space models for the `π_(q + 2)(B)` terms and an explicit tail
`π_1(F) ⟶ π_1(E) ⟶ π_1(B) ⟶ π₀(F) ⟶ π₀(E) ⟶ {*} `. -/
structure FibrationHomotopyLongExactSequence {E B : BasedSpace} (p : E ⟶ B) where
  /-- The connecting homomorphism `π_(q + 2)(B) ⟶ π_(q + 1)(F)` on the Chapter 9 loop-space
  model of `π_(q + 2)(B)`. -/
  boundary :
    ∀ q : ℕ, fibrationBaseLoopHomotopyGroup B q → fibrationFiberHomotopyGroup p (q + 1)
  /-- The terminal connecting map `π_1(B) ⟶ π₀(F)` in the long exact sequence. -/
  boundaryZero :
    fibrationBaseLoopPiZeroHomotopyGroup B → ZerothHomotopy (actualFiberSet p)
  /-- The source-facing exactness specification attached to these connecting maps. -/
  spec : fibrationHomotopyLongExactSequenceSpec p boundary boundaryZero

namespace FibrationHomotopyLongExactSequence

variable {E B : BasedSpace} {p : E ⟶ B}

/-- Exactness of `π_(q + 2)(F) ⟶ π_(q + 2)(E) ⟶ π_(q + 2)(B)` on the loop-space models. -/
theorem exact_fiber_to_total (les : FibrationHomotopyLongExactSequence p) (q : ℕ) :
    Function.MulExact
      (fibrationLoopFiberInclusionHomotopyGroupMap p q)
      (fibrationLoopTotalToBaseHomotopyGroupMap p q) :=
  les.spec.1 q

/-- Exactness of `π_(q + 2)(E) ⟶ π_(q + 2)(B) ⟶ π_(q + 1)(F)`. -/
theorem exact_total_to_boundary (les : FibrationHomotopyLongExactSequence p) (q : ℕ) :
    Function.MulExact
      (fibrationLoopTotalToBaseHomotopyGroupMap p q)
      (les.boundary q) :=
  les.spec.2.1 q

/-- Exactness of `π_(q + 2)(B) ⟶ π_(q + 1)(F) ⟶ π_(q + 1)(E)`. -/
theorem exact_boundary_to_fiber (les : FibrationHomotopyLongExactSequence p) (q : ℕ) :
    Function.MulExact
      (les.boundary q)
      (fibrationFiberInclusionHomotopyGroupMap p q) :=
  les.spec.2.2.1 q

/-- The tail `π_1(F) ⟶ π_1(E) ⟶ π_1(B) ⟶ π₀(F) ⟶ π₀(E) ⟶ {*} ` is exact. -/
theorem tail_exact (les : FibrationHomotopyLongExactSequence p) :
    fibrationHomotopyTailExact p les.boundaryZero :=
  les.spec.2.2.2

end FibrationHomotopyLongExactSequence

/-- Helper for Theorem 9.3.4: postcomposition on homotopy groups respects composition of the
underlying continuous maps. -/
private theorem homotopyGroupMap_comp
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (q : ℕ) (a : A) :
    homotopyGroupMap (g.comp f) q a =
      (homotopyGroupMap g q (f a)) ∘ homotopyGroupMap f q a := by
  -- Reduce to representatives, where both sides are the same postcomposition map.
  funext x
  refine Quotient.inductionOn x ?_
  intro γ
  rfl

/-- Helper for Theorem 9.3.4: a target-basepoint equality transports the induced homotopy-group
map to the chosen target owner. -/
private def homotopyGroupMapOverEq
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (q : ℕ) :
    π_ q A a → π_ q B b :=
  cast
    (congrArg (fun y ↦ π_ q A a → π_ q B y) hf)
    (homotopyGroupMap f q a)

/-- Helper for Theorem 9.3.4: changing only the endpoint-equality proof does not change the
transported homotopy-group map. -/
private theorem homotopyGroupMapOverEq_proofIrrel
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (h₁ h₂ : f a = b) (q : ℕ) :
    homotopyGroupMapOverEq f h₁ q = homotopyGroupMapOverEq f h₂ q := by
  -- The codomain transport depends only on a proposition-valued equality witness.
  cases h₁
  cases h₂
  rfl

/-- Helper for Theorem 9.3.4: equal continuous maps induce equal transported homotopy-group maps.
-/
private theorem homotopyGroupMapOverEq_congr
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(A, B)} (hfg : f = g) {a : A} {b : B} (hf : f a = b) (hg : g a = b) (q : ℕ) :
    homotopyGroupMapOverEq f hf q = homotopyGroupMapOverEq g hg q := by
  -- After identifying the underlying maps, only proof irrelevance remains.
  subst hfg
  exact homotopyGroupMapOverEq_proofIrrel f hf hg q

/-- Helper for Theorem 9.3.4: transported homotopy-group maps respect composition of the
underlying continuous maps. -/
private theorem homotopyGroupMapOverEq_comp
    {A : Type*} {B : Type*} {C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C))
    {a : A} {b : B} {c : C} (hf : f a = b) (hg : g b = c) (q : ℕ) :
    (homotopyGroupMapOverEq g hg q) ∘ (homotopyGroupMapOverEq f hf q) =
      homotopyGroupMapOverEq (g.comp f)
        (by simpa [ContinuousMap.comp_apply, hf] using hg) q := by
  -- Remove the endpoint transports, then invoke functoriality of `homotopyGroupMap`.
  funext x
  cases hg
  cases hf
  simpa [homotopyGroupMapOverEq] using congrFun (homotopyGroupMap_comp f g q a).symm x

/-- Helper for Theorem 9.3.4: postcomposing a generalized loop and then viewing it at the chosen
target basepoint still satisfies the boundary condition. -/
private theorem genLoopMapOverEqLoop_boundary
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (q : ℕ)
    (γ : Ω^ (Fin q) A a) :
    ∀ t ∈ Cube.boundary (Fin q), (genLoopMap f γ).1 t = b := by
  intro t ht
  calc
    (genLoopMap f γ).1 t = f a := by
      simpa using congrArg f (γ.2 t ht)
    _ = b := hf

/-- Helper for Theorem 9.3.4: the postcomposed generalized loop regarded at the chosen target
basepoint. -/
private def genLoopMapOverEqLoop
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) {q : ℕ}
    (γ : Ω^ (Fin q) A a) :
    Ω^ (Fin q) B b :=
  ⟨(genLoopMap f γ).1, genLoopMapOverEqLoop_boundary f hf q γ⟩

/-- Helper for Theorem 9.3.4: transported homotopy-group maps send a representative to the class
of its transported postcomposition. -/
private theorem homotopyGroupMapOverEq_mk
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (q : ℕ)
    (γ : Ω^ (Fin q) A a) :
    homotopyGroupMapOverEq f hf q ⟦γ⟧ =
      (⟦genLoopMapOverEqLoop f hf γ⟧ : π_ q B b) := by
  -- Reduce to the definitional case where the target basepoint is literally `f a`.
  cases hf
  simpa [homotopyGroupMapOverEq, genLoopMapOverEqLoop] using homotopyGroupMap_mk f q a γ

/-- Helper for Theorem 9.3.4: applying the bundled positive-degree transported map agrees with the
unbundled transported homotopy-group map. -/
private theorem eStarMulHomOverEq_apply
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (n : ℕ)
    (x : π_ (n + 1) A a) :
    f.eStarMulHomOverEq n hf x = homotopyGroupMapOverEq f hf (n + 1) x := by
  -- Once the endpoint proof is definitionally `rfl`, both transported maps are literally the
  -- same induced homomorphism.
  cases hf
  rfl

/-- Helper for Theorem 9.3.4: transported postcomposition preserves the constant generalized
loop. -/
private theorem genLoopMapOverEqLoop_const
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) {q : ℕ} :
    genLoopMapOverEqLoop f hf (GenLoop.const : Ω^ (Fin q) A a) =
      (GenLoop.const : Ω^ (Fin q) B b) := by
  -- Route correction: compare the transported constant loop pointwise instead of unfolding the
  -- quotient classes inside the tail exactness proof.
  cases hf
  ext t
  rfl

/-- Helper for Theorem 9.3.4: specializing the pair loop-inclusion map to the actual fiber gives
the loop-space inclusion used in the fibration sequence. -/
private theorem pairLoopSubspaceInclusionHomotopyGroupMap_actualFiber
    {E B : BasedSpace} (p : E ⟶ B) (q : ℕ) :
    pairLoopSubspaceInclusionHomotopyGroupMap (actualFiberSet p) (actualFiberBasepoint p) q =
      fibrationLoopFiberInclusionHomotopyGroupMap p q := by
  -- Both sides are induced by the same subtype inclusion of the actual fiber into `E.right`.
  funext a
  rfl

/-- Helper for Theorem 9.3.4: specializing the pair inclusion map to the actual fiber gives the
ordinary inclusion of the actual fiber into the total space. -/
private theorem pairSubspaceInclusionHomotopyGroupMap_actualFiber
    {E B : BasedSpace} (p : E ⟶ B) (q : ℕ) :
    pairSubspaceInclusionHomotopyGroupMap (actualFiberSet p) (actualFiberBasepoint p) (q + 1) =
      fibrationFiberInclusionHomotopyGroupMap p q := by
  -- Both sides are induced by the same continuous inclusion `actualFiberSet p ↪ E.right`.
  funext a
  rfl

/-- Helper for Theorem 9.3.4: the `π₁(F) → π₁(E)` map in the pair tail agrees with the fibration
tail map after specializing to the actual fiber. -/
private theorem pairLoopSubspaceInclusionPiZeroMap_actualFiber
    {E B : BasedSpace} (p : E ⟶ B) :
    pairLoopSubspaceInclusionPiZeroMap (actualFiberSet p) (actualFiberBasepoint p) =
      fibrationLoopFiberInclusionPiZeroMap p := by
  -- Both sides are induced by the same loop-space inclusion `ΩF ↪ ΩE`.
  funext a
  rfl

/-- Helper for Theorem 9.3.4: composing the pair loop-to-relative path-space map of the actual
fiber with `actualFiberRelativeToLoopMap` recovers the loop map induced by `p`. -/
private theorem actualFiberRelativeToLoopMap_comp_pairLoopToRelativePathSpaceMap
    {E B : BasedSpace} (p : E ⟶ B) :
    (actualFiberRelativeToLoopMap p).comp
        (pairLoopToRelativePathSpaceMap (actualFiberSet p) (actualFiberBasepoint p)) =
      fibrationLoopTotalToBaseMap p := by
  -- Route correction: compare the underlying loop in `B` pointwise instead of unfolding the full
  -- transported homotopy-group owners in the final theorem.
  ext γ t
  rfl

/-- Helper for Theorem 9.3.4: on positive-degree loop-space homotopy groups, the Chapter 9
comparison `π_(q + 2)(E, F) ≃ π_(q + 2)(B)` intertwines the pair connecting map with the
fibration map `π_(q + 2)(E) → π_(q + 2)(B)`. -/
private theorem fibrationRelativeToLoopMap_intertwines_pairLoopToRelative
    {E B : BasedSpace} (p : E ⟶ B) (q : ℕ) :
    fibrationRelativeHomotopyGroupToLoopMap p ((q + 1).succPNat) ∘
        pairLoopToRelativeHomotopyGroupMap (actualFiberSet p) (actualFiberBasepoint p) q =
      fibrationLoopTotalToBaseHomotopyGroupMap p q := by
  -- Route correction: rewrite both public maps through the local transported-`π` API, so the
  -- comparison reduces to one composite continuous map `ΩE → P(E; *, F) → ΩB`.
  cases relativeHomotopyGroup_succ (q + 1) (actualFiberSet p) (actualFiberBasepoint p)
  simpa [fibrationRelativeHomotopyGroupToLoopMap, pairLoopToRelativeHomotopyGroupMap,
    fibrationLoopTotalToBaseHomotopyGroupMap, homotopyGroupMapOverEq] using
    (calc
      homotopyGroupMapOverEq (actualFiberRelativeToLoopMap p)
          (actualFiberRelativeToLoopMap_refl p) (q + 1) ∘
        homotopyGroupMapOverEq
          (pairLoopToRelativePathSpaceMap (actualFiberSet p) (actualFiberBasepoint p))
          (pairLoopToRelativePathSpaceMap_refl (actualFiberSet p) (actualFiberBasepoint p))
          (q + 1)
          =
          homotopyGroupMapOverEq
            ((actualFiberRelativeToLoopMap p).comp
              (pairLoopToRelativePathSpaceMap (actualFiberSet p) (actualFiberBasepoint p)))
            (by
              simpa [ContinuousMap.comp_apply] using
                (actualFiberRelativeToLoopMap_refl p))
            (q + 1) := by
              simpa using
                (homotopyGroupMapOverEq_comp
                  (pairLoopToRelativePathSpaceMap (actualFiberSet p) (actualFiberBasepoint p))
                  (actualFiberRelativeToLoopMap p)
                  (pairLoopToRelativePathSpaceMap_refl
                    (actualFiberSet p) (actualFiberBasepoint p))
                  (actualFiberRelativeToLoopMap_refl p)
                  (q + 1))
      _ = homotopyGroupMapOverEq
            (fibrationLoopTotalToBaseMap p)
            (fibrationLoopTotalToBaseMap_refl p)
            (q + 1) := by
              exact homotopyGroupMapOverEq_congr
                (actualFiberRelativeToLoopMap_comp_pairLoopToRelativePathSpaceMap p)
                _ _
                (q + 1))

/-- Helper for Theorem 9.3.4: the degree-`1` comparison `π₁(E, F) ≃ π₁(B)` intertwines the tail
map `π₁(E) → π₁(E, F)` with the fibration tail map `π₁(E) → π₁(B)`. -/
private theorem fibrationRelativeToLoopMap_intertwines_pairLoopToRelativePiZero
    {E B : BasedSpace} (p : E ⟶ B) :
    fibrationRelativeHomotopyGroupToLoopMap p 1 ∘
        pairLoopToRelativePiZeroMap (actualFiberSet p) (actualFiberBasepoint p) =
      fibrationLoopTotalToBasePiZeroMap p := by
  -- Route correction: the `π_ 0` tail uses the same composite continuous map, but read on the
  -- transported `π_ 0` owners instead of the positive-degree groups.
  cases relativeHomotopyGroup_succ 0 (actualFiberSet p) (actualFiberBasepoint p)
  simpa [fibrationRelativeHomotopyGroupToLoopMap, pairLoopToRelativePiZeroMap,
    fibrationLoopTotalToBasePiZeroMap, homotopyGroupMapOverEq] using
    (calc
      homotopyGroupMapOverEq (actualFiberRelativeToLoopMap p)
          (actualFiberRelativeToLoopMap_refl p) 0 ∘
        homotopyGroupMapOverEq
          (pairLoopToRelativePathSpaceMap (actualFiberSet p) (actualFiberBasepoint p))
          (pairLoopToRelativePathSpaceMap_refl (actualFiberSet p) (actualFiberBasepoint p))
          0
          =
          homotopyGroupMapOverEq
            ((actualFiberRelativeToLoopMap p).comp
              (pairLoopToRelativePathSpaceMap (actualFiberSet p) (actualFiberBasepoint p)))
            (by
              simpa [ContinuousMap.comp_apply] using
                (actualFiberRelativeToLoopMap_refl p))
            0 := by
              simpa using
                (homotopyGroupMapOverEq_comp
                  (pairLoopToRelativePathSpaceMap (actualFiberSet p) (actualFiberBasepoint p))
                  (actualFiberRelativeToLoopMap p)
                  (pairLoopToRelativePathSpaceMap_refl
                    (actualFiberSet p) (actualFiberBasepoint p))
                  (actualFiberRelativeToLoopMap_refl p)
                  0)
      _ = homotopyGroupMapOverEq
            (fibrationLoopTotalToBaseMap p)
            (fibrationLoopTotalToBaseMap_refl p)
            0 := by
              exact homotopyGroupMapOverEq_congr
                (actualFiberRelativeToLoopMap_comp_pairLoopToRelativePathSpaceMap p)
                _ _
                0)

/-- Helper for Theorem 9.3.4: in positive degree, the Chapter 9 comparison preserves the unit
element. -/
private theorem pairLoopToRelativeHomotopyGroupMap_one_actualFiber
    {E B : BasedSpace} (p : E ⟶ B) (q : ℕ) :
    pairLoopToRelativeHomotopyGroupMap (actualFiberSet p) (actualFiberBasepoint p) q 1 = 1 := by
  -- Normalize the relative owner; the remaining statement is the standard `homotopyGroupMap_one`
  -- computation for `pairLoopToRelativePathSpaceMap`.
  cases relativeHomotopyGroup_succ (q + 1) (actualFiberSet p) (actualFiberBasepoint p)
  change homotopyGroupMapOverEq
      (pairLoopToRelativePathSpaceMap (actualFiberSet p) (actualFiberBasepoint p))
      (pairLoopToRelativePathSpaceMap_refl (actualFiberSet p) (actualFiberBasepoint p))
      (q + 1) 1 = 1
  rw [← eStarMulHomOverEq_apply
    (pairLoopToRelativePathSpaceMap (actualFiberSet p) (actualFiberBasepoint p))
    (pairLoopToRelativePathSpaceMap_refl (actualFiberSet p) (actualFiberBasepoint p))
    q 1]
  exact (ContinuousMap.eStarMulHomOverEq
    (pairLoopToRelativePathSpaceMap (actualFiberSet p) (actualFiberBasepoint p))
    q
    (pairLoopToRelativePathSpaceMap_refl (actualFiberSet p) (actualFiberBasepoint p))).map_one

/-- Helper for Theorem 9.3.4: the loop-space map induced by the fibration preserves the unit
element on positive-degree homotopy groups. -/
private theorem fibrationLoopTotalToBaseHomotopyGroupMap_one
    {E B : BasedSpace} (p : E ⟶ B) (q : ℕ) :
    fibrationLoopTotalToBaseHomotopyGroupMap p q 1 = 1 := by
  -- This is the standard unit computation for the induced map on the loop-space model of `B`.
  change homotopyGroupMapOverEq
      (fibrationLoopTotalToBaseMap p)
      (fibrationLoopTotalToBaseMap_refl p)
      (q + 1) 1 = 1
  rw [← eStarMulHomOverEq_apply
    (fibrationLoopTotalToBaseMap p)
    (fibrationLoopTotalToBaseMap_refl p)
    q 1]
  exact (ContinuousMap.eStarMulHomOverEq
    (fibrationLoopTotalToBaseMap p)
    q
    (fibrationLoopTotalToBaseMap_refl p)).map_one

/-- Helper for Theorem 9.3.4: in positive degree, the Chapter 9 comparison preserves the unit
element. -/
private theorem fibrationRelativeHomotopyGroupToLoopMap_one
    {E B : BasedSpace} (p : E ⟶ B) (q : ℕ) :
    (fibrationRelativeHomotopyGroupToLoopMap p ((q + 1).succPNat) :
        relativeHomotopyGroup ((q + 1).succPNat) (actualFiberSet p) (actualFiberBasepoint p) →
          fibrationBaseLoopHomotopyGroup B q)
        (1 : relativeHomotopyGroup ((q + 1).succPNat) (actualFiberSet p) (actualFiberBasepoint p)) =
      (1 : fibrationBaseLoopHomotopyGroup B q) := by
  -- Route correction: read the unit through the loop/relative comparison already proved above,
  -- instead of forcing a direct dependent cast normalization.
  calc
    fibrationRelativeHomotopyGroupToLoopMap p ((q + 1).succPNat)
        (1 : relativeHomotopyGroup ((q + 1).succPNat) (actualFiberSet p) (actualFiberBasepoint p))
        =
      fibrationRelativeHomotopyGroupToLoopMap p ((q + 1).succPNat)
        (pairLoopToRelativeHomotopyGroupMap (actualFiberSet p) (actualFiberBasepoint p) q 1) := by
        rw [pairLoopToRelativeHomotopyGroupMap_one_actualFiber p q]
    fibrationRelativeHomotopyGroupToLoopMap p ((q + 1).succPNat)
        (pairLoopToRelativeHomotopyGroupMap (actualFiberSet p) (actualFiberBasepoint p) q 1)
        =
      fibrationLoopTotalToBaseHomotopyGroupMap p q 1 := by
        exact congrFun (fibrationRelativeToLoopMap_intertwines_pairLoopToRelative p q) 1
    _ = 1 := fibrationLoopTotalToBaseHomotopyGroupMap_one p q
    _ = (1 : fibrationBaseLoopHomotopyGroup B q) := rfl

/-- Helper for Theorem 9.3.4: in degree `1`, the comparison `π₁(E, F) → π₁(B)` sends the
distinguished relative-path component to the distinguished loop component. -/
private theorem fibrationRelativeHomotopyGroupToLoopMap_default
    {E B : BasedSpace} (p : E ⟶ B) :
    fibrationRelativeHomotopyGroupToLoopMap p 1 default = default := by
  -- Route correction: evaluate the transported `π_ 0` map on the constant representative rather
  -- than trying to normalize the tail basepoint after the fact.
  cases relativeHomotopyGroup_succ 0 (actualFiberSet p) (actualFiberBasepoint p)
  change homotopyGroupMapOverEq (actualFiberRelativeToLoopMap p)
      (actualFiberRelativeToLoopMap_refl p) 0 default = default
  rw [show (default :
      π_ 0 (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)
        (PathToSet.refl (actualFiberBasepoint p))) =
      ⟦(GenLoop.const :
          Ω^ (Fin 0) (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)
            (PathToSet.refl (actualFiberBasepoint p)))⟧ by
    rfl]
  rw [homotopyGroupMapOverEq_mk
    (actualFiberRelativeToLoopMap p)
    (actualFiberRelativeToLoopMap_refl p)
    0
    (GenLoop.const :
      Ω^ (Fin 0) (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)
        (PathToSet.refl (actualFiberBasepoint p)))]
  rw [genLoopMapOverEqLoop_const
    (actualFiberRelativeToLoopMap p)
    (actualFiberRelativeToLoopMap_refl p)]
  rfl

/-- Helper for Theorem 9.3.4: if the base is path connected, every path component of `E.right`
meets the actual fiber over the basepoint. -/
private theorem zerothHomotopyInclusion_surjective_of_pathConnectedBase {E B : BasedSpace}
    (p : E ⟶ B) [IsBasedFibration p] [PathConnectedSpace B.right] :
    Function.Surjective (zerothHomotopyInclusion (actualFiberSet p)) := by
  intro e₀
  -- Represent the ambient path component by an actual point of `E.right`.
  refine Quotient.inductionOn e₀ ?_
  intro e
  -- Join `p e` to the chosen basepoint of `B`, then lift that path from the starting point `e`.
  rcases PathConnectedSpace.joined (p.right.hom e) (underTopBasepoint B) with ⟨γ⟩
  rcases (IsBasedFibration.iff_surjective_and_nonempty_basedPathLiftingFunction p).1 inferInstance
      with ⟨_, hs⟩
  rcases hs with ⟨s⟩
  let x : BasedMappingPathSpace p := ⟨(e, γ.toContinuousMap), by simpa using γ.source'⟩
  let a : actualFiberSet p := ⟨s x 1, by
    -- Projecting the lifted path to `B` shows that its endpoint lies in the actual fiber.
    have hproj := BasedPathLiftingFunction.proj_apply s x 1
    simpa [x] using hproj.trans γ.target'⟩
  refine ⟨⟦a⟧, ?_⟩
  rw [zerothHomotopyInclusion_mk]
  -- The lifted path in `E` witnesses that `a.1` and `e` lie in the same path component.
  apply Quotient.sound
  refine ⟨(Path.mk (s x) ?_ ?_).symm⟩
  · simpa [x] using BasedPathLiftingFunction.apply_zero s x
  · rfl

/-- Theorem 9.3.4: if `p : E ⟶ B` is a based fibration with path-connected base `B`, then the
actual fiber `F = p⁻¹' {underTopBasepoint B}` admits connecting maps
`π_(q + 2)(B) ⟶ π_(q + 1)(F)` and `π_1(B) ⟶ π₀(F)` making the source long exact homotopy
sequence
`⋯ ⟶ π_n(F) ⟶ π_n(E) ⟶ π_n(B) ⟶ π_(n - 1)(F) ⟶ ⋯ ⟶ π₀(E) ⟶ {*} `
exact. In the formalization, the `π_n(B)` terms are written on the canonical Chapter 9
loop-space model from Theorem 9.3.3, and the tail is recorded by
`fibrationHomotopyLongExactSequenceSpec p boundary boundaryZero`. -/
theorem fibrationHomotopyLongExactSequence {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] [PathConnectedSpace B.right] :
    ∃ boundary :
        ∀ q : ℕ, fibrationBaseLoopHomotopyGroup B q → fibrationFiberHomotopyGroup p (q + 1),
      ∃ boundaryZero :
          fibrationBaseLoopPiZeroHomotopyGroup B → ZerothHomotopy (actualFiberSet p),
        fibrationHomotopyLongExactSequenceSpec p boundary boundaryZero := by
  let ePos :
      ∀ q : ℕ,
        relativeHomotopyGroup ((q + 1).succPNat) (actualFiberSet p) (actualFiberBasepoint p) ≃
          fibrationBaseLoopHomotopyGroup B q :=
    fun q ↦
      Equiv.ofBijective
        (fibrationRelativeHomotopyGroupToLoopMap p ((q + 1).succPNat))
        (fibrationRelativeHomotopyGroupToLoopMap_bijective p ((q + 1).succPNat))
  let eZero :
      relativeHomotopyGroup 1 (actualFiberSet p) (actualFiberBasepoint p) ≃
        fibrationBaseLoopPiZeroHomotopyGroup B :=
    Equiv.ofBijective
      (fibrationRelativeHomotopyGroupToLoopMap p 1)
      (fibrationRelativeHomotopyGroupToLoopMap_bijective p 1)
  let boundary :
      ∀ q : ℕ, fibrationBaseLoopHomotopyGroup B q → fibrationFiberHomotopyGroup p (q + 1) :=
    fun q ↦ pairHomotopyBoundaryMap (actualFiberSet p) (actualFiberBasepoint p) q ∘ (ePos q).symm
  let boundaryZero :
      fibrationBaseLoopPiZeroHomotopyGroup B → ZerothHomotopy (actualFiberSet p) :=
    pairHomotopyBoundaryZeroMap (actualFiberSet p) (actualFiberBasepoint p) ∘ eZero.symm
  refine ⟨boundary, boundaryZero, ?_⟩
  constructor
  · intro q
    -- Transport the first pair exactness clause across the injective comparison map
    -- `π_(q + 2)(E, F) → π_(q + 2)(B)`.
    have hExact :=
      pairHomotopyLongExactSequenceSubspaceToAmbient
        (actualFiberSet p) (actualFiberBasepoint p) q
    let compare :
        relativeHomotopyGroup ((q + 1).succPNat) (actualFiberSet p) (actualFiberBasepoint p) →
          fibrationBaseLoopHomotopyGroup B q :=
      fibrationRelativeHomotopyGroupToLoopMap p ((q + 1).succPNat)
    have hTransport :
        Function.MulExact
          (pairLoopSubspaceInclusionHomotopyGroupMap
            (actualFiberSet p) (actualFiberBasepoint p) q)
          (compare ∘
            pairLoopToRelativeHomotopyGroupMap
              (actualFiberSet p) (actualFiberBasepoint p) q) := by
      exact Function.MulExact.comp_injective
        (f := pairLoopSubspaceInclusionHomotopyGroupMap
          (actualFiberSet p) (actualFiberBasepoint p) q)
        (g := pairLoopToRelativeHomotopyGroupMap
          (actualFiberSet p) (actualFiberBasepoint p) q)
        (g' := compare)
        hExact
        (ePos q).injective
        (fibrationRelativeHomotopyGroupToLoopMap_one p q)
    have hCompare :
        compare ∘ pairLoopToRelativeHomotopyGroupMap
            (actualFiberSet p) (actualFiberBasepoint p) q =
          fibrationLoopTotalToBaseHomotopyGroupMap p q := by
      simpa [compare] using fibrationRelativeToLoopMap_intertwines_pairLoopToRelative p q
    rw [hCompare] at hTransport
    simpa [pairLoopSubspaceInclusionHomotopyGroupMap_actualFiber] using hTransport
  constructor
  · intro q
    -- Use the positive-degree comparison equivalence to rewrite the pair exactness clause
    -- `π_(q + 2)(E) → π_(q + 2)(E, F) → π_(q + 1)(F)`.
    have hExact :=
      pairHomotopyLongExactSequenceAmbientToRelative
        (actualFiberSet p) (actualFiberBasepoint p) q
    intro r
    constructor
    · intro hr
      have hr' :
          pairHomotopyBoundaryMap (actualFiberSet p) (actualFiberBasepoint p) q
              ((ePos q).symm r) = 1 := by
        simpa [boundary] using hr
      rcases (hExact ((ePos q).symm r)).1 hr' with ⟨g, hg⟩
      refine ⟨g, ?_⟩
      calc
        fibrationLoopTotalToBaseHomotopyGroupMap p q g
            = (ePos q)
                (pairLoopToRelativeHomotopyGroupMap
                  (actualFiberSet p) (actualFiberBasepoint p) q g) := by
              simpa [ePos] using
                (congrFun (fibrationRelativeToLoopMap_intertwines_pairLoopToRelative p q) g).symm
        _ = r := by rw [hg, Equiv.apply_symm_apply]
    · rintro ⟨g, rfl⟩
      have hPair :
          pairHomotopyBoundaryMap (actualFiberSet p) (actualFiberBasepoint p) q
              (pairLoopToRelativeHomotopyGroupMap
                (actualFiberSet p) (actualFiberBasepoint p) q g) = 1 :=
        Function.MulExact.apply_apply_eq_one hExact g
      calc
        boundary q (fibrationLoopTotalToBaseHomotopyGroupMap p q g)
            = boundary q
                ((ePos q)
                  (pairLoopToRelativeHomotopyGroupMap
                    (actualFiberSet p) (actualFiberBasepoint p) q g)) := by
              rw [show
                fibrationLoopTotalToBaseHomotopyGroupMap p q g =
                  (ePos q)
                    (pairLoopToRelativeHomotopyGroupMap
                      (actualFiberSet p) (actualFiberBasepoint p) q g) by
                simpa [ePos] using
                  (congrFun (fibrationRelativeToLoopMap_intertwines_pairLoopToRelative p q) g).symm]
        _ = pairHomotopyBoundaryMap (actualFiberSet p) (actualFiberBasepoint p) q
              (pairLoopToRelativeHomotopyGroupMap
                (actualFiberSet p) (actualFiberBasepoint p) q g) := by
              simp [boundary]
        _ = 1 := hPair
  constructor
  · intro q
    -- Rewrite the range of the pair boundary map through the same comparison equivalence.
    have hExact :=
      pairHomotopyLongExactSequenceBoundaryToSubspace
        (actualFiberSet p) (actualFiberBasepoint p) q
    intro a
    constructor
    · intro ha
      have ha' :
          pairSubspaceInclusionHomotopyGroupMap
              (actualFiberSet p) (actualFiberBasepoint p) (q + 1) a = 1 := by
        simpa [pairSubspaceInclusionHomotopyGroupMap_actualFiber] using ha
      rcases (hExact a).1 ha' with ⟨r, hr⟩
      refine ⟨(ePos q) r, ?_⟩
      simpa [boundary] using hr
    · rintro ⟨r, hr⟩
      have hr' :
          pairHomotopyBoundaryMap (actualFiberSet p) (actualFiberBasepoint p) q
              ((ePos q).symm r) = a := by
        simpa [boundary] using hr
      have ha' :
          pairSubspaceInclusionHomotopyGroupMap
              (actualFiberSet p) (actualFiberBasepoint p) (q + 1) a = 1 :=
        (hExact a).2 ⟨(ePos q).symm r, hr'⟩
      simpa [pairSubspaceInclusionHomotopyGroupMap_actualFiber] using ha'
  constructor
  · intro g
    -- The first tail clause is the pair exactness statement transported through the degree-`1`
    -- comparison `π₁(E, F) ≃ π₁(B)`.
    have hExact :=
      pairHomotopyLongExactSequenceTail_exact_subspace_to_ambient
        (actualFiberSet p) (actualFiberBasepoint p)
    have hBase :
        eZero (pairRelativePiZeroBasepoint (actualFiberSet p) (actualFiberBasepoint p)) =
          default := by
      simpa [eZero, pairRelativePiZeroBasepoint_eq_default] using
        fibrationRelativeHomotopyGroupToLoopMap_default p
    constructor
    · intro hg
      have hg' :
          pairLoopToRelativePiZeroMap (actualFiberSet p) (actualFiberBasepoint p) g =
            pairRelativePiZeroBasepoint (actualFiberSet p) (actualFiberBasepoint p) := by
        apply (eZero.injective)
        calc
          eZero
              (pairLoopToRelativePiZeroMap
                (actualFiberSet p) (actualFiberBasepoint p) g)
              = fibrationLoopTotalToBasePiZeroMap p g := by
                  simpa [eZero] using
                    (congrFun
                      (fibrationRelativeToLoopMap_intertwines_pairLoopToRelativePiZero p) g)
          _ = default := hg
          _ = eZero
                (pairRelativePiZeroBasepoint
                  (actualFiberSet p) (actualFiberBasepoint p)) := hBase.symm
      rcases (hExact g).1 hg' with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      simpa [pairLoopSubspaceInclusionPiZeroMap_actualFiber] using ha
    · rintro ⟨a, ha⟩
      have ha' :
          pairLoopSubspaceInclusionPiZeroMap
              (actualFiberSet p) (actualFiberBasepoint p) a = g := by
        simpa [pairLoopSubspaceInclusionPiZeroMap_actualFiber] using ha
      have hPair :
          pairLoopToRelativePiZeroMap (actualFiberSet p) (actualFiberBasepoint p) g =
            pairRelativePiZeroBasepoint (actualFiberSet p) (actualFiberBasepoint p) :=
        (hExact g).2 ⟨a, ha'⟩
      calc
        fibrationLoopTotalToBasePiZeroMap p g
            = eZero
                (pairLoopToRelativePiZeroMap
                  (actualFiberSet p) (actualFiberBasepoint p) g) := by
              simpa [eZero] using
                (congrFun (fibrationRelativeToLoopMap_intertwines_pairLoopToRelativePiZero p) g).symm
        _ = eZero
              (pairRelativePiZeroBasepoint
                (actualFiberSet p) (actualFiberBasepoint p)) := by
              rw [hPair]
        _ = default := hBase
  constructor
  · intro r
    -- Transport the second tail clause
    -- `π₁(E, F) ⟶ π₀(F)` through the same comparison equivalence.
    have hExact :=
      pairHomotopyLongExactSequenceTail_exact_ambient_to_relative
        (actualFiberSet p) (actualFiberBasepoint p)
    constructor
    · intro hr
      have hr' :
          pairHomotopyBoundaryZeroMap (actualFiberSet p) (actualFiberBasepoint p)
              (eZero.symm r) = ⟦actualFiberBasepoint p⟧ := by
        simpa [boundaryZero] using hr
      rcases (hExact (eZero.symm r)).1 hr' with ⟨g, hg⟩
      refine ⟨g, ?_⟩
      calc
        fibrationLoopTotalToBasePiZeroMap p g
            = eZero
                (pairLoopToRelativePiZeroMap
                  (actualFiberSet p) (actualFiberBasepoint p) g) := by
              simpa [eZero] using
                (congrFun (fibrationRelativeToLoopMap_intertwines_pairLoopToRelativePiZero p) g).symm
        _ = r := by rw [hg, Equiv.apply_symm_apply]
    · rintro ⟨g, hg⟩
      have hg' :
          pairLoopToRelativePiZeroMap (actualFiberSet p) (actualFiberBasepoint p) g =
            eZero.symm r := by
        apply (eZero.injective)
        calc
          eZero
              (pairLoopToRelativePiZeroMap
                (actualFiberSet p) (actualFiberBasepoint p) g)
              = fibrationLoopTotalToBasePiZeroMap p g := by
                  simpa [eZero] using
                    (congrFun
                      (fibrationRelativeToLoopMap_intertwines_pairLoopToRelativePiZero p) g)
          _ = r := hg
          _ = eZero (eZero.symm r) := by rw [Equiv.apply_symm_apply]
      have hr' :
          pairHomotopyBoundaryZeroMap (actualFiberSet p) (actualFiberBasepoint p)
              (eZero.symm r) = ⟦actualFiberBasepoint p⟧ :=
        (hExact (eZero.symm r)).2 ⟨g, hg'⟩
      simpa [boundaryZero] using hr'
  constructor
  · intro a₀
    -- The third tail clause only depends on the range of the terminal pair boundary map, so the
    -- comparison equivalence simply reindexes the witnesses.
    have hExact :=
      pairHomotopyLongExactSequenceTail_exact_boundary_to_piZero
        (actualFiberSet p) (actualFiberBasepoint p)
    constructor
    · intro ha₀
      rcases (hExact a₀).1 (by simpa using ha₀) with ⟨r, hr⟩
      refine ⟨eZero r, ?_⟩
      simpa [boundaryZero] using hr
    · rintro ⟨r, hr⟩
      have hr' :
          pairHomotopyBoundaryZeroMap (actualFiberSet p) (actualFiberBasepoint p)
              (eZero.symm r) = a₀ := by
        simpa [boundaryZero] using hr
      simpa using (hExact a₀).2 ⟨eZero.symm r, hr'⟩
  · -- The final tail clause is the geometric path-lifting argument already isolated above.
    exact zerothHomotopyInclusion_surjective_of_pathConnectedBase p
