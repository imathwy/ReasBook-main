import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap

open CategoryTheory FundamentalGroupoid
open scoped TopCat Topology Topology.Homotopy
open Path.Homotopic.Quotient

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]
variable [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]

-- Semantic recall via `lean_leansearch`: mathlib exposes basepoint-change on `π₁` through
-- `FundamentalGroup.fundamentalGroupMulEquivOfPath`, while Chapter 7 provides the general
-- fiber-translation construction for fibrations. This item therefore records the Section 9.5
-- basepoint-change construction on the explicit sphere-evaluation fiber model of `π_n(X, x)`.

/-- Evaluation at `sphereBasepoint n`, with the sphere universe pinned to the current file's
universe parameter. -/
private abbrev sphereBasepointEvalMap (n : ℕ) : C(C((𝕊 n : TopCat.{u}), X), X) :=
  sphereMapEvalAtBasepoint n (sphereBasepoint n : (𝕊 n : TopCat.{u}))

/-- The source-faithful evaluation map whose domain is May's compactly generated mapping space,
rather than the raw compact-open mapping space. -/
private def sphereBasepointEvalMapKified (n : ℕ) :
    C(CompactlyGenerated.MapSpace (𝕊 n : TopCat.{u}) X, X) where
  toFun f := f (sphereBasepoint n : (𝕊 n : TopCat.{u}))
  continuous_toFun :=
    (continuous_eval_const (sphereBasepoint n : (𝕊 n : TopCat.{u}))).comp
      (continuousKifiedForget C((𝕊 n : TopCat.{u}), X))

/-- K-ifying the domain of the sphere-evaluation fibration preserves its lifting property. -/
private instance sphereBasepointEvalMapKified_isFibration (n : ℕ) :
    IsFibration.{u, u, u} (sphereBasepointEvalMapKified (X := X) n) where
  surjective := by
    intro x
    exact ⟨CompactlyGenerated.MapSpace.ofContinuousMap
      (ContinuousMap.const (𝕊 n : TopCat.{u}) x), rfl⟩
  homotopyLift {A} _ _ {f₀} {f₁} H {g₀} hg₀ := by
    let pRaw : C(C((𝕊 n : TopCat.{u}), X), X) := sphereBasepointEvalMap n
    let g₀Raw : C(A, C((𝕊 n : TopCat.{u}), X)) :=
      ⟨fun a ↦ (g₀ a : C((𝕊 n : TopCat.{u}), X)),
        (continuousKifiedForget C((𝕊 n : TopCat.{u}), X)).comp g₀.continuous⟩
    have hg₀Raw : pRaw.comp g₀Raw = f₀ := by
      ext a
      exact ContinuousMap.congr_fun hg₀ a
    letI : IsFibration pRaw := sphereMapEvalAtBasepointInstIsFibration n
    obtain ⟨g₁Raw, GRaw, hGRaw⟩ :=
      IsFibration.exists_homotopyLift (p := pRaw) (H := H) (g₀ := g₀Raw) hg₀Raw
    let g₁ : C(A, CompactlyGenerated.MapSpace (𝕊 n : TopCat.{u}) X) :=
      ⟨fun a ↦ CompactlyGenerated.MapSpace.ofContinuousMap (g₁Raw a),
        continuousToKifiedOfContinuous g₁Raw.continuous⟩
    let _ : UCompactlyGeneratedSpace.{u} (↑unitInterval × A) :=
      uCompactlyGeneratedSpaceCompHausProd ↑unitInterval A
    have hGContinuous :
        Continuous fun z : ↑unitInterval × A ↦
          CompactlyGenerated.MapSpace.ofContinuousMap (GRaw z) := by
      exact continuousToKifiedOfContinuous GRaw.continuous
    let G : g₀.Homotopy g₁ :=
      { toFun := fun z ↦ CompactlyGenerated.MapSpace.ofContinuousMap (GRaw z)
        continuous_toFun := hGContinuous
        map_zero_left := by
          intro a
          exact congrArg Kified.mk (GRaw.apply_zero a)
        map_one_left := by
          intro a
          exact congrArg Kified.mk (GRaw.apply_one a) }
    refine ⟨g₁, G, ?_⟩
    ext z
    exact ContinuousMap.congr_fun hGRaw z

/-- The functor sending a space to its set of path components factors through
`TopCatHomotopyCategory`. -/
private def zerothHomotopyFunctorToTypes : TopCat.{u} ⥤ Type u where
  obj Y := ZerothHomotopy Y
  map f := zerothHomotopyMap f.hom
  map_id Y := by
    ext q
    refine Quotient.inductionOn q ?_
    intro y
    rfl
  map_comp f g := by
    ext q
    refine Quotient.inductionOn q ?_
    intro y
    rfl

private theorem zerothHomotopyFunctorToTypes_respects
    (Y Z : TopCat.{u}) (f g : Y ⟶ Z) (hfg : topCatHomotopyRel f g) :
    zerothHomotopyFunctorToTypes.map f = zerothHomotopyFunctorToTypes.map g := by
  exact zerothHomotopyMap_eq_of_homotopic hfg

private abbrev sphereBasepointFiberKified (n : ℕ) (x : X) :=
  fiber (sphereBasepointEvalMapKified (X := X) n) x

/-- Forgetting the k-ification sends the convenient sphere-evaluation fiber to the raw
compact-open fiber used by the public Section 9.5 API. -/
private def sphereBasepointFiberKifiedForget (n : ℕ) (x : X) :
    C(sphereBasepointFiberKified n x, sphereBasepointFiber n x) where
  toFun f := ⟨f.1.of, f.2⟩
  continuous_toFun :=
    Continuous.subtype_mk
      ((continuousKifiedForget C((𝕊 n : TopCat.{u}), X)).comp continuous_subtype_val)
      fun f ↦ f.2

/-- Pointwise inclusion of the raw sphere-evaluation fiber into its k-ified version. This map is
used only on points and compact paths; no global continuity assertion is needed. -/
private def sphereBasepointFiberToKified (n : ℕ) (x : X) :
    sphereBasepointFiber n x → sphereBasepointFiberKified n x :=
  fun f ↦ ⟨Kified.mk f.1, f.2⟩

private theorem sphereBasepointFiberToKified_respects (n : ℕ) (x : X)
    {f g : sphereBasepointFiber n x} (hfg : Joined f g) :
    Joined (sphereBasepointFiberToKified n x f)
      (sphereBasepointFiberToKified n x g) := by
  let γ : Path f g := hfg.somePath
  have hγ : Continuous fun t : ↑unitInterval ↦
      Kified.mk ((γ t).1 : C((𝕊 n : TopCat.{u}), X)) :=
    continuousToKifiedOfContinuous (continuous_subtype_val.comp γ.continuous)
  refine ⟨{
    toContinuousMap :=
      ⟨fun t ↦ sphereBasepointFiberToKified n x (γ t),
        Continuous.subtype_mk hγ fun t ↦ (γ t).2⟩
    source' := ?_
    target' := ?_ }⟩
  · exact congrArg (sphereBasepointFiberToKified n x) γ.source
  · exact congrArg (sphereBasepointFiberToKified n x) γ.target

/-- K-ification changes the mapping-space topology but not its path components: paths have the
compactly generated interval as source, so every raw path lifts continuously to the k-ification.
-/
private def sphereBasepointFiberZerothEquivKified (n : ℕ) (x : X) :
    ZerothHomotopy (sphereBasepointFiberKified n x) ≃
      ZerothHomotopy (sphereBasepointFiber n x) where
  toFun := zerothHomotopyMap (sphereBasepointFiberKifiedForget n x)
  invFun := Quotient.map (sphereBasepointFiberToKified n x)
    (fun _ _ h ↦ sphereBasepointFiberToKified_respects n x h)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro f
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro f
    rfl

/-- The Section 9.5 sphere-fiber owner becomes a `FundamentalGroupoid X`-diagram after applying
path components to the Chapter 7 fiber-translation functor. -/
private def sphereBasepointFiberZerothFunctor (n : ℕ) :
    FundamentalGroupoid X ⥤ Type u :=
  let F : FundamentalGroupoid X ⥤ TopCatHomotopyCategory :=
    @fiberTranslationHomotopyFunctor.{u, u}
      (CompactlyGenerated.MapSpace (𝕊 n : TopCat.{u}) X)
      X
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      (sphereBasepointEvalMapKified n)
      inferInstance
  F ⋙
    CategoryTheory.Quotient.lift topCatHomotopyRel
      zerothHomotopyFunctorToTypes
      zerothHomotopyFunctorToTypes_respects

/-- Definition 9.5.2. A path class `α` from `x` to `x'` induces the basepoint-change isomorphism
on the Section 9.5 fiber model of `π_n(X, x)`, obtained by translation of the fibers of
`sphereMapEvalAtBasepoint n (sphereBasepoint n)`. -/
def sphereBasepointFiberZerothMap
    (n : ℕ) {x x' : X} (α : Path.Homotopic.Quotient x x') :
    ZerothHomotopy (sphereBasepointFiber n x) → ZerothHomotopy (sphereBasepointFiber n x') :=
  fun a ↦ sphereBasepointFiberZerothEquivKified n x'
    ((sphereBasepointFiberZerothFunctor n).map (fromPath α)
      ((sphereBasepointFiberZerothEquivKified n x).symm a))

/-- Definition 9.5.2. A path class `α` from `x` to `x'` induces the basepoint-change isomorphism
on the Section 9.5 fiber model of `π_n(X, x)`, obtained by translation of the fibers of
`sphereMapEvalAtBasepoint n (sphereBasepoint n)`. -/
def sphereBasepointFiberZerothEquivOfPathClass
    (n : ℕ) {x x' : X} (α : Path.Homotopic.Quotient x x') :
    ZerothHomotopy (sphereBasepointFiber n x) ≃ ZerothHomotopy (sphereBasepointFiber n x') :=
  (sphereBasepointFiberZerothEquivKified n x).symm.trans
    (((sphereBasepointFiberZerothFunctor n).mapIso (asIso (fromPath α))).toEquiv.trans
      (sphereBasepointFiberZerothEquivKified n x'))

/-- Applying `sphereBasepointFiberZerothEquivOfPathClass` amounts to applying the transported map
on path components induced by the path class `α`. -/
@[simp] theorem sphereBasepointFiberZerothEquivOfPathClass_apply
    (n : ℕ) {x x' : X} (α : Path.Homotopic.Quotient x x')
    (a : ZerothHomotopy (sphereBasepointFiber n x)) :
    sphereBasepointFiberZerothEquivOfPathClass n α a =
      sphereBasepointFiberZerothMap n α a :=
  rfl
